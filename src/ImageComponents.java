/*
 * ImageComponents.java
 * A5 Solution by Sheng Chen, 1263891.
 * 
 * P.S.
 * I think my code logically works fine, but for some reason it won't display the correct colors.
 * I've consulted multiple TAs and had them look at my code, but none of them was able to figure
 * out what was wrong. Same goes with the extra credit part. I was wondering if I can still get
 * partial credit for the extra credit problem.
 * 
 * 
 * 
 * CSE 373, University of Washington, Winter 2016.
 * 
 * Starter Code for CSE 373 Assignment 5, Part II.    Starter Code Version 1.
 * S. Tanimoto
 * 
 */ 

import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.image.BufferedImage;
import java.awt.image.BufferedImageOp;
import java.awt.image.ByteLookupTable;
import java.awt.image.ConvolveOp;
import java.awt.image.Kernel;
import java.awt.image.LookupOp;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;

import javax.imageio.ImageIO;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.filechooser.FileNameExtensionFilter;
import java.math.*;
public class ImageComponents extends JFrame implements ActionListener {
    public static ImageComponents appInstance; // Used in main().

    String startingImage = "gettysburg-address-p1.png";
    BufferedImage biTemp, biWorking, biFiltered; // These hold arrays of pixels.
    Graphics gOrig, gWorking; // Used to access the drawImage method.
    
    int w; // width of the current image.
    int h; // height of the current image.
    int unionCount;// number of unions
    int[][] parentID; // For your forest of up-trees.
    Map<Integer, Integer> componentCount;//stores pixel IDs and its counts
    PriorityQueue<Edge> Q;// priority queue used to store Edge objects
    final int DELTA = 255 * 255 * 3;// DELTA value large enough to cover black vs white
     
    JPanel viewPanel; // Where the image will be painted.
    JPopupMenu popup;
    JMenuBar menuBar;
    JMenu fileMenu, imageOpMenu, ccMenu, helpMenu;
    JMenuItem loadImageItem, saveAsItem, exitItem;
    JMenuItem lowPassItem, highPassItem, photoNegItem, RGBThreshItem;

    JMenuItem CCItem1, CCItem2;
    JMenuItem aboutItem, helpItem;
    
    JFileChooser fileChooser; // For loading and saving images.
    
    public class Color {
        int r, g, b;

        Color(int r, int g, int b) {
            this.r = r; this.g = g; this.b = b;    		
        }

        Color(int rgb) {
        	b = rgb & 0xFF;
        	g = (rgb >> 8) & 0xFF;
       		r = (rgb >> 16) & 0xFF;
        }
        
        double squaredEuclideanDistance(Color c2) {
			if (c2==null) { return Double.MAX_VALUE; }
			int dr = r-c2.r;
			int dg = g-c2.g;
			int db = b-c2.b;
			return dr*dr + dg*dg + db*db;
        }
    }


    // Some image manipulation data definitions that won't change...
    static LookupOp PHOTONEG_OP, RGBTHRESH_OP;
    static ConvolveOp LOWPASS_OP, HIGHPASS_OP;
    
    public static final float[] SHARPENING_KERNEL = { // sharpening filter kernel
        0.f, -1.f,  0.f,
       -1.f,  5.f, -1.f,
        0.f, -1.f,  0.f
    };

    public static final float[] BLURRING_KERNEL = {
        0.1f, 0.1f, 0.1f,    // low-pass filter kernel
        0.1f, 0.2f, 0.1f,
        0.1f, 0.1f, 0.1f
    };
    
    // find method that returns the pixelID of the root of the up-tree that contains 
    // the passed in pixelID
    int find(int pixelID) {
    	int xCoord = getXcoord(pixelID);
    	int yCoord = getYcoord(pixelID);
	    while (parentID[xCoord][yCoord] != -1) {
	   		pixelID = parentID[xCoord][yCoord];
	   		xCoord = getXcoord(pixelID);
	   		yCoord = getYcoord(pixelID);
	   	}
    	return yCoord * w + xCoord;
    }         
    
    // union method that unions two pixels, by making the one having the smaller pixelID 
    // value be the parent of the other.
    void union(int pixelID1, int pixelID2) {
    	unionCount++;
    	if (pixelID1 < pixelID2) {
    		parentID[getXcoord(pixelID2)][getYcoord(pixelID2)] = pixelID1;
    	}else {
    		parentID[getXcoord(pixelID1)][getYcoord(pixelID1)] = pixelID2;
    	}
    }
    
    // helper method that compares two sets of coordinates, if they have same color and are not
    // of same connected component, union them
    private void comparePixel(int x, int y, int a, int b) {
    	if (biWorking.getRGB(x, y) == biWorking.getRGB(a, b)) {
			if (find(y * w + x) != find(b * w + a)) {
				union(find(y * w + x), find(b * w + a));
			}
    	}
    }
    
    // with given height and width, build parentID, fill in -1
    void buildArray(int w, int h) {
    	parentID = new int[w][h];
		for (int y = 0; y < h; y++) {
			for (int x = 0; x < w; x++) {
				parentID[x][y] = -1;
			}
		}
    }
    
    // build up-trees for every pixel pair in the 2d array
    private void buildUpTrees() {
    	for (int y = 0; y < h - 1; y++) {
    		for (int x = 0; x < w - 1; x++) {
    			comparePixel(x, y, x, y + 1);
    			comparePixel(x, y, x + 1, y);
    		}
    	}
    	for (int y = 0; y < h -1; y++) {
			comparePixel(w - 1, y, w - 1, y + 1);
    	}
    	for (int x = 0; x < w - 1; x++) {
			comparePixel(x, h - 1, x + 1, h - 1);
    	}
    }
    
    // compute connected components, keep the counts in componentCount map
    void computeConnectedComponents() {
    	for (int y = 0; y < h; y++) {
    		for (int x = 0; x < w; x++) {
    			if (parentID[x][y] == -1) {
    				componentCount.put(y * w + x, 0);
    			}else {
    				if (componentCount.keySet().contains(find(y * w + x))) {
    					componentCount.put(find(y * w + x), componentCount.get(find(y * w + x)) + 1);
    				}else {
        				componentCount.put(find(y * w + x), 0);
    				}
    			}
    		}
    	}
    	System.out.println("The number of times that the method UNION was called for this image is: " + appInstance.getUnionCount() + ".");
    	System.out.println("The number of connected components in this image is: " + appInstance.getCount() + ".");
        colorScan();
        repaint();
    }
    
    // scan all pixels, find its progressive color, and put the new color into the image.
    private void colorScan() {
		ProgressiveColors pc = new ProgressiveColors();
    	for (int y = 0; y < h; y++) {
    		for (int x = 0; x < w; x++) {
    			int k = (int) componentCount.get(find(y * w + x));
    			int[] newRGB = pc.progressiveColor(k);
    			putPixel(biWorking, x, y, newRGB[0], newRGB[1], newRGB[2]);
    		}
    	}
    }
    
    // returns the x coordinate of a pixelID
    private int getXcoord(int id) {
    	return id % w;
    }
    // returns the y coordinate of a pixelID
    private int getYcoord(int id) {
    	return id / w;
    }
    
    // returns the number of times union() is called 
    int getUnionCount() {
    	return unionCount;
    }
    
    // returns the number of connected components in the image 
    int getCount() {
    	return componentCount.keySet().size();
    }
    
    /* This main method can be used to run the application. */
    public static void main(String[] args) {
        appInstance = new ImageComponents();
    	appInstance.componentCount = new HashMap<Integer, Integer>();
    }
    
    public ImageComponents() { // Constructor for the application.
        setTitle("Image Analyzer"); 
        addWindowListener(new WindowAdapter() { // Handle any window close-box clicks.
            public void windowClosing(WindowEvent e) {System.exit(0);}
        });

        // Create the panel for showing the current image, and override its
        // default paint method to call our paintPanel method to draw the image.
        viewPanel = new JPanel(){public void paint(Graphics g) { paintPanel(g);}};
        add("Center", viewPanel); // Put it smack dab in the middle of the JFrame.

        // Create standard menu bar
        menuBar = new JMenuBar();
        setJMenuBar(menuBar);
        fileMenu = new JMenu("File");
        imageOpMenu = new JMenu("Image Operations");
        ccMenu = new JMenu("Connected Components");
        helpMenu = new JMenu("Help");
        menuBar.add(fileMenu);
        menuBar.add(imageOpMenu);
        menuBar.add(ccMenu);
        menuBar.add(helpMenu);

        // Create the File menu's menu items.
        loadImageItem = new JMenuItem("Load image...");
        loadImageItem.addActionListener(this);
        fileMenu.add(loadImageItem);
        saveAsItem = new JMenuItem("Save as full-color PNG");
        saveAsItem.addActionListener(this);
        fileMenu.add(saveAsItem);
        exitItem = new JMenuItem("Quit");
        exitItem.addActionListener(this);
        fileMenu.add(exitItem);

        // Create the Image Operation menu items.
        lowPassItem = new JMenuItem("Convolve with blurring kernel");
        lowPassItem.addActionListener(this);
        imageOpMenu.add(lowPassItem);
        highPassItem = new JMenuItem("Convolve with sharpening kernel");
        highPassItem.addActionListener(this);
        imageOpMenu.add(highPassItem);
        photoNegItem = new JMenuItem("Photonegative");
        photoNegItem.addActionListener(this);
        imageOpMenu.add(photoNegItem);
        RGBThreshItem = new JMenuItem("RGB Thresholds at 128");
        RGBThreshItem.addActionListener(this);
        imageOpMenu.add(RGBThreshItem);

 
        // Create CC menu stuff.
        CCItem1 = new JMenuItem("Compute Connected Components and Recolor");
        CCItem2 = new JMenuItem("Segment Image and Recolor");
        CCItem1.addActionListener(this);
        CCItem2.addActionListener(this);
        ccMenu.add(CCItem1);
        ccMenu.add(CCItem2);
        
        // Create the Help menu's item.
        aboutItem = new JMenuItem("About");
        aboutItem.addActionListener(this);
        helpMenu.add(aboutItem);
        helpItem = new JMenuItem("Help");
        helpItem.addActionListener(this);
        helpMenu.add(helpItem);

        // Initialize the image operators, if this is the first call to the constructor:
        if (PHOTONEG_OP==null) {
            byte[] lut = new byte[256];
            for (int j=0; j<256; j++) {
                lut[j] = (byte)(256-j); 
            }
            ByteLookupTable blut = new ByteLookupTable(0, lut); 
            PHOTONEG_OP = new LookupOp(blut, null);
        }
        if (RGBTHRESH_OP==null) {
            byte[] lut = new byte[256];
            for (int j=0; j<256; j++) {
                lut[j] = (byte)(j < 128 ? 0: 200);
            }
            ByteLookupTable blut = new ByteLookupTable(0, lut); 
            RGBTHRESH_OP = new LookupOp(blut, null);
        }
        if (LOWPASS_OP==null) {
            float[] data = BLURRING_KERNEL;
            LOWPASS_OP = new ConvolveOp(new Kernel(3, 3, data),
                                        ConvolveOp.EDGE_NO_OP,
                                        null);
        }
        if (HIGHPASS_OP==null) {
            float[] data = SHARPENING_KERNEL;
            HIGHPASS_OP = new ConvolveOp(new Kernel(3, 3, data),
                                        ConvolveOp.EDGE_NO_OP,
                                        null);
        }
        loadImage(startingImage); // Read in the pre-selected starting image.
        setVisible(true); // Display it.
    }
    
    /*
     * Given a path to a file on the file system, try to load in the file
     * as an image.  If that works, replace any current image by the new one.
     * Re-make the biFiltered buffered image, too, because its size probably
     * needs to be different to match that of the new image.
     */
    public void loadImage(String filename) {
        try {
            biTemp = ImageIO.read(new File(filename));
            w = biTemp.getWidth();
            h = biTemp.getHeight();
            
            // build the parentID array with given w and h
            buildArray(w, h);
            viewPanel.setSize(w,h);
            biWorking = new BufferedImage(w, h, BufferedImage.TYPE_INT_RGB);
            gWorking = biWorking.getGraphics();
            gWorking.drawImage(biTemp, 0, 0, null);
            biFiltered = new BufferedImage(w, h, BufferedImage.TYPE_INT_RGB);
            pack(); // Lay out the JFrame and set its size.
            repaint();
            
            // build up trees using parentID
            buildUpTrees();
        } catch (IOException e) {
            System.out.println("Image could not be read: "+filename);
            System.exit(1);
        }
    }

    /* Menu handlers
     */
    void handleFileMenu(JMenuItem mi){
        System.out.println("A file menu item was selected.");
        if (mi==loadImageItem) {
            File loadFile = new File("image-to-load.png");
            if (fileChooser==null) {
                fileChooser = new JFileChooser();
                fileChooser.setSelectedFile(loadFile);
                fileChooser.setFileFilter(new FileNameExtensionFilter("Image files", new String[] { "JPG", "JPEG", "GIF", "PNG" }));
            }
            int rval = fileChooser.showOpenDialog(this);
            if (rval == JFileChooser.APPROVE_OPTION) {
                loadFile = fileChooser.getSelectedFile();
                loadImage(loadFile.getPath());
            }
        }
        if (mi==saveAsItem) {
            File saveFile = new File("savedimage.png");
            fileChooser = new JFileChooser();
            fileChooser.setSelectedFile(saveFile);
            int rval = fileChooser.showSaveDialog(this);
            if (rval == JFileChooser.APPROVE_OPTION) {
                saveFile = fileChooser.getSelectedFile();
                // Save the current image in PNG format, to a file.
                try {
                    ImageIO.write(biWorking, "png", saveFile);
                } catch (IOException ex) {
                    System.out.println("There was some problem saving the image.");
                }
            }
        }
        if (mi==exitItem) { this.setVisible(false); System.exit(0); }
    }

    void handleEditMenu(JMenuItem mi){
        System.out.println("An edit menu item was selected.");
    }

    void handleImageOpMenu(JMenuItem mi){
        System.out.println("An imageOp menu item was selected.");
        if (mi==lowPassItem) { applyOp(LOWPASS_OP); }
        else if (mi==highPassItem) { applyOp(HIGHPASS_OP); }
        else if (mi==photoNegItem) { applyOp(PHOTONEG_OP); }
        else if (mi==RGBThreshItem) { applyOp(RGBTHRESH_OP); }
        repaint();
    }

    void handleCCMenu(JMenuItem mi) {
        System.out.println("A connected components menu item was selected.");
        if (mi==CCItem1) { computeConnectedComponents(); }
        if (mi==CCItem2) { 
        	int nregions = 25; // default value.
        	String inputValue = JOptionPane.showInputDialog(
        										"Please input the number of regions desired");
        	try {
        		nregions = (new Integer(inputValue)).intValue();
        	}
        	catch(Exception e) {
        		System.out.println(e);
        		System.out.println("That did not convert to an integer. Using the default: 25.");
        	}
        	System.out.println("nregions is "+ nregions);
        	segmentImageAndRecolor(nregions);
        	computeConnectedComponents();
        }
    }
    
    // Segment image and re-color, takes in a parameter represents the number of regions
    void segmentImageAndRecolor(int nregions) {
    	Q = new PriorityQueue<Edge>();
    	for (int y = 0; y < h - 1; y++) {
    		for (int x = 0; x < w - 1; x++) {
    			Q.add(new Edge(x, y, x, y + 1));
    			Q.add(new Edge(x, y, x + 1, y));
    		}
    	}
    	for (int y = 0; y < h -1; y++) {
    		Q.add(new Edge(w - 1, y, w - 1, y + 1));
    	}
    	for (int x = 0; x < w - 1; x++) {
			Q.add(new Edge(x, h - 1, x + 1, h - 1));
    	}
    	buildMSF(nregions);
    }
    
    // Builds the minimum spanning tree
    void buildMSF(int n) {
    	boolean Finished = false;
    	int nTrees = w * h;
    	buildArray(w, h);
    	while (!Finished) {
    		Edge e = Q.remove();
    		int w = e.weight;
    		if (w > DELTA || nTrees <= n) {
    			Finished = true;
    			break;
    		}
	    	int u = e.endpoint0;
	    	int v = e.endpoint1;
	   		if (find(u) != find(v)) {
	   			union(find(u), find(v));
	   			nTrees -= 1;
	   		}
    	}
    	System.out.println("Done finding minimum spannng forest");
    }
    
    // Edge class that represents a edge between two vertices.
    public class Edge implements Comparable<Edge>{
    	int endpoint0;
    	int endpoint1;
    	int weight;
    	
    	// Constructor of the class that takes in two pairs of coordinates and calculates weight.
    	public Edge(int x, int y, int a, int b) {
    		endpoint0 = y * w + x;
    		endpoint1 = b * w + a;
    		Color currColor = new Color(biWorking.getRGB(x, y));
    		Color nextColor = new Color(biWorking.getRGB(a, b));
    		weight = (int) currColor.squaredEuclideanDistance(nextColor);
    	}
    	
		@Override
		public int compareTo(Edge e2) {
			if (weight < e2.weight) {
				return -1;
			}else if (weight == e2.weight) {
				return 0;
			}else {
				return 1;
			}
		}
    }
    
    void handleHelpMenu(JMenuItem mi){
        System.out.println("A help menu item was selected.");
        if (mi==aboutItem) {
            System.out.println("About: Well this is my program.");
            JOptionPane.showMessageDialog(this,
                "Image Components, Starter-Code Version.",
                "About",
                JOptionPane.PLAIN_MESSAGE);
        }
        else if (mi==helpItem) {
            System.out.println("In case of panic attack, select File: Quit.");
            JOptionPane.showMessageDialog(this,
                "To load a new image, choose File: Load image...\nFor anything else, just try different things.",
                "Help",
                JOptionPane.PLAIN_MESSAGE);
        }
    }

    /*
     * Used by Swing to set the size of the JFrame when pack() is called.
     */
    public Dimension getPreferredSize() {
        return new Dimension(w, h+50); // Leave some extra height for the menu bar.
    }

    public void paintPanel(Graphics g) {
        g.drawImage(biWorking, 0, 0, null);
    }
            	
    public void applyOp(BufferedImageOp operation) {
        operation.filter(biWorking, biFiltered);
        gWorking.drawImage(biFiltered, 0, 0, null);
    }

    public void actionPerformed(ActionEvent e) {
        Object obj = e.getSource(); // What Swing object issued the event?
        if (obj instanceof JMenuItem) { // Was it a menu item?
            JMenuItem mi = (JMenuItem)obj; // Yes, cast it.
            JPopupMenu pum = (JPopupMenu)mi.getParent(); // Get the object it's a child of.
            JMenu m = (JMenu) pum.getInvoker(); // Get the menu from that (popup menu) object.
            //System.out.println("Selected from the menu: "+m.getText()); // Printing this is a debugging aid.

            if (m==fileMenu)    { handleFileMenu(mi);    return; }  // Handle the item depending on what menu it's from.
            if (m==imageOpMenu) { handleImageOpMenu(mi); return; }
            if (m==ccMenu)      { handleCCMenu(mi);      return; }
            if (m==helpMenu)    { handleHelpMenu(mi);    return; }
        } else {
            System.out.println("Unhandled ActionEvent: "+e.getActionCommand());
        }
    }


    // Use this to put color information into a pixel of a BufferedImage object.
    void putPixel(BufferedImage bi, int x, int y, int r, int g, int b) {
        int rgb = (r << 16) | (g << 8) | b; // pack 3 bytes into a word.
        bi.setRGB(x,  y, rgb);
    }
}
