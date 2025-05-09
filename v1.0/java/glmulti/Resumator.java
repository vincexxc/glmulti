package glmulti;

// produces glm models and combines them if needed
// models are coded as bit sequences (using longs)
// Vincent Calcagno March 2009
// vincentcalcagno  -a-t- mcgill -d-o-t- ca


import java.io.*;

public class Resumator  {
	
	
	public static ModelGenerator resto(String argos) {
		try {
		// this will restore a previous GA from serialized objects
		File fifi1 = new File(argos+".modgen.back");
		File fifi2 = new File(argos+".mods.back");
		ObjectInputStream koala = new ObjectInputStream(new FileInputStream(fifi1));
		ModelGenerator babacool = (ModelGenerator)koala.readObject();
		ObjectInputStream koala2 = new ObjectInputStream(new FileInputStream(fifi2));
		// restore conf set
		babacool.confset = (GLMModel[]) koala2.readObject();
		babacool.ok = true;
		return babacool;	
	 } catch (Exception brrr) {
	 	System.out.println(brrr.getMessage());
	 	return  new ModelGenerator();	

	  }
			
	}
	

	
}
