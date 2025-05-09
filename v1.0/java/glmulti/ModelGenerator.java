package glmulti;

// produces glm models and combines them if needed
// models are coded as bit sequences (using longs)
// Vincent Calcagno March 2009
// updated December 2010
// vincentcalcagno  -a-t- mcgill -d-o-t- ca

import java.io.*;
import java.util.*;


public class ModelGenerator extends java.util.Random implements Runnable, Serializable {


static final long maxmods = 1000000000l; // max nb of models to look for in diagnose()
static final int DELTAR = 10; // number of generations between two updates of the confidence set (for GA)

int nc, nq; // number of expla variables (categorical/quantitative)
int nbmodsxc, nbmodsxq;
String interc;
boolean margot;
int errorDF; // how many degrees of freedoms are being used by the R fitting function
boolean cplxlim; // are there constraints on model complexity?
int nbintxqxq, nbintxqxq1, nbintxqxq2;
int[][] intxqxq;
long nbmodsxqxq1, nbmodsxqxq2;
int order; //1: main effects only, 2: two way interactions as well (3 is not implemented so far)
int minsize; // minimum number of terms to include in models
int mincplx, maxcplx, maxsize;

boolean ok;


String[] xc, xq; // variable names
String resp; // name of dependent variable
int[] nlevels; // number of levels of factors

int[][] forbxcxc, forbxqxq, forbxcxq;
int nbforbxc, nbforbxq, nbforbxcxc, nbforbxqxq, nbforbxcxq;
int ano, bno;

// related to holistic screening
transient  boolean over;
transient int bunch;
transient long currmodR;
transient boolean proceed, updated;
transient String[] currmodString, currtermsString;
transient Thread dadou;
transient int modfrom, mstep, modstored;

// related to genetic algorithm
int nbintxcxcG, nbintxcxqG ;
transient double mutrate, imm, sex;
transient int nbasex, nbimm, nbsex;
int sel, popsize, confsetsize;
long currgen;
GLMModel zebest;
transient GLMModel[] pop, confset;
transient GLMModel[] buffer;
int buffered, currposinbuffer;
int[] toeval;
double[] fifi;
transient String namou;
static int buffersize;

// *************************
// CONSTRUCTORS


public ModelGenerator() {
	// dummy;
	this.ok = false;
}

public ModelGenerator(String respou, String[] xcr, String[] xqr, String[] excluz, int order, int minsize, int maxsize, int mincplx, int maxcplx, boolean iii, boolean marg) {
	super();
	this.resp = respou;
	this.xc = new String[xcr.length -1];
	this.xq = new String[xqr.length -1];
	for (int i=1; i<xcr.length; i++) this.xc[i-1] = xcr[i];
	for (int i=1; i<xqr.length; i++) this.xq[i-1] = xqr[i];
	this.nc= this.xc.length;
	this.nq= this.xq.length;
	if (iii) interc = "1"; else interc="-1";
	this.margot=marg;
	// two long are used for encoding models of each category. 
	// this allows at most 63+63 = 126 interactions of each kind. And the most numerous are usually cross interactions
	this.ok= (nc*nq<126);
	this.over=false;
	this.order=order;
	this.minsize = minsize;
	this.maxsize = maxsize;
	this.mincplx = mincplx;
	this.maxcplx = maxcplx;
	
	nbmodsxc = (int)power(2,nc);
	nbmodsxq = (int)power(2,nq);
	
		// ***      **************       *************         ******************
	// take care of exclusions
	// matching of strings is insensitive to cass
	// CAUTION: exclusions MUST be non duplicated (i.e. several strings should not point to the same term)
	// R function glmulti does ensure that there are no duplicates, up to a certain point (only perfect duplicates...)
	if (excluz.length>1) {
	ano = 0; bno = 0;
	nbforbxc=0;
	nbforbxq=0;
	nbforbxcxc=0;
	nbforbxcxq=0;
	nbforbxqxq=0;
	forbxcxc = new int[2][excluz.length-1];
	forbxqxq = new int[2][excluz.length-1];
	forbxcxq = new int[2][excluz.length-1];
	
	for (int i=1; i<excluz.length; i++) {
		// is it an interaction or a simple effect ?
		int dodo = excluz[i].indexOf(":");
		if (dodo == -1) {// main effect
		//System.out.println("main effect excluded.");
		boolean found = false;
		// which one?
			for (int j=0; j<nc; j++) if (xc[j].equals(excluz[i])) {
				// xc
				nbforbxc++;
				ano = setLocusToOne(ano,j+1);
				found = true;
				break;
			}
			if (!found) for (int j=0; j<nq; j++) if (xq[j].equals(excluz[i])) {
				// xq
				nbforbxq++;
				bno = setLocusToOne(bno,j+1);
				break;
			}
		} else {// interaction
		//System.out.println("interaction excluded.");
			String term1 = excluz[i].substring(0,dodo);
			String term2 = excluz[i].substring(dodo+1);
			//System.out.println(term1+":"+term2);
			// which ones ?
			int who1 = -1;
			int who2 = -1;
			boolean isxc1 = true;
			boolean isxc2 = true;
			boolean found = false;
			// first
			for (int j=0; j<nc; j++) if (xc[j].equals(term1)) {
				who1 = j;
				found = true;
				break;
			}
			if (!found) for (int j=0; j<nq; j++) if (xq[j].equals(term1)) {
				who1 = j;
				found = true;
				isxc1 = false;
				break;
			}
			//if (found )System.out.println("F 1");
			// second
			found = false;
			for (int j=0; j<nc; j++) if (xc[j].equals(term2)) {
				who2 = j;
				found = true;
				break;
			}
			if (!found) for (int j=0; j<nq; j++) if (xq[j].equals(term2)) {
				who2 = j;
				found = true;
				isxc2 = false;
				break;
			}
			//if (found) System.out.println("F 2");

			// record
			if (found) if (isxc1 && isxc2) {
			// xcxc interaction	
					//System.out.println("xcxc");

			int tt1, tt2;
			if (who1>who2) {tt1=who1; tt2=who2;} else {tt1=who2; tt2=who1;}
			forbxcxc[0][nbforbxcxc]=tt1;
			forbxcxc[1][nbforbxcxc]=tt2;
			nbforbxcxc++;			
			} else if (!isxc1 && !isxc2) {
			// xqxq interaction
			//System.out.println("xqxq");
			int tt1, tt2;
			if (who1>who2) {tt1=who1; tt2=who2;} else {tt1=who2; tt2=who1;}
			forbxqxq[0][nbforbxqxq]=tt1;
			forbxqxq[1][nbforbxqxq]=tt2;
			nbforbxqxq++;			
			} else {
			// xcxq interaction
			//System.out.println("xcxq");
			forbxcxq[0][nbforbxcxq]= (isxc1)? who1 : who2;
			forbxcxq[1][nbforbxcxq]= (isxc2)? who1 : who2;
			nbforbxcxq++;							
				}	
		}	
		}}
		// ***      **************       *************         ******************
		
		// are there limits on model complexity?
		this.cplxlim = (mincplx>0 || maxcplx>0 );

	// take care of xqxq interactions once for all (since they imply nothing, in general)
    if (order==2) nbintxqxq = combi(nq)-nbforbxqxq; else nbintxqxq =0;
	intxqxq= new int[2][nbintxqxq];
	if (nbintxqxq>0) {
	int ind=0;
	for (int i=0; i<nq; i++) for (int j=0; j<nq; j++) if (i>j) {
			// check exclusions and ignore them
			boolean exclu = false;
			for (int e=0; e<nbforbxqxq; e++) if (forbxqxq[0][e]==i && forbxcxc[1][e]==j) {exclu = true; break;}
	if (!exclu) {

	intxqxq[0][ind] = i;
	intxqxq[1][ind] = j;
	ind++;
	}}
	}
	
	if (nbintxqxq>1) {
	nbintxqxq1= nbintxqxq/2;
	nbintxqxq2 = nbintxqxq-nbintxqxq1;
	} else {
	nbintxqxq1= nbintxqxq;
 	nbintxqxq2 = 0;	
	}
	nbmodsxqxq1 = power(2,nbintxqxq1);
	nbmodsxqxq2 = power(2,nbintxqxq2);
	
	
	// finalize init
	
	if (order==2) nbintxcxcG = combi(nc); else nbintxcxcG=0;
	if (order==2) nbintxcxqG = nc*nq; else nbintxcxqG=0;
	
	this.ok =  (nbintxqxq<128 && nbintxcxcG<128 && nbintxcxqG<128);
	
} 
	
 
//// *******************************
// ********************************
// MAIN METHOD (USED FOR DEBUG ONLY)

public static void main(String[] argos) {
	 ModelGenerator bibi = new ModelGenerator("rt",new String[]{"eee","f1","f2"},new String[]{"eee","LogMean","Nlev","pHlev","SpR"},new String[]{},2,-1,-1,-1,-1, true, true);
 	 GLMModel.init(bibi.nc, bibi.nq, 2, 0.3, bibi);
 	 //GLMModel dede = new GLMModel(bibi);
 	 ///System.out.println(dede.toFormula());
	 //System.out.println(bibi.makeHeaderG());
	 //System.out.println(dede.toRString());
	//System.out.println(bibi.makeHeaderG());
	
	// screen for marginality violations
	
	 GLMModel dede, dede1;
	 int[] momod1;
	 int[] momob1;
	 int nerr =0;
	 int nnoint = 0;
	 int nnomain = 0;
	 for (int i=0; i<Integer.valueOf(argos[0]); i++) {
	 dede = new GLMModel(bibi);
	 dede1 = dede.mutate();
	 dede = dede1.mutate(dede);
	 momob1 = bibi.binary(dede.b,dede.nq);
	 momod1 = bibi.binary(dede.d1,dede.nbintxqxq1);
	 //System.out.print(momod1.length);
	 boolean inthere = false;
	 boolean mainhere = false; 
	 if (momod1.length>0) {
		for (int j=0; j< momod1.length; j++) if (momod1[j]==1) {inthere=true; break;}
		if (inthere) {
		for (int j=0; j< momob1.length; j++) if (momob1[j]==0) {mainhere=true; break;}
		}
		if (!inthere) nnoint++;
		if (!mainhere) nnomain++;
	 if (inthere && !mainhere) nerr++;
	 //if (inthere) System.out.println(dede.toFormula());
	 // Now we check the formulas, to look for discrepancies
	 String[] spispi = dede.toRString().split( "\t");
	 if (spispi[5].trim().equals("0")  && spispi[15].trim().equals("1")) {
		System.out.println(dede.toFormula());
	 }
	 
	  }
	  
	 }
	 System.out.println(nnomain);
	  System.out.println(nnoint);
	   System.out.println(nerr);
	  
	   /*
	// identity test
	   GLMModel dede, dede1;
	   dede = new GLMModel(bibi);
	 dede1 = new GLMModel(bibi);
	 System.out.println(dede.sameas(dede1));
	 dede = dede1.mutate();
	 System.out.println(dede.sameas(dede1));
	 */
}


public int testou() {
	//ModelGenerator bibi = new ModelGenerator("rt",new String[]{"eee"},new String[]{"eee","LogMean","Nlev","pHlev","SpR"},new String[]{},2,-1,-1,-1,-1, true, true);
 	GLMModel.init(this.nc, this.nq, 2, 0.01, this);
	GLMModel[] roro = new GLMModel[150];
	GLMModel dede;
	int neo = 0;
	for (int i =0; i<10000; i++) {
	dede = new GLMModel(this);
	boolean ff = false;
		for (int j=0; j<neo; j++) if (dede.sameas(roro[j])) {
		ff=true;
		break;
		}
	if (!ff) {
	roro[neo]=dede;
	neo++;
	}
	}
	return neo;
}

public int testou2() {
	//ModelGenerator bibi = new ModelGenerator("rt",new String[]{"eee"},new String[]{"eee","LogMean","Nlev","pHlev","SpR"},new String[]{},2,-1,-1,-1,-1, true, true);
 	GLMModel.init(this.nc, this.nq, 2, 0.01, this);
	GLMModel[] roro = new GLMModel[150];
	GLMModel dede;
	int neo = 0;
	for (int i =0; i<10000; i++) {
	dede = new GLMModel(this);
	boolean ff = false;
		for (int j=0; j<neo; j++) if (dede.toFormula().equals(roro[j].toFormula())) {
		ff=true;
		break;
		}
	if (!ff) {
	roro[neo]=dede;
	neo++;
	}
	}
	return neo;
}

public String[] testou3() {
	//ModelGenerator bibi = new ModelGenerator("rt",new String[]{"eee"},new String[]{"eee","LogMean","Nlev","pHlev","SpR"},new String[]{},2,-1,-1,-1,-1, true, true);
 	GLMModel.init(this.nc, this.nq, 2, 0.01, this);
	GLMModel[] roro = new GLMModel[150];
	GLMModel dede;
	int neo = 0;
	for (int i =0; i<10000; i++) {
	dede = new GLMModel(this);
	boolean ff = false;
		for (int j=0; j<neo; j++) if (dede.toFormula().equals(roro[j].toFormula())) {
		ff=true;
		break;
		}
	if (!ff) {
	roro[neo]=dede;
	neo++;
	}
	}
	String[] ern = new String[neo*(neo-1)/2];
	int weird = 0;
	for (int i=0; i<neo; i++) for (int j=i+1; j<neo; j++) if (roro[i].sameas(roro[j])) {
	System.out.println(roro[i].toFormula()+" // "+roro[j].toFormula());
	ern[weird]=roro[i].toFormula()+" // "+roro[j].toFormula();
	weird++;
	}
	return ern;
}


public String testou(ModelGenerator molly) {
	//ModelGenerator bibi = new ModelGenerator("rt",new String[]{"eee","f1","f2"},new String[]{"eee","LogMean","Nlev","pHlev","SpR"},new String[]{},2,-1,-1,-1,-1, true, true);
 	GLMModel.init(this.nc, this.nq, 2, 0.3, this);
 	GLMModel dede, dede1;
	dede = new GLMModel(this);
	 //dede1 = dede.mutate();
	 //dede = dede1.mutate(dede);
	return dede.toRString();
}




// *************************
// MATH TOOLS 


public long power(int q, int b) {
	if (b==0) return 1l; else {
	long r= (long)q;
	for (int i=1; i<b;i++) r=r*(long)q;
	return r;	
}}


public int combi(int nn) {
	return (nn)*(nn-1)/2;
	
}


public int choose(double[] tab) {
		// Selects a random target in the array of double tab
		// tab must be cumulated !
		double aim = nextDouble()*tab[tab.length-1];
		int target = 0;
		while (aim > tab[target]) {
			target ++;
			}
		return target;
		}



// *************************
// TOOLS FOR BIT MANIPULATION


public long readLocus(long lg, int locus) {
		// reads the allele (0/1) at the i th locus on chromosome lg
		return ((lg >> (locus-1)) & 1);
	}

public int setLocusToOne(int lg, int locus) {
			int powo = (1 << (locus-1));
			if (readLocus(lg, locus) == 0l)
		 	return (lg + powo);
			else return lg;			
		}


public int[] binary(int nn , int dim) {
	// returns the list of effects present in the model encoded as nn
	//System.out.println(Integer.toBinaryString(nn));
	int nboc = 0;
	int[] dido = new int[Integer.bitCount(nn)];
	//int nnu;
	//if (nn>0) nnu=nn; else nnu=nn+(int)power(2,32);
	for (int i=1; i<=dim; i++) if (readLocus(nn,i)==1) {
		dido[nboc]=i-1;
		nboc++;
	}
	return dido;
}


public int[] binary(long nn ,int dim) {
	// returns the list of effects present in the model encoded as nn
	//System.out.println(Integer.toBinaryString(nn));
	int nboc = 0;
	int[] dido = new int[Long.bitCount(nn)];
	for (int i=1; i<= dim; i++) if (readLocus(nn,i)==1) {
		dido[nboc]=i-1;
		nboc++;
	}
	return dido;
}

// *************************
// FUNCTIONS FOR DIALOGUING WITH R
//  ****************************


public String makeHeaderG () {
	
	StringBuffer temp = new StringBuffer();
	if (nc>0) {
		temp.append("F:");
		for (int i=0; i<nc; i++) temp.append("\t"+xc[i]);
	}
	if (nq>0) {
		if (nc>0) temp.append("\tC:"); else temp.append("C:"); 
		for (int i=0; i<nq; i++) temp.append("\t"+xq[i]);
	}
if (this.order==2) {

if (GLMModel.nbintxcxc>0) {
temp.append("\tF:F:");
for (int i=0; i<GLMModel.nbintxcxc; i++) 
temp.append("\t"+xc[GLMModel.intxcxc[0][i]]+":"+xc[GLMModel.intxcxc[1][i]]);
}
if (GLMModel.nbintxqxq>0) {
	temp.append("\tC:C:");
for (int i=0; i<GLMModel.nbintxqxq; i++)
temp.append("\t"+xq[GLMModel.intxqxq[0][i]]+":"+xq[GLMModel.intxqxq[1][i]]);	
}
if (GLMModel.nbintxcxq>0) {
	temp.append("\tF:C:");
for (int i=0; i<GLMModel.nbintxcxq; i++)
temp.append("\t"+xc[GLMModel.intxcxq[0][i]]+":"+xq[GLMModel.intxcxq[1][i]]);
}
	
	}

return temp.toString();
}



public String makeHeaderH () {
	StringBuffer temp = new StringBuffer();
	if (nc>0) {
		temp.append("F:");
		for (int i=0; i<nc; i++) temp.append("\t"+xc[i]);
	}
	if (nq>0) {
		if (nc>0) temp.append("\tC:"); else temp.append("C:"); 
		for (int i=0; i<nq; i++) temp.append("\t"+xq[i]);
	}	
if (this.order==2) {

int nbintxcxc = combi(nc);
int nbintxcxq = nc*nq;
int[][] intxcxc;
int[][] intxcxq;
intxcxc= new int[2][nbintxcxc];
intxcxq= new int[2][nbintxcxq];
if (nbintxcxc>0) {
temp.append("\tF:F:");
for (int i=0; i<nc; i++) for (int j=0; j<nc; j++) if (i>j) {
temp.append("\t"+xc[i]+":"+xc[j]);
}}
if (nbintxqxq>0) {
	temp.append("\tC:C:");
for (int i=0; i<nq; i++) for (int j=0; j<nq; j++) if (i>j) {
temp.append("\t"+xq[i]+":"+xq[j]);	
}}
if (nbintxcxq>0) {
	temp.append("\tF:C:");
for (int i=0; i<nc; i++) for (int j=0; j<nq; j++)  {
temp.append("\t"+xc[i]+":"+xq[j]);
}}
	
	}
return temp.toString();
}

public void supplyNbLev(int[] nbl) {
	// informs this model generator of the number of levels for each factor
	this.nlevels = nbl;	
}

public void supplyErrorDF(int ndf) {
	// informs this model generator of the number of DF taken by the error distribution
	this.errorDF = ndf;	
}




// ***************************************************
//  DIAGNOSTIC TO GET NUMBER OF MODELS


public int diagnose() {
		// evaluates the number of models in the full candidate set
		// specific functions are used depending on the context
	if (!margot) if (this.cplxlim) return diagnoseFULL(); else return diagnoseFAST();
	else  if (this.cplxlim) return diagnoseFULLm(); else return diagnoseFASTm();
}

public int diagnoseFAST() {
	// evaluates the number of models in the full candidate set
	// this function is faster but cannot handle constraints on model complexity
	
int a=0;
long currmod=0;
while (a < nbmodsxc) {
	a++;
	int[] modsxc = binary(a-1, nc);
		// check for exclusions
		if (((a-1)&ano) == 0) {

	int b=0;
	while (b < nbmodsxq) {
		 b++;
		 int[] modsxq = binary(b-1, nq);
		 	// check for exclusions
			if (((b-1)&bno) == 0) {

// ************************************************************************
// at this stage we define the set of xcxc and xcxq interactions to consider		 
int nbxc = modsxc.length;
int nbxq = modsxq.length; 
// this is without any exclusion
int nbintxcxc = 0; 
if (order==2) nbintxcxc = combi(nbxc);
int nbintxcxq = 0;
if (order==2) nbintxcxq = nc*nbxq;

	
int[][] intxcxc;
int[][] intxcxq;

intxcxc= new int[2][nbintxcxc];
intxcxq= new int[2][nbintxcxq];

// True numbers of interactions (taking exclusions into account)
int nbintxcxcT = 0;
int nbintxcxqT = 0;

// proceed and ignore exclusions

if (nbintxcxc>0) {
int ind=0;
for (int i=0; i<nbxc; i++) for (int j=0; j<nbxc; j++) if (i>j) {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxcxc; e++) if (forbxcxc[0][e]==modsxc[i] && forbxcxc[1][e]==modsxc[j]) {exclu = true; break;}
if (!exclu) {
intxcxc[0][ind] = modsxc[i];
intxcxc[1][ind] = modsxc[j];
ind++;
}
}
nbintxcxcT = ind;
}


if (nbintxcxq>0) {
int ind=0;
for (int i=0; i<nc; i++) for (int j=0; j<nbxq; j++)  {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxcxq; e++) if (forbxcxq[0][e]==i && forbxcxq[1][e]==modsxq[j]) {exclu = true; break;}
if (!exclu) {	
intxcxq[0][ind] = i;
intxcxq[1][ind] = modsxq[j];
ind++;
}}
nbintxcxqT = ind;
}

// correct numbers for exclusions
nbintxcxc = nbintxcxcT;
nbintxcxq = nbintxcxqT;

// take care of potentially high numbers! Use two long to ensure enough space in most cases (up to 128 interaction terms in each class)
int nbintxcxc1;
int nbintxcxc2;
if (nbintxcxc>1) {
 nbintxcxc1= nbintxcxc/2;
 nbintxcxc2 = nbintxcxc-nbintxcxc1;
} else {
 nbintxcxc1= nbintxcxc;
 nbintxcxc2 = 0;
}
int nbintxcxq1;
int nbintxcxq2;
if (nbintxcxq>1) {
 nbintxcxq1= nbintxcxq/2;
 nbintxcxq2 = nbintxcxq-nbintxcxq1;
} else {
 nbintxcxq1= nbintxcxq;
 nbintxcxq2 = 0;
}

long nbmodsxcxc1;
long nbmodsxcxq1;
long nbmodsxcxc2;
long nbmodsxcxq2;
nbmodsxcxc1 = power(2,nbintxcxc1);  
nbmodsxcxq1 = power(2,nbintxcxq1); 
nbmodsxcxc2 = power(2,nbintxcxc2); 
nbmodsxcxq2 = power(2,nbintxcxq2);

// ************************************************************
// We are now ready to proceed
		 long c1=0;
		 while (c1 < nbmodsxcxc1) {
		 	c1++;
			long c2=0;
			while (c2 < nbmodsxcxc2) {
		 	c2++;
			// go for xcxq interactions
		 	long e1 = 0;
				 while (e1 < nbmodsxcxq1) {
				 	e1++;
					long e2=0;
					while (e2 < nbmodsxcxq2) {
				 	e2++;
					// Finally, go for xqxq interactions
					long d1=0;
					while (d1 < nbmodsxqxq1) {
					d1++;
					long d2=0;
					while (d2 < nbmodsxqxq2) {
					d2++;
					int size = Integer.bitCount(a-1)+Integer.bitCount(b-1)+Long.bitCount(c1-1)+Long.bitCount(c2-1)+Long.bitCount(d1-1)+Long.bitCount(d2-1)+Long.bitCount(e1-1)+Long.bitCount(e2-1);
					boolean val = (size>=minsize && (maxsize<0 || size<=maxsize));					
					if (val) currmod++;
					
				if (currmod>ModelGenerator.maxmods) return -1;
		}
}}}}}}}}}
	// over!
return (int)currmod;
}


public int diagnoseFASTm() {
	// evaluates the number of models in the full candidate set
	// this function is faster but cannot handle constraints on model complexity
	// this is the Full Marginality rule version (i.e. all effects are implied)
	
int a=0;
long currmod=0;
while (a < nbmodsxc) {
	a++;
	int[] modsxc = binary(a-1, nc);
		// check for exclusions
		if (((a-1)&ano) == 0) {

	int b=0;
	while (b < nbmodsxq) {
		 b++;
		 int[] modsxq = binary(b-1, nq);
		 	// check for exclusions
			if (((b-1)&bno) == 0) {

// ************************************************************************
// at this stage we define the set of xcxc and xcxq interactions to consider		 
int nbxc = modsxc.length;
int nbxq = modsxq.length; 
// this is without any exclusion
int nbintxcxc = 0; 
if (order==2) nbintxcxc = combi(nbxc);
int nbintxcxq = 0;
if (order==2) nbintxcxq = nbxc*nbxq;
int nbintxqxqLoc = 0;
if (order==2) nbintxqxqLoc = combi(nbxq);

	
int[][] intxcxc;
int[][] intxcxq;
int[][] intxqxqLoc;

intxcxc= new int[2][nbintxcxc];
intxcxq= new int[2][nbintxcxq];
intxqxq= new int[2][nbintxqxqLoc];

// True numbers of interactions we are about to compute (taking exclusions into account)
int nbintxcxcT = 0;
int nbintxcxqT = 0;
int nbintxqxqLocT = 0;

// proceed and ignore exclusions

if (nbintxcxc>0) {
int ind=0;
for (int i=0; i<nbxc; i++) for (int j=0; j<nbxc; j++) if (i>j) {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxcxc; e++) if (forbxcxc[0][e]==modsxc[i] && forbxcxc[1][e]==modsxc[j]) {exclu = true; break;}
if (!exclu) {
intxcxc[0][ind] = modsxc[i];
intxcxc[1][ind] = modsxc[j];
ind++;
}
}
nbintxcxcT = ind;
}


if (nbintxcxq>0) {
int ind=0;
for (int i=0; i<nbxc; i++) for (int j=0; j<nbxq; j++)  {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxcxq; e++) if (forbxcxq[0][e]==modsxc[i] && forbxcxq[1][e]==modsxq[j]) {exclu = true; break;}
if (!exclu) {	
intxcxq[0][ind] = modsxc[i];
intxcxq[1][ind] = modsxq[j];
ind++;
}}
nbintxcxqT = ind;
}


if (nbintxqxqLoc>0) {
int ind=0;
for (int i=0; i<nbxq; i++) for (int j=0; j<nbxq; j++) if (i>j) {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxqxq; e++) if (forbxqxq[0][e]==modsxq[i] && forbxqxq[1][e]==modsxq[j]) {exclu = true; break;}
if (!exclu) {	
intxqxq[0][ind] = modsxq[i];
intxqxq[1][ind] = modsxq[j];
ind++;
}}
nbintxqxqLocT = ind;
}



// correct numbers for exclusions
nbintxcxc = nbintxcxcT;
nbintxcxq = nbintxcxqT;
nbintxqxqLoc = nbintxqxqLocT;

// take care of potentially high numbers! Use two long to ensure enough space in most cases (up to 128 interaction terms in each class)
int nbintxcxc1;
int nbintxcxc2;
if (nbintxcxc>1) {
 nbintxcxc1= nbintxcxc/2;
 nbintxcxc2 = nbintxcxc-nbintxcxc1;
} else {
 nbintxcxc1= nbintxcxc;
 nbintxcxc2 = 0;
}
int nbintxcxq1;
int nbintxcxq2;
if (nbintxcxq>1) {
 nbintxcxq1= nbintxcxq/2;
 nbintxcxq2 = nbintxcxq-nbintxcxq1;
} else {
 nbintxcxq1= nbintxcxq;
 nbintxcxq2 = 0;
}
int nbintxqxqLoc1;
int nbintxqxqLoc2;
if (nbintxqxqLoc>1) {
 nbintxqxqLoc1= nbintxqxqLoc/2;
 nbintxqxqLoc2 = nbintxqxqLoc-nbintxqxqLoc1;
} else {
 nbintxqxqLoc1= nbintxqxqLoc;
 nbintxqxqLoc2 = 0;
}



long nbmodsxcxc1;
long nbmodsxcxq1;
long nbmodsxcxc2;
long nbmodsxcxq2;
long nbmodsxqxqLoc1;
long nbmodsxqxqLoc2;
nbmodsxcxc1 = power(2,nbintxcxc1);  
nbmodsxcxq1 = power(2,nbintxcxq1); 
nbmodsxcxc2 = power(2,nbintxcxc2); 
nbmodsxcxq2 = power(2,nbintxcxq2);
nbmodsxqxqLoc1 = power(2,nbintxqxqLoc1); 
nbmodsxqxqLoc2 = power(2,nbintxqxqLoc2);

// ************************************************************
// We are now ready to proceed
		 long c1=0;
		 while (c1 < nbmodsxcxc1) {
		 	c1++;
			long c2=0;
			while (c2 < nbmodsxcxc2) {
		 	c2++;
			// go for xcxq interactions
		 	long e1 = 0;
				 while (e1 < nbmodsxcxq1) {
				 	e1++;
					long e2=0;
					while (e2 < nbmodsxcxq2) {
				 	e2++;
					// Finally, go for xqxq interactions
					long d1=0;
					while (d1 < nbmodsxqxqLoc1) {
					d1++;
					long d2=0;
					while (d2 < nbmodsxqxqLoc2) {
					d2++;
					int size = Integer.bitCount(a-1)+Integer.bitCount(b-1)+Long.bitCount(c1-1)+Long.bitCount(c2-1)+Long.bitCount(d1-1)+Long.bitCount(d2-1)+Long.bitCount(e1-1)+Long.bitCount(e2-1);
					boolean val = (size>=minsize && (maxsize<0 || size<=maxsize));					
					if (val) currmod++;
					
				if (currmod>ModelGenerator.maxmods) return -1;
		}
}}}}}}}}}
	// over!
return (int)currmod;
}


public int diagnoseFULL() {
	// evaluates the number of models in the full candidate set
	// this function is slower but can handle constraints on model complexity

GLMModel.papa = this;
int a=0;
long currmod=0;
while (a < nbmodsxc) {
	a++;
	int[] modsxc = binary(a-1, nc);
	// check for exclusions
	if (((a-1)&ano) == 0) {
	int b=0;
	
	 while (b < nbmodsxq) {
		 b++;
		 int[] modsxq = binary(b-1, nq);
	// check for exclusions
	if (((b-1)&bno) == 0) {
		
// ************************************************************************
// at this stage we define the set of xcxc and xcxq interactions to consider		 
		 
int nbxc = modsxc.length;
int nbxq = modsxq.length;

// this is without any exclusion
int nbintxcxc = 0; 
if (order==2) nbintxcxc = combi(nbxc);
int nbintxcxq = 0;
if (order==2) nbintxcxq = nc*nbxq;
	
int[][] intxcxc;
int[][] intxcxq;

intxcxc= new int[2][nbintxcxc];
intxcxq= new int[2][nbintxcxq];

// True numbers of interactions (taking exclusions into account)
int nbintxcxcT = 0;
int nbintxcxqT = 0;

// proceed and ignore exclusions

if (nbintxcxc>0) {
int ind=0;
for (int i=0; i<nbxc; i++) for (int j=0; j<nbxc; j++) if (i>j) {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxcxc; e++) if (forbxcxc[0][e]==modsxc[i] && forbxcxc[1][e]==modsxc[j]) {exclu = true; break;}
if (!exclu) {
intxcxc[0][ind] = modsxc[i];
intxcxc[1][ind] = modsxc[j];
ind++;
}
}
nbintxcxcT = ind;
}


if (nbintxcxq>0) {
int ind=0;
for (int i=0; i<nc; i++) for (int j=0; j<nbxq; j++)  {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxcxq; e++) if (forbxcxq[0][e]==i && forbxcxq[1][e]==modsxq[j]) {exclu = true; break;}
if (!exclu) {	
intxcxq[0][ind] = i;
intxcxq[1][ind] = modsxq[j];
ind++;
}}
nbintxcxqT = ind;
}

// correct numbers for exclusions
nbintxcxc = nbintxcxcT;
nbintxcxq = nbintxcxqT;

// take care of potentially high numbers! Use two long to ensure enough space in most cases (up to 128 interaction terms in each class)
int nbintxcxc1;
int nbintxcxc2;
if (nbintxcxc>1) {
 nbintxcxc1= nbintxcxc/2;
 nbintxcxc2 = nbintxcxc-nbintxcxc1;
} else {
 nbintxcxc1= nbintxcxc;
 nbintxcxc2 = 0;
}
int nbintxcxq1;
int nbintxcxq2;
if (nbintxcxq>1) {
 nbintxcxq1= nbintxcxq/2;
 nbintxcxq2 = nbintxcxq-nbintxcxq1;
} else {
 nbintxcxq1= nbintxcxq;
 nbintxcxq2 = 0;
}

long nbmodsxcxc1;
long nbmodsxcxq1;
long nbmodsxcxc2;
long nbmodsxcxq2;
nbmodsxcxc1 = power(2,nbintxcxc1);  
nbmodsxcxq1 = power(2,nbintxcxq1); 
nbmodsxcxc2 = power(2,nbintxcxc2); 
nbmodsxcxq2 = power(2,nbintxcxq2);

// ************************************************************
// We are now ready to proceed
		 long c1=0;
		 while (c1 < nbmodsxcxc1) {
		 	c1++;
		 	int[] modsxcxc1 = binary(c1-1, nbintxcxc1);

			long c2=0;
			while (c2 < nbmodsxcxc2) {
		 	c2++;
		 	int[] modsxcxc2 = binary(c2-1, nbintxcxc2);
			
			// go for xcxq interactions
		 	long e1 = 0;
				 while (e1 < nbmodsxcxq1) {
				 	e1++;
				 	int[] modsxcxq1 = binary(e1-1, nbintxcxq1);
					long e2=0;
					while (e2 < nbmodsxcxq2) {
				 	e2++;
				 	int[] modsxcxq2 = binary(e2-1, nbintxcxq2);
				 	
					// Finally, go for xqxq interactions
					long d1=0;
					while (d1 < nbmodsxqxq1) {
					d1++;
					int[] modsxqxq1 = binary(d1-1, nbintxqxq1);
					long d2=0;
					while (d2 < nbmodsxqxq2) {
					d2++;
					int[] modsxqxq2 = binary(d2-1, nbintxqxq2);
				int size = modsxc.length+modsxq.length+modsxcxc1.length+modsxcxc2.length+modsxcxq1.length+modsxcxq2.length+modsxqxq1.length+modsxqxq2.length;
				boolean val = (size>=minsize && (maxsize<0 || size<=maxsize));
						// evaluate model complexity
						int kkk = this.errorDF;
						kkk+= modsxqxq1.length+modsxqxq2.length;
						// scan other interactions
						int atoadd = a-1;
						int btoadd = b-1;
						for (int i=0; i<modsxcxc1.length;i++) { kkk+= this.nlevels[intxcxc[0][modsxcxc1[i]]]*this.nlevels[intxcxc[1][modsxcxc1[i]]]; atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[0][modsxcxc1[i]]+1); atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[1][modsxcxc1[i]]+1);}
						for (int i=0; i<modsxcxc2.length;i++) { kkk+= this.nlevels[intxcxc[0][modsxcxc2[i]+nbintxcxc1]]*this.nlevels[intxcxc[1][modsxcxc2[i]+nbintxcxc1]]; atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[0][modsxcxc2[i]+nbintxcxc1]+1); atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[1][modsxcxc2[i]+nbintxcxc1]+1);}
						for (int i=0; i<modsxcxq1.length;i++) { kkk+= this.nlevels[intxcxq[0][modsxcxq1[i]]]; btoadd = (int)GLMModel.setLocusToZero(btoadd,intxcxq[1][modsxcxq1[i]]+1);}
						for (int i=0; i<modsxcxq2.length;i++) { kkk+= this.nlevels[intxcxq[0][modsxcxq2[i]+nbintxcxq1]]; btoadd = (int)GLMModel.setLocusToZero(btoadd,intxcxq[1][modsxcxq2[i]+nbintxcxq1]+1);}
						// add non implied main effects
						kkk += Integer.bitCount(btoadd);
						for (int y=0; y<nc; y++) if (readLocus(atoadd,y+1)==1l) kkk += this.nlevels[y];
						// take care of intercept trick
						if (modsxc.length+modsxcxc1.length+modsxcxc2.length == 0 && this.interc.equals("1")) kkk++;
						// check that constraints are verified
						if (kkk<mincplx || (maxcplx>-1 && kkk>maxcplx)) val = false;
				if (val) {
				currmod++;
				if (currmod>ModelGenerator.maxmods) return -1;
				}
		}
			
}}}}}}}}}
// over!
return (int)currmod;
}


public int diagnoseFULLm() {
	// evaluates the number of models in the full candidate set
	// this function is slower but can handle constraints on model complexity
	// used with the general marginality rule

GLMModel.papa = this;
int a=0;
long currmod=0;
while (a < nbmodsxc) {
	a++;
	int[] modsxc = binary(a-1, nc);
	// check for exclusions
	if (((a-1)&ano) == 0) {
	int b=0;
	
	 while (b < nbmodsxq) {
		 b++;
		 int[] modsxq = binary(b-1, nq);
	// check for exclusions
	if (((b-1)&bno) == 0) {
		
// ************************************************************************
// at this stage we define the set of xcxc and xcxq interactions to consider		 
int nbxc = modsxc.length;
int nbxq = modsxq.length; 
// this is without any exclusion
int nbintxcxc = 0; 
if (order==2) nbintxcxc = combi(nbxc);
int nbintxcxq = 0;
if (order==2) nbintxcxq = nbxc*nbxq;
int nbintxqxqLoc = 0;
if (order==2) nbintxqxqLoc = combi(nbxq);

	
int[][] intxcxc;
int[][] intxcxq;
int[][] intxqxqLoc;

intxcxc= new int[2][nbintxcxc];
intxcxq= new int[2][nbintxcxq];
intxqxqLoc= new int[2][nbintxqxqLoc];

// True numbers of interactions we are about to compute (taking exclusions into account)
int nbintxcxcT = 0;
int nbintxcxqT = 0;
int nbintxqxqLocT = 0;

// proceed and ignore exclusions

if (nbintxcxc>0) {
int ind=0;
for (int i=0; i<nbxc; i++) for (int j=0; j<nbxc; j++) if (i>j) {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxcxc; e++) if (forbxcxc[0][e]==modsxc[i] && forbxcxc[1][e]==modsxc[j]) {exclu = true; break;}
if (!exclu) {
intxcxc[0][ind] = modsxc[i];
intxcxc[1][ind] = modsxc[j];
ind++;
}
}
nbintxcxcT = ind;
}


if (nbintxcxq>0) {
int ind=0;
for (int i=0; i<nbxc; i++) for (int j=0; j<nbxq; j++)  {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxcxq; e++) if (forbxcxq[0][e]==modsxc[i] && forbxcxq[1][e]==modsxq[j]) {exclu = true; break;}
if (!exclu) {	
intxcxq[0][ind] = modsxc[i];
intxcxq[1][ind] = modsxq[j];
ind++;
}}
nbintxcxqT = ind;
}


if (nbintxqxqLoc>0) {
int ind=0;
for (int i=0; i<nbxq; i++) for (int j=0; j<nbxq; j++) if (i>j) {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxqxq; e++) if (forbxqxq[0][e]==modsxq[i] && forbxqxq[1][e]==modsxq[j]) {exclu = true; break;}
if (!exclu) {	
intxqxqLoc[0][ind] = modsxq[i];
intxqxqLoc[1][ind] = modsxq[j];
ind++;
}}
nbintxqxqLocT = ind;
}



// correct numbers for exclusions
nbintxcxc = nbintxcxcT;
nbintxcxq = nbintxcxqT;
nbintxqxqLoc = nbintxqxqLocT;

// take care of potentially high numbers! Use two long to ensure enough space in most cases (up to 128 interaction terms in each class)
int nbintxcxc1;
int nbintxcxc2;
if (nbintxcxc>1) {
 nbintxcxc1= nbintxcxc/2;
 nbintxcxc2 = nbintxcxc-nbintxcxc1;
} else {
 nbintxcxc1= nbintxcxc;
 nbintxcxc2 = 0;
}
int nbintxcxq1;
int nbintxcxq2;
if (nbintxcxq>1) {
 nbintxcxq1= nbintxcxq/2;
 nbintxcxq2 = nbintxcxq-nbintxcxq1;
} else {
 nbintxcxq1= nbintxcxq;
 nbintxcxq2 = 0;
}
int nbintxqxqLoc1;
int nbintxqxqLoc2;
if (nbintxqxqLoc>1) {
 nbintxqxqLoc1= nbintxqxqLoc/2;
 nbintxqxqLoc2 = nbintxqxqLoc-nbintxqxqLoc1;
} else {
 nbintxqxqLoc1= nbintxqxqLoc;
 nbintxqxqLoc2 = 0;
}



long nbmodsxcxc1;
long nbmodsxcxq1;
long nbmodsxcxc2;
long nbmodsxcxq2;
long nbmodsxqxqLoc1;
long nbmodsxqxqLoc2;
nbmodsxcxc1 = power(2,nbintxcxc1);  
nbmodsxcxq1 = power(2,nbintxcxq1); 
nbmodsxcxc2 = power(2,nbintxcxc2); 
nbmodsxcxq2 = power(2,nbintxcxq2);
nbmodsxqxqLoc1 = power(2,nbintxqxqLoc1); 
nbmodsxqxqLoc2 = power(2,nbintxqxqLoc2);

// ************************************************************
// We are now ready to proceed
		 long c1=0;
		 while (c1 < nbmodsxcxc1) {
		 	c1++;
		 	int[] modsxcxc1 = binary(c1-1, nbintxcxc1);

			long c2=0;
			while (c2 < nbmodsxcxc2) {
		 	c2++;
		 	int[] modsxcxc2 = binary(c2-1, nbintxcxc2);
			
			// go for xcxq interactions
		 	long e1 = 0;
				 while (e1 < nbmodsxcxq1) {
				 	e1++;
				 	int[] modsxcxq1 = binary(e1-1, nbintxcxq1);
					long e2=0;
					while (e2 < nbmodsxcxq2) {
				 	e2++;
				 	int[] modsxcxq2 = binary(e2-1, nbintxcxq2);
				 	
					// Finally, go for xqxq interactions
					long d1=0;
					while (d1 < nbmodsxqxqLoc1) {
					d1++;
					int[] modsxqxq1 = binary(d1-1, nbintxqxqLoc1);
					long d2=0;
					while (d2 < nbmodsxqxqLoc2) {
					d2++;
					int[] modsxqxq2 = binary(d2-1, nbintxqxqLoc2);
				int size = modsxc.length+modsxq.length+modsxcxc1.length+modsxcxc2.length+modsxcxq1.length+modsxcxq2.length+modsxqxq1.length+modsxqxq2.length;
				boolean val = (size>=minsize && (maxsize<0 || size<=maxsize));
						// evaluate model complexity
						int kkk = this.errorDF;
						kkk+= modsxqxq1.length+modsxqxq2.length;
						// scan other interactions
						int atoadd = a-1;
						int btoadd = b-1;
						for (int i=0; i<modsxcxc1.length;i++) { kkk+= this.nlevels[intxcxc[0][modsxcxc1[i]]]*this.nlevels[intxcxc[1][modsxcxc1[i]]]; atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[0][modsxcxc1[i]]+1); atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[1][modsxcxc1[i]]+1);}
						for (int i=0; i<modsxcxc2.length;i++) { kkk+= this.nlevels[intxcxc[0][modsxcxc2[i]+nbintxcxc1]]*this.nlevels[intxcxc[1][modsxcxc2[i]+nbintxcxc1]]; atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[0][modsxcxc2[i]+nbintxcxc1]+1); atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[1][modsxcxc2[i]+nbintxcxc1]+1);}
						for (int i=0; i<modsxcxq1.length;i++) { kkk+= this.nlevels[intxcxq[0][modsxcxq1[i]]]; btoadd = (int)GLMModel.setLocusToZero(btoadd,intxcxq[1][modsxcxq1[i]]+1);}
						for (int i=0; i<modsxcxq2.length;i++) { kkk+= this.nlevels[intxcxq[0][modsxcxq2[i]+nbintxcxq1]]; btoadd = (int)GLMModel.setLocusToZero(btoadd,intxcxq[1][modsxcxq2[i]+nbintxcxq1]+1);}
						// add non implied main effects
						kkk += Integer.bitCount(btoadd);
						for (int y=0; y<nc; y++) if (readLocus(atoadd,y+1)==1l) kkk += this.nlevels[y];
						// take care of intercept trick
						if (modsxc.length+modsxcxc1.length+modsxcxc2.length == 0 && this.interc.equals("1")) kkk++;
						// check that constraints are verified
						if (kkk<mincplx || (maxcplx>-1 && kkk>maxcplx)) val = false;
				if (val) {
				currmod++;
				if (currmod>ModelGenerator.maxmods) return -1;
				}
		}
			
}}}}}}}}}
// over!
return (int)currmod;
}






// ************************************************************************
// ************************************************************************
// ************************************************************************
// ************************************************************************
// ************************************************************************
// *************************************************************** 
//  HOLISTIC SCREENING APPROACH


public void run() {
	// starts producing models iteratively in a separate thread
	// since this function must have one and only one name, it is splitted in two with an if, depending on whether we apply the marginality rule or not

int counter=modfrom;
int modstored = 0;

if (!margot) {
	////////////////////////////////////////////////////  no marginality
int a= 0;

while (a < nbmodsxc) {
	a++;
	int[] modsxc = binary(a-1, nc);
	// check for exclusions
	if (((a-1)&ano) == 0) {
	int b=0;
	
	 while (b < nbmodsxq) {
		 b++;
		 int[] modsxq = binary(b-1, nq);
	// check for exclusions
	if (((b-1)&bno) == 0) {
		
// ************************************************************************
// at this stage we define the set of xcxc and xcxq interactions to consider		 
		 
int nbxc = modsxc.length;
int nbxq = modsxq.length;

// this is without any exclusion
int nbintxcxc = 0; 
if (order==2) nbintxcxc = combi(nbxc);
int nbintxcxq = 0;
if (order==2) nbintxcxq = nc*nbxq;
	
int[][] intxcxc;
int[][] intxcxq;

intxcxc= new int[2][nbintxcxc];
intxcxq= new int[2][nbintxcxq];

// True numbers of interactions (taking exclusions into account)
int nbintxcxcT = 0;
int nbintxcxqT = 0;

// proceed and ignore exclusions

if (nbintxcxc>0) {
int ind=0;
for (int i=0; i<nbxc; i++) for (int j=0; j<nbxc; j++) if (i>j) {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxcxc; e++) if (forbxcxc[0][e]==modsxc[i] && forbxcxc[1][e]==modsxc[j]) {exclu = true; break;}
if (!exclu) {
intxcxc[0][ind] = modsxc[i];
intxcxc[1][ind] = modsxc[j];
ind++;
}
}
nbintxcxcT = ind;
}


if (nbintxcxq>0) {
int ind=0;
for (int i=0; i<nc; i++) for (int j=0; j<nbxq; j++)  {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxcxq; e++) if (forbxcxq[0][e]==i && forbxcxq[1][e]==modsxq[j]) {exclu = true; break;}
if (!exclu) {	
intxcxq[0][ind] = i;
intxcxq[1][ind] = modsxq[j];
ind++;
}}
nbintxcxqT = ind;
}

// correct numbers for exclusions
nbintxcxc = nbintxcxcT;
nbintxcxq = nbintxcxqT;

// take care of potentially high numbers! Use two long to ensure enough space in most cases (up to 128 interaction terms in each class)
int nbintxcxc1;
int nbintxcxc2;
if (nbintxcxc>1) {
 nbintxcxc1= nbintxcxc/2;
 nbintxcxc2 = nbintxcxc-nbintxcxc1;
} else {
 nbintxcxc1= nbintxcxc;
 nbintxcxc2 = 0;
}
int nbintxcxq1;
int nbintxcxq2;
if (nbintxcxq>1) {
 nbintxcxq1= nbintxcxq/2;
 nbintxcxq2 = nbintxcxq-nbintxcxq1;
} else {
 nbintxcxq1= nbintxcxq;
 nbintxcxq2 = 0;
}

long nbmodsxcxc1;
long nbmodsxcxq1;
long nbmodsxcxc2;
long nbmodsxcxq2;
nbmodsxcxc1 = power(2,nbintxcxc1);  
nbmodsxcxq1 = power(2,nbintxcxq1); 
nbmodsxcxc2 = power(2,nbintxcxc2); 
nbmodsxcxq2 = power(2,nbintxcxq2);

// ************************************************************
// We are now ready to proceed
		 long c1=0;
		 while (c1 < nbmodsxcxc1) {
		 	c1++;
		 	int[] modsxcxc1 = binary(c1-1, nbintxcxc1);

			long c2=0;
			while (c2 < nbmodsxcxc2) {
		 	c2++;
		 	int[] modsxcxc2 = binary(c2-1, nbintxcxc2);
			
			// go for xcxq interactions
		 	long e1 = 0;
				 while (e1 < nbmodsxcxq1) {
				 	e1++;
				 	int[] modsxcxq1 = binary(e1-1, nbintxcxq1);
					long e2=0;
					while (e2 < nbmodsxcxq2) {
				 	e2++;
				 	int[] modsxcxq2 = binary(e2-1, nbintxcxq2);
				 	
					// Finally, go for xqxq interactions
					long d1=0;
					while (d1 < nbmodsxqxq1) {
					d1++;
					int[] modsxqxq1 = binary(d1-1, nbintxqxq1);
					long d2=0;
					while (d2 < nbmodsxqxq2) {
					d2++;
					int[] modsxqxq2 = binary(d2-1, nbintxqxq2);
				if(Thread.currentThread()!= dadou) return;	
				int size = modsxc.length+modsxq.length+modsxcxc1.length+modsxcxc2.length+modsxcxq1.length+modsxcxq2.length+modsxqxq1.length+modsxqxq2.length;
				boolean val = (size>=minsize && (maxsize<0 || size<=maxsize));
					// should we evaluate model complexity?
					if (cplxlim) {
						// evaluate model complexity
						int kkk = this.errorDF;
						kkk+= modsxqxq1.length+modsxqxq2.length;
						// scan other interactions
						int atoadd = a-1;
						int btoadd = b-1;
						for (int i=0; i<modsxcxc1.length;i++) { kkk+= this.nlevels[intxcxc[0][modsxcxc1[i]]]*this.nlevels[intxcxc[1][modsxcxc1[i]]]; atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[0][modsxcxc1[i]]+1); atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[1][modsxcxc1[i]]+1);}
						for (int i=0; i<modsxcxc2.length;i++) { kkk+= this.nlevels[intxcxc[0][modsxcxc2[i]+nbintxcxc1]]*this.nlevels[intxcxc[1][modsxcxc2[i]+nbintxcxc1]]; atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[0][modsxcxc2[i]+nbintxcxc1]+1); atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[1][modsxcxc2[i]+nbintxcxc1]+1);}
						for (int i=0; i<modsxcxq1.length;i++) { kkk+= this.nlevels[intxcxq[0][modsxcxq1[i]]]; btoadd = (int)GLMModel.setLocusToZero(btoadd,intxcxq[1][modsxcxq1[i]]+1);}
						for (int i=0; i<modsxcxq2.length;i++) { kkk+= this.nlevels[intxcxq[0][modsxcxq2[i]+nbintxcxq1]]; btoadd = (int)GLMModel.setLocusToZero(btoadd,intxcxq[1][modsxcxq2[i]+nbintxcxq1]+1);}
						// add non implied main effects
						kkk += Integer.bitCount(btoadd);
						for (int y=0; y<nc; y++) if (readLocus(atoadd,y+1)==1l) kkk += this.nlevels[y];
						// take care of intercept trick
						if (modsxc.length+modsxcxc1.length+modsxcxc2.length == 0 && this.interc.equals("1")) kkk++;
						// check that constraints are verified
						if (kkk<mincplx || kkk>maxcplx) val = false;
					}
				if (val) {
					// is it a model to be treated in this chunk?
					if (counter < mstep) {
						// no it is not
						counter++;
				} else {
					counter=1; // resets the counter
					// yes it is
				try {
					while(this.proceed== false && Thread.currentThread()== dadou) {
					Thread.sleep(10l);
				}
			    } catch(InterruptedException rr) {return;}
				currmodR++;
				StringBuffer temp = new StringBuffer(resp+"~"+interc);
				for (int i=0; i<modsxc.length;i++) temp.append("+ " + this.xc[modsxc[i]]);
				for (int i=0; i<modsxq.length;i++) temp.append("+ "+ this.xq[modsxq[i]]);
				for (int i=0; i<modsxcxc1.length;i++) temp.append("+ "+this.xc[intxcxc[0][modsxcxc1[i]]]+":"+this.xc[intxcxc[1][modsxcxc1[i]]]);
				for (int i=0; i<modsxcxc2.length;i++) temp.append("+ "+this.xc[intxcxc[0][modsxcxc2[i]+nbintxcxc1]]+":"+this.xc[intxcxc[1][modsxcxc2[i]+nbintxcxc1]]);
				for (int i=0; i<modsxqxq1.length;i++) temp.append("+ "+this.xq[intxqxq[0][modsxqxq1[i]]]+":"+this.xq[intxqxq[1][modsxqxq1[i]]]);
				for (int i=0; i<modsxqxq2.length;i++) temp.append("+ "+this.xq[intxqxq[0][modsxqxq2[i]+nbintxqxq1]]+":"+this.xq[intxqxq[1][modsxqxq2[i]+nbintxqxq1]]);
				for (int i=0; i<modsxcxq1.length;i++) temp.append("+ "+this.xc[intxcxq[0][modsxcxq1[i]]]+":"+this.xq[intxcxq[1][modsxcxq1[i]]]);
				for (int i=0; i<modsxcxq2.length;i++) temp.append("+ "+this.xc[intxcxq[0][modsxcxq2[i]+nbintxcxq1]]+":"+this.xq[intxcxq[1][modsxcxq2[i]+nbintxcxq1]]);
				this.currmodString[modstored] = temp.toString();
				
				StringBuffer temp2 = new StringBuffer();
				if (nc>0) {
				temp2.append("X");
				for (int i=0; i<nc; i++) temp2.append("\t"+Long.toString(readLocus(a-1,i+1))); 
				}
				if (nq>0) {
				if (nc>0) temp2.append("\tX"); else temp2.append("X");
				for (int i=0; i<nq; i++) temp2.append("\t"+Long.toString(readLocus(b-1,i+1)));
				}
				if (this.order==2) {
						if (nbintxcxcG>0) {
						temp2.append("\tX");
						boolean[] truexcxc = new boolean[nbintxcxcG];
						for (int u=0; u<nbintxcxcG; u++) truexcxc[u]=false;
						for (int u=0; u<modsxcxc1.length; u++) {
							truexcxc[(intxcxc[0][modsxcxc1[u]]*(intxcxc[0][modsxcxc1[u]]-1))/2+intxcxc[1][modsxcxc1[u]]]=true;
						}
						for (int u=0; u<modsxcxc2.length; u++) {
							truexcxc[(intxcxc[0][modsxcxc2[u]+nbintxcxc1]*(intxcxc[0][modsxcxc2[u]+nbintxcxc1]-1))/2+intxcxc[1][modsxcxc2[u]+nbintxcxc1]]=true;
						}
						
						for (int i=0; i<nbintxcxcG; i++) temp2.append("\t"+(truexcxc[i]? 1 : 0));
						}
						
						if (nbintxqxq>0) {
						temp2.append("\tX");
						for (int i=0; i<nbintxqxq1; i++) temp2.append("\t"+Long.toString(readLocus(d1-1,i+1)));
						for (int i=0; i<nbintxqxq2; i++) temp2.append("\t"+Long.toString(readLocus(d2-1,i+1)));
						}
						
						if (nbintxcxqG >0) {
						temp2.append("\tX");
						boolean[] truexcxq = new boolean[nbintxcxqG];
						for (int u=0; u<nbintxcxqG; u++) truexcxq[u]=false;
						for (int u=0; u<modsxcxq1.length; u++) {
							truexcxq[(intxcxq[0][modsxcxq1[u]]*nq)+intxcxq[1][modsxcxq1[u]]]=true;
						}
						for (int u=0; u<modsxcxq2.length; u++) {
							truexcxq[(intxcxq[0][modsxcxq2[u]+nbintxcxq1]*nq)+intxcxq[1][modsxcxq2[u]+nbintxcxq1]]=true;
						}
					
						for (int i=0; i<nbintxcxqG; i++)  temp2.append("\t"+(truexcxq[i]? 1 : 0));
						}
				}
				this.currtermsString[modstored++]  = temp2.toString();
				if (modstored == (bunch-1)) {
					this.updated=true;
					this.proceed=false;
					modstored = 0;
					}
			}}
		}
			
}}}}}}}}}
// over!
this.over=true;
for (int hh=modstored; hh<bunch; hh++) {
	this.currtermsString[hh]=null;
	this.currmodString[hh]=null;
}
this.updated=true;
this.proceed=false;
modstored = 0;
return;	
	
} else {
	///////////////////////////////////////////////// with marginality
int a=0;

while (a < nbmodsxc) {
	a++;
	int[] modsxc = binary(a-1, nc);
	// check for exclusions
	if (((a-1)&ano) == 0) {
	int b=0;
	
	 while (b < nbmodsxq) {
		 b++;
		 int[] modsxq = binary(b-1, nq);
	// check for exclusions
	if (((b-1)&bno) == 0) {
		
// ************************************************************************
// at this stage we define the set of xcxc and xcxq interactions to consider		 
int nbxc = modsxc.length;
int nbxq = modsxq.length; 
// this is without any exclusion
int nbintxcxc = 0; 
if (order==2) nbintxcxc = combi(nbxc);
int nbintxcxq = 0;
if (order==2) nbintxcxq = nbxc*nbxq;
int nbintxqxqLoc = 0;
if (order==2) nbintxqxqLoc = combi(nbxq);

	
int[][] intxcxc;
int[][] intxcxq;
int[][] intxqxqLoc;

intxcxc= new int[2][nbintxcxc];
intxcxq= new int[2][nbintxcxq];
intxqxqLoc= new int[2][nbintxqxqLoc];

// True numbers of interactions we are about to compute (taking exclusions into account)
int nbintxcxcT = 0;
int nbintxcxqT = 0;
int nbintxqxqLocT = 0;

// proceed and ignore exclusions

if (nbintxcxc>0) {
int ind=0;
for (int i=0; i<nbxc; i++) for (int j=0; j<nbxc; j++) if (i>j) {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxcxc; e++) if (forbxcxc[0][e]==modsxc[i] && forbxcxc[1][e]==modsxc[j]) {exclu = true; break;}
if (!exclu) {
intxcxc[0][ind] = modsxc[i];
intxcxc[1][ind] = modsxc[j];
ind++;
}
}
nbintxcxcT = ind;
}


if (nbintxcxq>0) {
int ind=0;
for (int i=0; i<nbxc; i++) for (int j=0; j<nbxq; j++)  {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxcxq; e++) if (forbxcxq[0][e]==modsxc[i] && forbxcxq[1][e]==modsxq[j]) {exclu = true; break;}
if (!exclu) {	
intxcxq[0][ind] = modsxc[i];
intxcxq[1][ind] = modsxq[j];
ind++;
}}
nbintxcxqT = ind;
}


if (nbintxqxqLoc>0) {
int ind=0;
for (int i=0; i<nbxq; i++) for (int j=0; j<nbxq; j++) if (i>j) {
	// check exclusions
	boolean exclu = false;
	for (int e=0; e<nbforbxqxq; e++) if (forbxqxq[0][e]==modsxq[i] && forbxqxq[1][e]==modsxq[j]) {exclu = true; break;}
if (!exclu) {	
intxqxqLoc[0][ind] = modsxq[i];
intxqxqLoc[1][ind] = modsxq[j];
ind++;
}}
nbintxqxqLocT = ind;
}



// correct numbers for exclusions
nbintxcxc = nbintxcxcT;
nbintxcxq = nbintxcxqT;
nbintxqxqLoc = nbintxqxqLocT;

// take care of potentially high numbers! Use two long to ensure enough space in most cases (up to 128 interaction terms in each class)
int nbintxcxc1;
int nbintxcxc2;
if (nbintxcxc>1) {
 nbintxcxc1= nbintxcxc/2;
 nbintxcxc2 = nbintxcxc-nbintxcxc1;
} else {
 nbintxcxc1= nbintxcxc;
 nbintxcxc2 = 0;
}
int nbintxcxq1;
int nbintxcxq2;
if (nbintxcxq>1) {
 nbintxcxq1= nbintxcxq/2;
 nbintxcxq2 = nbintxcxq-nbintxcxq1;
} else {
 nbintxcxq1= nbintxcxq;
 nbintxcxq2 = 0;
}
int nbintxqxqLoc1;
int nbintxqxqLoc2;
if (nbintxqxqLoc>1) {
 nbintxqxqLoc1= nbintxqxqLoc/2;
 nbintxqxqLoc2 = nbintxqxqLoc-nbintxqxqLoc1;
} else {
 nbintxqxqLoc1= nbintxqxqLoc;
 nbintxqxqLoc2 = 0;
}



long nbmodsxcxc1;
long nbmodsxcxq1;
long nbmodsxcxc2;
long nbmodsxcxq2;
long nbmodsxqxqLoc1;
long nbmodsxqxqLoc2;
nbmodsxcxc1 = power(2,nbintxcxc1);  
nbmodsxcxq1 = power(2,nbintxcxq1); 
nbmodsxcxc2 = power(2,nbintxcxc2); 
nbmodsxcxq2 = power(2,nbintxcxq2);
nbmodsxqxqLoc1 = power(2,nbintxqxqLoc1); 
nbmodsxqxqLoc2 = power(2,nbintxqxqLoc2);
	

// ************************************************************
// We are now ready to proceed
		 long c1=0;
		 while (c1 < nbmodsxcxc1) {
		 	c1++;
		 	int[] modsxcxc1 = binary(c1-1, nbintxcxc1);

			long c2=0;
			while (c2 < nbmodsxcxc2) {
		 	c2++;
		 	int[] modsxcxc2 = binary(c2-1, nbintxcxc2);
			
			// go for xcxq interactions
		 	long e1 = 0;
				 while (e1 < nbmodsxcxq1) {
				 	e1++;
				 	int[] modsxcxq1 = binary(e1-1, nbintxcxq1);
					long e2=0;
					while (e2 < nbmodsxcxq2) {
				 	e2++;
				 	int[] modsxcxq2 = binary(e2-1, nbintxcxq2);
				 	
					// Finally, go for xqxq interactions
					long d1=0;
					while (d1 < nbmodsxqxqLoc1) {
					d1++;
					int[] modsxqxq1 = binary(d1-1, nbintxqxqLoc1);
					long d2 = 0;
					while (d2 < nbmodsxqxqLoc2) {
					d2++;
					int[] modsxqxq2 = binary(d2-1, nbintxqxqLoc2);
				if(Thread.currentThread()!= dadou) return;	
				int size = modsxc.length+modsxq.length+modsxcxc1.length+modsxcxc2.length+modsxcxq1.length+modsxcxq2.length+modsxqxq1.length+modsxqxq2.length;
				boolean val = (size>=minsize && (maxsize<0 || size<=maxsize));
					// should we evaluate model complexity?
					if (cplxlim) {
						// evaluate model complexity
						int kkk = this.errorDF;
						kkk+= modsxqxq1.length+modsxqxq2.length;
						// scan other interactions
						int atoadd = a-1;
						int btoadd = b-1;
						for (int i=0; i<modsxcxc1.length;i++) { kkk+= this.nlevels[intxcxc[0][modsxcxc1[i]]]*this.nlevels[intxcxc[1][modsxcxc1[i]]]; atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[0][modsxcxc1[i]]+1); atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[1][modsxcxc1[i]]+1);}
						for (int i=0; i<modsxcxc2.length;i++) { kkk+= this.nlevels[intxcxc[0][modsxcxc2[i]+nbintxcxc1]]*this.nlevels[intxcxc[1][modsxcxc2[i]+nbintxcxc1]]; atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[0][modsxcxc2[i]+nbintxcxc1]+1); atoadd = (int)GLMModel.setLocusToZero(atoadd,intxcxc[1][modsxcxc2[i]+nbintxcxc1]+1);}
						for (int i=0; i<modsxcxq1.length;i++) { kkk+= this.nlevels[intxcxq[0][modsxcxq1[i]]]; btoadd = (int)GLMModel.setLocusToZero(btoadd,intxcxq[1][modsxcxq1[i]]+1);}
						for (int i=0; i<modsxcxq2.length;i++) { kkk+= this.nlevels[intxcxq[0][modsxcxq2[i]+nbintxcxq1]]; btoadd = (int)GLMModel.setLocusToZero(btoadd,intxcxq[1][modsxcxq2[i]+nbintxcxq1]+1);}
						// add non implied main effects
						kkk += Integer.bitCount(btoadd);
						for (int y=0; y<nc; y++) if (readLocus(atoadd,y+1)==1l) kkk += this.nlevels[y];
						// take care of intercept trick
						if (modsxc.length+modsxcxc1.length+modsxcxc2.length == 0 && this.interc.equals("1")) kkk++;
						// check that constraints are verified
						if (kkk<mincplx || kkk>maxcplx) val = false;
					}
				if (val) {
					// is it a model to be treated in this chunk?
					if (counter < mstep) {
						// no it is not
						counter++;
				} else {
					counter=1; // resets the counter
					// yes it is
				// update String representation of current model!
				try {
					while(this.proceed== false && Thread.currentThread()== dadou) {
					Thread.sleep(10l);
				}
			    } catch(InterruptedException rr) {return;}
				currmodR++;
				StringBuffer temp = new StringBuffer(resp+"~"+interc);
				for (int i=0; i<modsxc.length;i++) temp.append("+ " + this.xc[modsxc[i]]);
				for (int i=0; i<modsxq.length;i++) temp.append("+ "+ this.xq[modsxq[i]]);
				for (int i=0; i<modsxcxc1.length;i++) temp.append("+ "+this.xc[intxcxc[0][modsxcxc1[i]]]+":"+this.xc[intxcxc[1][modsxcxc1[i]]]);
				for (int i=0; i<modsxcxc2.length;i++) temp.append("+ "+this.xc[intxcxc[0][modsxcxc2[i]+nbintxcxc1]]+":"+this.xc[intxcxc[1][modsxcxc2[i]+nbintxcxc1]]);
				for (int i=0; i<modsxqxq1.length;i++) temp.append("+ "+this.xq[intxqxqLoc[0][modsxqxq1[i]]]+":"+this.xq[intxqxqLoc[1][modsxqxq1[i]]]);
				for (int i=0; i<modsxqxq2.length;i++) temp.append("+ "+this.xq[intxqxqLoc[0][modsxqxq2[i]+nbintxqxqLoc1]]+":"+this.xq[intxqxqLoc[1][modsxqxq2[i]+nbintxqxqLoc1]]);
				for (int i=0; i<modsxcxq1.length;i++) temp.append("+ "+this.xc[intxcxq[0][modsxcxq1[i]]]+":"+this.xq[intxcxq[1][modsxcxq1[i]]]);
				for (int i=0; i<modsxcxq2.length;i++) temp.append("+ "+this.xc[intxcxq[0][modsxcxq2[i]+nbintxcxq1]]+":"+this.xq[intxcxq[1][modsxcxq2[i]+nbintxcxq1]]);
				this.currmodString[modstored] = temp.toString();
				
				StringBuffer temp2 = new StringBuffer();
				if (nc>0) {
				temp2.append("X");
				for (int i=0; i<nc; i++) temp2.append("\t"+Long.toString(readLocus(a-1,i+1))); 
				}
				if (nq>0) {
				if (nc>0) temp2.append("\tX"); else temp2.append("X");
				for (int i=0; i<nq; i++) temp2.append("\t"+Long.toString(readLocus(b-1,i+1)));
				}
				if (this.order==2) {
						if (nbintxcxcG>0) {
						temp2.append("\tX");
						boolean[] truexcxc = new boolean[nbintxcxcG];
						for (int u=0; u<nbintxcxcG; u++) truexcxc[u]=false;
						for (int u=0; u<modsxcxc1.length; u++) {
							truexcxc[(intxcxc[0][modsxcxc1[u]]*(intxcxc[0][modsxcxc1[u]]-1))/2+intxcxc[1][modsxcxc1[u]]]=true;
						}
						for (int u=0; u<modsxcxc2.length; u++) {
							truexcxc[(intxcxc[0][modsxcxc2[u]+nbintxcxc1]*(intxcxc[0][modsxcxc2[u]+nbintxcxc1]-1))/2+intxcxc[1][modsxcxc2[u]+nbintxcxc1]]=true;
						}
						
						for (int i=0; i<nbintxcxcG; i++) temp2.append("\t"+(truexcxc[i]? 1 : 0));
						}
						
						if (nbintxqxq>0) {
						temp2.append("\tX");
						boolean[] truexqxq = new boolean[nbintxqxq];
						for (int u=0; u<nbintxqxq; u++) truexqxq[u]=false;
						for (int u=0; u<modsxqxq1.length; u++) {
							truexqxq[(intxqxqLoc[0][modsxqxq1[u]]*(intxqxqLoc[0][modsxqxq1[u]]-1))/2+intxqxqLoc[1][modsxqxq1[u]]]=true;
						}
						for (int u=0; u<modsxqxq2.length; u++) {
							truexqxq[(intxqxqLoc[0][modsxqxq2[u]+nbintxqxqLoc1]*(intxqxqLoc[0][modsxqxq2[u]+nbintxqxqLoc1]-1))/2+intxqxqLoc[1][modsxqxq2[u]+nbintxqxqLoc1]]=true;
						}
					
						for (int i=0; i<nbintxqxq; i++)  temp2.append("\t"+(truexqxq[i]? 1 : 0));
						}
						
						if (nbintxcxqG >0) {
						temp2.append("\tX");
						boolean[] truexcxq = new boolean[nbintxcxqG];
						for (int u=0; u<nbintxcxqG; u++) truexcxq[u]=false;
						for (int u=0; u<modsxcxq1.length; u++) {
							truexcxq[(intxcxq[0][modsxcxq1[u]]*nq)+intxcxq[1][modsxcxq1[u]]]=true;
						}
						for (int u=0; u<modsxcxq2.length; u++) {
							truexcxq[(intxcxq[0][modsxcxq2[u]+nbintxcxq1]*nq)+intxcxq[1][modsxcxq2[u]+nbintxcxq1]]=true;
						}
					
						for (int i=0; i<nbintxcxqG; i++)  temp2.append("\t"+(truexcxq[i]? 1 : 0));
						}
				}
				this.currtermsString[modstored++] = temp2.toString();
				if (modstored == (bunch-1)) {
					this.updated=true;
					this.proceed=false;
					modstored = 0;
					}			
			}}
		}
			
}}}}}}}}}
// over!
this.over=true;
for (int hh=modstored; hh<bunch; hh++) {
	this.currtermsString[hh]=null;
	this.currmodString[hh]=null;
}
this.updated=true;
this.proceed=false;
modstored = 0;
return;	
	
	
	
	
	
}
// end of run
}



public boolean produceModels(int chunk, int chunks, int bunchy) {
	// launches the model-producing thread
	if (ok) {
	try {
	this.bunch = bunchy;
	this.currmodR =0;
	this.updated = false;
	this.proceed = false;
	this.over=false;
	this.currmodString = new String[bunch];
	this.currtermsString = new String[bunch];
	this.dadou = new Thread(this);
	GLMModel.papa = this;
	// take care of splitting
	// splitting of the loop is done with an iterator in the loops
	this.mstep=chunks;
	this.modfrom=chunk;
	dadou.start();
	return true;
    } catch(IllegalThreadStateException  rr) {
		return false;
	}
    } else return false;
}



public boolean nextModel() {
	// tells the thread to update the string representations of the current candidate models, for R to read them
	 if (this.over) return false;
	 else {
	 	this.proceed=true;
		this.updated=false;
		return true;
	}
}


public String[] getCurrModel() {
	 try {
		while(!updated) {Thread.sleep(10);};
	return this.currmodString;
	} catch(InterruptedException rr) {return new String[1];}
}


public String[] getCurrTerms() {
	try {	while(!updated) {Thread.sleep(10);};
	return this.currtermsString;
	} catch(InterruptedException rr) {return new String[1];}
}


public void stopModels() {
	this.proceed=false;
	this.updated=false;
	this.dadou=null;
	this.over= true;
}





// ************************************************************************
// ************************************************************************
// ************************************************************************
// ************************************************************************
// ************************************************************************
// *************************************************************** 
// ************************************************
//  GENETIC ALGORITHM (BETTER FOR EXTREMELY LARGE CANDIDATE SETS)




public String[] initPop(int popsz, double mutrate, double imm, double sex, int confss, String namou) throws IOException, NotSerializableException, InvalidClassException {
	// Initiate a new population of models (created randomly)
	this.popsize=popsz;
	this.confsetsize = confss;
	ModelGenerator.buffersize = 3*popsize;
	GLMModel.init(nc,nq,this.order,mutrate,this);
	this.mutrate = mutrate;
	this.imm = imm;
	this.sex=sex;
	this.toeval = new int[popsize];
	this.fifi = new double[popsize];
	 nbsex = (int)Math.ceil(popsize*sex);
	 nbimm = (int)Math.ceil(popsize*imm);
	 nbasex = popsize -nbimm - nbsex;
	 nbasex = (nbasex<0)? 0 : nbasex;
	 this.confsetsize=confsetsize;
	confset = new GLMModel[confsetsize];
	sel = 0;
	currgen = 0L;
	zebest=new GLMModel();
	zebest.setIC(10000000d);
	this.buffer = new GLMModel[ModelGenerator.buffersize];
	this.currposinbuffer = 0;
	this.buffered = 0;
	// serialize this ModelGenerator and init the Object output Stream
	(new ObjectOutputStream(new FileOutputStream(new File(namou+".modgen.back")))).writeObject(this);
	this.namou = namou;
	// Make initial pop
	this.pop = new GLMModel[popsize];
	for (int i=0; i<popsize; i++) {
		pop[i] = new GLMModel(this);
	}
	
	// proceed and send request to R
	return manageMods();
}

public String[] initPopAgain(double mutrate, double imm, double sex, String namou)  {
	// this resumes a genetic algorithm from preexisting objects. This is used with method "r"
	this.mutrate = mutrate;
	this.imm = imm;
	this.sex = sex;
	this.namou = namou;
	 nbsex = (int)Math.ceil(popsize*sex);
	 nbimm = (int)Math.ceil(popsize*imm);
	 nbasex = popsize -nbimm - nbsex;
	 nbasex = (nbasex<0)? 0 : nbasex;
	GLMModel.init(nc,nq,this.order,mutrate,this);
	sel = this.confset.length;
	this.buffer = new GLMModel[ModelGenerator.buffersize];
	this.currposinbuffer = 0;
	this.buffered = 0;
	// Make the "not quite initial" pop
	// The popsize first models from the confset are taken (...), supplemented by random models if necessary
	this.pop = new GLMModel[popsize];
	if (sel>=popsize) for (int i=0; i<popsize; i++) 	pop[i] = confset[i];
	else {
		for (int i=0; i<sel; i++) 	pop[i] = confset[i];
		for (int i=sel; i<popsize; i++) 	pop[i] = new GLMModel(this);
	}
	
	// proceed and send request to R
	return manageMods();

}





public String[] manageMods() {
   // inspects population of models: finds duplicates, looks into the buffer, prepares request for R about unknown models
	for (int i=0; i<popsize; i++) {
		toeval[i]= 0;
		fifi[i] = -1d;
	}
	int neo = 0;
	// 1. Identify different models by coloring them
	for (int i=0; i<popsize; i++) 
		for (int j=i+1; j<popsize; j++) 
			if (toeval[i]==0 && toeval[j] == 0 && pop[i].sameas(pop[j])) toeval[j]=i+1; 
	// only models with 0 in color are "originals"
	// 2. evaluate unique models
	boolean found;
	for (int i=0; i<popsize; i++) 
	 if (toeval[i] == 0) {
	 	found = false;
		
		// first look into confidence set
	 	for (int j=0; j<sel; j++) if (pop[i].sameas(confset[j])) {
	 		// found in conf set
	 		fifi[i] = confset[j].ic;
	 		toeval[i] = -1; // it is already there so no need to consider it for addition/evaluation
	 		found = true;
	 		break;
		}
	 	// then look into buffer just in case
	 	if (!found)  for (int j=0; j<buffered; j++) if (pop[i].sameas(buffer[j])) {
	 		// found in buffer: no need to reevaluate but may be worth adding to confset later on
	 		fifi[i] = buffer[j].ic;
	 		toeval[i] = -3; // flag -3 : no need to evaluate in R but may be worh for confset 
	 		found = true;
	 		break;
		}
		
		// if new model, must be evaluated in R...
		if (!found) {
			toeval[i] = 0;
			neo++;	
		}
	}
	//System.out.println(neo);
	// 3. prepare for R sending
	String[] robert = new String[neo]; 
	int curev = 0;
	for (int i=0; i<popsize; i++) {
		if (toeval[i]==0) {
			// to evaluate
			robert[curev++] = pop[i].toFormula();
		} else if (toeval[i]>0) {
			// colored: take fields from duplicate, if available
			if (toeval[toeval[i]-1]== -1) { 
				fifi[i] =  fifi[toeval[i]-1];
				toeval[i] = -1;
		}
		} // otherwise values will be replaced after evaluation by R
	}
	
	return robert;
}


public String[] nextGeneration(double[] supports) {
	// Creates a new population of models by selective reproduction and random immigration
	// first complete fitness and parameters tabs from what R told
	int neo = 0;
	for (int i=0; i<popsize; i++) if (toeval[i] == 0) {
		// read new value computed by R
		// flag with -2 (just computed, i.e. fresh data)
		fifi[i] = supports[neo++];
		toeval[i] = -2; 
			} else if (toeval[i] > 0) {
		// replicate value from before
		fifi[i] = fifi[toeval[i]-1];
		toeval[i] = -1;
	}
		
	if (currgen%DELTAR==0) {
	// populate the growing confidence set at regular intervals
		for (int n=0; n<popsize;n++) if (toeval[n] <= -2) {
		// only consider those models that were not found in the conf set earlier 
			if (sel<confsetsize) {
				pop[n].setIC(fifi[n]);
				confset[sel]=pop[n];
				if (fifi[n]<zebest.ic) zebest=confset[sel];
				sel++;
			} else {
			int wsf = 0;
			for (int v=1; v<sel; v++) if (confset[v].ic>confset[wsf].ic) wsf=v;
			if (fifi[n]<confset[wsf].ic) {
				pop[n].setIC(fifi[n]);
				confset[wsf]=pop[n];
				if (fifi[n]<zebest.ic) zebest=confset[wsf];
			}
			}
		}
	} 
	
	// update the buffer
	for (int n=0; n<popsize;n++) if (toeval[n] == -2) {
	// only fresh material to be put there
		pop[n].setIC(fifi[n]);
		buffer[currposinbuffer] = pop[n];
		if (buffered<buffersize) buffered++;
		currposinbuffer++;
		if (currposinbuffer == buffersize) currposinbuffer=0; 
	}
	
	// next handle fitnesses
	double bestic = fifi[0];
	for (int i=1; i<popsize; i++) if (fifi[i]<bestic) bestic=fifi[i];

	// proceed to next gen
	double[] dsupp = new double[popsize];
	for (int i=1; i<popsize; i++) dsupp[i]=fifi[i]-bestic;
	GLMModel.fitness(dsupp);
	// produce new Pop
	GLMModel[] offsprings = new GLMModel[popsize];
	// asexual reproduction
	for (int i=0; i<nbasex; i++) {
		// select father
		int f = choose(dsupp);
		//reproduce
		offsprings[i]=pop[f].mutate();
	}
	// sexual reproduction
	for (int i=0; i<nbsex; i++) {
		//select parents
		int f = choose(dsupp);
		int m = choose(dsupp);
		// mate
		offsprings[i+nbasex]=pop[f].mutate(pop[m]);
	}
	// immigration
	for (int i=0; i<nbimm; i++) {
		offsprings[i+nbasex+nbsex] = new GLMModel(this);
	}
	this.pop = offsprings;
	currgen++;
	// manage and send request to R
	return manageMods();
}


public void printImage() throws IOException {
	// exports a file containing the binary image of the current confidence set
	// uses Java Serialization
	ObjectOutputStream koala = new ObjectOutputStream(new FileOutputStream(new File(namou+".mods.back")));
	koala.writeObject(this.confset);
	koala.close();
	return;
}



public double reportBestIC() {
	return zebest.ic;
	
}


public double reportMeanIC() {
	double m = 0d;
	for (int i=0; i<sel; i++) m+=confset[i].ic;
	return m/sel;
}

public String reportbestModel() {
	return zebest.toFormula();
	
}


public String[] reportConfMods() {
	String[] cong = new String[sel];
	for (int i=0; i<sel; i++) cong[i]=confset[i].toFormula();
	return cong;
}

public String[] reportConfCodes() {
	String[] cong = new String[sel];
	for (int i=0; i<sel; i++) cong[i]=confset[i].toRString();
	return cong;
}


public double[] reportConfIC() {
	double[] cong = new double[sel];
	for (int i=0; i<sel; i++) cong[i]=confset[i].ic;
	return cong;
}

public int[] reportConfKs() {
	int[] cong =  new int[sel];
	for (int i=0; i<sel; i++) if (confset[i].k == 0) cong[i]=confset[i].makeK(); else  cong[i]=confset[i].k;
	return cong;
	
}






}
