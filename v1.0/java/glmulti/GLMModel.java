package glmulti;

// produces glm models and combines them if needed
// models are coded as bit sequences (using longs)
// Vincent Calcagno March 2009
// updated October 20 2009
// vincentcalcagno  -a-t- mcgill -d-o-t- ca


import java.io.*;
import java.util.*;


public class GLMModel implements Serializable {
	
	int a, b;
	long c1,c2,d1,d2,e1,e2;
	double ic;
	int k;
	
	// ***************************************************************
	// ************** UTILS ******************************************
	
	static int nc, nq, lev;
	static ModelGenerator papa;
	static int nbintxqxq, nbintxqxq1,nbintxqxq2, nbintxcxc,nbintxcxc1,nbintxcxc2, nbintxcxq,nbintxcxq1,nbintxcxq2;
	static int[][] intxcxc,intxqxq,intxcxq;
	static long[] tempXCXC1, tempXCXC2, tempXCXQ1, tempXCXQ2, tempXQXQ1, tempXQXQ2, tempXCXQC1, tempXCXQC2; // implication and marginality stuff
	static double pmut;
	
		static void init(int ncv, int nqv, int lev, double mut, ModelGenerator dad) {
			// some useful precomputations
			// constants
			nc = ncv;
			nq = nqv;
			lev = lev;
			pmut = mut;
			papa = dad;
			
			nbintxqxq = papa.nbintxqxq;	
			nbintxqxq1 = papa.nbintxqxq1;
			nbintxqxq2 = papa.nbintxqxq2;
			
			nbintxcxc = (lev ==2) ? papa.nbintxcxcG - papa.nbforbxcxc : 0;
			nbintxcxq = (lev ==2) ? papa.nbintxcxqG - papa.nbforbxcxq : 0;
			// enumerate and dispatch xcxc and xcxq interactions
 
			if (nbintxcxc>1) {
			nbintxcxc1= nbintxcxc/2;
			nbintxcxc2 = nbintxcxc-nbintxcxc1;
			} else {
			nbintxcxc1= nbintxcxc;
			nbintxcxc2 = 0;	
			}
			if (nbintxcxq>1) {
			nbintxcxq1= nbintxcxq/2;
			nbintxcxq2 = nbintxcxq-nbintxcxq1;
			} else {
			nbintxcxq1= nbintxcxq;
			nbintxcxq2 = 0;	
			}  
			intxcxc= new int[2][nbintxcxc];
			intxcxq= new int[2][nbintxcxq];
			
			intxqxq = papa.intxqxq;
			
			if (nbintxcxc>0) {
			int ind=0;
			for (int i=0; i<nc; i++) for (int j=0; j<nc; j++) if (i>j) {
							// check exclusions and ignore them
							boolean exclu = false;
							for (int e=0; e<papa.nbforbxcxc; e++) if (papa.forbxcxc[0][e]==i && papa.forbxcxc[1][e]==j) {exclu = true; break;}
			if (!exclu) {

			intxcxc[0][ind] = i;
			intxcxc[1][ind] = j;
			ind++;
			}}
			}
			
			if (nbintxcxq>0) {
			int ind=0;
			for (int i=0; i<nc; i++) for (int j=0; j<nq; j++)  {
							// check exclusions and ignore them
							boolean exclu = false;
							for (int e=0; e<papa.nbforbxcxq; e++) if (papa.forbxcxq[0][e]==i && papa.forbxcxq[1][e]==j) {exclu = true; break;}
			if (!exclu) {
			intxcxq[0][ind] = i;
			intxcxq[1][ind] = j;
			ind++;
			}}   
			}
			
			         
			//templates
			tempXCXC1 = new long[nc];
			tempXCXC2 = new long[nc];
			tempXCXQ1 = new long[nq];
			tempXCXQ2 = new long[nq];
			for (int i=0; i<nc;i++) {tempXCXC1[i]=0L; tempXCXC2[i]=0L;}
			for (int i=0; i<nq;i++) {tempXCXQ1[i]=0L;tempXCXQ2[i]=0L;}
			for (int i=0; i<nbintxcxc1;i++) {
				// indicate which main xc effects are implied by this interaction
				tempXCXC1[intxcxc[0][i]]= setLocusToOne(tempXCXC1[intxcxc[0][i]],i+1);
				tempXCXC1[intxcxc[1][i]]= setLocusToOne(tempXCXC1[intxcxc[1][i]],i+1);
				}
			for (int i=0; i<nbintxcxc2;i++) {
				// indicate which main xc effects are implied by this interaction
				tempXCXC2[intxcxc[0][i+nbintxcxc1]]= setLocusToOne(tempXCXC2[intxcxc[0][i+nbintxcxc1]],i+1);
				tempXCXC2[intxcxc[1][i+nbintxcxc1]]= setLocusToOne(tempXCXC2[intxcxc[1][i+nbintxcxc1]],i+1);
				}
			for (int i=0; i<nbintxcxq1;i++) {
				// indicate which main xq effects are implied by this interaction
				tempXCXQ1[intxcxq[1][i]]= setLocusToOne(tempXCXQ1[intxcxq[1][i]],i+1);
				}
			for (int i=0; i<nbintxcxq2;i++) {
				// indicate which main xq effects are implied by this interaction
				tempXCXQ2[intxcxq[1][i+nbintxcxq1]]= setLocusToOne(tempXCXQ2[intxcxq[1][i+nbintxcxq1]],i+1);
				}
				

			if (papa.margot) {
				tempXQXQ1 = new long[nq];
				tempXQXQ2 = new long[nq];
				tempXCXQC1 = new long[nc];
				tempXCXQC2 = new long[nc];
				for (int i=0; i<nc;i++) {tempXCXQC1[i]=0L; tempXCXQC2[i]=0L;}
				// create templates for XQXQ too in this case
				for (int i=0; i<nq;i++) {tempXQXQ1[i]=0L; tempXQXQ2[i]=0L;}
				for (int i=0; i<nbintxqxq1;i++) {
				// indicate which main xq effects are implied by this interaction
				tempXQXQ1[intxqxq[0][i]]= setLocusToOne(tempXQXQ1[intxqxq[0][i]],i+1);
				tempXQXQ1[intxqxq[1][i]]= setLocusToOne(tempXQXQ1[intxqxq[1][i]],i+1);
				}
				for (int i=0; i<nbintxqxq2;i++) {
				// indicate which main xq effects are implied by this interaction
				tempXQXQ2[intxqxq[0][i+nbintxqxq1]]= setLocusToOne(tempXQXQ2[intxqxq[0][i+nbintxqxq1]],i+1);
				tempXQXQ2[intxqxq[1][i+nbintxqxq1]]= setLocusToOne(tempXQXQ2[intxqxq[1][i+nbintxqxq1]],i+1);
				}
				for (int i=0; i<nbintxcxq1;i++) {
				// indicate which main xc effects are implied by this interaction
				tempXCXQC1[intxcxq[0][i]]= setLocusToOne(tempXCXQC1[intxcxq[0][i]],i+1);
				}
				for (int i=0; i<nbintxcxq2;i++) {
				// indicate which main xc effects are implied by this interaction
				tempXCXQC2[intxcxq[0][i+nbintxcxq1]]= setLocusToOne(tempXCXQC2[intxcxq[0][i+nbintxcxq1]],i+1);
				}
			} else {
				tempXQXQ1 = new long[0];
				tempXQXQ2 = new long[0];
				tempXCXQC1 = new long[0];
				tempXCXQC2 = new long[0];
			}
				
		// Initialisation over
		}
		
		static void fitness(double[] deltasupports) {
			// computes the cumulated relative "fitness" of models in a pop given their IC
			// this (based on ER) may be modified, and is largely arbitrary 
			double tot = 0d;
			for (int i=0; i<deltasupports.length; i++) {
				deltasupports[i] = Math.exp(-deltasupports[i]);
				tot+=deltasupports[i];
				}
			deltasupports[0]/=tot;
			for (int i=1; i<deltasupports.length; i++) deltasupports[i]=deltasupports[i-1]+deltasupports[i]/tot;
			return;
		}
		
		public long randouL(int nbterms) {
		// returns a random model (coded as long), when there are nbterms interactions to consider
		return ((~(-1L<< nbterms))&papa.nextLong());
		
	}
	
		public int randouI(int nbterms) {
		// same for int (main effects)
		return ((~(-1<< nbterms))&papa.nextInt());
		
	}
	
		public long[] templCC(int[] effectsC) {
		// returns a template for xcxc interactions for a model in which the main xc effects listed are present
		// this is done by combining individual templates
		long t1 = 0L;
		long t2 = 0L;
		for (int i=0; i<effectsC.length; i++) 
				for (int j=0; j<i; j++) {
					t1 = t1|(tempXCXC1[effectsC[i]] & tempXCXC1[effectsC[j]]);
					t2 = t2|(tempXCXC2[effectsC[i]] & tempXCXC2[effectsC[j]]);
		}
		return new long[]{t1,t2};
		}

		public long[] templCQ(int[] effectsQ) {
		// returns a template for xcxq interactions for a model in which the main xq effects listed are present
		// this is done by combining individual templates
		long t1 = 0L;
		long t2 = 0L;
		for (int i=0; i<effectsQ.length; i++) {
			t1 = t1|tempXCXQ1[effectsQ[i]];
			t2 = t2|tempXCXQ2[effectsQ[i]];
		}
		return new long[]{t1,t2};
		}
		
		public long[] templCQC(int[] effectsC, int[] effectsQ) {
		// returns a template for xcxq interactions for a model in which the main xc and xq effects listed are present
		// this is done by combining individual templates
		// FUNCTION USED UNDER THE FULL MARGINALITY RULE
		long t1 = 0L;
		long t2 = 0L;
		for (int i=0; i<effectsC.length; i++) 
				for (int j=0; j<effectsQ.length; j++) {
					t1 = t1|(tempXCXQC1[effectsC[i]] & tempXCXQ1[effectsQ[j]]);
					t2 = t2|(tempXCXQC2[effectsC[i]] & tempXCXQ2[effectsQ[j]]);
		}
		return new long[]{t1,t2};
		}
		
		public long[] templQQ(int[] effectsQ) {
		// returns a template for xqxq interactions for a model in which the main xq effects listed are present
		// this is done by combining individual templates
		// FUNCTION USED UNDER THE FULL MARGINALITY RULE
		long t1 = 0L;
		long t2 = 0L;
		for (int i=0; i<effectsQ.length; i++) {
			for (int j=0; j<i; j++) {
			t1 = t1|(tempXQXQ1[effectsQ[i]] & tempXQXQ1[effectsQ[j]]);
			t2 = t2|(tempXQXQ2[effectsQ[i]] & tempXQXQ2[effectsQ[j]]);
		}
		}
		return new long[]{t1,t2};
		}
		
		
		
		
	// *********************************************************************************************
	// **************  CONSTRUCTORS *****************************************************************
	
		public GLMModel() {
			// empty, for reproduction
		}
		

		public GLMModel(ModelGenerator papa) {
			// creates a  new (random) model (immigration)
		do {
		a=randouI(nc);
		b=randouI(nq);
		c1 = randouL(nbintxcxc1);
		c2 = randouL(nbintxcxc2);
		d1 = randouL(nbintxqxq1);
		d2 = randouL(nbintxqxq2);
		e1 = randouL(nbintxcxq1);
		e2 = randouL(nbintxcxq2);
		} while (!this.valid());
		}
		
		
		
	// *********************************************************************************************
	// **************  MANIPULATIONS  *****************************************************************
			
			
		public void setIC(double a) {	
			this.ic = a;
		}
			
		
		public GLMModel mutate() {
			// produce a new "offspring" model from this model (ASEXUAL)
			// when mutating we repeat the process until a "viable" (i.e. non redundant) model is produced
			// i.e. we do not ensure a priori viability
			GLMModel son = new GLMModel();
			son.a=a;
			son.b=b;
			son.c1=c1;
			son.c2=c2;
			son.d1=d1;
			son.d2=d2;
			son.e1=e1;
			son.e2=e2;
			do {
				for (int i=0; i<nc; i++) if (papa.nextDouble()<pmut) son.a=(int)changeLocus(son.a, i+1);
				for (int i=0; i<nq; i++) if (papa.nextDouble()<pmut) son.b=(int)changeLocus(son.b, i+1);
				for (int i=0; i<nbintxcxc1; i++) if (papa.nextDouble()<pmut) son.c1=changeLocus(son.c1, i+1);
				for (int i=0; i<nbintxcxc2; i++) if (papa.nextDouble()<pmut) son.c2=changeLocus(son.c2, i+1);
				for (int i=0; i<nbintxqxq1; i++) if (papa.nextDouble()<pmut) son.d1=changeLocus(son.d1, i+1);
				for (int i=0; i<nbintxqxq2; i++) if (papa.nextDouble()<pmut) son.d2=changeLocus(son.d2, i+1);
				for (int i=0; i<nbintxcxq1; i++) if (papa.nextDouble()<pmut) son.e1=changeLocus(son.e1, i+1);
				for (int i=0; i<nbintxcxq2; i++) if (papa.nextDouble()<pmut) son.e2=changeLocus(son.e2, i+1);
		
		}  while (!son.valid());
			return son;			
		}
		
		
		public GLMModel mutate(GLMModel mate) {
			// produce a new "offspring" model from this model and model mate (SEXUAL)
			// when recombination/mutation we repeat the process until a "viable" (i.e. non redundant) model is produced
			// i.e. we do not ensure a priori viability
			// for simplicity recombination occurs between "chromosomes" only (full linkage in chromosomes)
			GLMModel son = new GLMModel();
			son.a= (papa.nextDouble()<0.5d)? a : mate.a;
			son.b= (papa.nextDouble()<0.5d)? b : mate.b;
			son.c1= (papa.nextDouble()<0.5d)? c1 : mate.c1;
			son.c2= (papa.nextDouble()<0.5d)? c2 : mate.c2;
			son.d1= (papa.nextDouble()<0.5d)? d1 : mate.d1;
			son.d2= (papa.nextDouble()<0.5d)? d2 : mate.d2;
			son.e1= (papa.nextDouble()<0.5d)? e1 : mate.e1;
			son.e2= (papa.nextDouble()<0.5d)? e2 : mate.e2;
			do {
				for (int i=0; i<nc; i++) if (papa.nextDouble()<pmut) son.a=(int)changeLocus(son.a, i+1);
				for (int i=0; i<nq; i++) if (papa.nextDouble()<pmut) son.b=(int)changeLocus(son.b, i+1);
				for (int i=0; i<nbintxcxc1; i++) if (papa.nextDouble()<pmut) son.c1=changeLocus(son.c1, i+1);
				for (int i=0; i<nbintxcxc2; i++) if (papa.nextDouble()<pmut) son.c2=changeLocus(son.c2, i+1);
				for (int i=0; i<nbintxqxq1; i++) if (papa.nextDouble()<pmut) son.d1=changeLocus(son.d1, i+1);
				for (int i=0; i<nbintxqxq2; i++) if (papa.nextDouble()<pmut) son.d2=changeLocus(son.d2, i+1);
				for (int i=0; i<nbintxcxq1; i++) if (papa.nextDouble()<pmut) son.e1=changeLocus(son.e1, i+1);
				for (int i=0; i<nbintxcxq2; i++) if (papa.nextDouble()<pmut) son.e2=changeLocus(son.e2, i+1);
		
		}  while (!son.valid());
			return son;			
		}
		
		
		
		public boolean sameas(GLMModel buddy) {
			// tests for identity of models
			return (a==buddy.a && b==buddy.b && c1==buddy.c1 && c2 == buddy.c2 && d1==buddy.d1 && d2==buddy.d2 && e1==buddy.e1 && e2==buddy.e2);
		}		
		
		public int makeK() {
			// computes the complexity of the model
			int kkk = papa.errorDF;
						// cc interactions
						kkk += Long.bitCount(this.d1)+Long.bitCount(this.d2);
						// take care of intercept trick
						if (Integer.bitCount(this.a)+Long.bitCount(this.c1)+Long.bitCount(this.c2) == 0 && papa.interc.equals("1")) kkk++;
						// scan other interactions / determine non implied effects
						int atoadd = this.a;
						int btoadd = this.b;
						for (int i=0; i<nbintxcxc1;i++) { if (papa.readLocus(c1,i+1)==1) {kkk+= papa.nlevels[intxcxc[0][i]]*papa.nlevels[intxcxc[1][i]]; atoadd = (int)setLocusToZero(atoadd,intxcxc[0][i]+1); atoadd = (int)setLocusToZero(atoadd,intxcxc[1][i]+1);}}
						for (int i=0; i<nbintxcxc2;i++) { if (papa.readLocus(c2,i+1)==1) {kkk+= papa.nlevels[intxcxc[0][i+nbintxcxc1]]*papa.nlevels[intxcxc[1][i+nbintxcxc1]]; atoadd = (int)setLocusToZero(atoadd,intxcxc[0][i+nbintxcxc1]+1); atoadd = (int)setLocusToZero(atoadd,intxcxc[1][i+nbintxcxc1]+1);}}
						for (int i=0; i<nbintxcxq1;i++) { if (papa.readLocus(e1,i+1)==1) {kkk+= papa.nlevels[intxcxq[0][i]]; btoadd = (int)setLocusToZero(btoadd,intxcxq[1][i]+1);}}
						for (int i=0; i<nbintxcxq2;i++) { if (papa.readLocus(e2,i+1)==1) {kkk+= papa.nlevels[intxcxq[0][i+nbintxcxq1]]; btoadd = (int)setLocusToZero(btoadd,intxcxq[1][i+nbintxcxq1]+1);}}
						// add non implied main effects
						kkk += Integer.bitCount(btoadd);
						for (int y=0; y<nc; y++) if (papa.readLocus(atoadd,y+1)==1l) kkk += papa.nlevels[y];
				
			return(this.k = kkk);
		}
		
		
		public boolean valid() {
			// tests for model "viability", i.e. non-redundancy, size/complexity and absence of forbidden main effects (those are not controlled for a priori).
			// first test for size
			int sissi = Integer.bitCount(a)+Integer.bitCount(b)+Long.bitCount(c1)+Long.bitCount(c2)+Long.bitCount(d1)+Long.bitCount(d2)+Long.bitCount(e1)+Long.bitCount(e2);
			if ( sissi < papa.minsize ||  (papa.maxsize>-1 && sissi>papa.maxsize)) return false;
			else if ((a&papa.ano)!= 0 || (b&papa.bno) != 0) { // test of forbidden main effects	
				return false;
			} else {	
			// test for non redundancy 
			int[] effxc = papa.binary(a, nc);
			long[] tt1 = templCC(effxc);
				for (int i=0; i<nbintxcxc1; i++) if (papa.readLocus(tt1[0],i+1)==0 && papa.readLocus(c1,i+1)==1) return false;
				for (int i=0; i<nbintxcxc2; i++) if (papa.readLocus(tt1[1],i+1)==0 && papa.readLocus(c2,i+1)==1) return false;
			int[] effxq = papa.binary(b, nq);
			// if general marginality rule, test XQXQ and XCXQC too	
			if (papa.margot) {
				long[] tt3 = templQQ(effxq);
				for (int i=0; i<nbintxqxq1; i++) if (papa.readLocus(tt3[0],i+1)==0 && papa.readLocus(d1,i+1)==1) return false;
				for (int i=0; i<nbintxqxq2; i++) if (papa.readLocus(tt3[1],i+1)==0 && papa.readLocus(d2,i+1)==1) return false;
				long[] tt4 = templCQC(effxc,effxq);
				for (int i=0; i<nbintxcxq1; i++) if (papa.readLocus(tt4[0],i+1)==0 && papa.readLocus(e1,i+1)==1) return false;
				for (int i=0; i<nbintxcxq2; i++) if (papa.readLocus(tt4[1],i+1)==0 && papa.readLocus(e2,i+1)==1) return false;
			} else {
				// if no marginality test XCXQ only
				long[] tt2 = templCQ(effxq);
				for (int i=0; i<nbintxcxq1; i++) if (papa.readLocus(tt2[0],i+1)==0 && papa.readLocus(e1,i+1)==1) return false;
				for (int i=0; i<nbintxcxq2; i++) if (papa.readLocus(tt2[1],i+1)==0 && papa.readLocus(e2,i+1)==1) return false;
			}
			// test for complexity if necessary
			if (papa.cplxlim) {
				if (this.makeK()<papa.mincplx || this.k>papa.maxcplx) return false;	
			}	
			
			return true;
			}
		}

		
		public String toFormula() {
			// returns the R formula corresponding to this model
			StringBuffer temp = new StringBuffer(papa.resp+ "~"+papa.interc);
			int[] modsxc = papa.binary(a,nc);
			int[] modsxq = papa.binary(b,nq);
			int[] modsxcxc1 = papa.binary(c1,nbintxcxc1);
			int[] modsxcxc2 = papa.binary(c2,nbintxcxc2);
			int[] modsxcxq1 = papa.binary(e1,nbintxcxq1);
			int[] modsxcxq2 = papa.binary(e2,nbintxcxq2);
			int[] modsxqxq1 = papa.binary(d1,nbintxqxq1);
			int[] modsxqxq2 = papa.binary(d2,nbintxqxq2);
			
			
			
				for (int i=0; i<modsxc.length;i++) temp.append("+ " + papa.xc[modsxc[i]]);
				for (int i=0; i<modsxq.length;i++) temp.append("+ "+ papa.xq[modsxq[i]]);
				for (int i=0; i<modsxcxc1.length;i++) temp.append("+ "+papa.xc[intxcxc[0][modsxcxc1[i]]]+":"+papa.xc[intxcxc[1][modsxcxc1[i]]]);
				for (int i=0; i<modsxcxc2.length;i++) temp.append("+ "+papa.xc[intxcxc[0][modsxcxc2[i]+nbintxcxc1]]+":"+papa.xc[intxcxc[1][modsxcxc2[i]+nbintxcxc1]]);
				for (int i=0; i<modsxqxq1.length;i++) temp.append("+ "+papa.xq[intxqxq[0][modsxqxq1[i]]]+":"+papa.xq[intxqxq[1][modsxqxq1[i]]]);
				for (int i=0; i<modsxqxq2.length;i++) temp.append("+ "+papa.xq[intxqxq[0][modsxqxq2[i]+nbintxqxq1]]+":"+papa.xq[intxqxq[1][modsxqxq2[i]+nbintxqxq1]]);
				for (int i=0; i<modsxcxq1.length;i++) temp.append("+ "+papa.xc[intxcxq[0][modsxcxq1[i]]]+":"+papa.xq[intxcxq[1][modsxcxq1[i]]]);
				for (int i=0; i<modsxcxq2.length;i++) temp.append("+ "+papa.xc[intxcxq[0][modsxcxq2[i]+nbintxcxq1]]+":"+papa.xq[intxcxq[1][modsxcxq2[i]+nbintxcxq1]]);
				return temp.toString();	
		}
		
		public String toRString() {
			// returns the String encoding this model, for output purposes in R
			StringBuffer temp = new StringBuffer();
			if (nc>0) {
				temp.append("X");
				for (int i=0; i<nc; i++) if (papa.readLocus(a,i+1)==1) temp.append("\t 1 "); else temp.append("\t 0 ");
			}
			if (nq>0) {
				if (nc>0) temp.append("\tX"); else temp.append("X");
				for (int i=0; i<nq; i++) if (papa.readLocus(b,i+1)==1) temp.append("\t 1 "); else temp.append("\t 0 ");
			}
			if (nbintxcxc>0) {
				temp.append("\tX");
				for (int i=0; i<nbintxcxc1; i++) if (papa.readLocus(c1,i+1)==1) temp.append("\t 1 "); else temp.append("\t 0 ");
				for (int i=0; i<nbintxcxc2; i++) if (papa.readLocus(c2,i+1)==1) temp.append("\t 1 "); else temp.append("\t 0 ");
			}
			if (nbintxqxq>0) {
				temp.append("\tX");
				for (int i=0; i<nbintxqxq1; i++) if (papa.readLocus(d1,i+1)==1) temp.append("\t 1 "); else temp.append("\t 0 ");
				for (int i=0; i<nbintxqxq2; i++) if (papa.readLocus(d2,i+1)==1) temp.append("\t 1 "); else temp.append("\t 0 ");
			}
			if (nbintxcxq>0) {
				temp.append("\tX");
				for (int i=0; i<nbintxcxq1; i++) if (papa.readLocus(e1,i+1)==1) temp.append("\t 1 "); else temp.append("\t 0 ");
				for (int i=0; i<nbintxcxq2; i++) if (papa.readLocus(e2,i+1)==1) temp.append("\t 1 "); else temp.append("\t 0 ");
			}
				return temp.toString();	

		}


// **************************************************
// *********** MORE BIT MANIPULATION TOOLS ************

		public static long changeLocus(long lg, int locus) {
		// changes the allelic state of the locus th locus on chromosome lg
		 long powo = (1l << (locus-1));
		 if (papa.readLocus(lg, locus) == 1)
		 	return (lg - powo);
		 else return(lg + powo);
	}	
		
		public static long setLocusToOne(long lg, int locus) {
			long powo = (1l << (locus-1));
			if (papa.readLocus(lg, locus) == 0)
		 	return (lg + powo);
			else return lg;			
		}
		public static long setLocusToZero(long lg, int locus) {
			long powo = (1l << (locus-1));
			if (papa.readLocus(lg, locus) == 1)
		 	return (lg - powo);
			else return lg;			
		}
		
	
}
