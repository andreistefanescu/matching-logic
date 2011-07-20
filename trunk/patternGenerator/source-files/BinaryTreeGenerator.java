
public class BinaryTreeGenerator {
	private static String unroll = "", sroll = "", lroll = "", rroll="", croll="", vars = "";
	private static String hpname = "";
	private static int nof = 0;
	private static int noef = 0;
	private static CStructure cs;
	private static int[] valueFieldsIndex;

	
	public BinaryTreeGenerator(CStructure cs)
	{
		String HeapPatternName = cs.getSmi().name();
		unroll = ""; sroll = ""; lroll = ""; rroll=""; croll=""; vars = "";
		hpname = ""; 
		this.cs = cs;
		nof = cs.getNumberoffields();
		noef = cs.numberOfElementaryFileds();
		this.hpname = HeapPatternName;
		valueFieldsIndex = new int[nof];
		
		int index = 0;
		for(int i=0; i<nof; i++)
		{	
			if ((i != cs.indexNext()) && (i != cs.indexPrev()))
			{
				valueFieldsIndex[index] = i;
				index++;
			}
		}
		index++;
	}
	
	private static void genVars()
	{
		vars = "kvar ";
		for(int i=0; i<nof; i++)
		{
			vars = vars + "I" + (i) + " ";
		}
		vars = vars + ": Int++\n";
	}

	private static void genUnroll()
	{
		int next=0, prev=0, counter=nof+2;
		noef = cs.numberOfElementaryFileds();
		int valueFieldsIndex[] = new int[noef];
		int index = 0;
		
		for(int i=0; i<nof; i++)
		{
			String s = Integer.toString(i);

			unroll = unroll + "      (P +Int " + s + ") |-> FreeInt(N +Int " + s + ") : " +
					  "(id(\"" + hpname + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			
			if ((i != cs.indexNext()) && (i != cs.indexPrev()))
			{
				valueFieldsIndex[index] = i;
				index++;
			}
		}
		
		if (cs.indexNext() > cs.indexPrev())
		{
			prev = nof;
			next = nof+1;
		}
		else
		{
			prev = nof+1;
			next = nof;
		}
		
		
		if (noef > 1)
		{
			unroll = unroll + "      " + hpname + "(FreeInt(N +Int " + cs.indexPrev() + "))(FreeTree(N +Int " + prev 
			    			  + "))\n      " + hpname + "(FreeInt(N +Int " + cs.indexNext() + "))(FreeTree(N +Int " + next
						  + "))\n" + "      H\n  </heap>\n    <counter> N +Int " + counter
						  + "    </counter>\n    CfgItems\n  </config>\n  </form>\n    Phi /\\ ~(P === 0) /\\ (Alpha === FreeTree (N +Int "
						  + prev + ") [< ";
		}
		else
		{
			unroll = unroll + "      " + hpname + "(FreeInt(N +Int " + cs.indexPrev() + "))(FreeTree(N +Int " + (prev) 
			  + "))\n      " + hpname + "(FreeInt(N +Int " + cs.indexNext() + "))(FreeTree(N +Int " + (next)
			  + "))\n" + "      H\n  </heap>\n    <counter> N +Int " + (nof + 2) 
			  + "    </counter>\n    CfgItems\n  </config>\n  </form>\n    Phi /\\ ~(P === 0) /\\ (Alpha === FreeTree(N +Int "
			  + prev + ") [";
		}
		
		for(int i=0;i < noef;i++)
		{
			unroll = unroll + "FreeInt(N +Int " + (valueFieldsIndex[i]) + "), ";
		}
		unroll = unroll.substring(0, unroll.length() - 2);
		if (noef > 1)
		{
			unroll = unroll + ">] FreeTree(N +Int " + next + "))\n  </form>\n  TaskItems\n </task>\n" 
							  + "  if VALID(Phi ===> ";
		}
		else
		{
			unroll = unroll + " ] FreeTree(N +Int " + next + "))\n  </form>\n  TaskItems\n </task>\n" 
			  				  + "  if VALID(Phi ===> ";
		}
		for(int i=0;i<nof;i++)
		{
			unroll = unroll + "(P' === P +Int " + (i) + ") \\/ ";
		}
		
		unroll = unroll.substring(0, unroll.length() - 4);
		unroll = unroll + ")";
	}

	private static void genSRoll()
	{
        
		int next=0, prev=0;
		if (cs.indexNext() > cs.indexPrev())
		{			prev = nof;			next = nof+1;	}
		else
		{			prev = nof+1;		next = nof;		}
		
		for(int i=0; i<nof;i++)
		{
			sroll = sroll + "      (P +Int " + i + ") |-> ";
			if ((i == cs.indexNext()) || (i == cs.indexPrev()))
			{
				sroll = sroll + "0 : (id(\"" + hpname + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			}else
			{
				sroll = sroll + "I" + i + ": (id(\"" + hpname + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			}	
		}
		
		sroll = sroll + "      => \n      " + hpname + "(P)(upsilon ";
		
		/*hpname(P)(upsilon [I] upsilon)    SROLL*/
		if (noef > 1)
		{
			sroll = sroll + "[<";
			for(int i=0;i<noef;i++)
				{
					sroll = sroll + "I" + valueFieldsIndex[i] + ", ";
				}
			sroll = sroll.substring(0, sroll.length() - 2);
			sroll = sroll + ">])";
		}
		else if (noef == 1)
		{
			sroll = sroll + "[I" + (valueFieldsIndex[0]) + "])";
		}
		sroll = sroll + " upsilon)";
	}

	private static void genLRoll()
	{	
		for(int i=0; i<nof;i++)
		{
			lroll = lroll + "      (P +Int " + i + ") |-> ";
			if (i == cs.indexNext())
			{
				lroll = lroll + "0 : (id(\"" + hpname + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			}else
			{
				lroll = lroll + "I" + i + ": (id(\"" + hpname + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			}	
		}
		lroll = lroll + "        " + hpname + "(I" + cs.indexPrev() + ")(Tau)\n      =>\n        " + hpname + "(P)(Tau [";
		
		if (noef > 1)
		{
			lroll = lroll + "<";
			for(int i=0;i<noef;i++)
				{
					lroll = lroll + "I" + valueFieldsIndex[i] + ", ";
				}
			lroll = lroll.substring(0, lroll.length() - 2);
			lroll = lroll + ">";
		}
		else if (noef == 1)
		{
			lroll = lroll + "[I" + (valueFieldsIndex[0]);
		}
		
		lroll = lroll + "] upsilon)";
	}
	
	private static void genRRoll()
	{	
		for(int i=0; i<nof;i++)
		{
			rroll = rroll + "      (P +Int " + i + ") |-> ";
			if (i == cs.indexPrev())
			{
				rroll = rroll + "0 : (id(\"" + hpname + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			}else
			{
				rroll = rroll + "I" + i + ": (id(\"" + hpname + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			}	
		}
		rroll = rroll + "        " + hpname + "(I" + cs.indexNext() + ")(Tau)\n      =>\n        " + hpname + "(P)(upsilon [";
		
		if (noef > 1)
		{
			rroll = rroll + "<";
			for(int i=0;i<noef;i++)
				{
					rroll = rroll + "I" + valueFieldsIndex[i] + ", ";
				}
			rroll = rroll.substring(0, rroll.length() - 2);
			rroll = rroll + ">";
		}
		else if (noef == 1)
		{
			rroll = rroll + "[I" + (valueFieldsIndex[0]);
		}
		
		rroll = rroll + "] Tau)";
	}
	
	private static void genCRoll()
	{	
		for(int i=0; i<nof;i++)
		{
			croll = croll + "      (P +Int " + i + ") |-> " + "I" + i + ": (id(\"" + hpname + "\").id(\"" + cs.nameOfField(i) + "\"))\n";	
		}
		croll = croll + "        " + hpname + "(I" + cs.indexPrev() + ")(Tau)\n" 
				      + "        " + hpname + "(I" + cs.indexNext() + ")(Sigma)\n      =>\n        " + hpname + "(P)(Tau [";
		
		if (noef > 1)
		{
			croll = croll + "<";
			for(int i=0;i<noef;i++)
				{
					croll = croll + "I" + valueFieldsIndex[i] + ", ";
				}
			croll = croll.substring(0, croll.length() - 2);
			croll = croll + ">";
		}
		else if (noef == 1)
		{
			croll = croll + "[I" + (valueFieldsIndex[0]);
		}
		
		croll = croll + "] Sigma)";
	}
	
	public static void Generate()
	{
		genVars();
		genUnroll();
		genSRoll();
		genLRoll();
		genRRoll();
		genCRoll();
		String content = GeneralFunctions.readFileContent("../patternTemplates/BinaryTree.template");
		content = content.replaceAll("HPNAME", hpname.toUpperCase());
		content = content.replaceAll("hpname", hpname);
		content = content.replace("VARGEN", vars);
		content = content.replace("UNROLL", unroll);
		content = content.replaceAll("SROLL", sroll);
		content = content.replaceAll("LROLL", lroll);
		content = content.replaceAll("RROLL", rroll);
		content = content.replaceAll("CROLL", croll);
		content = content.replaceAll(" [+]Int 0", "");
		GeneralFunctions.writeFileContent(content, "../GeneratedContent/" + hpname + ".k");
	}
}