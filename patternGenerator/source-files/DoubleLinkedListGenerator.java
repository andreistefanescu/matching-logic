
public class DoubleLinkedListGenerator {
	private static String lunroll = "", runroll = "", sroll = "", vars = "";
	private static String hpname = "", hpseg = "";
	private static int nof = 0;
	private static int noef = 0;
	private static CStructure cs;
	
	public DoubleLinkedListGenerator(CStructure cs)
	{
		String HeapPatternName = cs.getSmi().name();
		lunroll = ""; runroll = ""; sroll = ""; vars = "";
		hpname = ""; hpseg = "";
		this.cs = cs;
		nof = cs.getNumberoffields();
		noef = cs.numberOfElementaryFileds();
		this.hpname = HeapPatternName;
		this.hpseg  = this.hpname + "seg";
	}
	
	private static void genVars()
	{
		vars = "kvar ";
		for(int i=0; i<nof; i++)
		{
			vars = vars + "I" + Integer.toString(i) + " ";
		}
		vars = vars + ": Int++\n";
	}
	
	private static void genLUnroll()
	{
		int valueFieldsIndex[] = new int[noef];
		int index = 0;
		noef = cs.numberOfElementaryFileds();
		
		for(int i=0; i<nof; i++)
		{
			String s = Integer.toString(i);
			
			lunroll = lunroll + "      (LEFT +Int " + s + ") |-> FreeInt(N +Int " + s + ") : " +
			"(id(\"" + hpseg + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			
			if ((i != cs.indexNext()) && (i != cs.indexPrev()))
			{
				valueFieldsIndex[index] = i;
				index++;
			}
		}
		if (noef > 1)
		{
			lunroll = lunroll + "      " + hpseg + "(LEFT, FreeInt(N +Int " + cs.indexNext() + "))(RIGHT, ERIGHT, FreeSeq(N +Int "
			+ Integer.toString(nof) + "))\n      H\n  </heap>\n    <counter> N +Int " + Integer.toString(nof + 1) 
			+ "    </counter>\n    CfgItems\n  </config>\n  </form>\n    Phi /\\ ~(LEFT === 0) /\\ (Alpha === [< ";
		}
		else
		{
			lunroll = lunroll + "      " + hpseg + "(LEFT, FreeInt(N +Int " + cs.indexNext() + "))(RIGHT, ERIGHT, FreeSeq(N +Int "
			+ Integer.toString(nof) + "))\n      H\n  </heap>\n    <counter> N +Int " + Integer.toString(nof + 1) 
			+ "    </counter>\n    CfgItems\n  </config>\n  </form>\n    Phi /\\ ~(LEFT === 0) /\\ (Alpha === [ ";
		}
		
		for(int i=0;i < noef;i++)
		{
			lunroll = lunroll + "FreeInt(N +Int " + Integer.toString(valueFieldsIndex[i]) + "), ";
		}
		lunroll = lunroll.substring(0, lunroll.length() - 2);
		if (noef > 1)
		{
			lunroll = lunroll + ">] @ FreeSeq(N +Int " + Integer.toString(nof) + "))\n  </form>\n  TaskItems\n </task>\n" 
			+ "  if VALID(Phi ===> ";
		}
		else
		{
			lunroll = lunroll + "] @ FreeSeq(N +Int " + Integer.toString(nof) + "))\n  </form>\n  TaskItems\n </task>\n" 
			+ "  if VALID(Phi ===> ";
		}
		for(int i=0;i<nof;i++)
		{
			lunroll = lunroll + "(P' === LEFT +Int " + Integer.toString(i) + ") \\/ ";
		}
		
		lunroll = lunroll.substring(0, lunroll.length() - 4);
		lunroll = lunroll + ")";
	}
	
	private static void genRUnroll()
	{
		int valueFieldsIndex[] = new int[noef];
		int index = 0;
		noef = cs.numberOfElementaryFileds();
		
		for(int i=0; i<nof; i++)
		{
			String s = Integer.toString(i);
			
			runroll = runroll + "      (RIGHT +Int " + s + ") |-> FreeInt(N +Int " + s + ") : " +
			"(id(\"" + hpseg + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			
			if ((i != cs.indexNext()) && (i != cs.indexPrev()))
			{
				valueFieldsIndex[index] = i;
				index++;
			}
		}
		if (noef > 1)
		{
			runroll = runroll + "      " + hpseg + "(ELEFT, LEFT)(FreeInt(N +Int " + cs.indexPrev() + "), RIGHT, FreeSeq(N +Int "
			+ Integer.toString(nof) + "))\n      H\n  </heap>\n    <counter> N +Int " + Integer.toString(nof + 1) 
			+ "    </counter>\n    CfgItems\n  </config>\n  </form>\n    Phi /\\ ~(RIGHT === 0) /\\ (Alpha === [< ";
		}
		else
		{
			runroll = runroll + "      " + hpseg + "(ELEFT, LEFT)(FreeInt(N +Int " + cs.indexPrev() + "), RIGHT, FreeSeq(N +Int "
			+ Integer.toString(nof) + "))\n      H\n  </heap>\n    <counter> N +Int " + Integer.toString(nof + 1) 
			+ "    </counter>\n    CfgItems\n  </config>\n  </form>\n    Phi /\\ ~(RIGHT === 0) /\\ (Alpha === [ ";
		}
		
		for(int i=0;i < noef;i++)
		{
			runroll = runroll + "FreeInt(N +Int " + Integer.toString(valueFieldsIndex[i]) + "), ";
		}
		runroll = runroll.substring(0, runroll.length() - 2);
		if (noef > 1)
		{
			runroll = runroll + ">] @ FreeSeq(N +Int " + Integer.toString(nof) + "))\n  </form>\n  TaskItems\n </task>\n" 
			+ "  if VALID(Phi ===> ";
		}
		else
		{
			runroll = runroll + "] @ FreeSeq(N +Int " + Integer.toString(nof) + "))\n  </form>\n  TaskItems\n </task>\n" 
			+ "  if VALID(Phi ===> ";
		}
		for(int i=0;i<nof;i++)
		{
			runroll = runroll + "(P' === RIGHT +Int " + Integer.toString(i) + ") \\/ ";
		}
		
		runroll = runroll.substring(0, runroll.length() - 4);
		runroll = runroll + ")";
	}
	
	private static void genSRoll()
	{
		int valueFieldsIndex[] = new int[noef];
		int index = 0;
		int indexOfPointerField = cs.indexOfPointerField(0); 
		
		for(int i=0; i<nof; i++)
		{
			String s = Integer.toString(i);
			{
				sroll = sroll + "      (P +Int " + s + ") |-> I" + s + " : " +
				"(id(\"" + cs.getName() + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			}
			
			if ((i != cs.indexNext()) && (i != cs.indexPrev()))
			{
				valueFieldsIndex[index] = i;
				index++;
			}
		}
		
		sroll = sroll + "      => " + hpseg + "(I" + cs.indexPrev() + ", P)(P, I" + cs.indexNext() + ", ";
		CStructure cs = new CStructure();
		cs.copy(cs);
		System.out.println(cs);
		
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
		else
		{
			sroll = sroll + "[I" + (valueFieldsIndex[0]) + "])";
		}
	}
	
	public static void Generate()
	{
		genVars();
		genLUnroll();
		genRUnroll();
		String content = GeneralFunctions.readFileContent("../patternTemplates/DLList.template");
		content = content.replaceAll("HPNAME", hpname.toUpperCase());
		content = content.replaceAll("hpname", hpname);
		content = content.replaceAll("hpnameseg", hpseg);
		content = content.replace("KVARS", vars);
		content = content.replace("LUNROLL", lunroll);
		content = content.replace("RUNROLL", runroll);
		content = content.replaceAll("SROLL", sroll);
		content = content.replaceAll(" [+]Int 0", "");
		GeneralFunctions.writeFileContent(content, "../GeneratedContent/" + hpname + ".k");
	}
	
	
}
