
public class ElementaryFieldsOnlyGenerator {
	private static String vars = "", sunroll = "", sunrolling = "", sroll = "";
	private static String hpname = "";
	private static String lseghp = "";
	private static int nof = 0;
	private static CStructure cs;
	
	public ElementaryFieldsOnlyGenerator(CStructure cs, String HeapPatternName)
	{
		vars = "";  sunroll = "";  sunrolling = "";  sroll = "";
		setHpname("");
		lseghp = "";
		this.setCs(cs);
		nof = cs.getNumberoffields();
		this.setHpname(HeapPatternName);
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
	
	private static void genSUnroll()
	{	
		for(int i=0; i<nof; i++)
		{
			String s = Integer.toString(i);

			sunroll = sunroll + "      (P +Int " + s + ") |-> FreeInt(N +Int " + s + ") : " +
					  "(id(\"" + getCs().getName() + "\").id(\"" + getCs().nameOfField(i) + "\"))\n";

		}
		if (nof>2)
		{
			sunroll = sunroll + "      H\n  </heap>\n    <counter> N +Int " + Integer.toString(nof) 
						  + "    </counter>\n    CfgItems\n  </config>\n  </form>\n    Phi /\\ ~(P === 0) /\\ (Alpha === [< ";
		}
		else
		{
			sunroll = sunroll + "      H\n  </heap>\n    <counter> N +Int " + Integer.toString(nof) 
			  + "    </counter>\n    CfgItems\n  </config>\n  </form>\n    Phi /\\ ~(P === 0) /\\ (Alpha === [ ";
		}
		
		for(int i=0;i<nof;i++)
		{
			sunroll = sunroll + "FreeInt(N +Int " + i + "), ";
		}
		sunroll = sunroll.substring(0, sunroll.length() - 2);
		if (nof>2)
		{
			sunroll = sunroll + ">] ))\n  </form>\n  TaskItems\n </task>\n" 
							  + "  if VALID(Phi ===> ";
		}
		else
		{
			sunroll = sunroll + "] ))\n  </form>\n  TaskItems\n </task>\n" 
			  				  + "  if VALID(Phi ===> ";
		}
		for(int i=0;i<nof;i++)
		{
			sunroll = sunroll + "(P' === P +Int " + Integer.toString(i) + ") \\/ ";
		}
		
		sunroll = sunroll.substring(0, sunroll.length() - 4);
		sunroll = sunroll + ")";
	}

	private static void genSUnrolling()
	{ 
		for(int i=0; i<nof; i++)
		{
			sunrolling = sunrolling + "      (P +Int " + i + ") |-> FreeInt(N +Int " + i + ") : " +
					  "(id(\"" + getCs().getName() + "\").id(\"" + getCs().nameOfField(i) + "\"))\n";
			
		}
		if (nof>2)
		{
			sunrolling = sunrolling + "        <_/heap>\n  <counter> N +Int " + Integer.toString(nof) 
						  + "  </counter>\n  </form>\n    Phi /\\ ~(P === 0) /\\ (Alpha === [< ";
		}
		else
		{
			sunrolling = sunrolling + "        <_/heap>\n  <counter> N +Int " + Integer.toString(nof) 
			  + "  </counter>\n  </form>\n    Phi /\\ ~(P === 0) /\\ (Alpha === [ ";
		}
		
		for(int i=0;i<nof;i++)
		{
			sunrolling = sunrolling + "FreeInt(N +Int " + i + "), ";
		}
		sunrolling = sunrolling.substring(0, sunrolling.length() - 2);
		if (nof>2)
		{
			sunrolling = sunrolling + ">] ))\n  </form>\n" ;
		}
		else
		{
			sunrolling = sunrolling + "] ))\n  </form>\n";
		}
	}

	private static void genSRoll()
	{	
		for(int i=0; i<nof; i++)
		{
			String s = Integer.toString(i);
				sroll = sroll + "      (P +Int " + s + ") |-> I" + s + " : " +
					  "(id(\"" + getCs().getName() + "\").id(\"" + getCs().nameOfField(i) + "\"))\n";
		}
		
		sroll = sroll + "      => " + getHpname() + "(P)(";
		
		if (nof>1)
		{
			sroll = sroll + "[<";
			for(int i=0;i<nof;i++)
				{
					sroll = sroll + "I" + i + ", ";
				}
			sroll = sroll.substring(0, sroll.length() - 2);
			sroll = sroll + ">])";
		}
		else
		{
			sroll = sroll + "[I])";
		}
		
	}

	public static void Generate()
	{
		genVars();
		genSUnroll();
		genSUnrolling();
		genSRoll();
		String content = GeneralFunctions.readFileContent("../patternTemplates/SEL.template");
		content = content.replaceAll("HPNAME", getHpname().toUpperCase());
		content = content.replaceAll("hpname", getHpname());
		content = content.replaceAll("hpnameseg", lseghp);
		content = content.replace("VARGEN", vars);
		content = content.replace("SIMPLEUNROLL", sunroll);
		content = content.replace("SIMPLEUNROLING", sunrolling);
		content = content.replace("SIMPLEROLL", sroll);
		content = content.replaceAll(" [+]Int 0", "");
		GeneralFunctions.writeFileContent(content, "../GeneratedContent/" + getHpname() + ".k");
	}

	public void setCs(CStructure cs) {
		ElementaryFieldsOnlyGenerator.cs = cs;
	}

	public static CStructure getCs() {
		return cs;
	}

	public void setHpname(String hpname) {
		ElementaryFieldsOnlyGenerator.hpname = hpname;
	}

	public static String getHpname() {
		return hpname;
	}
}
