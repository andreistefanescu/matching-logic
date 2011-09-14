
public class SimpleStructureGenerator {
	private static int numberOfFields = 0;
	private static String hpname = "";
	private static CStructure cs = null;

	public SimpleStructureGenerator(CStructure cs)
	{
		String HeapPatternName = cs.getSmi().name();
		this.numberOfFields = cs.getNumberoffields();
		this.cs = cs;
	}
	
	private static String genVars()
	{
		String result = "";
		
		result = "kvar ";
		for(int i=0; i < numberOfFields;i++)
		{
			result = result + " I" + i;
		}
		result = result + " : Int++";
		return result;
	}
	
	private static String genSUR()
	{
		String result = "";
		
		for(int i=0; i< numberOfFields; i++)
		{
			result = result + "      (P +Int " + i + ") |-> FreeInt(N +Int " + i + ") : " +
			  "(id(\"" + cs.getName() + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
		}
		result = result + "    H\n    </heap>\n    <counter> N +Int " + numberOfFields + "</counter>\n"
				 + "CfgItems\n    </config>\n    <form>\n      Phi /\\ ~(P === 0) /\\ (Alpha === (";
		
		for(int i=0; i< numberOfFields; i++)
		{
			result = result + "[FreeInt(N +Int " + i + ")] @ ";
		}
		
		result = result.substring(0, result.length()-3);
		
		result = result + ")\n    </form>\n    TaskItems\n  </task>\nif VALID(Phi ===> P' === P ";
		
		for(int i=1; i < numberOfFields; i++)
		{
			result = result + "\\/ P' === P +Int " + i;
		}
		
		result = result + " )";
		
		return result;
	}
	
	private static String genSURing()
	{
		String result = "      ";
		result = result + hpname + "(P)(Alpha)\n      ";
		
		for (int i=0; i < numberOfFields; i++)
		{
			result = result + "(P +Int " + i + ") |-> FreeInt(N +Int " + i + ") : " +
			  "(id(\"" + cs.getName() + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
		}
		
		result = result + "    </heap>\n    <counter> N => N +Int" + numberOfFields + " </counter>\n"
						+ "    <form>\n      Phi /\\ ~(P === 0) => Phi /\\ ~(P === 0) /\\ (Alpha === (";
		
		for(int i=0; i< numberOfFields; i++)
		{
			result = result + "[FreeInt(N +Int " + i + ")] @ ";
		}
		
		result = result.substring(0, result.length()-3);
		result = result + ")\n    </form>";
		
		return result;
	}

	
	private static String genR()
	{
		String result = "";
		
		for (int i=0; i < numberOfFields; i++)
		{
			result = result + "(P +Int " + i + ") |-> I" + i + ") : " +
			  "(id(\"" + cs.getName() + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
		}
		result = result + "    =>\n      " + hpname + "(P)(";
		
		for(int i=0; i < numberOfFields; i++)
		{
			result = result + " [I" + i + "] @";
		}
		
		result = result.substring(0, result.length()-2);
		result = result + ")\n";
		
		return result;
	}
	
	public static void Generate()
	{
		String vars = genVars();
		String sunroll = genSUR();
		String sunrolling = genSURing();
		String roll = genR();
		
		String content = GeneralFunctions.readFileContent(GlVars.patternGenFile + "/patternTemplates/Simple.template");
		content = content.replaceAll("HPNAME", hpname.toUpperCase());
		content = content.replaceAll("hpname", hpname);
		content = content.replace("VARGEN", vars);
		content = content.replace("SIMPLEUNROLL", sunroll);
		content = content.replace("SIMPLEUNROLING", sunrolling);
		content = content.replace("ROLL", roll);

		content = content.replaceAll(" [+]Int 0", "");
		GeneralFunctions.writeFileContent(content, GlVars.patterns + "/" + hpname + ".k");
                
                GeneralFunctions.addContent(GlVars.semantics + "/Makefile", 
                                    "#GENERATEDCONTENTSTART", 
                                    "EXT_K_" + hpname.toUpperCase() + "= $(ML_PATTERNS_DIR)/" + hpname + ".k");
        GeneralFunctions.addContent(GlVars.semantics + "/Makefile", 
                                    "$(EXT_K_MAIN)", 
                                    " \\ \n$(EXT_K_" + hpname.toUpperCase() + ")");
        GeneralFunctions.addContent(GlVars.semantics + "/matchC.k", 
                                    "***LOADPATTERNSSTART", 
                                    "load ../patterns/" + hpname);
        GeneralFunctions.addContent(GlVars.semantics + "/matchC.k", 
                                    "***ADDMODULESSTART", 
                                    "+ " + hpname.toUpperCase() + "-HP");
        GeneralFunctions.addContent(GlVars.lib + "/config.maude", 
                                    "***newheapnamesstart", 
                                    "  op " + hpname + " : -> HeapLabel .");
	}
}
