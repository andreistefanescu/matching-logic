
public class SingleLinkedListGenerator {
	private static String vars = "", sunroll = "", sunrolling = "", sroll = "";
	private static String croll = "", sunrollseg = "", srollseg = "";
	private static String hpname = "";
	private static String lseghp = "";
	private static int nof = 0;
	private static CStructure cs;
	
	public SingleLinkedListGenerator(CStructure cs, String HeapPatternName)
	{
		vars = "";  sunroll = "";  sunrolling = "";  sroll = "";
		croll = "";  sunrollseg = "";  srollseg = "";
		hpname = "";
		lseghp = "";
		this.cs = cs;
		nof = cs.getNumberoffields();
		this.hpname = HeapPatternName;
		this.lseghp = hpname + "seg";
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
		int valueFieldsIndex[] = new int[nof -1];
		int index = 0;
		int indexOfPointerField = cs.indexOfPointerField(0); 
		
		for(int i=0; i<nof; i++)
		{
			String s = Integer.toString(i);

			sunroll = sunroll + "      (P +Int " + s + ") |-> FreeInt(N +Int " + s + ") : " +
					  "(id(\"" + cs.getName() + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			
			if (indexOfPointerField != (i))
			{
				valueFieldsIndex[index] = i;
				index++;
			}
		}
		if (nof>2)
		{
			sunroll = sunroll + "      " + hpname + "(FreeInt(N +Int " + indexOfPointerField + "))(FreeSeq(N +Int "
						  + Integer.toString(nof) + "))\n      H\n  </heap>\n    <counter> N +Int " + Integer.toString(nof + 1) 
						  + "    </counter>\n    CfgItems\n  </config>\n  </form>\n    Phi /\\ ~(P === 0) /\\ (Alpha === [< ";
		}
		else
		{
			sunroll = sunroll + "      " + hpname + "(FreeInt(N +Int " + indexOfPointerField + "))(FreeSeq(N +Int "
			  + Integer.toString(nof) + "))\n      H\n  </heap>\n    <counter> N +Int " + Integer.toString(nof + 1) 
			  + "    </counter>\n    CfgItems\n  </config>\n  </form>\n    Phi /\\ ~(P === 0) /\\ (Alpha === [ ";
		}
		
		for(int i=0;i<(nof-1);i++)
		{
			sunroll = sunroll + "FreeInt(N +Int " + Integer.toString(valueFieldsIndex[i]) + "), ";
		}
		sunroll = sunroll.substring(0, sunroll.length() - 2);
		if (nof>2)
		{
			sunroll = sunroll + ">] @ FreeSeq(N +Int " + Integer.toString(nof) + "))\n  </form>\n  TaskItems\n </task>\n" 
							  + "  if VALID(Phi ===> ";
		}
		else
		{
			sunroll = sunroll + "] @ FreeSeq(N +Int " + Integer.toString(nof) + "))\n  </form>\n  TaskItems\n </task>\n" 
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
		int valueFieldsIndex[] = new int[nof -1];
		int index = 0;
		int indexOfPointerField = cs.indexOfPointerField(0); 
		for(int i=0; i<nof; i++)
		{
			sunrolling = sunrolling + "      (P +Int " + i + ") |-> FreeInt(N +Int " + i + ") : " +
					  "(id(\"" + cs.getName() + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			
			if (indexOfPointerField != (i))
			{
				valueFieldsIndex[index] = i;
				index++;
			}
		}
		if (nof>2)
		{
			sunrolling = sunrolling + "      " + hpname + "(FreeInt(N +Int " + indexOfPointerField + "))(FreeSeq(N +Int "
						  + Integer.toString(nof) + "))\n  <_/heap>\n  <counter> N +Int " + Integer.toString(nof + 1) 
						  + "  </counter>\n  </form>\n    Phi /\\ ~(P === 0) /\\ (Alpha === [< ";
		}
		else
		{
			sunrolling = sunrolling + "      " + hpname + "(FreeInt(N +Int " + indexOfPointerField + "))(FreeSeq(N +Int "
			  + Integer.toString(nof) + "))\n  <_/heap>\n  <counter> N +Int " + Integer.toString(nof + 1) 
			  + "  </counter>\n  </form>\n    Phi /\\ ~(P === 0) /\\ (Alpha === [ ";
		}
		
		for(int i=0;i<(nof-1);i++)
		{
			sunrolling = sunrolling + "FreeInt(N +Int " + Integer.toString(valueFieldsIndex[i]) + "), ";
		}
		sunrolling = sunrolling.substring(0, sunrolling.length() - 2);
		if (nof>2)
		{
			sunrolling = sunrolling + ">] @ FreeSeq(N +Int " + Integer.toString(nof) + "))\n  </form>\n" ;
		}
		else
		{
			sunrolling = sunrolling + "] @ FreeSeq(N +Int " + Integer.toString(nof) + "))\n  </form>\n";
		}
	}

	private static void genSRoll()
	{
		int valueFieldsIndex[] = new int[nof -1];
		int index = 0;
		int indexOfPointerField = cs.indexOfPointerField(0); 
		
		for(int i=0; i<nof; i++)
		{
			String s = Integer.toString(i);
			if (i == indexOfPointerField)
			{
				sroll = sroll + "      (P +Int " + s + ") |-> 0 : " +
				  "(id(\"" + cs.getName() + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			}
			else
			{
				sroll = sroll + "      (P +Int " + s + ") |-> I" + s + " : " +
					  "(id(\"" + cs.getName() + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			}
			
			if (indexOfPointerField != (i))
			{
				valueFieldsIndex[index] = i;
				index++;
			}
		}
		
		sroll = sroll + "      => " + hpname + "(P)(";
		
		if (nof>2)
		{
			sroll = sroll + "[<";
			for(int i=0;i<nof -1;i++)
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
	
	private static void genCRoll()
	{
		int valueFieldsIndex[] = new int[nof -1];
		int index = 0;
		int indexOfPointerField = cs.indexOfPointerField(0); 
		
		for(int i=0; i<nof; i++)
		{
			String s = Integer.toString(i);
			croll = croll + "      (P +Int " + s + ") |-> I" + s + " : " +
					  "(id(\"" + cs.getName() + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			
			if (indexOfPointerField != (i))
			{
				valueFieldsIndex[index] = i;
				index++;
			}
		}
		
		croll = croll + "      " + hpname + "(I" + indexOfPointerField + ")(Alpha)\n      =>\n       " + hpname + "(P)(";
		
		if (nof>2)
		{
			croll = croll + "[<";
			for(int i=0;i<nof -1;i++)
				{
					croll = croll + "I" + valueFieldsIndex[i] + ", ";
				}
			croll = croll.substring(0, croll.length() - 2);
			croll = croll + ">] @ Alpha)";
		}
		else
		{
			croll = croll + "[I" + (valueFieldsIndex[0]) + "]) @ Alpha)";
		}
	}
	
	private static void genSUnrollSeg()
	{	int valueFieldsIndex[] = new int[nof -1];
		int index = 0;
		int indexOfPointerField = cs.indexOfPointerField(0); 
		
		for(int i=0; i<nof; i++)
		{
			String s = Integer.toString(i);
			sunrollseg = sunrollseg + "      (P +Int " + s + ") |-> FreeInt(N +Int " + s + ") : " +
					  "(id(\"" + cs.getName() + "\").id(\"" + cs.nameOfField(i) + "\"))\n";
			
			if (indexOfPointerField != (i))
			{
				valueFieldsIndex[index] = i;
				index++;
			}
		}
		if (nof>2)
		{
			sunrollseg = sunrollseg + "      " + lseghp + "(FreeInt(N +Int " + indexOfPointerField + "),Q)(FreeSeq(N +Int "
						  + Integer.toString(nof) + "))\n      H\n  </heap>\n    <counter> N +Int " + Integer.toString(nof + 1) 
						  + "    </counter>\n    CfgItems\n  </config>\n  </form>\n    Phi /\\ ~(P === 0) /\\ (Alpha === [< ";
		}
		else
		{
			sunrollseg = sunrollseg + "      " + lseghp + "(FreeInt(N +Int " + indexOfPointerField + "),Q)(FreeSeq(N +Int "
			  + Integer.toString(nof) + "))\n      H\n  </heap>\n    <counter> N +Int " + Integer.toString(nof + 1) 
			  + "    </counter>\n    CfgItems\n  </config>\n  </form>\n    Phi /\\ ~(P === Q) /\\ (Alpha === [ ";
		}
		
		for(int i=0;i<(nof-1);i++)
		{
			sunrollseg = sunrollseg + "FreeInt(N +Int " + Integer.toString(valueFieldsIndex[i]) + "), ";
		}
		sunrollseg = sunrollseg.substring(0, sunrollseg.length() - 2);
		if (nof>2)
		{
			sunrollseg = sunrollseg + ">] @ FreeSeq(N +Int " + Integer.toString(nof) + "))\n  </form>\n  TaskItems\n </task>\n" 
							  + "  if VALID(Phi ===> ";
		}
		else
		{
			sunrollseg = sunrollseg + "] @ FreeSeq(N +Int " + Integer.toString(nof) + "))\n  </form>\n  TaskItems\n </task>\n" 
			  				  + "  if VALID(Phi ===> ";
		}
		for(int i=0;i<nof;i++)
		{
			sunrollseg = sunrollseg + "(P' === P +Int " + Integer.toString(i) + ") \\/ ";
		}
		
		sunrollseg = sunrollseg.substring(0, sunrollseg.length() - 4);
		sunrollseg = sunrollseg + ")";
	}

	private static void genSRollSeg()
	{
		int valueFieldsIndex[] = new int[nof -1];
		int index = 0;
		int indexOfPointerField = cs.indexOfPointerField(0); 
		
		for(int i=0; i<nof; i++)
		{
			String s = Integer.toString(i);

				srollseg = srollseg + "      (P +Int " + s + ") |-> I" + s + ") : " +
					  "(id(\"" + cs.getName() + "\").id(\"" + cs.nameOfField(i) + "\"))\n";			
			if (indexOfPointerField != (i))
			{
				valueFieldsIndex[index] = i;
				index++;
			}
		}
		
		srollseg = srollseg + "      => " + lseghp + "(P , I" + indexOfPointerField + ")(";
		
		if (nof>2)
		{
			srollseg = srollseg + "[<";
			for(int i=0;i<nof -1;i++)
				{
					srollseg = srollseg + "I" + valueFieldsIndex[i] + ", ";
				}
			srollseg = srollseg.substring(0, srollseg.length() - 2);
			srollseg = srollseg + ">])";
		}
		else
		{
			srollseg = srollseg + "[I" + (valueFieldsIndex[0]) + "])";
		}
	}

	public static void Generate()
	{
		genVars();
		genSUnroll();
		genSUnrolling();
		genSRoll();
		genCRoll();
		genSUnrollSeg();
		genSRollSeg();
		String content = GeneralFunctions.readFileContent("src/patternTemplates/SLList.template");
		content = content.replaceAll("HPNAME", hpname.toUpperCase());
		content = content.replaceAll("hpname", hpname);
		content = content.replaceAll("hpnameseg", lseghp);
		content = content.replace("VARGEN", vars);
		content = content.replace("SIMPLEUNROLL", sunroll);
		content = content.replace("SIMPLEUNROLING", sunrolling);
		content = content.replace("SIMPLEROLL", sroll);
		content = content.replace("COMPLEXROLL", croll);
		content = content.replace("SUNROLLSEG", sunrollseg);
		content = content.replaceAll("SROLLSEG", srollseg);
		content = content.replaceAll(" [+]Int 0", "");
		GeneralFunctions.writeFileContent(content, "src/" + hpname + ".k");
	}
}
