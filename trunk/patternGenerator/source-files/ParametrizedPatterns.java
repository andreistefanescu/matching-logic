import java.io.File;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

public class ParametrizedPatterns {
    public static void theBody(CProcessor cp)
	{
		int no = cp.getNumberOfIndependentStructs();
		
		for (int i=0; i < no; i++)
		{
			CStructure cs = cp.structNo(i);
			String name = cs.getName();
			
			int noelemfields = cs.numberOfElementaryFileds();
			if (noelemfields > 1)
			{
				MathObjUpleGenerate.generatePatternFile(noelemfields);
			}
			if (cs.getSmi().pattern().equalsIgnoreCase("simple"))
			{
				new ElementaryFieldsOnlyGenerator(cs).Generate();
			}
			else
			if (cs.getSmi().pattern().equalsIgnoreCase("singlelinkedlist"))
			{
				SingleLinkedListGenerator sllg = new SingleLinkedListGenerator(cs);
				sllg.Generate();
			} 
			else
			if (cs.getSmi().pattern().equalsIgnoreCase("doublelinkedlist"))
			{
				DoubleLinkedListGenerator dllg = new DoubleLinkedListGenerator(cs);
				dllg.Generate();
			}
			else
			if (cs.getSmi().pattern().equalsIgnoreCase("binarytree"))
			{
				new BinaryTreeGenerator(cs).Generate();
			}
		}	
	}

    public static void theClean()
    {
        String content = GeneralFunctions.readFileContent(GlVars.semantics + "/Makefile");
        content = GeneralFunctions.cleanContent(content, "#GENERATEDCONTENTSTART", "#END_EXT_K");
        content = GeneralFunctions.cleanContent(content, "$(EXT_K_MAIN)", "#GENERATEDCONTENTSTOP");
        GeneralFunctions.writeFileContent(GlVars.semantics + "/Makefile", content);
        
        content = GeneralFunctions.readFileContent(GlVars.semantics + "/matchC.k");
        content = GeneralFunctions.cleanContent(content, "***LOADPATTERNSSTART", "***LOADPATTERNSSTOP");
                content = GeneralFunctions.cleanContent(content, "***ADDMODULESSTART", "***ADDMODULESSTOP");
        GeneralFunctions.writeFileContent(GlVars.semantics + "/matchC.k", content);
        
        content = GeneralFunctions.readFileContent(GlVars.lib+"/config.maude");
        content = GeneralFunctions.cleanContent(content, "***newheapnamesstart", "***newheapnamesstop");
        GeneralFunctions.writeFileContent(GlVars.lib +"/config.maude", content);
    }
        
    public static void main(String[] args) {

        theClean();
        
	File folder = new File(GlVars.patternGenFile + "/CsourceFiles/");
	File[] listOfFiles = folder.listFiles();
	int numberoffiles = listOfFiles.length;
	
	List<String> fileProcessors = new LinkedList<String>(); 
	CProcessor cp = new CProcessor();

	for (int i = 0; i < listOfFiles.length; i++) 
	{
		if (listOfFiles[i].isFile()) 
		{
			String filename = listOfFiles[i].getName();
			if (filename.contains(".c")) 
			{
				//fileProcessors.add(filename);
				cp.process(GlVars.patternGenFile + "/CSourceFiles/"+filename);
				theBody(cp);
			}
		}
	}/* */
    }
}
