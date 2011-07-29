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

	public static void main(String[] args) {

	File folder = new File("../CsourceFiles/");
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
				cp.process("../CSourceFiles/"+filename);
				theBody(cp);
			}
		}
	}
	
	

	//theBody(cp);
		
		
		/*
		CStructure cs1 = new CStructure();
		cs1.setName("simple");
		cs1.addFieldToStruct("ceva", "int");
		cs1.addFieldToStruct("altceva", "int");
		cs1.addFieldToStruct("lucru", "int");
		
		ElementaryFieldsOnlyGenerator efg = new ElementaryFieldsOnlyGenerator(cs1, "hpsimple");
		efg.Generate(); 
		*/
		
	}

}
