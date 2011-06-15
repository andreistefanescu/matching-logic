import java.util.Map;


public class ParametrizedPatterns {

	/**
	 * @param args
	 */
	public static void main(String[] args) {

		//KProcessor.replaceRealNamesSingleLinkedList(args[0]);
		
		CProcessor cp = new CProcessor();
		cp.process(args[0]);//"src/CSourceFiles/sllanddll.c");

		int no = cp.getNumberOfIndependentStructs();
		/*
		CStructure cs1 = new CStructure();
		cs1.setName("simple");
		cs1.addFieldToStruct("ceva", "int");
		cs1.addFieldToStruct("altceva", "int");
		cs1.addFieldToStruct("lucru", "int");
		
		ElementaryFieldsOnlyGenerator efg = new ElementaryFieldsOnlyGenerator(cs1, "hpsimple");
		efg.Generate(); 
		
		CStructure cs2 = new CStructure();
		cs2.setName("btree");
		cs2.addFieldToStruct("info", "int");
		cs2.addFieldToStruct("info2", "int");
		cs2.addFieldToStruct("left", "struct btree*");
		cs2.addFieldToStruct("right", "struct btree*");
		
		String[] pointers = {"right", "left"};
		StructMetaInfo smi = new StructMetaInfo("binarytree", "bt", pointers);
		cs2.setSmi(smi);
		
		BinaryTreeGenerator btg = new BinaryTreeGenerator(cs2, "binarytree");
		btg.Generate();
		*/
		for (int i=0; i < no; i++)
		{
			CStructure cs = cp.structNo(i);
			String name = cs.getName();
			
			int noelemfields = cs.numberOfElementaryFileds();
			if (noelemfields > 1)
			{
				MathObjUpleGenerate.generatePatternFile(noelemfields);
			}
			if (cs.isSLL())
			{
				//System.out.println("SLL " + cs.getName());
				SingleLinkedListGenerator sllg = new SingleLinkedListGenerator(cs, cs.getSmi().name());
				sllg.Generate();
			} 
			else
			if (cs.isDLL())
			{
				//System.out.println("DLL " + cs.getName());
				DoubleLinkedListGenerator dllg = new DoubleLinkedListGenerator(cs, cs.getSmi().name());
				dllg.Generate();
			}
		}	
	}

}
