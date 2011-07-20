
public class MathObjUpleGenerate {
	private static String content = "";
	

	private static String generate(int total)
	{	
		content = "mod MATHEMATICAL-"+ Integer.toString(total) + "UPLE-BUILTIN-MODULE is\n";
		content = content + "  inc MATHEMATICAL-SEQUENCE-BUILTIN-MODULE .\n";
		content = content + "  sorts PE" + Integer.toString(total) + "Uple " + 
						  "FE" + Integer.toString(total) + "Uple " +
						  "Free" + Integer.toString(total) + "Uple " + 
						  Integer.toString(total) + "Uple " + 
						  Integer.toString(total) + "Uple++ .\n";
		content = content + "  subsort PE" + Integer.toString(total) + "Uple < PEMathObj .\n";
		content = content + "  subsort FE" + Integer.toString(total) + "Uple < FEMathObj .\n";
		content = content + "  subsort Free" + Integer.toString(total) + "Uple < FreeMathObj .\n";
		content = content + "  subsort " + Integer.toString(total) + "Uple < MathObj .\n";
		content = content + "  subsort " + Integer.toString(total) + "Uple++ < MathObj++ .\n\n";
		
		content = content + "  op ?" + Integer.toString(total) + "Uple : Nat -> PE" + Integer.toString(total) + "Uple .\n";
		content = content + "  op !" + Integer.toString(total) + "Uple : Nat -> FE" + Integer.toString(total) + "Uple .\n";
		content = content + "  op Free" + Integer.toString(total) + "Uple : Nat -> Free" + Integer.toString(total) + "Uple .\n\n";
		
		content = content + "  op skolem : Nat PE" + Integer.toString(total) + "Uple -> Free" 
						  + Integer.toString(total) + "Uple [ditto] .\n";
		content = content + "  op co-skolem : Nat Free" + Integer.toString(total) + "Uple -> FE"
				    	  + Integer.toString(total) + "Uple [ditto] .\n\n";
		
		int index = 1;
		String constr, args, vars, left, right;
		constr = args = vars = left = right = "";
		
		while (index <= total)
		{
			constr = constr + "_,";
			args = args + "Int++ ";
			vars = vars + "I" + Integer.toString(index) + " "
			  			+ "I" + Integer.toString(index) + "' ";
			left = left + "I" + Integer.toString(index) + ", ";
			right = right + "I" + Integer.toString(index) + "', ";
			index++;
		}
		constr = constr.substring(0, constr.length() - 1);
		left = left.substring(0, left.length() - 2);
		right = right.substring(0, right.length() - 2);
		
		content = content + "  op <" + constr + "> : " + args + "-> " + Integer.toString(total) + "Uple++ .\n\n";
		content = content + "  eq <" + left + "> === <" + right + "> = [" + left + "] === [" + right + "] .\n\n";
		content = content + "endm \n\n";
		
		//System.out.println(content);
		
		return content;
	}

	public static void generatePatternFile(int functionalNumber)
	{
		generate(functionalNumber);
		GeneralFunctions.writeFileContent(content, "../GeneratedContent/" + Integer.toString(functionalNumber) + "Uple.maude");
	}
}
