import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.StringTokenizer;


public class CProcessor {
	private CStructures fileStructs = new CStructures();
	private Set<String> hpnames = new HashSet<String>();
	
	private String validateHPName(String name)
	{
		if (GeneralFunctions.SetHasElement(this.hpnames, name)) 
		{
			System.out.print("The " + name + " heap pattern name is used in" 
					+ " affiliation with more than one structure!\n");

		    try 
		    {
		    	throw new Exception("An unintended double assignment for a heap pattern name occured!\n");
		    } 
		    catch (Exception e)
		    {
		         e.printStackTrace();;
		         //System.exit(1);
		    }

		}
		else this.hpnames.add(name);
		return name;
	}

	private String validPattern(String pattern, String structure)
	{
		if (pattern.equalsIgnoreCase("tuple") || 
                    pattern.equalsIgnoreCase("singlelinkedlist") || 
                    pattern.equalsIgnoreCase("doublelinkedlist") || 
                    pattern.equalsIgnoreCase("binarytree")) return pattern;
		else
		{
			try
			{
                            System.out.println("The file contains the following pattern in the annotation: " + pattern + ".\n" 
						+ "It is not a recognizable pattern!\n");
                            throw new Exception("Unrecognized heap pattern! Process was halted");
			}
			catch (Exception e)
			{
                            e.printStackTrace();
                            System.exit(1);
			}
		}
		return "";
	}
	
	public int getNumberOfIndependentStructs()
	{
		return fileStructs.getStructSet().size();
	}
	
	public String getString(String original, String starter, String ender)
	{
		int indexofstarter = original.indexOf(starter);
		int indexofender = original.lastIndexOf(ender);

		if ((indexofender != -1) && (indexofstarter != -1))
		{
			return original.substring((indexofstarter + starter.length()), indexofender);
		}
		
		return "";
	}

	public String[] getPattern(String original)
	{
		int startindex, endindex;
		String[] res = {"",""};
		
		startindex = getPatternIndex(original);
		
		if (original.indexOf("//@ pattern ") == startindex)
		{
			String ceva = original.substring(startindex); 
			endindex = ceva.indexOf("\n") + startindex;
			
			String result = "";
			
			if ((startindex != -1) && (endindex != -1))
			{
				result =  original.substring(startindex, endindex+1);
				original = original.substring(endindex+1);
			}
			else
			{
				original = "";
			}
			res[0] = original;
			res[1] = result;
		}
		else if (original.indexOf("/*@ pattern ") == startindex)
		{
			endindex = original.substring(startindex).indexOf("*/") + startindex;
			
			String result = "";
			
			if ((startindex != -1) && (endindex != -1))
			{
				result =  original.substring(startindex, endindex+2);
				original = original.substring(endindex+2);
			}
			else
			{
				original = "";
			}
			res[0] = original;
			res[1] = result;
		}

		return res;
	}
	
	public String[] getStruct(String original)
	{
		int startindex = original.indexOf("struct ");
		int endindex = original.substring(startindex).indexOf("};") + startindex;
		
		String result = "";
		
		if ((startindex != -1) && (endindex != -1))
		{
			result =  original.substring(startindex, endindex);
			original = original.substring(endindex+2);
		}
		else
		{
			original = "";
		}
		String[] res = {original, result};
		return res;
	}

	public String getAnnHP(String information)
	{
		String result = getString(information, "pattern", "<");
		result = result.replaceAll(" ", "");
		return result;
	}
	
	public String getAnnHPName(String information)
	{
		String result = "";
		if (information.contains("*/")) 
		{
			result = getString(information, ">", "*/");			
		}
		else
		{
			result = getString(information, ">", "\n");		
		}
		result = result.replaceAll(" ", "");
		return result;
	}
	
	public String[] getAnnHPPointers(String information, String hpname)
	{
		if (information.indexOf("(") > -1)
		{
			if (hpname.contains("singlelinkedlist"))
			{
				String[] result = {getString(information, "),", ">")};
				return result;
			}
			else if (hpname.contains("doublelinkedlist"))
			{
				String next = getString(information, "),", ",");
				String prev = getString(information, next + ",", ">");
				String[] result = {next, prev};
				return result;
			}
                        else if (hpname.contains("binarytree"))
                        {
				String left = getString(information, "),", ",");
				String right = getString(information, left + ",", ">");
				String[] result = {left, right};
				return result;
			}
			// to be filled with the rest of hp
		}
		return null;
	}
	
	public String[] getAnnInfo(String information)
	{
		if (information.indexOf("(") > -1)
		{
			String str = getString(information,"(",")");
			StringTokenizer st = new StringTokenizer(str, ",");
			String[] info = new String[st.countTokens()];
			int index = 0;
			
			while(st.hasMoreTokens())
			{
				info[index] = st.nextToken().replaceAll(" ", "");
				index++;
			}
			return info;
		}
		else
		{
			return null;
		}
	}	
	
	private int getPatternIndex(String original)
	{
		int indexpattern;
		
		if (original.contains("/*@ pattern") && original.contains("//@ pattern"))
		{
			if (original.indexOf("/*@ pattern") < original.indexOf("//@ pattern"))
				{
					indexpattern = original.indexOf("/*@ pattern"); 
				}
			else
			{
				indexpattern = original.indexOf("//@ pattern");
			}
		}
		else if (original.contains("/*@ pattern")) indexpattern = original.indexOf("/*@ pattern");
		else if (original.contains("//@ pattern")) indexpattern = original.indexOf("//@ pattern");
		else indexpattern = -1;
		
		return indexpattern;
	}
	
	private void getGroups(String original)
	{
		while(original.contains("  "))
		{
			original = original.replaceAll("  ", " ");
		}
		
		original = original.replaceAll(" ;", ";");
		
		int indexpattern;
		
		indexpattern = getPatternIndex(original);
		int indexstruct = original.indexOf("struct ");
		int structend = original.indexOf("};");
		String[] patterns = new String[10];
		int numberofpatternforstruct = 0;
		
		while ((indexstruct > -1) && (structend > -1))
		{
			if ((indexpattern < indexstruct) && (indexstruct > -1) && (indexpattern > -1))
			{
				patterns[numberofpatternforstruct] = getPattern(original)[1];
				numberofpatternforstruct++;
				original = getPattern(original)[0];
				indexpattern = getPatternIndex(original);;
				indexstruct = original.indexOf("struct ");
				structend = original.indexOf("};");
			}
			else if ((indexstruct > -1) && (numberofpatternforstruct>0))
			{
				String struct = getStruct(original)[1];
				original = getStruct(original)[0];
				
				struct = struct.replace("{", "");
				struct = struct.replace("}", "");
				
				StringTokenizer st = new StringTokenizer(struct);
				CStructure s = new CStructure();
				
				st.nextToken();
				s.setName(st.nextToken());
				while(st.hasMoreTokens())
				{
					String type = st.nextToken();
					if (type.contains("struct")) type = type + " " + st.nextToken();
					String field = st.nextToken();
					field = field.replaceAll(";", "");
					s.addFieldToStruct(field, type);
				}
				
				for(int i=0; i< numberofpatternforstruct; i++)
				{
					CStructure strct = new CStructure();
					strct.copy(s);
					String hpattern = getAnnHP(patterns[i]);
					String name = getAnnHPName(patterns[i]);
					
					hpattern = validPattern(hpattern, s.getName());
					name = validateHPName(name);
						
					String[] pointers = getAnnHPPointers(patterns[i],hpattern);
					String[] inf = getAnnInfo(patterns[i]);
					
					StructMetaInfo smi = new StructMetaInfo(hpattern, name, pointers, inf);
					
					GeneralFunctions.refine(strct, smi);
					GeneralFunctions.scramble(strct, smi);
					
					strct.setSmi(smi);
					this.fileStructs.addStruct(strct);
				}

				indexpattern = getPatternIndex(original);
				indexstruct = original.indexOf("struct ");
				structend = original.indexOf("};");
				numberofpatternforstruct = 0;
			}
		}
	}
	
	private void validateAnnStructs()
	{
		// add the code that checks/ interchanges the fields of the structure with the information in the annotation
		Iterator<CStructure> it = fileStructs.getStructSet().iterator();
		
		while(it.hasNext())
		{
			it.next();
		}
	}

	public void process(String PathFileName)
	{
		this.getGroups(GeneralFunctions.readFileContent(PathFileName));
		validateAnnStructs();
	}
	
	public CStructure structNo(int index)
	{
		return fileStructs.getStructure(index);
	}

}