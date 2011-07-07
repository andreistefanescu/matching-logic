import java.util.StringTokenizer;


public class CProcessor {
	private CStructures fileStructs = new CStructures();
	
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
		int startindex = original.indexOf("/*@ pattern ");
		int endindex = original.substring(startindex).indexOf("*/") + startindex;
		
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
		String[] res = {original, result};
		return res;
	}
	
	public String[] getStruct(String original)
	{
		int startindex = original.indexOf("struct ");
		int endindex = original.indexOf("};");
		
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
		String result = getString(information, ">", "*/");
		result = result.replaceAll(" ", "");
		return result;
	}
	
	public String[] getAnnHPPointers(String information)
	{
		if (information.indexOf("(") > -1)
		{
			if (getAnnHP(information).contains("singlelinkedlist"))
			{
				String[] result = {getString(information, "),", ">")};
				return result;
			}
			else if (getAnnHP(information).contains("doublelinkedlist"))
			{
				String next = getString(information, "),", ",");
				String prev = getString(information, next + ",", ">");
				String[] result = {next, prev};
				return result;
			}
			// to be filled with the rest of hp
		}
		else
		{
			if (getAnnHP(information).contains("singlelinkedlist"))
			{
				String[] result = {getString(information, "<", ">")};
				return result;
			}
			else if (getAnnHP(information).contains("doublelinkedlist"))
			{
				String next = getString(information, "<", ",");
				String prev = getString(information, ",", ">");
				String[] result = {next, prev};
				return result;
			}
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
	
	private void getGroups(String original)
	{
		while(original.contains("  "))
		{
			original = original.replaceAll("  ", " ");
		}
		
		original = original.replaceAll(" ;", ";");
		
		int indexpattern = original.indexOf("/*@ pattern");
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
				indexpattern = original.indexOf("/*@ pattern");
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
					CStructure strct = s;
					String hpattern = getAnnHP(patterns[i]);
					String name = getAnnHPName(patterns[i]);
					String[] pointers = getAnnHPPointers(patterns[i]);
					String[] inf = getAnnInfo(patterns[i]);
					strct.setSmi(new StructMetaInfo(hpattern, name, pointers, inf));
					this.fileStructs.addStruct(strct);
				}

				indexpattern = original.indexOf("/*@ pattern");
				indexstruct = original.indexOf("struct ");
				structend = original.indexOf("};");
				numberofpatternforstruct = 0;
			}
		}
	}

	public void process(String PathFileName)
	{
		this.getGroups(GeneralFunctions.readFileContent(PathFileName));
	}
	
	public CStructure structNo(int index)
	{
		return fileStructs.getStructure(index);
	}

}