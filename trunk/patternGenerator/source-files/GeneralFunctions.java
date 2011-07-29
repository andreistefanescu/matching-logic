
import java.util.LinkedHashMap;
import java.io.BufferedInputStream;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import sun.reflect.generics.tree.FieldTypeSignature;


public class GeneralFunctions {
	public static String readFileContent(String PathAndFileName)
	{
		byte[] buffer = new byte[(int) new File(PathAndFileName).length()];
	    BufferedInputStream f = null;
	    try {
	        f = new BufferedInputStream(new FileInputStream(PathAndFileName));
	        f.read(buffer);
	    } 
	    catch (Exception e) {
			e.printStackTrace();
	    }
	    finally {
	        if (f != null) try { f.close(); } catch (IOException ignored) { }
	    }
	    String content = new String(buffer);
	    content = content.replaceAll("[ ]*\\*", "\\*");
	    
	    return content;
	}
	
	public static void writeFileContent(String content, String PathAndFileName)
	{
		try {
			BufferedWriter out = new BufferedWriter(new FileWriter(PathAndFileName));
			out.write(content);
			out.close();
		} 
		catch (IOException e) 
		{ 
			e.printStackTrace();
		}
	}
	
	public static int MapHasElement(Map<String,String> map, String element)
	{
		Iterator<Map.Entry<String, String>> it = map.entrySet().iterator();
		int index = 0;
		while(it.hasNext())
		{
			String field = it.next().getKey();
			if (field.contains(element)) return index;
			index++;
		}
		
		return -1;
	}
	
	public static int ArrayHasElement(String[] array, String element)
	{
		for(int i=0; i < array.length; i++)
		{
			if (array[i].contains(element)) return i;
		}
		return -1;
	}
	
	public static Map.Entry<String,String> Field(Map<String,String> map, String fieldname)
	{
		Iterator<Map.Entry<String, String>> it = map.entrySet().iterator();
		
		while(it.hasNext())
		{
			Map.Entry<String,String> field = it.next();
			if (field.getKey().contains(fieldname)) return field;
		}
		return null;
	}
	
	public static boolean SetHasElement(Set<String> set, String element)
	{
		Iterator<String> it = set.iterator();
		while (it.hasNext())
		{
			if (element.equals(it.next())) return true;
		}
		return false;
	}
	
	public static void insert(String[] array, String element, int position)
	{
		if ((position >= array.length) || (position < 0))
		{
			System.out.println("The position is outside the rangre of the array!\n");
			System.exit(1);
		}
		for(int i=array.length-1; i > position; i--)
		{
			array[i] = array[i-1];
		}
		array[position] = element;
	}
	
	public static void refine(CStructure cs, StructMetaInfo smi)
	{
		int firstlength = 0;
		String[] smifields;
		
		if ((smi.pointers() == null) && (smi.valuefields() == null))
		{
			return;
		}
		
		if (smi.valuefields() == null)
		{
			smifields = smi.pointers();
			
			Map<String,String> fields = cs.getFields();
			Map<String,String> newfields = new LinkedHashMap<String,String>();
			
			fields.putAll(cs.getFields());
			Iterator<Map.Entry<String, String>> it = fields.entrySet().iterator();
			
			while(it.hasNext())
			{
				Map.Entry<String, String> entry = it.next(); 
				String key = entry.getKey();
				String val = entry.getValue();
				if (ArrayHasElement(smifields, key) != -1)
				{
					newfields.put(key, val);
				}
			}
			cs.setFields(newfields);
			return;
		}
		
		if (smi.pointers() != null)
		{
			smifields = new String[smi.pointers().length + smi.valuefields().length];
			firstlength = smi.pointers().length;
		}
		else
		{
			smifields = new String[smi.valuefields().length];
		}
		
		for(int i=0; i< smifields.length ; i++)
		{
			if (i < firstlength)
			{
				smifields[i] = smi.pointers()[i];
			}
			else
			{
				smifields[i] = smi.valuefields()[i-firstlength];
			}
		}
		
		for(int i=0; i < smifields.length; i++)
		{
			if (MapHasElement(cs.getFields(), smifields[i]) == -1)
			{
				try
				{
					throw new Exception();
		    	}
				catch (Exception e)
				{
					System.out.println("The " + smifields[i] + " field of the annotation is not a valid field of the \"" + cs.getName() + "\" stucture!\n" + "Process halted!\nPlease review your annotations!");
					System.exit(1);
				}
			}
		}
		
		Map<String,String> fields = cs.getFields();
		Map<String,String> newfields = new LinkedHashMap<String,String>();
		
		fields.putAll(cs.getFields());
		Iterator<Map.Entry<String, String>> it = fields.entrySet().iterator();
		
		while(it.hasNext())
		{
			Map.Entry<String, String> entry = it.next(); 
			String key = entry.getKey();
			String val = entry.getValue();
			
			if (ArrayHasElement(smifields, key) != -1) 
			{
				newfields.put(key, val);
			}
		}
		cs.setFields(newfields);
	}
	
	public static void swap(String[] array, int position1, int position2)
	{
		if ((position1 >= array.length) || (position2 >= array.length))
		{
			System.out.println("The postions for the swap are over the range of the array length!");
			System.exit(1);
		}
		String aux = array[position1];
		array[position1] = array[position2];
		array[position2]  = aux;
	}
	
	public static void scramble(CStructure cs, StructMetaInfo smi)
	{	
		if (smi.valuefields() == null) return;
		
		Map<String,String> copy = new LinkedHashMap<String,String>();
		copy.putAll(cs.getFields());
		Iterator<Map.Entry<String,String>>it = copy.entrySet().iterator();
		String[] fieldname = new String[copy.size()];
		String[] fieldtype = new String[copy.size()];
		int index = 0;
		int loc = 0;
		
		int[] pointerlocation = {-1, -1};
		String[] pointername = {"", ""};
		
		while(it.hasNext())
		{
			Map.Entry<String,String> entry = it.next();
			fieldname[index] = entry.getKey();
			fieldtype[index] = entry.getValue();
			if (entry.getValue().contains("struct " + cs.getName())) 
			{
				pointerlocation[loc] = index;
				pointername[loc] = entry.getKey();
				loc++;
			}
			index++;
		}
		
		String[] smifields = smi.valuefields();
		Map<String,String> newfields = new LinkedHashMap<String,String>();
		
		for(int i=0; i < smifields.length; i++)
		{
			int newlocation = ArrayHasElement(smifields, fieldname[i]);
			if (newlocation != -1)
			{
				swap(fieldname,newlocation,i);
				swap(fieldtype,newlocation,i);
			}
		}
		
		if (pointerlocation[1] != -1) insert(fieldname,pointername[0],pointerlocation[0]); // elementary structure
		if (pointerlocation[1] != -1) insert(fieldname,pointername[1],pointerlocation[1]); // single linked list
		
		for(int i=0; i<fieldname.length; i++)
		{
			newfields.put(fieldname[i], fieldtype[i]);
		}
		
		cs.setFields(newfields);
	}
	
}







