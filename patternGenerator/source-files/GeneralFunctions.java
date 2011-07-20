import java.io.BufferedInputStream;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;


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
}
