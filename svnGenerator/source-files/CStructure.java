import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

public class CStructure {
	private String name;
	private Map<String, String> fields = new LinkedHashMap<String, String>();// <name,type>
	private int numberoffields;
	private StructMetaInfo smi;
	private int size;
	
	public void addFieldToStruct(String FieldName, String FieldType)
	{
		fields.put(FieldName, FieldType);
		this.numberoffields+=1;
	}

	public int getNumberoffields() {
		return numberoffields;
	}
	
	public int numberOfElementaryFileds()
	{
		int noef = 0;
		Iterator<Map.Entry<String, String>> it = fields.entrySet().iterator();
		
		while(it.hasNext())
		{
			Map.Entry<String, String> pair = it.next();
			String type = pair.getValue();
			if (type.equalsIgnoreCase("int")) noef++;
		}
		
		return noef;
	}
	
	public int indexOfPointerField(int startPoint)
	{
		Iterator<Map.Entry<String, String>> it = fields.entrySet().iterator();
		int index = startPoint;
		while ((0 < startPoint) && (it.hasNext()))
		{
			it.next();
			startPoint--;
		}

	    while (it.hasNext()) 
	    {
	    	Map.Entry<String, String> pair = (Map.Entry<String, String>) it.next();
	    	if (pair.getValue().contains("struct "+ name + "*")) 
	    		{
	    			return (index);
	    		}
	    	else
	    	{
	    		index++;
	    	}
	    }
	    
		return -1;
	}

	public String nameOfField(int index)
	{
		Iterator<Map.Entry<String, String>> iterator = fields.entrySet().iterator();
		while ((index > 0) && (iterator.hasNext()))
		{
			iterator.next();
			index--;
		}
		if (iterator.hasNext())
		{
			Map.Entry<String, String> pair = iterator.next();
			return pair.getKey();
		}
		else
		{
			System.out.println("\npublic String nameOfField(int index)\nPlease check your index!\n");
			return "";
		}
	}
	
	public String typeOfField(int index)
	{
		Iterator<Map.Entry<String, String>> iterator = fields.entrySet().iterator();
		while ((index > 0) && (iterator.hasNext()))
		{
			iterator.next();
		}
		if (iterator.hasNext())
		{
			Map.Entry<String, String> pair = iterator.next();
			return pair.getValue();
		}
		else
		{
			System.out.println("\npublic String typeOfField(int index)\nPlease check your index!\n");
			return "";
		}
	}
	
	public String nameForPointerField()
	{
		Iterator<Map.Entry<String, String>> it = fields.entrySet().iterator();

	    while (it.hasNext()) 
	    {
	    	Map.Entry<String, String> pair = (Map.Entry<String, String>) it.next();
	    	if (pair.getValue().contains("struct "+ name+"*")) 
	    		{
	    			return pair.getKey();
	    		}
	    }
		return "";
	}
	
	public String nameForValueField(int startPos)
	{
		Iterator<Map.Entry<String, String>> it = fields.entrySet().iterator();
		
		while ((it.hasNext()) && (startPos > 0)) 
		{
			it.next();
			startPos--;
		}

	    while (it.hasNext())
	    {
	    	Map.Entry<String, String> pair = (Map.Entry<String, String>) it.next();
	    	if (! pair.getValue().contains("struct "+ name+"*")) 
	    		{
	    			return pair.getKey();
	    		}
	    }
		return "";
	}
	
	public int indexNext()
	{
		Iterator<Map.Entry<String, String>> it = fields.entrySet().iterator();
		int index = 0;
		while (it.hasNext())
	    {
	    	Map.Entry<String, String> pair = (Map.Entry<String, String>) it.next();
	    	if (! pair.getKey().contains(smi.pointers()[0])) 
	    		{
	    			index++;
	    		}
	    	if (pair.getKey().contains(smi.pointers()[0])) 
    		{
    			break;
    		}
	    }
		return index;
	}
	
	public int indexPrev()
	{
		Iterator<Map.Entry<String, String>> it = fields.entrySet().iterator();
		int index = 0;
		while (it.hasNext())
	    {
	    	Map.Entry<String, String> pair = (Map.Entry<String, String>) it.next();
	    	if (! pair.getKey().contains(smi.pointers()[1])) 
	    		{
	    			index++;
	    		}
	    	if (pair.getKey().contains(smi.pointers()[1])) 
    		{
    			break;
    		}
	    }
		return index;
	}
	
	public Map<String,String> getFields()
	{
		return fields;
	}
	
	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	public void setNumberoffields(int numberoffields) {
		this.numberoffields = numberoffields;
	}

	public void setSmi(StructMetaInfo smi) {
		this.smi = smi;
	}

	public StructMetaInfo getSmi() {
		return smi;
	}

	public boolean isSLL()
	{
		if (smi.pattern().contains("singlelinkedlist")) return true;
		return false;
	}
	
	public boolean isDLL()
	{
		if (smi.pattern().contains("doublelinkedlist")) return true;
		return false;
	}

	public void refine()
	{
		String[] fields = smi.fields();
		for(int i=0; i<fields.length;i++)
		{
			
		}
	}

	public void setSize(int size) {
		this.size = size;
	}

	public int getSize() {
		return size;
	}

}
