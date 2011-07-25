import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

public class CStructure {
	private String name;
	private Map<String, String> fields = new LinkedHashMap<String, String>();// <name,type>
	private int numberoffields;
	private StructMetaInfo smi = new StructMetaInfo("", "", null);
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
	
	public void copy(CStructure cs)
	{
		this.name = cs.getName();
		Iterator<Map.Entry<String, String>> it = cs.getFields().entrySet().iterator();
		
		while (it.hasNext())
		{
			Map.Entry<String, String> pair = (Map.Entry<String, String>) it.next();
			this.fields.put(pair.getKey(), pair.getValue());
			System.out.println();
		}
		this.numberoffields = this.fields.size();
		this.smi = null;
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
	
	public String toString()
	{
		String res = "";
		
		Iterator<Map.Entry<String, String>> it = this.fields.entrySet().iterator();
		
		res = name + " \n" + smi + "\nHaving the fields:\n";
		while (it.hasNext())
		{
			Map.Entry<String, String> pair = (Map.Entry<String, String>) it.next();
			res = res + pair.getKey() + " " + pair.getValue() + "\n";
			this.fields.put(pair.getKey(), pair.getValue());
		}
		
		return res;
	}
}
