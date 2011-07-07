public class StructMetaInfo {
	private String pattern = "", name = "";
	private String[] pointers;
	private String[] valuefields;

	public StructMetaInfo(String pattern, String name, String[] pointers)
	{
		this.pattern = pattern;
		this.name = name;
		this.pointers = pointers;
	}
	
	public StructMetaInfo(String pattern, String name, String[] pointers, String[] fields)
	{
		this.pattern = pattern;
		this.name = name;
		this.pointers = pointers;
		this.valuefields = fields;
	}
	
	public void setFields(String[] fields)
	{
		this.valuefields = fields;
	}
	
	public String[] fields()
	{
		return this.valuefields;
	}
	
	public String name()
	{
		return this.name;
	}
	
	public String pattern()
	{
		return this.pattern;
	}
	
	public String[] pointers()
	{
		return this.pointers;
	}
}
