import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class CStructures {
	private List<CStructure> structSet = new LinkedList<CStructure>();
	
	public void addStruct(CStructure cs)
	{
		structSet.add(cs);
	}
	
	public CStructure getStructure(int index)
	{
		Iterator<CStructure> it = structSet.iterator();
		while ((index > 0) && (it.hasNext()))
		{
			it.next();
			index--;
		}
		if (it.hasNext()) return it.next();
		return null;
	}
	
	public void setStructSet(List<CStructure> structSet) {
		this.structSet = structSet;
	}

	public List<CStructure> getStructSet() {
		return structSet;
	}
	
	public String toString()
	{
		String res = "";
		Iterator<CStructure> it = structSet.iterator();
		
		while (it.hasNext())
		{
			res = res + it.next() + "\n";
		}
		
		return res;
	}
}
