import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;

public class CStructures {
	private Set<CStructure> structSet = new LinkedHashSet<CStructure>();
	
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
	
	public void setStructSet(Set<CStructure> structSet) {
		this.structSet = structSet;
	}

	public Set<CStructure> getStructSet() {
		return structSet;
	}
}
