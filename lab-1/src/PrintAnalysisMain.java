import soot.Main;
import soot.PackManager;
import soot.Transform;

public class PrintAnalysisMain {
	public static void main(String[] args) {
		// Inject the analysis tagger into Soot
		PackManager.v().getPack("jap").add(new Transform("jap.printanalysis", PrintAnalysis.instance()));
		
		// Invoke soot.Main with arguments given
		Main.main(args);
	}
}