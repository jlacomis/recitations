import soot.BodyTransformer;
import soot.Body;
import soot.Unit;
import soot.SootMethod;
import soot.NormalUnitPrinter;
import soot.jimple.Stmt;
import java.util.Map;
import soot.jimple.DefinitionStmt;
import soot.jimple.BinopExpr;
import soot.jimple.NumericConstant;
import soot.jimple.IntConstant;
import soot.Value;

public class ShiftAnalysis extends BodyTransformer {
    @Override
    protected void internalTransform(Body body,
                                     String phaseName,
                                     Map<String,String> options) {
        NormalUnitPrinter printer = new NormalUnitPrinter(body);
        SootMethod method = body.getMethod();
        System.out.println("analyzing the body of "
                           + method.getDeclaringClass().getName()
                           + "." + method.getName());
        System.out.println();
        for (Unit unit : body.getUnits()) {
            Stmt stmt = (Stmt) unit;
            if (stmt instanceof DefinitionStmt) {
                DefinitionStmt def = (DefinitionStmt) stmt;
				
				// get the right-hand side
				
				// test if there is an operator, and test if it is a shift
				// OK to focus just on one of shift left or shift right for this lab
				
				// test if what we are shifting by is a constant
				
				// test whether the constant is negative
				// bonus: also test if the constant is >31
				
				// emit a warning if so
				
				// HINT: NumericConstant.lessThan(...) returns a NumericConstant that is 1 or 0, representing true or false respectively (it's a flawed design...)
				// HINT: you can create an IntConstant for a number n with IntConstant.v(n)
				
            }
        }
    }

    private static ShiftAnalysis theInstance = new ShiftAnalysis();
    public static ShiftAnalysis instance() {
        return theInstance;
    }
}
