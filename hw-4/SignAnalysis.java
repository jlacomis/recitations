package edu.cmu.se355.hw4;

import soot.BodyTransformer;
import soot.Body;
import soot.Unit;
import soot.Scene;
import soot.SootField;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.Stmt;
import java.util.Map;
import java.util.Set;
import java.util.HashSet;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.Value;
import soot.*;
import soot.toolkits.scalar.*;
import soot.toolkits.graph.*;

    /** This analysis identifies the sign of integer variables
     * and warns when a definitely or possibly negative variable
     * is used as an array index.
     */
public class SignAnalysis extends BodyTransformer {
    @Override
    protected void internalTransform(Body body,
                                     String phaseName,
                                     Map options) {
        new GuaranteedDefs(new ExceptionalUnitGraph(body));
        // print guaranteed defs for each unit
    }

    private static SignAnalysis theInstance = new SignAnalysis();
    public static SignAnalysis instance() {
        return theInstance;
    }
}
