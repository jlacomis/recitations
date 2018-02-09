Soot describes how to implement a dataflow analysis here:

https://github.com/Sable/soot/wiki/Implementing-an-intra-procedural-data-flow-analysis-in-Soot

A good example is `GuaranteedDefs.java`. This folder contains a 
`GuaranteedDefs.java` that works with the sign analysis distribution.

In this lab we'll go over `GuaranteedDefs.java` and how it interfaces with
Soot's dataflow API.

We'll make a temporary modification to `SignAnalysis.java` so that it invokes
the `GuaranteedDefs` analysis.  The important modification is `SignAnalysis`:

```java
    protected void internalTransform(Body body,                                     
                                     String phaseName,                              
                                     Map options) {                                 
        new GuaranteedDefs(new ExceptionalUnitGraph(body));                         
        // TODO print out guaranteed defs for each unit                                  
    } 
```

Our small TODO will be to print the list of guaranteed definitions for each
program point that was analyzed.

