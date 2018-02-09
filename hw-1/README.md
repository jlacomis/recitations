# Some hints and resources for Recitation 1

## Instructions

Fill in code in ShiftAnalysis.java to implement the bad shift
analysis discussed in class.  

Your code should emit a warning message if it finds a shift expression whose
right operand is a constant that is less than 0 or greater than 31.


## Docs

You can find a "survivor's guide" for Soot in the `doc` folder

You can find documentation of the Soot API here:

https://soot-build.cs.uni-paderborn.de/public/origin/develop/soot/soot-develop/jdoc/

## Running

From the `src` directory, you can test-run Soot using:

```
java -cp ../soot-trunk.jar soot.Main --help
```

You can compile the Java files with:

```
javac -cp .:../soot-trunk.jar *.java
```

You can now generate Jimple with:

```
java -cp ../soot-trunk.jar soot.Main -cp .:/usr/lib/jvm/java-1.8.0-openjdk-1.8.0.111-1.b15.el7_2.x86_64/jre/lib/rt.jar -f J Foo
```

(You may need to locate your `rt.jar` in a different path above. E.g., `/Library/Java/JavaVirtualMachines/jdk1.8.0_25.jdk/Contents/Home/jre/lib/rt.jar` on Mac)

You can run the two analyses with:

```
java -cp .:../soot-trunk.jar PrintAnalysisMain -cp .:/usr/lib/jvm/java-1.8.0-openjdk-1.8.0.111-1.b15.el7_2.x86_64/jre/lib/rt.jar  -p jap.printanalysis on Shifty

java -cp .:../soot-trunk.jar ShiftAnalysisMain -cp .:/usr/lib/jvm/java-1.8.0-openjdk-1.8.0.111-1.b15.el7_2.x86_64/jre/lib/rt.jar  -p jap.shiftanalysis on Shifty
```

# Notes

Refer to https://github.com/Sable/soot/wiki/Introduction:-Soot-as-a-command-line-tool if any of the above commands aren't working for you.
