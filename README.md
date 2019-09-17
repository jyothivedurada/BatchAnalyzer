# BatchAnalyzer

BatchAnalyzer is a batch alias analysis implementation for Java.  It is built on top of [Demand driven points-to analysis](http://web.cs.ucla.edu/~harryxu/tools/alias.htm) and [Soot](https://sable.github.io/soot/).

BatchAnalyzer takes a set of alias queries as input, forms batch queries from the input set and solves the resultant batch queries.

# Instructions

This project is an eclipse project and can be imported into your workspace. It depends on the git repositories [Soot](https://github.com/Sable/soot). Create an eclipse project of Soot from its source and add it as a required project on the build path of BatchAnalyzer.

The package "edu.iitm.cse.alias.batch.analysis" contains the code for batch alias analysis (BATCH and SBATCH).  The implementations for BASIC, RT, VC and SMART are present in 'PAMain.java'.

'DacapoAnalysis.java' contains the driver code. Different implementation variants can be run by invoking runAliasAnalysisImpl() with the respective invariant enum code. For example, 

```
runAliasAnalysisImpl(AnalysisVariant.BATCH);
```

# Licencse
BatchAnalyzer is released under MIT LICENSE - see [LICENSE.txt](LICENSE.txt) for details.

# Authors
BatchAnalyzer has been developed by [Jyothi Vedurada](mailto:jyothi.vedurada@gmail.com).

Advisor: V Krishna Nandivada, nvk@iitm.ac.in
