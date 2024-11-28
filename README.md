[![Java CI with Maven](https://github.com/CodeShield-Security/SPDS/workflows/Java%20CI%20with%20Maven/badge.svg?branch=master)](https://github.com/CodeShield-Security/SPDS/actions)

# IMPORTANT: This version is no longer maintained

An updated version of Boomerang can be found [here](https://github.com/secure-software-engineering/SparseBoomerang). **We highly recommend using this version**. You can also find older Boomerang versions here (not recommended):
- [Boomerang v1](https://github.com/secure-software-engineering/boomerang)
- [Boomerang v2](https://github.com/CROSSINGTUD/SPDS)
- [Boomerang v3.0.0 - v3.1.2](https://github.com/CodeShield-Security/SPDS) (This repository)
- [Boomerang v3.2.0+](https://github.com/secure-software-engineering/SparseBoomerang) (recommended)

# SPDS

This repository contains a Java implementation of Synchronized Pushdown Systems.
Additionally, it contains an implementation of [Boomerang](boomerangPDS) and [IDEal](idealPDS) based on a Weighted Pushdown System.

# Use as Maven dependency

The projects are released on [Maven Central](https://central.sonatype.com/artifact/de.fraunhofer.iem/SPDS) and can be included as a dependency in `.pom` files:

```.xml
<dependencies>
  <dependency>
    <groupId>de.fraunhofer.iem</groupId>
    <artifactId>SPDS</artifactId>
    <version>3.1.2</version>
  </dependency>
</dependencies>
```

# Checkout, Build and Install

To build and install SPDS into your local repository, run 

``mvn clean install -DskipTests``

in the root directory of this git repository. If you do not want to skip the test cases, remove the last flag.

# Examples

Boomerang code examples can be found [here](https://github.com/CodeShield-Security/SPDS/tree/master/boomerangPDS/src/main/java/boomerang/example). Code examples for IDEal are given [here](https://github.com/CodeShield-Security/SPDS/tree/master/idealPDS/src/main/java/inference/example).


# Notes on the Test Cases

The projects Boomerang and IDEal contain JUnit test suites. As for JUnit, the test methods are annotated with @Test and can be run as normal JUnit tests.
However, these methods are *not* executed but only statically analyzed. When one executes the JUnit tests, the test method bodies are supplied as input to Soot 
and a static analysis is triggered. All this happens in JUnit's @Before test time. The test method itself is never run, may throw NullPointerExceptions or may not even terminate.

If the static analysis succeeded, JUnit will officially label the test method as skipped. However, the test will not be labeled as Error or Failure. 
Even though the test was skipped, it succeeded. Note, JUnit outputs a message:

``org.junit.AssumptionViolatedException: got: <false>, expected: is <true>``

This is ok! The test passed!
