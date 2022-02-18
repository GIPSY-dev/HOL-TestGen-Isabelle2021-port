# HOL-TestGen - specification based test case generation

## Prerequisites
  * [Isabelle 2016-1](https://isabelle.in.tum.de/website-Isabelle2016-1/):
    Please download Isabelle 2016-1 from the
    [Isabelle website](https://isabelle.in.tum.de/website-Isabelle2016-1/)
    and follow the installation instructions given there. In the
    following, we assume that Isabelle 2016-1 can be executed using the
    `isabelle` command on the command line.
  * Z3, version 3.2: You can obtain this version of Z3 as part of the
    (Isabelle
    2013-2)[http://isabelle.in.tum.de/website-Isabelle2013-2/index.html]
    distribution. If you download the isabelle archive for your
    system, you will find a copy of Z3 in the directory
    `Isabelle2013-2/contrib/z3-3.2/x86-linux/z3`. 
    The non-free distribution of HOL-TestGen has a copy of Z3 version 3.2
    for Linux, Windows, and OS X in the contrib folder. 
  

## Installation of HOL-TestGen
HOL-TestGen build system is based on the build system of Isabelle and
can be build on top of Isabelle/HOL:
* Building HOL-TestGen, i.e., HOL-TestGen based on HOL:
```
  isabelle build -b -d . HOL-TestGen
```
  
Similarly, the examples can be build or edited using the build system of 
Isabelle. For example,
  * to interactively work with the example List:
```
    cd examples/unit/List; isabelle jedit -d ../../ -l HOL-TestGen List_test.thy
```
  or 
```
     isabelle jedit -d . -l HOL-TestGen "examples/unit/List/List_test.thy"
```
  * to check the List example in batch mode: 
```
     isabelle build -d . HOL-TestGen-List
```

Moreover, to use the SMT interface, please ensure that the following
two environment variables are set:
```
  OLD_Z3_SOLVER=<path/to/z3-3.2>
  OLD_Z3_NON_COMMERCIAL=yes
```
where `<path/to/z3-3.2>` is the location of Z3 binary (version 3.2). 

In the *non-free* HOL-TestGen distribution, the Z3 binaries are stored in the 
folders
```
  contrib/z3-3.2/x86-linux   # Linux
  contrib/z3-3.2/x86-darwin  # OS X
  contrib/z3-3.2/x86-cygwin  # Windows 
```
Alternatively, ou can obtain this version of Z3 as part of the (Isabelle
2013-2)[http://isabelle.in.tum.de/website-Isabelle2013-2/index.html]
distribution (e.g., for Linux, the binary is `Isabelle2013-2/contrib/z3-3.2/x86-linux/z3`).

## Team 
###Main Contacts:
  * [Achim D. Brucker](http://www.brucker.ch/)
  * [Burkhart Wolff](https://www.lri.fr/~wolff/)
  
###Authors:
  * Achim D. Brucker <adbrucker@0x5f.org>
  * Lukas Bruegger <lukas.a.bruegger@gmail.com>
  * Abderrahmane Feliachi <Abderrahmane.Feliachi@lri.fr>
  * Chantal Keller <Chantal.Keller@lri.fr>
  * Matthias P. Krieger <Matthias.Krieger@lri.fr>
  * Delphine Longuet <delphine.longuet@lri.fr>
  * Yakoub Nemouchi <nemouchi@lri.fr>
  * Frederic Tuong <frederic.tuong@lri.fr>
  * Burkhart Wolff <wolff@lri.fr>

## License
This project is licensed under a 3-clause BSD-style license. Note that add-ons 
(in the `add-ons` folder) may be released under different licenses. In particular,
the non-free distribution of HOL-TestGen may contain add-ons that are subject to 
a non-free license agreement (e.g., restricting the commercial use). 
