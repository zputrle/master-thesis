This repository contains the master's thesis Consistency of classical synthetic computability theory (sl. Konsistentnost klasične sintetične teorije izračunljivosti) prepared by Žiga Putrle under the supervisor of prof. dr. Andrej Bauer at University of Ljubljana - Faculty of Mathematics and Physics.

# Abstract
Yannick Forster in his doctoral thesis Computability in constructive type theory [5] suggests a new approach towards computability theory that allows development of the theory in a classical way by using proof assistants. He develops the theory in a calculus of inductive constructions (CIC), the underlying type system of Coq proof assistant. He assumes that in CIC we can use synthetic Churches thesis (SCT), law of excluded middle (LEM) and rules of large elimination (RLE) without making the theory inconsistent. He justifies his assumption by referencing similar proven results [5, chapter 7] but he does not provide a proof. Our contribution to Forster’s work is a proof that computability theory developed in CIC + SCT + LEM + RLE is consistent.

We focus on a fragment of CIC that Forster uses to develop the theory and name it fCIC. We prove the consistency of fCIC + SCT + LEM + RLE in two ways. First, we syntactically map judgments from fCIC + SCT + LEM + RLE to fCIC + SCT + RLE where we replace logical propositions with their stable form which allows us to avoid ZIS. Then we build a model of fCIC + SCT + RLE in the theory of realizability. In the second proof, we build the model of fRIK + SCT + ZIS + RLE directly. We model dependent types as families of assemblies, universe of propositions P as assembly ∇Per(K1), where Per(K1) is a category of partial equivalence relations over Kleene’s fist algebra K1, and the universe of stable propositions P¬¬ as an assembly ∇2, where 2 is a set of assemblies 0 and 1.

## Structure of the repository

The master thesis can be found in the current directory under the name ?.
The proof/code written in Agda related to the thesis can be found in `src/PropNotNot.agda` file.

## Getting all the related materials

In order to type-check the code in `src/PropNotNotInAgda`, you also need to checkout the `agda-lib` submodule. For the initial checkout of the repository, you can use
    
    git clone --recurse-submodules git@github.com:zputrle/master-thesis.git
