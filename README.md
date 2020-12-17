# Formally Verified Bug-free Implementations of Logical Algorithms

Implementation and verification of standard Computational Logic Algorithms

## Contents

* Bool Theory
    * Bool Constants Theory
    * Bool Constant Sets Theory
    * Positive Literal Sets Theory
* Types and Evaluation of Formulas
* Transformation Algorithm to Conjunctive Normal Form
* Transformation Algorithm from CNF to Horn Clauses (Hornify)


## # [booltheory.mlw](https://gitlab.com/releaselab/factor/formally-verified-bug-free-implementations-of-logical-algorithms/-/blob/master/booltheory.mlw) - Boolean Theory


Description of each lemma and axiom proved/needed for each file.

Boolean Theory file with two modules (Bool and BoolImplementation)

**Boolean type:**

```
type t
constant bot: t
constant top: t
```

**Properties**: Bool module


1. axiom and_neutral : forall x. x /\*\ top = x
2. axiom or_neutral : forall x. x \\\*/ bot = x

All other properties can be deducted from the axioms above.

3. lemma or_elem_abso: forall x. x \\\*/ top = top
4. lemma and_elem_abso: forall x. x /\*\ bot = bot
5. lemma and_assoc: forall x y z. x /*\ (y /*\ z) = (x /*\ y) /*\ z
6. lemma or_assoc: forall x y z. x \*/ (y \*/ z) = (x \*/ y) \*/ z
7. lemma and_comm : forall x y : t. x /*\ y = y /*\ x
8. lemma or_comm : forall x y : t. x \*/ y = y \*/ x
9. lemma and_distr : forall x y z : t. x /*\ ( y \*/ z) = (x /*\ y ) \*/ (x /*\ z)
10. lemma or_distr : forall x y z : t. x \*/ (y /*\ z) = (x \*/ y) /*\  (x \*/ z) 
11. lemma compl_bot : forall x : t. x /*\ neg x = bot
12. lemma compl_top : forall x : t. x \*/ neg x = top
13. lemma doubleneg: forall b. neg (neg b) = b
14. lemma deMorgan_and: forall x1 x2. neg ((x1 /\*\ x2)) = ((neg x1) \\\*/ (neg x2))
15. lemma deMorgan_or: forall x1 x2. neg ((x1 \\\*/ x2)) = ((neg x1) /\*\ (neg x2)) 
16. lemma repr_of_top : (top) = (neg (bot))
17. lemma implEquiv: forall x1 x2. (x1 ->* x2) = ((neg x1) \\\*/ x2)


## # [setstheory.mlw](https://gitlab.com/releaselab/factor/formally-verified-bug-free-implementations-of-logical-algorithms/-/blob/master/setstheory.mlw) - Sets Theory


Theory for boolean sets and formula sets.

##### BoolSet module: Boolean Set

Eval functions (negative eval and positive eval). The negative evals take advantage of the disjunction connective and the positive of the conjunction connective.

**Lemmas**:

*  Derivation -- neg (eval_positive s) = eval_negative s
*  Evaluation of set with added elements -- eval_negative (add x s) = ((neg (x)) \\\*/ eval_negative s ) **and** eval_positive (add x s) = ((x) /\*\ eval_positive s )
*  Evaluation absorbent elements -- forall s x. x = bot -> (eval_positive (add x s) = bot) **and** forall s x. x = bot -> (eval_negative (add x s) = top)
*  Evaluation neutral elements -- forall s x. x = top -> (eval_positive (add x s) = eval_positive s) **and** forall s x. x = top -> (eval_negative (add x s) = eval_negative s)


##### PropositionalFormulaSet module: Formula Set

Positiveliteral type (containing only Prop and Var). The evaluation function and an additional function to cast a set of positiveliteral to a set of bool.
The negative and positive evaluations uses the functions defined in the BoolSet module.

**Axioms**:

*  Cast with empty set **--** forall s f. is_empty s -> cast_setPF_setB s f = empty
*  Cast with not empty set **--** forall s f. not (is_empty s) -> forall x. mem x s -> cast_setPF_setB s f = add (eval_pl x f) (cast_setPF_setB (remove x s) f)

**Lemmas**:

*  Derivation -- neg (eval_positive s f) = eval_negative s f
*  Evaluation of set with added elements  -- eval_negative (add x s) f = ((neg (eval_pl x f)) \\\*/ eval_negative s f ) **and** eval_positive (add x s) f = ((eval_pl x f) /\*\ eval_positive s f )
*  Evaluation of absorbent elements -- forall s x f. (eval_pl x f) = bot -> (eval_positive (add x s) f = bot) **and** forall s x f. (eval_pl x f) = bot -> (eval_negative (add x s) f = top)
*  Evaluation of neutral elements -- forall s x f. (eval_pl x f) = top -> (eval_positive (add x s) f = eval_positive s f) **and** forall s x f. (eval_pl x f) = top -> (eval_negative (add x s) f = eval_negative s f)
* Evaluation of singleton --  forall x e1 e2 f. e1 = CPL x /\ e2 = singleton x -> eval_positive e2 f = Horn.eval_positive e1 f



## # [formula.mlw](https://gitlab.com/releaselab/factor/formally-verified-bug-free-implementations-of-logical-algorithms/-/blob/master/formula.mlw) - Formula Types

This file has all the types of formulas and their respective evaluation function.

* Standard Formula (module PropositialFormula)
* Types for CNFC (module ConjunctiveNormalForm)
* Types for Hornify (module Horn)


Standard PropositionalFormula type with the following constructors:

```
Prop
Var
Neg
And
Or
Impl
```

## # [cnf.mlw](https://gitlab.com/releaselab/factor/formally-verified-bug-free-implementations-of-logical-algorithms/-/blob/master/cnf.mlw) - Transformation Algorithm to Conjunctive Normal Form

Implementation and Verification of the Transformation Algorithm to Conjunctive Normal Form.

**Functions:**

* ImplFree
* NNFC
* CNFC
* T (composition of the functions above)


## # [hornify.mlw](https://gitlab.com/releaselab/factor/formally-verified-bug-free-implementations-of-logical-algorithms/-/blob/master/hornify.mlw) - Transformation Algorithm from CNF to Horn Clauses

Implementation and Verification of the Transformation Algorithm from CNF to Horn Clauses.

It uses sets to identify the negative/positive literals of a specific formulae.

## # [horn.mlw](https://gitlab.com/releaselab/factor/formally-verified-bug-free-implementations-of-logical-algorithms/-/blob/master/horn.mlw) - Horn-satisfiability algorithm

Implementation and Verification of the Horn-satisfiability algorithm.

Deciding whether a given set of propositional Horn clauses is satisfiable or not.


## Authors

* **Pedro Barroso**
* **Mário Pereria** 
* **António Ravara**

## Acknowledgments

* Marco Giunti
* Tezos
