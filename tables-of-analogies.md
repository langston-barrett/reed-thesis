# Tables of Analogies

The beauty of homotopy type theory and the Curry-Howard isomorphism is that they
allow us to interpret the same syntactical system in many contexts
_simultaneously_. This leads to analogies between these semantics. These
analogies can usefully guide our intuition.

## Types and terms

This table is logically-oriented

| Logic             | Classical ITT              | HoTT                          | Haskell                          | Sets                           |
| ----------------- | -----------------------    | ------------------------- | ------------------------- | ------------------------ |
| Proposition       | Data(type)                 | Space                         | Type                             | Set                            |
| Proof             | Term, program              | Point                         | Program                          | Element                        |
| Predicate A(x)    | Dependent type A(x)        | Fibration                     | Can't be expressed               | Family of sets                 |
| False: ⊥          | Empty type: ⫫              | Empty type: **0**             | `_|_`?                           | Empty set: {}                  |
| True: ⊤           | Unit type: ⫪               | Unit type: **1**              | `()`                             | Set containing empty set: {{}} |
| And: A ∧ B        | Product type: A × B        | Product space: A × B          | `(A, B)`?                        | Cartesian product: A × B       |
| Or: A ∨ B         | Sum type: A + B            | Coproduct space: A ⨿ B        | `Either`                         | Disjoint union: A ⨿ B          |
| A ⇒ B             | Function: A → B            | Continuous function: A → B    | `A -> B`                          | Function: A → B               |
| Negation: ¬ A     | Contradiction: A → ⫫       | Contradiction: A → **0**      | Can't be expressed?               | Function: A → {}              |
| ∀ a in A, B(a)    | Pi type: Π (a : A) B(a)    | Function type: Π (a : A) B(a) | Can't be expressed                | Product                       |
| ∃ a in A, B(a)    | Sigma type: Σ (a : A) B(a) | Pair type: Σ (a : A) B(a)     | Can't be expressed                | Coproduct                     |
| Equality a = b    | Id(a,b), a ≡ b             | Path a ⇝ b                    | `a == b` (`a, b :: A` with `Eq A`) | {(x,x)\|x in A}               |

<!-- TODO: topos theory?? -->


## Equality

This is from the HoTT book (TODO: citation):

| Logic         | Homotopy            | ∞-Groupoids    |
| ------------- | ------------------- | -------------- |
| Reflexivity   | Constant path       | Identity arrow |
| Symmetry      | Inverse path        | Inverse arrow  |
| Transitivity  | Path concatenation  | Composition    |

## UniMath, HoTT book, and HoTT/M-types

| UniMath          | HoTT book               | HoTT/M-types | 
|----------------- | ----------------------- | ------------ | 
| funextfun        | Function extensionality | substⁱ-lemma  |
| maponpaths       | ap                      | app=         |
| total2\_paths\_f | Theorem 2.7.2           | unapΣ        |
| transportf       | transport               | subst        |
