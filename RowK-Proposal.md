# Row-K 

## Motivation 

Target's `row-types` library is an excellent, stable, well-tested, and well designed implementation of Row Types in Haskell. I believe most users looking for an extensible records library for ordinary everyday programming tasks would be hard pressed to find a better choice.

Having an excellent, stable Row Types library is a boon to the Haskell ecosystem. However, development on `row-types` proceeds very slowly. The maintainers (rightfully) do not show much interest in incorporating experimental features or pushing the boundaries of what a Row Types implementation can achieve. 

This project (tentative name: `row-k`) aims to serve as an aggressively experimental complement to `row-types`. `row-types` provides an excellent starting point for type-theory-focused experimental extensions. This project is not meant to replace its parent library, but to serve as a complement to it. My hope is that the experiments here, should they be prove successful, could be incorporated upstream once they have achieved the requisite measure of stability. 

## First steps

The classes `Forall`/`BiForall` form the logical core of `row-types` internal machinery. While these type classes (and their methods `metamorph`/`bimetamorph`) facilitate a variety of essential functions for transforming typed paramaterized by rows, they are neither as expressive or powerful as they could be. Consider `Forall`: 

```haskell
class Forall (r :: Row k) (c :: k -> Constraint)
```

This class enables operations on rows which depend on every element of some row satisfying a constraint. While this is sufficiently powerful for many purposes, this formulation of the row-quantifier type class precludes transformations which depend on some _relation_ between the elements of a row and the labels of that row. Note that, if we have row quantifier class which operates on relational constraints, we can redefine `Forall` as a special case of that class where the relational constraint is ignored. 

As a first step towards bolder experiments, I have defined a class 

```haskell 
class ForallX (r :: Row k) (c :: Symbol -> k -> Constraint)
```

and it's BiForall analog, and redefined the existing `Forall`/`BiForall` classes in terms of these.

The initial goal of this project is to explore new design space opened up by these stronger row quantifiers. A secondary goal is to investigate additional feature enhancements based on develops in GHC (especially in the 9.2 and 9.4.1 alpha releases). 

To advance towards these goals, I propose the following batch of initial changes (as the relational row quantifiers are already implemented, they are not included here): 

1) Implement explicit kind signatures wherever possible (to improve kind/type inference). 

2) Update existing kind signatures to conform with `NoStarIsType` 

3) *Reorder constraint arguments*: Because `ForallX` operates with constraint arguments of kind `Symbol -> k -> Constraint` (and `BiForallX` operates with constraint arguments of kind `Symbol -> k1 -> k2 -> Constraint`), existing constraints (e.g. `HasType`) should have their arguments reordered for more convenient use with those classes. 

4) *Replace labels with singletons*: Since any `Sing (s :: Symbol)` can serve as a dictionary for `KnownSymbol s`, moving from Labels to Singletons should allow for some simplification of constraints, and opens up the possibility of incorporating additional features from `singletons`

5) *Aggressively refactor type signatures using {-# ImpredicativeTypes -#}*: QuickLook impredicativity in GHC 9.2 allows for far more expressive type synonyms, which should be used to greatly improve readability in complex internal modules. 

6) *Additional axioms*: The current set of axioms in `row-types` is not comprehensive and could be expanded to facilitate more complex transformations of row-paramaterized types. 

7) *Richer notion of subset/containment*: The present implementation of Subset is type-family based and cannot be used to support sophisticated relationships between quantified rows. It should be replaced with a more robust (type class based) implementation. 
