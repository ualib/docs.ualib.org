---
layout: default
title : "Preface (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "the agda-algebras development team"
---

## <a id="preface">Preface</a>

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe #-}

module Preface where

\end{code}

To support formalization in type theory of research level mathematics in universal algebra and related fields, we present the [Agda Universal Algebra Library](https://github.com/ualib/agda-algebras) (or [agda-algebras](https://github.com/ualib/agda-algebras) for short), a library for the [Agda][] proof assistant which contains definitions, theorems and proofs from the foundations of universal algebra. In particular, the library formalizes the First (Noether) Isomorphism Theorem and the [Birkhoff HSP Theorem](https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem) asserting that every variety is an equational class.

### <a id="vision-and-goals">Vision and goals</a>

The idea for the [agda-algebras](https://github.com/ualib/agda-algebras) project originated with the observation that, on the one hand a number of basic and important constructs in universal algebra can be defined recursively, and theorems about them proved inductively, while on the other hand the *types* (of type theory---in particular, [dependent types][] and [inductive types][]) make possible elegant formal representations of recursively defined objects, and constructive (*computable*) proofs of their properties. These observations suggest that there is much to gain from implementing universal algebra in a language that facilitates working with dependent and inductive types.

#### <a id="primary-goals">Primary goals</a>

The first goal of [agda-algebras](https://github.com/ualib/agda-algebras) is to demonstrate that it is possible to express the foundations of universal algebra in type theory and to formalize (and formally verify) the foundations in the Agda programming language. We will formalize a substantial portion of the edifice on which our own mathematical research depends, and demonstrate that our research can also be expressed in type theory and formally implemented in such a way that we and other working mathematicians can understand and verify the results. The resulting library will also serve to educate our peers, and encourage and help them to formally verify their own mathematics research.

Our field is deep and wide and codifying all of its foundations may seem like a daunting task and a possibly risky investment of time and energy.  However, we believe our subject is well served by a new, modern, [constructive](https://ncatlab.org/nlab/show/constructive+mathematics) presentation of its foundations.  Our new presentation expresses the foundations of universal algebra in the language of type theory, and uses the Agda proof assistant to codify and formally verify everything.

#### <a id="secondary-goals">Secondary goals</a>

We wish to emphasize that our ultimate objective is not merely to translate existing results into a more modern and formal language.  Indeed, one important goal is to develop a system that is useful for conducting research in mathematics, and that is how we intend to use our library once we have achieved our immediate objective of implementing the basic foundational core of universal algebra in Agda.

To this end, our long-term objectives include

+ domain specific types to express the idioms of universal algebra,
+ automated proof search for universal algebra, and
+ formalization of theorems discovered in our own (informal) mathematics research,
+ documentation of the resulting Agda library so it is usable by others.

For our own mathematics research, we believe a proof assistant like Agda, equipped with a specialized library for universal algebra is an extremely useful research tool. Thus, a secondary goal is to demonstrate (to ourselves and colleagues) the utility of such technologies for discovering new mathematics.

### <a id="logical-foundations">Logical foundations</a>

The [Agda Universal Algebra Library][] is based on a minimal version of [Martin-Löf dependent type theory][] (MLTT) as implemented in Agda. More details on this type theory can be read at [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory).


### <a id="intended-audience">Intended audience</a>

The comments and source code in the library should provide enough detail so that people familiar with functional programming and proof assistants can learn enough about Agda and its libraries to put them to use when creating, formalizing, and verifying mathematical theorems and proofs.

While there are no strict prerequisites, we expect anyone with an interest in this work will have been motivated by prior exposure to universal algebra, as presented in, say, [Bergman (2012)][] or [McKenzie, McNulty, Taylor (2018)], or category theory, as presented in, say, [Riehl (2017)][].

Some prior exposure to [type theory][] and Agda would be helpful, but even without this background one might still be able to get something useful out of this by referring to one or more of the resources mentioned in the references section below to fill in gaps as needed.


### <a id="attributions">Attributions</a>

#### <a id="the-agda-algebras-development-team">The agda-algebras development team</a>

The [agda-algebras](https://github.com/ualib/agda-algebras) library is developed and maintained by the *Agda Algebras Development Team* led by [William DeMeo][] with major contributions by senior advisor [Jacques Carette][] (McMaster University).

#### <a id="Acknowledgements">Acknowledgements</a>

We thank [Andreas Abel][], [Andrej Bauer][], [Clifford Bergman][], [Venanzio Capretta][], [Martín Escardó][], [Ralph Freese][], [Hyeyoung Shin][], and [Siva Somayyajula][] for helpful discussions, corrections, advice, inspiration and encouragement.

Most of the mathematical results formalized in the [agda-algebras](https://github.com/ualib/agda-algebras) are well known. Regarding the source code in the [agda-algebras](https://github.com/ualib/agda-algebras) library, this is mainly due to the contributors listed above.


#### <a id="references">References</a>

The following Agda documentation and tutorials helped inform and improve the [agda-algebras](https://github.com/ualib/agda-algebras) library, especially the first one in the list.

* Escardo, [Introduction to Univalent Foundations of Mathematics with Agda][]
* Wadler, [Programming Language Foundations in Agda][]
* Bove and Dybjer, [Dependent Types at Work][]
* Gunther, Gadea, Pagano, [Formalization of Universal Algebra in Agda][]
* Norell and Chapman, [Dependently Typed Programming in Agda][]

Finally, the official [Agda Wiki][], [Agda User's Manual][], [Agda Language Reference][], and the (open source) [Agda Standard Library][] source code are also quite useful.


#### <a id="citing-the-agda-algebras-library">Citing the agda-algebras library</a>

If you find the [agda-algebras](https://github.com/ualib/agda-algebras) library useful, please cite it using the following BibTeX entry:

```bibtex
@misc{ualib_v2.0.1,
  author       = {De{M}eo, William and Carette, Jacques},
  title        = {The {A}gda {U}niversal {A}lgebra {L}ibrary (agda-algebras)},
  year         = 2021,
  note         = {Documentation available at https://ualib.org},
  version      = {2.0.1},
  doi          = {10.5281/zenodo.5765793},
  howpublished = {Git{H}ub.com},
  note         = {Ver.~2.0.1; source code:
                  \href{https://zenodo.org/record/5765793/files/ualib/agda-algebras-v.2.0.1.zip?download=1}
                  {agda-algebras-v.2.0.1.zip}, {G}it{H}ub repo:
                  \href{https://github.com/ualib/agda-algebras}{github.com/ualib/agda-algebras}}
}
```

#### <a id="citing-the-formalization-of-birkhoffs-theorem">Citing the formalization of Birkhoff's Theorem </a>

To cite the [formalization of Birkhoff's HSP Theorem](https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem), please use the following BibTeX entry:

```bibtex
@article{DeMeo:2021,
 author        = {De{M}eo, William and Carette, Jacques},
 title         = {A {M}achine-checked {P}roof of {B}irkhoff's {V}ariety {T}heorem
                  in {M}artin-{L}\"of {T}ype {T}heory},
 journal       = {CoRR},
 volume        = {abs/2101.10166},
 year          = {2021},
 eprint        = {2101.2101.10166},
 archivePrefix = {arXiv},
 primaryClass  = {cs.LO},
 url           = {https://arxiv.org/abs/2101.10166},
 note          = {Source code:
                  \href{https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda}
                  {https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda}}
}
```




#### <a id="contributions-welcomed">Contributions welcomed</a>

Readers and users are encouraged to suggest improvements to the Agda [agda-algebras](https://github.com/ualib/agda-algebras) library and/or its documentation by submitting a [new issue](https://github.com/ualib/agda-algebras/issues/new/choose) or [merge request](https://github.com/ualib/agda-algebras/compare) to [github.com/ualib/agda-algebras/](https://github.com/ualib/agda-algebras).


------------------------------------------------

<span style="float:left;">[↑ agda-algebras](agda-algebras.html)</span>
<span style="float:right;">[Base →](Base.html)</span>


[Agda Universal Algebra Library]: https://ualib.github.io/agda-algebras
[Agda UniversalAlgebra]: https://ualib.github.io/agda-algebras
[git repository of the Agda UALib]: https://github.com/ualib/agda-algebras
[git repository of the agda-algebras library]: https://github.com/ualib/agda-algebras
[UniversalAlgebra]: https://ualib.github.io
[UniversalAlgebra repository]: https://github.com/ualib/agda-universal-algebra
[new issue]: https://github.com/ualib/agda-algebras/issues/new/choose
[agda-algebras]: https://github.com/ualib/agda-algebras
[agda-algebras-everything]: agda-algebras-everything.html
[merge request]: https://github.com/ualib/agda-algebras/compare
[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

[Preface]: https://ualib.org/Preface.html
[Base]: https://ualib.org/Base.html
[Base.Adjunction]: https://ualib.org/Base.Adjunction.html
[Base.Adjunction.Closure]: https://ualib.org/Base.Adjunction.Closure.html
[Base.Adjunction.Galois]: https://ualib.org/Base.Adjunction.Galois.html
[Base.Adjunction.Residuation]: https://ualib.org/Base.Adjunction.Residuation.html
[Base.Algebras]: https://ualib.org/Base.Algebras.html
[Base.Algebras.Basic]: https://ualib.org/Base.Algebras.Basic.html
[Base.Algebras.Congruences]: https://ualib.org/Base.Algebras.Congruences.html
[Base.Algebras.Products]: https://ualib.org/Base.Algebras.Products.html
[Base.Categories]: https://ualib.org/Base.Categories.html
[Base.Categories.Functors]: https://ualib.org/Base.Categories.Functors.html
[Base.Complexity]: https://ualib.org/Base.Complexity.html
[Base.Complexity.Basic]: https://ualib.org/Base.Complexity.Basic.html
[Base.Complexity.CSP]: https://ualib.org/Base.Complexity.CSP.html
[Base.Equality]: https://ualib.org/Base.Equality.html
[Base.Equality.Extensionality]: https://ualib.org/Base.Equality.Extensionality.html
[Base.Equality.Truncation]: https://ualib.org/Base.Equality.Truncation.html
[Base.Equality.Welldefined]: https://ualib.org/Base.Equality.Welldefined.html
[Base.Homomorphisms]: https://ualib.org/Base.Homomorphisms.html
[Base.Homomorphisms.Basic]: https://ualib.org/Base.Homomorphisms.Basic.html
[Base.Homomorphisms.Factor]: https://ualib.org/Base.Homomorphisms.Factor.html
[Base.Homomorphisms.HomomorphicImages]: https://ualib.org/Base.Homomorphisms.HomomorphicImages.html
[Base.Homomorphisms.Isomorphisms]: https://ualib.org/Base.Homomorphisms.Isomorphisms.html
[Base.Homomorphisms.Kernels]: https://ualib.org/Base.Homomorphisms.Kernels.html
[Base.Homomorphisms.Noether]: https://ualib.org/Base.Homomorphisms.Noether.html
[Base.Homomorphisms.Products]: https://ualib.org/Base.Homomorphisms.Products.html
[Base.Homomorphisms.Properties]: https://ualib.org/Base.Homomorphisms.Properties.html
[Base.Overture]: https://ualib.org/Base.Overture.html
[Base.Overture.Injective]: https://ualib.org/Base.Overture.Injective.html
[Base.Overture.Inverses]: https://ualib.org/Base.Overture.Inverses.html
[Base.Overture.Preliminaries]: https://ualib.org/Base.Overture.Preliminaries.html
[Base.Overture.Surjective]: https://ualib.org/Base.Overture.Surjective.html
[Base.Overture.Transformers]: https://ualib.org/Base.Overture.Transformers.html
[Base.Relations]: https://ualib.org/Base.Relations.html
[Base.Relations.Continuous]: https://ualib.org/Base.Relations.Continuous.html
[Base.Relations.Discrete]: https://ualib.org/Base.Relations.Discrete.html
[Base.Relations.Properties]: https://ualib.org/Base.Relations.Properties.html
[Base.Relations.Quotients]: https://ualib.org/Base.Relations.Quotients.html
[Base.Structures]: https://ualib.org/Base.Structures.html
[Base.Structures.Basic]: https://ualib.org/Base.Structures.Basic.html
[Base.Structures.Congruences]: https://ualib.org/Base.Structures.Congruences.html
[Base.Structures.EquationalLogic]: https://ualib.org/Base.Structures.EquationalLogic.html
[Base.Structures.Graphs]: https://ualib.org/Base.Structures.Graphs.html
[Base.Structures.Graphs0]: https://ualib.org/Base.Structures.Graphs0.html
[Base.Structures.Homs]: https://ualib.org/Base.Structures.Homs.html
[Base.Structures.Isos]: https://ualib.org/Base.Structures.Isos.html
[Base.Structures.Products]: https://ualib.org/Base.Structures.Products.html
[Base.Structures.Sigma]: https://ualib.org/Base.Structures.Sigma.html
[Base.Structures.Sigma.Basic]: https://ualib.org/Base.Structures.Sigma.Basic.html
[Base.Structures.Sigma.Congruences]: https://ualib.org/Base.Structures.Sigma.Congruences.html
[Base.Structures.Sigma.Homs]: https://ualib.org/Base.Structures.Sigma.Homs.html
[Base.Structures.Sigma.Isos]: https://ualib.org/Base.Structures.Sigma.Isos.html
[Base.Structures.Sigma.Products]: https://ualib.org/Base.Structures.Sigma.Products.html
[Base.Structures.Substructures]: https://ualib.org/Base.Structures.Substructures.html
[Base.Structures.Terms]: https://ualib.org/Base.Structures.Terms.html
[Base.Subalgebras]: https://ualib.org/Base.Subalgebras.html
[Base.Subalgebras.Properties]: https://ualib.org/Base.Subalgebras.Properties.html
[Base.Subalgebras.Subalgebras]: https://ualib.org/Base.Subalgebras.Subalgebras.html
[Base.Subalgebras.Subuniverses]: https://ualib.org/Base.Subalgebras.Subuniverses.html
[Base.Terms]: https://ualib.org/Base.Terms.html
[Base.Terms.Basic]: https://ualib.org/Base.Terms.Basic.html
[Base.Terms.Operations]: https://ualib.org/Base.Terms.Operations.html
[Base.Terms.Properties]: https://ualib.org/Base.Terms.Properties.html
[Base.Varieties]: https://ualib.org/Base.Varieties.html
[Base.Varieties.Closure]: https://ualib.org/Base.Varieties.Closure.html
[Base.Varieties.EquationalLogic]: https://ualib.org/Base.Varieties.EquationalLogic.html
[Base.Varieties.FreeAlgebras]: https://ualib.org/Base.Varieties.FreeAlgebras.html
[Base.Varieties.Invariants]: https://ualib.org/Base.Varieties.Invariants.html
[Base.Varieties.Preservation]: https://ualib.org/Base.Varieties.Preservation.html
[Base.Varieties.Properties]: https://ualib.org/Base.Varieties.Properties.html
[Cubical]: https://ualib.org/Cubical.html
[Cubical.Overture]: https://ualib.org/Cubical.Overture.html
[Cubical.Overture.Preliminaries]: https://ualib.org/Cubical.Overture.Preliminaries.html
[Demos.HSP]: https://ualib.org/Demos.HSP.html
[Demos.HSP-markdown]: https://ualib.org/Demos.HSP-markdown.html
[Examples.Categories.Functors]: https://ualib.org/Examples.Categories.Functors.html
[Examples.Structures.Basic]: https://ualib.org/Examples.Structures.Basic.html
[Examples.Structures.Signatures]: https://ualib.org/Examples.Structures.Signatures.html
[Exercises.Complexity.FiniteCSP]: https://ualib.org/Exercises.Complexity.FiniteCSP.html
[Setoid]: https://ualib.org/Setoid.html
[Setoid.Algebras]: https://ualib.org/Setoid.Algebras.html
[Setoid.Algebras.Basic]: https://ualib.org/Setoid.Algebras.Basic.html
[Setoid.Algebras.Congruences]: https://ualib.org/Setoid.Algebras.Congruences.html
[Setoid.Algebras.Products]: https://ualib.org/Setoid.Algebras.Products.html
[Setoid.Homomorphisms]: https://ualib.org/Setoid.Homomorphisms.html
[Setoid.Homomorphisms.Basic]: https://ualib.org/Setoid.Homomorphisms.Basic.html
[Setoid.Homomorphisms.Factor]: https://ualib.org/Setoid.Homomorphisms.Factor.html
[Setoid.Homomorphisms.HomomorphicImages]: https://ualib.org/Setoid.Homomorphisms.HomomorphicImages.html
[Setoid.Homomorphisms.Isomorphisms]: https://ualib.org/Setoid.Homomorphisms.Isomorphisms.html
[Setoid.Homomorphisms.Kernels]: https://ualib.org/Setoid.Homomorphisms.Kernels.html
[Setoid.Homomorphisms.Noether]: https://ualib.org/Setoid.Homomorphisms.Noether.html
[Setoid.Homomorphisms.Products]: https://ualib.org/Setoid.Homomorphisms.Products.html
[Setoid.Homomorphisms.Properties]: https://ualib.org/Setoid.Homomorphisms.Properties.html
[Setoid.Overture]: https://ualib.org/Setoid.Overture.html
[Setoid.Overture.Bijective]: https://ualib.org/Setoid.Overture.Bijective.html
[Setoid.Overture.Injective]: https://ualib.org/Setoid.Overture.Injective.html
[Setoid.Overture.Inverses]: https://ualib.org/Setoid.Overture.Inverses.html
[Setoid.Overture.Preliminaries]: https://ualib.org/Setoid.Overture.Preliminaries.html
[Setoid.Overture.Surjective]: https://ualib.org/Setoid.Overture.Surjective.html
[Setoid.Relations]: https://ualib.org/Setoid.Relations.html
[Setoid.Relations.Discrete]: https://ualib.org/Setoid.Relations.Discrete.html
[Setoid.Relations.Quotients]: https://ualib.org/Setoid.Relations.Quotients.html
[Setoid.Subalgebras]: https://ualib.org/Setoid.Subalgebras.html
[Setoid.Subalgebras.Properties]: https://ualib.org/Setoid.Subalgebras.Properties.html
[Setoid.Subalgebras.Subalgebras]: https://ualib.org/Setoid.Subalgebras.Subalgebras.html
[Setoid.Subalgebras.Subuniverses]: https://ualib.org/Setoid.Subalgebras.Subuniverses.html
[Setoid.Terms]: https://ualib.org/Setoid.Terms.html
[Setoid.Terms.Basic]: https://ualib.org/Setoid.Terms.Basic.html
[Setoid.Terms.Operations]: https://ualib.org/Setoid.Terms.Operations.html
[Setoid.Terms.Properties]: https://ualib.org/Setoid.Terms.Properties.html
[Setoid.Varieties]: https://ualib.org/Setoid.Varieties.html
[Setoid.Varieties.Closure]: https://ualib.org/Setoid.Varieties.Closure.html
[Setoid.Varieties.EquationalLogic]: https://ualib.org/Setoid.Varieties.EquationalLogic.html
[Setoid.Varieties.FreeAlgebras]: https://ualib.org/Setoid.Varieties.FreeAlgebras.html
[Setoid.Varieties.HSP]: https://ualib.org/Setoid.Varieties.HSP.html
[Setoid.Varieties.Preservation]: https://ualib.org/Setoid.Varieties.Preservation.html
[Setoid.Varieties.Properties]: https://ualib.org/Setoid.Varieties.Properties.html
[Setoid.Varieties.SoundAndComplete]: https://ualib.org/Setoid.Varieties.SoundAndComplete.html




[Base.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base.lagda
[Base/Adjunction.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Adjunction.lagda
[Base/Adjunction/Closure.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Adjunction/Closure.lagda
[Base/Adjunction/Galois.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Adjunction/Galois.lagda
[Base/Adjunction/Residuation.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Adjunction/Residuation.lagda
[Base/Algebras.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Algebras.lagda
[Base/Algebras/Basic.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Algebras/Basic.lagda
[Base/Algebras/Congruences.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Algebras/Congruences.lagda
[Base/Algebras/Products.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Algebras/Products.lagda
[Base/Categories.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Categories.lagda
[Base/Categories/Functors.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Categories/Functors.lagda
[Base/Complexity.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Complexity.lagda
[Base/Complexity/Basic.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Complexity/Basic.lagda
[Base/Complexity/CSP.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Complexity/CSP.lagda
[Base/Equality.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Equality.lagda
[Base/Equality/Extensionality.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Equality/Extensionality.lagda
[Base/Equality/Truncation.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Equality/Truncation.lagda
[Base/Equality/Welldefined.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Equality/Welldefined.lagda
[Base/Homomorphisms.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Homomorphisms.lagda
[Base/Homomorphisms/Basic.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Homomorphisms/Basic.lagda
[Base/Homomorphisms/Factor.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Homomorphisms/Factor.lagda
[Base/Homomorphisms/HomomorphicImages.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Homomorphisms/HomomorphicImages.lagda
[Base/Homomorphisms/Isomorphisms.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Homomorphisms/Isomorphisms.lagda
[Base/Homomorphisms/Kernels.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Homomorphisms/Kernels.lagda
[Base/Homomorphisms/Noether.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Homomorphisms/Noether.lagda
[Base/Homomorphisms/Products.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Homomorphisms/Products.lagda
[Base/Homomorphisms/Properties.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Homomorphisms/Properties.lagda
[Base/Overture.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Overture.lagda
[Base/Overture/Injective.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Overture/Injective.lagda
[Base/Overture/Inverses.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Overture/Inverses.lagda
[Base/Overture/Preliminaries.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Overture/Preliminaries.lagda
[Base/Overture/Surjective.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Overture/Surjective.lagda
[Base/Overture/Transformers.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Overture/Transformers.lagda
[Base/Relations.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Relations.lagda
[Base/Relations/Continuous.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Relations/Continuous.lagda
[Base/Relations/Discrete.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Relations/Discrete.lagda
[Base/Relations/Properties.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Relations/Properties.lagda
[Base/Relations/Quotients.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Relations/Quotients.lagda
[Base/Structures.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures.lagda
[Base/Structures/Basic.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Basic.lagda
[Base/Structures/Congruences.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Congruences.lagda
[Base/Structures/EquationalLogic.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/EquationalLogic.lagda
[Base/Structures/Graphs.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Graphs.lagda
[Base/Structures/Graphs0.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Graphs0.lagda
[Base/Structures/Homs.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Homs.lagda
[Base/Structures/Isos.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Isos.lagda
[Base/Structures/Products.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Products.lagda
[Base/Structures/Sigma.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Sigma.lagda
[Base/Structures/Sigma/Basic.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Sigma/Basic.lagda
[Base/Structures/Sigma/Congruences.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Sigma/Congruences.lagda
[Base/Structures/Sigma/Homs.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Sigma/Homs.lagda
[Base/Structures/Sigma/Isos.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Sigma/Isos.lagda
[Base/Structures/Sigma/Products.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Sigma/Products.lagda
[Base/Structures/Substructures.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Substructures.lagda
[Base/Structures/Terms.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Structures/Terms.lagda
[Base/Subalgebras.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Subalgebras.lagda
[Base/Subalgebras/Properties.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Subalgebras/Properties.lagda
[Base/Subalgebras/Subalgebras.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Subalgebras/Subalgebras.lagda
[Base/Subalgebras/Subuniverses.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Subalgebras/Subuniverses.lagda
[Base/Terms.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Terms.lagda
[Base/Terms/Basic.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Terms/Basic.lagda
[Base/Terms/Operations.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Terms/Operations.lagda
[Base/Terms/Properties.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Terms/Properties.lagda
[Base/Varieties.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Varieties.lagda
[Base/Varieties/Closure.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Varieties/Closure.lagda
[Base/Varieties/EquationalLogic.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Varieties/EquationalLogic.lagda
[Base/Varieties/FreeAlgebras.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Varieties/FreeAlgebras.lagda
[Base/Varieties/Invariants.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Varieties/Invariants.lagda
[Base/Varieties/Preservation.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Varieties/Preservation.lagda
[Base/Varieties/Properties.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Base/Varieties/Properties.lagda
[Cubical.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Cubical.lagda
[Cubical/Overture.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Cubical/Overture.lagda
[Cubical/Overture/Preliminaries.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Cubical/Overture/Preliminaries.lagda
[Demos/HSP.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda
[Demos/HSP-markdown.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP/markdown.lagda
[Examples/Categories/Functors.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Examples/Categories/Functors.lagda
[Examples/Structures/Basic.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Examples/Structures/Basic.lagda
[Examples/Structures/Signatures.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Examples/Structures/Signatures.lagda
[Exercises/Complexity/FiniteCSP.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Exercises/Complexity/FiniteCSP.lagda
[Preface.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Preface.lagda
[Setoid.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid.lagda
[Setoid/Algebras.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Algebras.lagda
[Setoid/Algebras/Basic.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Algebras/Basic.lagda
[Setoid/Algebras/Congruences.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Algebras/Congruences.lagda
[Setoid/Algebras/Products.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Algebras/Products.lagda
[Setoid/Homomorphisms.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Homomorphisms.lagda
[Setoid/Homomorphisms/Basic.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Homomorphisms/Basic.lagda
[Setoid/Homomorphisms/Factor.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Homomorphisms/Factor.lagda
[Setoid/Homomorphisms/HomomorphicImages.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Homomorphisms/HomomorphicImages.lagda
[Setoid/Homomorphisms/Isomorphisms.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Homomorphisms/Isomorphisms.lagda
[Setoid/Homomorphisms/Kernels.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Homomorphisms/Kernels.lagda
[Setoid/Homomorphisms/Noether.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Homomorphisms/Noether.lagda
[Setoid/Homomorphisms/Products.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Homomorphisms/Products.lagda
[Setoid/Homomorphisms/Properties.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Homomorphisms/Properties.lagda
[Setoid/Overture.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Overture.lagda
[Setoid/Overture/Bijective.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Overture/Bijective.lagda
[Setoid/Overture/Injective.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Overture/Injective.lagda
[Setoid/Overture/Inverses.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Overture/Inverses.lagda
[Setoid/Overture/Preliminaries.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Overture/Preliminaries.lagda
[Setoid/Overture/Surjective.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Overture/Surjective.lagda
[Setoid/Relations.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Relations.lagda
[Setoid/Relations/Discrete.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Relations/Discrete.lagda
[Setoid/Relations/Quotients.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Relations/Quotients.lagda
[Setoid/Subalgebras.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Subalgebras.lagda
[Setoid/Subalgebras/Properties.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Subalgebras/Properties.lagda
[Setoid/Subalgebras/Subalgebras.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Subalgebras/Subalgebras.lagda
[Setoid/Subalgebras/Subuniverses.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Subalgebras/Subuniverses.lagda
[Setoid/Terms.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Terms.lagda
[Setoid/Terms/Basic.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Terms/Basic.lagda
[Setoid/Terms/Operations.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Terms/Operations.lagda
[Setoid/Terms/Properties.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Terms/Properties.lagda
[Setoid/Varieties.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Varieties.lagda
[Setoid/Varieties/Closure.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Varieties/Closure.lagda
[Setoid/Varieties/EquationalLogic.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Varieties/EquationalLogic.lagda
[Setoid/Varieties/FreeAlgebras.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Varieties/FreeAlgebras.lagda
[Setoid/Varieties/HSP.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Varieties/HSP.lagda
[Setoid/Varieties/Preservation.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Varieties/Preservation.lagda
[Setoid/Varieties/Properties.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Varieties/Properties.lagda
[Setoid/Varieties/SoundAndComplete.lagda]: https://github.com/ualib/agda-algebras/blob/master/src/Setoid/Varieties/SoundAndComplete.lagda




[absolute value]: https://en.wikipedia.org/wiki/Absolute_value
[Agda]: https://wiki.portal.chalmers.se/agda/pmwiki.php
[Agda Language Reference]: https://agda.readthedocs.io/en/v2.6.1.3/language
[Agda Standard Library]: https://agda.github.io/agda-stdlib/
[Agda Tools]: https://agda.readthedocs.io/en/v2.6.1.3/tools/
[Agda Tutorial]: https://people.inf.elte.hu/pgj/agda/tutorial/Index.html
[Agda User's Manual]: https://agda.readthedocs.io/en/v2.6.1.3/
[Agda Wiki]: https://wiki.portal.chalmers.se/agda/pmwiki.php
[agda2-mode]: https://agda.readthedocs.io/en/v2.6.1.3/tools/emacs-mode.html
[Algebraic Effects and Handlers]: https://www.cs.uoregon.edu/research/summerschool/summer18/topics.php#Bauer
[Andreas Abel]: http://www.cse.chalmers.se/~abela/
[Andrej Bauer]: http://www.andrej.com/index.html
[Axioms and Computation]: https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#

[Bill Lampe]: https://math.hawaii.edu/wordpress/people/william/

[Category Theory in Context]: http://www.math.jhu.edu/~eriehl/context.pdf
[categorytheory.gitlab.io]: https://categorytheory.gitlab.io
[Charles University in Prague]: https://cuni.cz/UKEN-1.html
[Clifford Bergman]: https://orion.math.iastate.edu/cbergman/
[Cliff Bergman]: https://orion.math.iastate.edu/cbergman/
[Bergman (2012)]: https://www.amazon.com/gp/product/1439851298/ref=as_li_tl?ie=UTF8&camp=1789&creative=9325&creativeASIN=1439851298&linkCode=as2&tag=typefunc-20&linkId=440725c9b1e60817d071c1167dff95fa
[Coercions using Type Classes]: https://leanprover.github.io/theorem_proving_in_lean/type_classes.html#coercions-using-type-classes
[Computer Aided Formal Reasoning]: http://www.cs.nott.ac.uk/~psztxa/g53cfr/
[constructive mathematics]: https://ncatlab.org/nlab/show/constructive+mathematics
[Coq]: http://coq.inria.fr

[Department of Algebra]: https://www.mff.cuni.cz/en/ka
[dependent types]: https://en.wikipedia.org/wiki/Dependent_type
[Dependent Types at Work]: http://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf
[Dependently Typed Programming in Agda]: http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf

[Emacs]: https://www.gnu.org/software/emacs/
[emacs]: https://www.gnu.org/software/emacs/
[Equality Section]: https://leanprover.github.io/logic_and_proof/first_order_logic.html?highlight=equality#equality
[Escardó]: https://www.cs.bham.ac.uk/~mhe
[Escardó's notes]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes

[Formalization of Universal Algebra in Agda]: http://www.sciencedirect.com/science/article/pii/S1571066118300768
[function extensionality]: https://ncatlab.org/nlab/show/function+extensionality


[Homotopy Type Theory]: https://homotopytypetheory.org/
[HoTT]: https://homotopytypetheory.org/
[HoTT book]: https://homotopytypetheory.org/book/
[HoTT-UF-in-Agda]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
[HSP Theorem]: https://en.wikipedia.org/wiki/Variety_(universal_algebra)#Birkhoff's_theorem
[Hyeyoung Shin]: https://hyeyoungshin.github.io/
[Implicit Arguments]: https://leanprover.github.io/theorem_proving_in_lean/dependent_type_theory.html#implicit-arguments
[Inductive Types in Lean]: https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html
[inductive types]: https://en.wikipedia.org/wiki/Intuitionistic_type_theory#Inductive_types
[Introduction to Univalent Foundations of Mathematics with Agda]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html
[Univalent Foundations of Mathematics with Agda]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html

[Jacques Carette]: http://www.cas.mcmaster.ca/~carette/
[JB Nation]: http://www.math.hawaii.edu/~jb/
[Jeremy Avigad]: http://www.andrew.cmu.edu/user/avigad/

[Lean]: https://leanprover.github.io/
[Lean 2]: https://github.com/leanprover/lean2
[Lean 4]: https://github.com/leanprover/lean4
[lean extension]: https://github.com/leanprover/vscode-lean
[Lean github repository]:  https://github.com/leanprover/lean/
[Lean Reference Manual]: https://leanprover.github.io/reference/
[Lean Standard Library]: https://github.com/leanprover/lean
[Lean Tutorial]: https://leanprover.github.io/tutorial/
[Lean Universal Algebra Library]: https://github.com/UniversalAlgebra/lean-ualib/
[Libor Barto]: http://www.karlin.mff.cuni.cz/~barto/
[Logic and Proof]: https://leanprover.github.io/logic_and_proof/

[markdown]: https://daringfireball.net/projects/markdown/
[Martin Escardo]: https://www.cs.bham.ac.uk/~mhe
[Martín Escardó]: https://www.cs.bham.ac.uk/~mhe
[Martín Escardó's notes]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes
[Martin Escardo's installation hints]: https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes/blob/master/INSTALL.md
[Martín Hötzel Escardó]: https://www.cs.bham.ac.uk/~mhe
[Martin Hötzel Escardo]: https://www.cs.bham.ac.uk/~mhe
[Martin-Löf dependent type theory]: https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory
[Martin-Löf type theory]: https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory
[Mathlib]: https://github.com/leanprover-community/mathlib/
[Mathlib documentation]: https://leanprover-community.github.io/papers/mathlib-paper.pdf
[McKenzie, McNulty, Taylor (2018)]: https://www.amazon.com/gp/product/1470442957/ref=as_li_qf_asin_il_tl?ie=UTF8&tag=typefunc-20&creative=9325&linkCode=as2&creativeASIN=1470442957&linkId=b3109d9c28ceb872df7d4b84b1cc4f29
[MHE]: https://www.cs.bham.ac.uk/~mhe
[Midlands Graduate School in the Foundations of Computing Science]: http://events.cs.bham.ac.uk/mgs2019/
[Miklós Maróti]: http://www.math.u-szeged.hu/~mmaroti/
[MLTT]: https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory
[More on Implicit Arguments]: https://leanprover.github.io/theorem_proving_in_lean/interacting_with_lean.html?highlight=implicit#more-on-implicit-arguments

[ncatlab]: https://ncatlab.org
[ncatlab.org]: https://ncatlab.org
[nlab]: https://ncatlab.org
[NuPRL]: http://www.nuprl.org/

[OPLSS 2018]: https://www.cs.uoregon.edu/research/summerschool/summer18/topics.php#Bauer

[Peter Mayr]: http://math.colorado.edu/~mayr/
[Programming Languages Foundations in Agda]: https://plfa.github.io/
[Programming Language Foundations in Agda]: https://plfa.github.io/
[proof assistant]: https://en.wikipedia.org/wiki/Proof_assistant
[proof tactics]: https://en.wikipedia.org/wiki/Tactic_(proof_assistant)

[A Machine-checked proof of Birkhoff's Variety Theorem in Martin-Löf Type Theory](https://arxiv.org/abs/2101.10166)

[Ralph Freese]: https://math.hawaii.edu/~ralph/
[reading material]: https://arxiv.org/abs/1807.05923
[Riehl (2017)]: http://www.math.jhu.edu/~eriehl/context/

[Siva Somayyajula]: http://www.cs.cmu.edu/~ssomayya/

[the main Agda website]: https://wiki.portal.chalmers.se/agda/pmwiki.php
[Theorem Proving in Lean]: https://leanprover.github.io/theorem_proving_in_lean/index.html
[this gist]: https://gist.github.com/andrejbauer/3cc438ab38646516e5e9278fdb22022c
[TPL]: https://leanprover.github.io/theorem_proving_in_lean/
[type theory]: https://en.wikipedia.org/wiki/Type_theory
[Type Theory and Formal Proof]: https://www.cambridge.org/vi/academic/subjects/computer-science/programming-languages-and-applied-logic/type-theory-and-formal-proof-introduction
[Type Topology]: https://github.com/martinescardo/TypeTopology

[Course on Univalent Foundations]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes
[Univalent Foundations with Agda]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes
[Univalent Foundations and Homotopy Type Theory]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes

[Venanzio Capretta]: https://www.duplavis.com/venanzio/
[vscode]: https://code.visualstudio.com/

[William DeMeo]: https://williamdemeo.gitlab.io/
[williamdemeo@gmail.com]: mailto:williamdemeo@gmail.com
[williamdemeo at gmail dot com]: mailto:williamdemeo@gmail.com
[williamdemeo.org]: https://williamdemeo.gitlab.io/
[williamdemeo@gitlab]: https://gitlab.com/williamdemeo
[williamdemeo@github]: https://github.com/williamdemeo


