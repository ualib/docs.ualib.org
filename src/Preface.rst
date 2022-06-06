.. FILE      : Preface.rst
.. AUTHOR    : William DeMeo
.. DATE      : 14 Jan 2021
.. UPDATED   : 04 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette, William DeMeo


Preface
=======

To support formalization in type theory of research level mathematics in
universal algebra and related fields, we present the `Agda Universal
Algebra Library <https://github.com/ualib/agda-algebras>`__ (or
`agda-algebras <https://github.com/ualib/agda-algebras>`__ for short), a
library for the
`Agda <https://wiki.portal.chalmers.se/agda/pmwiki.php>`__ proof
assistant which contains definitions, theorems and proofs from the
foundations of universal algebra. In particular, the library formalizes
the First (Noether) Isomorphism Theorem and the `Birkhoff HSP
Theorem <https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem>`__
asserting that every variety is an equational class.

Vision and goals
-----------------

The idea for the
`agda-algebras <https://github.com/ualib/agda-algebras>`__ project
originated with the observation that, on the one hand a number of basic
and important constructs in universal algebra can be defined
recursively, and theorems about them proved inductively, while on the
other hand the *types* (of type theory—in particular, `dependent
types <https://en.wikipedia.org/wiki/Dependent_type>`__ and `inductive
types <https://en.wikipedia.org/wiki/Intuitionistic_type_theory#Inductive_types>`__)
make possible elegant formal representations of recursively defined
objects, and constructive (*computable*) proofs of their properties.
These observations suggest that there is much to gain from implementing
universal algebra in a language that facilitates working with dependent
and inductive types.

.. _primary-goals:

Primary goals
~~~~~~~~~~~~~

The first goal of
`agda-algebras <https://github.com/ualib/agda-algebras>`__ is to
demonstrate that it is possible to express the foundations of universal
algebra in type theory and to formalize (and formally verify) the
foundations in the Agda programming language. We will formalize a
substantial portion of the edifice on which our own mathematical
research depends, and demonstrate that our research can also be
expressed in type theory and formally implemented in such a way that we
and other working mathematicians can understand and verify the results.
The resulting library will also serve to educate our peers, and
encourage and help them to formally verify their own mathematics
research.

Our field is deep and wide and codifying all of its foundations may seem
like a daunting task and a possibly risky investment of time and energy.
However, we believe our subject is well served by a new, modern,
`constructive <https://ncatlab.org/nlab/show/constructive+mathematics>`__
presentation of its foundations. Our new presentation expresses the
foundations of universal algebra in the language of type theory, and
uses the Agda proof assistant to codify and formally verify everything.

.. _secondary-goals:

Secondary goals
~~~~~~~~~~~~~~~

We wish to emphasize that our ultimate objective is not merely to
translate existing results into a more modern and formal language.
Indeed, one important goal is to develop a system that is useful for
conducting research in mathematics, and that is how we intend to use our
library once we have achieved our immediate objective of implementing
the basic foundational core of universal algebra in Agda.

To this end, our long-term objectives include

-  domain specific types to express the idioms of universal algebra,
-  automated proof search for universal algebra, and
-  formalization of theorems discovered in our own (informal)
   mathematics research,
-  documentation of the resulting Agda library so it is usable by
   others.

For our own mathematics research, we believe a proof assistant like
Agda, equipped with a specialized library for universal algebra is an
extremely useful research tool. Thus, a secondary goal is to demonstrate
(to ourselves and colleagues) the utility of such technologies for
discovering new mathematics.

.. _logical-foundations:

Logical foundations
-------------------

The `Agda Universal Algebra
Library <https://ualib.github.io/agda-algebras>`__ is based on a minimal
version of `Martin-Löf dependent type
theory <https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory>`__
(MLTT) as implemented in Agda. More details on this type theory can be
read at `ncatlab entry on Martin-Löf dependent type
theory <https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory>`__.

.. _intended-audience:

Intended audience
-----------------

The comments and source code in the library should provide enough detail
so that people familiar with functional programming and proof assistants
can learn enough about Agda and its libraries to put them to use when
creating, formalizing, and verifying mathematical theorems and proofs.

While there are no strict prerequisites, we expect anyone with an
interest in this work will have been motivated by prior exposure to
universal algebra, as presented in, say, `Bergman
(2012) <https://www.amazon.com/gp/product/1439851298/ref=as_li_tl?ie=UTF8&camp=1789&creative=9325&creativeASIN=1439851298&linkCode=as2&tag=typefunc-20&linkId=440725c9b1e60817d071c1167dff95fa>`__
or `McKenzie, McNulty, Taylor
(2018) <https://www.amazon.com/gp/product/1470442957/ref=as_li_qf_asin_il_tl?ie=UTF8&tag=typefunc-20&creative=9325&linkCode=as2&creativeASIN=1470442957&linkId=b3109d9c28ceb872df7d4b84b1cc4f29>`__,
or category theory, as presented in, say, `Riehl
(2017) <http://www.math.jhu.edu/~eriehl/context/>`__.

Some prior exposure to `type
theory <https://en.wikipedia.org/wiki/Type_theory>`__ and Agda would be
helpful, but even without this background one might still be able to get
something useful out of this by referring to one or more of the
resources mentioned in the references section below to fill in gaps as
needed.

.. _attributions:

Attributions
------------

.. _the-agda-algebras-development-team:

The agda-algebras development team
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The `agda-algebras <https://github.com/ualib/agda-algebras>`__ library
is developed and maintained by the *Agda Algebras Development Team* led
by `William DeMeo <https://williamdemeo.gitlab.io/>`__ with major
contributions by senior advisor `Jacques
Carette <http://www.cas.mcmaster.ca/~carette/>`__ (McMaster University).

.. _acknowledgements:

Acknowledgements
~~~~~~~~~~~~~~~~

We thank `Andreas Abel <http://www.cse.chalmers.se/~abela/>`__, `Andrej
Bauer <http://www.andrej.com/index.html>`__, `Clifford
Bergman <https://orion.math.iastate.edu/cbergman/>`__, `Venanzio
Capretta <https://www.duplavis.com/venanzio/>`__, `Martín
Escardó <https://www.cs.bham.ac.uk/~mhe>`__, `Ralph
Freese <https://math.hawaii.edu/~ralph/>`__, `Hyeyoung
Shin <https://hyeyoungshin.github.io/>`__, and `Siva
Somayyajula <http://www.cs.cmu.edu/~ssomayya/>`__ for helpful
discussions, corrections, advice, inspiration and encouragement.

Most of the mathematical results formalized in the
`agda-algebras <https://github.com/ualib/agda-algebras>`__ are well
known. Regarding the source code in the
`agda-algebras <https://github.com/ualib/agda-algebras>`__ library, this
is mainly due to the contributors listed above.

.. _references:

References
~~~~~~~~~~

The following Agda documentation and tutorials helped inform and improve
the `agda-algebras <https://github.com/ualib/agda-algebras>`__ library,
especially the first one in the list.

-  Escardo, `Introduction to Univalent Foundations of Mathematics with
   Agda <https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html>`__
-  Wadler, `Programming Language Foundations in
   Agda <https://plfa.github.io/>`__
-  Bove and Dybjer, `Dependent Types at
   Work <http://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf>`__
-  Gunther, Gadea, Pagano, `Formalization of Universal Algebra in
   Agda <http://www.sciencedirect.com/science/article/pii/S1571066118300768>`__
-  Norell and Chapman, `Dependently Typed Programming in
   Agda <http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf>`__

Finally, the official `Agda
Wiki <https://wiki.portal.chalmers.se/agda/pmwiki.php>`__, `Agda User’s
Manual <https://agda.readthedocs.io/en/v2.6.1.3/>`__, `Agda Language
Reference <https://agda.readthedocs.io/en/v2.6.1.3/language>`__, and the
(open source) `Agda Standard
Library <https://agda.github.io/agda-stdlib/>`__ source code are also
quite useful.

.. _citing-the-agda-algebras-library:

Citing the agda-algebras library
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If you find the
`agda-algebras <https://github.com/ualib/agda-algebras>`__ library
useful, please cite it using the following BibTeX entry:

.. code:: bibtex

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

.. _citing-the-formalization-of-birkhoffs-theorem:

Citing the formalization of Birkhoff’s Theorem 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To cite the `formalization of Birkhoff’s HSP
Theorem <https://ualib.org/Setoid.Varieties.HSP.html#proof-of-the-hsp-theorem>`__,
please use the following BibTeX entry for our paper,
`A Machine-checked proof of Birkhoff’s Variety Theorem in Martin-Löf
Type Theory <https://arxiv.org/abs/2101.10166>`__


.. code:: bibtex

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

.. _contributions-welcomed:

Contributions welcomed
----------------------

Readers and users are encouraged to suggest improvements to the Agda
`agda-algebras <https://github.com/ualib/agda-algebras>`__ library
and/or its documentation by submitting a `new
issue <https://github.com/ualib/agda-algebras/issues/new/choose>`__ or
`merge request <https://github.com/ualib/agda-algebras/compare>`__ to
`github.com/ualib/agda-algebras/ <https://github.com/ualib/agda-algebras>`__.

--------------
