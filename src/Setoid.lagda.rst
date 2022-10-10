.. FILE      : Setoid.lagda.rst
.. AUTHOR    : William DeMeo <williamdemeo@gmail.com>
.. DATE      : 12 Dec 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-types-for-general-algebra:

Setoid Types for General Algebra
================================

This is the Setoid_ module where we collect all submodules of the
`Agda Universal Algebra Library`_ based on *setoids* (cf. the Base_
module which collects analogous submodules based on "bare" types).

A *setoid* is a pair consisting of a type and an equivalence relation on that
type. Setoids are useful for representing a set with an explicit, "local" notion
of equivalence, instead of relying on an implicit, "global" one as is more common
in set theory. In reality, informal mathematical practice relies on equivalence
relations quite pervasively, taking great care to define only functions that
preserve equivalences, while eliding the details. To be properly formal, such
details must be made explicit. While there are many different workable approaches,
the one that requires no additional meta-theory is based on setoids, which is why
we adopt it here. While in some settings setoids are found by others to be
burdensome, we have not found them to be so for universal algebra.

The agda-algebras_ library was first developed without setoids, relying on
propositional equality instead, along with some new domain-specific types for
equivalence classes, quotients, etc. This required postulating function
extensionality, [1]_ which is known to be independent from MLTT_
:cite:p:`MHE,MHE:2019`; this was unsatisfactory as our aim is to show
that the theorems hold directly in MLTT_ without extra axioms. The present
work makes no appeal to functional extensionality or classical axioms like Choice
or Excluded Middle. [2]_

.. toctree::
   :maxdepth: 2

   Setoid/Levels
   Setoid/Relations
   Setoid/Functions
   Setoid/Algebras
   Setoid/Homomorphisms
   Setoid/Terms
   Setoid/Subalgebras
   Setoid/Varieties
   Setoid/Complexity

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Setoid where

  open import Setoid.Levels
  open import Setoid.Relations
  open import Setoid.Functions
  open import Setoid.Algebras
  open import Setoid.Homomorphisms
  open import Setoid.Terms
  open import Setoid.Subalgebras
  open import Setoid.Varieties
  open import Setoid.Complexity

-----------------------------------------

.. rubric:: Footnotes

.. [1]
   the axiom asserting that two point-wise equal functions are equal

.. [2]
   All submodules of the module in the library are also fully
   constructive in this sense.
