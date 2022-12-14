.. FILE      : Setoid/Subalgebras/Subalgebras.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 17 Jul 2021
.. UPDATED   : 18 Jun 2022

.. highlight:: agda
.. role:: code

.. subalgebras-of-setoid-algebras:

Subalgebras of setoid algebras
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Subalgebras.Subalgebras`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature)

  module Setoid.Subalgebras.Subalgebras {π : Signature π π₯} where

  -- imports from Agda and the Agda Standard Library ------------------------------------------
  open import Agda.Primitive   using () renaming ( Set to Type )
  open import Data.Product     using ( _,_ ; Ξ£-syntax )
                               renaming ( _Γ_ to _β§_ ; projβ to snd )
  open import Level            using ( Level ; _β_ )
  open import Relation.Binary  using ( REL )
  open import Relation.Unary   using ( Pred ; _β_ )

  -- Imports from the Agda Universal Algebra Library ------------------------------------------
  open import Overture          using ( β£_β£ ; β₯_β₯ )
  open import Setoid.Functions  using ( IsInjective )

  open import Setoid.Algebras       {π = π} using ( Algebra ; ov )
  open import Setoid.Homomorphisms  {π = π} using
   ( hom ; mon ; monβintohom ; kerquo ; FirstHomTheorem )

  private variable Ξ± Οα΅ Ξ² Οα΅ β : Level

  _β₯_  -- (alias for supalgebra (aka overalgebra))
   _IsSupalgebraOf_ : Algebra Ξ± Οα΅ β Algebra Ξ² Οα΅ β Type _
  π¨ IsSupalgebraOf π© = Ξ£[ h β hom π© π¨ ] IsInjective β£ h β£

  _β€_  -- (alias for subalgebra relation))
   _IsSubalgebraOf_ : Algebra Ξ± Οα΅ β Algebra Ξ² Οα΅ β Type (π β π₯ β Ξ± β Οα΅ β Ξ² β Οα΅)
  π¨ IsSubalgebraOf π© = Ξ£[ h β hom π¨ π© ] IsInjective β£ h β£

  -- Syntactic sugar for sup/sub-algebra relations.
  π¨ β₯ π© = π¨ IsSupalgebraOf π©
  π¨ β€ π© = π¨ IsSubalgebraOf π©

  monββ€ : {π¨ : Algebra Ξ± Οα΅}{π© : Algebra Ξ² Οα΅} β mon π¨ π© β π¨ β€ π©
  monββ€ {π¨ = π¨}{π©} x = monβintohom π¨ π© x

  record SubalgebraOf : Type (ov (Ξ± β Ξ² β Οα΅ β Οα΅)) where
   field
    algebra : Algebra Ξ± Οα΅
    subalgebra : Algebra Ξ² Οα΅
    issubalgebra : subalgebra β€ algebra

  Subalgebra : Algebra Ξ± Οα΅ β {Ξ² Οα΅ : Level} β Type _
  Subalgebra π¨ {Ξ²}{Οα΅} = Ξ£[ π© β (Algebra Ξ² Οα΅) ] π© β€ π¨

  {- usage note: for π¨ : Algebra Ξ± Οα΅, an inhabitant of `Subalgebra π¨` is a pair
     `(π© , p) : Subalgebra π¨`  providing
     - `π© : Algebra Ξ² Οα΅` and
     - `p : π© β€ π¨`, a proof that π© is a subalgebra of π΄. -}

  IsSubalgebraREL : {Ξ± Οα΅ Ξ² Οα΅ : Level} β REL (Algebra Ξ± Οα΅)(Algebra Ξ² Οα΅) β β Type _
  IsSubalgebraREL {Ξ±}{Οα΅}{Ξ²}{Οα΅} R = β {π¨ : Algebra Ξ± Οα΅}{π© : Algebra Ξ² Οα΅} β π¨ β€ π©

  record SubalgebraREL(R : REL (Algebra Ξ² Οα΅)(Algebra Ξ± Οα΅) β) : Type (ov (Ξ± β Ξ² β Οα΅ β β))
   where
   field isSubalgebraREL : IsSubalgebraREL R

From now on we will use ``π© β€ π¨`` to express the assertion that ``π©`` is a subalgebra of ``π¨``.

.. _subalgebras-of-classes:

Subalgebras of classes
^^^^^^^^^^^^^^^^^^^^^^

Suppose ``π¦ : Pred (Algebra Ξ± π) Ξ³`` denotes a class of ``π``-algebras and
``π© : Algebra Ξ² Οα΅`` denotes an arbitrary ``π``-algebra. Then we might wish
to consider the assertion that ``π©`` is a subalgebra of an algebra in the
class ``π¦``. The next type we define allows us to express this assertion
as ``π© IsSubalgebraOfClass π¦``.

::

  _β€c_
   _IsSubalgebraOfClass_ : Algebra Ξ² Οα΅ β Pred (Algebra Ξ± Οα΅) β β Type _
  π© IsSubalgebraOfClass π¦ = Ξ£[ π¨ β Algebra _ _ ] ((π¨ β π¦) β§ (π© β€ π¨))

  π© β€c π¦ = π© IsSubalgebraOfClass π¦  -- (alias)

  record SubalgebraOfClass : Type (ov (Ξ± β Ξ² β Οα΅ β Οα΅ β β)) where
   field
    class : Pred (Algebra Ξ± Οα΅) β
    subalgebra : Algebra Ξ² Οα΅
    issubalgebraofclass : subalgebra β€c class

  record SubalgebraOfClass' : Type (ov (Ξ± β Ξ² β Οα΅ β Οα΅ β β)) where
   field
    class : Pred (Algebra Ξ± Οα΅) β
    classalgebra : Algebra Ξ± Οα΅
    isclassalgebra : classalgebra β class
    subalgebra : Algebra Ξ² Οα΅
    issubalgebra : subalgebra β€ classalgebra

  -- The collection of subalgebras of algebras in class π¦.
  SubalgebrasOfClass : Pred (Algebra Ξ± Οα΅) β β {Ξ² Οα΅ : Level} β Type _
  SubalgebrasOfClass π¦ {Ξ²}{Οα΅} = Ξ£[ π© β Algebra Ξ² Οα΅ ] π© β€c π¦

.. _consequences-of-the-first-homomorphism-theorem:

Consequences of the First Homomorphism Theorem
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

As an example use-case of the ``IsSubalgebraOf`` type defined above, we prove the
following easy but useful corollary of the First Homomorphism Theorem (proved in
the `Setoid.Homomorphisms.Noether`_ module): If ``π¨`` and ``π©`` are ``π``-algebras
and ``h : hom π¨ π©`` a homomorphism from ``π¨`` to ``π©``, then the quotient
``π¨ β± ker h`` is (isomorphic to) a subalgebra of ``π©``.

::

  FirstHomCorollary :  {π¨ : Algebra Ξ± Οα΅}{π© : Algebra Ξ² Οα΅}
                       (hh : hom π¨ π©) β (kerquo hh) IsSubalgebraOf π©

  FirstHomCorollary hh = β£ FirstHomTheorem hh β£ , snd β₯ FirstHomTheorem hh β₯

