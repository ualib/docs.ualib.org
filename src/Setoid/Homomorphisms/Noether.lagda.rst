.. FILE      : Setoid/Homomorphisms/Noether.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 15 Sep 2021
.. UPDATED   : 18 Jun 2022

.. highlight:: agda
.. role:: code

.. _homomorphism-theorems-for-setoid-algebras:

Homomorphism Theorems for Setoid Algebras
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Homomorphisms.Noether`_] module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature)

  module Setoid.Homomorphisms.Noether {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library ---------------------------
  open import Data.Product     using (Ξ£-syntax ; _,_ )  renaming ( _Γ_ to _β§_ ; projβ to fst)
  open import Function         using ( id )             renaming ( Func to _βΆ_ )
  open import Level            using ( Level )
  open import Relation.Binary  using ( Setoid )

  open import Relation.Binary.PropositionalEquality as β‘ using ( _β‘_ )

  import Relation.Binary.Reasoning.Setoid as SetoidReasoning

  -- Imports from agda-algebras ------------------------------------------------
  open import Overture          using ( β£_β£ ; β₯_β₯ )
  open import Setoid.Functions  using ( IsInjective )

  open import Setoid.Algebras {π = π}               using ( Algebra ; _Μ_)
  open import Setoid.Homomorphisms.Basic {π = π}    using ( hom ; IsHom )
  open import Setoid.Homomorphisms.Kernels {π = π}  using ( kerquo ; Οker )

  private variable Ξ± Οα΅ Ξ² Οα΅ Ξ³ ΟαΆ ΞΉ : Level


The First Homomorphism Theorem for setoid algebras
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  open _βΆ_ using ( cong ) renaming ( f to _β¨$β©_ )
  open Algebra using ( Domain )

  module _ {π¨ : Algebra Ξ± Οα΅}{π© : Algebra Ξ² Οα΅}(hh : hom π¨ π©) where
   open Algebra π© using ( Interp ) renaming ( Domain to B )
   open Setoid B using ( _β_ ; refl ; sym ; trans ) -- renaming ( _β_ to _ββ_ )
   open Algebra (kerquo hh) using () renaming ( Domain to A/hKer )

   open IsHom
   private
    hfunc = β£ hh β£
    h = _β¨$β©_ hfunc

   FirstHomTheorem :  Ξ£[ Ο β hom (kerquo hh) π©  ]
                      ( β a β h a β β£ Ο β£ β¨$β© (β£ Οker hh β£ β¨$β© a) )
                       β§ IsInjective β£ Ο β£

   FirstHomTheorem = (Ο , Οhom) , (Ξ» _ β refl) , Οmon
    where
    Ο : A/hKer βΆ B
    _β¨$β©_ Ο = h
    cong Ο = id

    Οhom : IsHom (kerquo hh) π© Ο
    compatible Οhom = trans (compatible β₯ hh β₯) (cong Interp (β‘.refl , (Ξ» _ β refl)))

    Οmon : IsInjective Ο
    Οmon = id


Now we prove that the homomorphism whose existence is guaranteed by
``FirstHomTheorem`` is unique.

::

   FirstHomUnique :  (f g : hom (kerquo hh) π©)
    β                ( β a β  h a β β£ f β£ β¨$β© (β£ Οker hh β£ β¨$β© a) )
    β                ( β a β  h a β β£ g β£ β¨$β© (β£ Οker hh β£ β¨$β© a) )
    β                β [a]  β  β£ f β£ β¨$β© [a] β β£ g β£ β¨$β© [a]

   FirstHomUnique fh gh hfk hgk a = trans (sym (hfk a)) (hgk a)

