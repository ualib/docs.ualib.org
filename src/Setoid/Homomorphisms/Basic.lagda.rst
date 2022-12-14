.. FILE      : Setoid/Homomorphisms/Basic.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 13 Sep 2021
.. UPDATED   : 09 Jun 2022

.. highlight:: agda
.. role:: code

.. _homomorphisms-of-algebras-over-setoids:

Homomorphisms of setoid algebras
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Homomorphisms.Basic`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (๐ ; ๐ฅ ; Signature )

  module Setoid.Homomorphisms.Basic {๐ : Signature ๐ ๐ฅ} where

  -- Imports from Agda and the Agda Standard Library ------------------------------
  open import Agda.Primitive    using () renaming ( Set to Type )
  open import Data.Product      using ( _,_ ; ฮฃ ; ฮฃ-syntax )
  open import Function.Bundles  using () renaming ( Func to _โถ_ )
  open import Level             using ( Level ; _โ_ )
  open import Relation.Binary   using ( Setoid )

  -- Imports from the Agda Universal Algebra Library ---------------------------
  open import Overture          using ( โฃ_โฃ ; โฅ_โฅ )
  open import Setoid.Functions  using ( IsInjective ; IsSurjective )

  open import Setoid.Algebras {๐ = ๐} using ( Algebra ; _ฬ_ )

  private variable ฮฑ ฮฒ ฯแต ฯแต : Level

  module _ (๐จ : Algebra ฮฑ ฯแต)(๐ฉ : Algebra ฮฒ ฯแต) where
   open Algebra ๐จ  using() renaming (Domain to A )
   open Algebra ๐ฉ  using() renaming (Domain to B )
   open Setoid A   using() renaming ( _โ_ to _โโ_ )
   open Setoid B   using() renaming ( _โ_ to _โโ_ )

   open _โถ_ {a = ฮฑ}{ฯแต}{ฮฒ}{ฯแต}{From = A}{To = B} renaming (f to _โจ$โฉ_ )

   compatible-map-op : (A โถ B) โ โฃ ๐ โฃ โ Type (๐ฅ โ ฮฑ โ ฯแต)
   compatible-map-op h f =  โ {a}
    โ                       h โจ$โฉ (f ฬ ๐จ) a โโ (f ฬ ๐ฉ) ฮป x โ h โจ$โฉ (a x)

   compatible-map : (A โถ B) โ Type (๐ โ ๐ฅ โ ฮฑ โ ฯแต)
   compatible-map h = โ {f} โ compatible-map-op h f

   -- The property of being a homomorphism.
   record IsHom (h : A โถ B) : Type (๐ โ ๐ฅ โ ฮฑ โ ฯแต โ ฯแต) where
    field compatible : compatible-map h

   hom : Type (๐ โ ๐ฅ โ ฮฑ โ ฯแต โ ฮฒ โ ฯแต)
   hom = ฮฃ (A โถ B) IsHom


.. _monomorphisms-and-epimorphisms:

Monomorphisms and epimorphisms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   record IsMon (h : A โถ B) : Type (๐ โ ๐ฅ โ ฮฑ โ ฯแต โ ฮฒ โ ฯแต) where
    field
     isHom : IsHom h
     isInjective : IsInjective h

    HomReduct : hom
    HomReduct = h , isHom

   mon : Type (๐ โ ๐ฅ โ ฮฑ โ ฯแต โ ฮฒ โ ฯแต)
   mon = ฮฃ (A โถ B) IsMon

   monโhom : mon โ hom
   monโhom h = IsMon.HomReduct โฅ h โฅ

   record IsEpi (h : A โถ B) : Type (๐ โ ๐ฅ โ ฮฑ โ ฯแต โ ฮฒ โ ฯแต) where
    field
     isHom : IsHom h
     isSurjective : IsSurjective h

    HomReduct : hom
    HomReduct = h , isHom

   epi : Type (๐ โ ๐ฅ โ ฮฑ โ ฯแต โ ฮฒ โ ฯแต)
   epi = ฮฃ (A โถ B) IsEpi

   epiโhom : epi โ hom
   epiโhom h = IsEpi.HomReduct โฅ h โฅ

::

  module _ (๐จ : Algebra ฮฑ ฯแต)(๐ฉ : Algebra ฮฒ ฯแต) where
   open IsEpi
   open IsMon

   monโintohom : mon ๐จ ๐ฉ โ ฮฃ[ h โ hom ๐จ ๐ฉ ] IsInjective โฃ h โฃ
   monโintohom (hh , hhM) = (hh , isHom hhM) , isInjective hhM

   epiโontohom : epi ๐จ ๐ฉ โ ฮฃ[ h โ hom ๐จ ๐ฉ ] IsSurjective โฃ h โฃ
   epiโontohom (hh , hhE) = (hh , isHom hhE) , isSurjective hhE
