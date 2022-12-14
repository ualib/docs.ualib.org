.. FILE      : Setoid/Functions/Bijective.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 13 Sep 2021
.. UPDATE    : 18 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-functions-bijective-setoid-functions:

Bijective setoid functions
~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Functions.Bijective`_ module of the agda-algebras_ library.

Let ``๐จ = (A, โโ)`` and ``๐ฉ = (B, โโ)`` be setoids.
A setoid function from ``๐จ`` to ``๐ฉ`` is called **bijective** provided it is both
:ref:`injective <injective-setoid-functions>`_ and
:ref:`surjective <surjective-setoid-functions>`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Relation.Binary using ( Setoid )

  module Setoid.Functions.Bijective {ฮฑ ฯแต ฮฒ ฯแต }{๐จ : Setoid ฮฑ ฯแต}{๐ฉ : Setoid ฮฒ ฯแต} where

  -- Imports from Agda and the Agda Standard Library --------------------------
  open import Agda.Primitive    using ( _โ_ ; Level )  renaming ( Set to Type )
  open import Data.Product      using ( _,_ ; _ร_ )
  open import Function.Bundles  using ()               renaming ( Func to _โถ_ )

  -- Imports from agda-algebras -----------------------------------------------
  open import Setoid.Functions.Inverses    using ( Image_โ_ ; Inv )
  open import Setoid.Functions.Surjective  using ( IsSurjective )
  open import Setoid.Functions.Injective   using ( IsInjective )

  open Image_โ_

  open Setoid ๐จ  using ()               renaming (Carrier to A; _โ_ to _โโ_)
  open Setoid ๐ฉ  using ( sym ; trans )  renaming (Carrier to B; _โ_ to _โโ_)

  IsBijective : (๐จ โถ ๐ฉ) โ Type (ฮฑ โ ฮฒ โ ฯแต โ ฯแต)
  IsBijective f = IsInjective f ร IsSurjective f

  BijInv : (f : ๐จ โถ ๐ฉ) โ IsBijective f โ ๐ฉ โถ ๐จ
  BijInv f (fM , fE) = record { f = finv ; cong = c }
   where
   finv : B โ A
   finv b = Inv f fE

   handler :  โ {bโ bโ}(iโ : Image f โ bโ)(iโ : Image f โ bโ)
    โ         bโ โโ bโ โ (Inv f iโ) โโ (Inv f iโ)

   handler (eq a x) (eq aโ xโ) bโโbโ = fM (trans (sym x) (trans bโโbโ xโ))

   c : โ {bโ bโ} โ bโ โโ bโ โ (finv bโ) โโ (finv bโ)
   c bโโbโ = handler fE fE bโโbโ

