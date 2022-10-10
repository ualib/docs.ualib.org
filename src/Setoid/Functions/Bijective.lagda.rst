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

Let ``𝑨 = (A, ≈₀)`` and ``𝑩 = (B, ≈₁)`` be setoids.
A setoid function from ``𝑨`` to ``𝑩`` is called **bijective** provided it is both
:ref:`injective <injective-setoid-functions>`_ and
:ref:`surjective <surjective-setoid-functions>`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Relation.Binary using ( Setoid )

  module Setoid.Functions.Bijective {α ρᵃ β ρᵇ }{𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

  -- Imports from Agda and the Agda Standard Library --------------------------
  open import Agda.Primitive    using ( _⊔_ ; Level )  renaming ( Set to Type )
  open import Data.Product      using ( _,_ ; _×_ )
  open import Function.Bundles  using ()               renaming ( Func to _⟶_ )

  -- Imports from agda-algebras -----------------------------------------------
  open import Setoid.Functions.Inverses    using ( Image_∋_ ; Inv )
  open import Setoid.Functions.Surjective  using ( IsSurjective )
  open import Setoid.Functions.Injective   using ( IsInjective )

  open Image_∋_

  open Setoid 𝑨  using ()               renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid 𝑩  using ( sym ; trans )  renaming (Carrier to B; _≈_ to _≈₂_)

  IsBijective : (𝑨 ⟶ 𝑩) → Type (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ)
  IsBijective f = IsInjective f × IsSurjective f

  BijInv : (f : 𝑨 ⟶ 𝑩) → IsBijective f → 𝑩 ⟶ 𝑨
  BijInv f (fM , fE) = record { f = finv ; cong = c }
   where
   finv : B → A
   finv b = Inv f fE

   handler :  ∀ {b₀ b₁}(i₀ : Image f ∋ b₀)(i₁ : Image f ∋ b₁)
    →         b₀ ≈₂ b₁ → (Inv f i₀) ≈₁ (Inv f i₁)

   handler (eq a x) (eq a₁ x₁) b₀≈b₁ = fM (trans (sym x) (trans b₀≈b₁ x₁))

   c : ∀ {b₀ b₁} → b₀ ≈₂ b₁ → (finv b₀) ≈₁ (finv b₁)
   c b₀≈b₁ = handler fE fE b₀≈b₁

