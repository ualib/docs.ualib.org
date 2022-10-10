.. FILE      : Setoid/Functions/Basic.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 13 Sep 2021
.. UPDATE    : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-functions-setoid-functions:

Setoid functions
~~~~~~~~~~~~~~~~

This is the `Setoid.Functions.Basic`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Setoid.Functions.Basic where

  -- Imports from Agda and the Agda Standard Library -----------------------
  open import Agda.Primitive   using ()  renaming ( Set to Type )
  open import Function         using ( id )   renaming ( Func to _⟶_ ; _∘_ to _□_ )
  open import Level            using ( Level ; Lift ; _⊔_ )
  open import Relation.Binary  using ( Setoid )

  private variable α ρᵃ β ρᵇ γ ρᶜ : Level

  𝑖𝑑 : {A : Setoid α ρᵃ} → A ⟶ A
  𝑖𝑑 {A} = record { f = id ; cong = id }

  open _⟶_ renaming ( f to _⟨$⟩_ )

  _∘_ :  {A : Setoid α ρᵃ}{B : Setoid β ρᵇ}{C : Setoid γ ρᶜ}
   →     B ⟶ C → A ⟶ B → A ⟶ C
  f ∘ g = record { f = (_⟨$⟩_ f) □ (_⟨$⟩_ g); cong = (cong f) □ (cong g) }

  module _ {𝑨 : Setoid α ρᵃ} where
   open Lift ; open Level ; open Setoid using (_≈_)
   open Setoid 𝑨 using ( sym ; trans ) renaming (Carrier to A ; _≈_ to _≈ₐ_ ; refl to reflₐ)

   𝑙𝑖𝑓𝑡 : ∀ ℓ → Setoid (α ⊔ ℓ) ρᵃ
   𝑙𝑖𝑓𝑡 ℓ = record  { Carrier = Lift ℓ A
                  ; _≈_ = λ x y → (lower x) ≈ₐ (lower y)
                  ; isEquivalence = record { refl = reflₐ ; sym = sym ; trans = trans }
                  }

   lift∼lower : (a : Lift β A) → (_≈_ (𝑙𝑖𝑓𝑡 β)) (lift (lower a)) a
   lift∼lower a = reflₐ

   lower∼lift : ∀ a → (lower {α}{β}) (lift a) ≈ₐ a
   lower∼lift _ = reflₐ

   liftFunc : {ℓ : Level} → 𝑨 ⟶ 𝑙𝑖𝑓𝑡 ℓ
   liftFunc = record { f = lift ; cong = id }

