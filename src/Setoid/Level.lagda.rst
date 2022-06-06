.. FILE      : Setoid/Level.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 06 Jun 2022
.. UPDATED   : 06 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette, William DeMeo

.. highlight:: agda
.. role:: code

.. _setoid-universe-levels:

Setoid universe levels
-----------------------

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Setoid.Preliminaries where

  -- Imports from Agda and the Agda Standard Library -----------------------
  open import Agda.Primitive    using ( _⊔_ ) renaming ( Set to Type )
  open import Function          using ( id )
  open import Function.Bundles  using () renaming ( Func to _⟶_ )
  open import Relation.Binary   using ( Setoid )
  open import Level

  import Function.Base as Fun
  private variable
   α ρᵃ β ρᵇ γ ρᶜ : Level


  open _⟶_ renaming ( f to _⟨$⟩_ )

  module _ {𝑨 : Setoid α ρᵃ} where
   open Setoid using (_≈_)
   open Setoid 𝑨 using ( sym ; trans ) renaming (Carrier to A ; _≈_ to _≈ₐ_ ; refl to reflₐ)

   𝑙𝑖𝑓𝑡 : ∀ ℓ → Setoid (α ⊔ ℓ) ρᵃ
   𝑙𝑖𝑓𝑡 ℓ = record { Carrier = Lift ℓ A
                 ; _≈_ = λ x y → (lower x) ≈ₐ (lower y)
                 ; isEquivalence = record { refl = reflₐ ; sym = sym ; trans = trans }
                 }

   lift∼lower : (a : Lift β A) → (_≈_ (𝑙𝑖𝑓𝑡 β)) (lift (lower a)) a
   lift∼lower a = reflₐ

   lower∼lift : ∀ a → (lower {α}{β}) (lift a) ≈ₐ a
   lower∼lift _ = reflₐ

   liftFunc : {ℓ : Level} → 𝑨 ⟶ 𝑙𝑖𝑓𝑡 ℓ
   liftFunc = record { f = lift ; cong = id }

   module _ {𝑩 : Setoid β ρᵇ} where
    open Setoid 𝑩 using ( sym ) renaming (Carrier to B; _≈_ to _≈₂_)

    -- This is sometimes known as `cong` (see e.g. `Function.Equality` in the agda-stdlib)
    -- preserves≈ : (A → B) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
    -- preserves≈ f = ∀ {x y} → x ≈ₐ y → (f x) ≈₂ (f y)



