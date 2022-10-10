.. FILE      : Setoid/Relations/Discrete.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 16 Sep 2021
.. UPDATED   : 09 Jun 2022

.. highlight:: agda
.. role:: code

.. _discrete-setoid-relations:

Discrete setoid relations
~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Relations.Discrete`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Setoid.Relations.Discrete where

  -- Imports from Agda and the Agda Standard Library ----------------------------------------------
  open import Agda.Primitive        using () renaming ( Set to Type )
  open import Data.Product          using ( _,_ ; _×_ )
  open import Function              using ( _∘_ ) renaming ( Func to _⟶_ )
  open import Level                 using ( Level ;  _⊔_ ; Lift )
  open import Relation.Binary       using ( IsEquivalence ; Setoid )
  open import Relation.Binary.Core  using ( _⇒_ ; _=[_]⇒_ )
                                    renaming ( REL to BinREL ; Rel to BinRel )
  open import Relation.Binary.Definitions
                                    using ( Reflexive ; Transitive )
  open import Relation.Unary        using ( _∈_; Pred )
  open import Relation.Binary.PropositionalEquality
                                    using ( _≡_ )

  -- Imports from agda-algebras -------------------------------------------------------------------
  open import Overture using ( Π-syntax )

  private variable α β ρᵃ ρᵇ ℓ 𝓥 : Level

Here is a function that is useful for defining poitwise equality of functions wrt a given equality.

::

  open _⟶_ renaming ( f to _⟨$⟩_ )
  module _ {𝐴 : Setoid α ρᵃ}{𝐵 : Setoid β ρᵇ} where
   open Setoid 𝐴  using () renaming ( Carrier to A ; _≈_ to _≈₁_ )
   open Setoid 𝐵  using () renaming ( Carrier to B ; _≈_ to _≈₂_ )

   function-equality : BinRel (𝐴 ⟶ 𝐵) (α ⊔ ρᵇ)
   function-equality f g = ∀ x → f ⟨$⟩ x ≈₂ g ⟨$⟩ x

Here is useful notation for asserting that the image of a function (the first
argument) is contained in a predicate, the second argument (a "subset" of the
codomain).

::

   Im_⊆_ : (𝐴 ⟶ 𝐵) → Pred B ℓ → Type (α ⊔ ℓ)
   Im f ⊆ S = ∀ x → f ⟨$⟩ x ∈ S

.. _kernels-on-setoids:

Kernels on setoids
^^^^^^^^^^^^^^^^^^

Given setoids 𝐴 and 𝐵 (with carriers A and B, resp), the *kernel* of a function
``f : 𝐴 ⟶ 𝐵`` is defined informally by ``{(x , y) ∈ A × A : f ⟨$⟩ x ≈₂ f ⟨$⟩ y}``.

::

   fker : (𝐴 ⟶ 𝐵) → BinRel A ρᵇ
   fker g x y = g ⟨$⟩ x ≈₂ g ⟨$⟩ y

   fkerPred : (𝐴 ⟶ 𝐵) → Pred (A × A) ρᵇ
   fkerPred g (x , y) = g ⟨$⟩ x ≈₂ g ⟨$⟩ y

   open IsEquivalence

   fkerlift : (𝐴 ⟶ 𝐵) → (ℓ : Level) → BinRel A (ℓ ⊔ ρᵇ)
   fkerlift g ℓ x y = Lift ℓ (g ⟨$⟩ x ≈₂ g ⟨$⟩ y)

   -- The *identity relation* (equivalently, the kernel of a 1-to-1 function)
   0rel : {ℓ : Level} → BinRel A (ρᵃ ⊔ ℓ)
   0rel {ℓ} = λ x y → Lift ℓ (x ≈₁ y)
