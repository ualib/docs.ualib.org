.. FILE      : Base/Adjunction/Residuation.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 30 Aug 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-adjunction-residuation:

Residuation
~~~~~~~~~~~

This is the `Base.Adjunction.Residuation`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Adjunction.Residuation where

  -- Imports from Agda and the Agda Standard Library --------------------------------------
  open import Agda.Primitive   using ( _⊔_ ;  Level ; lsuc) renaming ( Set to Type )
  open import Function.Base    using ( _on_ ; _∘_ )
  open import Relation.Binary  using ( Poset ; _Preserves_⟶_ )

  -- Imports from the Agda Universal Algebra Library --------------------------------------
  open import Base.Relations   using ( PointWise )

  private variable α ιᵃ ρᵃ β ιᵇ ρᵇ : Level

  module _ (A : Poset α ιᵃ ρᵃ)(B : Poset β ιᵇ ρᵇ) where
   open Poset
   private
    _≤A_ = _≤_ A
    _≤B_ = _≤_ B

   record Residuation : Type (lsuc (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ))  where
    field
     f      : Carrier A → Carrier B
     g      : Carrier B → Carrier A
     fhom   : f Preserves _≤A_ ⟶ _≤B_
     ghom   : g Preserves _≤B_ ⟶ _≤A_
     gf≥id  : ∀ a → a ≤A g (f a)
     fg≤id  : ∀ b → f (g b) ≤B b


.. _base-adjunction-basic-properties-of-residual-pairs:

Basic properties of residual pairs
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  open Residuation
  open Poset

  module _ {A : Poset α ιᵃ ρᵃ} {B : Poset β ιᵇ ρᵇ} (R : Residuation A B) where
   private
    _≤A_ = _≤_ A
    _≤B_ = _≤_ B

    𝑓 = (R .f)
    𝑔 = (R .g)

    -- Pointwise equality of unary functions wrt equality on the given poset carrier
    -- 1. pointwise equality on B → A
    _≈̇A_ = PointWise{α = β}{A = Carrier B} (_≈_ A)
    -- 2. pointwise equality on A → B
    _≈̇B_ = PointWise{α = α}{A = Carrier A} (_≈_ B)

In a ring ``R``, if ``x y : R`` and if ``x y x = x``, then ``y`` is called a *weak
inverse* for ``x``. (A ring is called *von Neumann regular* if every element has a
unique weak inverse.)

::

   -- 𝑔 is a weak inverse for 𝑓
   weak-inverse : (𝑓 ∘ 𝑔 ∘ 𝑓) ≈̇B 𝑓
   weak-inverse a = antisym B lt gt
    where
    lt : 𝑓 (𝑔 (𝑓 a)) ≤B 𝑓 a
    lt = fg≤id R (𝑓 a)
    gt : 𝑓 a ≤B 𝑓 (𝑔 (𝑓 a))
    gt = fhom R (gf≥id R a)

   -- 𝑓 is a weak inverse of 𝑔
   weak-inverse' : (𝑔 ∘ 𝑓 ∘ 𝑔) ≈̇A 𝑔
   weak-inverse' b = antisym A lt gt
    where
    lt : 𝑔 (𝑓 (𝑔 b)) ≤A 𝑔 b
    lt = ghom R (fg≤id R b)
    gt : 𝑔 b ≤A 𝑔 (𝑓 (𝑔 b))
    gt = gf≥id R (𝑔 b)

