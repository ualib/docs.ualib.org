.. FILE      : Examples/Categories/Functors.lagda.rst
.. DATE      : 31 Aug 2021
.. UPDATED   : 04 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette and William DeMeo

.. _examples-of-functors:

Examples of Functors
~~~~~~~~~~~~~~~~~~~~

This is the `Examples.Categories.Functors`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Examples.Categories.Functors where

  open import Agda.Primitive using ( lsuc ) renaming ( Set to Type ; lzero to ℓ₀ )
  open import Data.Nat       using ( ℕ ; zero ; suc ; _>_ )
  open import Data.Sum.Base  using ( _⊎_ ) renaming ( inj₁ to inl ;  inj₂ to inr )
  open import Data.Product   using ( Σ-syntax ; _,_ ; _×_ )
  open import Level
  open import Data.Unit      using () renaming ( tt to 𝟎 )
  open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; _≢_ )

  open import Base.Categories.Functors using ( List ; list ; _⟦_⟧ ; _[_] ; μ_ ; Option )

  open μ_
  open list


.. _lists:

Lists
^^^^^

The empty list.

::

  L₀ : List ℕ
  L₀ = inn (inl (Level.lift 𝟎))

  l₀ : list ℕ
  l₀ = []


The one-element list ``(3)``.

::

  L₁ : List ℕ
  L₁ = inn (inr (3 , L₀))

  l₁ : list ℕ
  l₁ = 3 ∷ l₀

The three-element list ``(1, 2, 3)``.

::

  L₃ : List ℕ
  L₃ = inn (inr (1 , (inn (inr (2 , L₀)))))

  l₃ : list ℕ
  l₃ = 1 ∷ (2 ∷ l₁)


Some examples of lists using the option type.

::

  open Option

  L₀≡none : ∀ {n} → (L₀ [ n ]) ≡ none
  L₀≡none = refl

  l₀≡none : ∀ {n} → (l₀ ⟦ n ⟧) ≡ none
  l₀≡none = refl


  L₁[0]≡some3 : L₁ [ 0 ] ≡ some 3
  L₁[0]≡some3 = refl

  l₁⟦0⟧≡some3 : l₁ ⟦ 0 ⟧ ≡ some 3
  l₁⟦0⟧≡some3 = refl


  L₁[n>0]≡none : ∀ n → n > 0 → L₁ [ n ] ≡ none
  L₁[n>0]≡none (suc n) _ = refl

  l₁⟦n>0⟧≡none : ∀ n → n > 0 → l₁ ⟦ n ⟧ ≡ none
  l₁⟦n>0⟧≡none (suc n) _ = refl


  L₃[0]≡some1 : L₃ [ 0 ] ≡ some 1
  L₃[0]≡some1 = refl

  l₃⟦0⟧≡some1 : l₃ ⟦ 0 ⟧ ≡ some 1
  l₃⟦0⟧≡some1 = refl


  L₃[0]≢some2 : L₃ [ 0 ] ≢ some 2
  L₃[0]≢some2 = λ ()

  l₃[0]≢some2 : l₃ ⟦ 0 ⟧ ≢ some 2
  l₃[0]≢some2 = λ ()

--------------

.. include:: hyperlink_references.rst

