.. FILE      : Base/Structures/Terms.lagda.rst
.. DATE      : 26 Jul 2021
.. UPDATED   : 04 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette and William DeMeo

.. _interpretation-of-terms-in-general-structures:

Interpretation of Terms in General Structures
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Base.Structures.Terms`_ module of the `Agda Universal Algebra Library`_.

When we interpret a term in a structure we call the resulting function a *term
operation*. Given a term ``p`` and a structure ``𝑨``, we denote by ``𝑨 ⟦ p ⟧`` the
*interpretation* of ``p`` in ``𝑨``. This is defined inductively as follows.

1. If ``p`` is a variable symbol ``x : X`` and if ``a : X → ∣ 𝑨 ∣`` is a
   tuple of elements of ``∣ 𝑨 ∣``, then define ``𝑨 ⟦ p ⟧ a := a x``.

2. If ``p = f t``, where ``f : ∣ 𝑆 ∣`` is an operation symbol, if
   ``t : (arity 𝐹) f → 𝑻 X`` is a tuple of terms, and if
   ``a : X → ∣ 𝑨 ∣`` is a tuple from ``𝑨``, then define
   ``𝑨 ⟦ p ⟧ a := (f ᵒ 𝑨) (λ i → 𝑨 ⟦ t i ⟧ a)``.

Thus interpretation of a term is defined by structural induction.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Structures.Terms where

  -- Imports from Agda and the Agda Standard Library ---------------------
  open import Agda.Primitive         using ( lsuc ; _⊔_ ; Level ) renaming ( Set to Type )
  open import Base.Structures.Basic  using ( signature ; structure ; _ᵒ_ )
  open import Base.Terms.Basic

  private variable
   𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ χ α ρ : Level
   𝐹 : signature 𝓞₀ 𝓥₀
   𝑅 : signature 𝓞₁ 𝓥₁
   X : Type χ

  open signature
  open structure

  _⟦_⟧ : (𝑨 : structure 𝐹 𝑅 {α} {ρ}) → Term X → (X → carrier 𝑨) → carrier 𝑨
  𝑨 ⟦ ℊ x ⟧ = λ a → a x
  𝑨 ⟦ node f t ⟧ = λ a → (f ᵒ 𝑨) (λ i → (𝑨 ⟦ t i ⟧ ) a)

--------------


