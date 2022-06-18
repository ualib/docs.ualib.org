.. FILE      : Setoid/Functions/Basic.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 05 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette and William DeMeo

.. highlight:: agda
.. role:: code

.. _function-basics:

Function Basics
~~~~~~~~~~~~~~~

This is the `Setoid.Functions.Basic`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Setoid.Functions.Basic where

  open import Function         using ( id ) renaming ( Func to _⟶_ )
  open import Relation.Binary  using ( Setoid )
  open import Level            using ( Level )

  import Function.Base as Fun

  private variable α ρᵃ β ρᵇ γ ρᶜ : Level

  open _⟶_ renaming ( f to _⟨$⟩_ )

  𝑖𝑑 : {A : Setoid α ρᵃ} → A ⟶ A
  𝑖𝑑 {A} = record { f = id ; cong = id }

  _∘_ :  {A : Setoid α ρᵃ}{B : Setoid β ρᵇ}{C : Setoid γ ρᶜ}
   →     B ⟶ C → A ⟶ B → A ⟶ C

  f ∘ g = record  { f = Fun._∘_ (_⟨$⟩_ f) (_⟨$⟩_ g)
                  ; cong = Fun._∘_ (cong f) (cong g)
                  }



