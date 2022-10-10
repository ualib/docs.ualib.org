.. FILE      : Base/Functions/Injective.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 02 Jun 2022
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-functions-injective-functions:

Injective functions
~~~~~~~~~~~~~~~~~~~

This is the `Base.Functions.Injective`_ module of the agda-algebras_ library.

We say that a function ``f : A → B`` is *injective* (or *monic*) if it
does not map two distinct elements of the domain to the same point in
the codomain. The following type manifests this property.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Functions.Injective where

  -- Imports from Agda and the Agda Standard Library -----------------------------
  open import Agda.Primitive                         using () renaming ( Set to Type )
  open import Function                               using ( _↣_ ;  _∘_ ; Injective )
  open import Function.Construct.Identity            using ( id-↣ )
  open import Level                                  using ( _⊔_ ; Level )
  open import Relation.Binary                        using ( Rel )
  open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )

  private variable α β γ ℓ₁ ℓ₂ ℓ₃ : Level

  id-is-injective : {A : Type α} → A ↣ A
  id-is-injective {A = A} = id-↣ A

  module _ {A : Type α}{B : Type β} where

   IsInjective : (A → B) → Type (α ⊔ β)
   IsInjective f = Injective _≡_ _≡_ f

The composition of injective functions is injective.

::

  ∘-injective :  {A : Type α}{B : Type β}{C : Type γ}{f : A → B}{g : B → C}
   →             IsInjective f → IsInjective g → IsInjective (g ∘ f)

  ∘-injective fi gi = λ x → fi (gi x)
