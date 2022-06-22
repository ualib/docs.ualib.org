.. FILE      : Base/Overture/Injective.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 02 Jun 2022
.. UPDATED   : 02 Jun 2022
.. COPYRIGHT : (c) 2022 William DeMeo

.. _injective-functions:

Injective functions
~~~~~~~~~~~~~~~~~~~

This is the `Base.Overture.Injective`_ module of the agda-algebras_ library.

We say that a function ``f : A → B`` is *injective* (or *monic*) if it
does not map two distinct elements of the domain to the same point in
the codomain. The following type manifests this property.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Overture.Injective where

  -- Imports from Agda and the Agda Standard Library
  open import Agda.Primitive using ( _⊔_ ; Level ) renaming ( Set to Type )
  open import Function.Bundles using ( _↣_ )
  open import Function.Construct.Identity using ( id-↣ )
  open import Function.Base using ( _∘_ )
  open import Function.Definitions as FD using ( Injective )
  open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
  open import Relation.Binary using ( Rel )

  private variable α β γ ℓ₁ ℓ₂ ℓ₃ : Level

  id-is-injective : {A : Type α} → A ↣ A
  id-is-injective {A = A} = id-↣ A

  IsInjective : {A : Type α}{B : Type β} → (A → B) → Type (α ⊔ β)
  IsInjective f = Injective _≡_ _≡_ f


Next, we prove that the composition of injective functions is injective.

::

  ∘-injective :  {A : Type α}{B : Type β}{C : Type γ}{f : A → B}{g : B → C}
   →             IsInjective f → IsInjective g → IsInjective (g ∘ f)

  ∘-injective fi gi = λ x → fi (gi x)


