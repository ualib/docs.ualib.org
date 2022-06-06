.. FILE      : Base/Homomorphisms/Products.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 03 Jun 2022
.. UPDATED   : 03 Jun 2022
.. COPYRIGHT : (c) 2022 William DeMeo


.. _products-of-homomorphisms:

Products of Homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Base.Homomorphisms.Products`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Base.Algebras.Basic

  module Base.Homomorphisms.Products {𝑆 : Signature 𝓞 𝓥} where

  -- Imports from Agda and the Agda Standard Library --------------------------
  open import Agda.Primitive using ( _⊔_ ; lsuc ) renaming ( Set to Type )
  open import Axiom.Extensionality.Propositional
                             using () renaming (Extensionality to funext)
  open import Data.Product   using ( _,_ )
  open import Level          using ( Level )
  open import Relation.Binary.PropositionalEquality using ( refl )

  -- Imports from the Agda Universal Algebras Library ----------------------
  open import Base.Overture.Preliminaries using ( ∣_∣ ; ∥_∥)
  open import Base.Algebras.Products    {𝑆 = 𝑆} using ( ⨅ )
  open import Base.Homomorphisms.Basic  {𝑆 = 𝑆} using ( hom ; epi )

  private variable 𝓘 β : Level

Suppose we have an algebra ``𝑨``, a type ``I : Type 𝓘``, and a family ``ℬ : I →
Algebra β 𝑆`` of algebras. We sometimes refer to the inhabitants of ``I`` as
*indices*, and call ``ℬ`` an *indexed family of algebras*.

If in addition we have a family ``𝒽 : (i : I) → hom 𝑨 (ℬ i)`` of homomorphisms,
then we can construct a homomorphism from ``𝑨`` to the product ``⨅ ℬ`` in the
natural way.

::

  module _ {I : Type 𝓘}(ℬ : I → Algebra β 𝑆) where

   ⨅-hom-co : funext 𝓘 β → {α : Level}(𝑨 : Algebra α 𝑆) → (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
   ⨅-hom-co fe 𝑨 𝒽 = (λ a i → ∣ 𝒽 i ∣ a) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 𝒶)

The foregoing generalizes easily to the case in which the domain is also a
product of a family of algebras. That is, if we are given ``𝒜 : I → Algebra α 𝑆``
and ``ℬ : I → Algebra β 𝑆`` (two families of ``𝑆``-algebras), and
``𝒽 :  Π i ꞉ I , hom (𝒜 i)(ℬ i)`` (a family of homomorphisms), then we can
construct a homomorphism from ``⨅ 𝒜`` to  ``⨅ ℬ`` in the following natural way.

::

   ⨅-hom : funext 𝓘 β → {α : Level}(𝒜 : I → Algebra α 𝑆) → (∀ (i : I) → hom (𝒜 i) (ℬ i)) → hom (⨅ 𝒜)(⨅ ℬ)
   ⨅-hom fe 𝒜 𝒽 = (λ x i → ∣ 𝒽 i ∣ (x i)) , (λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 (λ x → 𝒶 x i))

.. _projection-out-of-products:

Projection out of products
^^^^^^^^^^^^^^^^^^^^^^^^^^

Later we will need a proof of the fact that projecting out of a product
algebra onto one of its factors is a homomorphism.

::

   ⨅-projection-hom : (i : I) → hom (⨅ ℬ) (ℬ i)
   ⨅-projection-hom = λ x → (λ z → z x) , λ _ _ → refl

We could prove a more general result involving projections onto multiple
factors, but so far the single-factor result has sufficed.

