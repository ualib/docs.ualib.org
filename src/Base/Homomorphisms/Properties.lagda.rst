.. FILE      : Base/Homomorphisms/Properties.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 08 Sep 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-homomorphisms-properties-of-homomorphisms:

Properties of Homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Base.Homomorphisms.Properties`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (Signature ; 𝓞 ; 𝓥 )

  module Base.Homomorphisms.Properties {𝑆 : Signature 𝓞 𝓥} where

  -- Imports from Agda and the Agda Standard Library --------------------------------
  open import Data.Product  using ( _,_ )
  open import Function      using ( _∘_ )
  open import Level         using ( Level )

  open  import Relation.Binary.PropositionalEquality as ≡
        using ( _≡_ ; module ≡-Reasoning )

  -- Imports from the Agda Universal Algebras Library --------------------------------
  open import Overture                           using ( ∣_∣ ; ∥_∥ )
  open import Base.Algebras             {𝑆 = 𝑆}  using ( Algebra ; _̂_ ; Lift-Alg )
  open import Base.Homomorphisms.Basic  {𝑆 = 𝑆}  using ( hom ; is-homomorphism )

  private variable α β γ ρ : Level

.. _base-homomorphisms-homomorphism-composition:

Homomorphism composition
^^^^^^^^^^^^^^^^^^^^^^^^

The composition of homomorphisms is again a homomorphism. We formalize this in a number of alternative ways.

::

  open ≡-Reasoning

  module _ (𝑨 : Algebra α){𝑩 : Algebra β}(𝑪 : Algebra γ) where

    ∘-hom : hom 𝑨 𝑩  →  hom 𝑩 𝑪  →  hom 𝑨 𝑪
    ∘-hom (g , ghom) (h , hhom) = h ∘ g , Goal where

     Goal : ∀ 𝑓 a → (h ∘ g)((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑪)(h ∘ g ∘ a)
     Goal 𝑓 a =  (h ∘ g)((𝑓 ̂ 𝑨) a)  ≡⟨ ≡.cong h ( ghom 𝑓 a )  ⟩
                 h ((𝑓 ̂ 𝑩)(g ∘ a))  ≡⟨ hhom 𝑓 ( g ∘ a )       ⟩
                 (𝑓 ̂ 𝑪)(h ∘ g ∘ a)  ∎

    ∘-is-hom :  {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
     →          is-homomorphism 𝑨 𝑩 f → is-homomorphism 𝑩 𝑪 g
     →          is-homomorphism 𝑨 𝑪 (g ∘ f)

    ∘-is-hom {f} {g} fhom ghom = ∥ ∘-hom (f , fhom) (g , ghom) ∥

A homomorphism from ``𝑨`` to ``𝑩`` can be lifted to a homomorphism from
``Lift-Alg 𝑨 ℓᵃ`` to ``Lift-Alg 𝑩 ℓᵇ``. 

::

  open Level

  Lift-hom :  {𝑨 : Algebra α}(ℓᵃ : Level){𝑩 : Algebra β} (ℓᵇ : Level)
   →          hom 𝑨 𝑩  →  hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)

  Lift-hom {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ (f , fhom) = lift ∘ f ∘ lower , Goal
   where
   lABh : is-homomorphism (Lift-Alg 𝑨 ℓᵃ) 𝑩 (f ∘ lower)
   lABh = ∘-is-hom (Lift-Alg 𝑨 ℓᵃ) 𝑩 {lower}{f} (λ _ _ → ≡.refl) fhom

   Goal : is-homomorphism(Lift-Alg 𝑨 ℓᵃ)(Lift-Alg 𝑩 ℓᵇ) (lift ∘ (f ∘ lower))
   Goal = ∘-is-hom  (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)
                    {f ∘ lower}{lift} lABh λ _ _ → ≡.refl

We should probably point out that while the lifting and lowering homomorphisms
are important for our formal treatment of algebras in type theory, they never
arise—in fact, they are not even definable—in classical universal algebra based
on set theory.

