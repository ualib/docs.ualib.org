.. FILE      : Setoid/Homomorphisms/Basic.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 13 Sep 2021
.. UPDATED   : 09 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette, William DeMeo

.. highlight:: agda
.. role:: code

.. _homs-of-setoid-algebras:

Homs of setoid algebras
~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Homomorphisms.Basic`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Base.Algebras using (𝓞 ; 𝓥 ; Signature )

  module Setoid.Homomorphisms.Basic {𝑆 : Signature 𝓞 𝓥} where

  -- Imports from Agda and the Agda Standard Library ------------------------------
  open import Agda.Primitive    using ( _⊔_ ; Level )  renaming ( Set to Type )
  open import Data.Product      using ( _,_ ; Σ ; Σ-syntax )
  open import Function.Bundles  using ()               renaming ( Func to _⟶_ )
  open import Relation.Binary   using ( Setoid )

  -- Imports from the Agda Universal Algebra Library ---------------------------
  open import Base.Overture.Preliminaries    using ( ∣_∣ ; ∥_∥ )
  open import Setoid.Functions.Injective     using ( IsInjective )
  open import Setoid.Functions.Surjective    using ( IsSurjective )
  open import Setoid.Algebras.Basic {𝑆 = 𝑆}  using ( Algebra ; _̂_ )

  private variable α β ρᵃ ρᵇ : Level

  module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where
   open Algebra 𝑨  using () renaming (Domain to A )
   open Algebra 𝑩  using () renaming (Domain to B )
   open Setoid A   using () renaming ( _≈_ to _≈₁_ )
   open Setoid B   using () renaming ( _≈_ to _≈₂_ )
   open _⟶_ {a = α}{ρᵃ}{β}{ρᵇ}{From = A}{To = B} renaming (f to _⟨$⟩_ )

   compatible-map-op : (A ⟶ B) → ∣ 𝑆 ∣ → Type (𝓥 ⊔ α ⊔ ρᵇ)
   compatible-map-op h f = ∀ {a} → (h ⟨$⟩ ((f ̂ 𝑨) a)) ≈₂ ((f ̂ 𝑩) (λ x → (h ⟨$⟩ (a x))))

   compatible-map : (A ⟶ B) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ)
   compatible-map h = ∀ {f} → compatible-map-op h f

   -- The property of being a homomorphism.
   record IsHom (h : A ⟶ B) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ ρᵇ) where
    field
     compatible : compatible-map h

   hom : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
   hom = Σ (A ⟶ B) IsHom


.. _monomorphisms-and-epimorphisms:

Monomorphisms and epimorphisms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   record IsMon (h : A ⟶ B) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
    field
     isHom : IsHom h
     isInjective : IsInjective h

    HomReduct : hom
    HomReduct = h , isHom

   mon : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
   mon = Σ (A ⟶ B) IsMon

   mon→hom : mon → hom
   mon→hom h = IsMon.HomReduct ∥ h ∥


   record IsEpi (h : A ⟶ B) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
    field
     isHom : IsHom h
     isSurjective : IsSurjective h

    HomReduct : hom
    HomReduct = h , isHom

   epi : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
   epi = Σ (A ⟶ B) IsEpi

   epi→hom : epi → hom
   epi→hom h = IsEpi.HomReduct ∥ h ∥

::

  module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where
   open IsEpi
   open IsMon

   mon→intohom : mon 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣
   mon→intohom (hh , hhM) = (hh , isHom hhM) , isInjective hhM

   epi→ontohom : epi 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsSurjective ∣ h ∣
   epi→ontohom (hh , hhE) = (hh , isHom hhE) , isSurjective hhE

