.. FILE      : Setoid/Functions/Surjective.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 07 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette, William DeMeo

.. highlight:: agda
.. role:: code

.. _surjective-setoid-functions:

Surjective setoid functions
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Functions.Surjective`_ module of the agda-algebras_ library.

Let ``𝑨 = (A , ≈₀)`` and ``𝑩 = (B , ≈₁)`` be setoids.  A *surjective setoid
function* from ``𝑨`` to ``𝑩`` is a setoid function ``f : 𝑨 ⟶ 𝑩`` such that
``∀(b : B) ∃(a : A) f ⟨$⟩ a ≈₁ b``. In other words, the range and codomain of
``f`` are the same.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Setoid.Functions.Surjective where

  -- Imports from Agda and the Agda Standard Library --------------------------
  open import Agda.Primitive    using ( _⊔_ ; Level )  renaming ( Set to Type )
  open import Data.Product      using ( _,_ ; Σ-syntax )
  open import Function.Bundles  using ( Surjection )   renaming ( Func to _⟶_ )
  open import Function          using ( IsSurjection )
  open import Relation.Binary   using ( Setoid )

  open import Function.Construct.Composition using ()  renaming ( isSurjection to isOnto )
  import Function.Definitions as FD

  -- Imports from agda-algebras -----------------------------------------------
  open import Base.Overture              using ( ∣_∣ ; ∥_∥ ; ∃-syntax ; transport )
  open import Setoid.Functions.Basic     using ( _∘_ )
  open import Setoid.Functions.Inverses  using ( Img_∋_ ; Image_∋_ ; Inv ; InvIsInverseʳ )

  private variable α ρᵃ β ρᵇ γ ρᶜ : Level

  open Image_∋_

  module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

   open Setoid 𝑨  using ()               renaming (Carrier to A; _≈_ to _≈₁_; isEquivalence to isEqA )
   open Setoid 𝑩  using ( trans ; sym )  renaming (Carrier to B; _≈_ to _≈₂_; isEquivalence to isEqB )

   open Surjection {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩}  renaming (f to _⟨$⟩_)
   open _⟶_ {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩}         renaming (f to _⟨$⟩_ )
   open FD _≈₁_ _≈₂_

   isSurj : (A → B) →  Type (α ⊔ β ⊔ ρᵇ)
   isSurj f = ∀ {y} → Img_∋_ {𝑨 = 𝑨}{𝑩 = 𝑩} f y

   IsSurjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ β ⊔ ρᵇ)
   IsSurjective F = ∀ {y} → Image F ∋ y

   isSurj→IsSurjective : (F : 𝑨 ⟶ 𝑩) → isSurj (_⟨$⟩_ F) → IsSurjective F
   isSurj→IsSurjective F isSurjF {y} = hyp isSurjF
    where
    hyp : Img (_⟨$⟩_ F) ∋ y → Image F ∋ y
    hyp (Img_∋_.eq a x) = eq a x

   open Image_∋_

   SurjectionIsSurjective : (Surjection 𝑨 𝑩) → Σ[ g ∈ (𝑨 ⟶ 𝑩) ] (IsSurjective g)
   SurjectionIsSurjective s = g , gE
    where
    g : 𝑨 ⟶ 𝑩
    g = (record { f = _⟨$⟩_ s ; cong = cong s })
    gE : IsSurjective g
    gE {y} = eq ∣ (surjective s) y ∣ (sym ∥ (surjective s) y ∥)

   SurjectionIsSurjection : (Surjection 𝑨 𝑩) → Σ[ g ∈ (𝑨 ⟶ 𝑩) ] (IsSurjection _≈₁_ _≈₂_ (_⟨$⟩_ g))
   SurjectionIsSurjection s = g , gE
    where
    g : 𝑨 ⟶ 𝑩
    g = (record { f = _⟨$⟩_ s ; cong = cong s })
    gE : IsSurjection _≈₁_ _≈₂_ (_⟨$⟩_ g)
    IsSurjection.isCongruent gE = record { cong = cong g ; isEquivalence₁ = isEqA ; isEquivalence₂ = isEqB }
    IsSurjection.surjective gE y = ∣ (surjective s) y ∣ , ∥ (surjective s) y ∥

With the next definition we represent a *right-inverse* of a surjective setoid function.

::

   SurjInv : (f : 𝑨 ⟶ 𝑩) → IsSurjective f → B → A
   SurjInv f fE b = Inv f (fE {b})

Thus, a right-inverse of ``f`` is obtained by applying ``Inv`` to ``f``
and a proof of ``IsSurjective f``. Next we prove that this does indeed
give the right-inverse.

::

   SurjInvIsInverseʳ : (f : 𝑨 ⟶ 𝑩)(fE : IsSurjective f) → ∀ {b} → (f ⟨$⟩ ((SurjInv f fE) b)) ≈₂ b
   SurjInvIsInverseʳ f fE = InvIsInverseʳ fE

We conclude this module by giving a formal proof of the fact that composition of two surjective surjective
setoid functions is again a surjective setoid function.

::

  module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ}{𝑪 : Setoid γ ρᶜ} where

   open Setoid 𝑨  using ()               renaming (Carrier to A; _≈_ to _≈₁_)
   open Setoid 𝑩  using ( trans ; sym )  renaming (Carrier to B; _≈_ to _≈₂_)
   open Setoid 𝑪  using ()               renaming (Carrier to C; _≈_ to _≈₃_)

   open Surjection  renaming (f to _⟨$⟩_)
   open _⟶_         renaming (f to _⟨$⟩_ )
   open FD _≈₁_ _≈₂_


   ∘-IsSurjective : {G : 𝑨 ⟶ 𝑪}{H : 𝑪 ⟶ 𝑩} → IsSurjective G → IsSurjective H → IsSurjective (H ∘ G)
   ∘-IsSurjective {G} {H} gE hE {y} = Goal
    where
    mp : Image H ∋ y → Image H ∘ G ∋ y
    mp (eq c p) = η gE
     where
     η : Image G ∋ c → Image H ∘ G ∋ y
     η (eq a q) = eq a (trans p (cong H q))

    Goal : Image H ∘ G ∋ y
    Goal = mp hE


   ∘-epic : Surjection 𝑨 𝑪 → Surjection 𝑪 𝑩 → Surjection 𝑨 𝑩
   Surjection.f (∘-epic g h) x = h ⟨$⟩ (g ⟨$⟩ x)
   Surjection.cong (∘-epic g h) {x} {y} xy = cong h (cong g xy)
   Surjection.surjective (∘-epic g h) = IsSurjection.surjective hgSurj
    where
    gSurj : Σ[ G ∈ (𝑨 ⟶ 𝑪) ] (IsSurjection _≈₁_ _≈₃_ (_⟨$⟩_ G))
    gSurj = SurjectionIsSurjection g
    hSurj : Σ[ H ∈ (𝑪 ⟶ 𝑩) ] (IsSurjection _≈₃_ _≈₂_ (_⟨$⟩_ H))
    hSurj = SurjectionIsSurjection h

    hgSurj : IsSurjection _≈₁_ _≈₂_ (λ x → h ⟨$⟩ (g ⟨$⟩ x))
    hgSurj = isOnto ∥ gSurj ∥ ∥ hSurj ∥


   epic-factor :  (f : 𝑨 ⟶ 𝑩)(g : 𝑨 ⟶ 𝑪)(h : 𝑪 ⟶ 𝑩)
    →             IsSurjective f → (∀ i → (f ⟨$⟩ i) ≈₂ ((h ∘ g) ⟨$⟩ i)) → IsSurjective h

   epic-factor f g h fE compId {y} = Goal
    where
     finv : B → A
     finv = SurjInv f fE

     ζ : y ≈₂ (f ⟨$⟩ (finv y))
     ζ = sym (SurjInvIsInverseʳ f fE)

     η : y ≈₂ ((h ∘ g) ⟨$⟩ (finv y))
     η = trans ζ (compId (finv y))

     Goal : Image h ∋ y
     Goal = eq (g ⟨$⟩ (finv y)) η
