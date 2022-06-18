Homomorphic images of setoid algebras
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This is the [Setoid.Homomorphisms.HomomorphicImages][] module of the
[Agda Universal Algebra Library][].

\\begin{code}

{-# OPTIONS –without-K –exact-split –safe #-}

open import Base.Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Setoid.Homomorphisms.HomomorphicImages {𝑆 : Signature 𝓞 𝓥} where

– Imports from Agda and the Agda Standard Library —————————————— open
import Agda.Primitive using ( *⊔* ; lsuc ) renaming ( Set to Type ) open
import Data.Product using ( *,* ; Σ-syntax ) renaming ( *×* to *∧* ;
proj₁ to fst ; proj₂ to snd ) open import Function using ( Func ; *on* ;
*∘* ; id ) open import Level using ( Level ) open import Relation.Binary
using ( Setoid ; *Preserves*\ ⟶\_ ) open import Relation.Unary using (
Pred ; *∈* ) open import Relation.Binary.PropositionalEquality as ≡
using ()

– Imports from the Agda Universal Algebra Library ——————————————— open
import Base.Overture.Preliminaries using ( ∣\ *∣ ; ∥*\ ∥ ; transport )
open import Setoid.Overture.Preliminaries using ( lift∼lower ) open
import Setoid.Overture.Inverses using ( Ran ; *range ; preimage ; image
; Inv ) using ( preimage≈image ; InvIsInverseʳ ; Image\ ∋ ) open import
Setoid.Overture.Surjective using ( IsSurjective ; ∘-IsSurjective ) open
import Setoid.Algebras.Basic {𝑆 = 𝑆} using ( Algebra ; ov ; ̂ ; ⟨\ ⟩ ;
Lift-Algˡ ) using ( Lift-Alg ; 𝕌[_] ) open import
Setoid.Homomorphisms.Basic {𝑆 = 𝑆} using ( hom ; IsHom ) open import
Setoid.Homomorphisms.Isomorphisms {𝑆 = 𝑆} using (*\ ≅\_ ; Lift-≅ ) open
import Setoid.Homomorphisms.Properties {𝑆 = 𝑆} using ( Lift-homˡ ;
ToLiftˡ ; lift-hom-lemma ) using ( 𝒾𝒹 ; ∘-hom ) private variable α ρᵃ β
ρᵇ : Level

open Algebra

\\end{code}

We begin with what seems, for our purposes, the most useful way to
represent the class of *homomorphic images* of an algebra in dependent
type theory.

\\begin{code} open IsHom

*IsHomImageOf* : (𝑩 : Algebra β ρᵇ)(𝑨 : Algebra α ρᵃ) → Type (𝓞 ⊔ 𝓥 ⊔ α
⊔ β ⊔ ρᵃ ⊔ ρᵇ) 𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣

HomImages : Algebra α ρᵃ → Type (α ⊔ ρᵃ ⊔ ov (β ⊔ ρᵇ)) HomImages {β =
β}{ρᵇ = ρᵇ} 𝑨 = Σ[ 𝑩 ∈ Algebra β ρᵇ ] 𝑩 IsHomImageOf 𝑨

IdHomImage : {𝑨 : Algebra α ρᵃ} → 𝑨 IsHomImageOf 𝑨 IdHomImage {α = α}{𝑨
= 𝑨} = 𝒾𝒹 , λ {y} → Image_∋_.eq y refl where open Setoid (Domain 𝑨)
using ( refl )

\\end{code}

These types should be self-explanatory, but just to be sure, let’s
describe the Sigma type appearing in the second definition. Given an
``𝑆``-algebra ``𝑨 : Algebra α ρ``, the type ``HomImages 𝑨`` denotes the
class of algebras ``𝑩 : Algebra β ρ`` with a map ``φ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣``
such that ``φ`` is a surjective homomorphism.

The image algebra of a hom
^^^^^^^^^^^^^^^^^^^^^^^^^^

Here we show how to construct a Algebra (called ``ImageAlgebra`` below)
that is the image of given hom.

\\begin{code}

module \_ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where open Algebra 𝑨
using (Interp) renaming (Domain to A ) open Algebra 𝑩 using () renaming
(Domain to B ; Interp to InterpB )

open Setoid A using ( ) renaming ( *≈* to *≈₁* ; Carrier to ∣A∣) open
Setoid B using ( reflexive ) renaming ( *≈* to *≈₂* ; refl to refl₂ )
renaming ( sym to sym₂ ; trans to trans₂ ; Carrier to ∣B∣)

open Func using ( cong ) renaming (f to *⟨$⟩* ) open IsHom

HomImageOf[_] : hom 𝑨 𝑩 → Algebra (α ⊔ β ⊔ ρᵇ) ρᵇ HomImageOf[ h ] =
record { Domain = Ran ∣ h ∣ ; Interp = record { f = f’ ; cong = cong’ }
} where open Setoid (⟨ 𝑆 ⟩ (Ran ∣ h ∣)) using () renaming (Carrier to
SRanh ; *≈* to *≈₃* ; refl to refl₃ )

hhom : ∀ {𝑓}(x : ∥ 𝑆 ∥ 𝑓 → ∣ h ∣ range ) → (∣ h ∣ ⟨$⟩ (𝑓 ̂ 𝑨) ((∣ h ∣
preimage) ∘ x)) ≈₂ (𝑓 ̂ 𝑩) ((∣ h ∣ image) ∘ x)

hhom {𝑓} x = trans₂ (compatible ∥ h ∥) (cong InterpB (≡.refl , (∣ h ∣
preimage≈image) ∘ x))

f’ : SRanh → ∣ h ∣ range f’ (𝑓 , x) = (𝑓 ̂ 𝑩)((∣ h ∣ image)∘ x) – b : the
image in ∣B∣ , (𝑓 ̂ 𝑨)((∣ h ∣ preimage) ∘ x) – a : the preimage in ∣A∣ ,
hhom x – p : proof that ``(∣ h ∣ ⟨$⟩ a) ≈₂ b``

cong’ : ∀ {x y} → x ≈₃ y → ((∣ h ∣ image) (f’ x)) ≈₂ ((∣ h ∣ image) (f’
y)) cong’ {(𝑓 , u)} {(.𝑓 , v)} (≡.refl , EqA) = Goal

::

   where

   -- Alternative formulation of the goal:
   goal : (𝑓 ̂ 𝑩)(λ i → ((∣ h ∣ image)(u i))) ≈₂ (𝑓 ̂ 𝑩)(λ i → ((∣ h ∣ image) (v i)))
   goal = cong InterpB (≡.refl , EqA )

   Goal : (∣ h ∣ image) (f' (𝑓 , u)) ≈₂ (∣ h ∣ image) (f' (𝑓 , v))
   Goal = goal

   -- Note: `EqA : ∀ i → (∣ h ∣ image) (u i) ≈₂ (∣ h ∣ image) (v i)`

\\end{code}

Homomorphic images of classes of setoid algebras
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Given a class ``𝒦`` of ``𝑆``-algebras, we need a type that expresses the
assertion that a given algebra is a homomorphic image of some algebra in
the class, as well as a type that represents all such homomorphic
images.

\\begin{code}

IsHomImageOfClass : {𝒦 : Pred (Algebra α ρᵃ)(lsuc α)} → Algebra α ρᵃ →
Type (ov (α ⊔ ρᵃ)) IsHomImageOfClass {𝒦 = 𝒦} 𝑩 = Σ[ 𝑨 ∈ Algebra \_ \_ ]
((𝑨 ∈ 𝒦) ∧ (𝑩 IsHomImageOf 𝑨))

HomImageOfClass : Pred (Algebra α ρᵃ) (lsuc α) → Type (ov (α ⊔ ρᵃ))
HomImageOfClass 𝒦 = Σ[ 𝑩 ∈ Algebra \_ \_ ] IsHomImageOfClass {𝒦 = 𝒦} 𝑩

\\end{code}

Lifting tools
^^^^^^^^^^^^^

Here are some tools that have been useful (e.g., in the road to the
proof of Birkhoff’s HSP theorem). The first states and proves the simple
fact that the lift of an epimorphism is an epimorphism.

\\begin{code}

module \_ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where

open Algebra 𝑨 using () renaming ( Domain to A ) open Algebra 𝑩 using ()
renaming ( Domain to B ) open Setoid B using ( sym ; trans ) renaming (
*≈* to *≈₂* )

open Func using ( cong ) renaming ( f to *⟨$⟩* ) open Level

Lift-epi-is-epiˡ : (h : hom 𝑨 𝑩)(ℓᵃ ℓᵇ : Level) → IsSurjective ∣ h ∣ →
IsSurjective ∣ Lift-homˡ {𝑨 = 𝑨}{𝑩} h ℓᵃ ℓᵇ ∣

Lift-epi-is-epiˡ h ℓᵃ ℓᵇ hepi {b} = Goal where open Algebra (Lift-Algˡ 𝑩
ℓᵇ) using () renaming (Domain to lB ) open Setoid lB using () renaming (
*≈* to *≈ₗ₂* )

a : 𝕌[ 𝑨 ] a = Inv ∣ h ∣ hepi

lem1 : b ≈ₗ₂ (lift (lower b)) lem1 = lift∼lower {𝑨 = B} b

lem2’ : (lower b) ≈₂ (∣ h ∣ ⟨$⟩ a) lem2’ = sym (InvIsInverseʳ hepi)

lem2 : (lift (lower b)) ≈ₗ₂ (lift (∣ h ∣ ⟨$⟩ a)) lem2 = cong{From = B} ∣
ToLiftˡ{𝑨 = 𝑩}{ℓᵇ} ∣ lem2’

lem3 : (lift (∣ h ∣ ⟨\ :math:`⟩ a)) ≈ₗ₂ ((∣ Lift-homˡ h ℓᵃ ℓᵇ ∣ ⟨`\ ⟩
lift a)) lem3 = lift-hom-lemma h a ℓᵃ ℓᵇ

η : b ≈ₗ₂ (∣ Lift-homˡ h ℓᵃ ℓᵇ ∣ ⟨$⟩ lift a) η = trans lem1 (trans lem2
lem3)

Goal : Image ∣ Lift-homˡ h ℓᵃ ℓᵇ ∣ ∋ b Goal = Image_∋_.eq (lift a) η

Lift-Alg-hom-imageˡ : (ℓᵃ ℓᵇ : Level) → 𝑩 IsHomImageOf 𝑨 → (Lift-Algˡ 𝑩
ℓᵇ) IsHomImageOf (Lift-Algˡ 𝑨 ℓᵃ)

Lift-Alg-hom-imageˡ ℓᵃ ℓᵇ ((φ , φhom) , φepic) = Goal where lφ : hom
(Lift-Algˡ 𝑨 ℓᵃ) (Lift-Algˡ 𝑩 ℓᵇ) lφ = Lift-homˡ {𝑨 = 𝑨}{𝑩} (φ , φhom)
ℓᵃ ℓᵇ

lφepic : IsSurjective ∣ lφ ∣ lφepic = Lift-epi-is-epiˡ (φ , φhom) ℓᵃ ℓᵇ
φepic Goal : (Lift-Algˡ 𝑩 ℓᵇ) IsHomImageOf (Lift-Algˡ 𝑨 ℓᵃ) Goal = lφ ,
lφepic

module \_ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where open *≅*
Lift-HomImage-lemma : ∀{γ} → (Lift-Alg 𝑨 γ γ) IsHomImageOf 𝑩 → 𝑨
IsHomImageOf 𝑩 Lift-HomImage-lemma {γ} φ = ∘-hom ∣ φ ∣ (from Lift-≅) ,
∘-IsSurjective ∥ φ ∥ (fromIsSurjective (Lift-≅{𝑨 = 𝑨}))

module \_ {𝑨 𝑨’ : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where open *≅*
HomImage-≅ : 𝑨 IsHomImageOf 𝑨’ → 𝑨 ≅ 𝑩 → 𝑩 IsHomImageOf 𝑨’ HomImage-≅ φ
A≅B = ∘-hom ∣ φ ∣ (to A≅B) , ∘-IsSurjective ∥ φ ∥ (toIsSurjective A≅B)

HomImage-≅’ : 𝑨 IsHomImageOf 𝑨’ → 𝑨’ ≅ 𝑩 → 𝑨 IsHomImageOf 𝑩 HomImage-≅’
φ A’≅B = (∘-hom (from A’≅B) ∣ φ ∣) , ∘-IsSurjective (fromIsSurjective
A’≅B) ∥ φ ∥

\\end{code}
-----------

`←
Setoid.Homomorphisms.Isomorphisms <Setoid.Homomorphisms.Isomorphisms.html>`__
`Setoid.Terms → <Setoid.Terms.html>`__

{% include UALib.Links.md %}
