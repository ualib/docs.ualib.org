Quotients of setoids
~~~~~~~~~~~~~~~~~~~~

This is the [Setoid.Relations.Quotients][] module of the [Agda Universal
Algebra Library][].

\\begin{code}

{-# OPTIONS –without-K –exact-split –safe #-}

module Setoid.Relations.Quotients where

– Imports from Agda and the Agda Standard Library ——————————- open
import Agda.Primitive using ( *⊔* ; Level ; lsuc ) renaming ( Set to
Type ) open import Data.Product using ( *,* ; Σ-syntax ) renaming ( *×*
to *∧* ) open import Function using ( id ) open import Function.Bundles
using () renaming ( Func to *⟶* ) open import Relation.Binary using (
IsEquivalence ) renaming ( Rel to BinRel ) open import Relation.Unary
using ( Pred ; *∈* ; *⊆* ) open import Relation.Binary using ( Setoid )
open import Relation.Binary.PropositionalEquality as ≡ using ( *≡* )

– Imports from agda-algebras —————————————————– open import
Base.Overture.Preliminaries using ( ∣\ *∣ ; ∥*\ ∥ ) open import
Setoid.Relations.Discrete using ( fker ) open import
Base.Relations.Quotients using ( [_] ; Equivalence )

private variable α β ρᵃ ρᵇ ℓ : Level

\\end{code}

Kernels
^^^^^^^

A prominent example of an equivalence relation is the kernel of any
function.

\\begin{code}

open *⟶* using ( cong ) renaming ( f to *⟨$⟩* )

module \_ {𝐴 : Setoid α ρᵃ}{𝐵 : Setoid β ρᵇ} where open Setoid 𝐴 using (
refl ) renaming (Carrier to A ) open Setoid 𝐵 using ( sym ; trans )
renaming (Carrier to B )

ker-IsEquivalence : (f : 𝐴 ⟶ 𝐵) → IsEquivalence (fker f)
IsEquivalence.refl (ker-IsEquivalence f) = cong f refl IsEquivalence.sym
(ker-IsEquivalence f) = sym IsEquivalence.trans (ker-IsEquivalence f) =
trans

record IsBlock {A : Type α}{ρ : Level}(P : Pred A ρ){R : BinRel A ρ} :
Type(α ⊔ lsuc ρ) where constructor mkblk field a : A P≈[a] : ∀ x → (x ∈
P → [ a ]{ρ} R x) ∧ ([ a ]{ρ} R x → x ∈ P)

\\end{code}

If ``R`` is an equivalence relation on ``A``, then the *quotient* of
``A`` modulo ``R`` is denoted by ``A / R`` and is defined to be the
collection ``{[ u ] ∣  y : A}`` of all ``R``-blocks.

\\begin{code}

open IsBlock Quotient : (A : Type α) → Equivalence A{ℓ} → Type(α ⊔ lsuc
ℓ) Quotient A R = Σ[ P ∈ Pred A \_ ] IsBlock P {∣ R ∣}

*/* : (A : Type α) → Equivalence A{ℓ} → Setoid \_ *A / R = record {
Carrier = A ;*\ ≈\_ = ∣ R ∣ ; isEquivalence = ∥ R ∥ }

infix -1 */*

\\end{code}

We use the following type to represent an R-block with a designated
representative.

\\begin{code}

open Setoid ⟪_⟫ : {α : Level}{A : Type α} → A → {R : Equivalence A{ℓ}} →
Carrier (A / R) ⟪ a ⟫{R} = a

module \_ {A : Type α}{R : Equivalence A{ℓ} } where

open Setoid (A / R) using () renaming ( *≈* to *≈₁* )

⟪\ *∼*\ ⟫-intro : (u v : A) → ∣ R ∣ u v → ⟪ u ⟫{R} ≈₁ ⟪ v ⟫{R} ⟪ u ∼ v
⟫-intro = id

⟪\ *∼*\ ⟫-elim : (u v : A) → ⟪ u ⟫{R} ≈₁ ⟪ v ⟫{R} → ∣ R ∣ u v ⟪ u ∼ v
⟫-elim = id

≡→⊆ : {A : Type α}{ρ : Level}(Q R : Pred A ρ) → Q ≡ R → Q ⊆ R ≡→⊆ Q .Q
≡.refl {x} Qx = Qx

\\end{code}

--------------

`← Setoid.Relations.Discrete <Setoid.Relations.Discrete.html>`__
`Setoid.Algebras → <Setoid.Algebras.html>`__

{% include UALib.Links.md %}
