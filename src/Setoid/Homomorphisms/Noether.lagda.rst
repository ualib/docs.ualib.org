Homomorphism Theorems for Setoid Algebras
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the [Setoid.Homomorphisms.Noether][] module of the [Agda
Universal Algebra Library][].

\\begin{code}

{-# OPTIONS –without-K –exact-split –safe #-}

open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Homomorphisms.Noether {𝑆 : Signature 𝓞 𝓥} where

– Imports from Agda and the Agda Standard Library ————————— open import
Agda.Primitive using ( Level ) open import Data.Product using (Σ-syntax
; *,* ) renaming ( *×* to *∧* ) open import Function.Base using ( id )
open import Function.Bundles using () renaming ( Func to *⟶* ) open
import Relation.Binary using ( Setoid ) open import
Relation.Binary.PropositionalEquality as ≡ using ( *≡* ) import
Relation.Binary.Reasoning.Setoid as SetoidReasoning

– Imports from agda-algebras ———————————————— open import
Base.Overture.Preliminaries using ( ∣\ *∣ ; ∥*\ ∥ ) open import
Setoid.Overture.Injective using ( IsInjective ) open import
Setoid.Algebras.Basic using ( Algebra ; *̂*) open import
Setoid.Homomorphisms.Basic {𝑆 = 𝑆} using ( hom ; IsHom ) open import
Setoid.Homomorphisms.Kernels {𝑆 = 𝑆} using ( kerquo ; πker )

private variable α ρᵃ β ρᵇ γ ρᶜ ι : Level

\\end{code}

The First Homomorphism Theorem for setoid algebras
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

\\begin{code}

open *⟶* using ( cong ) renaming ( f to *⟨$⟩* ) open Algebra using (
Domain )

module \_ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}(hh : hom 𝑨 𝑩) where open
Algebra 𝑩 using ( Interp ) renaming ( Domain to B ) open Setoid B using
( *≈* ; refl ; sym ; trans ) – renaming ( *≈* to *≈₂* ) open Algebra
(kerquo hh) using () renaming ( Domain to A/hKer )

open IsHom private hfunc = ∣ hh ∣ h = *⟨$⟩* hfunc

FirstHomTheorem : Σ[ φ ∈ hom (kerquo hh) 𝑩 ] (∀ a → h a ≈ ∣ φ ∣
⟨\ :math:`⟩ (∣ πker hh ∣ ⟨`\ ⟩ a)) ∧ IsInjective ∣ φ ∣

FirstHomTheorem = (φ , φhom) , (λ \_ → refl) , φmon where φ : A/hKer ⟶ B
*⟨$⟩* φ = h cong φ = id

φhom : IsHom (kerquo hh) 𝑩 φ compatible φhom = trans (compatible ∥ hh ∥)
(cong Interp (≡.refl , (λ \_ → refl)))

φmon : IsInjective φ φmon = id

\\end{code}

Now we prove that the homomorphism whose existence is guaranteed by
``FirstHomTheorem`` is unique.

.. raw:: latex

   \begin{code}

    FirstHomUnique : (f g : hom (kerquo hh) 𝑩)
     →                 (∀ a →  h a ≈ ∣ f ∣ ⟨$⟩ (∣ πker hh ∣ ⟨$⟩ a))
     →                 (∀ a →  h a ≈ ∣ g ∣ ⟨$⟩ (∣ πker hh ∣ ⟨$⟩ a))
     →                 ∀ [a]  →  ∣ f ∣ ⟨$⟩ [a] ≈ ∣ g ∣ ⟨$⟩ [a]

    FirstHomUnique fh gh hfk hgk a = trans (sym (hfk a)) (hgk a)

   \end{code}

--------------

`← Setoid.Homomorphisms.Products <Setoid.Homomorphisms.Products.html>`__
`Setoid.Homomorphisms.Factor → <Setoid.Homomorphisms.Factor.html>`__

{% include UALib.Links.md %}
