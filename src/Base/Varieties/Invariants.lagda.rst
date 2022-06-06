Algebraic invariants
~~~~~~~~~~~~~~~~~~~~

These are properties that are preserved under isomorphism.

\\begin{code}

{-# OPTIONS –without-K –exact-split –safe #-}

open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Base.Varieties.Invariants (𝑆 : Signature 𝓞 𝓥) where

– Imports from Agda and the Agda Standard Library ——————— open import
Agda.Primitive using ( Level ) renaming ( Set to Type ) open import
Relation.Unary using ( Pred )

– Imports from the Agda Universal Algebra Library ——————————————- open
import Base.Homomorphisms.Isomorphisms {𝑆 = 𝑆} using ( *≅* ) open import
Base.Algebras.Basic using ( Algebra )

private variable α ℓ : Level

AlgebraicInvariant : Pred (Algebra α 𝑆) ℓ → Type \_ AlgebraicInvariant P
= ∀ 𝑨 𝑩 → P 𝑨 → 𝑨 ≅ 𝑩 → P 𝑩

\\end{code}

--------------

{% include UALib.Links.md %}
