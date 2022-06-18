.. FILE      : Setoid/Homomorphisms/Kernels.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 17 Sep 2021
.. UPDATED   : 09 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette, William DeMeo

.. highlight:: agda
.. role:: code

.. _kernels-of-homomorphisms:

Kernels of homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~~

This is the [Setoid.Homomorphisms.Kernels][] module of the [Agda
Universal Algebra Library][].

\\begin{code}

{-# OPTIONS –without-K –exact-split –safe #-}

open import Base.Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Setoid.Homomorphisms.Kernels {𝑆 : Signature 𝓞 𝓥} where

– Imports from Agda and the Agda Standard Library —————————————— open
import Agda.Primitive using ( *⊔* ; lsuc ) open import Data.Product
using ( *,* ) open import Function using ( *∘* ; id ) open import
Function.Bundles using () renaming ( Func to *⟶* ) open import Level
using ( Level ) open import Relation.Binary using ( Setoid ) open import
Relation.Binary.PropositionalEquality as ≡ using ()

– Imports from the Agda Universal Algebra Library —————————————— open
import Base.Overture.Preliminaries using ( ∣\ *∣ ; ∥*\ ∥ ) open import
Setoid.Overture.Inverses using ( Image_∋\_ ) open import
Base.Relations.Discrete using ( kerRel ; kerRelOfEquiv ) open import
Setoid.Algebras.Basic {𝑆 = 𝑆} using ( Algebra ; *̂* ; ov ) open import
Setoid.Algebras.Congruences {𝑆 = 𝑆} using ( *∣≈* ; Con ; mkcon ; *╱* ;
IsCongruence ) open import Setoid.Homomorphisms.Basic {𝑆 = 𝑆} using (
hom ; IsHom ; epi ; IsEpi ; epi→hom ) open import
Setoid.Homomorphisms.Properties {𝑆 = 𝑆} using ( 𝒾𝒹 )

private variable α β ρᵃ ρᵇ ℓ : Level

open Algebra using ( Domain ) open *⟶* using ( cong ) renaming (f to
*⟨$⟩* )

module \_ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} (hh : hom 𝑨 𝑩) where

open Setoid (Domain 𝑨) using ( reflexive ) renaming ( *≈* to *≈₁* ) open
Algebra 𝑩 using ( Interp ) renaming (Domain to B ) open Setoid B using (
sym ; trans ; isEquivalence ) renaming ( *≈* to *≈₂* )

private h = *⟨$⟩* ∣ hh ∣

\\end{code}

``HomKerComp`` asserts that the kernel of a homomorphism is compatible
with the basic operations. That is, if each ``(u i, v i)`` belongs to
the kernel, then so does the pair ``((f ̂ 𝑨) u , (f ̂ 𝑨) v)``.

\\begin{code}

HomKerComp : 𝑨 ∣≈ (kerRel *≈₂* h) HomKerComp f {u}{v} kuv = Goal where
fhuv : ((f ̂ 𝑩)(h ∘ u)) ≈₂ ((f ̂ 𝑩)(h ∘ v)) fhuv = cong Interp (≡.refl ,
kuv) lem1 : (h ((f ̂ 𝑨) u)) ≈₂ ((f ̂ 𝑩) (h ∘ u)) lem1 = IsHom.compatible ∥
hh ∥

lem2 : ((f ̂ 𝑩) (h ∘ v)) ≈₂ (h ((f ̂ 𝑨) v)) lem2 = sym (IsHom.compatible ∥
hh ∥) Goal : (h ((f ̂ 𝑨) u)) ≈₂ (h ((f ̂ 𝑨) v)) Goal = trans lem1 (trans
fhuv lem2)

\\end{code}

The kernel of a homomorphism is a congruence of the domain, which we
construct as follows.

\\begin{code}

kercon : Con 𝑨 kercon = (kerRel *≈₂* h) , mkcon (λ x → cong ∣ hh ∣ x)
(kerRelOfEquiv isEquivalence h) (HomKerComp)

\\end{code}

Now that we have a congruence, we can construct the quotient relative to
the kernel.

\\begin{code}

kerquo : Algebra α ρᵇ kerquo = 𝑨 ╱ kercon

ker[*⇒*]\_ : (𝑨 : Algebra α ρᵃ) (𝑩 : Algebra β ρᵇ) → hom 𝑨 𝑩 → Algebra
\_ \_ ker[ 𝑨 ⇒ 𝑩 ] h = kerquo h \\end{code}

The canonical projection
^^^^^^^^^^^^^^^^^^^^^^^^

Given an algebra ``𝑨`` and a congruence ``θ``, the *canonical
projection* is a map from ``𝑨`` onto ``𝑨 ╱ θ`` that is constructed, and
proved epimorphic, as follows.

\\begin{code}

module \_ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} (h : hom 𝑨 𝑩) where

open IsCongruence

πepi : (θ : Con 𝑨 {ℓ}) → epi 𝑨 (𝑨 ╱ θ) πepi θ = p , pepi where

open Algebra (𝑨 ╱ θ) using () renaming ( Domain to A/θ ) open Setoid A/θ
using ( sym ; refl ) open IsHom {𝑨 = (𝑨 ╱ θ)} using ( compatible )

p : (Domain 𝑨) ⟶ A/θ p = record { f = id ; cong = reflexive ∥ θ ∥ }

pepi : IsEpi 𝑨 (𝑨 ╱ θ) p pepi = record { isHom = record { compatible =
sym (compatible ∥ 𝒾𝒹 ∥) } ; isSurjective = λ {y} → Image_∋_.eq y refl }

\\end{code}

In may happen that we don’t care about the surjectivity of ``πepi``, in
which case would might prefer to work with the *homomorphic reduct* of
``πepi``. This is obtained by applying ``epi-to-hom``, like so.

.. raw:: latex

   \begin{code}

    πhom : (θ : Con 𝑨 {ℓ}) → hom 𝑨 (𝑨 ╱ θ)
    πhom θ = epi→hom 𝑨 (𝑨 ╱ θ) (πepi θ)

   \end{code}

We combine the foregoing to define a function that takes 𝑆-algebras
``𝑨`` and ``𝑩``, and a homomorphism ``h : hom 𝑨 𝑩`` and returns the
canonical epimorphism from ``𝑨`` onto ``𝑨 [ 𝑩 ]/ker h``. (Recall, the
latter is the special notation we defined above for the quotient of
``𝑨`` modulo the kernel of ``h``.)

.. raw:: latex

   \begin{code}

    πker : epi 𝑨 (ker[ 𝑨 ⇒ 𝑩 ] h)
    πker = πepi (kercon h)

   \end{code}

The kernel of the canonical projection of ``𝑨`` onto ``𝑨 / θ`` is equal
to ``θ``, but since equality of inhabitants of certain types (like
``Congruence`` or ``Rel``) can be a tricky business, we settle for
proving the containment ``𝑨 / θ ⊆ θ``. Of the two containments, this is
the easier one to prove; luckily it is also the one we need later.

.. raw:: latex

   \begin{code}

    open IsCongruence

    ker-in-con : {θ : Con 𝑨 {ℓ}}
     →           ∀ {x}{y} → ∣ kercon (πhom θ) ∣ x y →  ∣ θ ∣ x y

    ker-in-con = id

   \end{code}

--------------

`←
Setoid.Homomorphisms.Properties <Setoid.Homomorphisms.Properties.html>`__
`Setoid.Homomorphisms.Products → <Setoid.Homomorphisms.Products.html>`__

{% include UALib.Links.md %}
