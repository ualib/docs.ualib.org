.. FILE      : Setoid/Homomorphisms/Kernels.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 13 Sep 2021
.. UPDATED   : 18 Jun 2022

.. highlight:: agda
.. role:: code

.. _kernels-of-homomorphisms:

Kernels of homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Homomorphisms.Kernels`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (𝓞 ; 𝓥 ; Signature)

  module Setoid.Homomorphisms.Kernels {𝑆 : Signature 𝓞 𝓥} where

  -- Imports from Agda and the Agda Standard Library ------------------------------------------
  open  import Data.Product      using ( _,_ )
  open  import Function          using ( _∘_ ; id ) renaming ( Func to _⟶_ )
  open  import Level             using ( Level )
  open  import Relation.Binary   using ( Setoid )
  open  import Relation.Binary.PropositionalEquality as ≡ using ()

  -- Imports from the Agda Universal Algebra Library ------------------------------------------
  open  import Overture          using  ( ∣_∣ ; ∥_∥ )
  open  import Base.Relations    using  ( kerRel ; kerRelOfEquiv )
  open  import Setoid.Functions  using  ( Image_∋_ )

  open  import Setoid.Algebras {𝑆 = 𝑆}
        using ( Algebra ; _̂_ ; ov ; _∣≈_ ; Con ; mkcon ; _╱_ ; IsCongruence )

  open  import Setoid.Homomorphisms.Basic {𝑆 = 𝑆}
        using ( hom ; IsHom ; epi ; IsEpi ; epi→hom )

  open  import Setoid.Homomorphisms.Properties {𝑆 = 𝑆} using ( 𝒾𝒹 )

  private variable  α β ρᵃ ρᵇ ℓ : Level

  open Algebra  using ( Domain )
  open _⟶_      using ( cong ) renaming (f to _⟨$⟩_ )

  module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} (hh : hom 𝑨 𝑩) where

   open Setoid (Domain 𝑨)  renaming ( _≈_ to _≈₁_ )  using ( reflexive )
   open Algebra 𝑩          renaming (Domain to B )   using ( Interp )
   open Setoid B           renaming ( _≈_ to _≈₂_ )
                           using ( sym ; trans ; isEquivalence )
   private h = _⟨$⟩_ ∣ hh ∣

``HomKerComp`` asserts that the kernel of a homomorphism is compatible
with the basic operations. That is, if each ``(u i, v i)`` belongs to
the kernel, then so does the pair ``((f ̂ 𝑨) u , (f ̂ 𝑨) v)``.

::

   HomKerComp : 𝑨 ∣≈ kerRel _≈₂_ h
   HomKerComp f {u}{v} kuv = Goal
    where
    fhuv : (f ̂ 𝑩)(h ∘ u) ≈₂ (f ̂ 𝑩)(h ∘ v)
    fhuv = cong Interp (≡.refl , kuv)

    lem1 : h ((f ̂ 𝑨) u) ≈₂ (f ̂ 𝑩)(h ∘ u)
    lem1 = IsHom.compatible ∥ hh ∥

    lem2 : (f ̂ 𝑩) (h ∘ v) ≈₂ h ((f ̂ 𝑨) v)
    lem2 = sym (IsHom.compatible ∥ hh ∥)

    Goal : h ((f ̂ 𝑨) u) ≈₂ h ((f ̂ 𝑨) v)
    Goal = trans lem1 (trans fhuv lem2)

The kernel of a homomorphism is a congruence of the domain, which we
construct as follows.

::

   kercon : Con 𝑨
   kercon =  kerRel _≈₂_ h ,
             mkcon (λ x → cong ∣ hh ∣ x)(kerRelOfEquiv isEquivalence h)(HomKerComp)

Now that we have a congruence, we can construct the quotient relative to
the kernel.

::

   kerquo : Algebra α ρᵇ
   kerquo = 𝑨 ╱ kercon

::

  ker[_⇒_]_ :  (𝑨 : Algebra α ρᵃ) (𝑩 : Algebra β ρᵇ) → hom 𝑨 𝑩 → Algebra _ _
  ker[ 𝑨 ⇒ 𝑩 ] h = kerquo h


.. _the-canonical-projection:

The canonical projection
^^^^^^^^^^^^^^^^^^^^^^^^

Given an algebra ``𝑨`` and a congruence ``θ``, the *canonical
projection* is a map from ``𝑨`` onto ``𝑨 ╱ θ`` that is constructed, and
proved epimorphic, as follows.

::

  module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} (h : hom 𝑨 𝑩) where
   open IsCongruence

   πepi : (θ : Con 𝑨 {ℓ}) → epi 𝑨 (𝑨 ╱ θ)
   πepi θ = p , pepi
    where

    open Algebra (𝑨 ╱ θ)      using () renaming ( Domain to A/θ )
    open Setoid A/θ           using ( sym ; refl )
    open IsHom {𝑨 = (𝑨 ╱ θ)}  using ( compatible )

    p : (Domain 𝑨) ⟶ A/θ
    p = record { f = id ; cong = reflexive ∥ θ ∥ }

    pepi : IsEpi 𝑨 (𝑨 ╱ θ) p
    pepi = record  { isHom = record { compatible = sym (compatible ∥ 𝒾𝒹 ∥) }
                   ; isSurjective = λ {y} → Image_∋_.eq y refl
                   }


In may happen that we don’t care about the surjectivity of ``πepi``, in
which case would might prefer to work with the *homomorphic reduct* of
``πepi``. This is obtained by applying ``epi-to-hom``, like so.

::

   πhom : (θ : Con 𝑨 {ℓ}) → hom 𝑨 (𝑨 ╱ θ)
   πhom θ = epi→hom 𝑨 (𝑨 ╱ θ) (πepi θ)

We combine the foregoing to define a function that takes 𝑆-algebras
``𝑨`` and ``𝑩``, and a homomorphism ``h : hom 𝑨 𝑩`` and returns the
canonical epimorphism from ``𝑨`` onto ``𝑨 [ 𝑩 ]/ker h``. (Recall, the
latter is the special notation we defined above for the quotient of
``𝑨`` modulo the kernel of ``h``.)

::

   πker : epi 𝑨 (ker[ 𝑨 ⇒ 𝑩 ] h)
   πker = πepi (kercon h)

The kernel of the canonical projection of ``𝑨`` onto ``𝑨 / θ`` is equal
to ``θ``, but since equality of inhabitants of certain types (like
``Congruence`` or ``Rel``) can be a tricky business, we settle for
proving the containment ``𝑨 / θ ⊆ θ``. Of the two containments, this is
the easier one to prove; luckily it is also the one we need later.

::

   open IsCongruence

   ker-in-con : {θ : Con 𝑨 {ℓ}} → ∀ {x}{y} → ∣ kercon (πhom θ) ∣ x y →  ∣ θ ∣ x y
   ker-in-con = id
