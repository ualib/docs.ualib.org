.. FILE      : Base/Homomorphisms/Kernels.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 08 Sep 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-homomorphisms-kernels-of-homomorphisms:

Kernels of Homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Base.Homomorphisms.Kernels`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( Signature; 𝓞 ; 𝓥 )

  module Base.Homomorphisms.Kernels {𝑆 : Signature 𝓞 𝓥} where

  -- Imports from Agda and the Agda Standard Library --------------------------------
  open import Data.Product   using ( _,_ )
  open import Function.Base  using ( _∘_ )
  open import Level          using ( Level ; _⊔_ ; suc )

  open  import Relation.Binary.PropositionalEquality
        using ( _≡_ ; module ≡-Reasoning ; refl )

  -- Imports from the Agda Universal Algebras Library --------------------------------
  open import Overture        using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
  open import Base.Functions  using ( Image_∋_ ; IsSurjective )
  open import Base.Equality   using ( swelldef )
  open import Base.Relations  using ( ker ; ker-IsEquivalence ; ⟪_⟫ ; mkblk )

  open  import Base.Algebras {𝑆 = 𝑆}
        using ( Algebra ; compatible ; _̂_ ; Con ; mkcon ; _╱_ ; IsCongruence ; /-≡ )

  open import Base.Homomorphisms.Basic {𝑆 = 𝑆}  using ( hom ; epi ; epi→hom )

  private variable α β : Level

.. _base-homomorphisms-definition:

Definition
^^^^^^^^^^

The kernel of a homomorphism is a congruence relation and conversely for every
congruence relation θ, there exists a homomorphism with kernel θ (namely, that
canonical projection onto the quotient modulo θ). 

::

  module _ {𝑨 : Algebra α} where
   open ≡-Reasoning
   homker-comp :  swelldef 𝓥 β → {𝑩 : Algebra β}(h : hom 𝑨 𝑩)
    →             compatible 𝑨 (ker ∣ h ∣)

   homker-comp wd {𝑩} h f {u}{v} kuv =
    ∣ h ∣((f ̂ 𝑨) u)    ≡⟨ ∥ h ∥ f u ⟩
    (f ̂ 𝑩)(∣ h ∣ ∘ u)  ≡⟨ wd(f ̂ 𝑩)(∣ h ∣ ∘ u)(∣ h ∣ ∘ v)kuv ⟩
    (f ̂ 𝑩)(∣ h ∣ ∘ v)  ≡⟨ (∥ h ∥ f v)⁻¹ ⟩
    ∣ h ∣((f ̂ 𝑨) v)    ∎



(Notice, it is here that the ``swelldef`` postulate comes into play, and because
it is needed to prove ``homker-comp``, it is postulated by all the lemmas below
that depend upon ``homker-comp``.)

It is convenient to define a function that takes a homomorphism and constructs a
congruence from its kernel. We call this function ``kercon``.

::

   kercon : swelldef 𝓥 β → {𝑩 : Algebra β} → hom 𝑨 𝑩 → Con{α}{β} 𝑨
   kercon wd {𝑩} h = ker ∣ h ∣ , mkcon (ker-IsEquivalence ∣ h ∣)(homker-comp wd {𝑩} h)


With this congruence we construct the corresponding quotient, along with some
syntactic sugar to denote it.

::

   kerquo : swelldef 𝓥 β → {𝑩 : Algebra β} → hom 𝑨 𝑩 → Algebra (α ⊔ suc β)
   kerquo wd {𝑩} h = 𝑨 ╱ (kercon wd {𝑩} h)

::

  ker[_⇒_]_↾_ :  (𝑨 : Algebra α)(𝑩 : Algebra β) → hom 𝑨 𝑩 → swelldef 𝓥 β
   →             Algebra (α ⊔ suc β)

  ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd = kerquo wd {𝑩} h
  
Thus, given ``h : hom 𝑨 𝑩``, we can construct the quotient of ``𝑨`` modulo the
kernel of ``h``, and the syntax for this quotient in the agda-algebras_ library
is ``𝑨 [ 𝑩 ]/ker h ↾ fe``.

.. _base-homomorphisms-the-canonical-projection:

The canonical projection
^^^^^^^^^^^^^^^^^^^^^^^^

Given an algebra ``𝑨`` and a congruence ``θ``, the *canonical projection* is a
map from ``𝑨`` onto ``𝑨 ╱ θ`` that is constructed, and proved epimorphic, as
follows.

::

  module _ {α β : Level}{𝑨 : Algebra α} where
   πepi : (θ : Con{α}{β} 𝑨) → epi 𝑨 (𝑨 ╱ θ)
   πepi θ = (λ a → ⟪ a ⟫) , (λ _ _ → refl) , cπ-is-epic  where
    cπ-is-epic : IsSurjective (λ a → ⟪ a ⟫)
    cπ-is-epic (C , mkblk a refl ) =  Image_∋_.eq a refl

In may happen that we don’t care about the surjectivity of ``πepi``, in which
case would might prefer to work with the *homomorphic reduct* of ``πepi``. This
is obtained by applying ``epi-to-hom``, like so. 

::

   πhom : (θ : Con{α}{β} 𝑨) → hom 𝑨 (𝑨 ╱ θ)
   πhom θ = epi→hom (𝑨 ╱ θ) (πepi θ)

We combine the foregoing to define a function that takes 𝑆-algebras ``𝑨`` and
``𝑩``, and a homomorphism ``h : hom 𝑨 𝑩`` and returns the canonical epimorphism
from ``𝑨`` onto ``𝑨 [ 𝑩 ]/ker h``. (Recall, the latter is the special notation
we defined above for the quotient of ``𝑨`` modulo the kernel of ``h``.)

::

   πker :  (wd : swelldef 𝓥 β){𝑩 : Algebra β}(h : hom 𝑨 𝑩)
    →      epi 𝑨 (ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd)

   πker wd {𝑩} h = πepi (kercon wd {𝑩} h)

The kernel of the canonical projection of ``𝑨`` onto ``𝑨 / θ`` is equal to
``θ``, but since equality of inhabitants of certain types (like ``Congruence``
or ``Rel``) can be a tricky business, we settle for proving the containment ``𝑨
/ θ ⊆ θ``. Of the two containments, this is the easier one to prove; luckily it
is also the one we need later.

::

   open IsCongruence

   ker-in-con :  {wd : swelldef 𝓥 (α ⊔ suc β)}(θ : Con 𝑨)
    →            ∀ {x}{y} → ∣ kercon wd {𝑨 ╱ θ} (πhom θ) ∣ x y →  ∣ θ ∣ x y

   ker-in-con θ hyp = /-≡ θ hyp
