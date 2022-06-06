.. FILE      : Base/Homomorphism/Basic.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 03 Jun 2022
.. UPDATED   : 03 Jun 2022
.. COPYRIGHT : (c) 2022 William DeMeo

.. _basic-definitions:

Basic Definitions
~~~~~~~~~~~~~~~~~

This is the `Base.Homomorphisms.Basic`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Base.Algebras.Basic

  module Base.Homomorphisms.Basic {𝑆 : Signature 𝓞 𝓥} where

  -- Imports from Agda and the Agda Standard Library --------------------------------
  open import Agda.Primitive using ( _⊔_ ; lsuc ) renaming ( Set to Type )
  open import Data.Product   using ( _,_ ; Σ ;  _×_ ; Σ-syntax) renaming ( proj₁ to fst )
  open import Function.Base  using ( _∘_ ; id )
  open import Level          using ( Level )
  open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

  -- Imports from the Agda Universal Algebras Library --------------------------------
  open import Base.Overture.Preliminaries using ( ∣_∣ ; ∥_∥ )
  open import Base.Overture.Injective     using ( IsInjective )
  open import Base.Overture.Surjective    using ( IsSurjective )

  private variable α β : Level


.. _homomorphisms:

Homomorphisms
^^^^^^^^^^^^^

If ``𝑨`` and ``𝑩`` are ``𝑆``-algebras, then a *homomorphism* from ``𝑨`` to ``𝑩`` is a
function ``h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣`` from the domain of ``𝑨`` to the domain of ``𝑩``
that is *compatible* (or *commutes*) with all of the basic operations of the
signature; that is, for all operation symbols ``𝑓 : ∣ 𝑆 ∣`` and tuples 
``a : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣`` of ``𝑨``, the following holds:
``h ((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑩) (h ∘ a)``.

**Remarks**. Recall, ``h ∘ 𝒂`` is the tuple whose i-th component is ``h (𝒂 i)``.
Instead of "homomorphism," we sometimes use the nickname "hom" to refer to such a map.

To formalize this concept, we first define a type representing the assertion
that a function ``h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣`` commutes with a single basic operation
``𝑓``. With Agda's extremely flexible syntax the defining equation above can be
expressed unadulterated. 

::

  module _ (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) where

   compatible-op-map : ∣ 𝑆 ∣ → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type(α ⊔ 𝓥 ⊔ β)
   compatible-op-map 𝑓 h = ∀ 𝑎 → h ((𝑓 ̂ 𝑨) 𝑎) ≡ (𝑓 ̂ 𝑩) (h ∘ 𝑎)

Agda infers from the shorthand ``∀ 𝑎`` that ``𝑎`` has type ``∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣``
since it must be a tuple on ``∣ 𝑨 ∣`` of "length" ``∥ 𝑆 ∥ 𝑓`` (the arity of
``𝑓``).

We now define the type ``hom 𝑨 𝑩`` of homomorphisms from ``𝑨`` to ``𝑩`` by first
defining the type ``is-homomorphism`` which represents the property of being a
homomorphism.

::

   is-homomorphism : (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
   is-homomorphism g = ∀ 𝑓  →  compatible-op-map 𝑓 g

   hom : Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
   hom = Σ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) is-homomorphism

.. _important-examples-of-homomorphisms:

Important examples of homomorphisms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Let's look at a few important examples of homomorphisms. These examples
are actually quite special in that every algebra has such a
homomorphism.

We begin with the identity map, which is proved to be (the underlying
map of) a homomorphism as follows.

::

  𝒾𝒹 : (𝑨 : Algebra α 𝑆) → hom 𝑨 𝑨
  𝒾𝒹 _ = id , λ 𝑓 𝑎 → refl

Next, the lifting of an algebra to a higher universe level is, in fact, a
homomorphism. Dually, the lowering of a lifted algebra to its original universe
level is a homomorphism.

::

  open Level

  𝓁𝒾𝒻𝓉 : {β : Level}(𝑨 : Algebra α 𝑆) → hom 𝑨 (Lift-Alg 𝑨 β)
  𝓁𝒾𝒻𝓉 _ = lift , λ 𝑓 𝑎 → refl

  𝓁ℴ𝓌ℯ𝓇 : {β : Level}(𝑨 : Algebra α 𝑆) → hom (Lift-Alg 𝑨 β) 𝑨
  𝓁ℴ𝓌ℯ𝓇 _ = lower , λ 𝑓 𝑎 → refl


.. _monomorphisms-and-epimorphisms:

Monomorphisms and epimorphisms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A *monomorphism* is an injective homomorphism and an *epimorphism* is a
surjective homomorphism. These are represented in the agda-algebras_ library by
the following types.

::

  is-monomorphism : (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type _
  is-monomorphism 𝑨 𝑩 g = is-homomorphism 𝑨 𝑩 g × IsInjective g

  mon : Algebra α 𝑆 → Algebra β 𝑆  → Type _
  mon 𝑨 𝑩 = Σ[ g ∈ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-monomorphism 𝑨 𝑩 g

  is-epimorphism : (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → Type _
  is-epimorphism 𝑨 𝑩 g = is-homomorphism 𝑨 𝑩 g × IsSurjective g

  epi : Algebra α 𝑆 → Algebra β 𝑆  → Type _
  epi 𝑨 𝑩 = Σ[ g ∈ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ] is-epimorphism 𝑨 𝑩 g

(Evidently, Agda_ is able to infer the return type of each of the last four
definitions, so we can use ``Type _`` instead of ``Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)``.)

It will be convenient to have a function that takes an inhabitant of ``mon`` (or
``epi``) and extracts the homomorphism part, or *hom reduct* (that is, the pair
consisting of the map and a proof that the map is a homomorphism).

::

  mon→hom : (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆} → mon 𝑨 𝑩 → hom 𝑨 𝑩
  mon→hom 𝑨 ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

  epi→hom : {𝑨 : Algebra α 𝑆}(𝑩 : Algebra β 𝑆) → epi 𝑨 𝑩 → hom 𝑨 𝑩
  epi→hom _ ϕ = ∣ ϕ ∣ , fst ∥ ϕ ∥

