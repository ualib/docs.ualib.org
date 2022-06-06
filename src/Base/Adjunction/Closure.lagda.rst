.. FILE      : Base/Adjunction/Closure.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 30 Aug 2021
.. UPDATED   : 02 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette and William DeMeo

.. _closure-systems-and-operators:

Closure Systems and Operators
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Base.Adjunction.Closure`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Adjunction.Closure where

  -- Imports from Agda and the Agda Standard Library  ---------------------------------------
  open import Agda.Primitive           using ( _⊔_ ; lsuc ) renaming ( Set to Type )
  open import Data.Product             using ( Σ-syntax ; _,_ ; _×_ )
  open import Function.Bundles         using ( _↔_ ; Inverse )
  open import Level                    using ( Level ; Lift ) renaming ( zero to ℓ₀ )
  open import Relation.Binary.Bundles  using ( Poset )
  open import Relation.Binary.Core     using ( Rel ; _Preserves_⟶_ )
  open import Relation.Unary           using ( Pred ; _∈_ ; ⋂ )

  import Relation.Binary.Reasoning.PartialOrder as ≤-Reasoning
  import Algebra.Definitions as ALG

  private variable
   α ρ ℓ ℓ₁ ℓ₂ : Level
   a : Type α


.. _closure-systems:

Closure Systems
^^^^^^^^^^^^^^^

A *closure system* on a set ``X`` is a collection ``𝒞`` of subsets of ``X`` that
is closed under arbitrary intersection (including the empty intersection, so
``⋂ ∅ = X ∈ 𝒞``. Thus a closure system is a complete meet semilattice with respect
to the subset inclusion ordering.

Since every complete meet semilattice is automatically a complete lattice, the
closed sets of a closure system form a complete lattice. (See J.B. Nation's
`Lattice Theory Notes <http://math.hawaii.edu/~jb/math618/Nation-LatticeTheory.pdf>`__,
Theorem 2.5.)

Some examples of closure systems are the following:

-  order ideals of an ordered set
-  subalgebras of an algebra
-  equivalence relations on a set
-  congruence relations of an algebra

::

  Extensive : Rel a ρ → (a → a) → Type _
  Extensive _≤_ C = ∀{x} → x ≤ C x
  -- (We might propose a new stdlib equivalent to Extensive in, e.g., `Relation.Binary.Core`.)

  module _ {χ ρ ℓ : Level}{X : Type χ} where

   IntersectClosed : Pred (Pred X ℓ) ρ → Type _
   IntersectClosed C = ∀ {I : Type ℓ}{c : I → Pred X ℓ} → (∀ i → (c i) ∈ C) → ⋂ I c ∈ C

   ClosureSystem : Type _
   ClosureSystem = Σ[ C ∈ Pred (Pred X ℓ) ρ ] IntersectClosed C

.. _closure-operators:

Closure Operators
^^^^^^^^^^^^^^^^^

Let ``𝑷 = (P, ≤)`` be a poset. An function ``C : P → P`` is called a *closure
operator* on ``𝑷`` if it is

1. (extensive) ``∀ x → x ≤ C x``
2. (order preserving) ``∀ x y → x ≤ y → C x ≤ C y``
3. (idempotent) ``∀ x → C (C x) = C x``

Thus, a closure operator is an extensive, idempotent poset endomorphism.

::

  record ClOp {ℓ ℓ₁ ℓ₂ : Level}(𝑨 : Poset ℓ ℓ₁ ℓ₂) : Type  (ℓ ⊔ ℓ₂ ⊔ ℓ₁) where
   open Poset 𝑨 ; private A = Carrier
   open ALG (_≈_) using ( IdempotentFun )

   field
    C : A → A
    isExtensive        : Extensive _≤_ C
    isOrderPreserving  : C Preserves _≤_ ⟶ _≤_
    isIdempotent       : IdempotentFun C

.. _basic-properties-of-closure-operators:

Basic properties of closure operators
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  open ClOp
  open Inverse

  module _ {𝑨 : Poset ℓ ℓ₁ ℓ₂}(𝑪 : ClOp 𝑨) where
   open Poset 𝑨
   open ≤-Reasoning 𝑨

   private
    c = C 𝑪
    A = Carrier

**Theorem 1**. If ``𝑨 = (A , ≦)`` is a poset and ``c`` is a closure operator on
``A``, then ``∀ (x y : A) → (x ≦ (c y) ↔ (c x) ≦ (c y))``

::

   clop→law⇒ : (x y : A) → x ≤ (c y) → (c x) ≤ (c y)
   clop→law⇒ x y x≤cy = begin
     c x      ≤⟨ isOrderPreserving 𝑪 x≤cy ⟩
     c (c y)  ≈⟨ isIdempotent 𝑪 y ⟩
     c y      ∎

   clop→law⇐ : (x y : A) → (c x) ≤ (c y) → x ≤ (c y)

   clop→law⇐ x y cx≤cy = begin  x  ≤⟨ isExtensive 𝑪 ⟩  c x  ≤⟨ cx≤cy ⟩  c y  ∎

The converse of Theorem 1 also holds. That is,

**Theorem 2**. If ``𝑨 = (A , ≤)`` is a poset and ``c : A → A`` satisfies
``∀ (x y : A) → (x ≤ (c y) ↔ (c x) ≤ (c y))`` then `c` is a closure operator on `A`.

::

  module _ {𝑨 : Poset ℓ ℓ₁ ℓ₂} where
   open Poset 𝑨
   private
    A = Carrier

   open ALG (_≈_) using ( IdempotentFun )

   clop←law : (c : A → A) → ((x y : A) → (x ≤ (c y) ↔ (c x) ≤ (c y)))
    →         Extensive _≤_ c × c Preserves _≤_ ⟶ _≤_ × IdempotentFun c

   clop←law c hyp  = e , (o , i)
    where
    h1 : ∀ {x y} → x ≤ (c y) → c x ≤ c y
    h1 {x}{y} = f (hyp x y)

    h2 : ∀ {x y} → c x ≤ c y → x ≤ (c y)
    h2 {x}{y} = f⁻¹ (hyp x y)

    e : Extensive _≤_ c
    e = h2 refl

    o : c Preserves _≤_ ⟶ _≤_
    o u = h1 (trans u e)

    i : IdempotentFun c
    i x = antisym (h1 refl) (h2 refl)


