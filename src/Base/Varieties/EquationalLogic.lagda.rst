.. FILE      : Base/Varieties.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 03 Jun 2022
.. UPDATED   : 03 Jun 2022
.. COPYRIGHT : (c) 2022 William DeMeo

.. _equational-logic:

Equational Logic
~~~~~~~~~~~~~~~~

This is the `Base.Varieties.EquationalLogic`_ module of the
`Agda Universal Algebra Library`_ where the binary "models" relation ``⊧``,
relating algebras (or classes of algebras) to the identities that they
satisfy, is defined.

Let ``𝑆`` be a signature. By an *identity* or *equation* in ``𝑆`` we mean an
ordered pair of terms, written ``p ≈ q``, from the term algebra ``𝑻 X``. If ``𝑨``
is an ``𝑆``-algebra we say that 𝑨 *satisfies* 𝑝 ≈ 𝑞 provided 𝑝 ̇ 𝑨 ≡ 𝑞 ̇ 𝑨 holds.
In this situation, we write 𝑨 ⊧ 𝑝 ≈ 𝑞 and say that 𝑨 *models* the
identity 𝑝 ≈ q. If 𝒦 is a class of algebras, all of the same signature,
we write 𝒦 ⊧ p ≈ q if, for every 𝑨 ∈ 𝒦, 𝑨 ⊧ 𝑝 ≈ 𝑞.

Because a class of structures has a different type than a single structure, we must use a slightly different syntax to avoid overloading the relations ``⊧`` and ``≈``. As a reasonable alternative to what we would normally express informally as ``𝒦 ⊧ p ≈ q``, we have settled on ``𝒦 ⊫ p ≈ q`` to denote this relation.  To reiterate, if ``𝒦`` is a class of ``𝑆``-algebras, we write ``𝒦 ⊫ p ≈ q`` iff every ``𝑨 ∈ 𝒦`` satisfies ``𝑨 ⊧ p ≈ q``.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

  module Base.Varieties.EquationalLogic {𝑆 : Signature 𝓞 𝓥} where

  -- Imports from Agda and the Agda Standard Library ----------------
  open import Agda.Primitive  using ( _⊔_ ;  lsuc ; Level )  renaming ( Set to Type )
  open import Data.Product    using ( _×_ ; _,_ ; Σ-syntax)  renaming ( proj₁ to fst ; proj₂ to snd )
  open import Relation.Unary  using ( Pred ; _∈_ )

  -- Imports from the Agda Universal Algebra Library ----------------
  open import Base.Overture.Preliminaries      using ( _≈_ )
  open import Base.Algebras.Basic              using ( Algebra )
  open import Base.Algebras.Products  {𝑆 = 𝑆}  using ( ov )
  open import Base.Terms.Basic        {𝑆 = 𝑆}  using ( Term ; 𝑻 )
  open import Base.Terms.Operations   {𝑆 = 𝑆}  using ( _⟦_⟧ )
  private variable
   χ α ρ ι : Level
   X : Type χ

.. _the-models-relation:

The models relation
^^^^^^^^^^^^^^^^^^^

We define the binary "models" relation ``⊧`` using infix syntax so that we may
write, e.g., ``𝑨 ⊧ p ≈ q`` or ``𝒦 ⊫ p ≈ q``, relating algebras (or classes of
algebras) to the identities that they satisfy. We also prove a couple of useful
facts about ``⊧``.

::

  _⊧_≈_ : Algebra α 𝑆 → Term X → Term X → Type _
  𝑨 ⊧ p ≈ q = 𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧

  _⊫_≈_ : Pred(Algebra α 𝑆) ρ → Term X → Term X → Type _
  𝒦 ⊫ p ≈ q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

**Unicode tip**. Type ``\models`` to get ``⊧`` ; type ``\||=`` to get ``⊫``.

The expression ``𝑨 ⊧ p ≈ q`` represents the assertion that the identity ``p ≈ q``
holds when interpreted in the algebra ``𝑨``; syntactically, ``𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧``.

The expression ``𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧`` denotes *extensional equality*; that is, for
each “environment” ``η :  X → ∣ 𝑨 ∣`` (assigning values in the domain of ``𝑨`` to
the variable symbols in ``X``) the (intensional) equality ``𝑨 ⟦ p ⟧ η ≡ 𝑨 ⟦ q ⟧ η``
holds.

.. _equational-theories-and-models:

Equational theories and models
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If ``𝒦`` denotes a class of structures, then ``Th 𝒦`` represents the set of
identities modeled by the members of ``𝒦``.

::

  Th : Pred (Algebra α 𝑆) (ov α) → Pred(Term X × Term X) _
  Th 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q

We represent ``Th 𝒦`` as an indexed collection of algebras by taking ``Th 𝒦``,
itself, to be the index set.

::

  module _ {X : Type χ}{𝒦 : Pred (Algebra α 𝑆) (ov α)} where

   ℐ : Type (ov(α ⊔ χ))
   ℐ = Σ[ (p , q) ∈ (Term X × Term X) ] 𝒦 ⊫ p ≈ q

   ℰ : ℐ → Term X × Term X
   ℰ ((p , q) , _) = (p , q)

If ``ℰ`` denotes a set of identities, then ``Mod ℰ`` is the class of
structures satisfying the identities in ``ℰ``.

::

  Mod : Pred(Term X × Term X) (ov α) → Pred(Algebra α 𝑆) _
  Mod ℰ = λ 𝑨 → ∀ p q → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q
  -- (tupled version)
  Modᵗ : {I : Type ι} → (I → Term X × Term X) → {α : Level} → Pred(Algebra α 𝑆) _
  Modᵗ ℰ = λ 𝑨 → ∀ i → 𝑨 ⊧ (fst (ℰ i)) ≈ (snd (ℰ i))

--------------


