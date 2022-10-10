.. FILE      : Base/Equality/Truncation.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 23 Feb 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-equality-truncation:

Truncation
~~~~~~~~~~

This is the `Base.Equality.Truncation`_ module of the `Agda Universal Algebra Library`_.

We start with a brief discussion of standard notions of *truncation*, *h-sets*
(which we just call *sets*), and the *uniqueness of identity types* principle.
We then prove that a monic function into a *set* is an embedding. The section
concludes with a *uniqueness of identity proofs* principle for blocks of
equivalence relations.

Readers who want to learn more about "proof-relevant mathematics" and other
concepts mentioned in this module may wish to consult other sources, such as
`Section 34 <https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation>`__
and
`35 <https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#resizing>`__
of `Martín Escardó's notes`_, or
`Guillaume Brunerie, Truncations and truncated higher inductive
types <https://homotopytypetheory.org/2012/09/16/truncations-and-truncated-higher-inductive-types/>`__,
or Section 7.1 of the `HoTT book`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Equality.Truncation where

  -- Imports from Agda and the Agda Standard Library  -------------------------------------
  open import Agda.Primitive   renaming ( Set to Type )                  using ()
  open import Data.Product     renaming ( proj₁ to fst ; proj₂ to snd )  using ( _,_ ; Σ ; Σ-syntax ; _×_ )
  open import Function                                                   using ( _∘_ ; id )
  open import Level                                                      using ( _⊔_ ; suc ; Level )
  open import Relation.Binary  renaming ( Rel to BinRel )                using ( IsEquivalence )
  open import Relation.Binary.PropositionalEquality as ≡                 using ( _≡_ ; module ≡-Reasoning )
  open import Relation.Unary                                             using ( Pred ; _⊆_ )

  -- Imports from the Agda Universal Algebra Library --------------------------------------
  open import Overture         using ( _⁻¹ ; transport ; ∥_∥ ; _≈_ ; ∣_∣ )
  open import Base.Functions    using ( IsInjective )
  open import Base.Relations   using ( IsBlock ; Rel ; REL )

  private variable α β ρ 𝓥 : Level

The MGS-Quotient module of the `Type Topology`_ library defines a *uniqueness-of-proofs*
principle for binary relations. We borrow this and related definitions.

First, a type is a *singleton* if it has exactly one inhabitant and a *subsingleton* if
it has *at most* one inhabitant. Representing these concepts are the following types
(whose original definitions we import from the ``MGS-Basic-UF`` module of `Type Topology`_).

::

  is-center : (A : Type α ) → A → Type α
  is-center A c = (x : A) → c ≡ x

  is-singleton : Type α → Type α
  is-singleton A = Σ A (is-center A)

  is-prop : Type α → Type α
  is-prop A = (x y : A) → x ≡ y

  is-prop-valued : {A : Type α} → BinRel A ρ → Type(α ⊔ ρ)
  is-prop-valued  _≈_ = ∀ x y → is-prop (x ≈ y)

  open ≡-Reasoning
  singleton-is-prop : {α : Level}(X : Type α) → is-singleton X → is-prop X
  singleton-is-prop X (c , φ) x y = x ≡⟨ (φ x)⁻¹ ⟩ c ≡⟨ φ y ⟩ y ∎

The concept of a `fiber <https://ncatlab.org/nlab/show/fiber>`__ of a function is,
in the `Type Topology`_ library, defined as a Sigma type whose inhabitants
represent inverse images of points in the codomain of the given function.

::

  fiber : {A : Type α } {B : Type β } (f : A → B) → B → Type (α ⊔ β)
  fiber {α}{β}{A} f y = Σ[ x ∈ A ] f x ≡ y

  -- A function is called an *equivalence* if all of its fibers are singletons.
  is-equiv : {A : Type α } {B : Type β } → (A → B) → Type (α ⊔ β)
  is-equiv f = ∀ y → is-singleton (fiber f y)

  -- An alternative means of postulating function extensionality.
  hfunext :  ∀ α β → Type (suc (α ⊔ β))
  hfunext α β = {A : Type α}{B : A → Type β} (f g : (x : A) → B x) → is-equiv (≡.cong-app{f = f}{g})

Thus, if ``R : Rel A β``, then ``is-subsingleton-valued R`` is the assertion that
for each pair ``x y : A`` there can be at most one proof that ``R x y`` holds.

.. _base-equality-uniqueness-of-identity-proofs:

Uniqueness of identity proofs
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This brief introduction is intended for novices; those already familiar with the
concept of *truncation* and *uniqueness of identity proofs* may want to skip to
the next subsection.

In general, we may have many inhabitants of a given type, hence (via Curry-Howard)
many proofs of a given proposition. For instance, suppose we have a type ``A``
and an identity relation ``_≡₀_`` on ``A`` so that, given two inhabitants of
``A``, say, ``a b : A``, we can form the type ``a ≡₀ b``. Suppose ``p`` and
``q`` inhabit the type ``a ≡₀ b``; that is, ``p`` and ``q`` are proofs of
``a ≡₀ b``, in which case we write ``p q : a ≡₀ b``. We might then wonder
whether and in what sense are the two proofs ``p`` and ``q`` the equivalent.

We are asking about an identity type on the identity type ``≡₀``, and whether
there is some inhabitant, say, ``r`` of this type; i.e., whether there is a
proof ``r : p ≡ₓ₁ q`` that the proofs of ``a ≡₀ b`` are the same. If such a
proof exists for all ``p q : a ≡₀ b``, then the proof of ``a ≡₀ b`` is unique;
as a property of the types ``A`` and ``≡₀``, this is sometimes called *uniqueness
of identity proofs* (uip).

Now, perhaps we have two proofs, say, ``r s : p ≡₁ q`` that the proofs ``p`` and
``q`` are equivalent. Then of course we wonder whether ``r ≡₂ s`` has a proof!
But at some level we may decide that the potential to distinguish two proofs of
an identity in a meaningful way (so-called *proof-relevance*) is not useful or
desirable. At that point, say, at level ``k``, we would be naturally inclined to
assume that there is at most one proof of any identity of the form ``p ≡ₖ q``.
This is called
`truncation <https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation>`__
(at level ``k``).

.. _base-equality-sets:

Sets
^^^^

In `homotopy type theory <https://homotopytypetheory.org>`__, a type ``A`` with
an identity relation ``≡₀`` is called a *set* (or *0-groupoid*) if for every
pair ``x y : A`` there is at most one proof of ``x ≡₀ y``. In other words, the
type ``A``, along with it's equality type ``≡₀``, form a *set* if for all
``x y : A`` there is at most one proof of ``x ≡₀ y``.

This notion is formalized in the `Type Topology`_ library, using the
``is-subsingleton`` type that we saw earlier (`Base.Functions.Inverses`_), as follows.

::

  is-set : Type α → Type α
  is-set A = is-prop-valued{A = A} _≡_

Thus, the pair ``(A , ≡₀)`` forms a set if and only if it satisfies
``∀ x y : A → is-subsingleton (x ≡₀ y)``.

We will also need the function
`to-Σ-≡ <https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sigmaequality>`__,
which is part of Escardó's characterization of *equality in Sigma types*.

::

  module _ {A : Type α}{B : A → Type β} where

   to-Σ-≡ : {σ τ : Σ[ x ∈ A ] B x} → (Σ[ p ∈ (fst σ ≡ fst τ) ] (transport B p ∥ σ ∥) ≡ ∥ τ ∥) → σ ≡ τ
   to-Σ-≡ (≡.refl , ≡.refl) = ≡.refl

.. _base-equality-embeddings:

Embeddings
^^^^^^^^^^

The ``is-embedding`` type is defined in the ``MGS-Embeddings`` module of the
`Type Topology`_ library in the following way.

::

  is-embedding : {A : Type α}{B : Type β} → (A → B) → Type (α ⊔ β)
  is-embedding f = ∀ b → is-prop (fiber f b)

  singleton-type : {A : Type α} → A → Type α
  singleton-type {α}{A} x = Σ[ y ∈ A ] y ≡ x

Thus, ``is-embedding f`` asserts that ``f`` is a function all of whose fibers are
subsingletons. Observe that an embedding is not simply an injective map. However,
if we assume that the codomain ``B`` has *unique identity proofs* (UIP), then we
can prove that a monic function into ``B`` is an embedding. We will do exactly that
in the `Base.Equality.Truncation`_ module when we take up the topic of *sets*
and the UIP.

Finding a proof that a function is an embedding isn’t always easy, but
one approach that is often fairly straightforward is to first prove that
the function is invertible and then invoke the
``invertible-is-embedding`` theorem from the `Type Topology`_ library.

::

  module _ {A : Type α}{B : Type β} where

   invertible : (A → B) → Type (α ⊔ β)
   invertible f = Σ[ g ∈ (B → A) ] ((g ∘ f ≈ id) × (f ∘ g ≈ id))

   equiv-is-embedding : (f : A → B) → is-equiv f → is-embedding f
   equiv-is-embedding f i y = singleton-is-prop (fiber f y) (i y)

We will use ``is-embedding``, ``is-set``, and ``to-Σ-≡`` in the next
subsection to prove that a monic function into a set is an embedding.

.. _base-equality-injective-functions-are-set-embeddings:

Injective functions are set embeddings
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Before moving on to define
`propositions <Base.Equality.Truncation.html#general-propositions>`__, we discharge
an obligation we mentioned but left unfulfilled in the
`embeddings <Base.Functions.Inverses.html#embeddings>`__ section of the
`Base.Functions.Inverses`_ module. Recall, we described and imported the
``is-embedding`` type, and we remarked that an embedding is not simply a monic
function. However, if we assume that the codomain is truncated so as to have
unique identity proofs (i.e., is a set), then we can prove that any monic
function into that codomain will be an embedding. On the other hand, embeddings
are always monic, so we will end up with an equivalence.

::

  private variable
   A : Type α
   B : Type β

  monic-is-embedding|Set : (f : A → B) → is-set B → IsInjective f → is-embedding f
  monic-is-embedding|Set f Bset fmon b (u , fu≡b) (v , fv≡b) = γ
   where
   fuv : f u ≡ f v
   fuv = ≡.trans fu≡b (fv≡b ⁻¹)

   uv : u ≡ v
   uv = fmon fuv

   arg1 : Σ[ p ∈ u ≡ v ] transport (λ a → f a ≡ b) p fu≡b ≡ fv≡b
   arg1 = uv , Bset (f v) b (transport (λ a → f a ≡ b) uv fu≡b) fv≡b

   γ : (u , fu≡b) ≡ (v , fv≡b)
   γ = to-Σ-≡ arg1

In stating the previous result, we introduce a new convention to which we will
try to adhere. If the antecedent of a theorem includes the assumption that one
of the types involved is a *set* (in the sense defined above), then we add to
the name of the theorem the suffix ``|Set``, which calls to mind the standard
mathematical notation for the restriction of a function.

.. _base-equality-equivalence-class-truncation:

Equivalence class truncation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Recall, ``IsBlock`` was defined in the `Base.Relations.Quotients`_ module as follows:

.. code:: agda

   IsBlock : {A : Type α}(C : Pred A β){R : Rel A β} → Type(α ⊔ lsuc β)
   IsBlock {A} C {R} = Σ u ꞉ A , C ≡ [ u ] {R}

In the next module we will define a *quotient extensionality* principle that will
require a form of unique identity proofs—specifically, we will assume that for
each predicate ``C : Pred A β`` there is at most one proof of ``IsBlock C``.
We call this proof-irrelevance principle "uniqueness of block identity proofs",
and define it as follows.

::

  blk-uip : (A : Type α)(R : BinRel A ρ ) → Type(α ⊔ suc ρ)
  blk-uip A R = ∀ (C : Pred A _) → is-prop (IsBlock C {R})

It might seem unreasonable to postulate that there is at most one inhabitant of
``IsBlock C``, since equivalence classes typically have multiple members, any
one of which could serve as a class representative. However, postulating
``blk-uip A R`` is tantamount to collapsing each ``R``-block to a single point,
and this is indeed the correct semantic interpretation of the elements of the
quotient ``A / R``.

.. _base-equality-general-propositions:

General propositions
^^^^^^^^^^^^^^^^^^^^

This section defines more general truncated predicates which we call *continuous
propositions* and *dependent propositions*. Recall, above (in the
`Base.Relations.Continuous`_ module) we defined types called ``Rel`` and ``REL``
to represent relations of arbitrary arity over arbitrary collections of sorts.

Naturally, we define the corresponding *truncated continuous relation type* and
*truncated dependent relation type*, the inhabitants of which we will call
*continuous propositions* and *dependent propositions*, respectively.

::

  module _ {I : Type 𝓥} where

   IsRelProp : {ρ : Level}(A : Type α) → Rel A I{ρ} → Type (𝓥 ⊔ α ⊔ ρ)
   IsRelProp B P = ∀ (b : (I → B)) → is-prop (P b)

   RelProp : Type α → (ρ : Level) → Type (𝓥 ⊔ α ⊔ suc ρ)
   RelProp A ρ = Σ[ P ∈ Rel A I{ρ} ] IsRelProp A P

   RelPropExt : Type α → (ρ : Level) → Type (𝓥 ⊔ α ⊔ suc ρ)
   RelPropExt A ρ = {P Q : RelProp A ρ } → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

   IsRELProp : {ρ : Level} (𝒜 : I → Type α) → REL I 𝒜 {ρ}  → Type (𝓥 ⊔ α ⊔ ρ)
   IsRELProp 𝒜 P = ∀ (a : ((i : I) → 𝒜 i)) → is-prop (P a)

   RELProp : (I → Type α) → (ρ : Level) → Type (𝓥 ⊔ α ⊔ suc ρ)
   RELProp 𝒜 ρ = Σ[ P ∈ REL I 𝒜 {ρ} ] IsRELProp 𝒜 P

   RELPropExt : (I → Type α) → (ρ : Level) → Type (𝓥 ⊔ α ⊔ suc ρ)
   RELPropExt 𝒜 ρ = {P Q : RELProp 𝒜 ρ} → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

