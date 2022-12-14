.. FILE      : Base/Relations/Discrete.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 02 Jun 2022
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-relations-discrete-relations:

Discrete Relations
~~~~~~~~~~~~~~~~~~

This is the `Base.Relations.Discrete`_ module of the agda-algebras_ library.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Relations.Discrete where

  -- Imports from Agda and the Agda Standard Library ----------------------------------------------
  open import Agda.Primitive               using ( _⊔_ ; lsuc ) renaming ( Set to Type )
  open import Data.Product                 using ( _,_ ; _×_ )
  open import Function.Base                using ( _∘_ )
  open import Level                        using ( Level ; Lift )
  open import Relation.Binary              using ( IsEquivalence ; _⇒_ ; _=[_]⇒_ )
                                        renaming ( REL to BinREL ; Rel to BinRel )
  open import Relation.Binary.Definitions  using ( Reflexive ; Transitive )
  open import Relation.Unary               using ( _∈_; Pred )
  open import Relation.Binary.PropositionalEquality using ( _≡_ )

  -- Imports from agda-algebras -------------------------------------------------------------------
  open import Overture using (_≈_ ; Π-syntax)

  private variable α β ρ 𝓥 : Level

Here is a function that is useful for defining poitwise equality of
functions wrt a given equality (see, e.g., the definition of ``_≈̇_`` in
the `Base.Adjunction.Residuation`_ module).

::

  PointWise :  {A : Type α}{B : Type β }
               (_≋_ : BinRel B ρ) → BinRel (A → B) _
  PointWise {A = A}{B} _≋_ = λ (f g : A → B) → ∀ x → f x ≋ g x

  depPointWise :  {A : Type α}{B : A → Type β }
                  (_≋_ : {γ : Level}{C : Type γ} → BinRel C ρ)
   →              BinRel ((a : A) → B a) _
  depPointWise {A = A}{B} _≋_ = λ (f g : (a : A) → B a) → ∀ x → f x ≋ g x


Here is useful notation for asserting that the image of a function (the first argument)
is contained in a predicate, the second argument (a "subset" of the codomain).

::

  Im_⊆_ : {A : Type α}{B : Type β} → (A → B) → Pred B ρ → Type (α ⊔ ρ)
  Im f ⊆ S = ∀ x → f x ∈ S


.. _base-relations-operation-symbols-unary-relations-binary-relations:

Operation symbols, unary relations, binary relations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The unary relation (or “predicate”) type is imported from Relation.Unary
of the std lib.

.. code:: agda

   Pred : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
   Pred A ℓ = A → Set ℓ

Sometimes it is useful to obtain the underlying type of a predicate.

::

  PredType : {A : Type α} → Pred A ρ → Type α
  PredType {A = A} _ = A

The binary relation types are called ``Rel`` and ``REL`` in the standard
library, but we will call them ``BinRel`` and ``BinREL`` and reserve the
names ``Rel`` and ``REL`` for the more general types of relations we
define below and in the Base.Relations.Continuous module.

The heterogeneous binary relation type is imported from the standard
library and renamed ``BinREL``.

.. code:: agda

   BinREL : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
   BinREL A B ℓ' = A → B → Type ℓ'

The homogeneous binary relation type is imported from the standard
library and renamed BinRel.

.. code:: agda

   BinRel : ∀{ℓ} → Type ℓ → (ℓ' : Level) → Type (ℓ ⊔ lsuc ℓ')
   BinRel A ℓ' = REL A A ℓ'

::

  Level-of-Rel : {A : Type α}{ℓ : Level} → BinRel A ℓ → Level
  Level-of-Rel {A = A}{ℓ} _ = ℓ


.. _base-relations-kernels:

Kernels
^^^^^^^

The *kernel* of ``f : A → B`` is defined informally by
``{(x , y) ∈ A × A : f x = f y}``. This can be represented in type
theory and Agda in a number of ways, each of which may be useful in a
particular context. For example, we could define the kernel to be an
inhabitant of a (binary) relation type, or a (unary) predicate type.

::

  module _ {A : Type α}{B : Type β} where

   ker : (A → B) → BinRel A β
   ker g x y = g x ≡ g y

   kerRel : {ρ : Level} → BinRel B ρ → (A → B) → BinRel A ρ
   kerRel _≈_ g x y = g x ≈ g y

   kernelRel : {ρ : Level} → BinRel B ρ → (A → B) → Pred (A × A) ρ
   kernelRel _≈_ g (x , y) = g x ≈ g y

   open IsEquivalence

   kerRelOfEquiv : {ρ : Level}{R : BinRel B ρ} → IsEquivalence R → (h : A → B) → IsEquivalence (kerRel R h)
   kerRelOfEquiv eqR h = record { refl = refl eqR ; sym = sym eqR ; trans = trans eqR }

   kerlift : (A → B) → (ρ : Level) → BinRel A (β ⊔ ρ)
   kerlift g ρ x y = Lift ρ (g x ≡ g y)

   ker' : (A → B) → (I : Type 𝓥) → BinRel (I → A) (β ⊔ 𝓥)
   ker' g I x y = g ∘ x ≡ g ∘ y

   kernel : (A → B) → Pred (A × A) β
   kernel g (x , y) = g x ≡ g y


  -- The *identity relation* (equivalently, the kernel of a 1-to-1 function)
  0[_] : (A : Type α) → {ρ : Level} → BinRel A (α ⊔ ρ)
  0[ A ] {ρ} = λ x y → Lift ρ (x ≡ y)

  module _ {A : Type (α ⊔ ρ)} where

   -- Subset containment relation for binary realtions
   _⊑_ : BinRel A ρ → BinRel A ρ → Type (α ⊔ ρ)
   P ⊑ Q = ∀ x y → P x y → Q x y

   ⊑-refl : Reflexive _⊑_
   ⊑-refl = λ _ _ z → z

   ⊑-trans : Transitive _⊑_
   ⊑-trans P⊑Q Q⊑R x y Pxy = Q⊑R x y (P⊑Q x y Pxy)



.. _base-relations-operation-type-and-compatibility:

Operation type and compatibility
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Notation**. For consistency and readability, we reserve two universe
variables for special purposes. The first of these is 𝓞 which shall be
reserved for types that represent *operation symbols*. The second is 𝓥
which we reserve for types representing *arities* of relations or
operations.

In the next subsection, we define types that are useful for asserting
and proving facts about *compatibility* of *operations* with relations,
but first we need a general type with which to represent operations.
Here is the definition, which we justify below.

The type ``Op`` encodes the arity of an operation as an arbitrary type
``I : Type 𝓥``, which gives us a very general way to represent an
operation as a function type with domain ``I → A`` (the type of
“tuples”) and codomain ``A``. For example, the ``I``-*ary projection
operations* on ``A`` are represented as inhabitants of the type
``Op I A`` as follows.

::
  -- The type of operations on A of arity I
  Op : Type α → Type 𝓥 → Type (α ⊔ 𝓥)
  Op A I = (I → A) → A

  -- Example (projections)
  π : {I : Type 𝓥} {A : Type α } → I → Op A I
  π i x = x i

  -- return the arity of a given operation symbol
  arity[_] : {I : Type 𝓥} {A : Type α } → Op A I → Type 𝓥
  arity[_] {I = I} f = I

  -- lift a binary relation to the corresponding `I`-ary relation.
  eval-rel : {A : Type α}{I : Type 𝓥} → BinRel A ρ → BinRel (I → A) (𝓥 ⊔ ρ)
  eval-rel R u v = ∀ i → R (u i) (v i)

  eval-pred : {A : Type α}{I : Type 𝓥} → Pred (A × A) ρ → BinRel (I → A) (𝓥 ⊔ ρ)
  eval-pred P u v = ∀ i → (u i , v i) ∈ P


If ``f : Op I`` and ``R : Rel A β``, then we say ``f`` and ``R`` are
*compatible* just in case ``∀ u v : I → A``,
``Π i ꞉ I , R (u i) (v i)  →  R (f u) (f v)``.

::

  _preserves_ : {A : Type α}{I : Type 𝓥} → Op A I → BinRel A ρ → Type (α ⊔ 𝓥 ⊔ ρ)
  f preserves R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)

  --shorthand notation for preserves
  _|:_ : {A : Type α}{I : Type 𝓥} → Op A I → BinRel A ρ → Type (α ⊔ 𝓥 ⊔ ρ)
  f |: R  = (eval-rel R) =[ f ]⇒ R

  -- predicate version of the compatibility relation
  _preserves-pred_ : {A : Type α}{I : Type 𝓥} → Op A I → Pred ( A × A ) ρ → Type (α ⊔ 𝓥 ⊔ ρ)
  f preserves-pred P  = ∀ u v → (eval-pred P) u v → (f u , f v) ∈ P

  _|:pred_ : {A : Type α}{I : Type 𝓥} → Op A I → Pred (A × A) ρ → Type (α ⊔ 𝓥 ⊔ ρ)
  f |:pred P  = (eval-pred P) =[ f ]⇒ λ x y → (x , y) ∈ P


  -- The two types just defined are logically equivalent.
  module _ {A : Type α}{I : Type 𝓥}{f : Op A I}{R : BinRel A ρ} where
   compatibility-agreement : f preserves R → f |: R
   compatibility-agreement c {x}{y} Rxy = c x y Rxy
   compatibility-agreement' : f |: R → f preserves R
   compatibility-agreement' c = λ u v x → c x


