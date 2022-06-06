.. FILE      : Base/Categories/Functors.lagda.rst
.. DATE      : 30 Aug 2021
.. UPDATED   : 04 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette and William DeMeo

.. _functors:

Functors
~~~~~~~~

This is the `Base.Categories.Functors`_ module of the `Agda Universal Algebra Library`_.

Recall, a *functor* ``F`` is a function that maps the objects and morphisms of one
category ``𝒞`` to the objects and morphisms of a category ``𝒟`` in such a way that
the following *functor laws* are satisfied:

-  ``∀ f g, F(f ∘ g) = F(f) ∘ F(g)``
-  ``∀ A, F(id A) = id (F A)`` (where ``id X`` denotes the identity morphism on ``X``)

.. _polynomial-functors:

Polynomial functors
^^^^^^^^^^^^^^^^^^^

The main reference for this section is `Modular Type-Safety Proofs in
Agda <https://doi.org/10.1145/2428116.2428120>`__ by Schwaab and Siek (PLPV '07).

An important class of functors for our domain is the class of so called
*polynomial functors*. These are functors that are built up using the constant,
identity, sum, and product functors. To be precise, the actions of the latter on
objects are as follows: ``∀ A B`` (objects), ``∀ F G`` (functors),

-  ``const B A = B``
-  ``Id A = A``
-  ``(F + G) A = F A + G A``
-  ``(F × G) A = F A × G A``

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Categories.Functors where

  -- Imports from Agda and the Agda Standard Library  ---------------------------------------
  open import Agda.Primitive                         using ( _⊔_ ; lsuc ; Level )
                                                     renaming ( Set to Type ; lzero to ℓ₀ )
  open import Data.Nat                               using ( ℕ ; zero ; suc ; _>_ )
  open import Data.Sum.Base                          using ( _⊎_ ) renaming ( inj₁ to inl ;  inj₂ to inr )
  open import Data.Product                           using ( Σ-syntax ; _,_ ; _×_ )
  open import Data.Unit                              using ( tt ) renaming ( ⊤ to ⊤₀ )
  open import Data.Unit.Polymorphic                  using ( ⊤ )
  open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; _≢_ )
  open import Level

  private variable α β : Level

  infixl 6 _⊕_
  infixr 7 _⊗_

  data Functor₀ : Type (lsuc ℓ₀) where
   Id : Functor₀
   Const : Type → Functor₀
   _⊕_ : Functor₀ → Functor₀ → Functor₀
   _⊗_ : Functor₀ → Functor₀ → Functor₀

  [_]₀ : Functor₀ → Type → Type
  [ Id ]₀ B = B
  [ Const C ]₀ B = C
  [ F ⊕ G ]₀ B = [ F ]₀ B ⊎ [ G ]₀ B
  [ F ⊗ G ]₀ B = [ F ]₀ B × [ G ]₀ B

  data Functor {ℓ : Level} : Type (lsuc ℓ) where
   Id : Functor
   Const : Type ℓ → Functor
   _⊕_ : Functor{ℓ} → Functor{ℓ} → Functor
   _⊗_ : Functor{ℓ} → Functor{ℓ} → Functor

  [_]_ : Functor → Type α → Type α
  [ Id ] B = B
  [ Const C ] B = C
  [ F ⊕ G ] B = [ F ] B ⊎ [ G ] B
  [ F ⊗ G ] B = [ F ] B × [ G ] B

  {- from Mimram's talk (MFPS 2021):
  record Poly (I J : Type) : Type (lsuc ℓ₀) where
   field
    Op : J → Type
    Pm : (i : I) → {j : J} → Op j → Type
  -}

The least fixed point of a polynomial function can then be defined in Agda_ with
the following datatype declaration.

::

  data μ_ (F : Functor) : Type where
   inn : [ F ] (μ F) → μ F

An important example is the polymorphic list datatype. The standard way to define
this in Agda_ is as follows:

::

  data list (A : Type) : Type ℓ₀ where
   [] : list A
   _∷_ : A → list A → list A

We could instead define a ``List`` datatype by applying ``μ`` to a polynomial
functor ``L`` as follows:

::

  L : {ℓ : Level}(A : Type ℓ) → Functor{ℓ}
  L A = Const ⊤ ⊕ (Const A ⊗ Id)

  List : (A : Type) → Type ℓ₀
  List A = μ (L A)

To see some examples demonstrating that both formulations of the polymorphic list
type give what we expect, see the `Examples.Categories.Functors`_ module. The
examples will use "getter" functions, which take a list ``l`` and a natural number
``n`` and return the element of ``l`` at index ``n``. (Since such an element doesn't
always exist, we first define the ``Option`` type.)

::

  data Option (A : Type) : Type where
   some : A → Option A
   none : Option A

  _[_] : {A : Type} → List A → ℕ → Option A
  inn (inl x) [ n ] = none
  inn (inr (x , xs)) [ zero ] = some x
  inn (inr (x , xs)) [ suc n ] = xs [ n ]

  _⟦_⟧ : {A : Type} → list A → ℕ → Option A
  [] ⟦ n ⟧ = none
  (x ∷ l) ⟦ zero ⟧ = some x
  (x ∷ l) ⟦ suc n ⟧ = l ⟦ n ⟧


--------------

   ..
      @inproceedings{10.1145/2428116.2428120,
      author = {Schwaab, Christopher and Siek, Jeremy G.},
      title = {Modular Type-Safety Proofs in Agda},
      year = {2013},
      isbn = {9781450318600},
      publisher = {Association for Computing Machinery},
      address = {New York, NY, USA},
      url = {https://doi.org/10.1145/2428116.2428120},
      doi = {10.1145/2428116.2428120},
      abstract = {Methods for reusing code are widespread and well researched, but methods for reusing
      proofs are still emerging. We consider the use of dependent types for this purpose,
      introducing a modular approach for composing mechanized proofs. We show that common
      techniques for abstracting algorithms over data structures naturally translate to
      abstractions over proofs. We introduce a language composed of a series of smaller
      language components, each defined as functors, and tie them together by taking the
      fixed point of their sum [Malcom, 1990]. We then give proofs of type preservation
      for each language component and show how to compose these proofs into a proof for
      the entire language, again by taking the fixed point of a sum of functors.},
      booktitle = {Proceedings of the 7th Workshop on Programming Languages Meets Program Verification},
      pages = {3–12},
      numpages = {10},
      keywords = {agda, meta-theory, modularity},
      location = {Rome, Italy},
      series = {PLPV '13}

