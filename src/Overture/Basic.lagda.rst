.. FILE      : Overture.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 13 Jan 2021
.. UPDATED   : 17 Jun 2022

.. _preliminaries:

Preliminaries
-------------

This is the `Overture.Basic`_ module of the `Agda Universal Algebra Library`_.


.. _logical-foundations:

Logical foundations
~~~~~~~~~~~~~~~~~~~

(See also the `Base.Equality`_ module of the agda-algebras_ library.)

An Agda program typically begins by setting some options and by
importing types from existing Agda libraries. Options are specified with
the ``OPTIONS`` *pragma* and control the way Agda behaves by, for
example, specifying the logical axioms and deduction rules we wish to
assume when the program is type-checked to verify its correctness. Every
Agda program in agda-algebras_ begins with the following ``OPTIONS`` pragma.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

These options control certain foundational assumptions that Agda makes
when type-checking the program to verify its correctness.

-  ``--without-K`` disables `Streicher's K
   axiom <https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29>`__;
   see also the `section on axiom
   K <https://agda.readthedocs.io/en/v2.6.1/language/without-k.html>`__
   in the `Agda Language Reference
   Manual <https://agda.readthedocs.io/en/v2.6.1.3/language>`__.

-  ``--exact-split`` makes Agda accept only those definitions that
   behave like so-called *judgmental* equalities. `Martín
   Escardó <https://www.cs.bham.ac.uk/~mhe>`__ explains this by saying
   it “makes sure that pattern matching corresponds to Martin-Löf
   eliminators;” see also the `Pattern matching and equality
   section <https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality>`__ of the `Agda Tools <https://agda.readthedocs.io/en/v2.6.1.3/tools/>`__
   documentation.

-  ``safe`` ensures that nothing is postulated outright—every non-MLTT
   axiom has to be an explicit assumption (e.g., an argument to a
   function or module); see also `this
   section <https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe>`__
   of the `Agda
   Tools <https://agda.readthedocs.io/en/v2.6.1.3/tools/>`__
   documentation and the `Safe Agda
   section <https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda>`__
   of the `Agda Language
   Reference <https://agda.readthedocs.io/en/v2.6.1.3/language>`__.

Note that if we wish to type-check a file that imports another file that
still has some unmet proof obligations, we must replace the ``--safe``
flag with ``--allow-unsolved-metas``, but this is never done in
(publicly released versions of) the agda-algebras_.


.. _agda-modules:

Agda modules
~~~~~~~~~~~~

The ``OPTIONS`` pragma is usually followed by the start of a module. For
example, the `Base.Functions.Basic`_ module begins with the following
line, and then a list of imports of things used in the module.

::

  module Overture.Basic where

  -- Imports from Agda and the Agda Standard Library -----------------------------------------------
  open import Agda.Primitive    using () renaming ( Set to  Type ; lzero to  ℓ₀ )
  open import Data.Product      using ( _,_ ; ∃ ; Σ-syntax ; _×_ )
                                renaming ( proj₁ to fst ; proj₂ to snd )
  open import Function.Base     using ( _∘_ ; id )
  open import Level             using ( Level ; suc ; _⊔_ ; lift ; lower ; Lift )
  open import Relation.Binary   using ( Decidable )
  open import Relation.Binary   using ( IsEquivalence ; IsPartialOrder )
  open import Relation.Nullary  using ( Dec ; yes ; no ; Irrelevant )

  open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; trans )

  private variable α β : Level

  ℓ₁ : Level
  ℓ₁ = suc ℓ₀

  -- the two element type
  data 𝟚 : Type ℓ₀ where 𝟎 : 𝟚 ;  𝟏 : 𝟚

  -- the three element type
  data 𝟛 : Type ℓ₀ where 𝟎 : 𝟛 ;  𝟏 : 𝟛 ;  𝟐 : 𝟛

.. _projection-notation:

Projection notation
~~~~~~~~~~~~~~~~~~~

The definition of ``Σ`` (and thus, of ``×``) includes the fields
``proj₁`` and ``proj₂`` representing the first and second projections
out of the product. However, we prefer the shorter names ``fst`` and
``snd``. Sometimes we prefer to denote these projections by ``∣_∣`` and
``∥_∥``, respectively. We define these alternative notations for
projections out of pairs as follows.

::

  module _ {A : Type α }{B : A → Type β} where

   ∣_∣ : Σ[ x ∈ A ] B x → A
   ∣_∣ = fst

   ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
   ∥_∥ = snd

   infix  40 ∣_∣

Here we put the definitions inside an *anonymous module*, which starts
with the ``module`` keyword followed by an underscore (instead of a
module name). The purpose is simply to move the postulated typing
judgments—the “parameters” of the module (e.g., ``A : Type α``)—out of
the way so they don't obfuscate the definitions inside the module.

Let's define some useful syntactic sugar that will make it easier to
apply symmetry and transitivity of ``≡`` in proofs.

::

  _⁻¹ : {A : Type α} {x y : A} → x ≡ y → y ≡ x
  p ⁻¹ = sym p

  infix  40 _⁻¹


If we have a proof ``p : x ≡ y``, and we need a proof of ``y ≡ x``, then
instead of ``sym p`` we can use the more intuitive ``p ⁻¹``. Similarly,
the following syntactic sugar makes abundant appeals to transitivity
easier to stomach.

::

  _∙_ : {A : Type α}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  p ∙ q = trans p q

  𝑖𝑑 : (A : Type α ) → A → A
  𝑖𝑑 A = λ x → x

  infixl 30 _∙_


.. _sigma-types:

Sigma types
~~~~~~~~~~~

::

  infix 2 ∃-syntax

  ∃-syntax : ∀ {A : Type α} → (A → Type β) → Set (α ⊔ β)
  ∃-syntax = ∃

  syntax ∃-syntax (λ x → B) = ∃[ x ∈ A ] B


.. _pi-types:

Pi types
~~~~~~~~

The dependent function type is traditionally denoted with an uppercase
pi symbol and typically expressed as ``Π(x : A) B x``, or something
similar. In Agda syntax, one writes ``(x : A) → B x`` for this dependent
function type, but we can define syntax that is closer to standard
notation as follows.

::

  Π : {A : Type α } (B : A → Type β ) → Type (α ⊔ β)
  Π {A = A} B = (x : A) → B x

  Π-syntax : (A : Type α)(B : A → Type β) → Type (α ⊔ β)
  Π-syntax A B = Π B

  syntax Π-syntax A (λ x → B) = Π[ x ∈ A ] B
  infix 6 Π-syntax

In the modules that follow, we will see many examples of this syntax in
action.


.. _pointwise-equality-of-dependent-functions:

Pointwise equality of dependent functions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We conclude this module with a definition that conveniently represents
te assertion that two functions are (extensionally) the same in the
sense that they produce the same output when given the same input. (We
will have more to say about this notion of equality in the
`Base.Equality.Extensionality`_ module.)

::

  module _ {α : Level}{A : Type α}{β : Level}{B : A → Type β } where

   _≈_ :  (f g : (a : A) → B a) → Type (α ⊔ β)
   f ≈ g = ∀ x → f x ≡ g x

   infix 8 _≈_

   ≈IsEquivalence : IsEquivalence _≈_
   IsEquivalence.refl   ≈IsEquivalence          = λ _ → refl
   IsEquivalence.sym    ≈IsEquivalence f≈g      = λ x → sym (f≈g x)
   IsEquivalence.trans  ≈IsEquivalence f≈g g≈h  = λ x → trans (f≈g x) (g≈h x)


The following is convenient for proving two pairs of a
product type are equal using the fact that their respective components
are equal.

::

  ≡-by-parts :  {A : Type α}{B : Type β}{u v : A × B}
   →            fst u ≡ fst v → snd u ≡ snd v → u ≡ v

  ≡-by-parts refl refl = refl

Lastly, we will use the following type (instead of ``subst``) to
transport equality proofs.

::

  transport : {A : Type α } (B : A → Type β) {x y : A} → x ≡ y → B x → B y
  transport B refl = id
