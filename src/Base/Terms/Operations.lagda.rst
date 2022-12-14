.. FILE      : Base/Terms/Operations.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 03 Jun 2022
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-terms-term-operations:

Term Operations
~~~~~~~~~~~~~~~

This section presents the [Base.Terms.Operations][] module of the [Agda
Universal Algebra Library][].

Here we define *term operations* which are simply terms interpreted in a
particular algebra, and we prove some compatibility properties of term
operations.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( ๐ ; ๐ฅ ; Signature )

  module Base.Terms.Operations {๐ : Signature ๐ ๐ฅ} where

  -- Imports from Agda and the Agda Standard Library ---------------------
  open import Agda.Primitive  using ()  renaming ( Set to Type )
  open import Data.Product    using ( _,_ ; ฮฃ-syntax ; ฮฃ )
  open import Function        using ( _โ_ )
  open import Level           using ( Level ; _โ_ )
  open import Relation.Binary.PropositionalEquality as โก
                              using ( _โก_ ; module โก-Reasoning )
  open import Axiom.Extensionality.Propositional
                              using () renaming (Extensionality to funext)

  -- Imports from Agda Universal Algebra Library ----------------------------------------------
  open import Overture        using ( _โ_ ; _โปยน ; โฃ_โฃ ; โฅ_โฅ ; ฮ  ; ฮ -syntax ; _โ_ )
  open import Base.Relations  using ( _|:_ )
  open import Base.Equality   using ( swelldef )

  open import Base.Algebras          {๐ = ๐}  using ( Algebra ; _ฬ_ ; ov ; โจ )
                                              using ( IsCongruence ; Con )
  open import Base.Homomorphisms     {๐ = ๐}  using ( hom )
  open import Base.Terms.Basic       {๐ = ๐}  using ( Term ; ๐ป )
  open import Base.Terms.Properties  {๐ = ๐}  using ( free-lift )

  open Term
  private variable ฮฑ ฮฒ ฮณ ฯ ฯ : Level


When we interpret a term in an algebra we call the resulting function a *term
operation*. Given a term ``p`` and an algebra ``๐จ``, we denote by ``๐จ โฆ p โง`` the
*interpretation* of ``p`` in ``๐จ``. This is defined inductively as follows.

1. If ``p`` is a variable symbol ``x : X`` and if ``a : X โ โฃ ๐จ โฃ`` is a
   tuple of elements of ``โฃ ๐จ โฃ``, then ``๐จ โฆ p โง a := a x``.

2. If ``p = f t``, where ``f : โฃ ๐ โฃ`` is an operation symbol, if
   ``t : โฅ ๐ โฅ f โ ๐ป X`` is a tuple of terms, and if ``a : X โ โฃ ๐จ โฃ``
   is a tuple from ``๐จ``, then we define
   ``๐จ โฆ p โง a = ๐จ โฆ f t โง a := (f ฬ ๐จ) (ฮป i โ ๐จ โฆ t i โง a)``.

Thus the interpretation of a term is defined by induction on the structure of the
term, and the definition is formally implemented in the agda-algebras_ library as
follows.

::

  _โฆ_โง : (๐จ : Algebra ฮฑ){X : Type ฯ } โ Term X โ (X โ โฃ ๐จ โฃ) โ โฃ ๐จ โฃ
  ๐จ โฆ โ x โง = ฮป ฮท โ ฮท x
  ๐จ โฆ node f t โง = ฮป ฮท โ (f ฬ ๐จ) (ฮป i โ (๐จ โฆ t i โง) ฮท)

It turns out that the intepretation of a term is the same as the ``free-lift``
(modulo argument order and assuming function extensionality).

::

  free-lift-interp :  swelldef ๐ฅ ฮฑ โ (๐จ : Algebra ฮฑ){X : Type ฯ }
                      (ฮท : X โ โฃ ๐จ โฃ)(p : Term X) โ (๐จ โฆ p โง) ฮท โก (free-lift ๐จ ฮท) p

  free-lift-interp _ ๐จ ฮท (โ x) = โก.refl
  free-lift-interp wd ๐จ ฮท (node f t) =
   wd (f ฬ ๐จ) (ฮป z โ (๐จ โฆ t z โง) ฮท)
   ((free-lift ๐จ ฮท) โ t)((free-lift-interp wd ๐จ ฮท) โ t)

If the algebra in question happens to be ``๐ป X``, then we expect that ``โ s`` we
have ``(๐ป X)โฆ p โง s โก p s``. But what is ``(๐ป X)โฆ p โง s`` exactly? By definition,
it depends on the form of ``p`` as follows:

-  if ``p = โ x``, then ``(๐ป X)โฆ p โง s := (๐ป X)โฆ โ x โง s โก s x``

-  if ``p = node f t``, then ``(๐ป X)โฆ p โง s := (๐ป X)โฆ node f t โง s = (f ฬ ๐ป X) ฮป i โ (๐ป X)โฆ t i โง s``

Now, assume ``ฯ : hom ๐ป ๐จ``. Then by ``comm-hom-term``, we have
``โฃ ฯ โฃ (๐ป X)โฆ p โง s = ๐จ โฆ p โง โฃ ฯ โฃ โ s``.

-  if ``p = โ x`` (and ``t : X โ โฃ ๐ป X โฃ``), then

   ``โฃ ฯ โฃ p โก โฃ ฯ โฃ (โ x) โก โฃ ฯ โฃ (ฮป t โ h t) โก ฮป t โ (โฃ ฯ โฃ โ t) x``

-  if ``p = node f t``, then

   ``โฃ ฯ โฃ p โก โฃ ฯ โฃ (๐ป X)โฆ p โง s = (๐ป X)โฆ node f t โง s = (f ฬ ๐ป X) ฮป i โ (๐ป X)โฆ t i โง s``

We claim that for all ``p : Term X`` there exists ``q : Term X`` and
``t : X โ โฃ ๐ป X โฃ`` such that ``p โก (๐ป X)โฆ q โง t``. We prove this fact as follows.

::

  term-interp :  {X : Type ฯ} (f : โฃ ๐ โฃ){s t : โฅ ๐ โฅ f โ Term X}
   โ             s โก t โ node f s โก (f ฬ ๐ป X) t

  term-interp f {s}{t} st = โก.cong (node f) st


  term-interp' :  swelldef ๐ฅ (ov ฯ) โ {X : Type ฯ} (f : โฃ ๐ โฃ){s t : โฅ ๐ โฅ f โ Term X}
   โ              (โ i โ s i โก t i) โ node f s โก (f ฬ ๐ป X) t

  term-interp' wd f {s}{t} st = wd (node f) s t st


  term-gen :  swelldef ๐ฅ (ov ฯ) โ {X : Type ฯ}(p : โฃ ๐ป X โฃ)
   โ          ฮฃ[ q โ โฃ ๐ป X โฃ ] p โก (๐ป X โฆ q โง) โ

  term-gen _ (โ x) = (โ x) , โก.refl
  term-gen wd (node f t) =  (node f (ฮป i โ โฃ term-gen wd (t i) โฃ)) ,
                            term-interp' wd f ฮป i โ โฅ term-gen wd (t i) โฅ

  term-gen-agreement :  (wd : swelldef ๐ฅ (ov ฯ)){X : Type ฯ}(p : โฃ ๐ป X โฃ)
   โ                    (๐ป X โฆ p โง) โ โก (๐ป X โฆ โฃ term-gen wd p โฃ โง) โ
  term-gen-agreement _ (โ x) = โก.refl
  term-gen-agreement wd {X} (node f t) = wd  ( f ฬ ๐ป X) (ฮป x โ (๐ป X โฆ t x โง) โ)
                                             (ฮป x โ (๐ป X โฆ โฃ term-gen wd (t x) โฃ โง) โ)
                                             ฮป i โ term-gen-agreement wd (t i)

  term-agreement : swelldef ๐ฅ (ov ฯ) โ {X : Type ฯ}(p : โฃ ๐ป X โฃ) โ p โก  (๐ป X โฆ p โง) โ
  term-agreement wd {X} p = โฅ term-gen wd p โฅ โ (term-gen-agreement wd p)โปยน

.. _base-terms-interpretation-of-terms-in-product-algebras:

Interpretation of terms in product algebras
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  module _ (wd : swelldef ๐ฅ (ฮฒ โ ฮฑ)){X : Type ฯ }{I : Type ฮฒ} where

   interp-prod :  (p : Term X)(๐ : I โ Algebra ฮฑ)(a : X โ ฮ [ i โ I ] โฃ ๐ i โฃ)
    โ             (โจ ๐ โฆ p โง) a โก ฮป i โ (๐ i โฆ p โง)(ฮป x โ (a x) i)

   interp-prod (โ _) ๐ a = โก.refl
   interp-prod (node f t) ๐ a = wd ((f ฬ โจ ๐)) u v IH
    where
    u : โ x โ โฃ โจ ๐ โฃ
    u = ฮป x โ (โจ ๐ โฆ t x โง) a
    v : โ x i โ โฃ ๐ i โฃ
    v = ฮป x i โ (๐ i โฆ t x โง)(ฮป j โ a j i)
    IH : โ i โ u i โก v i
    IH = ฮป x โ interp-prod (t x) ๐ a

   interp-prod2 :  funext (ฮฑ โ ฮฒ โ ฯ) (ฮฑ โ ฮฒ) โ (p : Term X)(๐ : I โ Algebra ฮฑ)
    โ              โจ ๐ โฆ p โง โก (ฮป a i โ (๐ i โฆ p โง) ฮป x โ a x i)

   interp-prod2 _ (โ xโ) ๐ = โก.refl
   interp-prod2 fe (node f t) ๐ = fe ฮป a โ wd (f ฬ โจ ๐)(u a) (v a) (IH a)
    where
    u : โ a x โ โฃ โจ ๐ โฃ
    u a = ฮป x โ (โจ ๐ โฆ t x โง) a
    v : โ (a : X โ โฃ โจ ๐ โฃ) โ โ x i โ โฃ ๐ i โฃ
    v a = ฮป x i โ (๐ i โฆ t x โง)(ฮป z โ (a z) i)
    IH : โ a x โ (โจ ๐ โฆ t x โง) a โก ฮป i โ (๐ i โฆ t x โง)(ฮป z โ (a z) i)
    IH a = ฮป x โ interp-prod (t x) ๐ a



.. _base-terms-compatibility-of-terms:

Compatibility of terms
^^^^^^^^^^^^^^^^^^^^^^

We now prove two important facts about term operations. The first of these, which
is used very often in the sequel, asserts that every term commutes with every
homomorphism.

::

  open โก-Reasoning

  comm-hom-term :  swelldef ๐ฅ ฮฒ โ {๐จ : Algebra ฮฑ} (๐ฉ : Algebra ฮฒ)
                   (h : hom ๐จ ๐ฉ){X : Type ฯ}(t : Term X)(a : X โ โฃ ๐จ โฃ)
                   ------------------------------------------------------
    โ              โฃ h โฃ ((๐จ โฆ t โง) a) โก (๐ฉ โฆ t โง) (โฃ h โฃ โ a)

  comm-hom-term _ ๐ฉ h (โ x) a = โก.refl
  comm-hom-term wd {๐จ} ๐ฉ h (node f t) a =
   โฃ h โฃ((f ฬ ๐จ) ฮป i โ  (๐จ โฆ t i โง) a)      โกโจ i  โฉ
   (f ฬ ๐ฉ)(ฮป i โ  โฃ h โฃ ((๐จ โฆ t i โง) a))   โกโจ ii โฉ
   (f ฬ ๐ฉ)(ฮป r โ (๐ฉ โฆ t r โง) (โฃ h โฃ โ a))  โ
   where i  = โฅ h โฅ f ฮป r โ (๐จ โฆ t r โง) a
         ii = wd (f ฬ ๐ฉ)  ( ฮป iโ โ โฃ h โฃ ((๐จ โฆ t iโ โง) a) )
                         ( ฮป r โ (๐ฉ โฆ t r โง) (ฮป x โ โฃ h โฃ (a x)) )
                         ฮป j โ comm-hom-term wd ๐ฉ h (t j) a

To conclude this module, we prove that every term is compatible with every
congruence relation. That is, if ``t : Term X`` and ``ฮธ : Con ๐จ``, then
``a ฮธ b โ t(a) ฮธ t(b)``. (Recall, the compatibility relation ``|:`` was defined in
`Base.Relations.Discrete`_.) 

::

  module _ {ฮฑ ฮฒ : Level}{X : Type ฮฑ} where

   open IsCongruence

   _โฃ:_ : {๐จ : Algebra ฮฑ}(t : Term X)(ฮธ : Con{ฮฑ}{ฮฒ} ๐จ) โ (๐จ โฆ t โง) |: โฃ ฮธ โฃ
   ((โ x) โฃ: ฮธ) p = p x
   ((node f t) โฃ: ฮธ) p = (is-compatible โฅ ฮธ โฅ) f ฮป x โ ((t x) โฃ: ฮธ) p


**WARNING!** The compatibility relation for terms ``โฃ:`` is typed as \|:, whereas
the compatibility type for functions ``|:`` (defined in the
`Base.Relations.Discrete`_ module) is typed as ``|:``.


.. _base-terms-substitution:

Substitution
^^^^^^^^^^^^

A substitution from ``Y`` to ``X`` is simply a function from ``Y`` to ``X``, and
the application of a substitution is represented as follows.

::

  _[_] : {ฯ : Level}{X Y : Type ฯ} โ Term Y โ (Y โ X) โ Term X
  (โ y) [ ฯ ] = โ (ฯ y)
  (node f t)  [ ฯ ] = node f ฮป i โ t i [ ฯ ]

Alternatively, we may want a substitution that replaces each variable symbol in
``Y``, not with an element of ``X``, but with a term from ``Term X``.

::

  -- Substerm X Y, an inhabitant of which replaces each variable symbol in Y with a term from Term X.
  Substerm : (X Y : Type ฯ) โ Type (ov ฯ)
  Substerm X Y = (y : Y) โ Term X

  -- Application of a Substerm.
  _[_]t : {X Y : Type ฯ } โ Term Y โ Substerm X Y โ Term X
  (โ y) [ ฯ ]t = ฯ y
  (node f t) [ ฯ ]t = node f (ฮป z โ (t z) [ ฯ ]t )

Next we prove the important Substitution Theorem which asserts that an identity
``p โ q`` holds in an algebra ``๐จ`` iff it holds in ``๐จ`` after applying any
substitution.

::

  subst-lemma :  swelldef ๐ฅ ฮฑ โ {X Y : Type ฯ }(p : Term Y)(ฯ : Y โ X)
                 (๐จ : Algebra ฮฑ)(ฮท : X โ โฃ ๐จ โฃ)
   โ             (๐จ โฆ p [ ฯ ] โง) ฮท โก (๐จ โฆ p โง) (ฮท โ ฯ)

  subst-lemma _ (โ x) ฯ ๐จ ฮท = โก.refl
  subst-lemma wd (node f t) ฯ ๐จ ฮท = wd (f ฬ ๐จ)  ( ฮป i โ (๐จ โฆ (t i) [ ฯ ] โง) ฮท )
                                               ( ฮป i โ (๐จ โฆ t i โง) (ฮท โ ฯ) )
                                               ฮป i โ subst-lemma wd (t i) ฯ ๐จ ฮท

  subst-theorem :  swelldef ๐ฅ ฮฑ โ {X Y : Type ฯ }
                   (p q : Term Y)(ฯ : Y โ X)(๐จ : Algebra ฮฑ)
   โ               ๐จ โฆ p โง โ ๐จ โฆ q โง โ ๐จ โฆ p [ ฯ ] โง โ ๐จ โฆ q [ ฯ ] โง

  subst-theorem wd p q ฯ ๐จ Apq ฮท =
   (๐จ โฆ p [ ฯ ] โง) ฮท  โกโจ subst-lemma wd p ฯ ๐จ ฮท โฉ
   (๐จ โฆ p โง) (ฮท โ ฯ)  โกโจ Apq (ฮท โ ฯ) โฉ
   (๐จ โฆ q โง) (ฮท โ ฯ)  โกโจ โก.sym (subst-lemma wd q ฯ ๐จ ฮท) โฉ
   (๐จ โฆ q [ ฯ ] โง) ฮท  โ


