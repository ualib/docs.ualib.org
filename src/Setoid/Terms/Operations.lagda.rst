.. FILE      : Setoid/Terms/Operations.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 25 Sep 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-terms-term-operations-for-setoid-algebras:

Term Operations for Setoid Algebras
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Terms.Operations`_ module of the `Agda Universal Algebra Library`_.

Here we define *term operations* which are simply terms interpreted in a particular
algebra, and we prove some compatibility properties of term operations.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (๐ ; ๐ฅ ; Signature)

  module Setoid.Terms.Operations {๐ : Signature ๐ ๐ฅ} where

  -- Imports from Agda and the Agda Standard Library ---------------------
  open import Agda.Primitive    using ()  renaming ( Set to Type )
  open import Data.Product      using ( _,_ )
  open import Function.Base     using ( _โ_ )
  open import Function.Bundles  using ()         renaming ( Func to _โถ_ )
  open import Level             using ( Level )
  open import Relation.Binary   using ( Setoid )

  open import Relation.Binary.PropositionalEquality as โก using ( _โก_ )

  import Relation.Binary.Reasoning.Setoid as SetoidReasoning

  -- Imports from Agda Universal Algebra Library -----------------------------------
  open  import Overture                         using ( โฃ_โฃ ; โฅ_โฅ )
  open  import Base.Terms               {๐ = ๐} using ( Term )
  open  import Setoid.Algebras          {๐ = ๐} using ( Algebra ; _ฬ_ ; ov ; โจ )
  open  import Setoid.Homomorphisms     {๐ = ๐} using ( hom ; IsHom )
  open  import Setoid.Terms.Properties  {๐ = ๐} using ( free-lift )
  open  import Setoid.Terms.Basic       {๐ = ๐}
        using ( module Environment ; ๐ป ; _โ_ ; โ-isRefl )

  open Term
  open _โถ_ using ( cong ) renaming ( f to _โจ$โฉ_ )

  private variable
   ฮฑ ฯแต ฮฒ ฯแต ฯ ฯ ฮน : Level
   X : Type ฯ


It turns out that the intepretation of a term is the same as the
``free-lift`` (modulo argument order and assuming function
extensionality).

::

  module _ {๐จ : Algebra ฮฑ ฯแต} where
   open Algebra ๐จ      using ( Interp )      renaming (Domain to A )
   open Setoid A       using ( _โ_ ; refl )  renaming ( Carrier to โฃAโฃ )
   open Environment ๐จ  using ( โฆ_โง )

   free-lift-interp :  (ฮท : X โ โฃAโฃ)(p : Term X)
    โ                  โฆ p โง โจ$โฉ ฮท โ (free-lift{๐จ = ๐จ} ฮท) p

   free-lift-interp ฮท (โ x) = refl
   free-lift-interp ฮท (node f t) = cong Interp (โก.refl , (free-lift-interp ฮท) โ t)

  module _ {X : Type ฯ} where
   open Algebra (๐ป X)      using ( Interp )      renaming (Domain to TX )
   open Setoid TX          using ( _โ_ ; refl )  renaming ( Carrier to โฃTXโฃ )
   open Environment (๐ป X)  using ( โฆ_โง ; โโEqual )
   open SetoidReasoning TX

   term-interp :  (f : โฃ ๐ โฃ){s t : โฅ ๐ โฅ f โ Term X} โ (โ i โ s i โ t i)
    โ             โ ฮท โ โฆ node f s โง โจ$โฉ ฮท โ โฆ node f t โง โจ$โฉ ฮท -- (f ฬ ๐ป X) t

   term-interp f {s}{t} st ฮท = cong Interp (โก.refl , ฮป i โ โโEqual (s i) (t i) (st i) ฮท )

   term-agreement : (p : Term X) โ p โ โฆ p โง โจ$โฉ โ
   term-agreement (โ x) = refl
   term-agreement (node f t) = cong Interp (โก.refl , (ฮป i โ term-agreement (t i)))

.. _setoid-terms-interpretation-in-product-algebras:

Interpretation in product algebras
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  module _ {X : Type ฯ }{I : Type ฮน}(๐ : I โ Algebra ฮฑ ฯแต) where
   open Algebra (โจ ๐)      using (Interp)  renaming ( Domain to โจA )
   open Setoid โจA          using ( _โ_ ; refl )
   open Environment (โจ ๐)  using ()        renaming ( โฆ_โง to โฆ_โงโ )
   open Environment        using ( โฆ_โง ; โโEqual )

   interp-prod :  (p : Term X)
    โ             โ ฯ โ โฆ p โงโ โจ$โฉ ฯ โ (ฮป i โ (โฆ ๐ i โง p) โจ$โฉ (ฮป x โ (ฯ x) i))

   interp-prod (โ x) = ฮป ฯ i โ โโEqual (๐ i) (โ x) (โ x) โ-isRefl ฮป x' โ (ฯ x) i
   interp-prod (node f t) = ฮป ฯ i โ cong Interp (โก.refl , (ฮป j k โ interp-prod (t j) ฯ k)) i


.. _setoid-terms-compatibility-of-terms:

Compatibility of terms
^^^^^^^^^^^^^^^^^^^^^^

We now prove two important facts about term operations. The first of these, which
is used very often in the sequel, asserts that every term commutes with every homomorphism.

::

  module _ {๐จ : Algebra ฮฑ ฯแต}{๐ฉ : Algebra ฮฒ ฯแต}(hh : hom ๐จ ๐ฉ) where
   open Algebra ๐จ      using () renaming (Domain to A ; Interp to Interpโ )
   open Setoid A       using () renaming ( _โ_ to _โโ_ ; Carrier to โฃAโฃ )
   open Algebra ๐ฉ      using () renaming (Domain to B ; Interp to Interpโ )
   open Setoid B       using ( _โ_ ; sym ; refl )
   open Environment ๐จ  using () renaming ( โฆ_โง to โฆ_โงโ )
   open Environment ๐ฉ  using () renaming ( โฆ_โง to โฆ_โงโ )
   open SetoidReasoning B
   open IsHom

   private
    hfunc = โฃ hh โฃ
    h = _โจ$โฉ_ hfunc

   comm-hom-term :  (t : Term X) (a : X โ โฃAโฃ)
    โ               h (โฆ t โงโ โจ$โฉ a) โ โฆ t โงโ โจ$โฉ (h โ a)

   comm-hom-term (โ x) a = refl
   comm-hom-term (node f t) a = goal
    where
    goal : h (โฆ node f t โงโ โจ$โฉ a) โ (โฆ node f t โงโ โจ$โฉ (h โ a))
    goal = begin
     h (โฆ node f t โงโ โจ$โฉ a)             โโจ (compatible โฅ hh โฅ) โฉ
     (f ฬ ๐ฉ)(ฮป i โ h (โฆ t i โงโ โจ$โฉ a))    โโจ cong Interpโ (โก.refl , ฮป i โ comm-hom-term (t i) a) โฉ
     (f ฬ ๐ฉ)(ฮป i โ โฆ t i โงโ โจ$โฉ (h โ a))  โโจ refl โฉ
     (โฆ node f t โงโ โจ$โฉ (h โ a))         โ


.. _setoid-terms-substitution:

Substitution
^^^^^^^^^^^^

A substitution from ``Y`` to ``X`` is simply a function from ``Y`` to ``X``, and
the application of a substitution is represented as follows.

::

  _[_]s : {ฯ : Level}{X Y : Type ฯ} โ Term Y โ (Y โ X) โ Term X
  (โ y) [ ฯ ]s = โ (ฯ y)
  (node f t)  [ ฯ ]s = node f ฮป i โ t i [ ฯ ]s


Alternatively, we may want a substitution that replaces each variable
symbol in ``Y``, not with an element of ``X``, but with a term from
``Term X``.

::

  -- Substerm X Y, an inhabitant of which replaces each variable symbol in Y with a term from Term X.
  Substerm : (X Y : Type ฯ) โ Type (ov ฯ)
  Substerm X Y = (y : Y) โ Term X

  -- Application of a Substerm.
  _[_]t : {X Y : Type ฯ } โ Term Y โ Substerm X Y โ Term X
  (โ y) [ ฯ ]t = ฯ y
  (node f t) [ ฯ ]t = node f (ฮป z โ (t z) [ ฯ ]t )

