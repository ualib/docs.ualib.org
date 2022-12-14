.. FILE      : Setoid/Homomorphisms/Products.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 21 Sep 2021
.. UPDATED   : 18 Jun 2022

.. highlight:: agda
.. role:: code

.. _products-of-homomorphisms-of-algebras:

Products of Homomorphisms of Algebras
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Homomorphisms.Products`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (๐ ; ๐ฅ ; Signature)

  module Setoid.Homomorphisms.Products {๐ : Signature ๐ ๐ฅ} where

  -- Imports from Agda and the Agda Standard Library --------------------------
  open import Agda.Primitive   using () renaming ( Set to Type )
  open import Function         using () renaming ( Func to _โถ_ )
  open import Data.Product     using ( _,_ )
  open import Level            using ( Level )
  open import Relation.Binary  using ( Setoid )
  open import Relation.Binary.PropositionalEquality as โก using ( _โก_ )

  -- Imports from the Agda Universal Algebras Library ----------------------
  open import Overture         using ( โฃ_โฃ ; โฅ_โฅ)
  open import Setoid.Algebras {๐ = ๐}
                               using ( Algebra ; _ฬ_ ; โจ )
  open import Setoid.Homomorphisms.Basic {๐ = ๐}
                               using ( hom ; IsHom ; epi )

  private variable ฮฑ ฯแต ฮฒ ฯแต ๐ : Level

Suppose we have an algebra ``๐จ``, a type ``I : Type ๐``, and a family
``โฌ : I โ Algebra ฮฒ ๐`` of algebras. We sometimes refer to the
inhabitants of ``I`` as *indices*, and call ``โฌ`` an *indexed family of
algebras*.

If in addition we have a family ``๐ฝ : (i : I) โ hom ๐จ (โฌ i)`` of
homomorphisms, then we can construct a homomorphism from ``๐จ`` to the
product ``โจ โฌ`` in the natural way.

::

  module _ {I : Type ๐}{๐จ : Algebra ฮฑ ฯแต}(โฌ : I โ Algebra ฮฒ ฯแต)  where
   open Algebra ๐จ      using ()        renaming ( Domain to A )
   open Algebra (โจ โฌ)  using ()        renaming ( Domain to โจB )
   open _โถ_            using ( cong )  renaming ( f to _โจ$โฉ_ )
   open IsHom

   โจ-hom-co : (โ(i : I) โ hom ๐จ (โฌ i)) โ hom ๐จ (โจ โฌ)
   โจ-hom-co ๐ฝ = h , hhom
    where
    h : A โถ โจB
    (h โจ$โฉ a) i = โฃ ๐ฝ i โฃ โจ$โฉ a
    cong h xy i = cong โฃ ๐ฝ i โฃ xy

    hhom : IsHom ๐จ (โจ โฌ) h
    compatible hhom = ฮป i โ compatible โฅ ๐ฝ i โฅ

The family ``๐ฝ`` of homomorphisms inhabits the dependent type
``ฮ? i ๊ I , hom ๐จ (โฌ i)``. The syntax we use to represent this type is
available to us because of the way ``-ฮ?`` is defined in the [Type
Topology][] library. We like this syntax because it is very close to the
notation one finds in the standard type theory literature. However, we
could equally well have used one of the following alternatives, which
may be closer to โstandard Agdaโ syntax:

``ฮ? ฮป i โ hom ๐จ (โฌ i)`` ย? or ย? ``(i : I) โ hom ๐จ (โฌ i)`` ย? or ย?
``โ i โ hom ๐จ (โฌ i)``.

The foregoing generalizes easily to the case in which the domain is also
a product of a family of algebras. That is, if we are given
``๐ : I โ Algebra ฮฑ ๐ and โฌ : I โ Algebra ฮฒ ๐`` (two families of
``๐``-algebras), and ``๐ฝ :  ฮ? i ๊ I , hom (๐ i)(โฌ i)`` (a family of
homomorphisms), then we can construct a homomorphism from ``โจ ๐`` to
``โจ โฌ`` in the following natural way.

::

   โจ-hom : (๐ : I โ Algebra ฮฑ ฯแต) โ (โ (i : I) โ hom (๐ i) (โฌ i)) โ hom (โจ ๐)(โจ โฌ)
   โจ-hom ๐ ๐ฝ = F , isHom
    where
    open Algebra (โจ ๐) using () renaming ( Domain to โจA )

    F : โจA โถ โจB
    (F โจ$โฉ x) i = โฃ ๐ฝ i โฃ โจ$โฉ x i
    cong F xy i = cong โฃ ๐ฝ i โฃ (xy i)

    isHom : IsHom (โจ ๐) (โจ โฌ) F
    compatible isHom i = compatible โฅ ๐ฝ i โฅ

.. _projection-out-of-products:

Projection out of products
^^^^^^^^^^^^^^^^^^^^^^^^^^

Later we will need a proof of the fact that projecting out of a product
algebra onto one of its factors is a homomorphism.

::

   โจ-projection-hom : (i : I) โ hom (โจ โฌ) (โฌ i)
   โจ-projection-hom i = F , isHom
    where
    open Algebra (โฌ i)  using () renaming ( Domain to Bi )
    open Setoid Bi      using () renaming ( refl to reflแตข )

    F : โจB โถ Bi
    F โจ$โฉ x = x i
    cong F xy = xy i

    isHom : IsHom (โจ โฌ) (โฌ i) F
    compatible isHom {f} {a} = reflแตข

We could prove a more general result involving projections onto multiple
factors, but so far the single-factor result has sufficed.

