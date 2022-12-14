.. FILE      : Setoid/Homomorphisms/Kernels.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 13 Sep 2021
.. UPDATED   : 18 Jun 2022

.. highlight:: agda
.. role:: code

.. _kernels-of-homomorphisms:

Kernels of homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Homomorphisms.Kernels`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature)

  module Setoid.Homomorphisms.Kernels {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library ------------------------------------------
  open  import Data.Product      using ( _,_ )
  open  import Function          using ( _β_ ; id ) renaming ( Func to _βΆ_ )
  open  import Level             using ( Level )
  open  import Relation.Binary   using ( Setoid )
  open  import Relation.Binary.PropositionalEquality as β‘ using ()

  -- Imports from the Agda Universal Algebra Library ------------------------------------------
  open  import Overture          using  ( β£_β£ ; β₯_β₯ )
  open  import Base.Relations    using  ( kerRel ; kerRelOfEquiv )
  open  import Setoid.Functions  using  ( Image_β_ )

  open  import Setoid.Algebras {π = π}
        using ( Algebra ; _Μ_ ; ov ; _β£β_ ; Con ; mkcon ; _β±_ ; IsCongruence )

  open  import Setoid.Homomorphisms.Basic {π = π}
        using ( hom ; IsHom ; epi ; IsEpi ; epiβhom )

  open  import Setoid.Homomorphisms.Properties {π = π} using ( πΎπΉ )

  private variable  Ξ± Ξ² Οα΅ Οα΅ β : Level

  open Algebra  using ( Domain )
  open _βΆ_      using ( cong ) renaming (f to _β¨$β©_ )

  module _ {π¨ : Algebra Ξ± Οα΅}{π© : Algebra Ξ² Οα΅} (hh : hom π¨ π©) where

   open Setoid (Domain π¨)  renaming ( _β_ to _ββ_ )  using ( reflexive )
   open Algebra π©          renaming (Domain to B )   using ( Interp )
   open Setoid B           renaming ( _β_ to _ββ_ )
                           using ( sym ; trans ; isEquivalence )
   private h = _β¨$β©_ β£ hh β£

``HomKerComp`` asserts that the kernel of a homomorphism is compatible
with the basic operations. That is, if each ``(u i, v i)`` belongs to
the kernel, then so does the pair ``((f Μ π¨) u , (f Μ π¨) v)``.

::

   HomKerComp : π¨ β£β kerRel _ββ_ h
   HomKerComp f {u}{v} kuv = Goal
    where
    fhuv : (f Μ π©)(h β u) ββ (f Μ π©)(h β v)
    fhuv = cong Interp (β‘.refl , kuv)

    lem1 : h ((f Μ π¨) u) ββ (f Μ π©)(h β u)
    lem1 = IsHom.compatible β₯ hh β₯

    lem2 : (f Μ π©) (h β v) ββ h ((f Μ π¨) v)
    lem2 = sym (IsHom.compatible β₯ hh β₯)

    Goal : h ((f Μ π¨) u) ββ h ((f Μ π¨) v)
    Goal = trans lem1 (trans fhuv lem2)

The kernel of a homomorphism is a congruence of the domain, which we
construct as follows.

::

   kercon : Con π¨
   kercon =  kerRel _ββ_ h ,
             mkcon (Ξ» x β cong β£ hh β£ x)(kerRelOfEquiv isEquivalence h)(HomKerComp)

Now that we have a congruence, we can construct the quotient relative to
the kernel.

::

   kerquo : Algebra Ξ± Οα΅
   kerquo = π¨ β± kercon

::

  ker[_β_]_ :  (π¨ : Algebra Ξ± Οα΅) (π© : Algebra Ξ² Οα΅) β hom π¨ π© β Algebra _ _
  ker[ π¨ β π© ] h = kerquo h


.. _the-canonical-projection:

The canonical projection
^^^^^^^^^^^^^^^^^^^^^^^^

Given an algebra ``π¨`` and a congruence ``ΞΈ``, the *canonical
projection* is a map from ``π¨`` onto ``π¨ β± ΞΈ`` that is constructed, and
proved epimorphic, as follows.

::

  module _ {π¨ : Algebra Ξ± Οα΅}{π© : Algebra Ξ² Οα΅} (h : hom π¨ π©) where
   open IsCongruence

   Οepi : (ΞΈ : Con π¨ {β}) β epi π¨ (π¨ β± ΞΈ)
   Οepi ΞΈ = p , pepi
    where

    open Algebra (π¨ β± ΞΈ)      using () renaming ( Domain to A/ΞΈ )
    open Setoid A/ΞΈ           using ( sym ; refl )
    open IsHom {π¨ = (π¨ β± ΞΈ)}  using ( compatible )

    p : (Domain π¨) βΆ A/ΞΈ
    p = record { f = id ; cong = reflexive β₯ ΞΈ β₯ }

    pepi : IsEpi π¨ (π¨ β± ΞΈ) p
    pepi = record  { isHom = record { compatible = sym (compatible β₯ πΎπΉ β₯) }
                   ; isSurjective = Ξ» {y} β Image_β_.eq y refl
                   }


In may happen that we donβt care about the surjectivity of ``Οepi``, in
which case would might prefer to work with the *homomorphic reduct* of
``Οepi``. This is obtained by applying ``epi-to-hom``, like so.

::

   Οhom : (ΞΈ : Con π¨ {β}) β hom π¨ (π¨ β± ΞΈ)
   Οhom ΞΈ = epiβhom π¨ (π¨ β± ΞΈ) (Οepi ΞΈ)

We combine the foregoing to define a function that takes π-algebras
``π¨`` and ``π©``, and a homomorphism ``h : hom π¨ π©`` and returns the
canonical epimorphism from ``π¨`` onto ``π¨ [ π© ]/ker h``. (Recall, the
latter is the special notation we defined above for the quotient of
``π¨`` modulo the kernel of ``h``.)

::

   Οker : epi π¨ (ker[ π¨ β π© ] h)
   Οker = Οepi (kercon h)

The kernel of the canonical projection of ``π¨`` onto ``π¨ / ΞΈ`` is equal
to ``ΞΈ``, but since equality of inhabitants of certain types (like
``Congruence`` or ``Rel``) can be a tricky business, we settle for
proving the containment ``π¨ / ΞΈ β ΞΈ``. Of the two containments, this is
the easier one to prove; luckily it is also the one we need later.

::

   open IsCongruence

   ker-in-con : {ΞΈ : Con π¨ {β}} β β {x}{y} β β£ kercon (Οhom ΞΈ) β£ x y β  β£ ΞΈ β£ x y
   ker-in-con = id
