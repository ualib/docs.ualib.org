.. FILE      : Base/Homomorphism/Basic.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 13 Jan 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-homomorphisms-basic-definitions:

Basic Definitions
~~~~~~~~~~~~~~~~~

This is the `Base.Homomorphisms.Basic`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( Signature; π ; π₯ )

  module Base.Homomorphisms.Basic {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library --------------------------------
  open import Agda.Primitive  renaming ( Set to Type )   using ()
  open import Data.Product    renaming ( projβ to fst )
                              using ( _,_ ; Ξ£ ;  _Γ_ ; Ξ£-syntax)
  open import Function        using ( _β_ ; id )
  open import Level           using ( Level ; _β_ )

  open import Relation.Binary.PropositionalEquality using ( _β‘_ ; refl )

  -- Imports from the Agda Universal Algebras Library --------------------------------
  open import Overture               using ( β£_β£ ; β₯_β₯ )
  open import Base.Functions         using ( IsInjective ; IsSurjective )
  open import Base.Algebras {π = π}  using ( Algebra ; _Μ_ ; Lift-Alg )

  private variable Ξ± Ξ² : Level


.. _base-homomorphisms-homomorphisms:

Homomorphisms
^^^^^^^^^^^^^

If ``π¨`` and ``π©`` are ``π``-algebras, then a *homomorphism* from ``π¨`` to ``π©`` is a
function ``h : β£ π¨ β£ β β£ π© β£`` from the domain of ``π¨`` to the domain of ``π©``
that is *compatible* (or *commutes*) with all of the basic operations of the
signature; that is, for all operation symbols ``π : β£ π β£`` and tuples 
``a : β₯ π β₯ π β β£ π¨ β£`` of ``π¨``, the following holds:
``h ((π Μ π¨) a) β‘ (π Μ π©) (h β a)``.

**Remarks**. Recall, ``h β π`` is the tuple whose i-th component is ``h (π i)``.
Instead of "homomorphism," we sometimes use the nickname "hom" to refer to such a map.

To formalize this concept, we first define a type representing the assertion
that a function ``h : β£ π¨ β£ β β£ π© β£`` commutes with a single basic operation
``π``. With Agda's extremely flexible syntax the defining equation above can be
expressed unadulterated. 

::

  module _ (π¨ : Algebra Ξ±)(π© : Algebra Ξ²) where

   compatible-op-map : β£ π β£ β (β£ π¨ β£ β β£ π© β£) β Type(Ξ± β π₯ β Ξ²)
   compatible-op-map π h = β π β h ((π Μ π¨) π) β‘ (π Μ π©) (h β π)

Agda infers from the shorthand ``β π`` that ``π`` has type ``β₯ π β₯ π β β£ π¨ β£``
since it must be a tuple on ``β£ π¨ β£`` of "length" ``β₯ π β₯ π`` (the arity of
``π``).

We now define the type ``hom π¨ π©`` of homomorphisms from ``π¨`` to ``π©`` by first
defining the type ``is-homomorphism`` which represents the property of being a
homomorphism.

::

   is-homomorphism : (β£ π¨ β£ β β£ π© β£) β Type(π β π₯ β Ξ± β Ξ²)
   is-homomorphism g = β π  β  compatible-op-map π g

   hom : Type(π β π₯ β Ξ± β Ξ²)
   hom = Ξ£ (β£ π¨ β£ β β£ π© β£) is-homomorphism

.. _base-homomorphisms-important-examples-of-homomorphisms:

Important examples of homomorphisms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Let's look at a few important examples of homomorphisms. These examples
are actually quite special in that every algebra has such a
homomorphism.

We begin with the identity map, which is proved to be (the underlying
map of) a homomorphism as follows.

::

  πΎπΉ : (π¨ : Algebra Ξ±) β hom π¨ π¨
  πΎπΉ _ = id , Ξ» π π β refl

Next, the lifting of an algebra to a higher universe level is, in fact, a
homomorphism. Dually, the lowering of a lifted algebra to its original universe
level is a homomorphism.

::

  open Level

  ππΎπ»π : {Ξ² : Level}(π¨ : Algebra Ξ±) β hom π¨ (Lift-Alg π¨ Ξ²)
  ππΎπ»π _ = lift , Ξ» π π β refl

  πβ΄πβ―π : {Ξ² : Level}(π¨ : Algebra Ξ±) β hom (Lift-Alg π¨ Ξ²) π¨
  πβ΄πβ―π _ = lower , Ξ» π π β refl


.. _base-homomorphisms-monomorphisms-and-epimorphisms:

Monomorphisms and epimorphisms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A *monomorphism* is an injective homomorphism and an *epimorphism* is a
surjective homomorphism. These are represented in the agda-algebras_ library by
the following types.

::

  is-monomorphism : (π¨ : Algebra Ξ±)(π© : Algebra Ξ²) β (β£ π¨ β£ β β£ π© β£) β Type _
  is-monomorphism π¨ π© g = is-homomorphism π¨ π© g Γ IsInjective g

  mon : Algebra Ξ± β Algebra Ξ² β Type _
  mon π¨ π© = Ξ£[ g β (β£ π¨ β£ β β£ π© β£) ] is-monomorphism π¨ π© g

  is-epimorphism : (π¨ : Algebra Ξ±)(π© : Algebra Ξ²) β (β£ π¨ β£ β β£ π© β£) β Type _
  is-epimorphism π¨ π© g = is-homomorphism π¨ π© g Γ IsSurjective g

  epi : Algebra Ξ± β Algebra Ξ² β Type _
  epi π¨ π© = Ξ£[ g β (β£ π¨ β£ β β£ π© β£) ] is-epimorphism π¨ π© g

(Evidently, Agda_ is able to infer the return type of each of the last four
definitions, so we can use ``Type _`` instead of ``Type (π β π₯ β Ξ± β Ξ²)``.)

It will be convenient to have a function that takes an inhabitant of ``mon`` (or
``epi``) and extracts the homomorphism part, or *hom reduct* (that is, the pair
consisting of the map and a proof that the map is a homomorphism).

::

  monβhom : (π¨ : Algebra Ξ±){π© : Algebra Ξ²} β mon π¨ π© β hom π¨ π©
  monβhom π¨ Ο = β£ Ο β£ , fst β₯ Ο β₯

  epiβhom : {π¨ : Algebra Ξ±}(π© : Algebra Ξ²) β epi π¨ π© β hom π¨ π©
  epiβhom _ Ο = β£ Ο β£ , fst β₯ Ο β₯

