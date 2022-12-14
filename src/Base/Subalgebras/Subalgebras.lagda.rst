.. FILE      : Base/Subalgebras/Subalgebras.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 14 Jan 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-subalgebras-subalgebras:

Subalgebras
~~~~~~~~~~~

This is the `Base.Subalgebras.Subalgebras`_ module of the `Agda Universal Algebra Library`_,
where we define the type, ``Subalgebra``, representing a *subalgebra* of a given algebra,
as well as the collection of all subalgebras of a given class of algebras.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature )

  module Base.Subalgebras.Subalgebras {π : Signature π π₯} where

  -- imports from Agda and the Agda Standard Library ------------------------------------
  open import Agda.Primitive  using () renaming ( Set to Type )
  open import Data.Product    using ( _,_ ; Ξ£-syntax ; _Γ_ ) renaming ( projβ to snd )
  open import Level           using ( Level ; _β_ )
  open import Relation.Unary  using ( Pred ; _β_ )

  -- Imports from the Agda Universal Algebra Library ------------------------------------
  open  import Overture       using ( β£_β£ ; β₯_β₯ )
  open  import Base.Functions using ( IsInjective )
  open  import Base.Equality  using ( swelldef ; is-set ; blk-uip ; pred-ext )

  open  import Base.Algebras       {π = π} using ( Algebra ; ov )
  open  import Base.Terms          {π = π} using ( π» ; Term )
  open  import Base.Homomorphisms  {π = π} using ( hom ; kercon ; ker[_β_]_βΎ_ )
                                           using ( FirstHomTheorem|Set ; _β_ )

  private variable Ξ± Ξ² Ξ³ π§ : Level


.. _base-subalgebras-subalgebra-type:

Subalgebra type
^^^^^^^^^^^^^^^

Given algebras ``π¨ : Algebra Ξ± π`` and ``π© : Algebra π¦ π``, we say that ``π©`` is a
*subalgebra* of ``π¨`` just in case ``π©`` can be *homomorphically embedded* in
``π¨``; that is, there exists a map ``h : β£ π© β£ β β£ π¨ β£`` that is both a
homomorphism and an embedding.

::

  _β€_  -- (alias for subalgebra relation))
   _IsSubalgebraOf_ : Algebra Ξ± β Algebra Ξ² β Type _
  π¨ IsSubalgebraOf π© = Ξ£[ h β hom π¨ π© ] IsInjective β£ h β£

  _β₯_  -- (alias for supalgebra (aka overalgebra))
   _IsSupalgebraOf_ : Algebra Ξ± β Algebra Ξ² β Type _
  π¨ IsSupalgebraOf π© = Ξ£[ h β hom π© π¨ ] IsInjective β£ h β£

  -- Syntactic sugar for sub/sup-algebra relations.
  π¨ β€ π© = π¨ IsSubalgebraOf π©
  π¨ β₯ π© = π¨ IsSupalgebraOf π©

  -- From now on we use `π¨ β€ π©` to express the assertion that `π¨` is a subalgebra of `π©`.
  record SubalgebraOf : Type (ov (Ξ± β Ξ²)) where
   field
    algebra : Algebra Ξ±
    subalgebra : Algebra Ξ²
    issubalgebra : subalgebra β€ algebra

  Subalgebra : Algebra Ξ± β {Ξ² : Level} β Type _
  Subalgebra  π¨ {Ξ²} = Ξ£[ π© β (Algebra Ξ²) ] π© β€ π¨

Note the order of the arguments. The universe ``Ξ²`` comes first because in certain
situations we must explicitly specify this universe, whereas we can almost always
leave the universe ``Ξ±`` implicit. (See, for example, the definition of
``_IsSubalgebraOfClass_`` below.)


.. _base-subalgebras-consequences-of-the-first-homomorphism-theorem:

Consequences of the First Homomorphism Theorem
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We take this opportunity to prove an important lemma that makes use of the
``IsSubalgebraOf`` type defined above. It is the following: If ``π¨`` and ``π©`` are
``π``-algebras and ``h : hom π¨ π©`` a homomorphism from ``π¨`` to ``π©``, then the
quotient ``π¨ β± ker h`` is (isomorphic to) a subalgebra of ``π©``. This is an easy
corollary of the First Homomorphism Theorem proved in the
`Base.Homomorphisms.Noether`_ module. 

::

  module _  (π¨ : Algebra Ξ±)(π© : Algebra Ξ²)(h : hom π¨ π©)
            -- extensionality assumptions:
            (pe : pred-ext Ξ± Ξ²)(fe : swelldef π₯ Ξ²)

            -- truncation assumptions:
            (Bset : is-set β£ π© β£)
            (buip : blk-uip β£ π¨ β£ β£ kercon fe {π©} h β£)
            where

   FirstHomCorollary|Set : (ker[ π¨ β π© ] h βΎ fe) IsSubalgebraOf π©
   FirstHomCorollary|Set = Οhom , Οinj
    where
     hh = FirstHomTheorem|Set π¨ π© h pe fe Bset buip
     Οhom : hom (ker[ π¨ β π© ] h βΎ fe) π©
     Οhom = β£ hh β£

     Οinj : IsInjective β£ Οhom β£
     Οinj = β£ snd β₯ hh β₯ β£

If we apply the foregoing theorem to the special case in which the ``π¨`` is term
algebra ``π» X``, we obtain the following result which will be useful later.

::

  module _  (X : Type π§)(π© : Algebra Ξ²)(h : hom (π» X) π©)
            -- extensionality assumptions:
            (pe : pred-ext (ov π§) Ξ²)(fe : swelldef π₯ Ξ²)

            -- truncation assumptions:
            (Bset : is-set β£ π© β£)
            (buip : blk-uip (Term X) β£ kercon fe {π©} h β£)
            where

   free-quot-subalg : (ker[ π» X β π© ] h βΎ fe) IsSubalgebraOf π©
   free-quot-subalg = FirstHomCorollary|Set{Ξ± = ov π§}(π» X) π© h pe fe Bset buip

.. _base-subalgebras-subalgebras-of-a-class:

Subalgebras of a class
^^^^^^^^^^^^^^^^^^^^^^

One of our goals is to formally express and prove properties of classes of
algebraic structures. Fixing a signature ``π`` and a universe ``Ξ±``, we represent
classes of ``π``-algebras with domains of type ``Type Ξ±`` as predicates over the
``Algebra Ξ± π`` type. In the syntax of the agda-algebras_ library, such predicates
inhabit the type ``Pred (Algebra Ξ± π) Ξ³``, for some universe ``Ξ³``.

Suppose ``π¦ : Pred (Algebra Ξ± π) Ξ³`` denotes a class of ``π``-algebras and ``π© :
Algebra Ξ² π`` denotes an arbitrary ``π``-algebra. Then we might wish to consider
the assertion that ``π©`` is a subalgebra of an algebra in the class ``π¦``. The
next type we define allows us to express this assertion as
``π© IsSubalgebraOfClass π¦``.

::

  module _ {Ξ± Ξ² : Level} where

   _IsSubalgebraOfClass_ : Algebra Ξ² β Pred (Algebra Ξ±) Ξ³ β Type _
   π© IsSubalgebraOfClass π¦ =  Ξ£[ π¨ β Algebra Ξ± ]
                              Ξ£[ sa β Subalgebra π¨ {Ξ²} ] ((π¨ β π¦) Γ (π© β β£ sa β£))

Using this type, we express the collection of all subalgebras of algebras in a
class by the type ``SubalgebraOfClass``, which we now define.

::

   SubalgebraOfClass : Pred (Algebra Ξ±)(ov Ξ±) β Type (ov (Ξ± β Ξ²))
   SubalgebraOfClass π¦ = Ξ£[ π© β Algebra Ξ² ] π© IsSubalgebraOfClass π¦



