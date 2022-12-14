.. FILE      : Base/Structures/Graphs.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 22 Jun 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-structures-graph-structures:

Graph Structures
~~~~~~~~~~~~~~~~

This is the `Base.Structures.Graphs`_ module of the `Agda Universal Algebra Library`_.


N.B. This module differs from `Base.Structures.0Graphs0`_ in that this module is universe
polymorphic; i.e., we do not restrict universe levels (to, e.g., ``ββ``). This
complicates some things; e.g., we must use lift and lower in some places (cf.
`Base.Structures.Graphs0`_). 

**Definition** (Graph of a structure). Let ``π¨`` be an ``(π, πΉ)``-structure
(relations from ``π`` and operations from ``πΉ``). The *graph* of ``π¨`` is the
structure ``Gr π¨`` with the same domain as ``π¨`` with relations from ``π``
together with a (``k+1``)-ary relation symbol ``G π`` for each ``π β πΉ`` of arity
``k``, which is interpreted in ``Gr π¨`` as all tuples ``(t , y) β Aα΅βΊΒΉ`` such that
``π t β‘ y``. (See also Definition 2 of :ref:`this paper <https://arxiv.org/pdf/2010.04958v2.pdf)>`__.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Structures.Graphs where

  -- imports from Agda and the Agda Standard Library -------------------------------------------
  open import Agda.Primitive  using () renaming  ( Set to Type ; lzero  to ββ )
  open import Data.Product    using ( _,_ ; Ξ£-syntax ; _Γ_ )
  open import Data.Sum.Base   using ( _β_ ) renaming  ( injβ to inl ; injβ to inr )
  open import Data.Unit.Base  using ( β€ ; tt )
  open import Level           using (  _β_ ; Level ; Lift ; lift ; lower )
  open import Function.Base   using ( _β_  )
  open import Relation.Binary.PropositionalEquality as β‘
                              using ( _β‘_ ; module β‘-Reasoning )

  -- Imports from the Agda Universal Algebra Library ---------------------------------------------
  open import Overture               using ( β£_β£ ; β₯_β₯ )
  open import Base.Relations         using ( Rel )
  open import Base.Structures.Basic  using ( signature ; structure )
  open import Base.Structures.Homs   using ( hom ; β-hom ; is-hom-rel ; is-hom-op)
  open import Examples.Structures.Signatures  using ( Sβ )

  open signature ; open structure ; open _β_

  Gr-sig : signature ββ ββ β signature ββ ββ β signature ββ ββ

  Gr-sig πΉ π = record  { symbol = symbol π β symbol πΉ
                       ; arity  = ar
                       }
   where
   ar : symbol π β symbol πΉ β Type _
   ar (inl π) = (arity π) π
   ar (inr π) = (arity πΉ) π β β€

  private variable
   πΉ π : signature ββ ββ
   Ξ± Ο : Level

  Gr : β{Ξ± Ο} β structure πΉ π {Ξ±} {Ο} β structure Sβ (Gr-sig πΉ π) {Ξ±} {Ξ± β Ο}
  Gr {πΉ}{π}{Ξ±}{Ο} π¨ = record { carrier = carrier π¨ ; op = Ξ» () ; rel = split }
    where
    split : (s : symbol π β symbol πΉ) β Rel (carrier π¨) (arity (Gr-sig πΉ π) s) {Ξ± β Ο}
    split (inl π) arg = Lift Ξ± (rel π¨ π arg)
    split (inr π) args = Lift Ο (op π¨ π (args β inl) β‘ args (inr tt))

  open β‘-Reasoning

  private variable Οα΅ Ξ² Οα΅ : Level

  module _ {π¨ : structure πΉ π {Ξ±} {Οα΅}} {π© : structure πΉ π {Ξ²} {Οα΅}} where

   homβGrhom : hom π¨ π© β hom (Gr π¨) (Gr π©)
   homβGrhom (h , hhom) = h , (i , ii)
    where
    i : is-hom-rel (Gr π¨) (Gr π©) h
    i (inl π) a x = lift (β£ hhom β£ π a (lower x))
    i (inr π) a x = lift goal
     where
     homop : h (op π¨ π (a β inl)) β‘ op π© π (h β (a β inl))
     homop = β₯ hhom β₯ π (a β inl)

     goal : op π© π (h β (a β inl)) β‘ h (a (inr tt))
     goal =  op π© π (h β (a β inl))  β‘β¨ β‘.sym homop β©
             h (op π¨ π (a β inl))    β‘β¨ β‘.cong h (lower x) β©
             h (a (inr tt))          β

    ii : is-hom-op (Gr π¨) (Gr π©) h
    ii = Ξ» ()

   Grhomβhom : hom (Gr π¨) (Gr π©) β hom π¨ π©
   Grhomβhom (h , hhom) = h , (i , ii)
    where
    i : is-hom-rel π¨ π© h
    i R a x = lower (β£ hhom β£ (inl R) a (lift x))
    ii : is-hom-op π¨ π© h
    ii f a = goal
     where
     split : arity πΉ f β β€ β carrier π¨
     split (inl x) = a x
     split (inr y) = op π¨ f a
     goal : h (op π¨ f a) β‘ op π© f (Ξ» x β h (a x))
     goal = β‘.sym (lower (β£ hhom β£ (inr f) split (lift β‘.refl)))

