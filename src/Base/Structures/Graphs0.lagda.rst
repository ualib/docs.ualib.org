.. FILE      : Base/Structures.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 22 Jun 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-structures-graph-structures-again:

Graph Structures (again)
~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Base.Structures.Graphs0`_ module of the `Agda Universal Algebra Library`_.

N.B. This module differs from `Graphs.lagda`_ in that here we assume some
universes are level zero (i.e., ``ββ``). This simplifies some things; e.g., we
avoid having to use lift and lower (cf. `Base.Structures.Graphs.lagda`_)

.. _base-structures-definition:

Definition
^^^^^^^^^^

Let ``π¨`` be an ``(π,πΉ)``-structure (relations from ``π`` and operations from ``πΉ``).
The *graph* of ``π¨`` is the structure ``Gr π¨`` with the same domain as ``π¨`` with
relations from ``π`` and together with a ``(k+1)``-ary relation symbol ``G π`` for
each ``π β πΉ`` of arity ``k``, which is interpreted in ``Gr π¨`` as all tuples ``(t
, y) β Aα΅βΊΒΉ`` such that ``π t β‘ y``.
(See also :ref:`Definition 2 of <https://arxiv.org/pdf/2010.04958v2.pdf>`__)

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Structures.Graphs0 where

  -- Imports from Agda and the Agda Standard Library -------------------------------------------
  open import Agda.Primitive  using () renaming ( Set to Type ; lzero to ββ )
  open import Data.Product    using ( _,_ ; _Γ_ ; Ξ£-syntax )
  open import Data.Sum.Base   using ( _β_ ) renaming ( injβ to inl ; injβ to inr )
  open import Data.Fin.Base   using ( Fin )
  open import Data.Nat        using ( β )
  open import Data.Unit.Base  using ( β€ ; tt )
  open import Function.Base   using ( _β_ )
  open import Relation.Unary  using ( Pred ; _β_ )
  open import Relation.Binary.PropositionalEquality
                              using ( _β‘_ ; module β‘-Reasoning ; cong ; sym ; refl )

  -- Imports from the Agda Universal Algebra Library ---------------------------------------------
  open import Overture                        using ( β£_β£ ; β₯_β₯ )
  open import Base.Relations                  using ( Rel )
  open import Base.Structures.Basic           using ( signature ; structure )
  open import Base.Structures.Homs            using ( hom ; is-hom-rel ; is-hom-op )
  open import Examples.Structures.Signatures  using ( Sβ )

  open signature ; open structure ; open _β_

  Gr-sig : signature ββ ββ β signature ββ ββ β signature ββ ββ

  Gr-sig πΉ π = record  { symbol = symbol π β symbol πΉ
                       ; arity  = ar }
   where
   ar : symbol π β symbol πΉ β Type ββ
   ar (inl π) = (arity π) π
   ar (inr π) = (arity πΉ) π β β€

  private variable πΉ π : signature ββ ββ

  Gr : structure πΉ π {ββ} {ββ} β structure Sβ (Gr-sig πΉ π) {ββ} {ββ}
  Gr {πΉ}{π} π¨ = record { carrier = carrier π¨ ; op = Ξ» () ; rel = split }
    where
    split : (s : symbol π β symbol πΉ) β Rel (carrier π¨) (arity (Gr-sig πΉ π) s) {ββ}
    split (inl π) arg = rel π¨ π arg
    split (inr π) args = op π¨ π (args β inl) β‘ args (inr tt)

  open β‘-Reasoning

  module _ {π¨ π© : structure πΉ π {ββ}{ββ}} where

   homβGrhom : hom π¨ π© β hom (Gr π¨) (Gr π©)
   homβGrhom (h , hhom) = h , (i , ii)
    where
    i : is-hom-rel (Gr π¨) (Gr π©) h
    i (inl π) a x = β£ hhom β£ π a x
    i (inr π) a x = goal
     where
     homop : h (op π¨ π (a β inl)) β‘ op π© π (h β (a β inl))
     homop = β₯ hhom β₯ π (a β inl)

     goal : op π© π (h β (a β inl)) β‘ h (a (inr tt))
     goal =  op π© π (h β (a β inl))  β‘β¨ sym homop β©
             h (op π¨ π (a β inl))    β‘β¨ cong h x β©
             h (a (inr tt))          β

    ii : is-hom-op (Gr π¨) (Gr π©) h
    ii = Ξ» ()

   Grhomβhom : hom (Gr π¨) (Gr π©) β hom π¨ π©
   Grhomβhom (h , hhom) = h , (i , ii)
    where
    i : is-hom-rel π¨ π© h
    i R a x = β£ hhom β£ (inl R) a x
    ii : is-hom-op π¨ π© h
    ii f a = goal
     where
     split : arity πΉ f β β€ β carrier π¨
     split (inl x) = a x
     split (inr y) = op π¨ f a
     goal : h (op π¨ f a) β‘ op π© f (Ξ» x β h (a x))
     goal = sym (β£ hhom β£ (inr f) split refl)


**Lemma III.1**. Let ``π`` be a signature and ``π¨`` be an ``π``-structure. Let
``β°`` be a finite set of identities such that ``π¨ β§ β°``. For every instance ``πΏ``
of CSP(``π¨``), one can compute in polynomial time an instance ``π`` of CSP(``π¨``)
such that ``π β§ β°`` and ``| hom πΏ π¨ | = | hom π π¨ |``.

**Proof**. ``β s β t`` in ``β°`` and each tuple ``b`` such that
``π© β¦ s β§ b β’ π© β¦ t β§ b``, one can compute the congruence
``ΞΈ = Cg (π© β¦ s β§ b , π© β¦ t β§ b)`` generated by ``π© β¦ s β§ b`` and
``π© β¦ t β§ b``. Let ``π©β := π© / ΞΈ``, and note that ``| π©β | < | π© |``.

We show there exists a bijection from ``hom π© π¨`` to ``hom π©β π¨``. Fix
an ``h : hom π© π¨``. For all ``s β t`` in ``β°``, we have

``h (π© β¦ s β§ b) = π¨ β¦ s β§ (h b) = π¨ β¦ t β§ (h b) = h (π© β¦ t β§ b)``.

Therefore, ``ΞΈ β ker h``, so ``h`` factors uniquely as
``h = h' β Ο : π© β (π© / ΞΈ) β π¨``, where ``Ο`` is the canonical
projection onto ``π© / ΞΈ``.

Thus the mapping ``Ο : hom π© π¨ β hom π©β π¨`` that takes each ``h`` to
``h'`` such that ``h = h' β Ο`` is injective. It is also surjective
since each ``g' : π© / ΞΈ β π¨`` is mapped back to a ``g : π© β π¨`` such
that ``g = g' β Ο``. Iterating over all identities in ``β°``, possibly
several times, at the final step we obtain a structure ``π©β`` that
satisfies ``β°`` and is such that ``β£ hom π© π¨ β£ = β£ hom π©β π¨ β£``.
Moreover, since the number of elements in the intermediate structures
decreases at each step, ``| π©α΅’ββ | < | π©α΅’ |``, the process finishes in
time that is bounded by a polynomial in the size of ``π©``.

::

  record _β_β_ (π© π¨ πͺ : structure πΉ π) : Type ββ where
   field
    to   : hom π© π¨ β hom πͺ π¨
    from : hom πͺ π¨ β hom π© π¨
    toβΌfrom : β h β (to β from) h β‘ h
    fromβΌto : β h β (from β to) h β‘ h

TODO:  Formalize Lemma III.1  
       Maybe start with something like...

::

   -- module _ {Ο : Level}{X : Type Ο}
   --          {π¨ : structure πΉ π {ββ} {ββ}} where
   -- LEMMAIII1 : {n : β}(β° : Fin n β (Term X Γ Term X))(π¨ β fMod β°)
   --  β          β(π© : structure πΉ π) β Ξ£[ πͺ β structure πΉ π ] (πͺ β fMod β° Γ (π© β π¨ β πͺ))
   -- LEMMAIII1 β° π¨β§β° π© = {!!} , {!!}


