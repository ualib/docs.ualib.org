.. FILE      : Base/Complexity/CSP.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 26 Jul 2021
.. UPDATED   : 02 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-complexity-constraint-satisfaction-problems:

Constraint Satisfaction Problems
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Base.Complexity.CSP`_ module of the `Agda Universal Algebra Library`_.

.. _base-complexity-the-relational-formulation-of-csp:

The relational formulation of CSP
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Let ๐ = (๐ด , ๐แต) be a *relational structure* (or ๐-structure), that is, a pair
consisting of a set ๐ด along with a collection ๐แต โ โโ ๐ซ(๐ดโฟ) of relations on ๐ด.

We associate with ๐ a *constraint satisfaction problem* denoted by CSP(๐), which
is the decision problem that is solved by finding an algorithm or program that
does the following:

Take as input

-  an *instance*, which is an ๐-structure โฌ = (๐ต , ๐แต) (in the same signature as ๐)

Output

-  "yes" or "no" according as there is, or is not, a *solution*, which is a
   ๐-structure homomorphism h : โฌ โ ๐.

If there is such an algorithm that takes at most a power of ๐ operations to
process an input structure โฌ of size ๐ (i.e., ๐ bits of memory are required to
encode โฌ), then we say that CSP(๐) is *tractable*. Otherwise, CSP(๐) is
*intractable*.

Equivalently, if we define

CSP(๐) := { โฌ โฃ โฌ an ๐-structure and โ hom โฌ โ ๐ }

then the CSP problem described above is simply the membership problem for the
subset CSP(๐) of ๐ structures having homomorphisms into ๐.

That is, our algorithm must take as input an ๐-structure (a relational structure
in the signature of ๐) and decide whether or not it belongs to the set CSP(๐).

.. _base-complexity-connection-to-algebraic-csp:

Connection to algebraic CSP
^^^^^^^^^^^^^^^^^^^^^^^^^^^

Let A be a set, let Op(A) denote the set of all operations, Rel(A) the set of all relations, on A.

Given R โ Rel(A), define the set of operations on A that preserve all
relations in R as follows:

โฃ: โ R = { f โ Op(๐ด) โฃ โ r โ R, f โฃ: r }.

Recall, f โฃ: r is our notation for ``f Preserves r โถ r``, which means that r is a
subuniverse of a power of the algebra (A , {f}).

Equivalently, ``f Preserves r โถ r means`` the following: if f is ๐-ary and r is
๐-ary, then for every size-๐ collection ๐๐? of ๐-tuples from r (that is, โฃ ๐๐? โฃ = ๐
and โ a โ ๐๐?, r a) we have r (f โ (zip ๐๐?)).

If ๐ = (A , R) is a relational structure, then the set โฃ: โR of operations on A
that preserve all relations in R is called the set of *polymorphisms* of ๐.

Conversely, starting with a collection F โ Op(A) of operations on A, define the
set of all relations preserved by the functions in F as follows:

F โ โฃ: = { r โ Rel(A) โฃ โ f โ F, f โฃ: r }.

It is easy to see that for all F โ Op(A) and all R โ Rel(A), we have

F โ โฃ: โ (F โ โฃ:) and R โ (โฃ: โ R) โ โฃ:.

Let ๐จ(R) denote the algebraic structure with domain A and operations โฃ: โ R.

Then every r โ R is a subalgebra of a power of ๐จ(R).

Clearly (โฃ: โ R) โ โฃ: is the set ๐ฒ (๐ฏfin ๐จ(R)) of subalgebras of finite powers of
๐จ(R).

The reason this Galois connection is useful is due to the following fact (observed
by Peter Jeavons in the late 1990's):

*Theorem*. Let ๐ = (A, R) be a finite relational structure. If Rโ โ (โฃ: โ R) โ โฃ: is
finite, then CSP((A, ฮโ)) is reducible in poly-time to CSP(๐)

In particular, the tractability of CSP(๐) depends only on its associated
polymorphism algebra, ๐จ(R) := (A , โฃ: โ R).

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( ๐ ; ๐ฅ ; Signature )

  module Base.Complexity.CSP {๐ : Signature ๐ ๐ฅ} where

  -- Imports from Agda and the Agda Standard Library ------------------------------
  open import Agda.Primitive   using ( _โ_ ; lsuc ; Level) renaming ( Set to Type )
  open import Function.Base    using ( _โ_ )
  open import Relation.Binary  using ( Setoid )

  -- Imports from the Agda Universal Algebra Library ------------------------------
  open import Base.Relations.Continuous       using ( REL ; REL-syntax )
  open import Setoid.Algebras.Basic  {๐ = ๐}  using ( Algebra )

.. _base-complexity-constraints:

Constraints
^^^^^^^^^^^

A constraint c consists of

1. a scope function, s : I โ var, and

2. a constraint relation, i.e., a predicate over the function type I โ D

   .. code::

       I ยทยทยท> var
        .     .
         .   .
          โ โ
           D

The *scope* of a constraint is an indexed subset of the set of variable
symbols. We could define a type for this, e.g.,

.. code:: agda

    Scope : Type ฮฝ โ Type ฮน โ _
    Scope V I = I โ V

but we omit this definition because itโs so simple; to reiterate, a
scope of "arity" I on "variables" V is simply a map from I to V, where,

-  I denotes the "number" of variables involved in the scope
-  V denotes a collection (type) of "variable symbols"

::

  module  _              -- levels for...
          {ฮน : Level}    -- ...arity (or argument index) types
          {ฮฝ : Level}    -- ...variable symbol types
          {ฮฑ โ : Level}  -- ... domain types
   where
   open Setoid
   record Constraint (var : Type ฮฝ) (dom : var โ Setoid ฮฑ โ) : Type (ฮฝ โ ฮฑ โ lsuc ฮน) where
    field
     arity  : Type ฮน               -- The "number" of variables involved in the constraint.
     scope  : arity โ var          -- Which variables are involved in the constraint.
     rel    : REL[ i โ arity ] (Carrier (dom (scope i)))   -- The constraint relation.

    satisfies : (โ v โ Carrier (dom v)) โ Type  -- An assignment ๐ : var โ dom of values to variables
    satisfies f = rel (f โ scope)      -- *satisfies* the constraint ๐ถ = (ฯ , ๐) provided
                                      -- ๐ โ ฯ โ ๐, where ฯ is the scope of the constraint.

.. _base-complexity-csp-templates-and-instances:

CSP templates and instances
^^^^^^^^^^^^^^^^^^^^^^^^^^^

A CSP "template" restricts the relations that may occur in instances of the
problem. A convenient way to specify a template is to give an indexed family
๐ : var โ Algebra ฮฑ ฯ of algebras (one for each variable symbol in var) and
require that relations be subalgebras of the product โจ var ๐.

To construct a CSP instance, then, we just have to give a family ๐ of algebras,
specify the number (ar) of constraints, and for each i : ar, define a constraint
as a relation over (some of) the members of ๐.

An instance of a constraint satisfaction problem is a triple ๐ = (๐, ๐ท, ๐ถ) where

-  ๐ denotes a set of "variables"
-  ๐ท denotes a "domain",
-  ๐ถ denotes an indexed collection of constraints.

::

   open Algebra
   open Setoid
   record CSPInstance (var : Type ฮฝ)(๐ : var โ Algebra ฮฑ โ) : Type (ฮฝ โ ฮฑ โ lsuc ฮน) where
    field
     ar : Type ฮน       -- ar indexes the contraints in the instance
     cs : (i : ar) โ Constraint var (ฮป v โ Domain (๐ v))

    isSolution : (โ v โ Carrier (Domain (๐ v))) โ Type _  -- An assignment *solves* the instance
    isSolution f = โ i โ (Constraint.satisfies (cs i)) f  -- if it satisfies all the constraints.

