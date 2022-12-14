.. FILE      : Base/Algebras/Basic.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 02 Jun 2022
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-algebras-basic-definitions:

Basic definitions
~~~~~~~~~~~~~~~~~

This is the `Base.Algebras.Basic`_ module of the agda-algebras_ library.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( ð ; ð¥ ; Signature )

  module Base.Algebras.Basic {ð : Signature ð ð¥ } where

  -- Imports from the Agda (Builtin) and the Agda Standard Library --------------
  open import Agda.Primitive   using () renaming ( Set to  Type ; lzero to ââ )
  open import Data.Product     using ( _,_ ; _Ã_ ; Î£-syntax )
  open import Level            using ( Level ; _â_ ; suc )
  open import Relation.Binary  using ( IsEquivalence ) renaming ( Rel to BinRel )
  open import Relation.Unary   using ( _â_ ; Pred )


  -- Imports from the Agda Universal Algebra Library ----------------------------
  open  import Overture        using ( â£_â£ ; â¥_â¥ ; Op )
  open  import Base.Relations  using ( _|:_ ; _|:pred_ ; Rel ; compatible-Rel )
                               using ( REL ; compatible-REL )

  private variable Î± Î² Ï : Level

.. _base-algebras-algebras:

Algebras
^^^^^^^^

Our first goal is to develop a working vocabulary and formal library for
classical (single-sorted, set-based) universal algebra. In this section
we define the main objects of study. An *algebraic structure* (or
*algebra*) in the signature ð = (ð¹, Ï) is denoted by
ð¨ = (A , Fá´¬) and consists of

-  A := a *nonempty* set (or type), called the *domain* (or *carrier* or *universe*) of the algebra;
-  Fá´¬ := { fá´¬ â£ f â F, : (Ïf â A) â A }, a collection of *operations* on ð¨;
-  a (potentially empty) collection of *identities* satisfied by elements and operations of ð¨.

Note that to each operation symbol f â ð¹ corresponds an operation
fá´¬ on ð¨ of arity Ïf; we call such fá´¬ the *interpretation* of the symbol
f in the algebra ð¨. We call an algebra in the signature ð an ð-*algebra*.
An algebra is called *finite* if it has a finite domain, and is called *trivial*
if its universe is a singleton.  Given two algebras ð¨ and ð©, we say that ð©
is a *reduct* of ð¨ if both algebras have the same domain and ð© can be obtained
from ð¨ by simply removing some of the operations.

Recall, we defined the type Signature ð ð¥ above as the dependent pair type
Î£ F ê Type ð , (F â Type ð¥), and the type Op of operation symbols is the
function type Op I A = (I â A) â A (see [Base.Relations.Discrete][]).

For a fixed signature ð : Signature ð ð¥ and universe level Î±, we define the
*type of algebras in the signature* ð (or *type of* ð-*algebras*) *with domain
type* Type Î± as follows.

::

  Algebra : (Î± : Level) â Type (ð â ð¥ â suc Î±)
  Algebra Î± =  Î£[ A â Type Î± ]                 -- the domain
               â (f : â£ ð â£) â Op A (â¥ ð â¥ f)  -- the basic operations

It would be more precise to refer to inhabitants of this type as
â-*algebras* because their domains can be of arbitrary type and need
not be truncated at some level and, in particular, need to be a set.
(See `Base.Equality.Truncation`_.)

We might take this opportunity to define the type of 0-*algebras*,
that is, algebras whose domains are sets, which is probably closer to
what most of us think of when doing informal universal algebra. However,
in the agda-algebras_
library we will only need to know that the domains of certain algebras
are sets in a few places, so it seems preferable to work with general
(â-)algebras throughout and then explicitly postulate additional axioms
(e.g., `uniquness of identity
proofs <https://ualib.github.io/agda-algebras/Equality.Truncation.html#uniqueness-of-identity-proofs>`__
if and only if necessary.

.. _base-algebras-algebras-as-record-types:

Algebras as record types
^^^^^^^^^^^^^^^^^^^^^^^^

A popular way to represent algebraic structures in type theory is with
record types. The Sigma type defined above provides an alternative that
morally equivalent, but technically distinct; in particular, in Agda_,
equality of inhabitants of a record type is handled differently than equality of
inhabitants of a Sigma type.

%%% LEFT OFF HERE %%%


Sigma types have the advantage of reflecting the existential quantifier of
logic. Recall that the type ``Î£ x ê X , P x`` represents the proposition, âthere exists ``x`` in
``X`` such that ``P x`` holds;â in symbols, ``â x â X , P x``. Indeed,
an inhabitant of ``Î£ x ê X , P x`` is a pair ``(x , p)`` such that ``x``
inhabits ``X`` and ``p`` is a proof of ``P x``. In other terms, the pair
``(x , p)`` is a witness and proof of the proposition ``â x â X , P x``.

Nonetheless, for those who prefer to represent algebraic structures in
type theory using records, we offer the following definition (which is
equivalent to the Sigma type formulation).

::

  record algebra (Î± : Level) : Type(suc(ð â ð¥ â Î±)) where
   constructor mkalg
   field
    carrier : Type Î±
    opsymbol : (f : â£ ð â£) â ((â¥ ð â¥ f) â carrier) â carrier

This representation of algebras as inhabitants of a record type is
equivalent to the representation using Sigma types in the sense that a
bi-implication between the two representations is obvious.

::

  open algebra

  algebraâAlgebra : algebra Î± â Algebra Î±
  algebraâAlgebra ð¨ = (carrier ð¨ , opsymbol ð¨)

  Algebraâalgebra : Algebra Î± â algebra Î±
  Algebraâalgebra ð¨ = mkalg â£ ð¨ â£ â¥ ð¨ â¥


.. _base-algebras-operation-interpretation-syntax:

Operation interpretation syntax
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We now define a convenient shorthand for the interpretation of an
operation symbol. This looks more similar to the standard notation one
finds in the literature as compared to the double bar notation we
started with, so we will use this new notation almost exclusively in the
remaining modules of the agda-algebras_ library.

::

  _Ì_ : (ð : â£ ð â£)(ð¨ : Algebra Î±) â (â¥ ð â¥ ð  â  â£ ð¨ â£) â â£ ð¨ â£

  ð Ì ð¨ = Î» ð â (â¥ ð¨ â¥ ð) ð


So, if ``ð : â£ ð â£`` is an operation symbol in the signature ``ð``, and
if ``ð : â¥ ð â¥ ð â â£ ð¨ â£`` is a tuple of the appropriate arity, then
``(ð Ì ð¨) ð`` denotes the operation ``ð`` interpreted in ``ð¨`` and
evaluated at ``ð``.

.. _base-algebras-the-universe-level-of-an-algebra:

The universe level of an algebra
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Occasionally we will be given an algebra and we just need to know the
universe level of its domain. The following utility function provides
this.

::

  Level-of-Alg : {Î± : Level} â Algebra Î± â Level
  Level-of-Alg {Î± = Î±} _ = ð â ð¥ â suc Î±

  Level-of-Carrier : {Î± : Level} â Algebra Î± â Level
  Level-of-Carrier {Î± = Î±} _ = Î±


.. _base-algebras-level-lifting-algebra-types:

Level lifting algebra types
^^^^^^^^^^^^^^^^^^^^^^^^^^^

Recall, in the `section on level lifting and lowering`_, we
described the difficulties one may encounter when working with a
noncumulative universe hierarchy. We made a promise to provide some
domain-specific level lifting and level lowering methods. Here we
fulfill this promise by supplying a couple of bespoke tools designed
specifically for our operation and algebra types.

::

  open Level

  Lift-alg-op : {I : Type ð¥} {A : Type Î±} â Op A I â (Î² : Level) â Op (Lift Î² A) I
  Lift-alg-op f Î² = Î» x â lift (f (Î» i â lower (x i)))

  Lift-Alg : Algebra Î± â (Î² : Level) â Algebra (Î± â Î²)
  Lift-Alg ð¨ Î² = Lift Î² â£ ð¨ â£ , (Î» (ð : â£ ð â£) â Lift-alg-op (ð Ì ð¨) Î²)

  open algebra

  Lift-algebra : algebra Î± â (Î² : Level) â algebra (Î± â Î²)
  Lift-algebra ð¨ Î² = mkalg (Lift Î² (carrier ð¨)) (Î» (f : â£ ð â£) â Lift-alg-op ((opsymbol ð¨) f) Î²)

What makes the ``Lift-Alg`` type so useful for resolving type level
errors involving algebras is the nice properties it possesses. Indeed,
the agda-algebras_ library contains formal proofs of the following
facts.

-  ```Lift-Alg`` is a
   homomorphism <base-homomorphisms-basic-exmples-of-homomorphisms>`__
   (see `Base.Homomorphisms.Basic`_)
-  ```Lift-Alg`` is an algebraic
   invariant <base-homomorphisms-isomorphisms-lift-is-an-algebraic-invariant%22>`__
   (see `Base.Homomorphisms.Isomorphisms`_)
-  ```Lift-Alg`` of a subalgebra is a
   subalgebra <Base.Subalgebras.Subalgebras.html#lifts-of-subalgebras>`__
   (see `Base.Subalgebras.Subalgebras`_)
-  ```Lift-Alg`` preserves
   identities <Base.Varieties.EquationalLogic.html#lift-invariance>`__)
   (see `Base.Varieties.EquationalLogic`_)

.. _base-algebras-compatibility-of-binary-relations:

Compatibility of binary relations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We now define the function ``compatible`` so that, if ``ð¨`` denotes an
algebra and ``R`` a binary relation, then ``compatible ð¨ R`` will
represent the assertion that ``R`` is *compatible* with all basic
operations of ``ð¨``. The formal definition is immediate since all the
work is done by the relation ``|:``, which we defined above (see
`Base.Relations.Discrete`_).

::

  compatible : (ð¨ : Algebra Î±) â BinRel â£ ð¨ â£ Ï â Type (ð â ð¥ â Î± â Ï)
  compatible  ð¨ R = â ð â (ð Ì ð¨) |: R

  compatible-pred : (ð¨ : Algebra Î±) â Pred (â£ ð¨ â£ Ã â£ ð¨ â£)Ï â Type (ð â ð¥ â Î± â Ï)
  compatible-pred  ð¨ P = â ð â (ð Ì ð¨) |:pred P

Recall, the ``|:`` type was defined in `Base.Relations.Discrete`_ module.

.. _base-algebras-compatibility-of-continuous-relations:

Compatibility of continuous relations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In the `Base.Relations.Continuous`_ module, we defined a function
called ``compatible-Rel`` to represent the assertion that a given
continuous relation is compatible with a given operation. With that, it
is easy to define a function, which we call ``compatible-Rel-alg``,
representing compatibility of a continuous relation with all operations
of an algebra. Similarly, we define the analogous ``compatible-REL-alg``
function for the (even more general) type of *dependent relations*.

::

  module _ {I : Type ð¥} where

   compatible-Rel-alg : (ð¨ : Algebra Î±) â Rel â£ ð¨ â£ I{Ï} â Type(ð â Î± â ð¥ â Ï)
   compatible-Rel-alg ð¨ R = â (ð : â£ ð â£ ) â  compatible-Rel (ð Ì ð¨) R

   compatible-REL-alg : (ð : I â Algebra Î±) â REL I (Î» i â â£ ð  i â£) {Ï} â Type(ð â Î± â ð¥ â Ï)
   compatible-REL-alg ð R = â ( ð : â£ ð â£ ) â  compatible-REL (Î» i â ð Ì (ð i)) R

