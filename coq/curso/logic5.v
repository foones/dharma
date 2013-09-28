(** * The Computational View of Proofs
    *** Version of 11/4/2008
*)

(* By this point, we've seen and used many specific features
   of Coq.  This chapter paints a "big picture" that puts
   these specifics in context.
*)

Require Export logic4. 

(*
COQ'S TWO UNIVERSES
-------------------

Coq divides the world into two distinct universes:
   - [Set] is the universe of COMPUTATIONS and DATA
   - [Prop] is the universe of LOGICAL ASSERTIONS and EVIDENCE

The two universes have some deep similarities -- in each, we
can talk about values, inductive definitions,
quantification, etc. -- but there are some technical
differences; more importantly, they play quite different
roles in the way we define and reason about mathematical
structures.

(Technically, there is another universe called [Type] that
subsumes both [Set] and [Prop].  This is handy for stating
definitions that we want to work equally well for both.)


VALUES
------

Both universes begin with an infinite set of CONSTRUCTORS.
Constructors have no internal structure: they are just
"tags", and all we can do with them is tell whether they are
the same or different.  Examples:
  - [true], [false], [O], [S], [nil], [cons], [even_0],
    [even_SS], [conj], ...

The simplest VALUES are trees of constructor applications.
Their leaves are nullary constructors (applied to no
arguments), and internal nodes are applications of
constructors to one or more values.  Examples:
  - [true]
  - [O] 
  - [S (S (S O))]
  - [even_0]
  - [even_SS 0 even_0]
  - [even_SS (S (S O)) (even_SS 0 even_0)]

In the universe [Set], we think of values as DATA (belonging
to certain sets).  In [Prop], we think of values as
EVIDENCE (that prove certain propositions).

Values consisting entirely of constructor applications can
be thought of as TREES.  In [Prop], such trees are called
DERIVATION TREES.

[Inductive] declarations give names to subsets of the set of
all values.  For example, the declaration of the inductive
type [nat] defines a SET whose ELEMENTS are values
representing natural numbers.  That is, it picks out a
subset [nat] of the set of all values that satisfies the
following properties:
  - the value [O] is in this set
  - the set is CLOSED under applications of [S] (i.e., if a
    value [n] is in the set, then [S n] is too)
  - it is the smallest set satisfying these
    conditions (i.e., the only values in [nat] are the ones
    that MUST be, according to the previous two
    conditions... there is no other "junk").

Sets themselves are also values and can appear as arguments
to constructors in compound values.  Examples: [Possible
confusion: nil is usually written [], not @nil X.]
  - [nat]
  - [@nil nat]
  - [cons nat O (cons nat (S O) (@nil nat))]

Also, we can write functions that take sets as arguments and
return sets as results.  For example, [list] is a function
of type [Set->Set]: it takes a set [X] as argument and
returns as result the set [list X] (whose members are lists
with elements drawn from [X]).

Similarly, the declaration of the inductive type [evenI]
defines a FAMILY OF SETS whose ELEMENTS are values
representing evidence that numbers are even.  That is, for
each [n], the definition picks out a subset [evenI n] of the
set of all values satisfying the following properties:
  - the value [even_0] is in the set [evenI O]
  - the sets are CLOSED under well-typed applications of
    [even_SS] -- i.e., if [e] is in the set [evenI n], then
    [even_SS n e] is in the set [evenI (S (S n))]
  - it is the smallest family of sets satisfying these
    conditions (i.e., the only values in any set [evenI n]
    are the ones that MUST be, according to the previous two
    conditions... there is no other junk).


EXAMPLE: The [square_of] Relation
---------------------------------

Recall the inductive definition of the [square_of] relation:

  Inductive square_of : nat -> nat -> Prop :=
    sq : forall n:nat, square_of n (times n n).

This definition can be read as follows:
   - We are defining (inductively) a family of sets of
     values (in [Prop]) that we are going to consider as
     evidence for propositions of the form [square_of n
     m] -- that is "[m] is the square of [n]."
   - For every number [n], there is one way to construct
     evidence for [square_of n (times n n)]: by applying the
     constructor [sq] to [n] and [times n n].  That is,
     whenever [m] is the square of [n], we have a way of
     constructing evidence of [square_of n m].
   - For [m] and [n] where [m] is NOT the square of [n], we
     have no way of building elements of the type [square_of
     n m].


FUNCTIONS AND QUANTIFIERS
-------------------------

The types [A->B] and [forall x:A, B] both describe functions
from [A] to [B].  The only difference is that, in the second
case, the expression [B] -- the type of the result -- can
mention the argument [x] by name.  For example:

   - The function [fun x:nat => plus x x] has type
     [nat->nat] -- that is, it maps each number [n] to a
     number.
   - The function [fun X:Set => @nil (list X)] has type
     [forall X:Set, list (list X)] -- that is, it maps each
     set [X] to a particular list of lists of [X]s.
     [Possible confusion: nil is usually written [], not @nil
     X.]

In fact, the two ways of writing function types are really
the same: In Coq, [A->B] is actually just an abbreviation
for [forall x:A, B], where [x] is some variable name not
occurring in [B].  For example, the type of [fun x:nat =>
plus x x] can be written, if we like, as [forall x:nat,
nat].


FUNCTIONS AND IMPLICATIONS
--------------------------

In both [Set] and [Prop], we can write functions that
transform values into other values.  Also, functions
themselves are values; this means we can
  - write higher-order functions that take functions as
    arguments or return functions as results, and
  - apply constructors to functions to build complex values
    containing functions.

A function of type [P->Q] in [Prop] is something that takes
evidence for [P] as an argument and yields evidence for [Q]
as its result.  Such a function can be regarded as EVIDENCE
that [P] implies [Q], since, whenever we have evidence that
[P] is true, we can apply the function and get back evidence
that [Q] is true: evidence for an implication is a function
on evidence.  This is why we use the same notation for
functions and logical implications in Coq: they are exactly
the same thing!

This coincidence between functions and implications is an
instance of a deep connection between programming languages
and mathematical logic known as the CURRY-HOWARD
CORRESPONDENCE:

Types correspond to Propositions
Terms correspond to Proofs

*)

(* One place that the functional nature of application is
can be put to practical use is when we need to specialize
a lemma or hypothesis, particularly when doing forward 
reasoning.   Here's a characteristic example: *)

Lemma cons_snoc : forall (X:Set) (x:X) xs, 
                  exists y, exists ys, x::xs = snoc ys y.
intros X x xs. generalize dependent x. induction xs. 
  Case "nil".
    intros x.  exists x. exists (@nil X). auto.  
  Case "cons".
    intros x0.  
    assert (exists y, exists ys, x::xs = snoc ys y).  
    (* annoying! *)
       apply IHxs. 
    destruct H as [y H']. destruct H' as [ys H''].
    exists y. exists (x0::ys). simpl. rewrite H''. auto.
Qed.

Lemma cons_snoc' : forall (X:Set) (x:X) xs, 
                   exists y, exists ys, x::xs = snoc ys y.
intros X x xs. generalize dependent x. induction xs. 
  Case "nil".
    intros x.  exists x. exists (@nil X). auto.  
  Case "cons".
    intros x0.
    destruct (IHxs x) as [y H']. destruct H' as [ys H''].
    (* or just: 
    destruct (IHxs x) as [y [ys H'']].
    *)
   exists y. exists (x0::ys). simpl. rewrite H''. auto.
Qed.


(* It is sometimes useful or enlightening to work directly with
proof terms (functions that manipulate evidence) rather than with 
tactic-driven proofs. 

We can use the [Print] command to show an inductive
definition or to print a proof term.  For 
simple proofs, these are not too hard to understand. *)

Print or.

Lemma or_sym : forall P Q, P \/ Q -> Q \/ P.
intros P Q A.  destruct A. right. apply H. left. apply H. 
Qed.

Print or_sym. 

(* This lemma is proved by a combination of pattern matching
on, and construction of, values in the [or] inductive type. *)

(* We can also prove simple theorems directly by providing the
necessary proof term. *)

Print conj.

Definition and_sym : forall P Q,  P /\ Q -> Q /\ P :=
 fun (P Q : Prop) (A: P /\ Q) =>
 match A with
 | conj H1 H2 => conj Q P H2 H1
 end.


(* In practice, we don't do this much, because it's much
easier to build proofs using tactics.   The proofs themselves
can get huge and perhaps ugly. *)

Print le_antisymmetric. 

(* But sometimes the ability to write a proof term directly is
very handy.  Consider the induction principle on naturals.
Recall that Coq generates this for us automatically from the
Inductive declation for [nat].  But there's nothing magic about
the induction lemma: it's just another Coq lemma that requires a
proof.  Coq generates the proof automatically too...
 *)

Check nat_ind.
Print nat_ind. 
Print nat_rect.

(* We can read this as follows: 
   Suppose we have evidence:
   f: P holds on 0,  and 
   f0 : forall n:nat, P n -> P (S n).  
   Then we can prove that P holds of an arbitrary nat n via 
   a recursive function F that pattern matches on n: 
     - If it finds 0, F uses f to show that P n holds.
     - If it finds S n0, F applies itself recursively on n0 
        to obtain evidence that P n holds; then it applies f0 
        on that evidence to show that P (S n) holds. 
   F is just an ordinary recursive function that happens to 
   operate on evidence in Prop rather than on terms in Set.

   Aside to those interested in functional programming: 
   You may notice that the [match] in F requires
   an annotation [as n0 return (P n0)] to help Coq's 
   typechecker realize that    the two arms of the [match] 
   actually return the same type (namely [P n]).
   This is essentially like matching over a GADT in Haskell. 
   In fact, F has a DEPENDENT type: its result type depends 
   on its argument; GADT's can be used to describe simple 
   dependent types like this. 
*)
      

(* We can adapt this approach to proving [nat_ind] to help prove 
   *NON-STANDARD* induction principles too.  Recall our desire to 
   prove that

forall n : nat,  evenE n -> evenI n.

Attempts to do this by standard induction on [n] fail, because the
induction principle only lets us proceed when we can prove that evenE
n -> evenE (S n) --- which is of course never provable.  What we did
before was a hack:

Lemma evenE_evenI : forall n : nat,
  (evenE n -> evenI n) /\ (evenE (S n) -> evenI (S n)).

We can make a much better proof by defining and proving a non-standard
induction principle that goes "by twos":

*)

Definition nat_ind2 : 
   forall (P : nat -> Prop), 
   P 0 -> 
   P 1 -> 
   (forall n : nat, P n -> P (S(S n))) -> 
   forall n : nat , P n :=
      fun P => fun P0 => fun P1 => fun PSS => 
         fix f (n:nat) := match n return P n with 
                            0 => P0 
                          | 1 => P1 
                          | S (S n') => PSS n' (f n') 
                         end.
 

(* Once you get the hang of it, it is entirely straightforward to give
an explicit proof term for induction principles like this.  Proving
this as a lemma using tactics is much less intuitive -- try it! *)
   

(* The [induction ... using] tactic gives a convenient way to specify
   a non-standard induction principle. *)

Lemma evenE_evenI' : forall n, evenE n -> evenI n.
intros.  
induction n using nat_ind2. 
 apply even_0.  
 inversion H.
 apply even_SS. 
   auto.
Qed. 

(* **** The Coq Trusted Computing Base ****

One issue that arises with any automated proof assistant is "why trust
it"?  What if there is a bug in the implementation of the prover that
renders all its reasoning suspect?

While it is impossible to allay such concerns completely, provers that
-- like Coq -- are based on the Curry-Howard Correspondence have a
significant advantage. Because propositions are just types and proofs
are just terms, checking that an alleged proof of a proposition is
valid just amounts to TYPE-CHECKING the term.  Type checkers are
relatively small and straightforward to write, so the "trusted
computing base" for Coq -- the part of the code that we have to
believe is operating correctly -- is small too.

What must a typechecker do?  Its primary job is to make sure that in
each function application the expected and actual argument types
match, that the arms of a [match] expression are constructor patterns
belonging to the inductive type being matched over and that all arms
return the same type, and so on.

There are a few additional wrinkles:

- The checker must make sure that [match] expressions are EXHAUSTIVE.
That is, there must be an arm for every possible constructor.
To see why, consider the following alleged proof:

Definition or_bogus : forall P Q, P \/ Q -> P :=
fun (P Q : Prop) (A : P \/ Q) =>
match A with
| or_introl H => H
end.

All the types here match correctly, but the [match] only considers
one of the possible constructors for [or].  

- The checker must make sure that each [fix] expression terminates.
It does this using a syntactic check to make sure that each recursive
call is on a subexpression of the original argument.  To see why this
is essential, consider the alleged proof:

Definition nat_false : forall (n:nat), False :=
        fix f (n:nat) : False := f n.
 
Again, this is perfectly well-typed, but (fortunately) Coq will reject
it.

*** PROOFS vs. TACTIC SCRIPTS. ***

Note that the soundness of Coq depends only on the correctness of this
typechecking engine, not on the tactic machinery.  If there is a bug
in a tactic implementation (and this certainly does happen!), that
tactic might construct an invalid proof term.  But when you type
[Qed], Coq checks the term for validity from scratch.  Only lemmas
whose proofs pass the type-checker can be used in further proof
developments.  *)



