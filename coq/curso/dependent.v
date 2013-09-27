(* Mixing Prop and Set for fun and profit *)

Require Import opsem4.
Require Import midterm.
Require Import pigeon.


(* Thanks to Adam Chlipala's new book-in-progress

"Certified Programming with Dependent Types"

http://adam.chlipala.net/cpdt/

*)


(* We have seen that inductive definitions work uniformly to build
values in Prop and Set.  So far we've kept these two worlds 
fairly separate.  But Coq allows us to mix and match them quite flexibly. 
We can include Prop's as components of Set's, and 
Set's as components of Prop's, and both of these can be useful.*)

(****************** [sumbool] *************************)

Module sumbool.

(* Let's start by considering Prop's within Set's. One useful application
of this has to do with decidable (that is, computable) equalities.
Remember that we have a powerful and general equality *predicate* written
with [=], but we can't use this to compute within a function.  On the
other hand, we've defined type-specific computable equality functions that
return values in type [bool], e.g. [beq_nat]. *)

About beq_nat.

(* While [beq_nat] is fine for computing with, it is somewhat awkward to 
prove things about, because:

(a) When we [destruct] over [beq_nat n m] we lose information about the 
relationship between n and m.  We can use [remember] to keep this information,
but..
(b) We still have to do extra work to turn [beq_nat n m = true] into something
we can use for rewriting, i.e. [n=m]. 

Here's an example:

*)

Definition sillyfun4 (n : nat) : nat :=
  if beq_nat n 3 then n+1
  else if beq_nat n 5 then n-1
  else 4.

Lemma sillyfun4_is_4 : forall (n : nat),
  sillyfun4 n = 4.
Proof.
  intros n. unfold sillyfun4. 
  remember (beq_nat n 3) as e. destruct e.
    Case "true".
      apply sym_eq in Heqe. 
      apply beq_nat_true in Heqe. 
      rewrite Heqe. auto.
    Case "false".
      remember (beq_nat n 5) as e. destruct e.
      SCase "true".
        apply sym_eq in Heqe0. 
        apply beq_nat_true in Heqe0. 
        rewrite Heqe0. auto.
      SCase "false". reflexivity.
Qed.


(* An alternative approach that is often used in Coq is to define
a type of booleans with attached Props. *)


Inductive sumbool (A B:Prop) : Set :=
  | left : A -> sumbool A B
  | right : B -> sumbool A B.

Notation "{ A } + { B }" := (sumbool A B) : type_scope.

(* A value of type [sumbool A B] is *either* a proof of A *or*
a proof of B.  Moreover, the tags [left] and [right] indicate
which proof is present.  Ordinarily, we instantiate A and B
with some predicate P and its negation ~P.  Then the [sumbool]
value can be viewed as a boolean with an attached proof; hence
its name.

To use the type {P}+{~P}, we need to be able to come up with such 
a proof object.  This amounts to proving that P is *decidable*, 
that is, that there's a constructive method proving that either P
or ~P holds. We can actually compute with this method too, 
making essential use of the underlying "pun" between proofs and
data.  

In principle, there are several ways to achieve this, the 
most direct being to write down an appropriate proof term directly.
In practice, this is prohibitively complicated in most cases,
for most people (though apparently not Adam Chlipala!)

In practice, the best approach is nearly always to use tactics 
to build the proof just as usual.  Here's an example for 
equality on [nat].  *)

Definition eq_nat_dec : forall (m n :nat), {m = n} + {m <> n}.
Proof.
  induction m; destruct n.
  left. reflexivity.
  right. intro. inversion H.
  right. intro. inversion H. 
  destruct (IHm n). 
    left. auto. 
    right. intro. inversion H. apply n0. apply H1. 
Defined.

(* By the way, note that this proof depends crucially on fact that we
are comparing [nat]s. In fact, there's no way to prove a generic
result of this kind this kind over all types -- a good thing, since it
isn't true for, e.g. functions!

But notice a couple of unusual things here.  First, we've used
the keyword [Definition], but then we've concluded it with a period
without giving a [:=] and body.  Used like this, [Definition] is 
essentially a synonym for [Lemma]: it causes Coq to establish
a goal and enter interactive proof mode expecting tactics.
In this case the goal simply asserts that we can construct
a value of the desired [sumbool] type.  

The other unusual feature is that we have terminated the proof
with the keyword [Defined] rather than [Qed].  Using [Defined]
makes the proof "transparent," which enables it to be used
computationally.  If we used [Qed], the proof would be "opaque."
Opaque proofs are fine when we don't care *how* something is
proved, but here that is crucial. 

You may be worried at this point.  Surely it is not enough to
prove that a [sumbool] value always exists: it is crucial that
it be the correct value!  Moreover, we would like that value
to be computed in the "obvious" way by recursive pattern
matching over [m] and [n], analogously to [beq_nat]. 

To see what [eq_nat_dec] looks like computationally, we can 
[Print] it : *)

Print eq_nat_dec.

(* This is a bit daunting!  But we can see that the rough outlines 
of the computation look like what we'd expect, although they are
obscured by all the details of proof manipulation. 

One way to cut through these details and get a quick idea of
the computational content of a proof like this is to *extract*
it.  Extraction is a Coq facility for turning proof or program terms
into executable OCaml (or Haskell) code.  It strips off everything
to do with [Prop] and leaves just the underlying [Set] computation. 
Normally one does extraction into a file to feed to a compiler later,
but it can also be done in an interactive session: *)

Extraction eq_nat_dec.

(* Now we can see the structure clearly; happily it is (nearly) 
isomorphic to that for [beq_nat] :*)

Extraction beq_nat.

(*
In fact, for this particular goal, there is really no choice in what
the proof computes.   To obtain a [sumbool] we must either prove that
[m] and [n] are equal or prove that they are not; the only way to
obtain such proofs is by recursive traversal of the nat's.  
Variations in *efficiency* are still possible, of course.
But sometimes when we use this "programming by tactic" technique,
we really *do* need to worry about what the proof computes;
we'll see an example below. *)

(* Anyhow, now we can rephrase our function in terms of [eq_nat_dec]
instead of [beq_nat].  Crucially, this is still a *computable*
function, even though it is manipulating proofs instead of simple
booleans.  By the way, we can still use the [if-then-else] construct,
because it works over all two-constructor types! *)

Definition sillyfun4' (n:nat) : nat :=
  if eq_nat_dec n 3 then n+1
  else if eq_nat_dec n 5 then n-1
  else 4.

Lemma sillyfun4_test : sillyfun4' 3 = 4. 
 reflexivity. (* we're relying on [eq_nat_dec] being "transparent" *)
Qed.

(* Our lemma is now considerably more straighforward to prove: *)

Lemma sillyfun4'_is_4 : forall (n:nat),
  sillyfun4' n = 4.
Proof.
  intros n. unfold sillyfun4'. 
  destruct (eq_nat_dec n 3). 
    Case "n=3". rewrite e. reflexivity.
    Case "n<>3". destruct (eq_nat_dec n 5).
      SCase "n=5". rewrite e. reflexivity.
      SCase "n<>5". reflexivity.
Qed.

End sumbool.
(* From here on, the visible definition of sumbool reverts
to the built-in one, which is identical to what we showed here. *)



(* ---------- Subset types --------------------------------- *)

Module subset.

(* So far, we've kept functions (on Set) and properties of these
functions (in Prop) quite distinct.  Our basic methodology has
been to define the functions and then, separately, prove properties
about them.  

An alternative approach is try to *combine* programming and proving
in a single framework.  We won't discuss this very much, because
the details get unpleasantly messy (although recent versions of 
Coq have substantially improved the situation).  But we'll show
one simple application of the idea, using *subset types*.

It is often natural to *refine* a type (like nat, or nat -> nat)
to a subset based on some particular predicate. For example we
might want to define the set of non-empty lists of [X]:

{ xs : list X | xs <> nil }

and (re)define [head] to work only on this subset, so that it no
longer has to return an [option X].

head : {xs : list X | xs <> nil } -> X

The usual way to do this in Coq is to package up the type with 
the predicate in a kind of *dependent product*, thus:   *)



Inductive sig (A:Type) (P:A -> Prop) : Type :=
    exist : forall x:A, P x -> sig A P.
Implicit Arguments sig [A].
Implicit Arguments exist [A].

Notation "{ x | P }" := (sig (fun x => P)) : type_scope.
Notation "{ x : A | P }"  := (sig (fun (x:A) => P)) : type_scope.


(* 
An element [y] of a subset [{x:A | P x}] is the pair of 
an [a] of type [A] and of a proof [h] that [a] satisfies [P].
Note that is definition is extremely similar to the one 
we gave for existential quantification: *)

Print ex.  

(* (Hence the constructor name [exist].)
The only difference is that we can use [sig] to construct a 
Type (hence a Set) not merely a Prop.

Now try out this facility. This time we'll try to program directly
with both Set and Prop terms, rather than using tactics.  It is
crucial to remember that members of [{xs:list X | xs <> nil}] are
pairs, not lists!  *)

Definition head_strong (X:Set) (l : {xs : list X | xs <> nil}) : X  :=
  match l with
   | exist nil pf => match (pf (refl_equal nil)) with end   (* !!! *) 
   | exist (y::ys) _ => y
  end.


(* What happened in the nil branch?  To be type-correct, we need
to return a plain [X], but we don't have any!  Of course, this branch
is impossible.  This is reflected by the fact that in this branch 
we have a proof [pf] that [nil <> nil].   We can turn this into 
a proof of [False] by applying it to a proof that [nil = nil], which
is constructed by [refl_equal nil].  Then, the trick is to use this
proof of [False] to convince the typechecker that we have a "value" of
type [X].  To do this, we recall that a [match] expression can have 
*any* type, so long as its arms agree.  A complete [match] over [False]
has no arms, so it can be assigned any type we like!  

This kind of reasoning is not so easy!  In general, we're better off
trying to use tactic-based methods. *)

Definition head_strong' (X:Set) (l : {xs : list X | xs <> nil}) : X.
  intros X l. 
  inversion l as [xs P]. 
  destruct xs.  
    impossible. apply P.  reflexivity.
    apply x. 
Defined.  

(* The generated proof term is a bit more complicated, but fundamentally 
similar to the term we wrote by hand. And it has the correct
computational content. *)
Print head_strong'. 
Extraction head_strong'. 

  
(* Now let's try the same thing for tail: *)
Definition tail_strong_oops (X:Set) (l : {xs : list X | xs <> nil}) : list X.
  intros X l. 
  inversion l as [xs P]. 
  (* It's easy to solve this goal ! *)
  auto. 
Defined.

Extraction tail_strong_oops.

(* But this was not we wanted!  Not every proof of the correct
type does the right thing computationally.  It can be all
too tempting just to "solve the goal" without considering
the computational consequences.  For this reason, 
it is generally unwise to use automation tactics when
the computational content of the proof matters, because it is
hard to predict just what proof term (and hence computable
function) they will produce.   
*)

Definition tail_strong (X:Set) (l : {xs : list X | xs <> nil}) : list X.
(* FILL IN HERE (and delete "Admitted") *) Admitted.


(* Sometimes it would be nice to specify *part* of a proof term explicitly,
so as to control the computational aspects, while leaving the rest to
be filled in using tactics.  Coq provides a tactic called [refine] that
supports this mode of work, but it is not for the faint of heart! 

There is another very useful Coq mechanism called [Program], which
aims to make it easier to use subset types by separating programming
and proving.  We won't be looking at it here (partly because it is
still under development and its behavior changes a lot between Coq 
releases) but it is well worth learning about if this style of proof
attracts you. *)

End subset.


(* ---------------- FINITE SETS ------------------------------- *)


(* Let's push on, and use the subset mechanism to give a useful implementation
of finite sets as lists with no duplicates.  By packaging the fact that
there are no duplicates together with the list, we will be able to prove
a pigeon-hole principle for the sets.

This development is based on the Coq ListSet library, but that library
doesn't maintain the NoDup predicate. *)

(* We'll use a section to handle the list element type and comparison operator. *)

Section FiniteSets.


  Variable X : Set.  (* the element type *)

  (* we must be able to compare elements to avoid duplicates *)
  Hypothesis Xeq_dec : forall x y:X, {x = y} + {x <> y}.  

  Definition fset  := {xs : list X | @NoDup X xs} .


  (* We'll lift decidability of equality from X's to  lists of X's using
    the same "programming by tactics" as before. *)
  Definition in_list_dec : forall (x:X) (xs:list X), {In x xs} + {~In x xs}.
  Proof.
    intros x. induction xs.
    right.  apply in_nil. 
    destruct IHxs. 
      left.  apply in_cons.  auto.
      destruct (Xeq_dec x x0); subst. 
      left. simpl.  left; auto.
      right. intro. inversion H; subst; auto. 
  Defined.

  (* For these fundamental definitions, we can write the proof manipulation
     parts of the functions by hand without too much difficulty. *)

Print NoDup.

  Definition empty_fset : fset := exist _ (@nil X) (NoDup_nil X).

(* Try this one as an exercise: 
  Definition insert_fset (x:X) (s:fset) : fset := ...
*)

(* FILL IN HERE *)


  Definition fset_In (x:X) (s:fset) : Prop := 
     match s with
     | exist xs nd => In x xs
     end.

  Lemma fset_In_dec : forall (x:X) (s:fset), {fset_In x s} + {~ fset_In x s}.
  Proof.
    intros x s. 
    destruct s.   unfold fset_In.
    clear n. generalize dependent x. induction x0. 
    intro x. right. intro. inversion H. 
    intro x1. destruct (Xeq_dec x x1). 
      left. simpl. left.  auto.
      destruct (IHx0 x1).
        left. simpl. right. auto.
        right. intro. simpl in H. inversion H; auto. 
  Qed.


  Definition size_fset (s: fset) : nat := 
    match s with
    | exist xs _ => length xs
    end.

  Lemma pigeon_fset : 
    forall (xs:list X) (s:fset), 
    (forall x, In x xs -> fset_In x s) -> 
    size_fset s < length xs  -> 
    exists i, exists j, 
      i < j /\ j <= size_fset s /\ index i xs = index j xs. 
   Proof.
     intros xs s I LT. destruct s. 
     unfold size_fset in *.
     unfold lt in LT. 
     destruct (pigeon X Xeq_dec x n (take (S (length x)) xs)) as [i [j [P [Q R]]]].
     apply take_incl. unfold fset_In in I.  unfold incl.  apply I. 
     apply take_length. auto. 
     exists i. exists j. 
     rewrite take_length in Q. 
     split. apply P. split. 
       unfold lt in Q. apply Sn_le_Sm__n_le_m. auto.
     rewrite index_take in R. rewrite index_take in R. auto.
     auto.  unfold lt in P, Q |- *. apply le_transitive with j. 
      auto.  apply le_transitive with (S j).  apply le_S.  apply le_n. auto. 
     auto. 
  Qed.


End FiniteSets.


(* --------------- Dependently-typed terms -------------------------- *)

(* Finally, let's take advantage of another dimension of Coq's generality, by
   making use of dependent types to simplify handling of terms for our 
   little language of arithemetic and booleans. *)


Module interp1.

Export FullArithTypes.

(* First, we'll do things the old-fashioned way, without fancy types. 

Recall that we had two ways of giving semantics to a term: via a reduction 
relation or using an interpretation function.  We've mostly been working
with the former; now let's consider the latter.

An interpeter recursively evaluates a term to a (Coq) value.  For the
arithmetic-only language, we could write this as a funcion of type 
[tm -> nat].  But for the extended language with two types, we can't 
give a simple return type of this kind.  But we can define a union
type [dvalute] (here [d] is for "denotation") that covers both 
possibilities; we also include a third type of "undefined" values 
to handle situations where we try to run [interp] on an ill-typed term. *)

Inductive dvalue : Set :=
  | d_bool : bool -> dvalue
  | d_nat : nat -> dvalue
  | d_undef : dvalue.


(* Now the interpreter is straightforward.
Notice that we propagate [d_undef] values wherever they appear *)

Fixpoint interp (t:tm) : dvalue :=
  match t with
  | tm_true => d_bool true
  | tm_false => d_bool false
  | tm_if t1 t2 t3 =>
      match interp t1 with
      | d_bool(true) => interp t2
      | d_bool(false) => interp t3
      | _ => d_undef
      end 
  | tm_zero => d_nat 0
  | tm_succ t =>
      match interp t with
      | d_nat n => d_nat(S n)
      | _ => d_undef
      end
  | tm_pred t =>     
      match interp t with
      | d_nat n => d_nat(pred n)
      | _ => d_undef
      end
  | tm_iszero t =>
      match interp t with
      | d_nat 0 => d_bool true
      | d_nat _ => d_bool false
      | _ => d_undef
      end
  end.

Lemma check : interp (tm_if (tm_iszero (tm_pred (tm_succ tm_zero))) tm_false tm_true) = d_bool false.
Proof.
 auto.
Qed.


(* Finally, we can prove that interpretation of
well-typed terms yields a result value of the
expected type. *)

Inductive dval_has_type : dvalue -> ty -> Prop :=
  | dt_bool : forall b, dval_has_type (d_bool b) ty_bool
  | dt_nat : forall n, dval_has_type (d_nat n) ty_nat.

Lemma interp_preserves_type : forall t T, has_type t T -> 
  dval_has_type (interp t) T.
  intros t T HT. induction HT; simpl. 
    apply dt_bool. 
    apply dt_bool. 
    inversion IHHT1. 
      destruct b; auto.  
    apply dt_nat. 
    inversion IHHT.
      apply dt_nat.
    inversion IHHT. 
      apply dt_nat.
    inversion IHHT.
      destruct n; apply dt_bool.  
Qed.


End interp1.

Module interp2.

(* Working with [dvalue]s in [interp] is tedious, because we must constantly
check tags of subexpressions.  We can avoid this by parameterizing (or "indexing")
the type of each term by the type of the (Coq) value to which the term evaluates.
*)


(* This definition essentially incorporates the typing relation:
only well-typed terms can be expressed! *)

Inductive tm : Set -> Type :=
  | tm_true : tm bool
  | tm_false : tm bool
  | tm_if : forall t, tm bool -> tm t -> tm t -> tm t
  | tm_zero : tm nat
  | tm_succ : tm nat -> tm nat
  | tm_pred : tm nat -> tm nat
  | tm_iszero : tm nat -> tm bool.
(* We have to build these terms in [Type] instead of [Set] for obscure technical
reasons. *)

(* There's no need for a type-preservation proof; it's built in! *)

Fixpoint interp (T:Set) (t:tm T) : T :=
  match t in tm T return T with
  | tm_true => true
  | tm_false => false
  | tm_if T23 t1 t2 t3 =>
      if interp bool t1 then interp T23 t2 else interp T23 t3
  | tm_zero => 0
  | tm_succ t1 => S (interp nat t1)
  | tm_pred t1 => pred (interp nat t1)
  | tm_iszero t1 => beq_nat (interp nat t1) 0   
  end.

(* Notice the extra syntax associated with [match t]. The [in] clause
*binds* variable [T] to be the underlying type index of [t].  The
[return] clause specifies that each arm of the match returns [T].
Without these clauses, Coq will reject the [match] as ill-typed, because
it doesn't do type inference in such situations.  (That's because
inference is impossible in the general case here, and Coq would rather
consistenly do nothing than use heuristics.)

We can ease the use of [interp] by making type parameters implicit : *)

Implicit Arguments tm_if [t]. 
Implicit Arguments interp [T].

Lemma check : interp (tm_if (tm_iszero (tm_pred (tm_succ tm_zero))) tm_false tm_true) = false.
Proof.
 auto.
Qed.

(* 

This whole approach is essentially the same thing as using Generalized 
Algebraic Data Types (GADTs) in a language like Haskell.  And in fact
Coq's syntax and restrictions probably make it less convenient to program
in this style here compared to in Haskell. 

But wait, there's more...

*)

End interp2.


Module interp3.

(* In Coq, we can go one more step. Rather than committing 
to using existing Coq types for values, we can revert to modeling types
explicitly and STILL write an implicitly well-typed [interp].  Here's how. *)

Inductive ty : Set :=
  | Nat : ty
  | Bool : ty .

Inductive tm : ty -> Set := 
  | tm_true : tm Bool
  | tm_false : tm Bool
  | tm_if : forall t, tm Bool -> tm t -> tm t -> tm t
  | tm_zero : tm Nat
  | tm_succ : tm Nat -> tm Nat
  | tm_pred : tm Nat -> tm Nat
  | tm_iszero : tm Nat -> tm Bool.

Definition interp_ty (T:ty) : Set :=
  match T with
  | Nat => nat
  | Bool => bool
  end.

Fixpoint interp (T:ty) (t:tm T) {struct t} : (interp_ty T) :=
  match t in tm T return interp_ty T with
  | tm_true => true
  | tm_false => false
  | tm_if T23 t1 t2 t3 =>
      if interp Bool t1 then interp T23 t2 else interp T23 t3
  | tm_zero => 0
  | tm_succ t1 => S (interp Nat t1)
  | tm_pred t1 => pred (interp Nat t1)
  | tm_iszero t1 => beq_nat (interp Nat t1) 0   
  end.

(* Notice the *type-level* computation being performed by [interp_ty T] ! 
   This *can't* be done with GADT's.  (Though perhaps it can be done
   by other means in GHC Haskell; one can never be sure these days.) *)

Implicit Arguments tm_if.
Implicit Arguments interp [T].

Lemma check : interp (tm_if (tm_iszero (tm_pred (tm_succ tm_zero))) tm_false tm_true) = false.
Proof.
 auto.
Qed.

(* Is this alternative any better than the last one?

It is certainly more flexible.  One demonstration of that is that we
can change the interpretation of types and values without changing
their representation.


For example, suppose we'd like to implement both [Nat] and [Bool] as
Coq [nat]s.  For [Bool] we'll choose the convention that 0 represents
true and anything non-zero represents false. *)

(* We simply give a different interpretation to types... *)
Definition interp_ty' (T:ty) : Set :=
  match T with
  | Nat => nat
  | Bool => nat
  end.

(* ... and terms *)
Fixpoint interp' (T:ty) (t:tm T) {struct t} : (interp_ty' T) :=
  match t in tm T return interp_ty' T with
  | tm_true => 0
  | tm_false => 1
  | tm_if T23 t1 t2 t3 =>
      if beq_nat (interp' Bool t1) 0 then interp' T23 t2 else interp' T23 t3
  | tm_zero => 0
  | tm_succ t1 => S (interp' Nat t1)
  | tm_pred t1 => pred (interp' Nat t1)
  | tm_iszero t1 => interp' Nat t1  (* tricky! *)
  end.


Implicit Arguments interp' [T].

Lemma check' : interp' (tm_if (tm_iszero (tm_pred (tm_succ tm_zero))) tm_false tm_true) <> 0. 
Proof.
 simpl. intro.  inversion H. 
Qed.

(* More importantly, in this reprsentation, the types of the simple language
are concrete data that we can inspect.  For example: *)

Definition beq_ty (T1 T2: ty) : bool :=
  match (T1,T2) with
  | (Nat,Nat) => true
  | (Bool,Bool) => true
  | (_,_) => false
  end.

(* Thus, we can write type-dependent analyses and transformations on 
terms, which is not possible in the previous scheme.
Such functions are quite important in compilers.

 For a (silly) example, here's a function that, given a [term t] and
a [ty T0], checks whether [t] contains any subterm that is a [tm_if]
returning [T0]. *)

Fixpoint check_if (T: ty) (t: tm T) T0 {struct t} : bool :=
  match t with
  | tm_if T23 t1 t2 t3 => 
        orb (beq_ty T0 T23) (orb (check_if _ t1 T0) 
                                 (orb (check_if _ t2 T0) (check_if _ t3 T0)))
  | tm_succ t1 => check_if _ t1 T0
  | tm_pred t1 => check_if _ t1 T0
  | tm_iszero t1 => check_if _ t1 T0
  | _ => false
  end.
Implicit Arguments check_if [T].

Lemma test1 : check_if (tm_if (tm_iszero (tm_if tm_false (tm_succ tm_zero) (tm_pred tm_zero))) tm_false tm_true) Bool = true.
  auto.
Qed.

Lemma test2 : check_if (tm_if (tm_iszero (tm_if tm_false (tm_succ tm_zero) (tm_pred tm_zero))) tm_zero tm_zero) Bool = false.
  auto.
Qed.


End interp3.


