(** * Reasoning About Functional Programs
    *** Version of 9/29/2008
*)

(* We've now seen quite a bit of Coq's facilities for
   functional programming.  It is time to start looking at
   how we can REASON in Coq about the programs we've
   written. *)

Require Export func.

(* -------------------------------------------------- *)
(** ** Reasoning by "partial evaluation" *)

(* Some facts about functions can be proved simply by
   unfolding their recursive definitions. *)

(* For example, the fact that 0 is a neutral element for
   plus on the left can be proved just by observing that
   [plus 0 n] reduces to [n] no matter what [n] is, since
   the definition of [plus] is recursive in its first
   argument. *)
Lemma zero_plus : forall n:nat, 
  plus 0 n = n.
Proof.
  simpl. reflexivity. 
Qed.

(* Here are some more facts that can be proved by the same
   "partial evaluation" technique... *)
Lemma one_plus : forall n:nat, 
  plus 1 n = S n.
Proof.
  simpl. reflexivity. 
Qed.

(* Actually, the [reflexivity] tactic implicitly simplifies
both sides of the equality before testing to see if they
are the same.  So we can omit the explicit use of [simpl]
just before any use of [reflexivity], and we'll generally do
from now on. *)
Lemma zero_times : forall n:nat, 
  times 0 n = 0.
Proof.
  reflexivity.
Qed.

Lemma one_times : forall n:nat, 
  times 1 n = n.
Proof.
  reflexivity.
Qed.

Lemma two_times : forall n:nat, 
  times 2 n = plus n n.
Proof.
  reflexivity.
Qed.

Lemma nil_app : forall X:Set, forall l:list X, 
  app [] l = l.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma const_app : forall l:list nat, 
  app [3,4] l = 3 :: 4 :: l.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* ------------------------------------------------------- *)
(** ** The [intros] and [rewrite] tactics *)

(* It will often happen that the goal we're trying to prove
   begins with some kind of quantifier (e.g., "for all
   numbers n, ...") or hypothesis ("assuming m=n, ...").

   In such situations, it is convenient to be able to move
   the "left-hand part" out of the way and concentrate on
   the "right-hand part."  The [intros] tactic permits us to
   do this, by moving a quantifier or hypothesis from the
   goal to a "context" of current assumptions.

   For example, here is a slightly different -- perhaps
   slightly clearer -- proof of one of the facts we proved a
   minute ago.
*)
Lemma zero_plus' : forall n:nat, 
  plus 0 n = n.
Proof.
  intros n. simpl. reflexivity. 
Qed.

(* Here is a more interesting proof that involves moving a
   hypothesis into the context and then APPLYING this
   hypothesis to rewrite the rest of the goal. *)
Lemma plus_id_common : forall m n:nat, 
  m = n -> plus m n = plus n m. (* -> is pronounced "implies" *)
Proof.
  intros m n.     (* move both quantifiers into the 
                     context at once *)
   intros eq.     (* move the hypothesis into the context *)
   rewrite -> eq. (* Rewrite the goal according to 
                     the hypothesis *)
   reflexivity. 
Qed.

(* The [->] annotation in [rewrite ->] tells Coq to apply
   the rewrite from left to right.  To rewrite from right to
   left, you can use [rewrite <-].  Try this in the above
   proof and see what changes.

   Note that this has nothing to do with the use of the
   symbol [->] to denote implication in the statement of the
   lemma. *)

Lemma plus_id_exercise : forall m n o : nat, 
  m = n -> n = o -> plus m n = plus n o.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* We can also use the [rewrite] tactic with a previously
   proved lemma instead of a hypothesis from the context. *)
Lemma times_zero_plus : forall m n : nat, 
  times (plus 0 n) m = times n m.
Proof.
  intros m n. 
   rewrite -> zero_plus'. reflexivity.
Qed.


(* ----------------------------------------------------- *)
(** ** Case analysis *)

(* Of course, not everything can be proved by simple
   calculation: In general, unknown, hypothetical
   values (arbitrary numbers, booleans, lists, etc.) can
   show up in the "head position" of functions that we want
   to reason about, blocking simplification.  For example,
   if we try to prove the following fact using the [simpl]
   tactic as above, we get stuck.
 *)
Lemma plus_one_neq_zero_firsttry : forall n,
  beq_nat (plus n 1) 0 = false.
Proof.
  intros n. simpl.  (* does nothing! *)
Admitted.
(* The [Admitted] command tells Coq that we want to give up
   trying to prove this lemma and just accept it as a given.
   This can be useful for developing longer proofs, since we
   can state subsidiary facts that we believe will be useful
   for making some larger argument, use [Admitted] to accept
   them on faith for the moment, and continue thinking about
   the larger argument until we are sure it is working; then
   we can go back and fill in the proofs we skipped.  Be
   careful, though: Every time you say [Admitted] you are
   leaving a door open for total nonsense to enter your nice
   rigorous formally checked world! *)

(* What we need is to be able to consider the possible forms
   of [n] separately: if it is [O], then we can calculate
   the final result of [beq_nat (plus n 1) 0] and check that
   it is, indeed, [false].  And if [n = S(n')] for some
   [n'], then, although we don't know exactly what number
   [plus n 1] yields, we can calculate that, at least, it
   begins with one [S], and this is enough to calculate
   that, again, [beq_nat (plus n 1) 0] will yield [false].

   The tactic that tells Coq to consider the cases where [n
   = O] and where [n = S n'] separately is called
   [destruct].  It generates TWO subgoals, which we must
   then prove, separately, in order to get Coq to accept the
   Lemma as proved.  (There is no special command for moving
   from one subgoal to the other.  When the first subgoal
   has been proved, it just disappears and we are left with
   the other "in focus.") *)
Lemma plus_one_neq_0 : forall n,
  beq_nat (plus n 1) 0 = false.
Proof.
  intros n. destruct n.
    reflexivity.
    reflexivity.
Qed.

Lemma negb_negb : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity.
Qed.

Lemma andb_ex : forall b : bool,
  andb b false = false.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma all3_spec : forall b c : bool,
    orb 
      (andb b c) 
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.



(* ---------------------------------------------------- *)
(** ** Induction on numbers *)

(* We proved above that 0 is a neutral element for plus on
   the left using a simple partial evaluation argument.  The
   fact that it is also a neutral element on the RIGHT
   cannot be proved in the same simple way... *)
Lemma plus_zero_firsttry : forall n:nat, 
  plus n 0 = n.
Proof.
  intros n.
   simpl. (* Does nothing! *) 
Admitted.  

(* Case analysis gets us a little further, but not all the
   way. *)
Lemma plus_zero_secondtry : forall n:nat, 
  plus n 0 = n.
Proof.
  intros n. destruct n.
    simpl. reflexivity. (* so far so good... *)
    simpl.              (* ...but here we are stuck again *)
Admitted.  

(* To prove such facts -- indeed, to prove most interesting
   facts about numbers, lists, and other inductively defined
   sets -- we need a more powerful reasoning principle:
   INDUCTION.

   Recall (from high school) the principle of induction over
   natural numbers:

     If [P(n)] is some proposition involving a natural
     number n, and we want to show that P holds for ALL
     numbers n, we can reason like this:

        - show that [P(O)] holds
        - show that, if [P(n)] holds, then so does [P(S n)]
        - conclude that [P(n)] holds for all n.

   In Coq, the style of reasoning is "backwards": we begin
   with the goal of proving [P(n)] for all n and break it
   down (by applying the [induction] tactic) into two
   separate subgoals: first showing P(O) and then showing
   [P(n) -> P(S n)]. *)
Lemma plus_0 : forall n:nat, 
  plus n 0 = n.
Proof.
  intros n. induction n.      
    (* First subgoal: *)
    simpl. reflexivity.
    (* Second subgoal: *)
    simpl. rewrite -> IHn. reflexivity.
Qed.
Lemma times_0 : forall n:nat, n * 0 = 0.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma plus_one : forall n:nat, 
  plus n 1 = S n.
Proof.
  intros n. induction n. 
    reflexivity.
    simpl. rewrite -> IHn. reflexivity.
Qed.

Lemma times_one : forall n:nat, 
  times n 1 = n.
Proof.
  intros n. induction n.
    reflexivity.
    simpl. rewrite -> IHn. rewrite -> plus_one. 
    reflexivity.
Qed.
(* Note that we applied a rewrite here justified by a
   previously proved lemma ([plus_one]) rather than an
   assumption in the immediate context. *)

Lemma plus_assoc : forall m n p : nat, 
  plus m (plus n p) = plus (plus m n) p.   
Proof.
  intros m n p. induction m.
    reflexivity.
    simpl. rewrite -> IHm. reflexivity.
Qed.

(** An exercise to be worked together: *)
Lemma minus_n_n_0 : forall n,
  minus n n = 0.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma dist_succ_plus : forall m n : nat, 
  plus m (S n) = S (plus m n).
Proof. 
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma plus_commut : forall m n : nat, 
  plus m n = plus n m.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(** Exercise: Which of the following lemmas require induction
   in their proofs?  (See if you can predict in advance,
   before trying with Coq.) *)
Lemma S_neq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma zero_neq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma n_neq_Sn : forall n : nat,
  beq_nat n (S n) = false.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* Some basic properties of beq_nat require inductive proofs. *)

Lemma beq_nat_n_n : forall n : nat,
  beq_nat n n = true.
Proof.
  intros n. induction n.
    simpl. reflexivity.
    simpl. rewrite -> IHn. reflexivity.
Qed.

(* Naturally, we might expect as similar property to hold on 
unequal [nat]'s:

Lemma beq_nat_n_n' : forall n n' : nat,
     n <> n'
  -> eqnat n n' = false.

But it will be a while before we get to terms with what
[n <> n'] really means... *)

Lemma beq_nat_symm : forall x y r,
  beq_nat x y = r -> beq_nat y x = r.
Proof.
  induction x.
    (* Case "O". *)
    intros y r E. destruct y.
      rewrite E. reflexivity. 
      rewrite <- E. reflexivity. 
    (* Case "S". *)
    intros y r E. destruct y.
      rewrite <- E. reflexivity. 
      rewrite <- E. simpl. apply IHx. reflexivity.
Qed.


(* ---------------------------------------------------- *)
(** ** Induction on lists *)

(* We can do induction not just on numbers, but on any
   inductively defined type: Coq generates an appropriate
   induction principle when it processes the [Inductive]
   declaration.

   Here is the induction principle for (polymorphic) lists:

     If X is a type and [P l] is some proposition involving
     a list l of type [list X], and we want to show that P
     holds for all l, we can reason like this:

        - show that P [] holds
        - show that, for any element x:X and any list l :
          list X, if [P l] holds, then so does [P (x::l)]
        - conclude that [P l] holds for all lists l.
*)
Lemma append_assoc : forall X:Set, forall l1 l2 l3 : list X, 
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.   
Proof.
  intros X l1 l2 l3. induction l1.
    reflexivity.
    simpl. rewrite -> IHl1. reflexivity.
Qed.

Lemma append_nil : forall X:Set, forall l : list X, 
  l ++ [] = l.   
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(** An exercise to be worked together: *)
Lemma length_append : forall X : Set,
                      forall l1 l2 : list X,
  length (l1 ++ l2) = plus (length l1) (length l2).
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* Now let's try something a little more intricate: proving
   that reversing a list does not change its length.  Our
   first attempt at this proof gets stuck in the successor
   case... *)
Lemma length_reverse_firsttry : 
  forall X : Set, forall l : list X,
  length l = length (reverse l).
Proof.
  intros X l. induction l.
    simpl. reflexivity.
    simpl. (* Here we get stuck: the goal is an equality
              involving [snoc], but we don't have any equations
              in either the immediate context or the global
              environment that have anything to do with
              [snoc]! *)
Admitted.

(* So let's take the equation about snoc that would have
   enabled us to make progress and prove it as a separate
   lemma. *)
Lemma length_snoc : forall X : Set,
                    forall v : X,
                    forall l : list X,
  length (snoc l v) = S (length l).
Proof.
  intros X v l. induction l.
    simpl. reflexivity.
    simpl. rewrite -> IHl. reflexivity.
Qed. 

(* Now we can complete the original proof. *)
Lemma length_reverse : forall X : Set,
                       forall l : list X,
  length l = length (reverse l).
Proof.
  intros X l. induction l.
    simpl. reflexivity.
    simpl. rewrite -> length_snoc. rewrite -> IHl.  reflexivity.
Qed. 

(** An exercise to work together: Show that [map] and
   [reverse] "commute" in a similar way. *)
Lemma map_reverse : forall X Y : Set, 
                    forall f : X->Y,
                    forall s : list X,
  map f (reverse s) = reverse (map f s).
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(** Exercises... *)

Lemma reverse_reverse : forall X : Set, 
                        forall s : list X,
  reverse (reverse s) = s.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma reverse_append : forall X : Set, 
                       forall l1 l2 : list X,
  reverse (l1 ++ l2) = (reverse l2) ++ (reverse l1).
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(** Exercise: 
     - Find a non-trivial equation involving cons (::),
       snoc, and append (++).
     - Prove it. 

FILL IN HERE
*) 

(* There is a short solution to the next exercise.  If you
   find yourself getting tangled up, step back and try to
   look for a simpler way... *)
Lemma append_assoc4 : forall X : Set,
                      forall l1 l2 l3 l4 : list X,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma snoc_append : forall (X:Set) (l:list X) (x:X),
  snoc l x = l ++ [x].
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.



