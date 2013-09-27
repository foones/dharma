(** * More Coq Tactics 
    *** Version of 10/15/2008
*)

(* The small set of tactics we have seen so far can already
   be used to prove some fairly interesting properties of
   inductively defined functions.  In this chapter we extend
   our range by introducing several other fundamental
   tactics and exploring how they can be used for more
   sophisticated reasoning involving equalities and
   induction. 
*)

Require Export func1.

(* ------------------------------------------------------- *)
(** ** The [Case] annotation *)

(* One of the less nice things about Coq's mechanisms for
   interactive proof is the way subgoals seem to come and go
   almost at random, with no explicit indication of where we
   are -- which case of an induction or case analysis we are
   in -- at any given moment.  In very short proofs, this is
   not a big deal.  But in more complex proofs it can become
   quite difficult to stay oriented.

   Here is a simple hack that I find helps things quite a
   bit.  It uses some facilities of Coq that we have not
   discussed -- the string library (just for the concrete
   syntax of quoted strings) and the [Ltac] command, which
   allows us to declare custom tactics.  We will come back
   to [Ltac] in more detail later.  For now, don't worry
   about the details of this declaration. *)
Require String. Open Scope string_scope.
Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.
(*
Ltac Case s := 
  let c := fresh "case" in set (c := s); 
  move_to_top c.
*)

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case." ].

Ltac Case name := Case_aux Case name.
Ltac SCase name := Case_aux SCase name.
Ltac SSCase name := Case_aux SSCase name.
Ltac SSSCase name := Case_aux SSSCase name.
Ltac SSSSCase name := Case_aux SSSSCase name.
Ltac SSSSSCase name := Case_aux SSSSSCase name.
Ltac SSSSSSCase name := Case_aux SSSSSSCase name.
Ltac SSSSSSSCase name := Case_aux SSSSSSSCase name.

(* Having defined the [Case] tactic, let's see how it is
   used.  Step through the following proof and observe how
   the context changes. *)
Lemma length_reverse' : forall X : Set,
                        forall l : list X,
  length l = length (reverse l).
Proof.
  intros X l. induction l.
    Case "nil". 
      simpl. reflexivity.
    Case "cons". 
      simpl. rewrite -> length_snoc. rewrite -> IHl.  
      reflexivity.
Qed. 

(* The [Case] tactic does something very trivial: It simply
   adds a string that we choose (tagged with the identifier
   "case") to the context for the current goal.  When
   subgoals are generated, this string is carried over into
   their contexts.  When the last of these subgoals is
   finally proved and the next top-level goal (a sibling of
   the current one) becomes active, this string will no
   longer appear in the context and we will be able to see
   that the case where we introduced it is complete. *)

(* ------------------------------------------------------- *)
(** ** The [unfold] tactic *)

(* Sometimes the [simpl] tactic doesn't make things quite as
   simple as we need.  The [unfold] tactic can be used to
   explicitly replace a defined name by the right-hand side
   of its definition. *)

Definition plus3 (n:nat) := plus n 3.


Lemma plus3_example : forall n,
  plus3 n = plus 3 n.
Proof.
  simpl.
  (* Note that the [simpl] rewrites the right-hand side of
     the equation, but not the left.  Now we are stuck
     unless we know something about the way plus3 is
     defined. *)
  unfold plus3. intros n. rewrite -> plus_commut. reflexivity.
Qed.

(* ----------------------------------------------------- *)
(** ** The [apply] tactic *)

(* We often encounter situations where the goal to be proved
   is exactly the same as some hypothesis in the context or
   some previously proved lemma. *)
Lemma silly1 : forall (m n o p : nat),
     m = n 
  -> [m,o] = [m,p]
  -> [m,o] = [n,p].
Proof.
  intros m n o p eq1 eq2.
  rewrite <- eq1.
  (* At this point, we could finish with [rewrite ->
     eq2. reflexivity.]  as we have done several times above.
     But we can achieve the same effect in a single step by
     using the [apply] tactic instead: *)
  apply eq2.
Qed.

(* The [apply] tactic also works with CONDITIONAL hypotheses
   and lemmas: if the statement being applied is an
   implication, then the premises of this implication will
   be added to the list of subgoals needing to be proved. *)
Lemma silly2 : forall (m n o p : nat),
     m = n 
  -> (forall (q r : nat), q = r -> [q,o] = [r,p])
  -> [m,o] = [n,p].
Proof.
  intros m n o p eq1 eq2.
  apply eq2. apply eq1.
Qed.
(* You may find it instructive to experiment with this proof
   and see if there is a way to complete it using just
   [rewrite] instead of [apply]. *)

(* Typically, when we use [apply H], the statement [H] will
   begin with a [forall] binding some "universal variables."
   When Coq matches the current goal against the conclusion
   of [H], it will try to find appropriate values for these
   variables.  For example, when we do [apply eq2] in in the
   following proof, the universal variable [q] in [eq2] gets
   instantiated with [(m,m)] and [r] gets instantiated with
   [(n,n)].  (What does [X] get instantiated with?) *)
Lemma silly2a : forall (m n : nat),
     (m,m) = (n,n) 
  -> (forall (X : Set) (q r : X), q = r -> [q] = [r])
  -> [(m,m)] = [(n,n)].
Proof.
  intros m n eq1 eq2.
  apply eq2. apply eq1.
Qed.

(* Exercise: Complete the following proof without using
[simpl]. *)
Lemma silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true)
  -> evenb 3 = true
  -> oddb 4 = true.
Proof.
  (* SOLUTION *)
  intros H1 H2.
  apply H1. apply H2.
Qed.

(* To use the [apply] tactic, the (conclusion of the) fact
   being applied must match the goal EXACTLY -- for example,
   [apply] will not work if the left and right sides of the
   equality are swapped. *)
Lemma silly3_firsttry : forall (m : nat),
     true = beq_nat m 5 
  -> beq_nat (S (S m)) 7 = true.
Proof.
  intros m H.
  (* here we are stuck *)
Admitted.

(* When you find yourself in such a situation, one thing to
   do is to go back and try changing reorganizing the
   statement of whatever you are trying to prove so that
   things appear the right way around when they are needed.
   But if this is not possible or convenient, then the
   following lemma can be used to swap the sides of an
   equality statement in the goal so that some other lemma
   can be applied. *)
Lemma sym_eq : forall (X:Set) (m n : X),
  m = n -> n = m.
Proof.
  intros X m n eq. rewrite -> eq. reflexivity.
Qed.

Lemma silly3 : forall (m : nat),
     true = beq_nat m 5 
  -> beq_nat (S (S m)) 7 = true.
Proof.
  intros m H.
  apply sym_eq.   (* NOTE that, just as with [rewrite],
                      we can [apply] a lemma, 
                     not just an assumption in the context *)
  simpl.          (* Actually, this is unnecessary!*)
  apply H.        (* [apply] will do a [simpl] step first. *)
Qed.
Lemma reverse_exercise1 : forall (X : Set) (l l' : list X),
     l = reverse l'
  -> l' = reverse l.
Proof.
  (* SOLUTION *)
  intros X l l' eq. rewrite -> eq. apply sym_eq. apply reverse_reverse.
Qed.



(* --------------------------------------------------------- *)
(** ** Using tactics on hypotheses *)

(* By default, most tactics perform some operation on the
   goal formula and leave the context unchanged.  But
   tactics often come with variants that can be used to
   perform similar operations on a statement in the
   context. *)

(* For example, the tactic [simpl in H] performs
   simplification in the hypothesis named [H] in the
   context. *)
Lemma S_inj : forall (m n : nat) (b : bool),
     beq_nat (S m) (S n) = b 
  -> beq_nat m n = b. 
Proof.
  intros m n b H. simpl in H. apply H. 
Qed.

(* Similarly, the tactic [apply L in H] matches some
   conditional statement [L] (of the form [L1->L2], say)
   against a hypothesis H in the context.  However, unlike
   ordinary [apply] (which rewrites a goal matching [L2]
   into a subgoal [L1]), [apply L in H] matches [H] against
   [L1] and, if successful, replaces it with [L2].

   In other words, [apply L in H] gives us a form of FORWARD
   REASONING -- from [L1->L2] and a hypothesis matching
   [L1], it gives us a hypothesis matching [L2].

   By contrast, [apply L] is BACKWARD REASONING -- it says
   that if we know [L1->L2] and we are trying to prove [L2],
   it suffices to prove [L1]. *)

(* Here is a variant of a proof from above, using forward
   reasoning throughout intead of backward reasoning. *)
Lemma silly3' : forall (m : nat),
  (beq_nat m 5 = true -> beq_nat (S (S m)) 7 = true)
  -> true = beq_nat m 5 
  -> true = beq_nat (S (S m)) 7.
Proof.
  intros m eq H.
  apply sym_eq in H. apply eq in H. apply sym_eq in H. 
  apply H.
Qed.


(* ------------------------------------------------------ *)
(** ** The [assert] tactic *)

(* Coq's default style of reasoning is backward.  However,
   it can sometimes be convenient to switch to a "forward
   mode" for part of a proof.  Here is one more tactic that
   does this in a very powerful way... *)

(* It is common to reach a point in a proof where we would
   like to apply some fact [L] that we have not proven yet.
   One way to deal with this is to abort the current proof,
   state [L] as a separate lemma, prove it, and then go back
   to where we were.  But this strategy may sometimes not be
   attractive: it may be that [L] depends on many local
   assumptions, so that stating it as a separate lemma would
   require adding many awkward hypotheses; or it may be that
   the proof of [L] is short or uninteresting.  The [assert]
   tactic helps in such cases.

   If the current goal statement is [G], then doing [assert
   L as H] leaves us with two subgoals:
     - proving [L]
     - proving [G] again, but now with [L] as a
       hypothesis (named [H]) in the context.

   For example, here is an alternative proof of the
   [reverse_reverse] lemma, with the proof of the auxiliary
   [reverse_snoc] lemma in-lined using [assert]. *)

Lemma reverse_reverse' : forall X : Set, 
                         forall s : list X,
  reverse (reverse s) = s.
Proof.
  intros X s. induction s.
    Case "nil".
      simpl. reflexivity.
    Case "cons". 
      simpl. 
      assert (forall Y : Set, 
              forall v : Y,
              forall l : list Y,
              reverse (snoc l v) = v :: (reverse l))
          as reverse_snoc.
        SCase "Proof of reverse_snoc".
          intros Y v l. induction l.
            SSCase "nil". reflexivity.
            SSCase "cons". simpl. rewrite -> IHl. reflexivity.
      rewrite -> reverse_snoc. rewrite -> IHs. reflexivity.
Qed.  

(* In the previous proof, [reverse_snoc] was inlined
   "verbatim" from above, for simplicity.  But this example
   is also an illustration of how asserting needed facts
   in-line can be simpler than breaking them out as separate
   lemmas: we can simplify the statement of [reverse_snoc]
   by omitting the quantification over [Y] -- essentially,
   proving just the version of [reverse_snoc] that we need
   right here (where the elements of the list have type [X])
   rather than a more general one. *)
Lemma reverse_reverse'' : forall X : Set, 
                          forall s : list X,
  reverse (reverse s) = s.
Proof.
  intros X s. induction s.
    Case "nil".
      simpl. reflexivity.
    Case "cons". 
      simpl. 
      assert (forall v : X,
              forall l : list X,
              reverse (snoc l v) = v :: (reverse l))
          as reverse_snoc.
        SCase "Proof of reverse_snoc".
          intros v l. induction l.
            SSCase "nil". reflexivity.
            SSCase "cons". simpl. rewrite -> IHl. reflexivity.
      rewrite -> reverse_snoc. rewrite -> IHs. reflexivity.
Qed.


(* --------------------------------------------------- *)
(** ** The [inversion] tactic *)

(* A fundamental property of inductive definitions is that
   their constructors are INJECTIVE.  For example, the only
   way we can have [S n = S m] is if [m = n].

   The [inversion] tactic uses this injectivity principle to
   'destruct' an equality hypothesis. *)
Lemma eq_add_S : forall (m o : nat),
     S m = S o
  -> m = o.
Proof.
  intros m o eq. inversion eq. reflexivity.
Qed.

(* The same principle applies to other inductively defined
   sets, such as lists. *)
Lemma silly4 : forall (m o : nat),
     [m] = [o]
  -> m = o.
Proof.
  intros m o eq. inversion eq. reflexivity.
Qed.

(* The [inversion] tactic will destruct equalities between
   complex values, binding multiple variables as it goes. *)
Lemma silly5 : forall (m n o : nat),
     [m,n] = [o,o]
  -> [m] = [n].
Proof.
  intros m n o eq. inversion eq. reflexivity.
Qed.

Lemma sillyex1 : forall (X : Set) (x y z : X) (l j : list X),
     x :: y :: l = z :: j
  -> y :: l = x :: j
  -> x = y.
Proof.
  (* SOLUTION *)
  intros X x y z l j eq1 eq2.
  inversion eq1. inversion eq2. apply sym_eq. apply H0.
Qed.

(* Another critical property of inductive definitions is
   that distinct constructors are never equal, no matter
   what they are applied to.  For example, [S n] can never
   be equal to [O], no matter what [n] is.  This means that
   anytime we can see a HYPOTHESIS of the form [S n = O], we
   know that we must have made contradictory assumptions at
   some point.  The [inversion] tactic can be used to cut
   off the proof at this point. *)
Lemma silly6 : forall (n : nat),
     S n = O
  -> plus 2 2 = 5.
Proof.
  intros n contra. inversion contra. 
Qed.

(* Similarly, under the assumption that [false = true],
   anything at all becomes provable. *)
Lemma silly7 : forall (m n : nat),
     false = true
  -> [m] = [n].
Proof.
  intros m n contra. inversion contra. 
Qed.

Lemma sillyex2 : forall (X : Set) (x y z : X) (l j : list X),
     x :: y :: l = []
  -> y :: l = z :: j
  -> x = z.
Proof.
  (* SOLUTION *)
  intros X x y z l j eq1 eq2. inversion eq1.
Qed.

(* Here is a more realistic use of inversion to prove a
   property that we will find useful at many points later
   on... *)
Lemma beq_nat_true : forall m n,
  beq_nat m n = true -> m = n.
Proof.
  intros m. induction m. 
    Case "O". 
      intros n. destruct n.  
      SCase "O". simpl. reflexivity.  
      SCase "S". simpl. intros contra. inversion contra. 
    Case "S". 
      intros n. destruct n.
      SCase "O". intros contra. inversion contra.
      SCase "S". intros H. simpl in H.
        apply IHm in H. rewrite -> H. reflexivity.
Qed.

(* Exercise: The above lemma can also be proved by induction
   on [n]. (though we have to be a little careful about which
   order we introduce the variables, so that we get a
   general enough induction hypothesis; this is done for you
   below).  Finish the following proof.  To get maximum
   benefit from the exercise, try first to do it without
   looking back at the one above. *)
Lemma beq_nat_true' : forall n m,
  beq_nat m n = true -> m = n.
Proof.
  intros n. induction n. 
  (* SOLUTION *)
    Case "O". 
      intros m. destruct m.  
      SCase "O". simpl. reflexivity.  
      SCase "S". simpl. intros contra. inversion contra. 
    Case "S". 
      intros m. destruct m.
      SCase "O". intros contra. inversion contra.
      SCase "S". intros H. simpl in H.
        apply IHn in H. rewrite -> H. reflexivity.
Qed.

     

(* ------------------------------------------------------- *)
(** ** The [apply...with...] tactic *)

(* The following (silly) example uses two rewrites in a row
   to get from [ [m,n] ] to [ [r,s] ]. *)
Lemma trans_eq_example : forall (a b c d e f : nat),
     [a,b] = [c,d]
  -> [c,d] = [e,f]
  -> [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

(* Since this is a common pattern, we might abstract it out
   as a lemma recording once and for all the fact that
   equality is transitive. *)
Lemma trans_eq : forall (X:Set) (m n o : X),
  m = n -> n = o -> m = o.
Proof.
  intros X m n o eq1 eq2. rewrite -> eq1. rewrite -> eq2. 
  reflexivity.
Qed.

(* Now, we should be able to use [trans_eq] to prove the
   above example.  However, to do this we need a slight
   refinement of the [apply] tactic... *)
Lemma trans_eq_example' : forall (a b c d e f : nat),
     [a,b] = [c,d]
  -> [c,d] = [e,f]
  -> [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2. 
  (* If we simply tell Coq [apply trans_eq] at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate [X]
     with [nat], [m] with [[a,b]], and [o] with [[e,f]].
     However, the matching process doesn't determine an
     instantiation for [n]: we have to supply one explicitly
     by adding [with (n:=[c,d])] to the invocation of
     [apply]. *)
  apply trans_eq with (n:=[c,d]). apply eq1. apply eq2. 
Qed.

(* Actually, we usually don't have to include the name [n] 
in the [with] clause; Coq is often smart enough to figure
out which instantiation we're giving. *)

Lemma trans_eq_exercise : forall (m n o p : nat),
     n = (minustwo o)
  -> (plus m p) = n
  -> (plus m p) = (minustwo o). 
Proof.
  intros m n o p eq1 eq2. 
  (* SOLUTION *)
  apply trans_eq with n. apply eq2. apply eq1. 
Qed.

(* -------------------------------------------------- *)
(** ** Practice session *)

(* Some nontrivial but not-too-complicated proofs to work
   together in class, and some for you to work as
   exercises... *)

(* This is a slightly roundabout way of stating a fact that
   we have already proved above.  The extra equalities force
   us to do a little more equational reasoning and exercise
   some of the tactics we've seen recently. *)
Lemma length_snoc' : forall (X : Set) (v : X)
                            (l : list X) (n : nat),
     length l = n
  -> length (snoc l v) = S n. 
Proof.
  intros X v l. induction l.
    Case "nil". intros n eq. simpl in eq. rewrite <- eq. reflexivity.
    Case "cons". intros n eq. simpl. destruct n.
      SCase "O".  inversion eq.
      SCase "S". 
        assert (length (snoc l v) = S n).
          SSCase "Proof of assertion". apply IHl. 
          inversion eq. reflexivity.
        rewrite -> H. reflexivity.
Qed.

(* A slightly different way of making the same assertion. *)
Lemma length_snoc'' : forall (X : Set) (v : X)
                             (l : list X) (n : nat),
     S (length l) = n
  -> length (snoc l v) = n.
Proof.
  intros X v l. induction l.
    (* SOLUTION *)
    Case "nil". intros n eq. rewrite <- eq. reflexivity.
    Case "cons". intros n eq. simpl. destruct n.
      SCase "O". inversion eq.
      SCase "S". 
        assert (length (snoc l v) = n).
          SSCase "Proof of assertion". apply IHl. 
          inversion eq. reflexivity.
        rewrite -> H. reflexivity.
Qed.


Fixpoint double (n:nat) {struct n} :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_injective : forall m n,
     double m = double n
  -> m = n.
Proof.
  intros m. induction m.
  (* SOLUTION *)
    Case "O". simpl. intros n eq. destruct n.  
      SCase "O". reflexivity.
      SCase "S". inversion eq. 
    Case "S". intros n eq. destruct n.
      SCase "O". inversion eq.
      SCase "S". 
        assert (m = n) as H.
          SSCase "Proof of assertion". apply IHm. inversion eq. reflexivity.
        rewrite -> H. reflexivity.
Qed.

Lemma plus_m_m_injective : forall m n,
     plus m m = plus n n
  -> m = n.
Proof.
  intros m. induction m.
    (* Hint: use the dist_succ_plus lemma from func1.v *)
    (* SOLUTION *)
    Case "0". intros n. simpl. intros eq. destruct n.
      SCase "O". reflexivity.
      SCase "S". inversion eq. 
    Case "S". intros n eq. destruct n.
      SCase "O". inversion eq.
      SCase "S". assert (m = n) as H.
        SSCase "Proof of assertion". apply IHm. 
          (* note that just [simpl in eq] doesn't work here *)
          rewrite -> dist_succ_plus in eq. rewrite -> dist_succ_plus in eq.   
          inversion eq. reflexivity.
        rewrite -> H. reflexivity.
Qed.

(* ------------------------------------------------- *)
(** ** Case analysis of compound expressions *)

(* We have seen many examples where the [destruct] tactic is
   used to perform case analysis of the value of some
   variable.  But sometimes we need to reason by cases on
   the result of some *expression*.  We can also do this
   with [destruct]. *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Lemma sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun. 
  destruct (beq_nat n 3).
    Case "true". reflexivity.
    Case "false". destruct (beq_nat n 5).
      SCase "true". reflexivity.
      SCase "false". reflexivity.
Qed.

Lemma sillyfun_odd : forall (n : nat),
     sillyfun n = true
  -> oddb n = true.
Proof.
  (* SOLUTION *)
  intros n. unfold sillyfun. intros eq. 
  destruct (beq_nat n 3).
    Case "true". inversion eq.
    Case "false". destruct (beq_nat n 5).
      SCase "true". inversion eq.
      SCase "true". inversion eq.
Qed.

(* ----------------------------------------------------- *)
(** ** The [remember] tactic *)

(* We have seen how the [destruct] tactic can be used to
   perform case analysis of the results of arbitrary
   computations.  If [e] is an expression whose type is some
   inductively defined set [T], then, for each constructor
   [c] of [T], [destruct e] generates a subgoal in which all
   occurrences of [e] (in the goal and in the context) are
   replaced by [c].

   Sometimes, however, this substitution process loses
   information that we need in order to complete the proof.
   For example, suppose we define a function [sillyfun1]
   like this... *)
Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(* ... and suppose that we want to convince Coq of the
   rather obvious observation that [sillyfun1 n] yields
   [true] only when [n] is odd.  By analogy with the proofs
   we did with [sillyfun] above, it is natural to start the
   proof like this: *)
Lemma sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true
  -> oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* At this point, we are stuck: the context does not
     contain enough information to prove the goal!  The
     problem is that the substitution peformed by [destruct]
     is too brutal -- it threw away every occurrence of
     [eqnat n 3], but we need to keep at least one of these
     because we need to be able to reason that since, in
     this branch of the case analysis, [eqnat n 3 = true],
     it must be that [n = 3], from which it follows that [n]
     is odd. *)
Admitted.

(* What we would really like is not to use [destruct]
   directly on [eqnat n 3] and substitute away all
   occurrences of this expression, but rather to use
   [destruct] on something else that is EQUAL to [eqnat n
   3] -- e.g., if we had a variable that we knew was equal
   to [eqnat n 3], we could [destruct] this variable
   instead.

   The [remember] tactic allows us to introduce such a
   variable. *)

Lemma sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true
  -> oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  remember (beq_nat n 3) as e3.
  (* At this point, the context has been enriched with a new
     variable [e3] and an assumption that [e3 = eqnat n 3].
     Now if we do [destruct e3]... *)
  destruct e3.
  (* ... the variable [e3] gets substituted away (it
     disappears completely) and we are left with the same
     state as at the point where we got stuck above, except
     that the context still contains the extra equality
     assumption -- now with [true] substituted for [e3] --
     which is exactly what we need to make progress. *)
    Case "true". apply sym_eq in Heqe3. apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    Case "false".
      (* When we come to the second equality test in the
         body of the function we are reasoning about, we can
         use [remember] again in the same way, allowing us
         to finish the proof. *)
      remember (beq_nat n 5) as e5. destruct e5.
        SCase "true". apply sym_eq in Heqe5. 
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        SCase "false". inversion eq.
Qed.

(** Now you try it... *)
(*  This one is a bit challenging.  Be sure your initial intros go
     only up through the parameter on which you want to do induction! *)
Lemma filter_exercise : forall (X : Set) (test : X -> bool)
                               (x : X) (l l' : list X),
     filter test l = x :: l'
  -> test x = true.
Proof.
  (* SOLUTION *)
  intros X test x l. induction l.
    Case "nil". intros l' eq. inversion eq.
    Case "cons". intros l' eq.
      simpl in eq.
      remember (test x0) as t. destruct t.
        SCase "true". inversion eq. rewrite <- H0. rewrite <- Heqt. reflexivity.
        SCase "false". apply IHl with (l':=l').
          apply eq.
Qed.
