(** * Programming with Propositions
    *** Version of 10/30/2008
*)

(* Now we turn to something a bit different: using Coq to
   build up the reasoning facilities of ordinary logic.  The
   theme of this part of the book is that constructing
   proofs of logical propositions is simply "programming
   with evidence" in a very precise sense.
*)

Require Export func4.

(* A PROPOSITION is a factual claim.  In Coq, propositions
   are written as expressions of type Prop. *)
Check (plus 2 2 = 4).

(* So far, all the propositions we have seen are equality
   propositions.  But we can build on equality propositions
   to make other sorts of claims.  For example, what does it
   mean to claim that "a number n is even"?  We have a
   function that (we believe) tests evenness, so one
   possible definition is "n is even if (evenb n = true)."
   We can capture this idea as follows:
*) 
Definition evenE (n:nat) := 
  evenb n = true.

(* [evenE] is a PARAMETERIZED PROPOSITION.  Think of it as a
   function that, when applied to a number n, yields a
   proposition asserting that n is even. *)
Check evenE.
Check (evenE 4).

(* If we can give evidence for a proposition, is is said to
   be PROVABLE. For example, the proposition [evenE 4] is
   provable, and the evidence is that we can show [even 4]
   is equal to [true]. *)
Lemma evenE_4 : 
  evenE 4.
Proof.
  (* Note that we need to [unfold evenE] to enable [simpl]. *)
  unfold evenE. simpl. reflexivity.
Qed.

(* Both provable and unprovable claims are perfectly good
   propositions.  Simply BEING a proposition is one thing;
   being PROVABLE is something else! *)
Check (evenE 2).
Check (evenE 3).

(* At this point, we have two rather different ways of
   talking about evenness:
     - a function [even] that CALCULATES evenness
     - a parameterized proposition [evenE] that ASSERTS
       evenness, defined in terms of the [even] function.

   We can now give EVIDENCE for the provability of an
   [evenE] proposition by showing that the [even] function
   returns [true]. *)

(* -------------------------------- *)
(* Inductively defined propositions *)

(* There is yet another way of talking about assertions of
   evenness.  Instead of going "indirectly" via the [even]
   function, we can give a "direct" definition of evenness
   by saying, straight out, what we would be willing to
   accept as EVIDENCE that a given number is even.  *)
Inductive evenI : nat -> Prop :=
  | even_0 : evenI O
  | even_SS : forall n:nat, evenI n -> evenI (S (S n)).

(* Let's examine the parts of this definition:
      - The first line declares that [evenI] is a
        proposition parameterized by a natural number (i.e.,
        it is the same sort of thing as [evenE])
      - The second line declares that the constructor
        [even_0] can be taken as evidence for the assertion
        [evenI O].
      - The third line declares that, if [n] is a number and
        [E] is evidence that [n] is even (i.e., [E] is
        evidence for the assertion [evenI n]), then [even_SS
        n E] can be taken as evidence for [evenI (S (S n))].
        That is, we can construct evidence that [S (S n)] is
        even by applying the constructor [even_SS] to
        evidence that [n] is even. *)

(* These two constructors can be combined to produce
   evidence of the evenness of particular numbers. *)
Lemma four_even :
  evenI 4.
Proof.
  apply even_SS. apply even_SS. 
  apply even_0. 
Qed.

(* We can also prove implications involving evenness in this
   style.  For example, the assertion [evenI n ->
   evenI (plus 4 n)] can be read "assuming we have evidence
   that [n] is even, we can construct evidence that [plus 4
   n] is even." *)
Lemma even_plus4 : forall n,
  evenI n -> evenI (plus 4 n).
Proof.
  intros n E. simpl. apply even_SS. apply even_SS. apply E.
Qed.

(* An exercise along the same lines. *)
Lemma double_even : forall n,
  evenI (double n).
Proof.
  (* SOLUTION *)
  intros n. induction n.
    Case "O". simpl. apply even_0.
    Case "S". simpl. apply even_SS. apply IHn.
Qed.

(* Besides CONSTRUCTING evidence of evenness, we can also
   REASON ABOUT evidence of evenness.  The fact that we
   introduced [evenI] with an [Inductive] declaration tells
   us not only that the two constructors can be used to
   build evidence of evenness but that these two
   constructors are the ONLY ways that evidence of evenness
   can be built.  In other words, if someone gives us a
   number [n] and evidence [E] justifying the assertion
   [evenI n], then we know that [E] can only have one of two
   forms: either [E] is [even_0] (and [n] is [O]), or [E] is
   [even_SS m E'], where [n = S (S m)] and [E'] is evidence
   that [m] is even.

   This means that it makes sense to use all the tactics
   that we have already seen for inductively defined DATA to
   reason about inductively defined EVIDENCE.

   For example, here we use a [destruct] on evidence that
   [n] is even in order to show that [evenI n] implies
   [evenI (n-2)].  (Recall the behavior of [pred] on [0].)  *)
Lemma even_minus2: forall n,
  evenI n -> evenI (pred (pred n)). 
Proof.
intros n E.
destruct E.  
  simpl. apply even_0. 
  simpl. apply E.
Qed.
(* Query: what happens if we try to [destruct] on [n] 
instead of [E]? *)


(* We can also perform induction on evidence that 
   [n] is even. Here we use it show that the old 
   [evenb] function returns [true] on [n]. *)

Lemma evenI_evenE : forall n,
  evenI n -> evenE n.
Proof.
  intros n E. induction E.
    Case "even_0". unfold evenE. reflexivity.
    Case "even_SS".  unfold evenE. simpl.  unfold evenE in IHE. apply IHE. 
Qed.
(* Thought question: Could this proof be carried out by
   induction on [n] instead of [E]? *)




(* Here's another exercise requiring induction. *)
Lemma even_sum : forall n m,
   evenI n -> evenI m -> evenI (n+m).
Proof.         
  (* SOLUTION *)
  intros n m en. generalize dependent m. induction en. 
    intros m em. simpl. apply em. 
    intros m em. simpl. apply even_SS.  apply IHen. apply em. 
Qed.


(* Here's another situation where we want analyze evidence
for evenness and build two sub-goals. *)
Lemma SSeven_even_firsttry : forall n,
  evenI (S (S n)) -> evenI n.
Proof.
  intros n E.  
  destruct E.  
  (* Oops. [destruct] destroyed far too much! *)
Admitted.

(* The right thing to use here is [inversion] (!) *)
Lemma SSeven_even : forall n,
  evenI (S (S n)) -> evenI n.
Proof.
  intros n E.  inversion E. apply H0.
Qed.
(* This may seem mysterious; so far we've only used
[inversion] on equality propositions, to utilize
injectivity of constructors or to discriminate 
between different constructors.   
But [inversion] is much more generally applicable
for analyzing inductive propositions.  
In this particular case, it analyzed the construction 
[evenI (S (S n))], determined that this could only
have been constructed using [even_SS], and generated 
the arguments of that constructor as new hypotheses.
(It also produced an auxiliary equality, which happens 
to be useless.)
We'll begin exploring its general behavior in what follows. *)

(* A simple exercise  *)
Lemma SSSSeven_even : forall n,
  evenI (S (S (S (S n)))) -> evenI n.
Proof.
  (* SOLUTION *)
  intros n E. inversion E. inversion H0. apply H2.
Qed.

(* [inversion] can also be used to derive goals 
by showing absurdity of a hypothesis. *)
Lemma even5_nonsense : 
  evenI 5 -> plus 2 2 = 9.
Proof.
  (* SOLUTION *)
  intros E. inversion E. inversion H0. 
  inversion H2. (* Neither constructor can possibly apply... *)
Qed.

(* We can generally use [inversion] instead of
  [destruct] on inductive propositions.  This illustrates
  that in general, we get one case for each possible
  constructor. Again, we also get some auxiliary equalities
  which are rewritten in the goal but not in the other
  hypotheses. *)
Lemma even_minus2': forall n,
  evenI n -> evenI (pred (pred n)). 
Proof.
intros n E.
inversion E. 
  simpl. apply even_0. 
  simpl. apply H.
Qed.

(* An exercise for later.  
   Finding an appropriate thing to do induction on is a bit tricky. *)
Lemma even_even_even : forall n m,
  evenI (n+m) -> evenI n -> evenI m.
  (* SOLUTION *)
intros n m E F. generalize dependent m.
induction F.
  intros m E. simpl in E. apply E.
  intros m E. simpl in E. inversion E. apply IHF. apply H0. 
Qed.



(* ----------------- *)

(* The discussion so far has shown that the proposition that
   "a number is even" can be phrased in two different
   ways -- indirectly, via a testing function [even], or
   directly, by inductively describing what constitutes
   evidence for evenness.  These two ways of defining
   evenness are about equally easy to state and work with.

   However, for many other properties of interest, the
   direct inductive definition is preferable, since writing
   a testing function may be awkward or even impossible.
   For example, consider the property MyProp defined as
   follows:

       1) the number 4 has property MyProp
       2) if n has property MyProp, then so does 4+n
       3) if n+2 has property MyProp, then so does n
       4) no other numbers have property MyProp

   This is a perfectly sensible definition of a set of
   numbers, but we cannot write this definition directly as
   a Coq Fixpoint (or as a recursive function in any other
   programming language).

   We might be able to find a clever way of testing this
   property using a Fixpoint (indeed, it is not even too
   hard to find one in this case), but in general this could
   require arbitrarily much thinking.  In fact, if the
   property we are interested in is uncomputable, then we
   cannot define it as a Fixpoint no matter how hard we try,
   because Coq requires that all Fixpoints correspond to
   terminating computations.

   On the other hand, an inductive definition of what it
   means to give evidence for the property MyProp is
   straightforward:
*)
Inductive MyProp : nat -> Prop :=
  | MyProp1 : MyProp 4
  | MyProp2 : forall n:nat, MyProp n -> MyProp (plus 4 n)
  | MyProp3 : forall n:nat, MyProp (plus 2 n) -> MyProp n.
(* The first three clauses in the informal definition of
   MyProp above are reflected in the first three clauses of
   the inductive definition.  The fourth clause is the
   precise force of the keyword [Inductive]. *)

(* As we did with evenness, we can now construct evidence
   that certain numbers satisfy [MyProp]. *)
Lemma MyProp_ten : MyProp 10.
Proof.
  apply MyProp3. simpl. 
  assert (12 = plus 4 8) as H.
    Case "Proof of assertion". reflexivity.
  rewrite -> H. 
  apply MyProp2. 
  (* a nicer way using a new tactic [replace] *)
  replace 8 with (plus 4 4) by reflexivity.
  apply MyProp2. 
  apply MyProp1. 
Qed.


Lemma MyProp_0 : MyProp 0.
Proof.
  (* SOLUTION *)
  apply MyProp3. apply MyProp3. apply MyProp1. 
Qed.

Lemma MyProp_plustwo : forall n:nat, MyProp n -> MyProp (S (S n)).
Proof.
  (* SOLUTION *)
  intros n H. apply MyProp3. simpl. 
  replace (S(S(S(S n)))) with (plus 4 n) by reflexivity. 
  apply MyProp2. apply H.
Qed.

(* With these, we can show that MyProp holds of all even
   numbers, and vice versa. *)
Lemma MyProp_even : forall n:nat, 
  evenI n -> MyProp n.
Proof.
  intros n H.
  induction H.  
    apply MyProp_0.
    apply MyProp_plustwo. apply IHevenI.
Qed.

Lemma even_MyProp : forall n:nat, 
  MyProp n -> evenI n.
Proof.
  (* SOLUTION *)
  intros n H. induction H.
    Case "MyProp1". apply four_even. 
    Case "MyProp2". simpl. apply even_SS. 
                    apply even_SS. apply IHMyProp.
    Case "MyProp3". apply SSeven_even. apply IHMyProp.
Qed.

(* --------------------------------------------------- *)
(* Induction principles *)

(* Every time we define something with an [Inductive]
   declaration, Coq automatically generates an induction
   principle.  The [induction] tactic invokes this principle
   for us automatically, but we are also free to invoke it
   ourselves if we like.

   The induction principle for a type [t] is called [t_ind].
   Here is the one for natural numbers: *)
Check nat_ind.

(* The fact [nat_ind] is stored in Coq's global environment
   just like any other lemma we have proved.  We can invoke
   it directly using the [apply] tactic instead of
   [induction]. *)
Lemma times_0' : forall n:nat, times n 0 = 0.
Proof.
  apply nat_ind.
    Case "O". simpl. reflexivity.
    Case "S". simpl. intros n IHn. rewrite -> IHn. simpl. 
      reflexivity.
Qed.
(* Note that, in the induction step of the proof (the "S"
   case), we have to do a little bookkeeping (the [intros])
   manually that [induction] does automatically.  Also, note
   that we do not introduce [n] into the context before
   applying [nat_ind] -- the conclusion of [nat_ind] is a
   quantified formula, and [apply] needs this conclusion to
   match the shape of our goal state. *)

Lemma plus_one' : forall n:nat, 
  plus n 1 = S n.
Proof.
  (* Complete this proof without using the [induction] tactic. *)
  (* SOLUTION *)
  apply nat_ind.
    Case "O". reflexivity.
    Case "S". simpl. intros n IHn. rewrite -> IHn. reflexivity.
Qed.

Lemma plus_assoc'' : forall m n p : nat, 
  plus m (plus n p) = plus (plus m n) p.   
Proof.
  intros m n p. 
  (* Complete this proof without using the [induction]
     tactic.  Don't change the [intros] in the first
     line. *)
  (* SOLUTION *)
  generalize dependent m.
  apply nat_ind.
    Case "O". reflexivity.
    Case "S". intros n0 IHm. simpl. rewrite -> IHm. 
      reflexivity.
Qed.

(* The induction principles for inductively defined
   propositions like [evenI] are a tiny bit more
   complicated.  Intuitively, this is because we want to use
   them to prove things by inductively considering the
   possible shapes that something in [evenI] can have --
   either it is evidence that [0] is even, or else it is
   evidence that, for some [n], [S (S n)] is even, and it
   includes evidence that [n] itself is.  But the things we
   want to prove are not statements about EVIDENCE, they are
   statements about NUMBERS.  So we want an induction
   principle that allows reasoning by induction on the
   former to prove properties of the latter.

   In English, it goes like this:

      - Suppose, P is a predicate on natural numbers (that
        is, [P n] is a [Prop] for every [n]).  To show that
        [P n] holds whenever [n] is even, it suffices to
        show:
          -- [P] holds for [0]
          -- for any [n], if [n] is even and [P] holds for
            [n], then [P] holds for [S (S n)].

   Formally: *)
Check evenI_ind.

(* We can apply [evenI_ind] directly instead of using
   [induction], following pretty much the same pattern as
   above. *)
Lemma evenI_evenE' : forall n,
  evenI n -> evenE n.
Proof.
  apply evenI_ind.
    Case "even_0". unfold evenE. reflexivity.
    Case "even_SS". intros n H IHE. unfold evenE. apply IHE.
Qed.

(* THOUGHT EXERCISE (not to be handed in, but recommended). 

   Write out the induction principles that Coq will generate
   for the inductive declarations [list] and [MyProp].
   Compare your answers against the results Coq prints for
   the following queries. *)
Check list_ind.
Check MyProp_ind.

Lemma even_MyProp' : forall n:nat, 
  MyProp n -> evenI n.
Proof.
  (* Complete this proof without using the [induction] tactic. *)
  (* SOLUTION *)
  apply MyProp_ind.
    Case "MyProp1". apply four_even. 
    Case "MyProp2". intros n H IHMyProp. 
      simpl. apply even_SS. apply even_SS. apply IHMyProp.
    Case "MyProp3". intros n H IHMyProp. apply SSeven_even. 
      apply IHMyProp.
Qed.

(* Exercise:

A palindrome is a sequence that reads the same backwards as forwards.

(1) Define an inductive proposition [pal] on [list nat] that captures
what it means to be a palindrome. (Hint: You'll need three cases.)

(2) Prove that 

forall l, pal(l++(reverse l))

(3) Prove that 

forall l, pal l => l = reverse l.

(4 -- ONLY  for those who are bored) Try to prove that

forall l, l = reverse l => pal l.

This is quite hard; in fact, I haven't succeeded in
proving it yet using only the tactics we've seen so far.

*)

(* SOLUTION *)
Inductive pal : list nat -> Prop :=
  | pal_nil : pal []
  | pal_one : forall x, pal [x]
  | pal_cons : forall x l, pal l -> pal (x::(snoc l x)).
Lemma pal_app_rev : forall l,
  pal (l ++ (reverse l)).
induction l. 
  simpl. apply pal_nil.
  simpl. rewrite <- snoc_with_append. apply pal_cons. apply IHl.
Qed.
Lemma pal_rev : forall l, pal l -> l = reverse l. 
intros l P. induction P. 
 reflexivity.
 reflexivity. 
 simpl. rewrite reverse_snoc.  rewrite <- IHP.  simpl.  reflexivity.
Qed.




