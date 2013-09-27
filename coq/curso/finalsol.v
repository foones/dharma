(* Final Exam. 
   Complete as many proofs as you can.  

   Your filled-in file is due via email by 5pm, Thursday, December 11.

   As usual, the missing proofs vary widely in difficulty.
   If you get stuck on a proof, leave it as "Admitted" and move on.
   
   Work individually.  If you have any questions, please email me;
   I'll copy replies of general interest to the mailing list.
   If you have major difficulties, we can arrange to meet next week.

   If you need more intuition about automata concepts, you may wish to
   consult Ch.1 of Sipser, "Introduction to the Theory of Computation,"
   2nd ed.  I've placed a scanned copy of this on the web, beneath the
   course home page in the unpublicized file "sipser_ch1.pdf". For obvious
   copyright reasons, please don't distribute this copy publicly.

   You'll need full copies of all the files we've used so far.
   They can be downloaded from the course web page if you don't
   have them already. 
   WARNING: In particular, you'll need a *completed* version of
   pigeon.v that contains a full definition of [In_dec].  The
   safest thing to do is:
     - rename your pigeon.v to something else.
     - download pigeonsol.v 
     - rename it to pigeon.v
     - compile it
     - recompile fset.v and automata.v.
*)

Require Export automata.

(* Just for convenience *)
Implicit Arguments eq_language [A].
Implicit Arguments eq_language_1 [A l1 l2].
Implicit Arguments eq_language_2 [A l1 l2].
Implicit Arguments regular [A]. 

(* Miscellaneous useful lemmas and definitions. *)

(* Computable equality on natural numbers. *)
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

(* List stuff *)

Lemma NoDup_app : forall (X:Set) (l1 l2: list X), 
                      NoDup l1 -> NoDup l2 -> disjoint l1 l2 -> 
                      NoDup (l1++l2).
Proof.
  (* SOLUTION *)
  intros X. induction l1; intros l2 ND1 ND2 D. 
     auto.
     simpl. apply NoDup_cons. 
     apply not_in_app.
       inversion ND1; auto. 
       unfold disjoint in D. apply D. simpl.  left. auto.
       apply IHl1.  inversion ND1. auto. auto. 
       unfold disjoint in D |- *. intros x0 I.  apply D. right. auto.
Qed.

Lemma length_le_app : forall (X:Set) (ys xs: list X), length xs <= length (xs++ys).
Proof.
 (* SOLUTION *)
 induction ys; intro xs.
   simpl. rewrite  append_nil. apply le_n.
   replace (xs ++ x::ys) with ((xs ++ [x]) ++ ys).
   apply le_transitive with (length (xs++[x])).
     rewrite length_append. simpl. rewrite plus_commut.  simpl. apply le_S. apply le_n. 
     auto.
   rewrite <- append_assoc. simpl. auto.
Qed.

Lemma snoc_distr_app : forall (X:Set) xs ys (z:X), snoc (xs ++ ys) z = xs ++ (snoc ys z).
Proof.
  (* SOLUTION *)
  intros X. induction xs; intros ys z.
     auto.
     simpl. rewrite IHxs. auto.
Qed.


Lemma take_snoc: forall (X:Set) xs n (x:X), n <= length xs -> take n (snoc xs x) = take n xs.
Proof.
  intros X. induction xs; intros n x0 P. 
     simpl in P. inversion P; subst. auto.
     simpl. destruct n.  auto. simpl. rewrite IHxs. auto. simpl in P. apply Sn_le_Sm__n_le_m. auto.
Qed.


Lemma take_app: forall (X:Set) (xs:list X) ys, take (length xs) (xs ++ ys) = xs.
(* SOLUTION *)
Proof.
  induction xs; intro ys. auto.  simpl. rewrite IHxs. auto.
Qed.

(* Some arithmetic stuff. *)

Lemma plus_cancel_l : forall a b c, a + b = a + c -> b = c.
(* SOLUTION *)
Proof.
  induction a; intros b c.
   simpl.  auto.
   simpl. intro. inversion H.   auto. 
Qed.

Lemma plus_cancel_r : forall c a b,  a + c = b + c -> a = b.
Proof.
   intros c a b E. 
   replace (a+c) with (c+a) in E.  replace (b+c) with (c+b) in E.  apply (plus_cancel_l _ _ _ E). 
   apply plus_commut. apply plus_commut.
Qed.

(* Language stuff *)

Lemma eq_language_trans : forall A l1 l2 l3, @eq_language A l1 l2 -> eq_language l2 l3 -> eq_language l1 l3.
Proof. 
  intros A l1 l2 l3 E12 E23.
  unfold eq_language in *. 
  intro w.  
  apply iff_trans with (l2 w); auto. 
Qed.  

Lemma eq_language_sym : forall A l1 l2, @eq_language A l1 l2 -> eq_language l2 l1.
(* SOLUTION *)
Proof.
  intros A l1 l2 E.
  unfold eq_language in *. 
  intro w.
  apply iff_sym.  auto.
Qed.

Lemma regular_eq_language : forall A l l', @eq_language A l l' -> regular l -> regular l'.
Proof.
(* SOLUTION *)
  intros A l l' E R.
  unfold regular in *.
  destruct R as [d E0].
  exists d. 
  apply eq_language_trans with l.
  apply eq_language_sym. auto. auto.
Qed.

(* ------------------------------------------------------------------------- *)

(* Product fsets *)

Section product_fset.

  Variable A B: Set.
  Hypothesis Aeq_dec : forall (a1 a2:A), {a1 = a2} + {a1 <> a2}.
  Hypothesis Beq_dec : forall (b1 b2:B), {b1 = b2} + {b1 <> b2}.

  (* Computable equality on pairs *)
  Definition prod_eq_dec : 
    forall (ab1 ab2 : A*B), {ab1 = ab2} + {ab1 <> ab2}.
  Proof.
    intros ab1 ab2.
    destruct ab1 as [a1 b1]. destruct ab2 as [a2 b2].
    destruct (Aeq_dec a1 a2); subst. 
      destruct (Beq_dec b1 b2); subst.
        left. reflexivity.
        right. intro. inversion H; subst. auto.
        right. intro. inversion H; subst. auto.
  Defined.


  (* First define product of two lists without regard to uniqueness. *)
  
  (* And do this in two steps *)
  Fixpoint one_product (a:A) (lb: list B) {struct lb} : list (A*B) :=
    match lb with
    | nil => @nil (A*B)
    | b::lb' => (a,b)::(one_product a lb')
    end.

  Fixpoint product (la:list A) (lb:list B) {struct la} : list (A*B) :=
    match la with
    | nil => @nil (A*B)
    | a::la' => (one_product a lb) ++ (product la' lb)
    end.

  (* Now define the product fset with a proof of uniqueness. *)

  Definition product_fset (sa : fset A) (sb:fset B) : fset (A*B).
     intros [la NDa] [lb NDb].
     unfold fset. eapply exist.
     instantiate (1:=product la lb).
     induction la. 
       simpl. apply NoDup_nil.
       inversion NDa; subst. 
       simpl. apply NoDup_app.
         (* NoDup x*lb *)
         clear - NDb. generalize dependent x.  induction lb. 
            intro x. simpl. apply NoDup_nil.
            intro x0. inversion NDb; subst.
            simpl. apply NoDup_cons.
                intro.  clear - lb H H1.  induction lb.  
                   inversion H. 
                   eapply IHlb.  intro. apply H1. simpl. right. apply H0. 
                   simpl in H.  inversion H. inversion H0; subst. impossible. apply H1.  
                         simpl.  left. auto. auto. auto.
         (* NoDup la*lb *)
         auto. 
         (* disjoint (x*lb) (la*lb) *)
         unfold disjoint. intros. destruct x0 as [a0 b0].
           assert (a0 = x). clear - lb H. induction lb. 
               inversion H. 
               simpl in H. inversion H. 
                  inversion H0; subst. auto.
                  auto.
           subst.         
           intro. apply H1. 
           clear - la H0. induction la. 
             inversion H0. 
             simpl in H0.  apply in_app_or in H0.  destruct H0. 
                 simpl in H. clear - lb H. induction lb. 
                   inversion H. 
                   simpl in H. destruct H.  
                     inversion H; subst.  simpl. left. auto.
                     auto.
                 simpl. right. auto.
  Defined.


  (* For practial use, we want lemmas showing that the products behave as expected. *)

  Lemma In_product_fset  : forall (sa:fset A) (sb:fset B) (x: A*B),
    In_fset x (product_fset sa sb) -> In_fset (fst x) sa /\ In_fset (snd x) sb.
  Proof.
    intros sa sb x I.
    destruct x as [a b]. destruct sa as [la NDa]. destruct sb as [lb NDb].
    unfold In_fset in *. simpl in *. 
    clear - I.   (* this clears all hypotheses EXCEPT [I] and anything it depends on *)
    induction la.  
      inversion I. 
      simpl in I. 
      apply in_app_or in I.  destruct I.
      (* Hint: now do induction on lb. *)
      (* SOLUTION *) 
      SCase "left".
        clear - H. induction lb. 
          inversion H. 
          simpl in H. destruct H. 
            inversion H; subst. split; simpl; left; auto.
            destruct (IHlb H) as [PA PB].
            split. 
              auto. 
              simpl. right. auto.
      SCase "right".
        destruct (IHla H) as [PA PB].
        split. 
          simpl. right. auto.
          auto.
  Qed.

  Lemma In_fset_product : forall (sa: fset A) (sb: fset B) (a:A) (b:B),
    In_fset a sa -> In_fset b sb -> In_fset (a,b) (product_fset sa sb).
  Proof.
    intros sa sb a b Ia Ib.
    destruct sa as [la NDa]. destruct sb as [lb NDb].
    unfold In_fset in *. simpl in *. 
    (* SOLUTION *)
    clear - Ia Ib. generalize dependent b. generalize dependent a.
    induction la; intros a Ia b Ib. 
       inversion Ia. 
       simpl. simpl in Ia. inversion Ia; subst.
         Case "x =a".
           apply in_app1.
           clear - b Ib. induction lb. 
              inversion Ib. 
              simpl. simpl in Ib. inversion Ib; subst.
                left. auto.
                right. auto.
         Case "In a la".
            apply in_app2. auto.             
  Qed.



End product_fset.

(* ------------------------------------------------------------------------- *)
(* Now the regular languages stuff. *)

(* Part 1. Showing the intersection of any two regular languages is regular. 
   Cf. Sipser Thm. 1.25, observing the footnote on p. 46. *)

Definition lintersection (A:Set) (l1 l2 : language A) : language A :=
   fun w => l1 w /\ l2 w.
Implicit Arguments lintersection [A].


Definition product_delta 
  (St1 St2:Set) (A:Set) 
  (delta1:St1 -> A -> St1) (delta2:St2 -> A -> St2) : (St1*St2) -> A -> (St1*St2) :=
  fun s a => (delta1 (fst s) a,delta2(snd s) a).
Implicit Arguments product_delta [St1 St2 A].

Lemma fold_left_product_delta : 
  forall (St1 St2:Set) (A:Set) delta1 delta2
         (w:list A) (s1:St1) (s2:St2),
         fold_left (product_delta delta1 delta2) w (s1,s2) = (fold_left delta1 w s1,fold_left delta2 w s2).
Proof.
(* SOLUTION *)
  induction w. 
    auto.
    simpl. 
    intros s1 s2. rewrite <- IHw. auto.
Qed.


Definition intersection_dfa (A:Set) (d1 d2: dfa A) : dfa A.
  intros A d1 d2.
  destruct d1 as [St1 St1_eq_dec Q1 q1 q1_OK F1 F1_OK delta1 delta1_OK].
  destruct d2 as [St2 St2_eq_dec Q2 q2 q2_OK F2 F2_OK delta2 delta2_OK].
  set (eq_St12_dec := prod_eq_dec St1 St2 St1_eq_dec St2_eq_dec).
  eapply (dfa_intro A (St1 * St2) eq_St12_dec
          (product_fset St1 St2 Q1 Q2) (q1,q2)).
  apply In_fset_product; auto.
  instantiate (1:= product_fset St1 St2 F1 F2).
  unfold subset_fset. intros [a b] H.
  apply In_product_fset in H. simpl in H. destruct H. 
  apply In_fset_product.  apply F1_OK. auto. apply F2_OK. auto.
  instantiate (1:= product_delta delta1 delta2).
  intros [s1 s2]H a.
  apply In_product_fset in H. simpl in H.  destruct H. 
  unfold product_delta.  simpl. apply In_fset_product. apply delta1_OK. auto. apply delta2_OK. auto.
Defined.
 


Theorem regular_intersection : 
  forall (A:Set) (l1 l2: language A), 
    regular l1 -> regular l2 -> regular (lintersection l1 l2).
Proof.
  intros A l1 l2 [d1 R1] [d2 R2].  
  unfold regular. exists (intersection_dfa A d1 d2).
  split.
  (* SOLUTION *)
  Case "->".
    intros H. inversion H as [H1 H2]. 
    assert (A1:dfa_accepts A d1 w). apply (eq_language_1 R1). auto.
    assert (A2:dfa_accepts A d2 w). apply (eq_language_1 R2). auto. 
    destruct d1 as [St1 St1_eq_dec Q1 q1 q1_OK F1 F1_OK delta1 delta1_OK].
    destruct d2 as [St2 St2_eq_dec Q2 q2 q2_OK F2 F2_OK delta2 delta2_OK].
    unfold dfa_accepts in A1, A2 |- *. 
    unfold intersection_dfa.
    rewrite fold_left_product_delta.
    apply In_fset_product; auto.
  Case "<-".
    intros P. 
    destruct d1 as [St1 St1_eq_dec Q1 q1 q1_OK F1 F1_OK delta1 delta1_OK].
    destruct d2 as [St2 St2_eq_dec Q2 q2 q2_OK F2 F2_OK delta2 delta2_OK].
    simpl in P. 
    apply In_product_fset in P. destruct P as [P1 P2]. 
    split.
    SCase "1".
      rewrite fold_left_product_delta in P1. simpl in P1.  
      unfold dfa_accepts in R1. apply (eq_language_2 R1). auto.
    SCase "2".
      rewrite fold_left_product_delta in P2. simpl in P2. 
      unfold dfa_accepts in R2. apply (eq_language_2 R2). auto.
Qed.


(* ------------------------------------------------------------------------- *)
(* Part 2: Showing the language {A^mB^n | m, n >= 0} is regular. *)

(* Define a convenient alphabet to use for all our languages. *)

Inductive Sigma : Set :=  
| A : Sigma  
| B : Sigma.
 
(* Comparison on elements of Sigma *)
Definition eq_Sigma_dec : forall (m n :Sigma), {m = n} + {m <> n}.
  intros m n. 
  destruct m.
    destruct n.
      left. auto.
      right. intro. inversion H.
    destruct n.
      right. intro. inversion H. 
      left. auto.
Defined.


(* A useful function for counting symbols in words. *)

Fixpoint count x0 (xs:list Sigma) {struct xs} : nat :=
match xs with
| nil => 0
| (x::xs') => if eq_Sigma_dec x0 x then S(count x0 xs') else count x0 xs'
end.

Lemma count_app : forall x0 xs1 xs2, count x0 (xs1 ++ xs2) = count x0 xs1 + count x0 xs2.
Proof.
(* SOLUTION *)
 intros x0. induction xs1; intros xs2.
  auto.
  simpl. rewrite IHxs1. destruct (eq_Sigma_dec x0 x); auto. 
Qed. 

(* A function for generating x^n, with some useful lemmas. *)

Fixpoint rep (X:Set) (x:X) (n:nat) {struct n} :=
  match n with
  | 0 => []
  | S n' => x::(rep X x n')
  end.
Implicit Arguments rep [X].

Lemma count_rep : forall c d n, count d (rep c n) = if eq_Sigma_dec d c then n else 0.
Proof.
  intros c d. induction n.
     simpl.  destruct (eq_Sigma_dec d c); auto. 
     simpl. destruct (eq_Sigma_dec d c). rewrite IHn. auto. 
     auto.
Qed.
       
Lemma length_rep: forall (X:Set) (c:X) n, length (rep c n) = n.
Proof.
(* SOLUTION *)
  induction n.
   auto.
   simpl. auto.
Qed.

Lemma cons_rep_snoc : forall (X:Set) (c:X) n,  c::(rep c n) = snoc (rep c n) c.
Proof. 
(* SOLUTION *)
  intros. induction n.
    auto.
    simpl. rewrite <- IHn. auto.
Qed.

(* Finally, the definition of the language *)

Inductive LAmBn : word Sigma  -> Prop :=
LAmBn_intro : forall m n, LAmBn (rep A m ++ rep B n).

(* We'll show LAmBn is regular by giving an explicit definition of 
a DFA that accepts it.  (This approach is ok for very simple languages,
although it clearly doesn't scale very well.) 

The machine we want has three states: 0, 1, 2.
State 0 is the start state. States 0 and 1 are final states.

Informally: 

- if machine is in state 0, it has read 0 or more 'A's
- if machine is in state 1, it has read 0 or more 'A's followed by 1 or more 'B's
- if machine is in state 2, it has read an 'A' after an 'B'; this is the "error state"

Transition table:

                     State

Input       0        1         2
------------------------------------
A           0        2         2
B           1        1         2


*)


(* The transition table represented as a function. *)
Definition delta_AmBn (s:nat) (x:Sigma) : nat :=
   if eq_nat_dec s 0 then
     if eq_Sigma_dec x A then 0 else if eq_Sigma_dec x B then 1 else 2
   else if eq_nat_dec s 1 then
     if eq_Sigma_dec x A then 2 else if eq_Sigma_dec x B then 1 else 2
   else 2.

(* A convenient way to generate sets: nat_set n = {0,1,...,n-1}. *)
Fixpoint nat_set (n:nat) : fset nat :=
  match n with
  | 0 => empty_fset nat
  | S n => insert_fset eq_nat_dec n (nat_set n)
end.

(* Now, the components of the machine and their proofs of well-formedness *)

Definition Q_AmBn := nat_set 3.  (* states : {0,1,2} *)

Definition q0_AmBn := 0.         (* initial state : 0 *)

Definition F_AmBn := nat_set 2.  (* final states: {0,1} *)
     
Lemma q0_AmBn_OK : In_fset q0_AmBn Q_AmBn.
Proof.
   right. right. left. auto.
Qed.

Lemma F_AmBn_OK : subset_fset F_AmBn Q_AmBn.
Proof.
  unfold subset_fset.  intros x P. unfold In_fset in P. simpl in P. 
    inversion P; subst. 
      right. left. auto.
      inversion H; subst. 
        right. right. left. auto.
        inversion H0. 
Qed.

Lemma delta_AmBn_OK :   forall q : nat,
   In_fset q Q_AmBn ->
   forall a : Sigma, In_fset (delta_AmBn q a) Q_AmBn.
Proof.
(* SOLUTION *)
  intros q P a.
    unfold delta_AmBn.
    unfold In_fset in *. simpl in *. 
    inversion P; subst; simpl.  
      left. auto.
      inversion H; subst; simpl. 
        destruct (eq_Sigma_dec a A); simpl. 
          left. auto. 
          destruct (eq_Sigma_dec a B); simpl. 
            right. left. auto. 
            left. auto.
          inversion H0; subst; simpl.
          destruct (eq_Sigma_dec a A); simpl. 
             right. right. left. auto.
             destruct (eq_Sigma_dec a B); simpl. 
               right. left. auto.
               left. auto.
             inversion H1.
Qed. 

Definition DFA_AmBn : dfa Sigma := 
  dfa_intro Sigma nat eq_nat_dec Q_AmBn q0_AmBn q0_AmBn_OK F_AmBn F_AmBn_OK delta_AmBn delta_AmBn_OK.


(* The key lemma describing what the machine reads on any possible transition.
   Impossible transitions, such as from 1 to 0, must be excluded.
   Transitions to the error state (2) don't have to be described.
   Note the need for a mutual induction over all of these.  *)
Lemma delta_AmBn_behavior :  forall w,
 (fold_left delta_AmBn w 0 = 0 -> exists m, w = rep A m) /\
 (fold_left delta_AmBn w 0 = 1 -> exists m, exists n, w = rep A m ++ rep B n) /\
 (fold_left delta_AmBn w 1 = 1 -> exists n, w = rep B n) /\
 (fold_left delta_AmBn w 1 = 0 -> False) /\
 (fold_left delta_AmBn w 2 = 0 -> False) /\
 (fold_left delta_AmBn w 2 = 1 -> False).
Proof.
 induction w.
   repeat split; intro P.
     exists 0. auto.
     exists 0. exists 0.  auto.
     exists 0. auto.
     inversion P.
     inversion P.
     inversion P.  
   destruct IHw as [IHw1 [IHw2 [IHw3 [IHw4 [IHw5 IHw6]]]]]. 
   repeat split; intro P; simpl in P; unfold delta_AmBn at 2 in P; simpl in P; 
      destruct (eq_Sigma_dec x A); destruct (eq_Sigma_dec x B); subst; try inversion e0; auto. 
(* SOLUTION *)
        destruct (IHw1 P) as [m E]. exists (S m). rewrite E. auto. 
        impossible. auto.
        impossible. auto.
        destruct (IHw2 P) as [m0 [n0 E]]. exists (S m0). exists (n0). rewrite E. auto.
        destruct (IHw3 P) as [n0 E]. exists 0. exists (S n0). rewrite E. auto.
        impossible. auto.
        impossible. auto.
        destruct (IHw3 P) as [n0 E]. exists (S n0). rewrite E. auto.
        impossible. auto.  
Qed.

(* Finally, we show that the machine really recognized the language we claim. *)
Theorem LAmBn_regular : regular LAmBn.
  unfold regular. exists DFA_AmBn.
  unfold eq_language. intros w. split.
  Case "->".
    intro P. destruct P. 
    simpl. unfold In_fset. simpl. 
      rewrite fold_left_app. 
      destruct n. 
        right. left. simpl. induction m. auto. simpl.  unfold delta_AmBn at 2. simpl. auto. 
        left. simpl. induction m. simpl. unfold delta_AmBn at 2. simpl. 
            induction n. auto.  simpl.  unfold delta_AmBn at 2. auto. auto.
  Case "<-".  
    (* Hint: use the Lemma delta_AmBn_behavior ! *)
    (* SOLUTION *) 
    intro P. simpl in P. unfold In_fset in P. simpl in P. 
    destruct (delta_AmBn_behavior w) as [H [H0 _]].  
    destruct P. apply sym_eq in H1.  
      destruct (H0 H1) as [m [n E]].
      rewrite E. apply LAmBn_intro.
    destruct H1. apply sym_eq in H1. 
      destruct (H H1) as [m E].
      rewrite E. replace (rep A m) with (rep A m ++ rep B 0). apply LAmBn_intro. simpl. rewrite append_nil. auto.
    inversion H1. 
Qed.      

(* ------------------------------------------------------------------------- *)
(* Part 3: Showing the language {A^nB^n | n >= 0} is not regular, by
  using the Pumping Lemma to obtain a contradiction.  
  Cf. Sipser pp. 80-81, although the proof formalized here is not exactly either example. *)

(* The language *)
Inductive LAnBn : word Sigma  -> Prop :=
LAnBn_intro : forall n, LAnBn (rep A n ++ rep B n).


(* A generator for words in LAnBn : *)
Definition wAnBn (n:nat) : word Sigma :=
  rep A n ++ rep B n.

Lemma wAnBn_in_LAnBn : forall n, LAnBn (wAnBn n).
Proof.
 intros n. unfold wAnBn. apply (LAnBn_intro n).
Qed.

(* Some rather ad-hoc lemmas that are useful in the main proof. *)

Lemma wAnBn_long : forall n, n <= length (wAnBn n).
Proof.
(* SOLUTION *)
  induction n.
   simpl. apply le_n.
   simpl. apply le_n_S. apply le_transitive with (length (rep A n)).
     rewrite length_rep. apply le_n.
     apply length_le_app. 
Qed.

Lemma wAnBn_S : forall n, wAnBn (S n) = A::(snoc (wAnBn n) B).
Proof.
  induction n.
    unfold wAnBn. auto.
    unfold wAnBn in *. simpl in *. inversion IHn. 
    rewrite H0. rewrite snoc_distr_app. rewrite snoc_distr_app.
    rewrite <- cons_rep_snoc. simpl. rewrite <- cons_rep_snoc. auto. 
Qed.

Lemma wAnBn_prefix : forall p n, n <= p -> take n (wAnBn p) = rep A n.
Proof.  
  (* SOLUTION *)
  induction p; intros n LE.
    inversion LE; subst. auto.
    rewrite  wAnBn_S.
    destruct n. auto. 
    apply Sn_le_Sm__n_le_m in LE. 
    simpl. 
    rewrite take_snoc.  rewrite (IHp n); auto.
    apply le_transitive with p. auto. apply wAnBn_long.
Qed.

Lemma wAnBn_A : forall p n, n <=p -> forall xs, xs = take n (wAnBn p) -> count A xs = length xs.
Proof.
  intros. 
  rewrite (wAnBn_prefix _ _ H) in H0. rewrite H0.
  rewrite count_rep. simpl. rewrite length_rep. auto.
Qed.


Lemma wAnBn_notB : forall p n, n <=p -> forall xs, xs = take n (wAnBn p) -> count B xs = 0.
Proof.
  intros. 
  rewrite (wAnBn_prefix _ _ H) in H0. rewrite H0.
  rewrite count_rep. simpl. auto.
Qed.


Lemma wAnBn_counts : forall n xs, xs = wAnBn n -> count A xs = count B xs.
Proof.
  (* SOLUTION *)
  intros n xs E. rewrite E.
  destruct n; simpl; subst; auto.
    rewrite count_app. rewrite count_app. simpl. 
    repeat (rewrite count_rep). simpl.  rewrite plus_0. auto.
Qed.

(* The main result: *)

Theorem LAnBn_not_regular : ~ regular LAnBn.
Proof.
  intro. destruct (pumping _ _ H) as [p P].
  destruct (P (wAnBn p) (wAnBn_in_LAnBn p) (wAnBn_long p)) as [xs [ys [zs [Q [R [S T]]]]]].
  pose proof (T 0) as T1.  simpl in T1. inversion T1 as [n Q1]. fold (wAnBn n) in Q1.
  apply R. cut (length ys = 0).  intro. destruct ys.  auto. inversion H0. 
  assert (S1: length xs <= p).  
   apply le_transitive with (length (xs++ys)). 
   apply length_le_app. apply S. 

  (* Proof sketch. The intutition is that (length ys) must be 0 because
     otherwise we would would have a string in LAnBn with fewer A's 
     than B's.  We can prove this via the following series of equalities:

  E1 : count A (xs++ys++zs) = count B (xs++ys++zs)         (by Q)
  E2 : count A (xs++zs) = count B (xs++zs)                 (by Q1)
  E3 : count A (xs++ys) = length (xs++ys)                  (by Q,S).
  E4 : count A xs = length xs                              (by Q,S1)

  E5:  count A (xs++ys++zs) = length (xs++ys) + count A zs (from E3)  
  E6:  count A (xs++zs) = length xs + count A zs           (from E4)

  E7:  count B (xs++ys) = 0                                (by Q,S)
  E8:  count B xs = 0                                      (by Q,S1)
  E9:  count B (xs++ys++zs) = count B zs                   (from E7)
  E10: count B (xs++zs) = count B zs                       (from E8)
        
  E11: length (xs++ys) + count A zs = length xs + count A zs (from E5,E6,E1,E2,E9,E10)
  E12: length (xs++ys) = length x                          (from E11)
  
  I suggest proving each of these as a named assertion. 
  The lemmas immediately above
  (as well as more generic ones at the top of this file)
  should be useful.

*)
  assert (E1:count A (xs++ys++zs) = count B (xs++ys++zs)).
       rewrite <- Q. apply (wAnBn_counts p). auto.
  assert (E2:count A (xs++zs) = count B (xs++zs)).
       rewrite <- Q1. apply (wAnBn_counts n). auto.
  assert (E3: count A (xs++ys) = length (xs++ys)).
       apply (wAnBn_A _ _ S).  rewrite Q.
       rewrite append_assoc. rewrite take_app. auto.
  (* SOLUTION *) 
  assert (E4: count A xs = length xs).
    apply (wAnBn_A _ _ S1). rewrite Q.
    rewrite take_app. auto.
  assert (E5: count A (xs++ys++zs) = length (xs++ys) + count A zs).
    rewrite append_assoc. rewrite count_app. rewrite E3. auto.
  assert (E6: count A (xs++zs) = length xs + count A zs).
    rewrite count_app. rewrite E4. auto.
  assert (E7: count B (xs++ys) = 0). 
    apply (wAnBn_notB _ _ S).  rewrite Q.
    rewrite append_assoc. rewrite take_app. auto.
  assert (E8: count B xs = 0).
    apply (wAnBn_notB _ _ S1). rewrite Q.
    rewrite take_app. auto.
  assert (E9: count B (xs++ys++zs) = count B zs). 
    rewrite append_assoc.  rewrite count_app.  rewrite E7. auto.
  assert(E10: count B (xs++zs) = count B zs). 
    rewrite count_app. rewrite E8. auto.
  assert(E11: length (xs++ys) + count A zs = length xs + count A zs).
    rewrite <- E5. rewrite <- E6.
    rewrite E1. rewrite E2. rewrite E9. rewrite E10. auto.
  assert(E12: length(xs++ys) = length xs).
    apply (plus_cancel_r _ _ _ E11).
  rewrite length_append in E12.
  rewrite plus_commut in E12.
  eapply plus_cancel_r. simpl.  apply E12.
Qed.  


(* ------------------------------------------------------------------------- *)
(* Part 4: Show the language LequalAB = {w | w contains equal numbers of A's and B's} 
   is not regular using an indirect argument.        

  Here's the idea. Suppose LequalAB were regular.  Then (LAmBn intersect LequalAB) would also be
  regular, by our previous proof.  But this language is simply LnBn, which we've just proved is
  *not* regular.  Contradiction!  So LequalAB cannot be regular.
*)


Definition LequalAB (w: word Sigma) :  Prop :=   count A w = count B w.

Lemma LAnBn_as_intersection: eq_language   LAnBn  (lintersection LAmBn LequalAB).
Proof.
  unfold eq_language. intro w. 
  split; intros P.
  (* SOLUTION *)
  Case "->".
    inversion P; subst. unfold lintersection. 
    split.
        apply LAmBn_intro. 
        unfold LequalAB. rewrite count_app. rewrite count_app. 
          repeat (rewrite count_rep). simpl. apply plus_0.
  Case "<-".
       inversion P. inversion H; subst. 
         unfold LequalAB in H0. rewrite count_app in H0. rewrite count_app in H0. 
         repeat (rewrite count_rep in H0).  simpl in H0. rewrite plus_0 in H0. rewrite H0. 
         apply LAnBn_intro.
Qed.

     
Theorem LequalAB_not_regular : ~ regular LequalAB.
Proof.
  intro. 
  apply LAnBn_not_regular.
  (* SOLUTION *)
  eapply regular_eq_language.
  apply eq_language_sym.
  apply LAnBn_as_intersection.
  apply regular_intersection.
  apply LAmBn_regular.
  auto.
Qed.

