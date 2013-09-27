(* Midterm: fun with lists. *)

(* Instructions:

   Please complete as many of the proofs in this file as you can. 

   Your filled-in file is due via email by 10am, Thursday, November 6. 
   
   The ordering of lemmas and theorems in this file is deliberate;
   often, an earlier lemma is very useful for proving a later one.
   If you get stuck on a proof, leave it as "Admitted" and move on.
   The lemmas are definitely *not* presented in order of increasing
   difficulty!

   Of course, you should strive for simple and elegant proofs, but
   I won't count off for messy ugly ones that work. However,
   please try to use only the Coq features we have discussed 
   in class so far (up through file logic4.v). 

   Work individually.  If you have any questions, please email me;
   I'll copy replies of general interest to the mailing list.
   If you have major difficulties, we can arrange to meet next week.
   
   You'll need full copies of all the files we've used so far.
   They can be downloaded from the course web page if you don't
   have them already. 

*)

Require Import logic4.


(* -------------------------------------------------------------------- *)

(* In: a value is in a list. *)

Fixpoint In (A:Set) (a:A) (l:list A) {struct l} : Prop := 
  match l with
    | nil => False
    | b :: m => b = a \/ In _ a m
  end.
Implicit Arguments In [A].

Lemma in_eq : forall (A:Set) (a:A) (l:list A), In a (a :: l).
Proof.
  (* SOLUTION *)
  intros A a l. simpl. left. auto. 
Qed.

Lemma in_cons : forall (A:Set) (a b:A) (l:list A), In b l -> In b (a :: l).
Proof.
  (* SOLUTION *)
  intros A a b l. simpl. right. auto. 
Qed.

Lemma In_not_head : forall (A:Set) (x:A) y ys, In x (y::ys) -> x <> y -> In x ys. 
Proof.
   intros A x y ys P NE. 
   simpl in P. inversion P. 
   Case "y = x".
     subst.  
     impossible. auto. 
   Case "In x ys".
     auto.
Qed.

Lemma in_nil : forall (A:Set) (a:A), ~ In a nil.
Proof.
  (* SOLUTION *)
  unfold not. intros A a H. inversion H. 
Qed.



Theorem In_split : forall (A:Set) (x:A) (l:list A), In x l -> exists l1, exists l2, l = l1++x::l2.
Proof.
  intros A x l.  induction l; intros P. 
  (* SOLUTION *)
  Case "nil".
    inversion P. 
  Case "cons".
    simpl in P; inversion P;  subst.  
     SCase "head".
       exists (@nil A). exists l. auto.
     SCase "tail".
       apply IHl in H. 
       inversion H as [l1 H'].   
       inversion H' as [l2 H'']. 
       exists (x0::l1). exists l2.
       simpl. rewrite H''.  auto. 
Qed.

Lemma in_app1 : forall (A:Set) (x:A) (xs:list A) (ys:list A),
  In x xs -> In x (xs++ys). 
Proof.
  intros A x xs.  induction xs; intros ys P. 
  inversion P. 
  simpl. inversion P. 
   left. auto. 
   right. auto. 
Qed.

Lemma in_app2 : forall (A:Set) (x:A) (xs:list A) (ys:list A),
  In x ys -> In x (xs++ys). 
Proof.
  (* SOLUTION *)
  intros A x xs. induction xs; intros ys P. 
  simpl. auto. 
  simpl. right. auto. 
Qed.

Lemma in_app_or : forall (A:Set) (xs ys : list A) (x:A),
   In x (xs++ys) -> In x xs \/ In x ys.
Proof.
  (* SOLUTION *)
   intros A xs. induction xs. 
     intros ys x P. right. auto. 
     intros ys x0 P. 
       simpl in P. inversion P; subst. 
         left. apply in_eq. 
         apply IHxs in H. inversion H. 
            left. apply in_cons. auto.
            right. auto.
Qed.
 

Lemma app1_not_in: forall (A:Set) (x:A) (xs:list A) (ys:list A),
  ~In x (xs++ys) -> ~In x xs.
Proof.
  intros A x xs ys P Q.
  destruct xs. 
    inversion Q. 
    apply P.  apply in_app1. auto. 
Qed.


Lemma app2_not_in: forall (A:Set) (x:A) (xs:list A) (ys:list A),
  ~In x (xs++ys) -> ~In x ys.
Proof.
  (* SOLUTION *)
  intros A x xs ys P Q. 
  destruct xs. 
    simpl in P. auto. 
    apply P.  apply in_app2. auto. 
Qed.

Lemma not_in_app : forall (A:Set) (x:A) (xs:list A) (ys:list A),
  ~In x xs -> ~In x ys -> ~In x (xs ++ ys).
Proof.
  (* SOLUTION *)
  intros A x xs ys PX PY Q.
  apply in_app_or in Q. inversion Q; auto. 
Qed.

(* -------------------------------------------------------------------- *)

(* NoDup: A list contains no repeated elements. *)

Inductive NoDup (A:Set) : list A -> Prop :=
    | NoDup_nil : NoDup A nil
    | NoDup_cons : forall x l, ~ In x l -> NoDup A l -> NoDup A (x::l).
Implicit Arguments NoDup [A].


(* -------------------------------------------------------------------- *)

(* disjoint: Two lists contain no common elements *)

Definition disjoint (A:Set) (l1 l2:list A) : Prop :=
  forall x:A, In x l1 -> ~ In x l2.
Implicit Arguments disjoint [A]. 


Lemma disjoint_sym : forall (A:Set), symmetric (@disjoint A). 
Proof.
  (* SOLUTION *)
  unfold disjoint. unfold symmetric. 
  intros A a b P x Q.   
  intro R. apply P in R. auto. 
Qed.

Lemma disjoint_cons : forall (A:Set) (l1 l2: list A) (x:A),
 disjoint l1 l2 -> ~ In x l2 -> disjoint (x::l1) l2.
Proof.
  (* SOLUTION *)
  unfold disjoint. intros A l1 l2 x P Q. 
  intros x0 R S. 
  simpl in R; inversion R; subst. 
    auto. 
    apply P in H. auto. 
Qed.  
      


Theorem NoDup_disjoint : forall (A:Set) (l1 l2: list A), 
 NoDup (l1++l2) -> disjoint l1 l2.
Proof.
  (* SOLUTION *)
  intros A l1. induction l1; intros l2 P.  
  unfold disjoint. intros x Q R. inversion Q.
  inversion P.  
  apply disjoint_cons.
  auto. 
  apply app2_not_in in H1.
  auto. 
Qed.


(* -------------------------------------------------------------------- *)

(* Permutation: one list is a permutation of another *)

Inductive Permutation (A:Set) : list A -> list A -> Prop :=
| perm_nil: Permutation A nil nil
| perm_skip: forall (x:A) (l l':list A), Permutation A l l' -> Permutation A (cons x l) (cons x l')
| perm_swap: forall (x y:A) (l:list A), Permutation A (cons y (cons x l)) (cons x (cons y l))
| perm_trans: forall (l l' l'':list A), Permutation A l l' -> Permutation A l' l'' -> Permutation A l l''.
Implicit Arguments Permutation [A]. 

Lemma Permutation_refl : forall (A:Set) (l: list A), Permutation l l. 
Proof. 
  (* SOLUTION *)
  intros A l. induction l. 
    apply perm_nil. 
    apply perm_skip. auto. 
Qed.

Lemma Permutation_sym : forall (A:Set) (l1 l2: list A), Permutation l1 l2 -> Permutation l2 l1.
Proof.  
  (* SOLUTION *)
  intros A l1 l2 P. induction P. 
    apply perm_nil. 
    apply perm_skip. apply IHP. 
    apply perm_swap. 
    apply perm_trans with l'; auto.  
Qed.

Lemma Permutation_trans : forall (A:Set) (l1 l2 l3:list A), Permutation l1 l2 -> Permutation l2 l3 -> Permutation l1 l3. 
Proof.
  (* SOLUTION *)
  intros A l1 l2 l3 P12 P23. 
  apply perm_trans with l2; auto.
Qed. 


Theorem Permutation_equiv : forall (A:Set), equivalence (@Permutation A). 
Proof. 
  (* SOLUTION *)
  intros A. unfold equivalence. 
  split. 
     unfold reflexive. apply Permutation_refl. 
     split. 
        unfold symmetric. apply Permutation_sym. 
        unfold transitive. apply Permutation_trans.
Qed.


Lemma Permutation_cons_app : forall (A:Set) (l l1 l2:list A) (a:A), 
     Permutation l (l1 ++ l2) -> Permutation (a::l) (l1 ++ a::l2). 
Proof.
  intros A l l1. generalize dependent l. induction l1; simpl; intros l l2 a P.  
  (* This one is quite tricky to prove! *)
  (* SOLUTION *)
    apply perm_skip. auto.
    apply perm_trans with (a::x::l1 ++ l2).
      apply perm_skip. auto.
      apply perm_trans with (x::a::l1++l2). 
        apply perm_swap. 
        apply perm_skip. 
          apply IHl1. 
          apply Permutation_refl. 
Qed.



Theorem Permutation_app_swap : forall (A:Set) (l1 l2:list A), Permutation (l1++l2) (l2++l1).
Proof.
  (* But this one should be simple! *)
  (* SOLUTION *)
  intros A l1. induction l1.
    intros l2.  simpl. rewrite append_nil. apply Permutation_refl.
    intros l2. simpl.  apply Permutation_cons_app. auto. 
Qed.
  


Lemma Permutation_in : forall (A:Set) (l1 l2: list A) (x: A), Permutation l1 l2 -> In x l1 -> In x l2.
Proof.
   intros A l1 l2 x P. induction P; intros H.  
   (* SOLUTION *)
   Case "nil".
     auto. 
   Case "skip".
     simpl. 
     inversion H; subst.  
        left.  auto.
        right. auto. 
   Case "swap".
     simpl. 
     inversion H; subst.  
        right. left. auto. 
        inversion H0; subst. 
          left. auto. 
          right. right. auto.
   Case "trans".
     auto. 
Qed.


(* For definition of [preserves] see file logic4.v *)
Theorem NoDup_Permutation: forall (A:Set), preserves (@Permutation A) (@NoDup A).
Proof. 
  (* SOLUTION *)
  unfold preserves. 
  intros A l1 ll ND P. induction P. 
  Case "nil".  
    auto. 
  Case "skip".
    apply NoDup_cons. 
      inversion ND; subst. 
        intro Q.  apply H1. 
        apply Permutation_in with l'.
          apply Permutation_sym. auto.
          auto. 
      apply IHP. 
        inversion ND. auto. 
  Case "swap".
    inversion ND; subst.  inversion H2; subst. 
    apply NoDup_cons.
      intro Q. inversion Q; subst; auto.   
      apply NoDup_cons. 
        intro Q. apply H1. simpl. right. auto. 
        auto. 
  Case "trans".
    auto. 
Qed.

