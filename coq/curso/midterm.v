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
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma in_cons : forall (A:Set) (a b:A) (l:list A), In b l -> In b (a :: l).
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

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
  (* FILL IN HERE (and delete "Admitted") *) Admitted.



Theorem In_split : forall (A:Set) (x:A) (l:list A), In x l -> exists l1, exists l2, l = l1++x::l2.
Proof.
  intros A x l.  induction l; intros P. 
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

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
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma in_app_or : forall (A:Set) (xs ys : list A) (x:A),
   In x (xs++ys) -> In x xs \/ In x ys.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

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
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma not_in_app : forall (A:Set) (x:A) (xs:list A) (ys:list A),
  ~In x xs -> ~In x ys -> ~In x (xs ++ ys).
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

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


Lemma disjoint_cons : forall (A:Set) (l1 l2: list A) (x:A),
 disjoint l1 l2 -> ~ In x l2 -> disjoint (x::l1) l2.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Theorem NoDup_disjoint : forall (A:Set) (l1 l2: list A), 
 NoDup (l1++l2) -> disjoint l1 l2.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.


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
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma Permutation_sym : forall (A:Set) (l1 l2: list A), Permutation l1 l2 -> Permutation l2 l1.
Proof.  
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma Permutation_trans : forall (A:Set) (l1 l2 l3:list A), Permutation l1 l2 -> Permutation l2 l3 -> Permutation l1 l3. 
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.


Theorem Permutation_equiv : forall (A:Set), equivalence (@Permutation A). 
Proof. 
  (* FILL IN HERE (and delete "Admitted") *) Admitted.


Lemma Permutation_cons_app : forall (A:Set) (l l1 l2:list A) (a:A), 
     Permutation l (l1 ++ l2) -> Permutation (a::l) (l1 ++ a::l2). 
Proof.
  intros A l l1. generalize dependent l. induction l1; simpl; intros l l2 a P.  
  (* This one is quite tricky to prove! *)
  (* FILL IN HERE (and delete "Admitted") *) Admitted.



Theorem Permutation_app_swap : forall (A:Set) (l1 l2:list A), Permutation (l1++l2) (l2++l1).
Proof.
  (* But this one should be simple! *)
  (* FILL IN HERE (and delete "Admitted") *) Admitted.


Lemma Permutation_in : forall (A:Set) (l1 l2: list A) (x: A), Permutation l1 l2 -> In x l1 -> In x l2.
Proof.
   intros A l1 l2 x P. induction P; intros H.  
   (* FILL IN HERE (and delete "Admitted") *) Admitted.


(* For definition of [preserves] see file logic4.v *)
Theorem NoDup_Permutation: forall (A:Set), preserves (@Permutation A) (@NoDup A).
Proof. 
  (* Warning: you'll need to generalize/reintroduce in order to get the right induction set up. *)
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

