Require Export opsem4.
Require Export midterm.
Require Export pigeon.

(* First, still more on lists *)

Fixpoint fold_left (A B : Set) (f: A -> B -> A) (l:list B) (a0:A) {struct l} : A :=
  match l with
    | nil => a0
    | cons b t => fold_left A B f t (f a0 b)
  end.
Implicit Arguments fold_left [A B]. 

Lemma fold_left_app : forall (A B : Set) (f : A -> B -> A) (l l':list B)(i:A),
  fold_left f (l++l') i = fold_left f l' (fold_left  f l i).
Proof.
  induction l.
  simpl; auto.
  intros.
  simpl.
  auto.
Qed.

Fixpoint fold_right  (A B: Set) (f: B -> A -> A) (a0:A) (bs: list B) {struct bs} : A :=
  match bs with
  | nil => a0
  | cons b t => f b (fold_right A B f a0 t)
  end.
Implicit Arguments fold_right [A B]. 



(* ---------------- FINITE SETS ------------------------------- *)


(* We use the subset mechanism to give a useful implementation
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

  Definition list_of (s:fset) : list X :=
  match s with
  | exist xs _ => xs
  end.


  (* For these fundamental definitions, we can write the proof manipulation
     parts of the functions by hand without too much difficulty. *)

  Definition empty_fset : fset := exist _ (@nil X) (NoDup_nil X).

  Definition insert_fset (x:X) (s:fset) : fset := 
     match s with 
     | exist xs nd =>    
         match In_dec Xeq_dec x xs with
         | left _ => exist _ xs nd
         | right ne => exist _ (x::xs) (NoDup_cons X x xs ne nd)
         end
     end.


  Definition In_fset (x:X) (s:fset) : Prop := 
    In x (list_of s).

  Lemma In_empty_fset : forall (x:X), ~ In_fset x empty_fset.
  Proof.    
    intros x H. 
    inversion H. 
  Qed.

  Lemma In_insert_fset1 : forall (x:X) (s:fset), In_fset x (insert_fset x s).
  Proof.
   intros x s.
   destruct s as [xs ND]. unfold In_fset, insert_fset.
   destruct (In_dec Xeq_dec x xs). 
      auto.
      simpl. left. auto.
  Qed.

  Lemma In_insert_fset2 : forall (x x0:X) (s:fset), In_fset x s -> In_fset x (insert_fset x0 s).
  Proof.
    intros x x0 s P.
    destruct s as [xs ND]. unfold In_fset, insert_fset in *.
    simpl in P. 
    destruct (In_dec Xeq_dec x0 xs).
       auto. 
       simpl. right. auto.
  Qed.
 

  Lemma In_fset_dec : forall (x:X) (s:fset), {In_fset x s} + {~ In_fset x s}.
  Proof.
    intros x s.
    destruct s. 
    unfold In_fset. simpl. 
    apply (In_dec Xeq_dec). 
  Defined.


  Definition size_fset (s: fset) : nat := 
    length (list_of s). 


  Lemma pigeon_fset : 
    forall (xs:list X) (s:fset), 
    (forall x, In x xs -> In_fset x s) -> 
    size_fset s < length xs  -> 
    exists i, exists j, 
      i < j /\ j <= size_fset s /\ index i xs = index j xs. 
   Proof.
     intros xs s I LT. destruct s. 
     unfold size_fset in *.
     unfold lt in LT. 
     destruct (pigeon X Xeq_dec x n (take (S (length x)) xs)) as [i [j [P [Q R]]]].
     apply take_incl. unfold In_fset in I.  unfold incl.  apply I. 
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

  Definition subset_fset (s1 s2:fset) := forall (x:X), In_fset x s1 -> In_fset x s2. 
  Definition eq_fset (s1 s2 : fset) := subset_fset s1 s2 /\ subset_fset s2 s1. 

  Definition fold_left_fset (B:Set) (f:B->X->B) (s:fset) (b0:B) : B :=
    fold_left f (list_of s) b0.

  Definition fold_right_fset (B:Set) (f:X->B->B) (b0:B) (s:fset) : B :=
    fold_right f b0 (list_of s).

  Definition union_fset (s1 s2: fset) : fset :=
    fold_right_fset fset insert_fset s1 s2. 

  Lemma In_union_fset1 : forall (x:X) (s1 s2 :fset), In_fset x s1 -> In_fset x (union_fset s1 s2).
  Proof.
    intros x s1 s2 P. destruct s1. destruct s2. 
    unfold In_fset in P.  unfold list_of in P. 
    unfold union_fset. unfold fold_right_fset. 
    simpl. 
    clear n0. generalize dependent x0. induction x1; intros.
      simpl.  auto.
    simpl.
    apply In_insert_fset2. apply IHx1; auto.
  Qed.

  Lemma In_union_fset2 : forall (x:X) (s1 s2 :fset), In_fset x s2 -> In_fset x (union_fset s1 s2).
  Proof.
    intros x s1 s2 P. destruct s1. destruct s2. 
    unfold In_fset in P.  unfold list_of in P. 
    unfold union_fset. unfold fold_right_fset. 
    simpl. 
    clear n0. generalize dependent x0. induction x1; intros. 
      inversion P. 
      simpl in P. inversion P; subst. 
        simpl. apply In_insert_fset1.
        simpl. 
        apply In_insert_fset2. 
        apply IHx1; auto. 
  Qed.

  Definition intersection_fset (s1 s2 : fset) : fset  :=
    fold_right_fset fset (fun x s1' => if In_fset_dec x s2 then insert_fset x s1' else s1') empty_fset s1.
End FiniteSets.

Implicit Arguments insert_fset [X]. 
Implicit Arguments In_fset [X]. 
Implicit Arguments In_fset_dec [X]. 
Implicit Arguments size_fset [X]. 
Implicit Arguments pigeon_fset [X]. 
Implicit Arguments subset_fset [X]. 
Implicit Arguments eq_fset [X]. 
Implicit Arguments fold_left_fset [X B].
Implicit Arguments fold_right_fset [X B].
Implicit Arguments union_fset [X]. 
Implicit Arguments intersection_fset [X].

