Require Export List.
Require Export ListSet.
Require Export Arith.
Require Import Omega. 

Set Implicit Arguments.

(* More on sets *)

Definition set_subset (A:Set) (s1 s2:set A) := forall (a:A), set_In a s1 -> set_In a s2. 
Definition set_eq (A:Set)( s1 s2 : set A) := set_subset s1 s2 /\ set_subset s2 s1. 

Definition set_card (A:Set) (x: set A) := set_fold_right (fun _ => S)  x 0. 

(* The key lemma *)
Lemma pigeon : forall (X:Set) (xs:list X) s, (forall x, In x xs -> set_In x s) -> length xs > set_card s -> 
                 exists i, exists j, i < j /\ j <= set_card s /\ nth_error xs i = nth_error xs j.
Admitted. 

(* This lemma is true for ListSets built using set_add, because they have no duplicates.
   But we don't have the machinery to prove it yet. *)

Section language.

(* For simplicity, we allow an infinite alphabet. *)
Variable A : Set.

Definition word := list A. 

(* A language is a (possibly infinite) set of words described by its characteristic function. *)

Definition language := word -> Prop. 

Definition eq_language (l1 l2:language) := forall (w:word), l1 w <-> l2 w.  

Lemma eq_language_left : forall (l1 l2 : language), eq_language l1 l2 -> forall (w:word), l1 w -> l2 w.
unfold eq_language. intros l1 l2 P w. destruct (P w) as [P1 P2]. auto. 
Qed.

Lemma eq_language_right : forall (l1 l2 : language), eq_language l1 l2 -> forall (w:word), l2 w -> l1 w.
unfold eq_language. intros l1 l2 P w. destruct (P w) as [P1 P2]. auto. 
Qed.


(* Automata *)

Section automaton.

  Variable St:Set.  (* Type of states *)
  Axiom St_dec : forall (s1 s2:St), {s1 = s2} + {s1 <> s2}.

  Variable Q : set St.  (* Finite set of states *)
  Variable q0 : St.     (* Start state *)
  Variable F: set St.   (* Set of final states *)

  Variable delta : St -> A -> St.   (* Transition function *)

  Inductive dfa : Prop := 
     dfa_intro : 
     set_In q0 Q -> 
     set_subset F Q -> 
     (forall q, set_In q Q -> forall a, set_In (delta q a) Q) -> 
     dfa.

  Definition dfa_accepts (w:word) : Prop :=
    set_In (fold_left delta w q0) F.

End automaton.

End language.


Inductive regular (A:Set) (L: language A) : Prop :=
 | regular_intro:
      forall (St:Set) Q (q0:St) F delta, 
       dfa Q q0 F delta -> 
       eq_language L (dfa_accepts q0 F delta) ->
       regular L. 


Fixpoint L_01star (w: list nat) : Prop :=
  match w with
  | nil => True
  | (0::1::w') => L_01star w'
  | _ => False
  end.


Definition DFA_01star : dfa (set_add eq_nat_dec 0 (set_add eq_nat_dec 1 (set_add eq_nat_dec 2 (empty_set nat)))) 0 
                            (set_add eq_nat_dec 0 (empty_set nat))
            (fun s => fun a => match (s,a) with (0,0) => 1 | (1,1) => 0 | _ => 2 end).
apply dfa_intro.
   simpl. auto.
   simpl. unfold set_subset. intros. inversion H; subst.  simpl.  auto. inversion H0. 
   intros. inversion H; subst.  simpl. auto. 
   simpl in H0.  inversion H0; subst.  destruct a. simpl. auto. destruct a.  simpl. auto. simpl. auto.
   inversion H1; subst. destruct a; simpl; auto. 
   inversion H2. 
Defined.

Lemma L_01star_regular : regular L_01star.
Admitted.  (* Not so easy *)
    


(* ------------------ PUMPING LEMMA -------------------------------------- *)

(* First, some functions on lists, etc. *)

Fixpoint dup (X:Set) (n:nat) (xs:list X) {struct n } : list X :=
match n with
| 0 => nil
| S n' => xs++(dup n' xs)
end.


Fixpoint take (X:Set) (n:nat) (xs:list X) {struct n} : list X :=
match n with
| 0 => nil
| S n' => match xs with
          | nil => nil     
          | (x::xs') => x :: take n' xs'
          end
end.

Fixpoint drop (X:Set) (n:nat) (xs:list X) {struct n} : list X :=
match n with
| 0 => xs
| S n' => match xs with
          | nil => nil     
          | (x::xs') => drop n' xs'
          end
end.

Lemma take_drop :forall (X:Set) i (xs:list X), take i xs ++ drop i xs = xs. 
Proof.
  induction i; intro xs.  
  auto. 
  destruct xs. 
    auto. 
    simpl.  rewrite IHi. auto. 
Qed.


(* Iterate a function over a list, accumulating the results *)
Fixpoint accum (X Y:Set) (f:X->Y->X) (x:X) (ys:list Y) {struct ys} : list X :=
x ::
(match ys with
 | nil => nil
 | (y::ys') => let x' := f x y in accum f x' ys' 
 end).

(* Test *)
Lemma accum_test1 : accum (fun x => fun y => x+y) 0 (1::2::3::nil) = (0::1::3::6::nil).
auto.
Qed.

Lemma accum_length : forall (X Y:Set) f (x:X) (ys: list Y), length (accum f x ys) = S(length ys).
intros X Y f x ys. generalize dependent x. 
induction ys.
  auto.
  intro x.   simpl. rewrite IHys.  auto. 
Qed.

Lemma accum_fold_take : forall (X Y:Set) (xs:list X) (i:nat) (f:X->Y->X) (x0:X) (w:list Y), 
  i < length xs -> 
  xs = accum f x0 w -> 
  nth_error xs i = Some (fold_left f (@take Y i w) x0).
Proof.
  intros X Y xs i f x0 w. generalize dependent xs. generalize dependent x0. generalize dependent w.
  induction i; intros w x0 xs LT E. 
    subst xs. simpl. destruct w; subst. simpl. auto. simpl. auto.
    subst xs. simpl. destruct w; subst. 
        simpl in LT. inversion LT; subst. inversion H0. 
        simpl. apply IHi. simpl in LT. auto with arith.  auto.
Qed.

(* The key lemma *)
Lemma repeated_state : 
       forall A:Set,
       forall St:Set,
       forall Q : set St,
       forall delta, (forall q:St, set_In q Q -> forall a, set_In (delta q a) Q) -> 
       forall p, p = set_card Q -> 
       forall (w:list A), length w >= p ->
       forall q0, set_In q0 Q ->
         exists i, exists j, 
         i < j /\ j <= p /\ 
         fold_left delta (take i w) q0 = fold_left delta (take j w) q0.
intros.
set (qs := accum delta q0 w).
assert (length qs > p).
  unfold qs. rewrite accum_length. 
     auto with arith. 
assert (forall q, In q qs -> set_In q Q).
  clear H1 H3. generalize dependent q0. simpl.   
  induction w; intros q0 P1 q P2. 
    simpl in P2.  inversion P2. rewrite <- H1. auto. inversion H1.
    simpl in P2. 
    inversion P2.
      rewrite <- H1. apply P1.
      apply IHw with (delta q0 a). apply H. apply P1. 
      auto.
subst p.
destruct (pigeon qs Q H4 H3) as [i [j [LT [LE P]]]].
exists i. exists j.  split; auto.  split; auto with arith.
subst qs. 
rewrite (@accum_fold_take St A (accum delta q0 w) i delta q0 w) in P; auto. 
rewrite (@accum_fold_take St A (accum delta q0 w) j delta q0 w) in P; auto.  
inversion P. auto. 
omega.
omega.
Qed.


(* Pumping Lemma *)
Lemma pumping: 
     forall A,
     forall L: language A, 
     regular L -> 
     exists p, 
     forall w, L w -> length w >= p ->
     exists x, exists y, exists z,
     w = x ++ y ++ z /\ y <> nil /\ length (x ++ y) <= p /\ forall i, L (x++(dup i y)++z).
Proof.
   intros A L r.  inversion r; subst. inversion H. 
   set (p := set_card Q). 
   exists p.
   intros w P wlen.
   unfold dfa_accepts in P. 
   destruct (repeated_state Q delta H3 (refl_equal p) w wlen q0 H1) as [i [j [P1 [P2 P3]]]].
   replace (take j w) with (take i w ++ take (j-i) (drop i w)) in P3.
   exists (take i w). exists (take (j-i) (drop i w)). exists (drop (j-i) (drop i w)).
   split.
     rewrite take_drop. rewrite take_drop. reflexivity.
     split. 
       admit.  (* !! *)
       split. 
       admit.  (* !! *)
       intros i0.
       apply (eq_language_right H0).
       unfold dfa_accepts.
       rewrite fold_left_app.
       induction i0. 
         simpl.  
         rewrite P3.  
         rewrite <- fold_left_app. rewrite app_ass. rewrite take_drop. rewrite take_drop.  
         apply (eq_language_left H0) in P. apply P. 
         simpl.  rewrite app_ass.  rewrite <- fold_left_app. 
         rewrite <- app_ass.  rewrite fold_left_app. rewrite <- P3. apply IHi0.
   (* leftover *)
   admit. (* !! *)
Qed.
     
Inductive L_0n1n : list nat -> Prop :=
| L_0n1n_intro : forall n, forall w, w = dup n (0::nil) ++ dup n (1::nil) -> L_0n1n w.

Lemma L_0n1n_nor_regular : ~ (regular L_0n1n).
intro. destruct (pumping H) as [p P].
destruct (P (dup p (0::nil) ++ dup p (1::nil))).
  apply (L_0n1n_intro p).  auto.
  admit.
  destruct H0 as [y [z [P1 [P2 [P3 P4]]]]].
Admitted.