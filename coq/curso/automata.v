Require Export fset.

Section language.

  Variable A : Set.  (* The underlying alphabet.  Might be infinite (we don't care).  *)
  
  Definition word := list A.  (* A word over the alphabet *)

  Definition language := word -> Prop. (* A language (i.e. set of strings) over the alphabet, represented by the set's membership function *)

  Definition eq_language (l1 l2:language) := forall (w:word), l1 w <-> l2 w.  

  Lemma eq_language_1 : forall (l1 l2 : language), eq_language l1 l2 -> forall (w:word), l1 w -> l2 w.
  Proof.
    unfold eq_language. intros l1 l2 P w. destruct (P w) as [P1 P2]. auto. 
  Qed.

  Lemma eq_language_2 : forall  (l1 l2 : language), eq_language l1 l2 -> forall (w:word), l2 w -> l1 w.
  Proof.
    unfold eq_language. intros l1 l2 P w. destruct (P w) as [P1 P2]. auto. 
  Qed.

  (* Automata *)

  Section automata. 
    
    Inductive dfa : Type :=
    dfa_intro : forall (St:Set),                         (* underlying type of states *)
                forall (St_eq_dec : forall (s1 s2 : St), {s1 = s2} + {s1 <> s2}), (* decidable equality on states *)
                forall (Q: fset St),                     (* set of states *)
                forall (q0 : St), In_fset q0 Q ->        (* start state *)
                forall (F: fset St), subset_fset F Q ->  (* final states *)
                forall (delta: St -> A -> St),           (* transition function *)
                  (forall q, In_fset q Q -> forall a, In_fset (delta q a) Q) -> 
                dfa.

    Definition dfa_accepts (d:dfa) (w:word) : Prop :=
        match d with
        | dfa_intro _ _ _ q0 _ F _ delta _ => 
            In_fset (fold_left delta w q0) F
      end.

    Definition regular (L: language) : Prop :=
      exists d, eq_language L (dfa_accepts d).

End automata.

End language.

Implicit Arguments regular [A]. 


(* ------------------ PUMPING LEMMA -------------------------------------- *)

(* First, some functions on lists, etc. *)

Fixpoint dup (X:Set) (n:nat) (xs:list X) {struct n } : list X :=
match n with
| 0 => nil
| S n' => xs++(dup X n' xs)
end.
Implicit Arguments dup [X]. 


(* Iterate a function over a list, accumulating the results *)
Fixpoint scanl (X Y:Set) (f:X->Y->X) (x:X) (ys:list Y) {struct ys} : list X :=
x ::
(match ys with
 | nil => nil
 | (y::ys') => scanl X Y f (f x y) ys' 
 end).
Implicit Arguments scanl [X Y].

(* Test *)
Lemma scanl_test1 : scanl (fun x => fun y => x+y) 0 (1::2::3::nil) = (0::1::3::6::nil).
Proof.
  auto.
Qed.

Lemma scanl_length : forall (X Y:Set) f (x:X) (ys: list Y), length (scanl f x ys) = S(length ys).
Proof.
  intros X Y f x ys. generalize dependent x. 
  induction ys.
    auto.
    intros x0.   simpl. rewrite IHys.  auto. 
Qed.


Lemma scanl_foldl_take : forall (X Y:Set) (xs:list X) (i:nat) (f:X->Y->X) (x0:X) (w:list Y), 
  xs = scanl f x0 w -> 
  i < length xs -> 
  index i xs = Some (fold_left f (@take Y i w) x0).
Proof.
  intros X Y xs i f x0 w. generalize dependent xs. generalize dependent x0. generalize dependent w.
  induction i; intros w x0 xs E LT. 
    subst xs. simpl. destruct w; subst. simpl. auto. simpl. auto.
    subst xs. simpl. destruct w; subst. 
        simpl in LT. inversion LT; subst. inversion H0. 
        simpl. apply IHi. auto. simpl in LT. unfold lt in LT |- *. apply Sn_le_Sm__n_le_m. auto. 
Qed.


(* The key lemma *)
Lemma repeated_state : 
       forall A:Set,
       forall St:Set, (forall (s1 s2 : St), {s1 = s2} + {s1 <> s2}) -> 
       forall Q : fset St,
       forall delta, (forall q:St, In_fset q Q -> forall a, In_fset (delta q a) Q) -> 
       forall p, p = size_fset Q -> 
       forall (w:list A), p <= length w ->
       forall q0, In_fset q0 Q ->
         exists i, exists j, 
         i < j /\ j <= p /\ 
         fold_left delta (take i w) q0 = fold_left delta (take j w) q0.
Proof.
  intros A St St_eq_dec Q delta H p H0 w H1 q0 H2.
  set (qs := scanl delta q0 w).
  assert (p < length qs).
    unfold qs. rewrite scanl_length. 
       unfold lt.  apply le_n_S. auto.
  assert (forall q, In q qs -> In_fset q Q).
    clear H1 H3. generalize dependent q0. simpl.   
    induction w; intros q0 P1 q P2. 
      simpl in P2.  inversion P2. rewrite <- H1. auto. inversion H1.
      simpl in P2. 
      inversion P2.
        rewrite <- H1. apply P1.
        apply IHw with (delta q0 x). apply H. apply P1. 
        auto.
  subst p.
  destruct (pigeon_fset St_eq_dec qs Q H4 H3) as [i [j [LT [LE P]]]].
  exists i. exists j.  split; auto.  split.  auto. 
  subst qs. 
  rewrite (@scanl_foldl_take St A (scanl delta q0 w) i delta q0 w) in P; auto. 
  rewrite (@scanl_foldl_take St A (scanl delta q0 w) j delta q0 w) in P; auto.  
  inversion P. auto. 
  unfold lt. unfold lt in H3. apply le_transitive with (S(size_fset Q)).
     apply le_n_S. auto. apply H3. 
  unfold lt. unfold lt in LT. apply le_transitive with (size_fset Q).
     apply le_transitive with j. auto. auto.
     unfold lt in H3.  apply le_transitive with (S(size_fset Q)). 
     apply le_S. apply le_n.  auto.
Qed.

(* There is some kind of strange scoping problem with the infix notation "-" *)
Lemma take_drop_app: forall (X:Set) (xs:list X) i j, i <= j ->
       take j xs = (take i xs ++ take (minus j i) (drop i xs)).
Proof.
  intros X xs i j. generalize dependent xs. generalize dependent i. induction j; intros i xs LE. 
    inversion LE. simpl. auto.
    destruct xs. 
       destruct i; subst.
         auto. simpl. destruct (minus j i); simpl; auto.  
       destruct i; subst.
         auto.
         simpl. rewrite <- IHj. auto. apply Sn_le_Sm__n_le_m. auto.
Qed.          

Lemma length_take : forall (X:Set) n (xs:list X), n <= length xs -> length (take n xs) = n.
Proof.
  intros X n. induction n; intros xs LE. 
    auto.
    destruct xs. inversion LE. 
      simpl.  rewrite IHn.  auto. apply Sn_le_Sm__n_le_m. apply LE. 
Qed.


Lemma length_drop : forall (X:Set) n (xs:list X), length (drop n xs) = minus (length xs) n.
Proof.  
  intros X n. induction n; intros xs.
    auto. 
    destruct xs. simpl. 
       clear IHn. induction n; auto. 
       simpl. auto.
Qed.


Lemma le_O_n : forall n, 0 <= n.
Proof.
  induction n.  apply le_n. apply le_S. auto.
Qed.

Lemma le_minus : forall m n1 n2, n1 <= n2 -> minus n1 m <= minus n2 m.
Proof.
  intros m. induction m; intros n1 n2 LE. 
  auto.
  simpl. apply IHm. 
      destruct n1; simpl.  apply le_O_n.
      destruct n2; simpl. inversion LE. apply Sn_le_Sm__n_le_m. auto.
Qed.

Lemma lt_minus_nonzero: forall n m, n < m -> minus m n <> 0.
Proof.  
  intros n. induction n; intros m LT.
  simpl.  intro. rewrite H in LT.  inversion LT. 
  simpl. apply IHn. destruct m.  inversion LT. 
    simpl. unfold lt in LT |- *.  apply Sn_le_Sm__n_le_m. auto.
Qed.

Lemma plus_minus : forall n m, n <= m -> plus n (minus m n) = m.
Proof. 
  intros n. induction n; intros m LT.
  simpl.  auto.
  simpl. rewrite IHn. 
    inversion LT; subst; auto.
    inversion LT; subst; simpl. apply le_n.  apply Sn_le_Sm__n_le_m. auto.
Qed.

(* Pumping Lemma *)
Lemma pumping: 
     forall A,
     forall L: language A, 
     regular L -> 
     exists p, 
     forall w, L w -> p <= length w  ->
     exists x, exists y, exists z,
     w = x ++ y ++ z /\ y <> nil /\ length (x ++ y) <= p /\ forall i, L (x++(dup i y)++z).
Proof.
   intros A L r.  inversion r as [d H].
   destruct d as [St St_eq_dec Q q0 q0_OK F F_Ok delta delta_OK].
   set (p := size_fset Q). 
   exists p.
   intros w P wlen.
   unfold dfa_accepts in H. 
   destruct (repeated_state A St St_eq_dec Q delta delta_OK p (refl_equal p) w wlen q0 q0_OK) as [i [j [P1 [P2 P3]]]].
   replace (take j w) with (take i w ++ take (minus j i) (drop i w)) in P3. 
   exists (take i w). exists (take (minus j i) (drop i w)). exists (drop (minus j i) (drop i w)).
   split.
     rewrite take_drop. rewrite take_drop. reflexivity.
     split. 
       intro.  assert (length (take (minus j i) (drop i w)) = 0). rewrite H0. auto. 
          rewrite length_take in H1. apply (lt_minus_nonzero _ _ P1). auto.
          rewrite length_drop. apply le_minus. apply le_transitive with p;auto . 
       split. 
          rewrite length_append. rewrite length_take. rewrite length_take. 
            rewrite plus_minus. auto. unfold lt in P1.  apply le_S_le. auto.
          rewrite length_drop. apply le_minus.  apply le_transitive with p; auto.
          apply le_transitive with j.  unfold lt in P1. apply le_S_le. auto.
          apply le_transitive with p; auto. 
       intros i0.
       apply (eq_language_2 A _ _ H).
       rewrite fold_left_app.
       induction i0. 
         simpl.  
         rewrite P3.  
         rewrite <- fold_left_app. rewrite <- append_assoc. rewrite take_drop. rewrite take_drop.  
         apply (eq_language_1 A _ _ H) in P. apply P. 
         simpl.  rewrite <- append_assoc.  rewrite <- fold_left_app. 
         rewrite append_assoc.  rewrite fold_left_app. rewrite <- P3. apply IHi0.
   apply sym_eq.
   apply take_drop_app. 
   unfold lt in P1. apply le_S_le.  auto. 
Qed.
     



