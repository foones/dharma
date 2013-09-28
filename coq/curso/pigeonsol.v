(* The pigeon-hole principle for lists. 

   Includes a bunch of necessary supporting lemmas on diverse topics
   that we never got to elsewhere. 

*)

Require Export opsem4.
Require Export midterm.


(* A few more facts about le *)

 Lemma le_0_n : forall n, 0 <= n.
 Proof.
  induction n. 
    apply le_n.
    apply le_S. auto.
 Qed.

 Lemma le_n_S : forall n m, n <= m -> S n <= S m.
 Proof.
   intros n m P; induction P.  apply le_n.
   apply le_transitive with (S m).  apply IHP.  apply le_S.  apply le_n.
 Qed.


(* More facts about lists. *)

Definition In_dec : forall (X:Set),
    (forall x y:X, {x = y} + {x <> y}) ->
    forall (a:X) (l:list X), {In a l} + {~ In a l}.
Proof.
   (* SOLUTION *)
    intros X Xeq_dec.
    intros a l. induction l. 
      right. intro. inversion H. 
    inversion  IHl. 
      left. unfold In. right. auto.
      destruct (Xeq_dec a x); subst. 
        left. unfold In. left. auto.
      right. intro. inversion H0; auto. 
Defined.

Implicit Arguments In_dec [X].

Lemma In_index : forall (X:Set) (x:X) (xs:list X), In x xs -> exists n, index n xs = Some x.
 Proof.
   (* SOLUTION *)
   induction xs; intros.
   inversion H. 
   inversion H. 
   subst. exists 0. simpl. auto.
  generalize (IHxs H0). intro. inversion H1 as [n0 P].  exists (S n0). simpl. assumption.
 Qed.

Lemma index_Some : forall (X:Set) (xs: list X) n (x:X) , index n xs = Some x -> n < length xs. 
Proof.
   (* SOLUTION *)
   induction xs; intros.
   destruct n; simpl in H; inversion H. 
   destruct n. simpl.  unfold lt. apply le_n_S. apply le_0_n.   
    simpl in H. generalize (IHxs _ _ H).  intro. simpl.  unfold lt in H0 |- *. 
       apply le_n_S. auto.
Qed.


Fixpoint take (X:Set) (n:nat) (xs:list X) {struct n} : list X :=
match n with
| 0 => nil
| S n' => match xs with
          | nil => nil     
          | (x::xs') => x :: take X n' xs'
          end
end.
Implicit Arguments take [X].

Fixpoint drop (X:Set) (n:nat) (xs:list X) {struct n} : list X :=
match n with
| 0 => xs
| S n' => match xs with
          | nil => nil     
          | (x::xs') => drop X n' xs'
          end
end.
Implicit Arguments drop [X].

Lemma take_drop :forall (X:Set) i (xs:list X), take i xs ++ drop i xs = xs. 
Proof.
  induction i; intro xs.  
  auto. 
  destruct xs. 
    auto. 
    simpl.  rewrite IHi. auto. 
Qed.


Lemma index_take : forall (X:Set) i n (xs:list X), i < n -> index i (take n xs) = index i xs.          
Proof.
  intros X i n. generalize dependent i. induction n; intros i xs P. 
    inversion P. 
  destruct xs. 
    auto. 
    destruct i. 
      auto. 
      simpl. apply IHn. unfold lt in P |-*. apply Sn_le_Sm__n_le_m. auto. 
Qed.


Definition incl (X:Set) (l m:list X) := forall a:X, In a l -> In a m.
Implicit Arguments incl [X].

Lemma take_In : forall (X:Set) (x:X) xs n, In x (take n xs) -> In x xs.
Proof. 
  (* SOLUTION *)
  intros X x xs n. generalize dependent x. generalize dependent xs. induction n; intros xs x  P. 
    inversion P. 
    destruct xs. 
      inversion P. 
      simpl in P. 
      inversion P; subst. 
        unfold In; left; auto. 
        unfold In. right. apply IHn.  auto.
Qed.



Lemma take_incl :forall (X:Set) (xs ys:list X),  incl xs ys -> forall n, incl (take n xs) ys.
Proof.
  (* SOLUTION *)
  unfold incl. intros X xs ys P n a Q.  
  apply P.  eapply take_In.  apply Q. 
Qed.

Lemma take_length : forall (X:Set)(xs: list X) (n:nat), n <= length xs -> length(take n xs) = n.
Proof. 
 induction xs; intros n P.
   simpl in P. inversion P; subst. auto.  
   simpl in P. 
   destruct n. auto. 
   simpl.  rewrite IHxs.  auto. apply Sn_le_Sm__n_le_m. auto.
Qed.

(* Removing elements from list *)

Fixpoint remove (X:Set) (Xeq_dec: forall (x1 x2 : X), {x1 = x2} + {x1 <> x2})
                (x : X) (l : list X) {struct l} : list X :=
      match l with
        | nil => nil
        | y::tl => if (Xeq_dec x y) then remove X Xeq_dec x tl else y::(remove X Xeq_dec x tl)
      end.
Implicit Arguments remove [X].


Lemma remove_In : forall (X:Set) (Xeq_dec: forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}) 
                    (l : list X) (x : X), ~ In x (remove Xeq_dec x l).
Proof.
   (* SOLUTION *)
   intros X Xeq_dec l. induction l. 
      intros x P. simpl in P. auto.
      intros x0 P. 
      simpl in P. 
      destruct (Xeq_dec x0 x); subst. 
         apply (IHl x); auto. 
         simpl in P. inversion P. auto. apply (IHl x0); auto.
Qed.

Lemma In_stable_remove : forall (X:Set) (Xeq_dec: forall (x1 x2 : X), {x1 = x2} + {x1 <> x2})
                                (a:X) (a0: X) (xs : list X),
                                In a0 (remove Xeq_dec a xs) -> In a0 xs.
Proof. 
  (* SOLUTION *)
  intros X Xeq_dec a a0 xs. induction xs; intros H.
  simpl.  apply H. 
  simpl. simpl in H. 
  destruct (Xeq_dec a x); subst.  
     right. auto. 
     simpl in H. inversion H; subst. 
        left. auto. 
        right. auto. 
Qed.

Lemma remove_not_In: forall (X:Set) (Xeq_dec : forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}) 
                     (x:X) (xs:list X),
                     ~ In x xs -> remove Xeq_dec x xs = xs.
Proof.
  (* SOLUTION *)
  intros X Xeq_dec x xs. induction xs; intros P. 
    simpl. auto.
    simpl. destruct (Xeq_dec x x0); subst. 
       impossible. apply P. unfold In. left. auto. 
       rewrite IHxs.  auto. 
       intro C. apply P. right. auto.
Qed.


Lemma not_in_remove : forall (X:Set) (Xeq_dec: forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}) 
                      (xs: list X) (a a0 : X),  
                       ~In a xs -> ~In a (remove Xeq_dec a0 xs).
Proof.
  (* SOLUTION *)
  intros X Xeq_dec. induction xs; intros a a0 H.  
     simpl. auto.
     simpl. 
     destruct (Xeq_dec a0 x).  apply IHxs.
         intro. apply H. simpl. right. auto.
         intro. apply (IHxs a a0). 
            intro. apply H.  right. auto. 
            inversion H0; subst.
                impossible. apply H.  left; auto.
                auto.
Qed.

Lemma remove_one : forall (X:Set) (Xeq_dec : forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}) 
                   (x:X) (xs:list X),
                   In x xs -> NoDup xs -> length xs = S(length(remove Xeq_dec x xs)).
Proof.
  (* SOLUTION *)
  intros X Xeq_dec x xs. induction xs; intros H P.
    inversion H. 
    simpl.
    destruct (Xeq_dec x x0); subst. 
    rewrite remove_not_In. auto. 
      inversion P; subst.  auto.
    simpl.  rewrite <- IHxs.  auto. 
      inversion H. impossible. auto.  auto.
      inversion P; subst. auto. 
Qed.

Lemma NoDup_remove : forall (X:Set) (Xeq_dec : forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}) 
                    (xs:list X) (x:X), 
                     NoDup xs -> NoDup (remove Xeq_dec x xs).
Proof.
  (* SOLUTION *)
  intros X Xeq_dec. 
  induction xs.
   intros x H. simpl; auto. 
   intros x0 H. 
   simpl.
   destruct (Xeq_dec x0 x); subst.
     apply IHxs. inversion H. auto. 
     inversion H; subst.  
     apply NoDup_cons.
       apply not_in_remove. auto.
       apply IHxs. auto.
Qed.
     


Lemma incl_length : forall (X:Set), (forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}) ->      
      forall (ys xs : list X),
      incl xs ys -> NoDup xs -> length xs <= length ys.
Proof.
   (* This is not trivial ! *)
   (* SOLUTION *)
  intros X Xeq_dec ys. induction ys; intros xs H ND. 
  Case "nil".
     destruct xs. 
       simpl. apply le_n.
       impossible. unfold incl in H. apply (H x). left. auto.
  Case "cons".
     assert (length (remove Xeq_dec x xs) <= length ys).
       apply IHys.  
       unfold incl in H |- *. 
          intros a P. 
          destruct (Xeq_dec a x); subst. 
             impossible. apply (remove_In _ Xeq_dec xs x). auto.
          eapply In_not_head. apply H.  apply (In_stable_remove _ Xeq_dec _ _ _ P). auto.
          apply NoDup_remove. auto.
     simpl. 
     destruct (In_dec Xeq_dec x xs).
     SCase "In x xs".
       rewrite (remove_one _ Xeq_dec x); auto. 
       apply le_n_S.  auto. 
     SCase "~ In x xs".
       rewrite (remove_not_In _ Xeq_dec _ _ n) in H0.  
       apply le_transitive with (length ys).
         apply H0.  apply le_S. apply le_n.
Qed.

Lemma hasDup : 
  forall (X:Set), (forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}) ->
  forall (xs:list X), ~ NoDup xs -> 
    exists i, exists j, i < j /\ j < length xs /\ index i xs = index j xs. 
Proof.
  intros X Xeq_dec. induction xs; intros H.
  destruct H.  apply NoDup_nil. 
  destruct (In_dec Xeq_dec x xs). 
  exists 0.
    generalize (In_index _ x xs i). intros. inversion H0 as [n P]. exists (S n).
    simpl.
    split. unfold lt. apply le_n_S. apply le_0_n.  
    split. unfold lt. apply le_n_S. fold (lt n (length xs)). 
    apply index_Some with x. auto.
    apply sym_equal. auto.
  assert (~ NoDup xs). 
    intro. 
    apply H. 
    apply NoDup_cons; auto.
  destruct (IHxs H0) as [i [j [P [Q R]]]].
    exists (S i).  exists (S j). 
    split.  unfold lt. apply le_n_S. apply P. 
    split.  simpl.  unfold lt. apply le_n_S. apply Q.
    simpl. auto.
Qed.
  

Theorem pigeon :  forall (X:Set), 
  (forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}) ->
  forall (ys:list X), NoDup ys ->   (* this is actually superfluous! *)
  forall xs, incl xs ys -> length xs = S(length ys) ->
  exists i, exists j, i < j /\ j < length xs /\ index i xs = index j xs.
Proof.
  (* SOLUTION *)
  intros.   
  apply (hasDup _ H).
  intro.
  assert (~ (length xs <= length ys)).
    intro. rewrite H2 in H4. apply (Sn_not_le_n _ H4).
  apply H4.
  apply incl_length; auto.
Qed.

