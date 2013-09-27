(* The pigeon-hole principle for lists. 

   Includes a bunch of necessary supporting lemmas on diverse topics
   that we never got to elsewhere. 

*)

Require Import opsem4.
Require Import midterm.


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
   (* FILL IN HERE (and delete "Admitted") *) Admitted.

Implicit Arguments In_dec [X].

Lemma In_index : forall (X:Set) (x:X) (xs:list X), In x xs -> exists n, index n xs = Some x.
 Proof.
   (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma index_Some : forall (X:Set) (xs: list X) n (x:X) , index n xs = Some x -> n < length xs. 
Proof.
   (* FILL IN HERE (and delete "Admitted") *) Admitted.


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
  (* FILL IN HERE (and delete "Admitted") *) Admitted.



Lemma take_incl :forall (X:Set) (xs ys:list X),  incl xs ys -> forall n, incl (take n xs) ys.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

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
   (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma In_stable_remove : forall (X:Set) (Xeq_dec: forall (x1 x2 : X), {x1 = x2} + {x1 <> x2})
                                (a:X) (a0: X) (xs : list X),
                                In a0 (remove Xeq_dec a xs) -> In a0 xs.
Proof. 
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma remove_not_In: forall (X:Set) (Xeq_dec : forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}) 
                     (x:X) (xs:list X),
                     ~ In x xs -> remove Xeq_dec x xs = xs.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.


Lemma not_in_remove : forall (X:Set) (Xeq_dec: forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}) 
                      (xs: list X) (a a0 : X),  
                       ~In a xs -> ~In a (remove Xeq_dec a0 xs).
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma remove_one : forall (X:Set) (Xeq_dec : forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}) 
                   (x:X) (xs:list X),
                   In x xs -> NoDup xs -> length xs = S(length(remove Xeq_dec x xs)).
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Lemma NoDup_remove : forall (X:Set) (Xeq_dec : forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}) 
                    (xs:list X) (x:X), 
                     NoDup xs -> NoDup (remove Xeq_dec x xs).
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.


Lemma incl_length : forall (X:Set), (forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}) ->      
      forall (ys xs : list X),
      incl xs ys -> NoDup xs -> length xs <= length ys.
Proof.
   (* This is not trivial ! *)
   (* FILL IN HERE (and delete "Admitted") *) Admitted.

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
  forall (ys:list X), NoDup ys -> 
  forall xs, incl xs ys -> length xs = S(length ys) ->
  exists i, exists j, i < j /\ j < length xs /\ index i xs = index j xs.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

