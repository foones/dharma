(** * Functional Programming 
    *** Version of 9/29/2008
*)




(* -------------------------------------------------------------- *)
(** ** Days of the week *)

Inductive day : Set :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day. 

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday saturday)).

Lemma test_next_weekday: 
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

(* -------------------------------------------------------------- *)
(** ** Booleans *)

Inductive bool : Set :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Lemma test_orb1:    (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Lemma test_orb2:    (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Lemma test_orb3:    (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Lemma test_orb4:    (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(** Exercise: Uncomment and then complete the definitions of the
    following functions, making sure that the assertions below each can
    be verified by Coq. *)
(* This function should return [true] if either or both of its inputs
   are [false]. *)
Definition norb (b1:bool) (b2:bool) : bool :=
  (* SOLUTION *)
  match b1 with
  | true => negb b2
  | false => true
  end.

Lemma test_norb1:               (norb true false) = true.
Proof. simpl. reflexivity. Qed.
Lemma test_norb2:               (norb false false) = true.
Proof. simpl. reflexivity. Qed.
Lemma test_norb3:               (norb false true) = true.
Proof. simpl. reflexivity. Qed.
Lemma test_norb4:               (norb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (* SOLUTION *)
  match b1 with
  | true =>
      match b2 with
      | true => b3
      | false => false
      end
  | false => false
  end.

Lemma test_andb31:                 (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Lemma test_andb32:                 (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Lemma test_andb33:                 (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Lemma test_andb34:                 (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.


(* -------------------------------------------------------------- *)
(** ** Numbers *)

(** Technical note: Coq provides a sophisticated module system, to aid
    in organizing large and complex developments.  In this course, we
    won't need most of its features, but one is useful: if we enclose a
    collection of declarations between [Module X] and [End X] markers,
    then, in the remainder of the file after the [End], all these
    definitions will be referred to by names like [X.foo] instead of
    just [foo].  This means that the new definition will not clash with
    the unqualified name [foo] later, which would otherwise be an
    error (a name can only be defined once in a given scope).

    Here, we use this feature to introduce the definition of [nat] in
    an inner module so that it does not shadow the one from the
    standard library, which provides a little bit of magic for writing
    numbers using standard arabic numerals.
*)
Module Nat.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

End Nat.

Definition pred (m : nat) : nat :=
  match m with
    | O => O
    | S m' => m'
  end.

Definition minustwo (m : nat) : nat :=
  match m with
    | O => O
    | S O => O
    | S (S m') => m'
  end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

Check pred.
Check minustwo.
Check S.
 
Fixpoint evenb (n:nat) {struct n} : bool := 
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Lemma test_oddb1:    (oddb (S O)) = true.
Proof. simpl. reflexivity. Qed.
Lemma test_oddb2:    (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity. Qed.

Fixpoint plus (m : nat) (n : nat) {struct m} : nat :=
  match m with
    | O => n
    | S m' => S (plus m' n)
  end.

Eval simpl in (plus (S (S (S O))) (S (S O))).

Fixpoint times (m n : nat) {struct m} : nat :=
  match m with
    | O => O
    | S m' => plus (times m' n) n
  end.

Fixpoint minus (m n : nat) {struct n} : nat :=
  match n with
    | O => m
    | S n' => minus (pred m) n'
  end.

Fixpoint exp (base power : nat) {struct power} : nat :=
  match power with
    | O => S O
    | S p => times base (exp base p)
  end.

Lemma test_times1:             (times 3 3) = 9.
Proof. simpl. reflexivity. Qed.

(** Exercise *)
Fixpoint factorial (n:nat) {struct n} : nat :=
  (* SOLUTION *)
  match n with
  | O => 1
  | S n' => times n (factorial n')
  end.

Lemma test_factorial1:          (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Lemma test_factorial2:          (factorial 5) = (times 10 12).
Proof. simpl. reflexivity. Qed.

Fixpoint beq_nat (m n : nat) {struct m} : bool :=
  match m with 
  | O =>
      match n with 
      | O => true
      | S n' => false
      end
  | S m' =>
      match n with
      | O => false
      | S n' => beq_nat m' n'
      end
  end.

(** Exercise *)
Fixpoint ble_nat (m n : nat) {struct m} : bool :=
  (* SOLUTION *)
  match m with 
  | O =>
    true
  | S m' =>
      match n with
      | O => false
      | S n' => ble_nat m' n'
      end
  end.
Lemma test_ble_nat1:             (ble_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.
Lemma test_ble_nat2:             (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Lemma test_ble_nat3:             (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (m n : nat) :=
  (* SOLUTION *)
  (ble_nat (S m) n).

Lemma test_blt_nat1:             (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Lemma test_blt_nat2:             (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Lemma test_blt_nat3:             (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)  (at level 50, left associativity).
Notation "x - y" := (minus x y)  (at level 50, left associativity).
Notation "x * y" := (times x y)  (at level 40, left associativity).

(* -------------------------------------------------------------- *)
(** ** Pairs of numbers *)

(** Technical note: Here, we again use the Module feature to wrap all
    of the definitions for pairs and lists of numbers in a module so
    that, later, we can use the same names for the
    generic ("polymorphic") versions of the same operations. *)
Module NatList.

Inductive prodnat : Set :=
  pair : nat -> nat -> prodnat.

Definition fst (p : prodnat) : nat := 
  match p with
  | pair x y => x
  end.
Definition snd (p : prodnat) : nat := 
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Eval simpl in (fst (3,4)).

Definition fst' (p : prodnat) : nat := 
  match p with
  | (x,y) => x
  end.
Definition snd' (p : prodnat) : nat := 
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : prodnat) : prodnat := 
  match p with
  | (x,y) => (y,x)
  end.

(* -------------------------------------------------------------- *)
(** ** Lists of numbers *)

Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition l123 := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Definition l123'   := 1 :: (2 :: (3 :: nil)).
Definition l123''  := 1 :: 2 :: 3 :: nil.
Definition l123''' := [1,2,3].

Definition head (l:natlist) : nat :=
  match l with
  | nil => 0  (** arbitrarily *)
  | h :: t => h
  end.

Definition tail (l:natlist) : natlist :=
  match l with
  | nil => nil  
  | h :: t => t
  end.

Fixpoint repeat (n count : nat) {struct count} : natlist := 
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) {struct l} : nat := 
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) {struct l1} : natlist := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Lemma test_app1:             [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. simpl. reflexivity. Qed.
Lemma test_app2:             nil ++ [4,5] = [4,5].
Proof. simpl. reflexivity. Qed.
Lemma test_app3:             [1,2,3] ++ nil = [1,2,3].
Proof. simpl. reflexivity. Qed.

(** Exercises *)
Fixpoint nonzeros (l:natlist) {struct l} : natlist :=
  (* SOLUTION *)
  match l with
  | nil => nil 
  | h :: t =>
      match h with
      | O => nonzeros t
      | S h' => h :: (nonzeros t)
      end
  end.

Lemma test_nonzeros:            nonzeros [0,1,0,2,3,0,0] = [1,2,3].
Proof. simpl. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) {struct l} : natlist :=
  (* SOLUTION *)
  match l with
  | nil => nil 
  | h :: t =>
      match (oddb h) with
      | true => h :: (oddmembers t)
      | false => oddmembers t
      end
  end.

Lemma test_oddmembers:            oddmembers [0,1,0,2,3,0,0] = [1,3].
Proof. simpl. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) {struct l} : nat :=
  (* SOLUTION *)
  match l with
  | nil => O
  | h :: t =>
      match (oddb h) with
      | true => S (countoddmembers t)
      | false => (countoddmembers t)
      end
  end.

Lemma test_countoddmembers1:    countoddmembers [1,0,3,1,4,5] = 4.
Proof. simpl. reflexivity. Qed.
Lemma test_countoddmembers2:    countoddmembers [0,2,4] = 0.
Proof. simpl. reflexivity. Qed.
Lemma test_countoddmembers3:    countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) {struct l1} : natlist :=
  (* SOLUTION *)
  match l1 with
  | nil => l2
  | h1 :: t1 =>
      match l2 with
      | nil => l1
      | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
      end
  end.

Lemma test_alternate1:        alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
Proof. simpl. reflexivity. Qed.
Lemma test_alternate2:        alternate [1] [4,5,6] = [1,4,5,6].
Proof. simpl. reflexivity. Qed.
Lemma test_alternate3:        alternate [1,2,3] [4] = [1,4,2,3].
Proof. simpl. reflexivity. Qed.

(* SOLUTION *)
Fixpoint snoc (l:natlist) (v:nat) {struct l} : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint reverse (l:natlist) {struct l} : natlist := 
  (* SOLUTION *)
  match l with
  | nil    => nil
  | h :: t => snoc (reverse t) h
  end.

Lemma test_reverse1:            reverse [1,2,3] = [3,2,1].
Proof. simpl. reflexivity. Qed.
Lemma test_reverse2:            reverse nil = nil.
Proof. simpl. reflexivity. Qed.

(* -------------------------------------------------------------- *)
(** Exercise: Bags via lists *)
Definition bag := natlist.  

Fixpoint count (v:nat) (s:bag) {struct s} : nat := 
  (* SOLUTION *)
  match s with
  | nil => 0
  | h :: t => 
      match beq_nat h v with
      | false => count v t
      | true => S (count v t)
      end
  end.

Lemma test_count1:              count 1 [1,2,3,1,4,1] = 3.
Proof. simpl. reflexivity. Qed.
Lemma test_count2:              count 6 [1,2,3,1,4,1] = 0.
Proof. simpl. reflexivity. Qed.

Definition union := 
  (* SOLUTION *)
  app.

Lemma test_union1:              count 1 (union [1,2,3] [1,4,1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := 
  (* SOLUTION *)
  v :: s.

Lemma test_add1:                count 1 (add 1 [1,4,1]) = 3.
Proof. simpl. reflexivity. Qed.
Lemma test_add2:                count 5 (add 1 [1,4,1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool := 
  (* SOLUTION *)
  negb (beq_nat (count v s) 0).

Lemma test_member1:             member 1 [1,4,1] = true.
Proof. simpl. reflexivity. Qed.
Lemma test_member2:             member 2 [1,4,1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) {struct s} : bag :=
  (* SOLUTION *)
  match s with
  | nil => nil
  | h :: t => 
      match beq_nat h v with
      | true => t
      | false => h :: (remove_one v t)
      end
  end.

Lemma test_remove_one1:         count 5 (remove_one 5 [2,1,5,4,1]) = 0.
Proof. simpl. reflexivity. Qed.
Lemma test_remove_one2:         count 5 (remove_one 5 [2,1,4,1]) = 0.
Proof. simpl. reflexivity. Qed.
Lemma test_remove_one3:         count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
Proof. simpl. reflexivity. Qed.
Lemma test_remove_one4: 
  count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) {struct s} : bag :=
  (* SOLUTION *)
  match s with
  | nil => nil
  | h :: t => 
      match beq_nat h v with
      | true => remove_all v t
      | false => h :: (remove_all v t)
      end
  end.

Lemma test_remove_all1:          count 5 (remove_all 5 [2,1,5,4,1]) = 0.
Proof. simpl. reflexivity. Qed.
Lemma test_remove_all2:          count 5 (remove_all 5 [2,1,4,1]) = 0.
Proof. simpl. reflexivity. Qed.
Lemma test_remove_all3:          count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
Proof. simpl. reflexivity. Qed.
Lemma test_remove_all4:          count 5 (remove_all 5 [2,1,5,4,5,1,4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) {struct s1} : bool :=
  (* SOLUTION *)
  match s1 with 
  | nil => true
  | h1 :: t1 => 
      andb (member h1 s2)
               (subset t1 (remove_one h1 s2))
  end.

Lemma test_subset1:              subset [1,2] [2,1,4,1] = true.
Proof. simpl. reflexivity. Qed.
Lemma test_subset2:              subset [1,2,2] [2,1,4,1] = false.
Proof. simpl. reflexivity. Qed.

(* -------------------------------------------------------------- *)
(** ** Options *)

Inductive natoption : Set :=
  | Some : nat -> natoption
  | None : natoption.  

Fixpoint index_bad (n:nat) (l:natlist) {struct l} : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
  | a :: l' => match beq_nat n O with true => a 
               | false => index_bad (pred n) l' end
  end.

Fixpoint index (n:nat) (l:natlist) {struct l} : natoption :=
  match l with
  | nil => None 
  | a :: l' => match beq_nat n O with true => Some a
               | false => index (pred n) l' end
  end.

Lemma test_index1 :    index 0 [4,5,6,7]  = Some 4.
Proof. simpl. reflexivity. Qed.
Lemma test_index2 :    index 3 [4,5,6,7]  = Some 7.
Proof. simpl. reflexivity. Qed.
Lemma test_index3 :    index 10 [4,5,6,7] = None.
Proof. simpl. reflexivity. Qed.

Fixpoint index' (n:nat) (l:natlist) {struct l} : natoption :=
  match l with
  | nil => None 
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Fixpoint beq_natlist (l1 l2 : natlist) {struct l1} : bool :=
  (* SOLUTION *)
  match l1,l2 with 
  | nil,nil => true
  | h1::t1,h2::t2 => andb (beq_nat h1 h2) (beq_natlist t1 t2)
  | _,_ => false
  end.


Lemma test_beq_natlist1 :   (beq_natlist nil nil = true).
Proof. simpl. reflexivity. Qed.
Lemma test_beq_natlist2 :   beq_natlist [1,2,3] [1,2,3] = true.
Proof. simpl. reflexivity. Qed.
Lemma test_beq_natlist3 :   beq_natlist [1,2,3] [1,2,4] = false.
Proof. simpl. reflexivity. Qed.


(* -------------------------------------------------------------- *)
(** * Programming with Functions *)

(** ** Higher-order functions *)

Definition doit3times (f:nat->nat) (n:nat) := f (f (f n)).

Lemma test_doit3times1:   doit3times minustwo 9 = 3.
Proof. simpl. reflexivity. Qed.

Fixpoint filter (p: nat->bool) (l: natlist) {struct l} 
                : natlist :=
  match l with 
  | nil => nil
  | h::t => if p h then h :: (filter p t)
            else filter p t
  end.

Lemma test_filter1 :    filter evenb [4,5,6,7] = [4,6].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers' (l:natlist) : nat := 
  length (filter oddb l).

Lemma test_countoddmembers'1:   countoddmembers' [1,0,3,1,4,5] = 4.
Proof. simpl. reflexivity. Qed.
Lemma test_countoddmembers'2:   countoddmembers' [0,2,4] = 0.
Proof. simpl. reflexivity. Qed.
Lemma test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. simpl. reflexivity. Qed.

(** Exercise *)
Fixpoint doublematches (p: nat->bool) (l: natlist) {struct l} 
                       : natlist :=
  (* SOLUTION *)
  match l with 
  | nil => nil
  | h::t => if p h then h :: h :: (doublematches p t)
            else h :: (doublematches p t)
  end.

Lemma test_doublematches :   doublematches evenb [4,5,6,7] = [4,4,5,6,6,7].
Proof. simpl. reflexivity. Qed.

Fixpoint map (f:nat->nat) (l:natlist) {struct l} 
             : natlist := 
  match l with
  | nil    => nil 
  | h :: t => (f h) :: (map f t)
  end.

Lemma test_map1:    map minustwo [1,2,3,4,5] = [0,0,1,2,3].
Proof. simpl. reflexivity. Qed.
Lemma test_map2:    map S [1,2,3,4] = [2,3,4,5].
Proof. simpl. reflexivity. Qed.

(* Exercise *)
Definition map_filter (p:nat->bool) (f:nat->nat) (l:natlist) : natlist := 
  (* SOLUTION *)
  map f (filter p l).

Lemma test_map_filter:       map_filter evenb minustwo [1,2,3,4] = [0,2].
Proof. simpl. reflexivity. Qed.

(* Exercise *)
Definition countzeros (l:natlist) : nat := 
  (* SOLUTION *)
  length (filter (beq_nat 0) l).

Lemma test_countzeros1:           countzeros [1,0,3,0,4,5] = 2.
Proof. simpl. reflexivity. Qed.

(** ** Partial application *)

Check plus.
Definition plus3 : nat->nat := plus 3.

Lemma test_plus3 :    plus3 4 = 7.
Proof. simpl. reflexivity. Qed.
Lemma test_plus3' :   map (plus 3) [1,2,3,4] = [4,5,6,7].
Proof. simpl. reflexivity. Qed.

(** ** Anonymous functions *)  

Eval simpl in (map (fun n => times n n) [2,0,3,1]).

Lemma test_doit3times4:   doit3times (fun n => minus (times n 2) 1) 2 = 9.
Proof. simpl. reflexivity. Qed.

(* ** A different implementation of bags *)

Definition bagf := nat -> nat.  

Definition countf (v:nat) (s:bagf) : nat := 
  s v.

Definition emptybagf : bagf := (fun n => 0).

Lemma test_emptybagf1:           countf 3 emptybagf = 0.
Proof. simpl. reflexivity. Qed.  

(* A bagf containing the numbers 5 (once) and 6 (twice): *)
Definition bagf566 : bagf := 
  fun n =>
    if beq_nat n 5 then 1
    else if beq_nat n 6 then 2
    else 0.

Lemma test_bagf566_1:             countf 5 bagf566 = 1.
Proof. simpl. reflexivity. Qed.  
Lemma test_bagf566_2:             countf 6 bagf566 = 2.
Proof. simpl. reflexivity. Qed.  
Lemma test_bagf566_3:             countf 7 bagf566 = 0.
Proof. simpl. reflexivity. Qed.  

Definition addf (m:nat) (b:bagf) := 
  fun (n:nat) => 
    match beq_nat m n with 
    | false => b n
    | true => S (b n)
    end.

Lemma test_addf1:                countf 3 (addf 3 emptybagf) = 1.
Proof. simpl. reflexivity. Qed.  

(* A function that converts from the old representation of bags to the
   new one. *)
Fixpoint bag2bagf (b:bag) {struct b} : bagf :=
  match b with
  | nil => emptybagf
  | h::t => addf h (bag2bagf t)
  end.

Lemma test_bag2bagf1:            countf 1 (bag2bagf [1,2,3,1,4,1]) = 3.
Proof. simpl. reflexivity. Qed.  
Lemma test_bag2bagf2:            countf 5 (bag2bagf [1,2,3,1,4,1]) = 0.
Proof. simpl. reflexivity. Qed.  

(* Exercise *)
Definition unionf (b1 b2 : bagf) := 
  (* SOLUTION *)
  fun n => plus (countf n b1) (countf n b2).

Lemma test_unionf1:  
  countf 1 (unionf (bag2bagf [1,2,3]) (bag2bagf [1,4,1])) 
  = 3.
Proof. simpl. reflexivity. Qed.

Definition remove_onef (v:nat) (s:bagf) : bagf :=
  (* SOLUTION *)
  fun n => 
    match beq_nat n v with
    | false => s n
    | true => pred (s n)
    end.

Lemma test_remove_onef1: 
  countf 5 (remove_onef 5 (bag2bagf [2,1,5,4,1])) 
  = 0.
Proof. simpl. reflexivity. Qed.
Lemma test_remove_onef2: 
  countf 5 (remove_onef 5 (bag2bagf [2,1,4,1])) 
  = 0.
Proof. simpl. reflexivity. Qed.
Lemma test_remove_onef3: 
  countf 4 (remove_onef 5 (bag2bagf [2,1,4,5,1,4])) 
  = 2.
Proof. simpl. reflexivity. Qed.
Lemma test_remove_onef4: 
  countf 5 (remove_onef 5 (bag2bagf [2,1,5,4,5,1,4])) 
  = 1.
Proof. simpl. reflexivity. Qed.

(* Can you write a [subset] function for this variant of bags? *)
(* SOLUTION: No -- this would require asking one of the bags for its
   counts for EVERY number, which cannot be done in finite time. *)

End NatList.

(* ---------------------------------------------------------------------- *)
(** ** Polymorphism *)

Definition doit3times_bool (f:bool->bool) (n:bool) : bool := 
  f (f (f n)).

Definition doit3times (X:Set) (f:X->X) (n:X) : X := 
  f (f (f n)).

Lemma test_doit3times1:  doit3times nat minustwo 9 = 3.
Proof. simpl. reflexivity. Qed.
Lemma test_doit3times2:  doit3times nat (plus 3) 2 = 11.
Proof. simpl. reflexivity. Qed.
Lemma test_doit3times3:  doit3times bool negb true = false.
Proof. simpl. reflexivity. Qed.

Check doit3times.

(* ---------------------------------------------------------------------- *)
(** ** Polymorphic lists *)

Inductive list (X:Set) : Set :=
  | nil : list X
  | cons : X -> list X -> list X.

Check nil.
Check cons.

Fixpoint length (X:Set) (l:list X) {struct l} : nat := 
  match l with
  | nil      => 0
  | cons h t => S (length X t)
  end.

Fixpoint app (X : Set) (l1 l2 : list X) {struct l1} 
                : (list X) := 
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

(* Exercise *)
Fixpoint repeat (X : Set) (n : X) (count : nat) {struct count} : list X := 
  (* SOLUTION *)
  match count with
  | O => nil X
  | S count' => cons X n (repeat X n count')
  end.

Lemma test_repeat1: 
  repeat bool true 2 = cons bool true (cons bool true (nil bool)).
Proof. simpl. reflexivity. Qed.

(* SOLUTION *)
Fixpoint snoc (X:Set) (l:list X) (v:X) {struct l} : (list X) := 
  match l with
  | nil      => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint reverse (X:Set) (l:list X) {struct l} : list X := 
  (* SOLUTION *)
  match l with
  | nil      => nil X
  | cons h t => snoc X (reverse X t) h
  end.

Lemma test_reverse1:            
    reverse nat (cons nat 1 (cons nat 2 (nil nat))) 
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. simpl. reflexivity. Qed.
Lemma test_reverse2: 
  reverse bool (nil bool) = nil bool.
Proof. simpl. reflexivity. Qed.


(** ** Implicit arguments *)

Fixpoint length' (X:Set) (l:list X) {struct l} : nat := 
  match l with
  | nil      => 0
  | cons h t => S (length' _ t)
  end.

Definition l123 := 
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition l123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Implicit Arguments nil [X].
Implicit Arguments cons [X].
Implicit Arguments length [X].
Implicit Arguments app [X].
Implicit Arguments reverse [X].
(* If these were defined... *)
Implicit Arguments repeat [X].
Implicit Arguments snoc [X].
Implicit Arguments reverse [X].

Notation "x :: y" := (cons x y) 
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) 
                     (at level 60, right associativity).

Definition l123'' := [1,2,3].

(** ** Polymorphic lists, continued *)

Fixpoint filter (X:Set) (test: X->bool) (l:list X) 
                {struct l} : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter _ test t)
                        else       filter _ test t
  end.

Implicit Arguments filter [X].

Lemma test_filter1: 
  filter evenb [1,2,3,4] = [2,4].
Proof. simpl. reflexivity. Qed.
Lemma test_filter2: 
  filter (fun l => beq_nat (length l) 1) 
         [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. simpl. reflexivity. Qed.
  
Fixpoint map (X:Set) (Y:Set) (f:X->Y) (l:list X) {struct l} 
             : (list Y) := 
  match l with
  | []     => []
  | h :: t => (f h) :: (map _ _ f t)
  end.

Implicit Arguments map [X Y].


(* This fails:
Definition mynil := nil. *)

Definition mynil := @nil nat.

Lemma test_map1: 
  map (plus 3) [2,0,2] = [5,3,5].
Proof. simpl. reflexivity. Qed.
Lemma test_map2: 
  map oddb [2,1,2,5] = [false,true,false,true].
Proof. simpl. reflexivity. Qed.
Lemma test_map3: 
    map (fun n => repeat false n) [2,1,3] 
  = [ [false,false], [false], [false,false,false] ].
Proof. simpl. reflexivity. Qed.

(** Exercise *)
Fixpoint flatmap (X:Set) (Y:Set) (f:X -> list Y) (l:list X) {struct l} 
                   : (list Y) := 
  (* SOLUTION *)
  match l with
  | []     => []
  | h :: t => (f h) ++ (flatmap _ _ f t)
  end.

Implicit Arguments flatmap [X Y].

Lemma test_flatmap1: 
  flatmap (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof. simpl. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Polymorphic pairs *)

Inductive prod (X Y : Set) : Set :=
  pair : X -> Y -> prod X Y.

Implicit Arguments pair [X Y].

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst (X Y : Set) (p : X * Y) : X := 
  match p with (x,y) => x end.

Implicit Arguments fst [X Y].

Definition snd (X Y : Set) (p : X * Y) : Y := 
  match p with (x,y) => y end.

Implicit Arguments snd [X Y].

Fixpoint zip (X Y : Set) (lx : list X) (ly : list Y) 
           {struct lx} : list (X*Y) :=
  match lx with
  | [] => []
  | x::tx => match ly with
             | [] => []
             | y::ty => (x,y) :: (zip _ _ tx ty)
             end
  end.

Check zip.

Implicit Arguments zip [X Y]. 

Eval simpl in (zip [1,2] [false,false,true,true]).

(* Exercise *)
Fixpoint unzip 
  (* SOLUTION *)
           (X Y : Set) (l : list (X*Y)) {struct l} 
           : (list X) * (list Y) :=
  match l with
  | [] => 
      ([], []) 
  | cons (x,y) t => 
      match unzip _ _ t with
        (lx,ly) => (x::lx, y::ly)
      end
  end.

Check unzip.

Implicit Arguments unzip [X Y].

Definition test_unzip :=
  unzip [(1,false),(2,false)] = ([1,2],[true,false]).


(* ---------------------------------------------------------------------- *)
(** ** Polymorphic options *)

Inductive option (X:Set) : Set :=
  | Some : X -> option X
  | None : option X.

Implicit Arguments Some [X].
Implicit Arguments None [X].

(* Exercise *)
Fixpoint index 
  (* SOLUTION *)
             (X : Set) (n : nat)
             (l : list X) {struct l} : option X :=
  match l with
  | [] => None 
  | a :: l' => if beq_nat n O then Some a else index _ (pred n) l'
  end.

Implicit Arguments index [X].

Lemma test_index1 :    index 0 [4,5,6,7]  = Some 4.
Proof. simpl. reflexivity. Qed.
Lemma test_index2 :    index  1 [[1],[2]]  = Some [2].
Proof. simpl. reflexivity. Qed.
Lemma test_index3 :    index  2 [true]  = None.
Proof. simpl. reflexivity. Qed.


(* Exercise *)
Definition head (X : Set) (l : list X)  : option X :=
  (* SOLUTION *)
  match l with
  | [] => None 
  | a :: l' => Some a 
  end.

Implicit Arguments head [X].

Lemma test_head1 :    @head nat [] = None.
Proof. simpl. reflexivity. Qed.
Lemma test_head2 :  head [1,2] = Some 1. 
Proof. simpl. reflexivity. Qed.
Lemma test_head3 :   head  [[1],[2]]  = Some [1].
Proof. simpl. reflexivity. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Example: Permutations of a list *)

Fixpoint inserteverywhere (X:Set) (v:X) (l:list X) 
                          {struct l} : (list (list X)) := 
  match l with
  | []     => [[v]]
  | h :: t =>
         (v :: l) ::
         (map (cons h) (inserteverywhere _ v t))
  end.

Implicit Arguments inserteverywhere [X].

Lemma test_inserteverywhere1: 
    inserteverywhere 3 [0,0,0]
  = [[3, 0, 0, 0], [0, 3, 0, 0],
     [0, 0, 3, 0], [0, 0, 0, 3]].
Proof. simpl. reflexivity. Qed.

Definition inserteverywhereall 
                 (X:Set) (v:X) (l:list (list X)) 
                 : (list (list X)) :=  
  flatmap (inserteverywhere v) l.

Implicit Arguments inserteverywhereall [X].

Lemma test_inserteverywhereall1: 
    inserteverywhereall 3 [[0,0,0],[0,0,0]]
  = [[3, 0, 0, 0], [0, 3, 0, 0],
     [0, 0, 3, 0], [0, 0, 0, 3],
     [3, 0, 0, 0], [0, 3, 0, 0],
     [0, 0, 3, 0], [0, 0, 0, 3]].
Proof. simpl. reflexivity. Qed.

Fixpoint perm (X: Set) (l:list X) {struct l} 
              : (list (list X)) := 
  match l with
  | [] => [[]]
  | h :: t =>
      inserteverywhereall h (perm X t)
  end.

Implicit Arguments perm [X].

Lemma test_perm1: 
    perm l123
  = [[1, 2, 3], [2, 1, 3], [2, 3, 1],
     [1, 3, 2], [3, 1, 2], [3, 2, 1]].
Proof. simpl. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Example: Currying and uncurrying *)

Definition curry (X Y Z : Set) (f : X * Y -> Z) 
                 : X -> Y -> Z :=
  fun x => fun y => f (x,y).

Definition uncurry (X Y Z : Set) (f : X -> Y -> Z) 
                   : (X * Y) -> Z :=
  fun p => 
    match p with
      (x,y) => f x y
    end.

Check curry.
Check uncurry.


(* ---------------------------------------------------------------------- *)
(** ** Non-structural recursion *)

Fixpoint all_interleavings_aux 
            (c:nat) (X:Set) (l1 : list X) (l2 : list X) 
            {struct c} : list (list X) :=
  match c with
  | O => []   (** Out of steam: return something silly *)
  | S c' =>
    match l1 with
    | nil => l2 :: []
    | h1 :: t1 =>
        match l2 with
        | nil => l1 :: []
        | h2 :: t2 => 
              (map (cons h1) 
                       (all_interleavings_aux c' _ t1 l2))
           ++ (map (cons h2) 
                       (all_interleavings_aux c' _ l1 t2))
        end end end.

Implicit Arguments all_interleavings_aux [X].

Definition all_interleavings 
               (X:Set) (l1 : list X) (l2 : list X) 
               : (list (list X)) :=
  all_interleavings_aux (length (l1 ++ l2)) l1 l2.

Implicit Arguments all_interleavings [X].

Lemma test_all_interleavings1: 
    all_interleavings [1,2] [3,4]
  = [[1, 2, 3, 4], [1, 3, 2, 4],
     [1, 3, 4, 2], [3, 1, 2, 4],
     [3, 1, 4, 2], [3, 4, 1, 2]].
Proof. simpl. reflexivity. Qed.


