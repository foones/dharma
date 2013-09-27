Require Import logic4.


Inductive Permutation (A:Set) : list A -> list A -> Prop :=
| perm_nil: Permutation A nil nil
| perm_skip: forall (x:A) (l l':list A), Permutation A l l' -> Permutation A (cons x l) (cons x l')
| perm_swap: forall (x y:A) (l:list A), Permutation A (cons y (cons x l)) (cons x (cons y l))
| perm_trans: forall (l l' l'':list A), Permutation A l l' -> Permutation A l' l'' -> Permutation A l l''.
Implicit Arguments Permutation [A]. 

(* Suppose we'd like to prove the following innocent looking result: *)

Lemma Perm_nil: forall (A:Set) (l:list A), 
    Permutation l [] -> l = [].
Admitted.


(* One obvious approach is to try induction on [l]. *)
Lemma Perm_nil_try1: forall (A:Set) (l:list A),
  Permutation l [] -> l = [].
Proof.
 intros A.
   induction l; intros H. 
   reflexivity.
 
   (* Now we're stuck.  The IH doesn't help.
      We might try doing inversion on H... *)
   inversion H; subst. 
   (* .. but perm_trans constructor *always* applies,
      so we don't really get anywhere. *)
Admitted.

(* So, how about induction on [Permutation l nil] ? 
   This is likely to have more "information content,"
   so we probably should have tried it in the first place...
*)


Lemma Perm_nil_try2: forall (A:Set) (l:list A),
  Permutation l  [] -> l = [].
Proof.
  intros A l H. induction H. 
  Case "perm_nil".
    reflexivity.
  Case "perm_skip". 
    (* Hmm. Something has gone screwy here. 
       The fact that l' is nil has been lost somehow. 
       But at any rate, we can prove this case: *)
    rewrite IHPermutation. reflexivity.
  Case "perm_swap".
     (* but not this one! *)
     admit.
  Case "perm_trans". 
     rewrite IHPermutation1. apply IHPermutation2.
Qed.

(* To find out what's going wrong, let's take a look at
the induction principle for Permutation: *)

Check Permutation_ind.

(* Hmmm. To apply this principle, our goal needs to look like
[P l l0] where [l] and [l0] are lists.  But our actual goal
is [l = nil]. How did Coq decide to instantiate P ? 

We can find out by looking at the generated proof term: *)

Print Perm_nil_try2. 

(* Aha: Coq has chosen to instantiate P with a more 
general predicate than our goal, namely:

(fun l1 l2 : list A => l1 = l2)

But we can't possibly hope to prove that

forall l1 l2, Permutation l1 l2 -> l1 = l2    (!)

No wonder we ran into trouble on the Perm_swap case! *)

(* Perhaps we can do better by forcing Coq to use a narrower
choice of P by applying Permutation_ind explictly. *)

Lemma Perm_nil_try3: forall (A:Set) (l:list A),
  Permutation l [] -> l = [].
Proof.
  intros A l H. 
  apply (Permutation_ind A (fun l => fun _ => l = [])) with (@nil A); (* a little fiddly *)
    intros.
  Case "perm_nil".
    reflexivity.
  Case "perm_skip". 
    (* Oops. Now the induction hypothesis is too weak
       to prove even this case. *)
    admit.
  Case "perm_swap".
     (* much less this one *)
     admit.
  Case "perm_trans". 
     apply H1. 
  apply H. 
Qed.

(* This phenomenon is quite common: induction over an overly-specific
instance of an inductive proposition doesn't work.   The standard trick
to get around this is to *generalize* the proposition, adding the instance
information as an extra hypothesis.  

Here's one way to do that in this case: *)
Lemma Perm_lnil: forall (A:Set) (lnil l:list A),
  lnil = [] -> Permutation l lnil -> l = [].
Proof. intros A l lnil E P. 
  induction P. 
   Case "perm_nil".
     auto.   
   Case "perm_skip".
     inversion E. 
   Case "perm_swap".
     inversion E. 
   Case "perm_trans".
     auto. 
Qed.


Lemma Perm_nil_ok1: forall (A:Set) (l:list A),
  Permutation l [] -> l = [].
Proof.
  intros A l P. apply Perm_lnil with (@nil A); auto. 
Qed.


(* There are various tricks by which you can avoid
actually using a separate lemma if that offends you. *)



(* It is also always worth considering a completely
different attack on the problem.  Here's an approach
based on the idea that Permutation preserves list length: *)

Lemma Perm_len : forall (A: Set) (l l' : list A), 
    Permutation l l' -> length l = length l'.
Proof. 
  intros A l l' P.  induction P; subst; simpl; auto. 
  rewrite IHP1; auto.
Qed.

Lemma Perm_nil_ok2: forall (A:Set) (l:list A),
  Permutation l [] -> l = [].
Proof.
  intros A l P.  
  destruct l.  
    auto. 
    apply Perm_len in P.  inversion P. 
Qed.





