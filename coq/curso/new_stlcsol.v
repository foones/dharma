(* Basic metatheory for Simply-Typed Lambda-Calculus, using
   capture-incurring substitution -- ok for CBV evaluation 
   of closed terms.
   Based on Pierce Lecture 17, but with substantially cleaner proofs. 

   Andrew Tolmach, April 2008. 
*)
 
Require Export logic5.

(* First, some useful tactics for dealing with beq_nat. *)

(* A simple but effective tactic for case splitting. *)

Ltac case_beq_nat x y :=
 let E := fresh "E" in 
 case_eq (beq_nat x y); intro E; 
     [(try (rewrite E in *|-); apply (beq_nat_true x y) in E; subst x) 
     | (try (rewrite E in *|-); apply beq_nat_false in E)] .


(* Note to those who care:

Here [case_eq P] is a built-in Coq tactic that behaves 
very similarly to [remember P as e; destruct e].
It should be possible to write a similar tactic using 'remember'
rather than 'case_eq'; indeed, this would be a little simpler:

Ltac case_beq_nat x y :=
 remember (beq_nat x y) as TTT; destruct TTT; apply sym_eq in HeqTTT; 
    [ apply (beq_nat_true x y) in HeqTTT; subst x
    | apply beq_nat_false in HeqTTT].

But Ltac doesn't believe that 'TTT' is in scope after
executing the 'remember'. Of course, it would be desirable to use
a fresh name instead of TTT anyhow, for robustness, but
that is stymied by the need to guess the name of the equality
hypothesis (here 'HeqTTT') constructed by 'remember'. 

*)


(* A more general tactic for handling beq_nat's in the goal. *)
Ltac elim_beq_nat :=
 repeat (
  match goal with
  | |- context[beq_nat ?x ?x] => rewrite beq_nat_n_n
  | |- context[beq_nat ?x ?y] => case_beq_nat x y; 
                               try match goal with
                               | H: ?z <> ?z |- _ => impossible; auto
                               end
  end).
  

(* Now to the definition of the simply-typed lambda-calculus. *)

Inductive ty : Set :=
  | ty_base  : nat -> ty
  | ty_arrow : ty -> ty -> ty.

Inductive tm : Set :=
  | tm_var : nat -> tm   
  | tm_app : tm -> tm -> tm
  | tm_abs : nat -> ty -> tm -> tm.

(* Define what it means for a variable to appear free in a term. *)
Inductive appears_free_in : nat -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tm_var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)
  | afi_abs : forall x y T t1,
        y <> x 
     -> appears_free_in x t1
     -> appears_free_in x (tm_abs y T t1).

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(*  Substitution is the main "engine" of evaluation for
the lambda-calculus.  Important: normally, substitution
is defined to be "capture-avoiding."   The definition here
does not have this property.  Fortunately, this doesn't 
matter so long as we only do call-by-value reduction of 
closed terms. *)

Fixpoint subst (x:nat) (s:tm) (t:tm) {struct t} : tm :=
  match t with
  | tm_var y => if beq_nat x y then s else t
  | tm_abs y T t1 =>  if beq_nat x y then t else tm_abs y T (subst x s t1)
  | tm_app t1 t2 => tm_app (subst x s t1) (subst x s t2)
  end.


Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tm_abs x T t).

Inductive step1 : tm -> tm -> Prop :=
  | E_AppAbs : forall x T t12 v2,
         value v2
      -> step1 (tm_app (tm_abs x T t12) v2) (subst x v2 t12)
  | E_App1 : forall t1 t1' t2,
         step1 t1 t1'
      -> step1 (tm_app t1 t2) (tm_app t1' t2)
  | E_App2 : forall v1 t2 t2',
         value v1
      -> step1 t2 t2'
      -> step1 (tm_app v1 t2) (tm_app v1  t2').


(* Define contexts. *)
Definition alist (X : Set) := list (nat * X).

Fixpoint lookup (X : Set) (k : nat) (l : alist X) {struct l} : option X :=
  match l with
  | nil => None
  | (j,a) :: l' =>
      if beq_nat j k then Some a else lookup X k l'
  end.
Implicit Arguments lookup [X].

Definition binds (X:Set) (k:nat) (v:X) (l:alist X) :=
  lookup k l = Some v.
Implicit Arguments binds [X].

Definition not_bound_in (X:Set) (k:nat) (l:alist X) :=
  lookup k l = None.
Implicit Arguments not_bound_in [X].

Definition context := (alist ty). 

Definition empty : context := nil.

 
(* The typing relation *)
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      binds x T Gamma ->
      has_type Gamma (tm_var x) T
  | T_Abs : forall Gamma x T1 T2 t,
      has_type ((x,T1) :: Gamma) t T2 -> 
      has_type Gamma (tm_abs x  T1 t) (ty_arrow T1 T2)
  | T_App : forall S T Gamma t1 t2,
      has_type Gamma t1 (ty_arrow S T) -> 
      has_type Gamma t2 S -> 
      has_type Gamma (tm_app t1 t2) T.


(* Some basic facts about free variables and contexts. *)

(* I found this lemma very useful for proving the next one. *)
Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   has_type Gamma t T ->
   exists T', binds x T' Gamma.
Proof. 
  (* SOLUTION *)
  intros. generalize dependent Gamma. generalize dependent T. 
  induction H; intros T0 Gamma HT; inversion HT; subst.
  Case "afi_var". 
    exists T0. assumption.
  Case "afi_app1".
    eapply IHappears_free_in.  apply H3. 
  Case "afi_app2". 
    eauto. 
  Case "afi_abs".
    destruct (IHappears_free_in T2 ((y,T)::Gamma) H6) as [x0 H2]. 
    unfold binds in H2. simpl in H2.  
    case_beq_nat y x.  
      impossible; auto. 
      exists x0. auto. 
Qed.

Lemma typable_empty_closed : forall t T, 
    has_type empty t T ->
    closed t.
Proof.
  intros t T H. unfold closed. intros x H1.
  destruct (free_in_context x t T empty H1 H) as [x0 H0]. 
  inversion H0. 
Qed.


(* This is a key helper lemma for the following substitition lemma. *)
Lemma context_invariance : forall Gamma Gamma' t S,
     has_type Gamma t S ->
     (forall x, appears_free_in x t -> lookup x Gamma = lookup x Gamma') ->
     has_type Gamma' t S.
Proof. 
  (* SOLUTION *)
  intros Gamma Gamma' t S H H0. 
  generalize dependent Gamma'. 
  induction H; intros.  
  Case "T_Var". 
    apply T_Var. unfold binds in *|-*. rewrite <- H0. assumption. apply afi_var. 
  Case "T_Abs".
    apply T_Abs. 
    apply IHhas_type. intros x0 afi. 
    simpl.
    elim_beq_nat.
      reflexivity. 
      apply H0. apply afi_abs;  assumption. 
  Case "T_App". 
    apply T_App with S. 
    apply IHhas_type1. intros. apply H1. apply afi_app1. assumption.
    apply IHhas_type2. intros. apply H1. apply afi_app2. assumption.
Qed.


(* This is the key lemma; almost all the non-trivial reasoning in this
file occurs here. *)
Lemma substitution_preserves_typing : forall Gamma x U v t S,
     has_type ((x,U)::Gamma) t S -> 
     has_type empty v U  -> 
     has_type Gamma (subst x v t) S.
Proof.
 intros Gamma x U v t S Ht Hv. 
 generalize dependent Gamma.  generalize dependent S. 
 induction t;  intros S Gamma H.
 (* SOLUTION *)
 simpl. 
 inversion H; subst.  inversion H2.
 elim_beq_nat. 
  inversion H1; subst. 
   eapply context_invariance. 
   apply Hv. 
   intros.
   assert (closed v) as C.  eapply typable_empty_closed.  apply Hv. 
   destruct (C x).  assumption.
  apply T_Var.  unfold binds.  assumption. 
 simpl. inversion H; subst.  eapply T_App with S0. 
  apply IHt1. assumption.
  apply IHt2. assumption. 
 simpl. 
  inversion H; subst.
  elim_beq_nat.
   apply T_Abs. 
     eapply context_invariance. apply H5. 
     intros. 
     simpl.
     elim_beq_nat; reflexivity.   
   apply T_Abs. 
     apply IHt.
     eapply context_invariance. apply H5. 
       intros. 
       simpl. 
       elim_beq_nat; reflexivity.
Qed. 


(* As usual, type safety boils down to 
preservation + progress. *)

Theorem preservation : forall t t' T,
     has_type empty t T -> 
     step1 t t' -> 
     has_type empty t' T.
remember empty as Gamma.   (* this is a trick to get [induction] to work right *)
intros t t' T HT. generalize dependent t'.   
induction HT; intros t' HE;  subst Gamma.
(* SOLUTION *)
inversion HE. 
inversion HE. 
inversion HE; subst.  
  apply substitution_preserves_typing with S.
    inversion HT1; assumption.  
    assumption.
  apply T_App with S. 
    apply IHHT1. reflexivity. assumption.  
    assumption.
  apply T_App with S.
    assumption.
    apply IHHT2. reflexivity. assumption.
Qed.


Theorem progress : forall t T, 
       has_type empty t T ->
       value t \/ exists t', step1 t t'. 
Proof.
  (* SOLUTION *)
  intros t T Ht.
  remember empty as Gamma. 
  induction Ht;  subst Gamma.  
   inversion H. 
   left. apply v_abs.
   right.
   inversion Ht1; subst.  
     destruct (IHHt1 (refl_equal empty)).
       inversion H0. 
       inversion H0. inversion H1.
     destruct (IHHt2 (refl_equal empty)). 
       econstructor. apply E_AppAbs. assumption.
       inversion H. econstructor. apply E_App2. apply v_abs. apply H0. 
     destruct (IHHt1 (refl_equal empty)).
       inversion H1. 
       inversion H1. econstructor. apply E_App1. apply H2. 
Qed.



