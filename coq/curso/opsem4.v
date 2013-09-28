(** * A First Taste of Types
    *** Version of 11/12/2008
*)

(* The last part of the book introduces the key topic of
   TYPES in programming languages.  

   We begin in this chapter with an extremely simple
   language of arithmetic and boolean expressions -- a
   language just barely complex enough to have the
   possibility of programs "going wrong" because of type
   errors.  We present a typing relation that classifies
   terms of this language into ones that return numbers and
   ones that return booleans, we prove the classical
   PRESERVATION and PROGRESS theorems, and we conclude by
   showing that well-typed programs don't get stuck. *)

Require Export opsem3. 



(* ---------------------------------------------------- *)
(* Types *)

Module FullArithTypes.
Export FullArith.

Inductive ty : Set := 
  | ty_bool : ty
  | ty_nat : ty.

Inductive has_type : tm -> ty -> Prop :=
  | T_True : 
         has_type tm_true ty_bool
  | T_False : 
         has_type tm_false ty_bool
  | T_If : forall t1 t2 t3 T,
         has_type t1 ty_bool
      -> has_type t2 T
      -> has_type t3 T
      -> has_type (tm_if t1 t2 t3) T
  | T_Zero : 
         has_type tm_zero ty_nat
  | T_Succ : forall t1,
         has_type t1 ty_nat
      -> has_type (tm_succ t1) ty_nat
  | T_Pred : forall t1,
         has_type t1 ty_nat
      -> has_type (tm_pred t1) ty_nat
  | T_Iszero : forall t1,
         has_type t1 ty_nat
      -> has_type (tm_iszero t1) ty_bool.


Theorem progress : forall t T,
     has_type t T
  -> value t \/ exists t', step1 t t'.
Proof.
  intros t T HT.
  induction HT.
    Case "T_True". 
      left. unfold value. left. apply bv_true. 
    Case "T_False". 
      left. unfold value. left. apply bv_false.
    Case "T_If". 
      right. 
      destruct IHHT1. 
        SCase "t1 is a value". destruct H. 
          SSCase "t1 is a bvalue". destruct H.
            SSSCase "t1 is tm_true". 
              exists t2. 
              apply E_IfTrue.
            SSSCase "t1 is tm_false". 
              exists t3. 
              apply E_IfFalse.
          SSCase "t1 is an nvalue". 
              solve by inversion 2.  (* on H and HT1 *)
        SCase "t1 can take a step". 
          destruct H as [t1' H1]. 
          exists (tm_if t1' t2 t3).
          apply E_If. assumption.
    (* FILL IN HERE (and delete "Admitted") *) Admitted.

Theorem preservation : forall t t' T,
     has_type t T
  -> step1 t t'
  -> has_type t' T.
Proof.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple 
            of things *)
         intros t' HE; 
         (* and we can deal with several impossible
            cases all at once *)
         try (solve by inversion).
    Case "T_If". inversion HE; subst. 
      SCase "E_IfTrue". assumption.
      SCase "E_IfFalse". assumption.
      SCase "E_If". apply T_If. apply IHHT1. 
        assumption. assumption. assumption.
    (* FILL IN HERE (and delete "Admitted") *) Admitted.

Theorem preservation' : forall t t' T,
     has_type t T
  -> step1 t t'
  -> has_type t' T.
Proof.
  (* Now prove the same property again by induction on the
     EVALUATION derivation instead of on the typing
     derivation.  Begin by carefully reading and thinking
     about the first few lines of the above proof to make
     sure you understand what each one is doing.  The set-up
     for this proof is similar, but not exactly the same. *)
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

Notation stepmany := (refl_step_closure step1).

Theorem soundness : forall t t' T,
  has_type t T -> 
  stepmany t t' ->
  ~ stuck t'. 
intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.   
  apply IHP.  apply (preservation x y T HT H).
  unfold stuck. split; auto.  
Qed.

End FullArithTypes.

