
Structure EstructuraDeMonoide
            (C : Set)
            (e : C)
            (op : C -> C -> C) :=
  mkEstructuraDeMonoide {
    EM_assoc  : forall x y z,  op (op x y) z = op x (op y z) ;
    EM_neut_l : forall x,      op e x = x ;
    EM_neut_r : forall x,      op x e = x
  }.

Structure EstructuraDeGrupo
            (C : Set)
            (e : C)
            (op : C -> C -> C)
            (inv : C -> C) :=
  mkEstructuraDeGrupo {
    EG_monoide : EstructuraDeMonoide C e op ; 
    EG_inv_r   : forall x,      op x (inv x) = e
  }.

Structure Grupo := mkGrupo {
  C   : Set ;           (* carrier *)
  e   : C ;             (* elemento neutro *)
  op  : C -> C -> C ;   (* operación binaria *)
  inv : C -> C ;        (* inverso *)

  es_grupo : EstructuraDeGrupo C e op inv
}.

Definition carrier (G : Grupo) : Set := C G.

Section Ejemplo_Grupo_ℤ2.
  
  Inductive ℤ2_carrier : Set :=
    | O : ℤ2_carrier
    | I : ℤ2_carrier.
  
  Let f (x : ℤ2_carrier) (y : ℤ2_carrier) : ℤ2_carrier :=
    match x with
    | O => y
    | I => match y with
           | O => I
           | I => O
           end
    end.

   Eval compute in (f (f O I) (f I I)).

   (* f asociativa *)
   Lemma ℤ2_G1 : forall a b c,  f (f a b) c = f a (f b c).
     intros a b c.
     case a; case b; case c; trivial.
   Qed.
   
   (* O neutro a izquierda *)
   Lemma ℤ2_G2 : forall a,  f O a = a.
     trivial.
   Qed.

   (* O neutro a derecha *)
   Lemma ℤ2_G3 : forall a,  f a O = a.
     intros a.
     case a; trivial.
   Qed.

   (* Cada elemento es inverso de sí mismo. *)
   Lemma ℤ2_G4 : forall a,  f a a = O.
     intros a.
     case a; trivial.
   Qed.
   
   Definition ℤ2 : Grupo :=
     mkGrupo
       ℤ2_carrier   (* carrier *)
       O            (* elemento neutro *)
       f            (* operación binaria *)
       (fun x => x) (* inverso *)
       (mkEstructuraDeGrupo _ _ _ _
         (mkEstructuraDeMonoide _ _ _ ℤ2_G1 ℤ2_G2 ℤ2_G3)
         ℤ2_G4).

End Ejemplo_Grupo_ℤ2.

Notation "x · y" := (op _ x y) (at level 20).
Notation "x ⁻¹"  := (inv _ x) (at level 5).
Notation "1"     := (e _).

Section Propiedades_Básicas.

    Variable G : Grupo.

    Lemma assoc : forall x y z : carrier G,  (x · y) · z = x · (y · z).
      intros.
      apply (EM_assoc (carrier G) (e G) (op G)).
      apply (EG_monoide (carrier G) (e G) (op G) (inv G)).
      apply es_grupo.
    Qed.

    Lemma neut_l : forall x : carrier G,  1 · x = x.
      intros.
      apply (EM_neut_l (carrier G) (e G) (op G)).
      apply (EG_monoide (carrier G) (e G) (op G) (inv G)).
      apply es_grupo.
    Qed.

    Lemma neut_r : forall x : carrier G,  x · 1 = x.
      intros.
      apply (EM_neut_r (carrier G) (e G) (op G)).
      apply (EG_monoide (carrier G) (e G) (op G) (inv G)).
      apply es_grupo.
    Qed.

    Lemma inv_r : forall x : carrier G,  x · x⁻¹ = 1.
      intros.
      apply (EG_inv_r (carrier G) (e G) (op G) (inv G)).
      apply es_grupo.
    Qed.
    
    Lemma cancel_r :  forall x y z : carrier G,  x·z = y·z  ->  x = y.
      intros x y z H.
      assert ( x·(z·z⁻¹) = y·(z·z⁻¹) ) as H'.
        rewrite <-? assoc.
        rewrite H.
        reflexivity.
      rewrite inv_r, ? neut_r in H'.
      assumption.
    Qed.

    Lemma inv_l : forall x : carrier G,  x⁻¹ · x = 1.
      intros x.
      apply cancel_r with (z := x⁻¹).
      rewrite assoc, inv_r, neut_r, neut_l.
      reflexivity.
    Qed.

    Lemma cancel_l : forall x y z : carrier G,  z·x = z·y  ->  x = y.
      intros x y z H.
      assert ( (z⁻¹·z)·x = (z⁻¹·z)·y ) as H'.
        rewrite ? assoc, H; reflexivity.
      rewrite inv_l, ? neut_l in H'.
      assumption.
    Qed.    

    (* Inverso del neutro *)
    Lemma inv_1 : 1⁻¹ = (1 : carrier G).
      apply cancel_l with 1.
      rewrite inv_r.
      rewrite neut_r.
      reflexivity.
    Qed.

    (* Inverso del producto *)
    Lemma inv_xy : forall x y : carrier G,  (x · y)⁻¹ = y⁻¹ · x⁻¹.
      intros x y.
      apply cancel_l with (x · y).
      rewrite inv_r, assoc. 
      replace (y·(y⁻¹·x⁻¹)) with ((y·y⁻¹)·x⁻¹). 
      rewrite inv_r, neut_l, inv_r.
      reflexivity.
      apply assoc.
    Qed.

    (* Inverso del inverso *)
    Lemma inv_inv : forall x : carrier G, x⁻¹⁻¹ = x.
      intro x.
      apply cancel_l with x⁻¹.
      rewrite inv_r.
      rewrite inv_l.
      reflexivity.
    Qed.
    
End Propiedades_Básicas.

Section Grupo_Simétrico.
  
  Require Import ProofIrrelevance.
  Require Import FunctionalExtensionality.
  Load Defs.

  (* El grupo simétrico depende de un parámetro: un conjunto X *)
  Variable X : Set.
  
  Let composición (f g : X -> X) := fun x => f (g x).

  Let Id (x : X) := x.

  Notation "f ∘ g" := (composición f g) (at level 20).
  
  Lemma composición_id :
    forall f g,  f ∘ g = Id  ->  forall x,  f (g x) = x.
  Proof.
    intros f g H x.
    apply equal_f with x in H.
    compute in H.
    assumption.
  Qed.    

  Let inversas (F G : X -> X) := F ∘ G = Id  /\  G ∘ F = Id.

  (* El siguiente va a ser el carrier del grupo simétrico.
   * Sus elementos son tuplas de la forma (F, G, inv_FG)
   * donde   F G : X -> X
   *         inv_FG : inversas F G
   * (inv_FG es evidencia de que F y G son inversas).   
   *)
  Structure Permutación := mkPerm {
                             F      : X -> X ;
                             G      : X -> X ;
                             inv_FG : inversas F G
                           }.

  (* Lema técnico: toda permutación está determinada por F y G.
   * Usa proof_irrelevance.
   *)
  Lemma perm_eq :
    forall σ τ,
      F σ = F τ  ->  G σ = G τ  ->  σ = τ.
  Proof.
    intros σ τ eq_F eq_G.
    destruct σ as (F1, G1, inv1).
    destruct τ as (F2, G2, inv2).
    assert (F1 = F2) as Fs. assumption.
    assert (G1 = G2) as Gs. assumption.
    destruct Fs, Gs.
    replace inv1 with inv2.
    reflexivity.
    apply proof_irrelevance.
  Qed.

  (* La operación del grupo simétrico es la composición. *)
  Let sym_op (σ τ : Permutación) : Permutación.
    apply mkPerm with (F := F σ ∘ F τ) (G := G τ ∘ G σ).
    split.
      (* F ∘ G *)
      apply functional_extensionality.
      intro x; unfold composición.
      rewrite (composición_id (F τ) (G τ)).
      rewrite (composición_id (F σ) (G σ)).
      reflexivity.
      apply (inv_FG σ).
      apply (inv_FG τ).

      (* G ∘ F *)
      apply functional_extensionality.
      intro x; unfold composición.
      rewrite (composición_id (G σ) (F σ)).
      rewrite (composición_id (G τ) (F τ)).
      reflexivity.
      apply (inv_FG τ).
      apply (inv_FG σ).
  Defined.

  (* El elemento neutro es la identidad. *)
  Let sym_e : Permutación.
    apply mkPerm with (F := Id) (G := Id).
    split; apply functional_extensionality; compute; reflexivity.
  Defined.

  (* La inversa de una permutación. *)
  Let sym_inv (σ : Permutación) : Permutación.
    destruct σ as (F, G, inv_FG).
    apply mkPerm with (F := G) (G := F).
    split.
    apply inv_FG.
    apply inv_FG.
  Defined.

  (* sym_op es asociativa *)
  Lemma sym_G1 : forall σ τ ρ, sym_op (sym_op σ τ) ρ = sym_op σ (sym_op τ ρ).
    intros σ τ ρ.
    apply perm_eq.
    reflexivity.
    reflexivity.
  Qed.
  
  (* sym_e neutro a izquierda *)
  Lemma sym_G2 : forall σ, sym_op sym_e σ = σ.
    intros.
    apply perm_eq.
    reflexivity.
    reflexivity.
  Qed.
  
  (* sym_e neutro a derecha *)
  Lemma sym_G3 : forall σ, sym_op σ sym_e = σ.
    intros.
    apply perm_eq.
    reflexivity.
    reflexivity.
  Qed.

  (* sym_inv inversa a derecha *)
  Lemma sym_G4 : forall σ, sym_op σ (sym_inv σ) = sym_e.
    intros σ.
    destruct σ as (F, G, inv_FG).
    apply perm_eq.
    simpl.
    apply inv_FG.
    apply inv_FG.
  Qed.
  
  (* El grupo simétrico *)
  Definition Sym : Grupo :=
    mkGrupo
       Permutación  (* carrier *)
       sym_e        (* elemento neutro *)
       sym_op       (* operación binaria *)
       sym_inv      (* inverso *)
       (mkEstructuraDeGrupo _ _ _ _
         (mkEstructuraDeMonoide _ _ _ sym_G1 sym_G2 sym_G3)
         sym_G4).

End Grupo_Simétrico.

Notation "φ $ x" := (π1 φ x) (at level 20).

Section Morfismos.

    Variable G H : Grupo.

    Definition es_morfismo (f : carrier G -> carrier H) : Prop :=
        (forall x y,  f (x · y) = f x · f y).

    Definition Morfismo :=
      { f : carrier G -> carrier H | es_morfismo f }.

    Lemma morfismo_en_prod : forall φ : Morfismo, forall x y, φ $ (x · y) = (φ $ x) · (φ $ y).
      intros.
      apply (π2 φ).
    Qed.

    Lemma morfismo_en_1 : forall φ : Morfismo, φ $ 1 = 1.
      intro φ.
      assert ((φ $ 1) · (φ $ 1) = φ $ 1).
      rewrite <- morfismo_en_prod.
      rewrite neut_l.
      reflexivity.
      apply cancel_r with (φ $ 1).
      rewrite neut_l.
      assumption.
    Qed.
    
    Lemma morfismo_en_inv : forall (φ : Morfismo) x, φ $ x⁻¹ = (φ $ x)⁻¹.
    Proof.
      intros φ x.
      apply cancel_r with (φ $ x).
      rewrite inv_l.
      rewrite <- morfismo_en_prod.
      rewrite inv_l.
      apply morfismo_en_1.
    Qed.
    
    Definition es_monomorfismo (f : carrier G -> carrier H) : Prop :=
      es_morfismo f /\
      forall x y,  f x = f y  ->  x = y.

    Lemma morfismo_eq : forall φ ψ : Morfismo, π1 φ = π1 ψ -> φ = ψ.
    Proof.
      intros φ ψ eq_π1.
      destruct φ as (f, f_mor).
      destruct ψ as (g, g_mor).
      assert (f = g) as eq_fg. assumption.
      destruct eq_fg.
      replace g_mor with f_mor.
      reflexivity.
      apply proof_irrelevance.
    Qed.

    Lemma morf_equal : forall φ ψ : Morfismo, forall x, φ = ψ -> φ $ x = ψ $ x.
      intros φ ψ x eq.
      destruct eq.
      reflexivity.
    Qed.

    Definition G_sub := { f : carrier G -> carrier H | es_monomorfismo f }.
 
End Morfismos.

(* ↪ == \hookrightarrow *)
Notation "G ↪ H" := (G_sub G H) (at level 20).

Definition Endomorfismo (G : Grupo) := Morfismo G G.

Section Teorema_de_Cayley.

  Variable G : Grupo.
  
  Let X := carrier G.

  (* Dado un x, denota la permutación que multiplica a izquierda por x. *)
  Definition μ (x : X) : Permutación X.
    apply mkPerm with (F := fun y => x·y) (G := fun y => x⁻¹·y).
    split.
      (* F ∘ G = Id *)
      apply functional_extensionality; intros y.
      rewrite <- assoc.
      rewrite inv_r.
      rewrite neut_l.
      reflexivity.
      (* G ∘ F = Id *)
      apply functional_extensionality; intros y.
      rewrite <- assoc.
      rewrite inv_l.
      rewrite neut_l.
      reflexivity.
  Defined.
  
  (* μ es homomórfico para el producto *)
  Lemma μ_hom_op : forall x y : X,  μ (x · y) = (μ x : carrier (Sym X)) · μ y.
    intros x y.
    apply perm_eq.
    (* multiplicar por (x · y) *)
    apply functional_extensionality.
    intro z.
    simpl.
    apply assoc.

    (* multiplicar por (x · y)⁻¹ *)
    apply functional_extensionality.
    intro z.
    simpl.
    rewrite inv_xy.
    apply assoc.
  Qed.

End Teorema_de_Cayley.

Theorem Cayley : forall G : Grupo, { X : Set & G ↪ Sym X }.
Proof.
  intro G.
  exists (carrier G).
  exists (μ G).
  split.

  (* morfismo *)
  unfold es_morfismo.
  intros x y.
  apply μ_hom_op.  (* homomórfico para el producto *)

  (* monomorfismo *)
  intros x y permx_eq_permy.
  replace x with (F _ (μ G x) 1).
  replace y with (F _ (μ G y) 1).
  rewrite permx_eq_permy.
  reflexivity.
  simpl. apply neut_r.
  simpl. apply neut_r.
Qed.

Definition es_abeliano (G : Grupo) := forall x y : carrier G, x · y = y · x.

Definition GrupoAbeliano := { G | es_abeliano G }.

Structure Anillo := mkAnillo {
  RC    : Set ;                           (* carrier *)

  R0    : RC ;                            (* 0 *)
  Radd  : RC -> RC -> RC ;                (* + *)
  Ropp  : RC -> RC ;                      (* - *)

  R1    : RC ;                            (* elemento neutro *)
  Rmul  : RC -> RC -> RC ;                (* operación binaria *)

  R_es_grupo_add    : EstructuraDeGrupo RC R0 Radd Ropp ;
  R_comm            : forall x y : RC, Radd x y = Radd y x ;

  R_es_monoide_mul  : EstructuraDeMonoide RC R1 Rmul ;

  R_distr_l : forall x y z : RC, Rmul x (Radd y z) = Radd (Rmul x y) (Rmul x z) ;
  R_distr_r : forall x y z : RC, Rmul (Radd y z) x = Radd (Rmul y x) (Rmul z x)
}.

Definition R_carrier (A : Anillo) : Set := RC A.

Definition tiene_estructura_de_anillo (X : Set) := exists A : Anillo, R_carrier A = X.

Notation "x + y" := (Radd _ x y).
Notation "x · y" := (Rmul _ x y) (at level 20).
Notation "0" := (R0 _).
Notation "1" := (R1 _).

Section Anillo_Propiedades_Basicas.

  Variable A : Anillo.

  Lemma R_mul_neut_l : forall x : R_carrier A,  1 · x = x.
    intros.
    apply (EM_neut_l _ _ _ (R_es_monoide_mul A)).
  Qed.

  Lemma R_mul_neut_r : forall x : R_carrier A,  x · 1 = x.
    intros.
    apply (EM_neut_r _ _ _ (R_es_monoide_mul A)).
  Qed.

  Lemma R_mul_assoc : forall x y z : R_carrier A,  (x · y) · z = x · (y · z).
    intros.
    apply (EM_assoc _ _ _ (R_es_monoide_mul A)).
  Qed.
                            
End Anillo_Propiedades_Basicas.

Section Anillo_Endomorfismos_Grupo_Abeliano.

  Variable G : Grupo.

  Hypothesis G_abeliano : es_abeliano G.
  
  Notation "0"     := (e G).
  Notation "x + y" := (op G x y).
  Notation "- x"   := (inv G x).
  
  (* Endomorfismo que manda todo al 1 del grupo *)
  Definition end_0 : Endomorfismo G.
    exists (fun x => 0).
    unfold es_morfismo.
    rewrite neut_r.
    reflexivity.
  Defined.

  (* Operación entre endomorfismos que calcula la suma punto a punto *)
  Definition end_add : Endomorfismo G -> Endomorfismo G -> Endomorfismo G.
    intros φ ψ.
    exists (fun x => (φ $ x) + (ψ $ x)).
    unfold es_morfismo.
    intros x y.
    rewrite ? morfismo_en_prod.
    apply cancel_l with (-φ $ x).
    rewrite <-? assoc, ? inv_l, ? neut_l.
    apply cancel_r with (-ψ $ y).
    rewrite ->? assoc, ? inv_r, ? neut_r.
    apply G_abeliano.
  Defined.
      
  (* Operación que dado un endomorfismo devuelve su opuesto aditivo punto a punto  *)
  Definition end_neg : Endomorfismo G -> Endomorfismo G.
    intro φ.
    exists (fun x => -φ $ x).
    unfold es_morfismo.
    intros.
    rewrite ? morfismo_en_prod.
    rewrite G_abeliano.
    apply inv_xy.
  Defined.
  
  Lemma end_add_assoc : forall α β γ : Endomorfismo G, end_add (end_add α β) γ = end_add α (end_add β γ).
    intros. apply morfismo_eq. apply functional_extensionality.
    intro. apply assoc.
  Qed.

  Lemma end_0_neut_l : forall φ : Endomorfismo G, end_add end_0 φ = φ.
    intro. apply morfismo_eq. apply functional_extensionality.
    intro. apply neut_l.
  Qed.

  Lemma end_0_neut_r : forall φ : Endomorfismo G, end_add φ end_0 = φ.
    intro. apply morfismo_eq. apply functional_extensionality.
    intro. apply neut_r.
  Qed.

  Lemma end_neg_inv_r : forall φ : Endomorfismo G, end_add φ (end_neg φ) = end_0.
    intro. apply morfismo_eq. apply functional_extensionality.
    intro. apply inv_r.
  Qed.

  Lemma end_add_comm : forall φ ψ : Endomorfismo G, end_add φ ψ = end_add ψ φ.
    intros. apply morfismo_eq. apply functional_extensionality.
    intro. apply G_abeliano.
  Qed.

  (* Endomorfismo identidad *)
  Definition end_1 : Endomorfismo G.
    exists (fun x => x).
    unfold es_morfismo.
    reflexivity.
  Defined.

  (* Producto de endomorfismos: la composición *)
  Definition end_mul : Endomorfismo G -> Endomorfismo G -> Endomorfismo G.
    intros φ ψ.
    exists (fun x => φ $ (ψ $ x)).
    unfold es_morfismo.
    intros x y.
    rewrite ? morfismo_en_prod.
    reflexivity.
  Defined.
      
  Lemma end_mul_assoc : forall α β γ, end_mul (end_mul α β) γ = end_mul α (end_mul β γ).
    intros. apply morfismo_eq. apply functional_extensionality.
    intro. reflexivity.
  Qed.

  Lemma end_1_neut_l : forall φ, end_mul end_1 φ = φ.
    intro. apply morfismo_eq. apply functional_extensionality.
    intro. reflexivity.
  Qed.

  Lemma end_1_neut_r : forall φ, end_mul φ end_1 = φ.
    intro. apply morfismo_eq. apply functional_extensionality.
    intro. reflexivity.
  Qed.
  
  Lemma end_distr_l : forall α β γ, end_mul α (end_add β γ) = end_add (end_mul α β) (end_mul α γ).
    intros. apply morfismo_eq. apply functional_extensionality.
    intro.
    simpl.
    rewrite morfismo_en_prod. 
    reflexivity.
  Qed.

  Lemma end_distr_r : forall α β γ, end_mul (end_add β γ) α = end_add (end_mul β α) (end_mul γ α).
    intros. apply morfismo_eq. apply functional_extensionality.
    intro.
    reflexivity.
  Qed.
  
  Definition AnilloEndomorfismos :=
    mkAnillo (Endomorfismo G)
             end_0 end_add end_neg
             end_1 end_mul
             (mkEstructuraDeGrupo _ _ _ _
                   (mkEstructuraDeMonoide _ _ _
                     end_add_assoc end_0_neut_l end_0_neut_r)
                   end_neg_inv_r)
             end_add_comm
             (mkEstructuraDeMonoide _ _ _
                end_mul_assoc end_1_neut_l end_1_neut_r)
             end_distr_l
             end_distr_r.

  Lemma G_abeliano_implica_End_anillo :
          tiene_estructura_de_anillo (Endomorfismo G).
  Proof.
    exists AnilloEndomorfismos.
    reflexivity.
  Qed.
  
End Anillo_Endomorfismos_Grupo_Abeliano.

Section Morfismo_Anillos.
  
  Variable A B : Anillo.

  Definition es_R_morfismo (f : R_carrier A -> R_carrier B) : Prop :=
       f 1 = 1
    /\ (forall x y,  f (x + y) = f x + f y)
    /\ (forall x y,  f (x · y) = f x · f y).

  Definition es_R_monomorfismo (f : R_carrier A -> R_carrier B) : Prop :=
       es_R_morfismo f
    /\ forall x y, f x = f y -> x = y.

  Definition R_Morfismo :=
    { f : R_carrier A -> R_carrier B | es_R_morfismo f }.

  Lemma R_morfismo_eq :
    forall φ ψ : R_Morfismo, π1 φ = π1 ψ -> φ = ψ.
  Proof.
    intros φ ψ eq.
    destruct φ as (f, f_mor).
    destruct ψ as (g, g_mor).
    assert (f = g) as f_eq_g.
    assumption.
    destruct f_eq_g.
    replace f_mor with g_mor.
    reflexivity.
    apply proof_irrelevance.
  Qed.

  Definition R_sub :=
    { f : R_carrier A -> R_carrier B | es_R_monomorfismo f }.

End Morfismo_Anillos.

Definition R_grupo_aditivo (A : Anillo) : Grupo :=
  mkGrupo (R_carrier A) (R0 A) (Radd A) (Ropp A) (R_es_grupo_add A).

Definition R_grupo_ab_aditivo (A : Anillo) : GrupoAbeliano.
  exists (R_grupo_aditivo A).
  unfold es_abeliano.
  intros.
  apply (R_comm A).
Defined.

(** ↪ == \hookrightarrow **)
Notation "A ↪ B" := (R_sub A B) (at level 20).

Section Pseudo_Cayley_Anillos.

  Variable A : Anillo.
  
  Let G : GrupoAbeliano := R_grupo_ab_aditivo A.
  Let Endo := AnilloEndomorfismos (π1 G) (π2 G).
  
  Definition Rμ (x : R_carrier A) : R_carrier Endo.
    exists (fun y => Rmul _ x y).
    intros y z.
    apply (R_distr_l A).
  Defined.

End Pseudo_Cayley_Anillos.

Theorem RCayley :
  forall A : Anillo,
    { G : GrupoAbeliano   &
      A ↪ AnilloEndomorfismos (π1 G) (π2 G)
    }.
Proof.
  intro A.
  exists (R_grupo_ab_aditivo A).
  exists (Rμ A).
  split.
    (* morfismo de anillos *)
    split.
      (* 1 *)
      apply morfismo_eq.
      apply functional_extensionality.
      intro.
      simpl.
      apply R_mul_neut_l.
    split.
      (* suma *)
      intros x y.
      apply morfismo_eq.
      apply functional_extensionality.
      intro z.
      simpl.
      apply R_distr_r.
      (* producto *)
      intros x y.
      apply morfismo_eq.
      apply functional_extensionality.
      intro z.
      simpl.
      apply R_mul_assoc.

    (* monomorfismo *)
    intros x y Hmul.
    assert (Rμ A x $ 1 = Rμ A y $ 1) as Hmul'.
      apply morf_equal. assumption.
    simpl in Hmul'.
    rewrite ? R_mul_neut_r in Hmul'.
    assumption.
Qed.

