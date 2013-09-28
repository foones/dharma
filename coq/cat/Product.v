Load Category.

Section Product.

  Variable c : Category.
  Variable A B : Ob c.

  Structure ProductOb : Type := mkProductOb {
      Product_P   : Ob c ;
      Product_pi1 : Product_P ~~> A ;
      Product_pi2 : Product_P ~~> B
    }.

  Structure ProductHom (X Y : ProductOb) : Type :=
    mkProductHom {
      Product_inj   : Product_P X ~~> Product_P Y ;
      Product_comm1 : Product_pi1 Y ** Product_inj = Product_pi1 X ;
      Product_comm2 : Product_pi2 Y ** Product_inj = Product_pi2 X
    }.

  Let P := Product_P.
  Let pi1 := Product_pi1.
  Let pi2 := Product_pi2.

  Definition ProductId (X : ProductOb) : ProductHom X X :=
    mkProductHom X X
      (Id c (P X))
      (Comp_id c (P X) A (pi1 X))
      (Comp_id c (P X) B (pi2 X)).

  Definition ProductComp (X Y Z : ProductOb)
                         (f : ProductHom Y Z)
                         (g : ProductHom X Y) : ProductHom X Z.
    intros.
    apply (mkProductHom X Z (Product_inj Y Z f ** Product_inj X Y g)).
    rewrite (Comp_assoc c).
    rewrite (Product_comm1 Y Z f).
    rewrite (Product_comm1 X Y g).
    reflexivity.
    rewrite (Comp_assoc c).
    rewrite (Product_comm2 Y Z f).
    rewrite (Product_comm2 X Y g).
    reflexivity.
  Defined.

  Definition ProductDataCategoryDefinition : CategoryDefinition :=
    mkCategoryDefinition ProductOb ProductHom ProductId ProductComp.

  Let D := ProductDataCategoryDefinition.

  Lemma ProductCompId : comp_id D. 
    unfold comp_id.
    intros X Y f.
    destruct f as (f_inj, f_comm1, f_comm2)_eqn:f_destruct_eqn.

    case_eq f.
    intros f_inj f_comm1 f_comm2 f_destruct_eqn.
    simpl; unfold ProductComp.

    simpl.
    unfold ProductComp.
    case_eq
    Check f_equal3.
      
    rewrite <- (f_equal3 _ _ _ _ mkProductHom f_inj f_comm1 f_comm2).
    rewrite <- f_equal3.
    unfold ProductComp.
    
    assert (f_inj = Product_inj X Y f ** Product_inj X X (ProductId X)).
      rewrite (Comp_id c).
      rewrite f_destruct_eqn.
      unfold Product_inj.
      reflexivity.
    generalize f_inj.
    Set Printing All.
    Check mkProductHom.
    rewrite H.

    

    
    Check f_equal3.
    apply f_equal3.

    replace (Product_inj X Y f ** Product_inj X X (ProductId X))
       with (Product_inj X Y f).
    admit.
    rewrite (Comp_id c).
    reflexivity.

    SearchAbout ProductHom.
    inversion f.
    split.
    constructor.
    case_eq.
    auto.
    apply (f_equal _ _ _ mkProductHom).
    congruence.
    SearchAbout congruence.
    SearchAbout ProductHom.
    apply Product_inj.

    replace (Product_inj X Y f ** Product_inj X X (ProductId X))
       with (Product_inj X Y f).
    admit.
    rewrite (Comp_id c).
    reflexivity.


  Definition ProductDataCategory : Category :=
    mkCategory ProductDataCategoryDefinition.

  Definition product (ProductData A B) :=
    forall (X : ProductData A B),

(*********************************************************************************)


  (*
  Let ProductHom_eq_congr :
    forall X Y injA comm1A comm2A injB comm1B comm2B,
      injA = injB ->
      comm1A = comm1B ->
      comm2A = comm2B ->
      mkProductHom X Y injA comm1A comm2A =
      mkProductHom X Y injB comm1B comm2B.
  Proof.
    apply ProductHom_rec.
  *)

  Let fap : forall (A B : Type) (f g : A -> B) (x y : A),
              f = g -> x = y -> f x = g y.
  Proof.
    intros.
    replace g with f.
    replace y with x.
    reflexivity.
  Qed.