(* vim:et:ts=2:
 *)
open Printf ;;
open List ;;

type id = string ;;

type kind = StarK
          | ForallK of id * typ * kind
 and typ = VarT of id
         | ForallT of id * typ * typ
         | AppExpT of typ * exp
 and exp = VarE of id
         | ConstE of int
         | LamE of id * typ * exp
         | AppE of exp * exp
         ;;

(* Free variables *)

let remove (xs : id list) (x : id) = filter (fun y -> y <> x) xs ;;

let
  rec free_vars_kind (k : kind) : id list =
    match k with
    | StarK             -> []
    | ForallK (x, t, k) -> free_vars_typ t @ remove (free_vars_kind k) x
  and free_vars_typ (t : typ) : id list =
    match t with
    | VarT b              -> []
    | ForallT (x, t1, t2) -> free_vars_typ t1 @ remove (free_vars_typ t2) x
    | AppExpT (t1, t2)    -> free_vars_typ t1 @ free_vars_exp t2
  and free_vars_exp (e : exp) : id list = 
    match e with
    | VarE x           -> [x]
    | ConstE n         -> []
    | LamE (x, t, e')  -> free_vars_typ t @ remove (free_vars_exp e') x
    | AppE (e1, e2)    -> free_vars_exp e1 @ free_vars_exp e2
  ;;

let show_id_list (xs : id list) : string =
  "[" ^ fold_right (fun a res -> a ^ ", " ^ res) xs "" ^ "]"
  ;;

(* Pretty printing *)

let parenthesize (str, level) : string =
  if level >= 1 then "(" ^ str ^ ")" else str ;;

let
  rec show_kind_level (k : kind) : string * int =
    match k with
    | StarK  -> "*", 0
    | ForallK (x, t, k) ->
        let s1 = parenthesize (show_typ_level t) in
        let s2 = parenthesize (show_kind_level k) in
          (if mem x (free_vars_typ t)
            then "forall " ^ x ^ " : " ^ s1 ^ "," ^ s2
            else s1 ^ " -> " ^ s2), 1
  and show_typ_level (t : typ)  : string * int =
    match t with
    | VarT b -> b, 0
    | ForallT (x, t1, t2) ->
        let s1 = parenthesize (show_typ_level t1) in
        let s2 = parenthesize (show_typ_level t2) in
          (if mem x (free_vars_typ t1)
            then "forall " ^ x ^ " : " ^ s1 ^ "," ^ s2
            else s1 ^ " -> " ^ s2), 1
    | AppExpT (t', e) ->
       let s1 = parenthesize (show_typ_level t') in
       let s2 = parenthesize (show_exp_level e) in
         s1 ^ " " ^ s2, 2
  and show_exp_level (e : exp)  : string * int =
    match e with
    | VarE x   -> x, 0
    | ConstE n -> string_of_int n, 0
    | LamE (x, t, e') ->
        let s1 = parenthesize (show_typ_level t) in
        let s2 = parenthesize (show_exp_level e') in
          "\\" ^ x ^ ":" ^ s1 ^ "." ^ s2, 1
    | AppE (e1, e2) ->
       let s1 = parenthesize (show_exp_level e1) in
       let s2 = parenthesize (show_exp_level e2) in
         s1 ^ " " ^ s2, 2
    ;;

let show_kind k = fst (show_kind_level k) ;;
let show_typ t = fst (show_typ_level t) ;;
let show_exp e = fst (show_exp_level e) ;;

(* Environments *)

type 'a environment = (id * 'a) list ;;

let rec lookup_env (env : 'a environment) (x : id) : 'a option =
  match env with
  | []          -> None
  | ((y, a) :: env') ->
    if x = y
     then Some a
     else lookup_env env' x
  ;;

let extend_env (env : 'a environment) (x : id) (a : 'a) : 'a environment = (x, a) :: env ;;

(* Fresh vars *)

let gensym = 
  let c = ref 1 in
    fun () ->
      c := !c + 1;
      !c ;;

let var_prefix x = String.sub x 0 (String.index (x ^ "_") '_') ;;
let fresh_var x = var_prefix x ^ "_" ^ string_of_int (gensym ()) ;;

(* Substitution *)

let
  rec substitute_kind (k0 : kind) (env : exp environment) : kind =
    match k0  with
    | StarK             -> StarK
    | ForallK (x, t, k) ->
        ForallK (x,
                 substitute_type t env, 
                 substitute_kind k env)
  and substitute_type (t0 : typ) (env : exp environment) : typ =
    match t0 with
    | VarT x              -> VarT x
    | ForallT (x, t1, t2) ->
        ForallT (x,
                 substitute_type t1 env,
                 substitute_type t2 env)
    | AppExpT (t, e) ->
        AppExpT (substitute_type t env, substitute_expr e env)
  and substitute_expr (e0 : exp) (env : exp environment) : exp =
    match e0 with
    | VarE x ->
      (match lookup_env env x with
      | None   -> VarE x
      | Some e -> e
      )
    | ConstE n -> ConstE n
    | LamE (x, t, e) ->
        let y = fresh_var x in
          LamE (y,
                substitute_type t env, 
                substitute_expr e (extend_env env x (VarE y)))
    | AppE (e1, e2) ->
        AppE (substitute_expr e1 env,
              substitute_expr e2 env)
  ;;

(* Evaluation *)

let
  rec evstep (env : exp environment) (e0 : exp) : exp option =
    match e0 with
    | VarE x   -> lookup_env env x
    | ConstE n -> None
    | LamE (x, t, e) ->
      (match evstep env e with
      | Some e' -> Some (LamE (x, t, e'))
      | None    -> None
      )
    | AppE (e1, e2) ->
      (match e1 with
      | LamE (x, t, e) ->
        Some (substitute_expr e (extend_env [] x e2))
      | _ ->
        (match evstep env e1 with
        | Some e1' -> Some (AppE (e1', e2))
        | None     ->
          (match evstep env e2 with
          | Some e2' -> Some (AppE (e1, e2'))
          | None     -> None
          )
        )
      )
    ;;

let rec normalize_expr (env : exp environment) (e0 : exp) : exp =
  match evstep env e0 with
  | None    -> e0
  | Some e1 -> normalize_expr env e1
  ;;

let rec normalize_type (env : exp environment) (t0 : typ) : typ =
  match t0 with
  | VarT x              -> VarT x
  | ForallT (x, t1, t2) ->
      let t2' = normalize_type env t2 in
        ForallT (x, t1, t2')
  | AppExpT (t, e) ->
      let t' = normalize_type env t in
      let e' = normalize_expr env e in
        (match t' with
        | ForallT (x, t1, t2) ->
            normalize_type (extend_env env x e') t2
        | _ -> AppExpT (t', e')
        )
  ;;

(* Contexts *)

type context = EmptyC
             | VarKindC of context * id * kind
             | VarTypeC of context * id * typ
             ;;

let rec var_lookup_kind (ctx : context) (x : id) : kind option =
  match ctx with
  | EmptyC                -> None
  | VarKindC (ctx', y, k) -> if x = y
                               then Some k
                               else var_lookup_kind ctx' x
  | VarTypeC (ctx', y, t) -> var_lookup_kind ctx' x
  ;;

let rec var_lookup_type (ctx : context) (x : id) : typ option =
  match ctx with
  | EmptyC                -> None
  | VarKindC (ctx', y, k) -> var_lookup_type ctx' x
  | VarTypeC (ctx', y, t) -> if x = y
                               then Some t
                               else var_lookup_type ctx' x
  ;;

let var_get_kind (ctx : context) (x : id) : kind =
  match var_lookup_kind ctx x with
  | None   -> raise (Failure ("variable \"" ^ x ^ "\" not in context"))
  | Some k -> k
  ;;

let var_get_type (ctx : context) (x : id) : typ =
  match var_lookup_type ctx x with
  | None   -> raise (Failure ("variable \"" ^ x ^ "\" not in context"))
  | Some t -> t
  ;;

(* Checking *)

let equal_types (env : exp environment) (t1 : typ) (t2 : typ) : bool =
  let rec check_equal_types (t1 : typ) (t2 : typ) : bool =
    (match t1 with
    | VarT x -> (match t2 with
                | VarT y -> x = y
                | _      -> false
                )
    | ForallT (x, t1a, t1b) ->
                (match t2 with
                | ForallT (y, t2a, t2b) ->
                    check_equal_types t1a t2a &&
                    let z = fresh_var x in
                      check_equal_types
                        (substitute_type t1b (extend_env env x (VarE z)))
                        (substitute_type t2b (extend_env env y (VarE z)))
                | _ -> false
                )
    | _ -> false
    )
  in
  let t1 = normalize_type [] t1 in
  let t2 = normalize_type [] t2 in
    check_equal_types t1 t2 
  ;;

let
  rec check_kind (ctx : context) (k0 : kind) : bool =
    match k0 with
    | StarK             -> check_context ctx
    | ForallK (x, t, k) -> check_type ctx t &&
                               check_kind (VarTypeC (ctx, x, t)) k
  and check_context (ctx : context) : bool =
    match ctx with
    | EmptyC               -> true
    | VarKindC (ctx, x, k) -> check_context ctx && check_kind ctx k
    | VarTypeC (ctx, x, t) -> check_context ctx && check_type ctx t
  and assert_context_ok (ctx : context) : unit =
    let _ = check_context ctx in ()
  and check_type (ctx : context) (t0 : typ) : bool =
    let _ = infer_kind ctx t0 in true
  and assert_type_ok (ctx : context) (t0 : typ) : unit =
    let _ = check_type ctx t0 in ()
  and infer_kind (ctx : context) (t0 : typ) : kind =
    match t0 with
    | VarT x ->
      assert_context_ok ctx; (* <-- should not be necessary when checking
                              *     a program; the context is correct
                              *     by construction *)
      var_get_kind ctx x
    | ForallT (x, t1, t2) ->
      assert_type_ok ctx t1 ;
      infer_kind (VarTypeC (ctx, x, t1)) t2
    | AppExpT (t, e)      ->
      (match infer_kind ctx t with
      | StarK -> raise (Failure
                         ("type (" ^ show_typ t ^ ")" ^
                          " applied to expression (" ^ show_exp e ^ ")" ^
                          " should have a 'forall' kind"))
      | ForallK (x, t1, k) ->
          assert_expr_has_type ctx e t1;
          substitute_kind k (extend_env [] x e)
      )
  and infer_expr_type (ctx : context) (e0 : exp) : typ =
    (match e0 with
    | VarE x -> var_get_type ctx x
    | ConstE n ->
        VarT "int" (* Test. Warning: int should be in the context *)
    | LamE (x, t, e) ->
        assert_type_ok ctx t;
        ForallT (x, t, infer_expr_type (VarTypeC (ctx, x, t)) e)
    | AppE (e1, e2) ->
        let t1 = infer_expr_type ctx e1 in
        let t2 = AppExpT (t1, e2) in
          assert_type_ok ctx t2;
          t2
    )
  and assert_expr_has_type (ctx : context) (e0 : exp) (t0 : typ) : unit =
    let t1 = infer_expr_type ctx e0 in
      (*** TODO: reemplazar [] por un parametro (env : exp environment) ***)
      if equal_types [] t0 t1
        then ()
        else raise (Failure
                     ("types do not match; expected: " ^ show_typ t0 ^ " got: " ^ show_typ t1))
    ;;

(***
let t2 = infer_expr_type ctx e2 in
  assert_type_ok ctx (AppExpT (t1, e2));
  (match t1 with
  | ForallT (x, s1, s2) ->
      if equal_types s1 t2
        then substitute_type s2 (extend_env [] x e2)
        else raise (Failure
              ("types do not match: " ^ show_typ s1 ^ " VS. " ^ show_typ t2))
  | t' -> AppExpT (t', e2)
  )
***)
(**if equal_types (infer_type ctx e) t1**)
(*raise (Failure
  ("argument (" ^ show_exp e ^ ")" ^
    " to type (" ^ show_typ t ^ ")" ^
    " should be of type " ^ show_typ t1))*)

(* Main *)

let expr = AppE (LamE ("x", VarT "int", (LamE ("y", VarT "int", VarE "x"))), ConstE 9)

(*
let main =
  print_string (
  match eval_expr [] expr with
  | None              -> "NADA\n"
  | Some (typ, value) -> show_value value ^ " : " ^ show_typ typ ^ "\n"
  )
  ;;
*)

let main = try
  (*
  print_string (if check_type (VarKindC (EmptyC, "t", ForallK ("x", VarT "bool", StarK))) (AppExpT (VarT "t", VarE "x"))
                 then "si"
                 else "no")
  *)
  let ctx = VarKindC (VarTypeC (VarKindC (EmptyC, "nat", StarK), "7", VarT "nat"), "vector", ForallK ("x", VarT "nat", StarK)) in
  let typ = AppExpT (VarT "vector", VarE "7") in
    print_string (show_typ typ ^ "\n");
    print_string (show_kind (infer_kind ctx typ) ^ "\n")
with
  Failure msg -> print_endline ("fallo: " ^ msg ^ "\n")
;;

