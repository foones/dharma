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
  and free_vars_exp (a : exp) : id list = 
    match a with
    | VarE x           -> [x]
    | ConstE n         -> []
    | LamE (x, t, a')  -> free_vars_typ t @ remove (free_vars_exp a') x
    | AppE (a1, a2)    -> free_vars_exp a1 @ free_vars_exp a2
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
  and show_exp_level (a : exp)  : string * int =
	match a with
	| VarE x   -> x, 0
	| ConstE n -> string_of_int n, 0
	| LamE (x, t, a') ->
		let s1 = parenthesize (show_typ_level t) in
		let s2 = parenthesize (show_exp_level a') in
		"\\" ^ x ^ ":" ^ s1 ^ "." ^ s2, 1
	| AppE (a1, a2) ->
	   let s1 = parenthesize (show_exp_level a1) in
	   let s2 = parenthesize (show_exp_level a2) in
		 s1 ^ " " ^ s2, 2
	;;

let show_kind a = fst (show_kind_level a) ;;
let show_typ a = fst (show_typ_level a) ;;
let show_exp a = fst (show_exp_level a) ;;

(* Evaluation *)

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

type value = ConstV of int
           | ClosureV of (id * typ * exp * (typ * value) environment)
 and typed_value = typ * value ;;

let
  rec show_value (v : value) : string =
    match v with
    | ConstV n             -> string_of_int n
    | ClosureV (x, t, a, env) ->
      "Closure[ "
      ^ show_exp (LamE (x, t, a)) ^ " @ "
      ^ show_typed_value_environment env
      ^ " ]"
  and show_typed_value_environment (env : typed_value environment) =
    match env with
    | []                -> ""
    | (x, (t, v))::env' -> x ^ ":" ^ show_typ t ^ "=" ^ show_value v ^ ", "
  ;;

let rec evaluate (env : typed_value environment) (a : exp) : typed_value option =
  match a with
  | VarE x         -> lookup_env env x
  | ConstE n       -> Some (VarT "int", ConstV n)
  | LamE (x, t, a) -> Some (VarT "XXX_closure", ClosureV (x, t, a, env))
  | AppE (a1, a2)  ->
    let r1 = evaluate env a1 in
      match r1 with
      | None       -> None
      | Some (type1, value1) ->
      let r2 = evaluate env a2 in
        match r2 with
        | None       -> None
        | Some (type2, value2) ->
          match value1 with
          | ClosureV (x, t, body, env') ->
            evaluate (extend_env env' x (type2, value2)) body
          | _ -> None
  ;;

(* Checking *)

let gensym = 
  let c = ref 1 in
    fun () ->
      c := !c + 1;
      !c ;;

type context = EmptyC
             | VarKindC of context * id * kind
             | VarTypeC of context * id * typ
             ;;

let rec var_has_kind (ctx : context) (x : id) : bool =
  match ctx with
  | EmptyC                -> raise (Failure ("variable " ^ x ^ " not in context"))
  | VarKindC (ctx', y, k) -> if x = y
                              then true
                              else var_has_kind ctx' x
  | VarTypeC (ctx', y, t) -> var_has_kind ctx' x
  ;;

let equal_types (t1 : typ) (t2 : typ) : bool =
  true (** TODO **)
  ;;

let
  rec check_kind (ctx : context) (k0 : kind) : bool =
      match k0 with
      | StarK             -> check_context ctx
      | ForallK (x, t, k) -> check_type ctx t &&
                             check_kind (VarTypeC (ctx, x, t)) k
  and check_context (ctx : context) : bool =
      true
  and check_type (ctx : context) (t0 : typ) : bool =
      match t0 with
      | VarT x              -> check_context ctx &&
                               var_has_kind ctx x
      | ForallT (x, t1, t2) -> check_type ctx t1 &&
                               check_type (VarTypeC (ctx, x, t1)) t2
      | AppExpT (t, e)      -> (match infer_kind ctx t with
                               | StarK -> raise (Failure
                                                  ("type (" ^ show_typ t ^ ")" ^
                                                   " applied to expression (" ^ show_exp e ^ ")" ^
                                                   " should have a 'forall' kind"
                                                  ))
                               | ForallK (x, t1, k) ->
                                   if equal_types (infer_type ctx e) t1
                                    then true (*** substitute k x e ***)
                                    else raise (Failure "argument should be of the expected type")
                               )
  and infer_kind (ctx : context) (t0 : typ) : kind = (*** maybe kind ***)
      StarK (** TODO **)
  and infer_type (ctx : context) (e0 : exp) : typ = (*** maybe typ ***)
      VarT "xxx" (** TODO **)
      ;;

(* Main *)

let expr = AppE (LamE ("x", VarT "int", (LamE ("y", VarT "int", VarE "x"))), ConstE 9)

(*
let main =
  print_string (
  match evaluate [] expr with
  | None              -> "NADA\n"
  | Some (typ, value) -> show_value value ^ " : " ^ show_typ typ ^ "\n"
  )
  ;;
*)

let main = try
  print_string (if check_type EmptyC (AppExpT (VarT "t", VarE "x"))
                 then "si"
                 else "no")
with
  Failure msg -> print_endline ("fallo: " ^ msg ^ "\n")
;;

