open List ;;

type id = string ;;

type term = VarT of id
          | AppT of id * term list
          ;;

type formula = PredF of id * term list
             | NotF of formula
             | AndF of formula * formula
             | OrF of formula * formula
             | ImpF of formula * formula
             | ForallF of id * formula
             | ExistsF of id * formula
             ;;

let rec nnf form =
  match form with 
  | PredF (p, ts)       -> PredF (p, ts)
  | AndF (a, b)         -> AndF (nnf a, nnf b)
  | OrF (a, b)          -> OrF (nnf a, nnf b)
  | ImpF (a, b)         -> OrF (nnf (NotF a), nnf b)
  | ForallF (x, a)      -> ForallF (x, nnf a)
  | ExistsF (x, a)      -> ExistsF (x, nnf a)
  | NotF PredF (p, ts)  -> NotF (PredF (p, ts))
  | NotF NotF a         -> nnf a
  | NotF AndF (a, b)    -> OrF (nnf (NotF a), nnf (NotF b))
  | NotF OrF (a, b)     -> AndF (nnf (NotF a), nnf (NotF b))
  | NotF ImpF (a, b)    -> AndF (nnf a, nnf (NotF b))
  | NotF ForallF (x, a) -> ExistsF (x, nnf (NotF a))
  | NotF ExistsF (x, a) -> ForallF (x, nnf (NotF a))
  ;;

let join_quantifier q f = q f ;;

let gensym, reset_counter =
  let counter = ref 0 in
    (fun () ->
      let res = !counter in
        counter := !counter + 1;
        res),
    (fun () -> counter := 0)
  ;;

let var_prefix x = String.sub x 0 (String.index (x ^ "_") '_') ;;
let fresh_var x = var_prefix x ^ "_" ^ string_of_int (gensym ()) ;;

let rec foldform
       (pred_case : (id -> term list -> formula) -> id -> term list -> 'a)
       (unary_case : (formula -> formula) -> 'a -> 'a)
       (binary_case : (formula -> formula -> formula) -> 'a -> 'a -> 'a)
       (quantifier_case : (id -> formula -> formula) -> id -> 'a -> 'a)
       (form : formula) : 'a =
  let recur = foldform pred_case unary_case binary_case quantifier_case in
  match form with
  | PredF (p, ts)  -> pred_case (fun p ts -> PredF (p, ts)) p ts
  | NotF a         -> unary_case (fun x -> NotF x) (recur a)
  | AndF (a, b)    -> binary_case (fun x y -> AndF (x, y)) (recur a) (recur b)
  | OrF (a, b)     -> binary_case (fun x y -> OrF (x, y)) (recur a) (recur b)
  | ImpF (a, b)    -> binary_case (fun x y -> ImpF (x, y)) (recur a) (recur b)
  | ForallF (x, a) -> quantifier_case (fun x y -> ForallF (x, y)) x (recur a)
  | ExistsF (x, a) -> quantifier_case (fun x y -> ExistsF (x, y)) x (recur a)
  ;;

let null xs =
  match xs with
  | []    -> true
  | y::ys -> false
  ;;

let rec lookup_env env x =
  match env with
  | []          -> None
  | (y,v)::env' -> if x = y
                    then Some v
                    else lookup_env env' x
  ;;

let rec replace_vars_term (env : (id * term) list) (t : term) : term =
  match t with
  | VarT x       -> (match lookup_env env x with
                    | None   -> VarT x
                    | Some v -> v
                    )
  | AppT (f, ts) -> AppT (f, map (replace_vars_term env) ts)
  ;;

let replace_vars form =
  reset_counter () ;
  let pred op p ts env = op p (map (replace_vars_term env) ts) in
  let unary op a env = op (a env) in
  let binary op a b env = op (a env) (b env) in
  let quantifier op x a env = 
    let y = fresh_var x in
      op y (a ((x, VarT y)::env))
  in
    foldform pred unary binary quantifier form
  ;;

let refresh_term_vars form = replace_vars form [] ;;

let prenex form =
  let pred op p ts = [], op p ts in
  let unary op (qs, f) = assert (null qs); qs, op f in
  let binary op (qa, fa) (qb, fb) = qa @ qb, op fa fb in
  let quantifier op x (qa, fa) = op x :: qa, fa in
  let qs, fs = foldform pred unary binary quantifier form in
    fold_right join_quantifier qs fs
  ;;

let rec show_term t =
    match t with
    | VarT x       -> x
    | AppT (f, ts) -> f ^ if null ts then "" else "(" ^ show_terms ts ^ ")"
  and show_terms ts =
    match ts with
    | []    -> ""
    | t::[] -> show_term t
    | t::ts -> show_term t ^ ", " ^ show_terms ts
    ;;

let rec show_formula form =
  match form with
  | PredF (p, ts)  -> p ^ if null ts then "" else "(" ^ show_terms ts ^ ")"
  | NotF a         -> "~" ^ show_formula a
  | AndF (a, b)    -> "(" ^ show_formula a ^ " /\\ " ^ show_formula b ^ ")"
  | OrF (a, b)     -> "(" ^ show_formula a ^ " \\/ " ^ show_formula b ^ ")"
  | ImpF (a, b)    -> "(" ^ show_formula a ^ " => " ^ show_formula b ^ ")"
  | ForallF (x, a) -> "forall " ^ x ^ "." ^ show_formula a
  | ExistsF (x, a) -> "exists " ^ x ^ "." ^ show_formula a
  ;;

let cartesian f xs ys = concat (map (fun x -> map (f x) ys) xs) ;;

let skolemize form = 
  let rec skolemize_with_deps form deps =
    match form with
    | ExistsF (x, a) ->
      let witness = let w = (if null deps then "C" else "F") in
                      AppT (fresh_var (w ^ var_prefix x), map (fun x -> VarT x) deps)
        in
        let a_witness = replace_vars a ((x, witness)::[]) in
          skolemize_with_deps a_witness deps
    | ForallF (x, a) -> skolemize_with_deps a (x::deps)
    | form           -> form
  in skolemize_with_deps form [] ;;

let rec conjunctive form =
  match form with
  | PredF (p, ts) -> PredF (p, ts)
  | NotF f -> NotF f
  | AndF (a, b) ->
      AndF (conjunctive a, conjunctive b)
  | OrF (a, b) ->
      let da = conjunctive a in
		(match da with
		| AndF (x, y) -> AndF (conjunctive (OrF (x, b)),
							   conjunctive (OrF (y, b)))
		| _           ->
		let db = conjunctive b in
		  match db with
		  | AndF (x, y) -> AndF (conjunctive (OrF (da, x)),
								 conjunctive (OrF (da, y)))
		  | _           -> OrF (da, db)
        )
  | _ -> raise (Failure "conjunctive should be applied to already nnf+prenex+skolemized formulas")
  ;;

let clause form : formula list list =
  let rec extract_or_clause form : formula list =
    match form with
    | OrF (a, b) -> extract_or_clause a @ extract_or_clause b
    | _          -> form :: []
  in let rec extract_and_clause form : formula list list =
    match form with
    | AndF (a, b) -> extract_and_clause a @ extract_and_clause b
    | _           -> extract_or_clause form :: []
  in
    extract_and_clause (conjunctive (skolemize (prenex (refresh_term_vars (nnf form)))))
  ;;

let rec show_clause clause =
  let rec show_forms forms =
    match forms with
    | []     -> "" 
    | f::[]  -> show_formula f
    | f::fs  -> show_formula f ^ ", " ^ show_forms fs
  in match clause with
  | []          -> "" 
  | fs::clause' -> show_forms fs ^ ";\n" ^ show_clause clause'
  ;;

(******************************************************************************)

let print_conversion form =
  print_string (show_formula form ^ "\n") ;
  print_string (show_formula (nnf form) ^ "\n") ;
  print_string (show_formula (prenex (refresh_term_vars (nnf form))) ^ "\n") ;
  print_string (show_formula (skolemize (prenex (refresh_term_vars (nnf form)))) ^ "\n") ;
  print_string (show_formula (conjunctive (skolemize (prenex (refresh_term_vars (nnf form))))) ^ "\n") ;
  print_string ("\n" ^ show_clause (clause form) ^ "\n")
  ;;

let all x a = ForallF (x, a) ;;
let ex x a = ExistsF (x, a) ;;
let andf a b = AndF (a, b) ;;
let orf a b = OrF (a, b) ;;
let impf a b = ImpF (a, b) ;;
let n a = NotF a ;;

let p = PredF ("p", []) ;;
let q = PredF ("q", []) ;;
let r = PredF ("r", []) ;;
let s = PredF ("s", []) ;;
let px = PredF ("p", (VarT "x")::[]) ;;
let py = PredF ("p", (VarT "y")::[]) ;;
let qx = PredF ("q", (VarT "x")::[]) ;;
let qy = PredF ("q", (VarT "y")::[]) ;;
let rx = PredF ("r", (VarT "x")::[]) ;;
let ry = PredF ("r", (VarT "y")::[]) ;;
let pxy = PredF ("p", (VarT "x")::(VarT "y")::[]) ;;
let pxx = PredF ("p", (VarT "x")::(VarT "x")::[]) ;;
let qxy = PredF ("q", (VarT "x")::(VarT "y")::[]) ;;
let rxy = PredF ("r", (VarT "x")::(VarT "y")::[]) ;;
let less_xy = PredF ("<", (VarT "x")::(VarT "y")::[]) ;;
(*
let px = PredF ("p", (VarT "x")::[]) ;;
let a = ImpF (ExistsF ("x", (OrF (px, px))), (ExistsF ("x", px))) ;;
*)

let iff a b = andf (impf a b) (impf b a) ;;
let neg = n ;;

(*
let form_8_I  = all "x" (all "y" (impf (n qxy) (n pxy))) ;;
let form_8_II = all "x" (all "y" (impf (andf pxy qxy) rxy)) ;;
let form_8_III = all "x" (ex "y" (impf pxy qxy)) ;;
let form_9_I = ex "x" (ex "y" less_xy) ;;
let form_9_II = all "x" (ex "y" less_xy) ;;
let form_9_III = all "x" (n (andf px (all "y" (orf (n py) qy)))) ;;
let form_9_IV = ex "x" (all "y" (andf (andf pxy qx) (n ry))) ;;
*)

let zero = AppT ("0", [])
let predic x = PredF ("p", x :: []);;
let suc x = AppT ("suc", x :: []);;
let p0 = predic zero ;;
let px = predic (VarT "x") ;;
let psucx = predic (suc (VarT "x")) ;;
let suma x y z = PredF ("s", x :: y :: z :: []) ;;
let f1 = (impf
            (andf p0 (all "x" (impf px psucx)))
            (all "x" px)) ;;
let f2 = all "x" (suma zero (VarT "x") (VarT "x"));;
let f3 = all "x" (impf
                   (suma (VarT "x") (suc (VarT "y")) (VarT "z"))
                   (suma (suc (VarT "x")) (VarT "y") (VarT "z"))) ;;
let f4 = all "x" (iff px (all "y" (all "z"
                   (iff (suma (VarT "x") (VarT "y") (VarT "z"))
                        (suma (VarT "y") (VarT "x") (VarT "z")))))) ;;
let f5 = all "x" px ;;
let form =
 (n
    (impf
       (**(andf f1 (andf f2 (andf f3 f4)))**)
       (andf (andf (andf f1 f2) f3) f4)
       f5)
 ) ;;

print_conversion form ;;

