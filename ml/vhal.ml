
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val add : int -> int -> int **)

let rec add = (+)

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Pervasives.max 0 (n-m)

(** val divmod : int -> int -> int -> int -> int * int **)

let rec divmod x y q u =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (q, u))
    (fun x' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> divmod x' y (succ q) y)
      (fun u' -> divmod x' y q u')
      u)
    x

(** val div : int -> int -> int **)

let div x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> y)
    (fun y' -> fst (divmod x y' 0 y'))
    y

(** val modulo : int -> int -> int **)

let modulo x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> y)
    (fun y' -> sub y' (snd (divmod x y' 0 y')))
    y

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (succ n) m

  (** val max : int -> int -> int **)

  let rec max n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' -> (fun fO fS n -> if n=0 then fO () else fS (n-1))
                   (fun _ -> n)
                   (fun m' -> succ (max n' m'))
                   m)
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> succ 0)
      (fun m0 -> mul n (pow n m0))
      m
 end

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> None
              | x :: _ -> Some x)
    (fun n0 -> match l with
               | [] -> None
               | _ :: l0 -> nth_error l0 n0)
    n

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n0 -> match l with
               | [] -> []
               | a :: l0 -> a :: (firstn n0 l0))
    n

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n0 -> match l with
               | [] -> []
               | _ :: l0 -> skipn n0 l0)
    n

(** val string_dec : char list -> char list -> bool **)

let rec string_dec s x =
  match s with
  | [] -> (match x with
           | [] -> true
           | _::_ -> false)
  | a::s0 -> (match x with
              | [] -> false
              | a0::s1 -> if (=) a a0 then string_dec s0 s1 else false)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val substring : int -> int -> char list -> char list **)

let rec substring n m s =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> [])
      (fun m' -> match s with
                 | [] -> s
                 | c::s' -> c::(substring 0 m' s'))
      m)
    (fun n' -> match s with
               | [] -> s
               | _::s' -> substring n' m s')
    n

(** val beq_nat : int -> int -> bool **)

let beq_nat =
  (=)

(** val beq_string : char list -> char list -> bool **)

let beq_string x y =
  if string_dec x y then true else false

(** val beq_string_list : char list list -> char list list -> bool **)

let rec beq_string_list ss ts =
  match ss with
  | [] -> (match ts with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs -> (match ts with
                | [] -> false
                | y :: ys -> (&&) (beq_string x y) (beq_string_list xs ys))

(** val insert_string : char list -> char list list -> char list list **)

let rec insert_string s = function
| [] -> s :: []
| t :: ts -> if string_dec s t then s :: ts else t :: (insert_string s ts)

(** val ret : 'a1 -> 'a1 option **)

let ret x =
  Some x

(** val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let bind a f =
  match a with
  | Some x -> f x
  | None -> None

type term =
| Var of char list
| Param of char list * char list list
| Bound of int
| Fun of char list * term list

type formula =
| Pred of char list * term list
| Conn of char list * formula list
| Quant of char list * char list * formula

type goal = formula list * formula list
  (* singleton inductive, whose constructor was G *)

(** val beq_term : term -> term -> bool **)

let rec beq_term t1 t2 =
  match t1 with
  | Var u -> (match t2 with
              | Var v -> beq_string u v
              | _ -> false)
  | Param (s, st) ->
    (match t2 with
     | Param (s', st') -> (&&) (beq_string s s') (beq_string_list st st')
     | _ -> false)
  | Bound n -> (match t2 with
                | Bound m -> beq_nat n m
                | _ -> false)
  | Fun (u, us) ->
    (match t2 with
     | Fun (v, vs) ->
       (&&) (beq_string u v)
         (let rec beq_term_list0 us0 vs0 =
            match us0 with
            | [] -> (match vs0 with
                     | [] -> true
                     | _ :: _ -> false)
            | x :: xs -> (match vs0 with
                          | [] -> false
                          | y :: ys -> (&&) (beq_term x y) (beq_term_list0 xs ys))
          in beq_term_list0 us vs)
     | _ -> false)

(** val replace' : term -> term -> term -> term **)

let rec replace' u1 u2 t =
  if beq_term u1 t
  then u2
  else (match t with
        | Fun (a, ts) ->
          Fun (a,
            (let rec replace'_list u3 u4 = function
             | [] -> []
             | s :: ss -> (replace' u3 u4 s) :: (replace'_list u3 u4 ss)
             in replace'_list u1 u2 ts))
        | _ -> t)

(** val abstract' : int -> term -> formula -> formula **)

let rec abstract' i t = function
| Pred (a, ts) -> Pred (a, (map (replace' t (Bound i)) ts))
| Conn (b, ps) ->
  Conn (b,
    (let rec abstract'_list i0 t0 = function
     | [] -> []
     | f0 :: fs' -> (abstract' i0 t0 f0) :: (abstract'_list i0 t0 fs')
     in abstract'_list i t ps))
| Quant (qnt, b, p) -> Quant (qnt, b, (abstract' (succ i) t p))

(** val subst' : int -> term -> formula -> formula **)

let rec subst' i t = function
| Pred (a, ts) -> Pred (a, (map (replace' (Bound i) t) ts))
| Conn (b, ps) ->
  Conn (b,
    (let rec subst'_list i0 t0 = function
     | [] -> []
     | f0 :: fs' -> (subst' i0 t0 f0) :: (subst'_list i0 t0 fs')
     in subst'_list i t ps))
| Quant (qnt, b, p) -> Quant (qnt, b, (subst' (succ i) t p))

(** val term_vars : term -> char list list -> char list list **)

let rec term_vars t ps =
  match t with
  | Var a -> insert_string a ps
  | Fun (_, ts) -> fold_right term_vars ps ts
  | _ -> ps

(** val term_params : term -> (char list * char list list) list -> (char list * char list list) list **)

let rec term_params t ps =
  match t with
  | Param (a, xs) -> (a, xs) :: ps
  | Fun (_, ts) -> fold_right term_params ps ts
  | _ -> ps

(** val beq_term_list : term list -> term list -> bool **)

let rec beq_term_list ts us =
  match ts with
  | [] -> (match us with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs -> (match us with
                | [] -> false
                | y :: ys -> (&&) (beq_term x y) (beq_term_list xs ys))

(** val beq_formula : formula -> formula -> bool **)

let rec beq_formula f1 f2 =
  match f1 with
  | Pred (a, ts) -> (match f2 with
                     | Pred (b, us) -> (&&) (beq_string a b) (beq_term_list ts us)
                     | _ -> false)
  | Conn (a, fs) ->
    (match f2 with
     | Conn (b, gs) ->
       (&&) (beq_string a b)
         (let rec beq_formula_list ts us =
            match ts with
            | [] -> (match us with
                     | [] -> true
                     | _ :: _ -> false)
            | x :: xs ->
              (match us with
               | [] -> false
               | y :: ys -> (&&) (beq_formula x y) (beq_formula_list xs ys))
          in beq_formula_list fs gs)
     | _ -> false)
  | Quant (a0, b0, f0) ->
    (match f2 with
     | Quant (a1, b1, f3) -> (&&) (beq_string a0 a1) ((&&) (beq_string b0 b1) (beq_formula f0 f3))
     | _ -> false)

(** val accum_form : (term -> 'a1 -> 'a1) -> formula -> 'a1 -> 'a1 **)

let rec accum_form g f z =
  match f with
  | Pred (_, ts) -> fold_right g z ts
  | Conn (_, ps) -> fold_right (accum_form g) z ps
  | Quant (_, _, p) -> accum_form g p z

(** val accum_goal : (formula -> 'a1 -> 'a1) -> goal -> 'a1 -> 'a1 **)

let rec accum_goal f g z =
  let (ps, qs) = g in fold_right f (fold_right f z qs) ps

(** val goal_vars : goal -> char list list -> char list list **)

let goal_vars =
  accum_goal (accum_form term_vars)

(** val goal_params : goal -> (char list * char list list) list -> (char list * char list list) list **)

let goal_params =
  accum_goal (accum_form term_params)

type env = (char list * term) list

(** val env_update : env -> char list -> term -> (char list * term) list **)

let env_update e s t =
  (s, t) :: e

(** val env_lookup : env -> char list -> term option **)

let rec env_lookup e s =
  match e with
  | [] -> None
  | p :: ts -> let (s', t) = p in if beq_string s s' then Some t else env_lookup ts s

(** val chase : env -> term -> term option **)

let chase e t = match t with
| Var x ->
  let rec chase'0 n e0 s =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Some t)
      (fun n' ->
      let v = env_lookup e0 s in
      (match v with
       | Some t0 -> (match t0 with
                     | Var y -> chase'0 n' e0 y
                     | _ -> v)
       | None -> v))
      n
  in chase'0 (length e) e x
| _ -> Some t

(** val size : term -> int **)

let rec size = function
| Param (_, bs) -> succ (length bs)
| Fun (_, ts) ->
  succ (let rec sizelist = function
        | [] -> 0
        | t0 :: ts' -> add (size t0) (sizelist ts')
        in sizelist ts)
| _ -> succ 0

(** val occurs_fuel : int -> env -> char list -> term -> bool **)

let rec occurs_fuel n e s t =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> false)
    (fun n' ->
    match t with
    | Var x ->
      (||) (beq_string x s)
        (let v = env_lookup e x in match v with
                                   | Some t0 -> occurs_fuel n' e s t0
                                   | None -> false)
    | Param (_, bs) ->
      let rec occurs'_params s0 = function
      | [] -> false
      | v :: vs -> (||) (occurs_fuel n' e s0 (Var v)) (occurs'_params s0 vs)
      in occurs'_params s bs
    | Bound _ -> false
    | Fun (_, ts) ->
      let rec occurs'_list s0 = function
      | [] -> false
      | v :: vs -> (||) (occurs_fuel n' e s0 v) (occurs'_list s0 vs)
      in occurs'_list s ts)
    n

(** val occ : env -> char list -> term -> bool **)

let occ e s t =
  occurs_fuel (Nat.max (length e) (size t)) e s t

(** val oc' : char list -> term -> bool **)

let oc' s t =
  occ [] s t

(** val chase' : env -> term -> term option **)

let chase' e t =
  let v = chase e t in (match v with
                        | Some _ -> v
                        | None -> Some t)

(** val get_env : (int * env) -> env **)

let get_env = function
| (_, v) -> v

(** val unify_fuel : int -> env -> term -> term -> (int * env) option **)

let rec unify_fuel n e s t =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun m ->
    match s with
    | Var a -> if beq_term t s then ret (m, e) else if oc' a t then None else ret (m, (env_update e a t))
    | Param (a, _) ->
      (match t with
       | Var a0 -> unify_fuel m e (Var a0) s
       | Param (b, _) -> if beq_string a b then ret (m, e) else None
       | _ -> None)
    | Bound _ -> (match t with
                  | Var a -> unify_fuel m e (Var a) s
                  | _ -> None)
    | Fun (a, ts) ->
      (match t with
       | Var a0 -> unify_fuel m e (Var a0) s
       | Fun (b, us) -> if beq_string a b then unifyl_fuel m e ts us else None
       | _ -> None))
    n

(** val unifyl_fuel : int -> env -> term list -> term list -> (int * env) option **)

and unifyl_fuel n e ts us =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun m ->
    match ts with
    | [] -> (match us with
             | [] -> ret (m, e)
             | _ :: _ -> None)
    | t :: ts' ->
      (match us with
       | [] -> None
       | u :: us' ->
         bind (chase' e t) (fun t' ->
           bind (chase' e u) (fun u' ->
             bind (unify_fuel m e t' u') (fun e' -> unifyl_fuel m (get_env e') ts' us')))))
    n

(** val unify_lists : term list -> term list -> env option **)

let unify_lists ts us =
  if (=) (length ts) (length us)
  then bind (unifyl_fuel (Nat.pow (succ (succ 0)) (fold_right add 0 (map size ts))) [] ts us) (fun e ->
         ret (get_env e))
  else None

(** val atoms : formula -> formula -> env option **)

let atoms f g =
  match f with
  | Pred (a, ts) ->
    (match g with
     | Pred (b, us) -> if beq_string a b then unify_lists ts us else None
     | _ -> None)
  | _ -> None

(** val inst_term_fuel : int -> env -> term -> term **)

let rec inst_term_fuel n e t =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> t)
    (fun m ->
    match t with
    | Var a -> (match env_lookup e a with
                | Some t' -> inst_term_fuel m e t'
                | None -> Var a)
    | Param (a, bs) -> Param (a, (fold_right term_vars [] (map (fun x -> inst_term_fuel m e (Var x)) bs)))
    | Bound _ -> t
    | Fun (a, ts) -> Fun (a, (map (inst_term_fuel m e) ts)))
    n

(** val inst_term : env -> term -> term **)

let inst_term e t =
  inst_term_fuel (Nat.pow (succ (succ 0)) (length e)) e t

(** val inst_form : env -> formula -> formula **)

let rec inst_form e = function
| Pred (a, ts) -> Pred (a, (map (inst_term e) ts))
| Conn (b, ps) -> Conn (b, (map (inst_form e) ps))
| Quant (qnt, b, p) -> Quant (qnt, b, (inst_form e p))

(** val inst_goal : env -> goal -> goal **)

let inst_goal e = function
| (ps, qs) -> ((map (inst_form e) ps), (map (inst_form e) qs))

type state =
| State of goal list * formula * int

type tactic = state -> state list option

(** val main : state -> formula **)

let main = function
| State (_, p, _) -> p

(** val subgoals : state -> goal list **)

let subgoals = function
| State (gs, _, _) -> gs

(** val initial : formula -> state **)

let initial p =
  State ((([], (p :: [])) :: []), p, 0)

(** val final : state -> bool **)

let final = function
| State (l, _, _) -> (match l with
                      | [] -> true
                      | _ :: _ -> false)

(** val splice_goals : goal list -> goal list -> int -> goal list **)

let splice_goals gs newgs i =
  app (firstn (sub i (succ 0)) gs) (app newgs (skipn i gs))

(** val prop_rule : (goal -> goal list option) -> int -> state -> state list option **)

let prop_rule gF i = function
| State (gs, p, n) ->
  bind (nth_error gs (sub i (succ 0))) (fun gi ->
    bind (gF gi) (fun gs' -> bind (ret (splice_goals gs gs' i)) (fun g2 -> ret ((State (g2, p, n)) :: []))))

(** val basic : int -> tactic **)

let basic =
  prop_rule (fun g ->
    let (ps, qs) = g in if existsb (fun p -> existsb (fun q -> beq_formula p q) qs) ps then Some [] else None)

(** val unifiable' : formula list -> formula list -> env list **)

let rec unifiable' ts us =
  match ts with
  | [] -> []
  | p :: ps ->
    let rec ufind qs = match qs with
    | [] -> unifiable' ps qs
    | q :: qs' -> (match atoms p q with
                   | Some e -> e :: (ufind qs')
                   | None -> ufind qs')
    in ufind us

(** val unifiable : goal -> env list **)

let rec unifiable = function
| (ps, qs) -> unifiable' ps qs

(** val inst : env -> goal list -> formula -> int -> state **)

let inst e gs p n =
  State ((map (inst_goal e) gs), p, n)

(** val next : env -> goal list -> formula -> int -> int -> state **)

let next e gs p i n =
  inst e (splice_goals gs [] i) p n

(** val unif : int -> state -> state list option **)

let rec unif i = function
| State (gs, p, n) ->
  bind (nth_error gs (sub i (succ 0))) (fun g -> ret (map (fun e -> next e gs p i n) (unifiable g)))

(** val getp : char list -> formula list -> formula list option **)

let rec getp a = function
| [] -> None
| q :: qs -> (match q with
              | Conn (b, ps) -> if beq_string a b then Some ps else getp a qs
              | _ -> getp a qs)

(** val delp : char list -> formula list -> formula list **)

let rec delp a = function
| [] -> []
| q :: qs ->
  (match q with
   | Conn (b, _) -> if beq_string a b then qs else q :: (delp a qs)
   | _ -> q :: (delp a qs))

(** val split_conn : char list -> formula list -> (formula list * formula list) option **)

let split_conn a qs =
  bind (getp a qs) (fun ps -> ret (ps, (delp a qs)))

(** val prop_l :
    char list -> (((formula list * formula list) * formula list) -> goal list option) -> int -> state -> state
    list option **)

let prop_l a leftF =
  prop_rule (fun g -> let (ps, qs) = g in bind (split_conn a ps) (fun ps' -> leftF (ps', qs)))

(** val prop_r :
    char list -> ((formula list * (formula list * formula list)) -> goal list option) -> int -> state -> state
    list option **)

let prop_r a rightF =
  prop_rule (fun g -> let (ps, qs) = g in bind (split_conn a qs) (fun qs' -> rightF (ps, qs')))

(** val conjL : int -> tactic **)

let conjL =
  prop_l ('&'::[]) (fun x ->
    let (p, qs) = x in
    let (l, ps) = p in
    (match l with
     | [] -> None
     | p1 :: l0 ->
       (match l0 with
        | [] -> None
        | p2 :: l1 -> (match l1 with
                       | [] -> ret (((p1 :: (p2 :: ps)), qs) :: [])
                       | _ :: _ -> None))))

(** val conjR : int -> tactic **)

let conjR =
  prop_r ('&'::[]) (fun x ->
    let (ps, p) = x in
    let (l, qs) = p in
    (match l with
     | [] -> None
     | q1 :: l0 ->
       (match l0 with
        | [] -> None
        | q2 :: l1 -> (match l1 with
                       | [] -> ret ((ps, (q1 :: qs)) :: ((ps, (q2 :: qs)) :: []))
                       | _ :: _ -> None))))

(** val disjL : int -> tactic **)

let disjL =
  prop_l ('|'::[]) (fun x ->
    let (p, qs) = x in
    let (l, ps) = p in
    (match l with
     | [] -> None
     | p1 :: l0 ->
       (match l0 with
        | [] -> None
        | p2 :: l1 -> (match l1 with
                       | [] -> ret (((p1 :: ps), qs) :: (((p2 :: ps), qs) :: []))
                       | _ :: _ -> None))))

(** val disjR : int -> tactic **)

let disjR =
  prop_r ('|'::[]) (fun x ->
    let (ps, p) = x in
    let (l, qs) = p in
    (match l with
     | [] -> None
     | q1 :: l0 ->
       (match l0 with
        | [] -> None
        | q2 :: l1 -> (match l1 with
                       | [] -> ret ((ps, (q1 :: (q2 :: qs))) :: [])
                       | _ :: _ -> None))))

(** val impL : int -> tactic **)

let impL =
  prop_l ('-'::('-'::('>'::[]))) (fun x ->
    let (p, qs) = x in
    let (l, ps) = p in
    (match l with
     | [] -> None
     | p1 :: l0 ->
       (match l0 with
        | [] -> None
        | p2 :: l1 -> (match l1 with
                       | [] -> ret (((p2 :: ps), qs) :: ((ps, (p1 :: qs)) :: []))
                       | _ :: _ -> None))))

(** val impR : int -> tactic **)

let impR =
  prop_r ('-'::('-'::('>'::[]))) (fun x ->
    let (ps, p) = x in
    let (l, qs) = p in
    (match l with
     | [] -> None
     | q1 :: l0 ->
       (match l0 with
        | [] -> None
        | q2 :: l1 -> (match l1 with
                       | [] -> ret (((q1 :: ps), (q2 :: qs)) :: [])
                       | _ :: _ -> None))))

(** val negL : int -> tactic **)

let negL =
  prop_l ('~'::[]) (fun x ->
    let (p0, qs) = x in
    let (l, ps) = p0 in
    (match l with
     | [] -> None
     | p :: l0 -> (match l0 with
                   | [] -> ret ((ps, (p :: qs)) :: [])
                   | _ :: _ -> None)))

(** val negR : int -> tactic **)

let negR =
  prop_r ('~'::[]) (fun x ->
    let (ps, p) = x in
    let (l, qs) = p in
    (match l with
     | [] -> None
     | q :: l0 -> (match l0 with
                   | [] -> ret (((q :: ps), qs) :: [])
                   | _ :: _ -> None)))

(** val iffL : int -> tactic **)

let iffL =
  prop_l ('<'::('-'::('>'::[]))) (fun x ->
    let (p, qs) = x in
    let (l, ps) = p in
    (match l with
     | [] -> None
     | p1 :: l0 ->
       (match l0 with
        | [] -> None
        | p2 :: l1 ->
          (match l1 with
           | [] -> ret (((p1 :: (p2 :: ps)), qs) :: ((ps, (p1 :: (p2 :: qs))) :: []))
           | _ :: _ -> None))))

(** val iffR : int -> tactic **)

let iffR =
  prop_r ('<'::('-'::('>'::[]))) (fun x ->
    let (ps, p) = x in
    let (l, qs) = p in
    (match l with
     | [] -> None
     | q1 :: l0 ->
       (match l0 with
        | [] -> None
        | q2 :: l1 ->
          (match l1 with
           | [] -> ret (((q1 :: ps), (q2 :: qs)) :: (((q2 :: ps), (q1 :: qs)) :: []))
           | _ :: _ -> None))))

(** val getq : char list -> formula list -> formula option **)

let rec getq qnt = function
| [] -> None
| q :: qs ->
  (match q with
   | Quant (qnt2, _, _) -> if beq_string qnt qnt2 then ret q else getq qnt qs
   | _ -> getq qnt qs)

(** val delq : char list -> formula list -> formula list **)

let rec delq qnt = function
| [] -> []
| q :: qs ->
  (match q with
   | Quant (qnt2, _, _) -> if beq_string qnt qnt2 then qs else q :: (delq qnt qs)
   | _ -> q :: (delq qnt qs))

(** val split_quant : char list -> formula list -> (formula * formula list) option **)

let rec split_quant qnt qs =
  bind (getq qnt qs) (fun ps -> ret (ps, (delq qnt qs)))

(** val letter : int -> char list **)

let letter n =
  substring n (succ 0)
    ('a'::('b'::('c'::('d'::('e'::('f'::('g'::('h'::('i'::('j'::('k'::('l'::('m'::('n'::('o'::('p'::('q'::('r'::('s'::('t'::('u'::('v'::('w'::('x'::('y'::('z'::[]))))))))))))))))))))))))))

(** val gensym' : int -> int -> char list **)

let rec gensym' n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n' ->
    if Nat.ltb m (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
         (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))))))))))))))))))))
    then append ('_'::[]) (letter m)
    else append
           (gensym' n'
             (div m (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
               (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))))))))))))))))))))))
           (letter
             (modulo m (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
               (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
               0)))))))))))))))))))))))))))))
    n

(** val gensym : int -> char list **)

let gensym n =
  gensym'
    (add
      (div n (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))))))))))))))))))))) (succ 0)) n

(** val quant_rule : (goal -> char list -> goal list option) -> int -> state -> state list option **)

let rec quant_rule gF i = function
| State (gs, p, n) ->
  bind (nth_error gs (sub i (succ 0))) (fun gi ->
    bind (gF gi (gensym n)) (fun gs' ->
      bind (ret (splice_goals gs gs' i)) (fun g2 -> ret ((State (g2, p, (add n (succ 0)))) :: []))))

(** val allL : int -> tactic **)

let allL =
  quant_rule (fun x b ->
    let (ps, qs) = x in
    bind (split_quant ('A'::('L'::('L'::[]))) ps) (fun qntForm ->
      let (q, ps') = qntForm in
      (match q with
       | Quant (_, _, p) -> let px = subst' 0 (Var b) p in ret (((px :: (app ps' (q :: []))), qs) :: [])
       | _ -> None)))

(** val allR : int -> tactic **)

let allR =
  quant_rule (fun x b ->
    let (ps, qs) = x in
    bind (split_quant ('A'::('L'::('L'::[]))) qs) (fun qntForm ->
      let (f, qs') = qntForm in
      (match f with
       | Quant (_, _, q) ->
         let vars = goal_vars x [] in let qx = subst' 0 (Param (b, vars)) q in ret ((ps, (qx :: qs')) :: [])
       | _ -> None)))

(** val exL : int -> tactic **)

let exL =
  quant_rule (fun x b ->
    let (ps, qs) = x in
    bind (split_quant ('E'::('X'::[])) ps) (fun qntForm ->
      let (f, ps') = qntForm in
      (match f with
       | Quant (_, _, p) ->
         let vars = goal_vars x [] in let px = subst' 0 (Param (b, vars)) p in ret (((px :: ps'), qs) :: [])
       | _ -> None)))

(** val exR : int -> tactic **)

let exR =
  quant_rule (fun x b ->
    let (ps, qs) = x in
    bind (split_quant ('E'::('X'::[])) qs) (fun qntForm ->
      let (q', qs') = qntForm in
      (match q' with
       | Quant (_, _, q) -> let qx = subst' 0 (Var b) q in ret ((ps, (qx :: (app qs' (q' :: [])))) :: [])
       | _ -> None)))


(** ADDED *)

let ctocs cs = String.concat "" (List.map (String.make 1) cs)
let stocs s = List.of_seq (String.to_seq s)             
  
let makeForall x f =
  Quant(stocs "ALL", stocs x, abstract' 0 (Fun(stocs x, [])) f)

let makeExists x f =
  Quant(stocs "EX", stocs x, abstract' 0 (Fun(stocs x, [])) f)

let makeConn (a : string) (p : formula) (q : formula) =
  Conn(stocs a, [p; q])

let makeNeg p = Conn(['~'], [p])    
