type t =
  | Block of t list * int * int                (* indentation, length *)
  | String of string
  | Break of int                               (* length *)

(* Add the lengths of the expressions until the next Break; if no Break tan
   include "after", to account for the text following this block. *)           
let rec breakdist ts after = match ts with
  | Block(_,_,len) :: es -> len + (breakdist es after)
  | String s :: es -> (String.length) s + (breakdist es after)
  | Break _ :: es -> 0
  | [] -> after

let rec pr e margin =
  let space = ref margin in
  
  let blanks n = print_string (String.make n ' ');
                 space := !space - n in
  
  let newline () = print_newline() ; space := margin in
  
  let rec printing = function
    | ([], _, _) -> ()
    | (e :: es, blockspace, after) ->
       (match e with
        | Block(bes, indent, len) ->
           printing(bes @ es, !space - indent, breakdist es after)
        | String s -> print_string s; space := !space - (String.length s);
                      printing(es, blockspace, breakdist es after);
        | Break len ->
           if len + (breakdist es after) <= !space
           then blanks len
           else (blanks(margin - blockspace));
           printing (es, blockspace, after))
      
  in printing([e], margin, 0); newline()

let len' = function
  | Block(_, _, len) -> len
  | String s -> String.length s
  | Break len -> len

let str x = String x
let brk n = Break n

let blo (indent, es) =
  let rec sum m = match m with
    | ([], k) -> k
    | (e :: es, k) -> sum(es, len' e + k)
  in Block(es, indent, sum(es,0))
       
let enclose sexp =
  blo (1, [str "("; sexp; str ")"])

let rec commas = function
  | [] -> []
  | sexp :: sexps -> str "," :: brk 1 :: sexp :: commas sexps

let list = function
  | sexp :: sexps -> blo (0, sexp :: commas sexps)
  | _ -> blo (0, [])

let ctos cs = String.concat "" (List.map (String.make 1) cs)
let stocs s = List.of_seq (String.to_seq s)
           
let rec term = function
  | Vhal.Param(a, _) -> str (ctos a)
  | Vhal.Var a -> str ("?" ^ (ctos a))
  | Vhal.Bound i -> str "??UNMATCHED INDEX??"
  | Vhal.Fun(a, ts) -> blo(0, [str (ctos a); args ts])
and args = function
  | [] -> str ""
  | ts -> enclose (list (List.map term ts))

let precOf = function
  | "~" -> 4
  | "&" -> 3
  | "|" -> 2
  | "<->" -> 1
  | "-->" -> 1
  | _ -> -1

(* display formula in context of operator with precedence k *)
let rec formp k f = match f with
  | Vhal.Pred(a, ts) -> blo(0, [str (ctos a); args ts])
  | Vhal.Conn(['~'], [p]) ->
     blo(0, [str "~"; formp (precOf "~") p])
  | Vhal.Conn(c, [p;q]) ->
     let pf = formp (max (precOf (ctos c)) k) in
     let sexp = blo(0, [pf p; str (" " ^ (ctos c)); brk 1; pf q]) in
     if precOf (ctos c) <= k then (enclose sexp) else sexp
  | Vhal.Quant(qnt,b,p) ->
     let q = Vhal.subst' 0 (Vhal.Fun(b,[])) p in
     let sexp = blo(2, [str ((ctos qnt) ^ " " ^ (ctos b) ^ ".");
                        brk 1; formp 0 q])
     in if k > 0 then (enclose sexp) else sexp
  | _ -> str "??UNKNOWN FORMAT??"
           
let formList = function
  | [] -> str "empty"
  | ps -> list (List.map (formp 0) ps)

let form p = pr (formp 0 p) 50

let printGoal (n : int) = function
  | (ps, qs) -> pr (blo (4, [str (" " ^ Pervasives.string_of_int n ^ ". ");
                             formList ps; brk 2; str "|-   "; formList qs]))
                  150

