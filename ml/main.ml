open Lexer
open Lexing
open Vhal
open Display

let read s =
  try Parser.main Lexer.read (Lexing.from_string s) with
  | _ -> failwith "invalid_syntax"
       
                  (** COMMAND *)

let currState = ref (initial (Pred(stocs "No goal yet!", [])))

let question s z = " ?" :: s :: z

let printParam = function
  | (a, []) -> ()
  | (a, ts) -> print_string
                 (String.concat ""
                    (a :: " not in " :: (List.fold_right question ts ["\n"])))

let rec printGoals = function
  | (_, []) -> ()
  | (n, g :: gs) -> printGoal n g; printGoals (n+1, gs)

let printState st =
  let p = main st in
  let gs = subgoals st
  in form p;
     if final st then print_string "No subgoals left!\n"
     else (printGoals (1, gs);
           List.iter
             (fun (x,y) -> printParam (ctos x, List.map ctos y))
             (List.fold_right goal_params gs []))

let setState state = printState state; currState := state

let thm s = setState (initial (read s))

let by (tac : state -> state list option) =
  match tac !currState with
  | Some e ->
     (try setState (List.hd e) with
      | _ -> print_endline "tactic failed!")
  | _ -> print_endline "tactic failed!!"

let getState () = printState (!currState);               
