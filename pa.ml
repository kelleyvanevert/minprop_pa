(*
  Helper functions
  ================
*)

(* Infix notation to remove an element (and it's duplicates) from a list *)
let (--) (l : 'a list) (e : 'a) = List.filter (fun e' -> e <> e') l;;

(* Split a list in two, given a split point *)
let split l n =
  let rec aux i acc = function
    | [] -> (List.rev acc, [])
    | h :: t as l -> if i == 0 then List.rev acc, l
                     else aux (i - 1) (h :: acc) t in
    aux n [] l;;


(*
  Core data types
  ===============
  
  Basically, we use sequents in two ways:
   either as a goal (something yet to be proven),
   of as a theorem (a proved statement).
  Ideally, the first one can be constructed
   ad hoc, anytime, anywhere, while the second
   is protected by a module (as is, e.g.,
   HOL Light).
   
  Tactics break a single goal into smaller
   pieces, conceptually going "up the
   natural deduction tree", but must also
   provide justification for their breaking up,
   in terms of a function that reconnects
   theorems of those pieces into a theorem of
   the original goal. This justification function
   may of course only use the three inference rules
   of minimal propositional logic.
*)
type formula =
  | Var of int
  | Imp of formula * formula;;

type sequent =
  (formula list) * formula;;

(* This one ideally protected by a module.. *)
type theorem =
  Proof of sequent;;

(* ..while this one is for "free" *)
type goal =
  Proposition of sequent;;

type justification = (theorem list) -> theorem;;
type goalstate = (goal list) * justification;;
type tactic = goal -> goalstate;;


(*
  Pretty printing
  ===============
  
  A TODO is to allow input like in HOL Light,
   e.g. writing
      `A => B => A`
   for
      Imp (Var 0, Imp (Var 1, Var 0))
*)
let rec print_formula : formula -> string = function
  | Var n -> Char.escaped (Char.chr (n + 65))
  | Imp (a,b) -> "(" ^ (print_formula a) ^ " => " ^ (print_formula b) ^ ")";;

let print_theorem (Proof (l, a) : theorem) : string =
    (String.concat ", " (List.map print_formula l)) ^ " |- " ^ (print_formula a);;

let print_goal (Proposition (l, a) : goal) : string =
    (String.concat ", " (List.map print_formula l)) ^ " ?- " ^ (print_formula a);;


(*
  Inference rules for minimal propositional logic
  ===============================================
*)
exception RuleException of string;;

let assume (a : formula) : theorem =
  Proof ([a], a);;

let intro_rule (a : formula) (Proof (gamma, b) : theorem) : theorem =
  Proof (gamma -- a, Imp (a,b));;

let elim_rule (Proof (gamma, imp) : theorem)
              (Proof (delta, a) : theorem)
            : theorem =
  match imp with
    | Var _ -> raise (RuleException "cannot use [elim_rule] with (Var _) in first argument")
    | Imp (a', b) ->
      if imp = Imp(a, b) then
        Proof (gamma @ delta, b)
      else
        raise (RuleException "antecedent of first argument must be the second argument");;


(*
  Tactics
  =======
  
  Breaking up goals into smaller pieces,
   and providing justification functions.
*)
let by (tac : tactic) ((goals, j1) : goalstate) : goalstate =
  match goals with
    | [] -> (goals, j1) (* do nothing *)
    | g :: gs2 ->
      let (gs2, j2) = tac g in (
          gs2 @ gs2,
          fun thms -> (* TODO check lengths *)
            let (thms2, thms1) = split thms (List.length gs2) in
              j1 ((j2 thms2) :: thms1)
        );;

exception TacticException of string;;
exception JustificationException;;

let assumption (Proposition (gamma, a) : goal) : goalstate =
  if List.mem a gamma then
    ([], fun _ -> assume a)
  else raise (TacticException "assumption tactic not applicable");;

let intro_tac (Proposition (gamma, imp) : goal) : goalstate =
  match imp with
    | Var _ -> raise (TacticException "intro tactic only works on implicative goals")
    | Imp (a,b) ->
      [Proposition (a::gamma, b)],
      function
        | [Proof (delta, b')] ->
          if b = b' then
            intro_rule a (Proof (delta, b))
          else raise JustificationException
        | _ -> raise JustificationException;;

let elim_tac (a : formula) (Proposition (gamma, b) : goal) : goalstate =
    [Proposition (gamma, Imp (a,b)); Proposition (gamma, a)],
    function
      | [Proof (delta, imp); Proof (delta', a')] ->
        if imp = Imp (a,b) && a = a' then
          elim_rule (Proof (delta, imp)) (Proof (delta', a'))
        else raise JustificationException
      | _ -> raise JustificationException;;


(*
  Stateful proof environment
  ==========================
*)
exception QED;;

let history : goalstate list ref =
  ref [];;

let current_goalstate () =
  match !history with
  | goalstate :: t -> goalstate
  | _ -> raise Not_found;;

let current_goal () =
  match current_goalstate () with
  | (g :: _, _) -> g
  | _ -> raise QED;;

let p () =
  print_goal (current_goal ());;

let g (a : formula) =
  history := [
    [Proposition ([], a)],
    function
    | [th] -> th
    | _ -> raise JustificationException
  ];
  p();;

let e (tac : tactic) =
  match !history with
  | goalstate :: t ->
    history := (by tac goalstate) :: goalstate :: t;
    p()
  | _ -> raise Not_found;;

let b () =
  match !history with
  | goalstate :: t ->
    history := t;
    p()
  | _ ->
    p();;

let top_theorem () : theorem =
  let (_, j) = current_goalstate() in j [];;


(*
  An example
  ==========
*)
g (Imp (Var 0, Imp (Var 1, Var 0)));;
e intro_tac;;
e intro_tac;;
e assumption;;
print_theorem (top_theorem ());;
