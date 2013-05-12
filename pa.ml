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
  Kernel
  ======

  Basically, we use sequents in two ways:
   either as a goal (something yet to be proven),
   or as a theorem (a proved statement).
  We protect the creation of theorems
   by marking the type as private in the Kernel
   module. Only the three inference rules can be
   used to construct theorems.
   
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
module type KERNEL =
  sig
    type formula =
      | Var of int
      | Imp of formula * formula

    type sequent =
      (formula list) * formula

    type theorem = private
      Provable of sequent

    type goal =
      Goal of sequent

    exception RuleException of string

    val assume : formula -> theorem
    val intro_rule : formula -> theorem -> theorem
    val elim_rule : theorem -> theorem -> theorem
  end;;

module Kernel : KERNEL = struct
  type formula =
    | Var of int
    | Imp of formula * formula

  type sequent =
    (formula list) * formula

  type theorem =
    Provable of sequent

  type goal =
    Goal of sequent

  exception RuleException of string

  let assume (a : formula) : theorem =
    Provable ([a], a);;

  let intro_rule (a : formula) (Provable (gamma, b) : theorem) : theorem =
    Provable (gamma -- a, Imp (a,b));;

  let elim_rule (Provable (gamma, imp) : theorem)
                (Provable (delta, a) : theorem)
              : theorem =
    match imp with
      | Var _ -> raise (RuleException "cannot use [elim_rule] with (Var _) in first argument")
      | Imp (a', b) ->
        if imp = Imp(a, b) then
          Provable (gamma @ delta, b)
        else
          raise (RuleException "antecedent of first argument must be the second argument");;
end;;

include Kernel;;



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

let print_theorem (Provable (l, a) : theorem) : string =
    (String.concat ", " (List.map print_formula l)) ^ " |- " ^ (print_formula a);;

let print_goal (Goal (l, a) : goal) : string =
    (String.concat ", " (List.map print_formula l)) ^ " ?- " ^ (print_formula a);;



(*
  Tactics
  =======
  
  Breaking up goals into smaller pieces,
   and providing justification functions.
*)
type justification = (theorem list) -> theorem;;
type goalstate = (goal list) * justification;;
type tactic = goal -> goalstate;;

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

(* An easy way to check against the conclusion of a theorem *)
let (|-) (th : theorem) (f : formula) =
  match th with
  | Provable (_, f') when f = f' -> true
  | _ -> false;;

let assumption (Goal (gamma, a) : goal) : goalstate =
  if List.mem a gamma then
    ([], fun _ -> assume a)
  else raise (TacticException "assumption tactic not applicable");;

let intro_tac (Goal (gamma, imp) : goal) : goalstate =
  match imp with
    | Var _ -> raise (TacticException "intro tactic only works on implicative goals")
    | Imp (a,b) ->
      [Goal (a::gamma, b)],
      function
        | [th] when th |- b ->
          intro_rule a th
        | _ -> raise JustificationException;;

let elim_tac (a : formula) (Goal (gamma, b) : goal) : goalstate =
    [Goal (gamma, Imp (a,b)); Goal (gamma, a)],
    function
      | [th1; th2] when th1 |- Imp (a,b) && th2 |- a ->
        elim_rule th1 th2
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
  let s = print_goal (current_goal ()) in
    print_string (s ^ "\n");
    s;;

let g (a : formula) =
  history := [
    [Goal ([], a)],
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
