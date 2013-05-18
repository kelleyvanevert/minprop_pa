
(*
  Helper functions
  ================
*)

(* Infix notation to remove an element (and it's
    duplicates) from a list *)
let (--) (l : 'a list) (e : 'a) = List.filter (fun e' -> e <> e') l;;

(* Split a list in two, given a split point *)
let split l n =
  let rec aux i acc = function
    | [] -> (List.rev acc, [])
    | h :: t as l -> if i == 0 then List.rev acc, l
                     else aux (i - 1) (h :: acc) t in
    aux n [] l;;

(* Compose functions *)
let ($) f g x = f (g x);;

(* Find the first element of a list that satisfies
    a certain criterion and return it *)
let rec find p l =
  match l with
  | [] -> None
  | x :: xs -> if p x then Some x else find p xs;;




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
  Parsing and pretty printing
  ===========================
  (Really quite dirty, but I couldn't get my head around camlp5 just yet..)
*)
let rec print_formula : formula -> string = function
  | Var n -> Char.escaped (Char.chr (n + 65))
  | Imp (f0, f1) -> "(" ^ (print_formula f0) ^ " => " ^ (print_formula f1) ^ ")";;

let print_theorem (Provable (l, a) : theorem) : string =
    (String.concat ", " (List.map print_formula l)) ^ " |- " ^ (print_formula a);;

let print_goal (Goal (l, a) : goal) : string =
    (String.concat ", " (List.map print_formula l)) ^ " ?- " ^ (print_formula a);;

let (@@) (s : string) (n : int) =
  String.sub s n ((String.length s) - n);;

type token =
  | LParen
  | RParen
  | Arrow
  | TVar of int;;

let rec lex (s : string) : token list =
  if s = "" then
    []
  else if s.[0] = ' ' then
    lex (s @@ 1)
  else if s.[0] = '(' then
    LParen :: lex (s @@ 1)
  else if s.[0] = ')' then
    RParen :: lex (s @@ 1)
  else if String.length s >= 2 && String.sub s 0 2 = "=>" then
    Arrow :: lex (s @@ 2)
  else
    TVar ((Char.code s.[0]) - 65) :: lex (s @@ 1);;

exception ShuntingException of string * token list * token list * token list;;

let rec shunting output stack tokens =
  match tokens with
  | [] ->
    begin match stack with
    | LParen :: _ -> raise (ShuntingException ("left paren over", output, stack, tokens))
    | RParen :: _ -> raise (ShuntingException ("right paren over", output, stack, tokens))
    | y :: ys -> shunting (y :: output) ys []
    | [] -> output
    end
  | x :: rest ->
    begin match x with
    | TVar n -> shunting (TVar n :: output) stack rest
    | Arrow -> shunting output (Arrow :: stack) rest
    | LParen -> shunting output (LParen :: stack) rest
    | RParen ->
      begin match stack with
      | [] -> raise (ShuntingException ("too much right parens", output, stack, tokens))
      | LParen :: stack' -> shunting output stack' rest
      | t :: stack' -> shunting (t :: output) stack' tokens
      end
    end;;

exception ParseException of formula list * token list;;

let rec parse stack postfix_tokens =
  match (stack, postfix_tokens) with
  | stack, TVar n :: rest -> parse (Var n :: stack) rest
  | a :: b :: stack', Arrow :: rest -> parse (Imp (b, a) :: stack') rest
  | [f], [] -> f
  | _, _ -> raise (ParseException (stack, postfix_tokens));;

let formula (s : string) : formula =
  parse [] (List.rev (shunting [] [] (lex s)));;







(*
  Tactics
  =======
  
  Breaking up goals into smaller pieces,
   and providing justification functions.
*)
type justification = theorem list -> theorem;;
type goalstate = goal list * theorem;;
type tactic = goal -> (goal list * justification);;

exception TacticException of string;;
exception JustificationException;;

let collapse_formula_list (gamma : formula list) : formula =
  match gamma with
  | z :: xs -> List.fold_right (fun x y -> Imp (x, y)) xs z
  | [] -> raise Not_found;;

let goal_to_theorem (Goal (gamma, b)) : theorem =
  List.fold_left
    (fun th phi -> elim_rule th (assume phi))
    (assume (collapse_formula_list (b :: gamma)))
    gamma;;



(* If f0  =  a0 => a1 => ... => aN => f1, then
  diff f0 f1  =  [aN; ... a1; a0] *)
exception StripException;;
let diff f conclusion : formula list =
  let rec diff' f conclusion diff =
    begin match f with
    | c' when c' = conclusion -> diff
    | Imp (a, b) -> diff' b conclusion (a :: diff)
    | _ -> raise StripException
    end
  in
    diff' f conclusion [];;

let conclusion th =
  match th with
  | Provable (_, c) -> c;;






(*
  Apply a tactic to the first subgoal in the given goalstate,
   resulting in a new goalstate.

  If
    s = g :: gs1, "phi_g, gamma_gs1 |- psi"
  and
    tac g = gs2, _
  then
    by tac s = gs2 @ gs1, "gamma_gs2, gamma_gs1 |- psi"
*)
let by (tac : tactic) (goals, th : goalstate) : goalstate =
  match goals, th with
  | g :: gs1, Provable (phi_g :: _, _) ->
    let (gs2, j) = tac g in
    let th_a = intro_rule phi_g th in
    let th_b = j (List.map goal_to_theorem gs2) in
    let th_b' = List.fold_right intro_rule (List.rev (diff phi_g (conclusion th_b))) th_b in
    gs2 @ gs1, elim_rule th_a th_b'
  | _, _ -> raise (TacticException "There must be an open goal");;

(* An easy way to check against the conclusion of a theorem *)
let (|-) (th : theorem) (f : formula) =
  match th with
  | Provable (_, f') when f = f' -> true
  | _ -> false;;

let assumption (Goal (gamma, a) : goal) =
  if List.mem a gamma then
    [], fun _ -> assume a
  else raise (TacticException "assumption tactic not applicable");;

let intro_tac (Goal (gamma, imp) : goal) =
  match imp with
    | Var _ -> raise (TacticException "intro tactic only works on implicative goals")
    | Imp (a, b) ->
      [Goal (gamma @ [a], b)],
      fun thms ->
        match find (fun th -> th |- b) thms with
        | Some th -> intro_rule a th
        | _ -> raise JustificationException;;

let elim_tac (a : formula) (Goal (gamma, b) : goal) =
    [Goal (gamma, Imp (a,b)); Goal (gamma, a)],
    fun thms ->
      match find (fun th -> th |- Imp (a, b)) thms,
            find (fun th -> th |- a) thms with
      | Some th_imp, Some th_b -> elim_rule th_imp th_b
      | _ -> raise JustificationException;;


(* Some tacticals *)

let try_tac (tac : tactic) (g : goal) : goal list * justification =
  try
    tac g
  with (TacticException _) ->
    [g], function [th] -> th | _ -> raise JustificationException;;

let rec repeat_tac (tac : tactic) (g : goal) : goal list * justification =
  try
    match tac g with
    | g' :: gs1, j1 ->
      let gs2, j2 = repeat_tac tac g' in
        gs2 @ gs1,
        fun thms ->
          if List.length thms = List.length gs2 + List.length gs1 then
            let (thms2, thms1) = split thms (List.length gs2) in
              j1 ((j2 thms2) :: thms1)
          else raise JustificationException
    | [], j1 -> [], j1
  with _ ->
    [g], function [th] -> th | _ -> raise JustificationException;;





(*
  Stateful proof environment
  ==========================
*)
let history : goalstate list ref =
  ref [];;

let current_goalstate () =
  match !history with
  | goalstate :: t -> goalstate
  | _ -> raise Not_found;;

let print_goalstate (goals, th : goalstate) =
  if List.length goals = 0 then
    print_string "\n  No subgoals\n\n"
  else
    print_string "\n  Subgoals:\n";
    Array.iteri (fun n -> fun g ->
      print_string ("    " ^ (string_of_int n) ^ ". " ^ print_goal g ^ "\n")
    ) (Array.of_list goals);
    print_string "\n  State:\n";
    print_string ("    " ^ (print_theorem th) ^ "\n\n");;

let p () =
  print_goalstate (current_goalstate ());;

let g (a : formula) =
  history := [
    [Goal ([], a)],
    assume a
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
  | now :: prev :: t ->
    history := prev :: t;
    p()
  | _ ->
    p();;

let top_theorem () : theorem =
  let (_, th) = current_goalstate() in th;;


(*
  Examples
  ========
*)
g (formula "A => B => A");;
e (repeat_tac intro_tac);;
e assumption;;
print_theorem (top_theorem ());;

g (formula "A => (A => B) => B");;
e (repeat_tac intro_tac);;
e (elim_tac (formula "A"));;
e assumption;;
e assumption;;
print_theorem (top_theorem ());;

g (formula "A => (B => C) => (A => B) => C");;
e (repeat_tac intro_tac);;
e (elim_tac (formula "B"));;
e assumption;;
e (elim_tac (formula "A"));;
e assumption;;
e assumption;;
print_theorem (top_theorem ());;
