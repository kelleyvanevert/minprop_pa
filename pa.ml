
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

(* Compose functions *)
let ($) f g x = f (g x);;

(* Find the first element of a list that satisfies a certain criterion *)
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
  exception SentException;;

  (* A sentinel to separate assumptions and conclusion from each other
      in the formula encoding of a goal. *)
  let sent : formula = Imp (Var 24, Var 24);;

  (* A proof of "|- sent". *)
  let sent_truth : theorem =
    intro_rule (Var 24) (assume (Var 24));;

  (* Encodes a goal into a formula, using the sentinal to separate the parts *)
  let encode_goal (Goal (assumptions, conclusion) : goal) : formula =
    List.fold_right (fun a f -> Imp (a, Imp (sent, f))) assumptions conclusion;;
*)






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

(* Encodes a goal "a1, .., aN ?- b" into
    a formula "a1 => .. => aN => b" *)
let encode_goal (Goal (gamma, b) : goal) : formula =
  List.fold_right (fun a f -> Imp (a, f)) gamma b;;

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
  match th with
  | Provable (current_goal_assumption :: _, _) ->
    begin match goals with
    | g :: gs1 ->
      let (gs2, j) = tac g in
        gs2 @ gs1,
        elim_rule
          (intro_rule current_goal_assumption th)
          (j (List.map (assume $ encode_goal) gs2))
    | [] -> raise (TacticException "There must be an open goal")
    end
  | _ -> raise (TacticException "There must be an open goal")
;;

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
      [Goal (a::gamma, b)],
      fun thms ->
        match find (fun th -> th |- b) thms with
        | Some th -> intro_rule a th
        | _ -> raise JustificationException;;

let elim_tac (a : formula) (Goal (gamma, b) : goal) =
    [Goal (gamma, Imp (a,b)); Goal (gamma, a)],
    function
      | [th1; th2] when th1 |- Imp (a,b) && th2 |- a ->
        elim_rule th1 th2
      | _ -> raise JustificationException;;


(*
  (* Some tacticals *)

  let try_tac (tac : tactic) (g : goal) : goalstate =
    try
      tac g
    with (TacticException _) ->
      [g],
      function
        | [th] -> th
        | _ -> raise JustificationException;;

  let rec iterate_until_exception (f : 'a -> 'a) (x: 'a) : 'a =
    try iterate_until_exception f (f x)
    with _ -> x;;


  let repeat_tac (tac : tactic) (g : goal) : goalstate =
    iterate_until_exception (fun (s : goalstate) -> by tac s) (tac g);;
*)


(*
  Parsing and pretty printing
  ===========================
  (Really quite dirty, but I couldn't get my head around camlp5 just yet..)
*)
let rec print_formula : formula -> string = function
  | Var n -> Char.escaped (Char.chr (n + 65))
  | Imp (a,b) -> "(" ^ (print_formula a) ^ " => " ^ (print_formula b) ^ ")";;

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
  | [] -> (match stack with
    | LParen :: _ -> raise (ShuntingException ("left paren over", output, stack, tokens))
    | RParen :: _ -> raise (ShuntingException ("right paren over", output, stack, tokens))
    | y :: ys -> shunting (y :: output) ys []
    | [] -> output)
  | x :: rest -> match x with
    | TVar n -> shunting (TVar n :: output) stack rest
    | Arrow -> shunting output (Arrow :: stack) rest
    | LParen -> shunting output (LParen :: stack) rest
    | RParen -> match stack with
      | [] -> raise (ShuntingException ("too much right parens", output, stack, tokens))
      | LParen :: stack' -> shunting output stack' rest
      | t :: stack' -> shunting (t :: output) stack' tokens;;

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
*)