type ide = string;;

(* Possible permissions*)

type perm = Read | Write | Open | Send;;

(* Label to identify if a variable or a function is public or private
   If it is private it cannot be executed by mobile code otherwise if it public then it can be executed by mobile code*)
type label = Public | Private;;

(* Possible expressions*)
type expr = 
  | Eint of int
  | Ebool of bool
  | Den of ide
  | Binop of ide * expr * expr
  | Exec of expr
  | LetPu of ide * expr * expr
  | LetPr of ide * expr * expr
  | If of expr * expr * expr
  | Fun of ide * expr * perm list * label
  | Call of expr * expr
  | ReadData of expr
  | WriteData of expr
  | OpenFile of expr
  | SendData of expr
;;

(* type of the environment with generic values
   label is private or public*)
type 'v t = (string * 'v * label) list

(*The closure definition has been extended with a list of permissions and a label
   which tells me if the function can be executed by mobile code or not
    The label is like the one defined for the variables so it can be Public or Private*)
type value = 
  | Int of int
  | Bool of bool
  | Closure of (ide * expr * perm list * label * value t);;

  (*This stack is used to store the set of permissions of the functions
     Each function can have a list of permissions
     The stack store all the active functions with their permissions*)
type permStack = (perm list) list;;
let emptyenv = [];;


let rec lookup (env : 'v t) x =
  match env with
  | []-> failwith (x ^ " not found")
  | (y,v,_) :: r -> if x = y then v
    else lookup r x;;

(* This function is used to retrieve the label associated to a specific variable*)
let rec lookup_label (env : 'v t) x =
  match env with
  | [] -> Public
  | (y,_,l) :: r -> if x = y then l
  else lookup_label r x;;

let bind (env : 'v t) (x,v,l) = (x,v,l) :: env;;

(*This function check if the element x belongs to the list lst*)
let rec check_list lst  x = 
  match lst with
  | [] -> false
  | h :: t -> if x = h then true else check_list t x;;


(*This function is used to check the permissions of all active functions stored inside the permission stack  *)
let rec check_perm (p_stack : permStack) (p : perm) (cond : bool) : bool =
  match p_stack with
  | [] -> cond
  | h :: t -> let r =  check_list h p in
    if (r) then check_perm t p r else
      false;;


(*This function check the expression e and show its label
   In this homework i assigned the labels only to variables and to functions so in
   the statements like LetPu, LetPr or in primitives like Read,Send,Write,Open i check
   all the expressions inside of them and look if there are functions or variables*)
let rec show_label (e : expr) (env : 'v t)= 
  match e with
  | Eint _ -> Public
  | Ebool _ -> Public
  | Den(x) -> lookup_label env x
  | Fun(_,_,_,lab) -> lab
  | LetPr(_,_,_) -> Private
  | LetPu(_,e1,e2) -> let lab1 = show_label e1 env in 
    let lab2 = show_label e2 env in
    if (lab1 = Public && lab2 = Public) then Public
    else Private
  | Binop(_,e1,e2) -> let lab1 = show_label e1 env in 
    let lab2 = show_label e2 env in 
    if(lab1 = Public && lab2 = Public) then Public
    else Private  
  | Call(f,arg) -> let lab1 = show_label f env in
    let lab2 = show_label arg env in 
    if (lab1 = Public && lab2 = Public) then Public
    else Private
  | ReadData(e1) -> let lab1 = show_label e1 env in
    if (lab1 = Public) then Public
    else Private
  | WriteData(e1) -> let lab1 = show_label e1 env in
    if (lab1 = Public) then Public
    else Private
  | SendData(e1) -> let lab1 = show_label e1 env in
    if (lab1 = Public) then Public
    else Private
  | OpenFile(e1) -> let lab1 = show_label e1 env in
    if (lab1 = Public) then Public
    else Private
  | _ -> failwith ("A variable or a function is required");;
    


(*The interpreter has been extended with the type label
   Let primitive has been divided into two different Let: LetPr and LetPu
   LetPr assign a value to a variable with the label Private while LetPu assign the label Public
   Exec is a primitive which call the function show_label and check all the labels of the possible expressions
   if all the expressions have the label Public then the mobile code can be evaluated and executed
    otherwise if one of the expressions has label Private then the program stops its executionn *)
let rec eval e env (p_stack : permStack) : value =
  begin
    match e with 
    | Eint(i) -> Int(i)
    | Ebool(b) -> Bool(b)
    | Den(x) -> lookup env x
    | LetPu(s,e1,e2) ->
      let let_value = eval e1 env p_stack in 
      let new_env = bind env (s,let_value,Public) in
      eval e2 new_env p_stack
    | LetPr(s,e1,e2) ->
      let let_value = eval e1 env p_stack in 
      let new_env = bind env (s,let_value,Private) in 
      eval e2 new_env p_stack
    | Binop(ope,e1,e2) ->
      let v1 = eval e1 env p_stack in 
      let v2 = eval e2 env p_stack in 
      begin
        match (ope,v1,v2) with
        | ("+", Int i1, Int i2) -> (Int (i1 + i2))
        | ("*", Int i1, Int i2) -> (Int (i1 * i2))
        | ("-", Int i1, Int i2) -> (Int (i1 - i2))
        | ("=", Int i1, Int i2) -> (Bool (i1 == i2))
        | (">", Int i1, Int i2) -> (Bool (i1 > i2))
        | ("<", Int i1, Int i2) -> (Bool (i1 < i2))
        | _, _, _ -> failwith "Unexpected primitive"
      end
      | If(e1,e2,e3)->
        begin
          match eval e1 env p_stack with
          | Bool(true) -> eval e2 env p_stack
          | Bool(false) -> eval e3 env p_stack
          | _ -> failwith "Unexpected condition"
        end
      | Fun(param,body,perms,lab) -> Closure(param,body,perms,lab,env)
      | Call(f,arg) ->
        begin
          let value_f = eval f env p_stack in 
          let value_arg = eval arg env p_stack in 
          match value_f with
          | Closure(param,body,f_perms,lab,closure_env) ->
            let new_p_stack = f_perms :: p_stack in 
            let new_env = bind closure_env (param,value_arg,lab) in 
            eval body new_env new_p_stack
          | _ -> failwith "A function is required on the Call"
          end
      | Exec(e1) ->
        begin
          let lab = show_label e1 env in
          if (lab = Public) then eval e1 env p_stack 
          else failwith "Mobile code is trying to execute private values"
        end
      | ReadData _ -> let condition = check_perm p_stack Read false in
        begin
          match condition with
          | true -> print_endline "Data read"; Bool(true)
          | false -> failwith "Read failed, no read permission"
        end
      | WriteData (e1) -> let condition = check_perm p_stack Write false in
        begin
          match condition with
          | true -> let data = eval e1 env p_stack in
          begin
            match data with
            | Int(i)-> print_endline ("Data " ^ (string_of_int i) ^ " written"); Bool(true)
            | Bool(b)-> print_endline("Data " ^ (string_of_bool b) ^ " written"); Bool(true)
            | _ -> failwith "Wrong type"
          end
          | false -> failwith "Write failed, no write permission"
        end
      | OpenFile _ -> let condition = check_perm p_stack Open false in
        begin
          match condition with
          | true -> print_endline ("File opened"); Bool(true)
          | false -> failwith "Open failed, no open permission"
        end
      | SendData (e1) -> let condition = check_perm p_stack Send false in 
        begin 
          match condition with
          | true -> let data = eval e1 env p_stack in 
          begin 
            match data with
            | Int(i) -> print_endline ("Data " ^ (string_of_int i) ^ " sent"); Bool(true)
            | Bool(b) -> print_endline ("Data " ^ (string_of_bool b) ^ " sent"); Bool(true)
            | _ -> failwith "Wrong type"
          end
          | false -> failwith "Send failed, no send permission"
        end
  end

(* TEST *)

let sec_env = [];;

let p_stack1 = [];;

let p_stack2 = [[Read;Write];[Read;Open];[Read;Send]];;

let p_stack3 = [[Write];[Open;Write];[Read;Write]];;

let p_stack4 = [[Send;Write];[Send;Read];[Send;Open;Write]];;

let a_test = LetPr("a",Eint(8),Den("a"));;

let b_test = LetPu("b",Eint(9),Den("b"));;

let sumOpe = LetPu("x",Eint(9),Binop("+",Den("x"),Eint(2)));; 

let my_pin = LetPr("pin", Eint(12345),Den("pin"));;

(*This test will fail because it is trying to execute private values*)
let testExecutePr = Exec(LetPr("x",Fun("y",ReadData(Ebool(true)),[Read],Private),Call(Den("x"),a_test)));;

(*This will work because all the values are public*)
let testExecutePu = Exec(LetPu("x",Fun("y",ReadData(Ebool(false)),[Read],Public),Call(Den("x"),b_test)));;

(*Also this one will fail because a_test is private*)
let testExecutePr2 = Exec(LetPu("x",Fun("y",ReadData(Ebool(true)),[Read],Public),Call(Den("x"),a_test)));;

(*This will fail because there is no Send permission in the stack*)
let testExecuteNoPerm = Exec(SendData(b_test));;

(*This will fail because my_pin is private*)
let testExecutePin = Exec(SendData(my_pin));;

(*All these test will work because they are not mobile code so unless there is fail due to permissions
   all the operations are evaluated and executed*)
let testSendPin = SendData(my_pin);;

let testReadPr = LetPr("x",Fun("y",ReadData(Eint(5)),[Read],Private),Call(Den("x"),Ebool(true)));;

let testReadPu = LetPu("x",Fun("y",ReadData(Eint(5)),[Read],Public),Call(Den("x"),Ebool(true)));;

let testWritePr = LetPr("x",Fun("y",WriteData(Eint(2)),[Write],Private),Call(Den("x"),Eint(2)));;

let testWritePu = LetPu("x",Fun("y",WriteData(Eint(2)),[Write],Public),Call(Den("x"),Eint(2)));;

let testOpenPr = LetPr("x",Fun("y",OpenFile(Eint(5)),[Open],Private),Call(Den("x"),Eint(3)));;

let testOpenPu = LetPu("x",Fun("y",OpenFile(Eint(5)),[Open],Public),Call(Den("x"),Eint(3)));;

let testSendPu = LetPu("x",Fun("y",SendData(Eint(2)),[Send],Public),Call(Den("x"),Eint(4)));;

let testSendPr = LetPr("x",Fun("y",SendData(Eint(2)),[Send],Private),Call(Den("x"),Eint(4)));;


