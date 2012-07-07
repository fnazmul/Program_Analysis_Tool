// Lang.fs

module Lang

open System

type Var = string
type Int = int
type Lab = int

type Program = 
    | Program of string * Cmd

and Cmd =
    | Skip of Lab
    | Abort of Lab
    | Read of Var * Lab
    | Write of Expr * Lab
    | Asgn of Var * Expr * Lab
    | Seq of Cmd * Cmd
    | Block of Cmd
    | If of GuardedCmd
    | Do of GuardedCmd

and GuardedCmd =
    | SingleGuard of Expr * GuardLab * Cmd // GuardLab was added to make the labelling in sequence
    | ComplexGuard of GuardedCmd * GuardedCmd 
    // member generating all the sister guards including its own
     member this.allGuards=        
         let rec findGuards gc : Set<int>=
             match gc with 
             |SingleGuard (expr,lab,cmd) -> Set.empty.Add(lab.value)
             |ComplexGuard(gc1,gc2)-> findGuards gc1 + findGuards gc2
         findGuards this

// to make the labels in sequence
and GuardLab =
    | GuardLabel of int
    // member holding the int value
    member this.value =
        let findValue gL:int =
             match gL with
             |GuardLabel(lab) -> lab
        findValue this
         

and Expr =
    | True
    | False
    | Var of string
    | Int of int
    | Add of Expr * Expr
    | Sub of Expr * Expr
    | Mul of Expr * Expr
    | Div of Expr * Expr
    | Or of Expr * Expr
    | And of Expr * Expr
    | Not of Expr
    | Minus of Expr
    | Gtn of Expr * Expr
    | Ltn of Expr * Expr    
    | Eq of Expr * Expr
    | Neq of Expr * Expr
    | Geq of Expr * Expr
    | Leq of Expr * Expr 

    // member holding the free variables in the expression
    member this.FreeVariables =
        let rec getFreeVariables exp =
            match exp with
            | True -> Set.empty
            | False -> Set.empty
            | Var(x) -> Set[x]
            | Int(c) -> Set.empty
            | Add(exp1,exp2) -> getFreeVariables exp1 +    getFreeVariables exp2
            | Sub(exp1,exp2) -> getFreeVariables exp1 +    getFreeVariables exp2
            | Mul(exp1,exp2) -> getFreeVariables exp1 +    getFreeVariables exp2
            | Div(exp1,exp2) -> getFreeVariables exp1 +    getFreeVariables exp2
            | Or(exp1,exp2) -> getFreeVariables exp1 +    getFreeVariables exp2
            | And(exp1,exp2) -> getFreeVariables exp1 +    getFreeVariables exp2
            | Not(exp1) -> getFreeVariables exp1    
            | Minus(exp1) -> getFreeVariables exp1
            | Gtn(exp1,exp2) -> getFreeVariables exp1+ getFreeVariables exp2
            | Ltn(exp1,exp2) -> getFreeVariables exp1    + getFreeVariables exp2
            | Eq(exp1,exp2) -> getFreeVariables exp1    + getFreeVariables exp2
            | Neq(exp1,exp2) -> getFreeVariables exp1    + getFreeVariables exp2
            | Geq(exp1,exp2) -> getFreeVariables exp1    + getFreeVariables exp2
            | Leq(exp1,exp2) -> getFreeVariables exp1    + getFreeVariables exp2
        getFreeVariables this

    // Override funtion for string representation of expression
    override this.ToString() =
        let rec exprToString exp =
            match exp with
            | True -> "TRUE"
            | False -> "FALSE"
            | Var(x) -> string(x)
            | Int(c) -> string(c) 
            | Add(exp1,exp2) -> exprToString exp1 + "+" + exprToString exp2
            | Mul(exp1,exp2) -> exprToString exp1 + "*" + exprToString exp2
            | Div(exp1,exp2) -> exprToString exp1 + "/" + exprToString exp2
            | Sub(exp1,exp2) -> exprToString exp1 + "-" + exprToString exp2
            | Or(exp1,exp2) -> exprToString exp1 + "|" + exprToString exp2
            | And(exp1,exp2) -> exprToString exp1 + "&" + exprToString exp2
            | Not(exp1) -> "!" + exprToString exp1 
            | Minus(exp1) -> "-" + exprToString exp1
            | Gtn(exp1,exp2) -> exprToString exp1 + ">" + exprToString exp2
            | Ltn(exp1,exp2) ->exprToString exp1 + "<" + exprToString exp2
            | Eq(exp1,exp2) -> exprToString exp1 + "=" + exprToString exp2
            | Neq(exp1,exp2) -> exprToString exp1 + "!=" + exprToString exp2
            | Geq(exp1,exp2) -> exprToString exp1 + ">=" + exprToString exp2
            | Leq(exp1,exp2) -> exprToString exp1 + "<=" + exprToString exp2
        exprToString this