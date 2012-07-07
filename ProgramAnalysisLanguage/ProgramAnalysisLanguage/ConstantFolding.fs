module ConstantFolding

open MFP
open Lang
open BlockDefinition
open BlockGenerator
open System.Collections.Generic

/// Type definition for the State of a variable. 
/// If it is Constant->CONST, Not a constant->TOP or Undefined ->BOTTOM
type State =
    |TOP
    |CONST of int
    |BOTTOM
    static member (+) (x:State, y:State) =
        match (x,y) with
        | (CONST(c1), CONST(c2)) -> CONST(c1+c2)
        | (TOP, _) -> TOP
        | (_, TOP) -> TOP
        | (_, _) -> BOTTOM
    static member (-) (x:State, y:State) =
        match (x,y) with
        | (CONST(c1), CONST(c2)) -> CONST(c1-c2)
        | (TOP, _) -> TOP
        | (_, TOP) -> TOP
        | (_, _) -> BOTTOM
    static member ( * ) (x:State, y:State) =
        match (x,y) with
        | (CONST(c1), CONST(c2)) -> CONST(c1*c2)
        | (TOP, _) -> TOP
        | (_, TOP) -> TOP
        | (_, _) -> BOTTOM
    static member (/) (x:State, y:State) =
        match (x,y) with
        | (CONST(c1), CONST(c2)) -> CONST(c1/c2)
        | (TOP, _) -> TOP
        | (_, TOP) -> TOP
        | (_, _) -> BOTTOM

/// Function to check if a variable is a constant or not
let isConstant (state:State) = 
    match state with
    | CONST(c) -> true
    | _ -> false

/// get the integer value of CONST state.
let valueOfState (state:State) = match state with
                                 | CONST(c) -> c
                                 | _ -> 0

/// Function to perform arithmetic operations on variables of type State. 
/// Returns of the State type of the given expression
let rec findStateOfExpression (currentMap:Map<string,State>) (exp:Expr) =
    match exp with
    | Int(c) -> CONST(c)
    | Var(x) -> currentMap.[x]
    | Add(exp1,exp2) -> (findStateOfExpression currentMap exp1) + (findStateOfExpression currentMap exp2)
    | Sub(exp1,exp2) -> (findStateOfExpression currentMap exp1) - (findStateOfExpression currentMap exp2)
    | Mul(exp1,exp2) -> (findStateOfExpression currentMap exp1) * (findStateOfExpression currentMap exp2)
    | Div(exp1,exp2) -> (findStateOfExpression currentMap exp1) / (findStateOfExpression currentMap exp2)
    | _ -> BOTTOM


/// initial set of variables with their initial state for CP Analysis.
/// initially all variables have the state BOTTOM
let initCP() : Set<(string*State)> = 
    Set.map(fun(var)-> (var,BOTTOM))(allVariables)


/// Function to determine the current State of each variable in the given CPcircle
let mapOfState (currentCP:Set<string*State>) =

    let mutable tempMap:Map<string,State> = Map.empty

    let mutable count = 0
    let mutable state = BOTTOM
    for var in allVariables do
        count <- 0       //state <- BOTTOM
        for tuple in currentCP do
            if var = fst(tuple) then
                count <- count + 1         //if (isConstant (snd(tuple))) then
                state <- (snd(tuple))
        if count = 1  then                //tempMap <- tempMap.Add(var,BOTTOM)        //else if count = 2 then
                tempMap <- tempMap.Add(var, state)
        else
                tempMap <- tempMap.Add(var,TOP)
    tempMap


/// find the constant vaiables in the given cp_bullet
let getMapOfConstants (CPbullet:Map<string,State>) =
    let mapOfConstants = CPbullet |> Map.toList |> Set.ofList |> Set.filter (fun (x,y) -> (isConstant y)) 
    mapOfConstants


/// Transfer function for Constant Propagation Analysis
let CPtransfer (CPcircle:Set<(string*State)>) (label:int) (currentBlocks:Dictionary<int,Block>) :Set<(string*State)> =
    
    let mutable tempMap = mapOfState CPcircle
    let state =
        match currentBlocks.[label] with
        | :? Assignment as assignment -> Some(findStateOfExpression tempMap assignment.AssignExpr)
        | :? Read as read -> Some(TOP)
        | _ -> None
    if state.IsSome then
        let key = currentBlocks.[label].KillSet.Value
        let newstate =    //match tempMap.[key] with //| CONST(c) when tempMap.[key] <> state.Value -> TOP
            //| CONST(c) when tempMap.[key] = state.Value -> tempMap.[key]  //| CONST(c) -> state.Value
            //| _ when tempMap.[key] = TOP -> TOP            //| _ -> 
            state.Value
        tempMap <- tempMap.Add(key,newstate)
    Set.ofList(Map.toList(tempMap))


/// Calculating the Constant Propagation
let ConstantPropagation (currentBlocks:Dictionary<int,Block>) = 
    MFP Set.empty (forwardFlow(currentBlocks)) (Set[1]) (initCP()) CPtransfer currentBlocks


/// Function to substitute the variables with constant in an expression
let rec replaceConstants (exp:Expr) (mapWithConstants:Map<string,State>) =
    match exp with
    | Int(c) -> Int(c)
    | Var(x) when mapWithConstants.ContainsKey(x) -> Int(valueOfState mapWithConstants.[x])
    | Var(x) -> Var(x)
    | Add(exp1,exp2) -> Add((replaceConstants exp1 mapWithConstants),(replaceConstants exp2 mapWithConstants))
    | Sub(exp1,exp2) -> Sub((replaceConstants exp1 mapWithConstants),(replaceConstants exp2 mapWithConstants))
    | Mul(exp1,exp2) -> Mul((replaceConstants exp1 mapWithConstants),(replaceConstants exp2 mapWithConstants))
    | Div(exp1,exp2) -> Div((replaceConstants exp1 mapWithConstants),(replaceConstants exp2 mapWithConstants))
    | And(exp1,exp2) -> And((replaceConstants exp1 mapWithConstants),(replaceConstants exp2 mapWithConstants))
    | Or(exp1,exp2)  -> Or((replaceConstants exp1 mapWithConstants),(replaceConstants exp2 mapWithConstants))
    | Not(exp1)      -> Not(replaceConstants exp1 mapWithConstants) 
    | Minus(exp1)    -> Minus(replaceConstants exp1 mapWithConstants)
    | Gtn(exp1,exp2) -> Gtn((replaceConstants exp1 mapWithConstants),(replaceConstants exp2 mapWithConstants))
    | Ltn(exp1,exp2) -> Ltn((replaceConstants exp1 mapWithConstants),(replaceConstants exp2 mapWithConstants))
    | Eq(exp1,exp2)  -> Eq((replaceConstants exp1 mapWithConstants),(replaceConstants exp2 mapWithConstants))
    | Neq(exp1,exp2) -> Neq((replaceConstants exp1 mapWithConstants),(replaceConstants exp2 mapWithConstants))
    | Geq(exp1,exp2) -> Geq((replaceConstants exp1 mapWithConstants),(replaceConstants exp2 mapWithConstants))
    | Leq(exp1,exp2) -> Leq((replaceConstants exp1 mapWithConstants),(replaceConstants exp2 mapWithConstants))
    | True -> True
    | False -> False
// ConstantFolding.fs


/// Function to evaluate expression
let rec evaluateExpression (exp:Expr) =
    match exp with
    | Var(x) -> Var(x)
    | Int(c) -> Int(c)
    | Add(Int(c1),Int(c2)) -> Int(c1+c2)
    | Add(Var(x),_) | Add(_, Var(x)) -> exp
    | Sub(Int(c1),Int(c2)) -> Int(c1-c2)
    | Sub(Var(x),_) | Sub(_, Var(x)) -> exp
    | Mul(Int(c1),Int(c2)) -> Int(c1*c2)
    | Mul(Var(x),_) | Mul(_, Var(x)) -> exp
    | Div(Int(c1),Int(c2)) -> Int(c1/c2)
    | Div(Var(x),_) | Div(_, Var(x)) -> exp
    | Add(exp1, exp2) -> evaluateExpression (Add(evaluateExpression exp1, evaluateExpression exp2))
    | Sub(exp1, exp2) -> evaluateExpression (Sub( evaluateExpression exp1, evaluateExpression exp2))
    | Mul(exp1, exp2) -> evaluateExpression (Mul( evaluateExpression exp1, evaluateExpression exp2))
    | Div(exp1, exp2) -> evaluateExpression (Div(evaluateExpression exp1, evaluateExpression exp2))
    | Gtn(exp1, exp2) -> (Gtn(evaluateExpression exp1, evaluateExpression exp2))
    | Ltn(exp1, exp2) -> (Ltn(evaluateExpression exp1, evaluateExpression exp2))
    | Geq(exp1, exp2) -> (Geq(evaluateExpression exp1, evaluateExpression exp2))
    | Leq(exp1, exp2) -> (Leq(evaluateExpression exp1, evaluateExpression exp2))
    | Eq(exp1, exp2) -> (Eq(evaluateExpression exp1, evaluateExpression exp2))
    | Neq(exp1, exp2) -> (Neq(evaluateExpression exp1, evaluateExpression exp2))
    | And(exp1, exp2) -> evaluateExpression (And(evaluateExpression exp1, evaluateExpression exp2))
    | Or(exp1, exp2) -> evaluateExpression (Or(evaluateExpression exp1, evaluateExpression exp2))
    | Not(exp1) -> evaluateExpression (Not(evaluateExpression exp1))
    | Minus(exp1) -> evaluateExpression (Minus(evaluateExpression exp1))
    | _ -> evaluateExpression exp

/// Constant folding of Expression
let foldExpression (exp:Expr) (mapWithConstants:Map<string,State>) =
    let exprWithConstant = replaceConstants exp mapWithConstants
   // printfn "\nReplace Constant %A" exprWithConstant
    evaluateExpression exprWithConstant

/// Constant Folding of Assignment
let foldAssignment (assignment:Assignment) (mapWithConstants:Map<string,State>) =
    let foldedExpression = foldExpression assignment.AssignExpr mapWithConstants
    assignment.AssignExpr <- foldedExpression
    assignment.FreeVar <- foldedExpression.FreeVariables

/// Constant Folding of Write statements.
let foldWrite (write:Write) (mapWithConstants:Map<string,State>) =
    let foldedExpression = foldExpression write.WriteExpr mapWithConstants
    write.WriteExpr <- foldedExpression
    write.FreeVar <- foldedExpression.FreeVariables

/// Constant Folding of Guard
let foldGuard (guard:Guard) (mapWithConstants:Map<string,State>) =
    let foldedExpression = foldExpression guard.GuardCon mapWithConstants
    guard.GuardCon <- foldedExpression
    guard.FreeVar <- foldedExpression.FreeVariables

/// function to perform Constant Folding and returns the Folded program
let constantFolding  (currentBlocks:Dictionary<int,Block>):(Dictionary<int,Block>)=

    // Calculate CPcircle and CPbullet
    let (CPcircle:Set<(string*State)>[], CPbullet:Set<(string*State)>[]) = ConstantPropagation(currentBlocks)

    let foldedBlocks = CloneBlocks(currentBlocks) 
    for label in foldedBlocks.Keys do
        let currentCPcircle = CPcircle.[label - 1]
        let setOfConstants = getMapOfConstants (mapOfState currentCPcircle)
        let mapOfConstants = setOfConstants |> Set.toList|> Map.ofList
        match (foldedBlocks.[label]):Block with
            | :? Assignment as assignment -> foldAssignment assignment mapOfConstants
            | :? Guard as guard -> foldGuard guard mapOfConstants
            | :? Write as write -> foldWrite write mapOfConstants
            | _ -> ()
        
        // printing purpose
        printProgramDetails <- printProgramDetails + "\n\n Label: " + label.ToString()
        printProgramDetails <- printProgramDetails + "\n  CPcircle: " + (printFull CPcircle.[label-1])
        printProgramDetails <- printProgramDetails + "\n  CPbullet: " + (printFull CPbullet.[label-1])
        printProgramDetails <- printProgramDetails + "\n  Current Exp: " + (foldedBlocks.[label]).ToString()
        printProgramDetails <- printProgramDetails + "\n  listofConstant " + (printFull setOfConstants)
        printProgramDetails <- printProgramDetails + "\n  Map of Constants: " + (printFull mapOfConstants)
        printProgramDetails <- printProgramDetails + "\n  Folded Exp: " + (foldedBlocks.[label]).ToString()
        
    foldedBlocks    