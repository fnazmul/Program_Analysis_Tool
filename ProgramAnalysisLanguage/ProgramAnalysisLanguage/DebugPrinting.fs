// DebugPrinting.fs


module DebugPrinting


open Lang
open BlockDefinition
open System.Collections.Generic

///function to print the contents of blocks
let printBlocks(analysedProgramBlocks:Dictionary<int,Block>) =

    
    let mutable nextBlocks =List.empty  
    nextBlocks <- [1]

    let printed=ref Set.empty

    while not nextBlocks.IsEmpty do
        let label = nextBlocks.Head
        if Set.contains label (Set(analysedProgramBlocks.Keys)) then
            
            printf "label %d : " label
            
            printf "\n"
            printf "entry set {"
            for entry in analysedProgramBlocks.[label].EntrySet do
                printf "%d " entry
            printf "}"
            
            printf "\n"
            printf "exit set {"
            for exitL in analysedProgramBlocks.[label].ExitSet do
                printf "%d " exitL
            printf "}"

            printf "\n"
            printf "guard number: %d " analysedProgramBlocks.[label].Guard 
            
            printf "\n"
            printf "freeVariables: %A" analysedProgramBlocks.[label].FreeVar

            printf "\n"
            printf "killSet : %A\n" analysedProgramBlocks.[label].KillSet
                
            let mutable temp = List.empty
            for exitLab in analysedProgramBlocks.[label].ExitSet do
                if not (Set.contains exitLab  !printed) then
                    temp <- temp @ [exitLab]
            nextBlocks<-(nextBlocks.Tail) @ temp

            printed:=!printed + Set.filter(fun elem->not(Set.contains elem !printed))(((analysedProgramBlocks.[label]):Block).ExitSet)
        printf "\n"


// function generating string from command given as parameter
let rec commandToString(cmd: Cmd):string=
    match cmd with
    |Asgn(var,exp,lab)-> "[" + var+ ":=" + exp.ToString() + "]" + (lab:int).ToString()
    |Skip(lab)-> "[ skip ]" + (lab:int).ToString()
    |Abort(lab)-> "[ abort ]" + (lab:int).ToString()
    |Read(var, lab)-> "[ read " + var + " ]" + (lab:int).ToString() 
    |Write(exp, lab)-> "[ write " + exp.ToString() + " ]" + (lab:int).ToString()
    |Do(gC)-> "do" + (gcToString gC) + "\nod"
    |If(gC)-> "if " + "\n" + (gcToString gC) + "fi "
    |Seq(cmd1, cmd2) -> (commandToString cmd1) + " ;\n" + (commandToString) cmd2
    |Block(cmd1)-> "{" + (commandToString cmd1) + "}"

and gcToString (gc: GuardedCmd): string=
    match gc with
    |SingleGuard(exp, glab, cmd)-> "[ " + exp.ToString() + " ]" + (glab.value).ToString() + "\n" + (commandToString cmd)
    |ComplexGuard(gc1, gc2)-> "\n"+ (gcToString gc1) + "\n[]" + (gcToString gc2)

let programToString (prg: Program) =
    match prg with
    |Program(name, cmd)-> "module : " + name + "\n" + commandToString(cmd) + "\n"



/// Function printing a single block into a string
let blockToString (currentBlocks:Dictionary<int,Block>)(label:int)=
    
    match (currentBlocks.[label]):Block with
    | :? Skip-> "[skip]" + (label.ToString())
    | :? Abort-> "[abort]" + (label.ToString())
    | :? Read as read when read.KillSet.IsSome-> "[read " + read.KillSet.Value + "]" + (label.ToString())
    | :? Write as write-> "[write " + (write.WriteExpr.ToString()) + "]" + (label.ToString())
    | :? Assignment as assign when assign.KillSet.IsSome-> "[ " + (assign.KillSet.Value) + ":=" + (assign.AssignExpr.ToString())+ "]" + (label.ToString())
    | :? Guard as guard-> ("[" + (guard.GuardCon.ToString()) + "]" + (label.ToString()))
    | _ -> ""

let rec allBlocksToString (cmd:Cmd) (currentBlocks:Dictionary<int,Block>) =

    match cmd with
    | Skip (label) -> "\n" + (blockToString (currentBlocks) (label))
    | Abort(label) ->  "\n" + (blockToString (currentBlocks) (label))
    | Read(var,label) ->  "\n" + (blockToString (currentBlocks) (label))
    | Write(exp,label) ->  "\n" + (blockToString (currentBlocks) (label))
    | Asgn(var,exp,label) ->  "\n" + (blockToString (currentBlocks) (label))
    | Seq(cmd1,cmd2)->  "\n" + ((allBlocksToString (cmd1) (currentBlocks) ) + " ;" + (allBlocksToString (cmd2) (currentBlocks)))
    | Block(cmd) -> "\n" + ( "{\n " + (allBlocksToString (cmd) (currentBlocks) ) +  "\n }")
    | If(gc) ->  "\n" + ("If " + (GCToString gc currentBlocks) + " fi")
    | Do(gc) ->  "\n" + ("Do " + (GCToString gc currentBlocks)+ " od")

and GCToString (gc:GuardedCmd) (currentBlocks:Dictionary<int,Block>) =
    match gc with
    |SingleGuard(exp,label,cmd)-> 
        "[" + (exp.ToString()) + "]" + ((label.value).ToString()) +  "->\n" +  (allBlocksToString (cmd) (currentBlocks))
    |ComplexGuard(gc1,gc2)-> 
         (GCToString (gc1) (currentBlocks) )+   "\n[]" + (GCToString (gc2) (currentBlocks))