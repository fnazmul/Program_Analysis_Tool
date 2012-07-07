// ProgramSlice.fs


// Module for Program Slice using Reaching Definitions analysis
module ProgramSlice
open System.Collections.Generic
open BlockDefinition
open BlockGenerator
open MFP
open DebugPrinting

/// Initializing RD circle with {(x,?)|x in FV(Cmd*)}
 
let extemalValue() : Set<(string*int)> = 
    Set.map(fun(var)-> (var,0))(allVariables)

/// Reaching Definitions analysis Transfer Function
let RDtransfer (RDcircle:Set<(string*int)>) (label:int) (currentBlocks:Dictionary<int,Block>)=
    // if any var killed at label
    if printKillGenStat then
        printProgramDetails <- printProgramDetails + " At Label:: " + label.ToString()
    if currentBlocks.[label].KillSet.IsSome then
        let var = currentBlocks.[label].KillSet.Value
         
        // include every other tuple except (var,l) i.e. RDcircle(label)\killRD
        let rdTransfer = 
            seq{for tuple in RDcircle do
                if fst(tuple) <> var then
                    yield tuple}
        // Add (var,label) i.e. genRD
        let currentTuple = Seq.ofList [(currentBlocks.[label].KillSet.Value, label)]
        if printKillGenStat then
            printProgramDetails <- printProgramDetails + "\n     Kill set:: " + var
            printProgramDetails <- printProgramDetails +  "\n     Gen set :: " +  (printFull currentTuple) + "\n\n"
            printKillGenStat<-false    
        let RDtransfer = List.ofSeq(rdTransfer) @ List.ofSeq(currentTuple)
        Set.ofList RDtransfer
    else
        if printKillGenStat then
             printProgramDetails <- printProgramDetails + "\n     kill set:: [] \n     Gen set:: []\n\n"
             printKillGenStat<-false
        RDcircle    

/// Defining MFP call to calculate Reaching Definitions Analysis
let ReachingDefinition(currentBlocks:Dictionary<int,Block>) = 
    MFP Set.empty (forwardFlow(currentBlocks)) programInit (extemalValue()) RDtransfer currentBlocks

/// function to return all the sister guards of a guard block
let getAllGuards (block : Block) : Set<int> =
                match block with
                    | :? Guard as guard -> guard.AllGuards
                    | _ -> Set.empty

/// function to check if a list contains an element
let containsElem number list = List.exists (fun elem -> elem = number) list



/// Program Slicing iterative algorithm.
let programSlice (currentBlocks:Dictionary<int,Block>) (poiLabel:int) =

    // calculate RDcircle and RDbullet
    let (RDcircle:Set<(string*int)>[], RDbullet:Set<(string*int)>[]) = ReachingDefinition(currentBlocks)
    // storing the detail of Program Slice for detail printing purpose
    let mutable PS = Set.empty
    let mutable workList = []
    let mutable allGuards = Set.empty

    //if POI is a guard itself then get all the sister guards including its own guard 
    if (poiLabel < currentBlocks.Count && poiLabel>0) then
        allGuards <- getAllGuards (currentBlocks.[poiLabel])
        // if it is a guard then add all sister guards including its own guard
        if (not(allGuards.IsEmpty)) then
            for g in allGuards do
                if ((g <> 0) && (not (containsElem g workList)) && (not (PS.Contains g))) then
                    workList <- g :: workList
        else // if its not a guard then just add its label
            workList <- poiLabel::[]
       // storing details of the process
        printProgramDetails <- printProgramDetails + " Algorithm:: \n At initial :: \n\t WorkList:: "+ (printFull (Set.ofList workList)) + "\n\t Program Slice:: " + (printFull (PS))
                                + "\n\t Free Var:: ...."+ "\n\t RDCircle:: ...."+ "\n\t All Guards:: ....\n\n"
                                
        // loop until workList is null
        while not(workList.IsEmpty) do
            let currentLabel = workList.Head
            workList <- workList.Tail
            PS <- Set.union PS (Set.empty.Add(currentLabel))
        
            // get the guard of currentLabel
            let mutable guardLabel:int = currentBlocks.[currentLabel].Guard
       
            //if it is guarded under a do of if
            let mutable printAllGuards = Set.empty
            if (guardLabel > 0) then                    
                // get all the sister guards including its own guard
                let mutable allGuards = Set.empty
            
                allGuards <- getAllGuards (currentBlocks.[guardLabel])
            
                // add all sister guards including its own guard
                if (not(allGuards.IsEmpty)) then
                    for g in allGuards do
                        if ((g <> 0) && (not (containsElem g workList)) && (not (PS.Contains g))) then
                            workList <- g :: workList

            // for each var in freeVar(currentLabel)
            let mutable printFreeVar:Set<string> = Set.empty
            for var in currentBlocks.[currentLabel].FreeVar do
                printFreeVar.Add(var) |> ignore
                for tuple in RDcircle.[currentLabel-1] do                
                    if(fst(tuple)=var) then                                        
                        let lprime = snd(tuple)
                        // if not 0 and was not already in PS or workList
                        if (lprime <> 0
                            && (not (containsElem lprime workList))
                            && (not (Set.contains lprime PS))) then
                            //add to workilist
                            workList <- lprime::workList

                       
            printProgramDetails <- printProgramDetails + "\n Label :: "+ currentLabel.ToString() + "\n\t WorkList:: "
                                        + (printFull (Set.ofList workList)) + "\n\t Program Slice:: " + (printFull PS)
                                        + "\n\t Free Var:: "+ (printFull printFreeVar) + "\n\t RDCircle:: "+ (printFull RDcircle.[currentLabel-1])
                                            + "\n\t Current Guard:: "+ guardLabel.ToString() +
                                                "\n\t All Guards:: "+ (printFull allGuards)
        if printDetail then  
            printfn "\n\n Program Slice Details :::::>> \n\n" 
            printBlocks(currentBlocks)
            printfn "\n\n RDcircle And RDbullet::\n %A" circle_bullet            
            printfn "\n\n %A" printProgramDetails
            printProgramDetails <- ""
        printfn "\n\n Sliced Program :: %A" (printFull PS)   
        PS
    else
        printfn "\n Sorry the menthion POI doesn't exist in the Program"
        printDetail <- false
        PS