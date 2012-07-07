// MFP.fs

module MFP
open System
open BlockDefinition
//open BlockGenerator
open System.Collections.Generic
open System.Diagnostics

// for exectution time
let sw = new Stopwatch()
// for printing purposes
/// string to store the details of program execution for printing purpose  
let mutable printProgramDetails:string= ""
/// fun to print all the set contents    
let printFull param:string = 
    let mutable result = "["
    for elem in param do
        result <- result + " " + elem.ToString()
    result <- result + " ]"
    result
let mutable circle_bullet=""
let mutable printDetail:bool = false
let mutable printKillGenStat:bool = false

/// MFP algorithm for solving data flow equations
// L : complete lattice 
// F - flow(Cmd*) or flowR(Cmd*)
// E - {init(Cmd*)}/final(Cmd*)
// i - initial or final analysis information
// f - transfer function associated with B[l] in currentBlocks(Cmd*)
// currentBlocks - map of blocks created for the program to be analysed



let MFP (L:Set<int>) (F:seq<(int*int)>) (E:Set<int>) (i:Set<'a>) (f:Set<'a>->int->Dictionary<int,Block>->Set<'a>)(currentBlocks:Dictionary<int,Block>)=
    sw.Start()
    let mutable workList = List.empty
    for tuple in F do
        workList <- tuple::workList
       
    let Analysis:Set<'a>[] = [|for label in currentBlocks.Keys -> Set.empty|]// to change 
    for label in currentBlocks.Keys do
        if (E.Contains label) then
            Analysis.[label-1] <- i
    while(workList.Length > 0) do
        let (l,lprime) = workList.Head
        workList<-(workList.Tail)
        let mutable fAnalysis = Set.empty       
        fAnalysis <- f (Analysis.[l-1]) l currentBlocks
        if (not (fAnalysis.IsSubsetOf(Analysis.[lprime-1]) )) then
            Analysis.[lprime-1] <- Set.union Analysis.[lprime-1] fAnalysis
            let flowlPrime =
                 seq<(int*int)>{for tuple in F do
                                    if(fst(tuple) = lprime) then
                                        yield tuple}
            workList<-((List.ofSeq flowlPrime) @ workList)
    let mutable MFPcircle:Set<'a>[] = [| for l in currentBlocks.Keys->Set.empty|]
    let mutable MFPbullet:Set<'a>[] = [| for l in currentBlocks.Keys->Set.empty|]
    for label in currentBlocks.Keys do
        printKillGenStat <- true;
        MFPcircle.[label-1]<-Analysis.[label-1]
        MFPbullet.[label-1]<-f (Analysis.[label-1]) label currentBlocks
        circle_bullet <- circle_bullet + "\n\n Label " + label.ToString() + "\n Circle::: " + (printFull MFPcircle.[label-1])
        circle_bullet <- circle_bullet + "\n Bullet::: " + (printFull MFPbullet.[label-1])
    sw.Stop()
    printfn "Elapsed time %A" (String.Format("Minutes :{0} Seconds :{1} Mili seconds :{2}", sw.Elapsed.Minutes, sw.Elapsed.Seconds, sw.Elapsed.TotalMilliseconds))
    sw.Reset()
    (MFPcircle, MFPbullet)