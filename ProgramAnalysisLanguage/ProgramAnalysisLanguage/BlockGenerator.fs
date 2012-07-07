// BlockGenerator.fs

module BlockGenerator
open System
open System.IO
open System.Collections.Generic
open Lang
open BlockDefinition
open DebugPrinting

/// holds the program blocks and corresponding start label
let blocks = new Dictionary<int,Block>()

/// list of guards the command is nested under
let mutable underGuards:int list = [0]
/// scope entered
let mutable scope:int list = [0]

let mutable programFinal:Set<int> = Set.empty
let mutable programInit:Set<int> = Set.empty
let mutable allVariables:Set<string> = Set.empty 

/// function to get a clone of blocks
let CloneBlocks(currentBlocks:Dictionary<int,Block>) =
    let clonedBlocks = new Dictionary<int,Block>()
    for key in currentBlocks.Keys do
        clonedBlocks.[key] <- currentBlocks.[key].Clone()
    clonedBlocks

/// type of exception thrown if parse errror
exception ParseError of string

/// function for parsing the program
let parseFormString (guardProg:string) =
    let lexbuf = Lexing.LexBuffer<byte>.FromBytes (System.Text.Encoding.ASCII.GetBytes(guardProg))
    try
        LangParser.start LangLexer.tokenize lexbuf
    with ex ->
        raise (ParseError("Parse Error. Incorrect syntax"))

/// function for parsing file   
let parseFromFile inputFilePath =
    use stream = System.IO.File.OpenRead(inputFilePath)
    use reader = new System.IO.BinaryReader(stream)
    let lexbuf = Lexing.LexBuffer<byte>.FromBinaryReader reader
    LangParser.start LangLexer.tokenize lexbuf

/// function extracting information from Asssign statement and generating block
let generateAssignBlock (var:string) (exp:Expr) (currentLabel:Lab) (previousExitLabel:Set<int>) =
    let assignBlock = 
        new Assignment(previousExitLabel,exp.FreeVariables,Some(var), exp, underGuards.Head, List.head scope)
    blocks.[currentLabel] <- assignBlock

    allVariables <- allVariables.Add(var) + Set.ofSeq(exp.FreeVariables);
    
    // returning current label of the assignment
    Set[currentLabel]

/// function extracting information from skip statement and generating block
let generateSkipBlock (currentLabel:Lab) (previousExitLabel:Set<int>) =
     let skipBlock = new Skip(previousExitLabel,underGuards.Head, List.head scope)
     blocks.[currentLabel] <- skipBlock
     // returning current label of the skip
     Set[currentLabel]


/// function extracting information from abort statement and generating block
let generateAbortBlock (currentLabel:Lab) (previousExitLabel:Set<int>) =
     let abortBlock = new Abort(previousExitLabel,underGuards.Head, List.head scope)
     blocks.[currentLabel] <- abortBlock
     // returning empty set
     Set.empty 
     

/// function extracting information from read statement and generating block
let generateReadBlock (var:string) (currentLabel:Lab) (previousExitLabel:Set<int>) =
    let readBlock = 
        new Read(previousExitLabel, Some(var), underGuards.Head, List.head scope)
    blocks.[currentLabel] <- readBlock

    allVariables <- allVariables.Add(var);

    // returning current label of the Read
    Set[currentLabel]

/// Function extracting information from write statement and generating block
let generateWriteBlock (exp:Expr) (currentLabel:Lab) (previousExitLabel:Set<int>) =
    //let currentLabel = label//labels.nextLabel()
    let writeBlock = 
        new Write(previousExitLabel, exp.FreeVariables, exp, underGuards.Head, List.head scope)
    blocks.[currentLabel] <- writeBlock

    allVariables <- allVariables + Set.ofSeq(exp.FreeVariables);

    // returning current label of the write
    Set[currentLabel]

/// function extracting information from sequence of commands
let rec analyzeSequence (cmd1:Cmd) (cmd2:Cmd) (previousExitLabel:Set<int>) =
    let exitCmd1 = analyzeCommand cmd1 previousExitLabel
    let exitCmd2 = analyzeCommand cmd2 exitCmd1
    exitCmd2

/// function extracting information from  single GC command
and analyzeSingleGC (exp:Expr) (cmd:Cmd) (currentLabel:Lab) (allGuards:Set<int>) (previousExitLabel:Set<int>) =
    let guardBlock = 
        new Guard(previousExitLabel, exp.FreeVariables,exp,allGuards, underGuards.Head, List.head scope)
    blocks.[currentLabel]<-guardBlock

    allVariables <- allVariables + Set.ofSeq(exp.FreeVariables);

    // adding the label of the current guard to underGuard
    underGuards <- currentLabel :: underGuards
    let tempSet: Set<int> = Set.empty.Add(currentLabel)
    let exitSet = 
        analyzeCommand cmd tempSet
    //removing the current guard from underGuard
    underGuards <- underGuards.Tail
    exitSet

/// function extracting information from complex GC command
and analyzeComplexGC (gc1:GuardedCmd) (gc2:GuardedCmd) (allGuards:Set<int>) (previousExitLabel:Set<int>) =
    let exitSet1 =analyzeGC gc1 allGuards previousExitLabel
    let exitSet2 =analyzeGC gc2 allGuards previousExitLabel
    exitSet1 + exitSet2

/// function extracting information from GC command
and analyzeGC (gc:GuardedCmd) (allGuards:Set<int>) (previousExitLabel:Set<int>) =
    match gc with
    |SingleGuard(exp,label,cmd)-> 
        analyzeSingleGC exp cmd label.value allGuards previousExitLabel
    |ComplexGuard(gc1,gc2)-> 
        analyzeComplexGC gc1 gc2 allGuards previousExitLabel
        
/// function extracting information from Do command
and analyzeDO (gc:GuardedCmd) (previousExitLabel:Set<int>) =       
    let exitGC = analyzeGC gc gc.allGuards previousExitLabel
    //exit from GC command is appended to the entry of Do
    for i in gc.allGuards do
        blocks.[i].EntrySet <- blocks.[i].EntrySet + exitGC
    gc.allGuards

/// function extracting information from block of command
and analyzeBlockCommand (cmd:Cmd) (previousExitLabel:Set<int>) =
    analyzeCommand cmd previousExitLabel
    
/// function to find out the type of the command
and analyzeCommand (cmd:Cmd) (previousExitLabel:Set<int>) =
    match cmd with
    | Skip (label) -> generateSkipBlock label previousExitLabel
    | Abort(label) -> generateAbortBlock label previousExitLabel
    | Read(var,label) -> generateReadBlock var label previousExitLabel
    | Write(exp,label) -> generateWriteBlock exp label previousExitLabel
    | Asgn(var,exp,label) -> generateAssignBlock var exp label previousExitLabel
    | Seq(cmd1,cmd2)-> analyzeSequence cmd1 cmd2 previousExitLabel
    | Block(cmd) -> analyzeCommand cmd previousExitLabel
    | If(gc) -> analyzeGC gc gc.allGuards previousExitLabel
    | Do(gc) -> analyzeDO gc previousExitLabel

/// function to generate exit set
let generateExitSet() =
    for label in blocks.Keys do
        for entryLabel in blocks.[label].EntrySet do
            blocks.[entryLabel].ExitSet <- blocks.[entryLabel].ExitSet.Add(label)

/// function to generate forward flow sequence of int*int
let forwardFlow(currentBlocks:Dictionary<int,Block>)=
    seq<(int*int)>{ for label in currentBlocks.Keys do
                        for finalLabel in currentBlocks.[label].ExitSet do
                            //printfn "forwardFlow %A" (label, finalLabel)
                            yield(label,finalLabel)} |> List.ofSeq |> List.rev |> Seq.ofList

/// function to generate reverse flow sequence of int*int
let reverseFlow(currentBlocks:Dictionary<int,Block>)=
    seq<(int*int)>{ for label in currentBlocks.Keys do
                        for initLabel in currentBlocks.[label].EntrySet do
                            //printfn "reverse flow %A" (label,initLabel)
                            yield(label,initLabel)}


/// functiong to parse the program and generate blocks by calling analyzeCommand
let generateProgramBlocks (program:Program):Cmd =

    // parsing input file using generated parser
    printfn "\nInput program:\n"    
    printfn "%s" (programToString(program))
    let command (prg: Program) =
        match prg with
        |Program(name, cmd)-> cmd
    
    let (programCmd:Cmd) = command(program)
    
    programFinal  <- analyzeCommand programCmd Set.empty
    programInit <- blocks.[1].EntrySet
    generateExitSet ()
    (programCmd)
    
/// function for clearing the data structures
let clearDataHandlers()=
   blocks.Clear()
   underGuards <- [0]
   scope <-[0]