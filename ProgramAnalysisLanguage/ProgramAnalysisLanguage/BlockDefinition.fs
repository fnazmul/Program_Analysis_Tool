// BlockDefinition.fs

module BlockDefinition

open Lang

/// type for a basic block
type Block(entry_set:int Set, free_var:string Set, kill:string option,guard:int,scopenumber:int)=
    let mutable entrySet = entry_set
    let mutable exitSet:int Set = Set.empty
    let mutable freeVar = free_var
    let mutable killSet = kill
    let mutable scopeNumber = scopenumber
    let mutable guardNo = guard
    member self.EntrySet 
        with get() = entrySet 
        and set(in_set)= entrySet <- in_set
    member self.ExitSet 
        with get() = exitSet 
        and set(out_set) =exitSet <- out_set
    member self.FreeVar 
        with get() =freeVar 
        and set(free_V) = freeVar <- free_V
    member self.KillSet 
        with get() = killSet
        and  set(kill_s) = killSet <- kill_s
    member self.Guard 
        with get() = guardNo 
        and set(gd_no) = guardNo <- gd_no
    member self.ScopeNumber 
        with get() = scopeNumber 
        and set(nsn) = scopeNumber <- nsn
    abstract member Labelling: int -> string
    default self.Labelling (label:int) ="[" + self.ToString() + "]" + string(label)
    abstract member Clone: unit -> Block
    default self.Clone() =
        let tempBlock = new Block(entrySet, Set.empty, None,scopenumber, guard)
        tempBlock.ExitSet <- self.ExitSet
        tempBlock


/// Type for skip block
type Skip(entry_set:int Set,guard:int, scopenumber:int) =
    inherit Block(entry_set, Set.empty,None,guard,scopenumber)
    override self.ToString() = "skip"
    override self.Clone() =
        let tempSkip = new Skip(self.EntrySet,self.Guard,self.ScopeNumber)
        tempSkip.ExitSet <- self.ExitSet
        tempSkip :> Block

/// Type for abort block
type Abort(entry_set:int Set, guard:int,scopenumber:int) =
    inherit Block(entry_set, Set.empty, None,guard,scopenumber)
    override self.ToString() ="abort"
    override self.Clone() =
        let tempAbort = new Abort(self.EntrySet, self.Guard, self.ScopeNumber)
        tempAbort.ExitSet <- self.ExitSet
        tempAbort :> Block

/// Type for read block
type Read(entry_set:int Set, kill:string option, guard:int, scopenumber:int) =
    inherit Block(entry_set, Set.empty, kill, guard, scopenumber)
    override self.ToString() =                
        "read " + self.KillSet.Value
    override self.Clone() =
        let tempRead = new Read(self.EntrySet, self.KillSet,self.ScopeNumber, self.Guard)
        tempRead.ExitSet <- self.ExitSet
        tempRead :> Block


/// Type for write block
type Write(entry_set:int Set, free_var:string Set, expr: Expr, guard:int,scopenumber:int) =
    inherit Block(entry_set, free_var, None, guard, scopenumber)
    let mutable writeExpr = expr
    member self.WriteExpr 
        with get() = writeExpr 
        and set(exp) = writeExpr <- exp
    override self.ToString() = "write " + self.WriteExpr.ToString()
    override self.Clone() =
        let tempWrite = new Write(self.EntrySet, self.FreeVar, self.WriteExpr, self.Guard, self.ScopeNumber)
        tempWrite.ExitSet <- self.ExitSet
        tempWrite :> Block

/// Type for assignment block
type Assignment(entry_set:int Set,free_var:string Set,kill:string option,expr:Expr,guard:int,scopenumber:int) =
    inherit Block(entry_set,free_var,kill,guard, scopenumber)
    let mutable assignExpr = expr
    member self.AssignExpr 
        with get():Expr =assignExpr 
        and set(exp) = assignExpr <- exp
    override self.ToString() =
        self.KillSet.Value + ":=" + (self.AssignExpr.ToString())
    override self.Clone() =
        let tempAssign = new Assignment(self.EntrySet,self.FreeVar, self.KillSet, self.AssignExpr,self.Guard, self.ScopeNumber)
        tempAssign.ExitSet <- self.ExitSet
        tempAssign :> Block


/// Type for guard block
type Guard(entry_set:int Set, free_var:string Set, guard_exp: Expr,all_guards:int Set, guard:int, scopenumber:int) =
    inherit Block(entry_set, free_var, None, guard, scopenumber)
    let mutable guardExp = guard_exp
    let mutable allGuards = all_guards
    member self.AllGuards
        with get() = allGuards
        and set(gSet) = allGuards <- gSet
    member self.GuardCon 
        with get() = guardExp 
        and set(exp) = guardExp <- exp
    override self.ToString() =self.GuardCon.ToString()
    override self.Clone() =
        let tempGuard = new Guard(self.EntrySet, self.FreeVar, self.GuardCon,self.AllGuards, self.Guard, self.ScopeNumber)
        tempGuard.ExitSet <- self.ExitSet
        tempGuard :> Block        