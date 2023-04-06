/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean

def Cont (κ α : Type _) := (α → κ) → κ

instance : Monad (Cont κ) where
  pure a k := k a
  map g f k := f fun a => k (g a)
  seq f g k := f fun f => g () fun a => k (f a)
  bind f g k := f fun a => g a k

class ForM' (m : Type u → Type v) (ρ : Type w₁) (α : outParam (Type w₂)) (mem : outParam (α → ρ → Prop)) where
  forM': (x : ρ) → ((a : α) → mem a x → m PUnit) → m PUnit

instance [Monad m] : ForM' m (List α) α (· ∈ ·) where
  forM' l body := forIn' l () (fun a h _ => .yield <$> body a h)

namespace Mathlib.Tactic.Do
open Lean.Parser.Term
open Lean Meta Elab Term
open TSyntax.Compat

/-- Return true if we should not lift `(<- ...)` actions nested in the syntax nodes with the given kind. -/
private def liftMethodDelimiter (k : SyntaxNodeKind) : Bool :=
  k == ``Parser.Term.do ||
  k == ``Parser.Term.doSeqIndent ||
  k == ``Parser.Term.doSeqBracketed ||
  k == ``Parser.Term.termReturn ||
  k == ``Parser.Term.termUnless ||
  k == ``Parser.Term.termTry ||
  k == ``Parser.Term.termFor

/-- Given `stx` which is a `letPatDecl`, `letEqnsDecl`, or `letIdDecl`, return true if it has binders. -/
private def letDeclArgHasBinders (letDeclArg : Syntax) : Bool :=
  let k := letDeclArg.getKind
  if k == ``Parser.Term.letPatDecl then
    false
  else if k == ``Parser.Term.letEqnsDecl then
    true
  else if k == ``Parser.Term.letIdDecl then
    -- letIdLhs := ident >> checkWsBefore "expected space before binders" >> many (ppSpace >> letIdBinder)) >> optType
    let binders := letDeclArg[1]
    binders.getNumArgs > 0
  else
    false

/-- Return `true` if the given `letDecl` contains binders. -/
private def letDeclHasBinders (letDecl : Syntax) : Bool :=
  letDeclArgHasBinders letDecl[0]

/-- Return true if we should generate an error message when lifting a method over this kind of syntax. -/
private def liftMethodForbiddenBinder (stx : Syntax) : Bool :=
  let k := stx.getKind
  if k == ``Parser.Term.fun || k == ``Parser.Term.matchAlts ||
     k == ``Parser.Term.doLetRec || k == ``Parser.Term.letrec  then
     -- It is never ok to lift over this kind of binder
    true
  -- The following kinds of `let`-expressions require extra checks to decide whether they contain binders or not
  else if k == ``Parser.Term.let then
    letDeclHasBinders stx[1]
  else if k == ``Parser.Term.doLet then
    letDeclHasBinders stx[2]
  else if k == ``Parser.Term.doLetArrow then
    letDeclArgHasBinders stx[2]
  else
    false

private partial def hasLiftMethod : Syntax → Bool
  | Syntax.node _ k args =>
    if liftMethodDelimiter k then false
    -- NOTE: We don't check for lifts in quotations here, which doesn't break anything but merely makes this rare case a
    -- bit slower
    else if k == ``Parser.Term.liftMethod then true
    else args.any hasLiftMethod
  | _ => false

structure ExtractMonadResult where
  m            : Expr
  returnType   : Expr
  expectedType : Expr

private def mkUnknownMonadResult : MetaM ExtractMonadResult := do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let m ← mkFreshExprMVar (← mkArrow (mkSort (mkLevelSucc u)) (mkSort (mkLevelSucc v)))
  let returnType ← mkFreshExprMVar (mkSort (mkLevelSucc u))
  return { m, returnType, expectedType := mkApp m returnType }

private partial def extractBind (expectedType? : Option Expr) : TermElabM ExtractMonadResult := do
  let some expectedType := expectedType? | mkUnknownMonadResult
  let extractStep? (type : Expr) : MetaM (Option ExtractMonadResult) := do
    let .app m returnType := type | return none
    try
      let bindInstType ← mkAppM ``Bind #[m]
      discard <| Meta.synthInstance bindInstType
      return some { m, returnType, expectedType }
    catch _ =>
      return none
  let rec extract? (type : Expr) : MetaM (Option ExtractMonadResult) := do
    match (← extractStep? type) with
    | some r => return r
    | none =>
      let typeNew ← whnfCore type
      if typeNew != type then
        extract? typeNew
      else
        if typeNew.getAppFn.isMVar then
          mkUnknownMonadResult
        else match (← unfoldDefinition? typeNew) with
          | some typeNew => extract? typeNew
          | none => return none
  match (← extract? expectedType) with
  | some r => return r
  | none   => throwError "invalid `do` notation, expected type is not a monad application{indentExpr expectedType}\nYou can use the `do` notation in pure code by writing `Id.run do` instead of `do`, where `Id` is the identity monad."

namespace Do

local instance : Ord Name := ⟨Name.cmp⟩
deriving instance Ord for Option

/-- Possible non-local exit points from a code block -/
inductive Exit where
  | return
  | break (label : Option Name)
  | continue (label : Option Name)
  deriving Ord

/-- A code block, and the collection of variables updated by it. -/
structure CodeBlock where
  code : Expr
  exits : RBTree Exit compare := {} -- set of exit points used by `code`
  updates : NameSet := {} -- set of variables updated by `code`
  deriving Inhabited

def getLetIdDeclVar (letIdDecl : Syntax) : Ident :=
  letIdDecl[0]

-- support both regular and syntax match
def getPatternVarsEx (pattern : Syntax) : TermElabM (Array Ident) :=
  getPatternVars pattern <|>
  Quotation.getPatternVars pattern

/--
Return the pattern variables occurring in the given patterns.
This method is used in the `match` and `do` notation elaborators
-/
def getPatternsVars (patterns : TSyntaxArray `term) : TermElabM (Array Ident) := do
  let collect : CollectPatternVars.M Unit := do
    for pattern in patterns do
      discard <| CollectPatternVars.collect (← liftMacroM <| expandMacros pattern)
  let (_, s) ← collect.run {}
  return s.vars

def Quotation.getPatternsVars (pats : TSyntaxArray `term) : TermElabM (Array Ident) :=
  pats.foldlM (fun vars pat => do return vars ++ (← getPatternVars pat.raw)) #[]

def getPatternsVarsEx (patterns : TSyntaxArray `term) : TermElabM (Array Ident) :=
  getPatternsVars patterns <|> Quotation.getPatternsVars patterns

def getLetPatDeclVars (letPatDecl : Syntax) : TermElabM (Array Ident) := do
  let pattern := letPatDecl[0]
  getPatternVarsEx pattern

def getLetEqnsDeclVar (letEqnsDecl : Syntax) : Ident :=
  letEqnsDecl[0]

def getLetDeclVars (letDecl : Syntax) : TermElabM (Array Ident) := do
  let arg := letDecl[0]
  if arg.getKind == ``Parser.Term.letIdDecl then
    return #[getLetIdDeclVar arg]
  else if arg.getKind == ``Parser.Term.letPatDecl then
    getLetPatDeclVars arg
  else if arg.getKind == ``Parser.Term.letEqnsDecl then
    return #[getLetEqnsDeclVar arg]
  else
    throwError "unexpected kind of let declaration"

def getHaveIdLhsVar (optIdent : Syntax) : TermElabM Ident :=
  if optIdent.isNone then
    `(this)
  else
    pure optIdent[0]

def getHaveDeclVars (doHave : TSyntax ``haveDecl) : TermElabM (Array Ident) := do
  -- haveDecl := leading_parser haveIdDecl <|> letPatDecl <|> haveEqnsDecl
  let arg := doHave.raw[0]
  if arg.getKind == ``Parser.Term.haveIdDecl then
    -- haveIdDecl := leading_parser atomic (haveIdLhs >> " := ") >> termParser
    -- haveIdLhs := optional (ident >> many (ppSpace >> letIdBinder)) >> optType
    return #[← getHaveIdLhsVar arg[0]]
  else if arg.getKind == ``Parser.Term.letPatDecl then
    getLetPatDeclVars arg
  else if arg.getKind == ``Parser.Term.haveEqnsDecl then
    -- haveEqnsDecl := leading_parser haveIdLhs >> matchAlts
    return #[← getHaveIdLhsVar arg[0]]
  else
    throwError "unexpected kind of have declaration"

def getLetRecDeclsVars (decls : TSyntax ``letRecDecls) : TermElabM (Array Ident) := do
  -- letRecDecls is an array of `(group (optional attributes >> letDecl))`
  let letRecDecls := decls.raw[0].getSepArgs
  let letDecls := letRecDecls.map fun p => p[2]
  let mut allVars := #[]
  for letDecl in letDecls do
    let vars ← getLetDeclVars letDecl
    allVars := allVars ++ vars
  return allVars

structure ExitPoint where
  ty : Expr
  jump : Expr → NameMap FVarId → TermElabM Expr
  deriving Inhabited

structure Context where
  ref         : Syntax
  /-- The monad associated with the do notation. -/
  mStx        : Syntax
  /-- The monad associated with the do notation. -/
  m           : Expr
  /-- The result of the monadic computation performed by the do notation. -/
  returnType  : Expr
  /-- The expected type of the current do block. -/
  expectedType : Expr
  muts        : NameMap FVarId := {}
  exits       : RBMap Exit ExitPoint compare := {}

abbrev M := ReaderT Context TermElabM

private partial def expandLiftMethodAux (inQuot : Bool) (inBinder : Bool) : Syntax → StateT (List (TSyntax `doElem)) M (TSyntax `doElem)
  | stx@(Syntax.node i k args) =>
    if liftMethodDelimiter k then
      return stx
    else if k == ``Parser.Term.liftMethod && !inQuot then withFreshMacroScope do
      if inBinder then
        throwErrorAt stx "cannot lift `(<- ...)` over a binder, this error usually happens when{""
          } you are trying to lift a method nested in a `fun`, `let`, or `match`-alternative,{""
          } and it can often be fixed by adding a missing `do`"
      let term := args[1]!
      let term ← expandLiftMethodAux inQuot inBinder term
      let auxDoElem ← `(doElem| let a ← $term:term)
      modify (auxDoElem::·)
      `(a)
    else do
      let inAntiquot := stx.isAntiquot && !stx.isEscapedAntiquot
      let inBinder   := inBinder || (!inQuot && liftMethodForbiddenBinder stx)
      let args ← args.mapM (expandLiftMethodAux (inQuot && !inAntiquot || stx.isQuot) inBinder)
      return Syntax.node i k args
  | stx => return stx

def expandLiftMethod (doElem : TSyntax `doElem) : M (List (TSyntax `doElem) × TSyntax `doElem) := do
  if !hasLiftMethod doElem then
    return ([], doElem)
  else
    let (doElem, doElemsNewRev) ← (expandLiftMethodAux false false doElem).run []
    return (doElemsNewRev, doElem)

def checkLetArrowRHS (doElem : Syntax) : M Unit := do
  let kind := doElem.getKind
  if kind == ``Parser.Term.doLetArrow ||
     kind == ``Parser.Term.doLet ||
     kind == ``Parser.Term.doLetRec ||
     kind == ``Parser.Term.doHave ||
     kind == ``Parser.Term.doReassign ||
     kind == ``Parser.Term.doReassignArrow then
    throwErrorAt doElem "invalid kind of value `{kind}` in an assignment"

inductive Binder where
  | ident (x : Ident) (ty : Expr)
  | term (e : Term)

inductive Continuation where
  | then (ref : Syntax) (k : M CodeBlock)
  | bind (ref : Syntax) (bi : Binder) (k : M CodeBlock)
  | discard (ref : Syntax) (ty : Expr) (k : NameMap FVarId → TermElabM Expr)
  | pure (ref : Syntax) (ty : Expr) (k : Expr → NameMap FVarId → TermElabM Expr)
  | id (ty : Expr)

def jumpToJP [Pure m] (ctx : Context) (tgt ret : Expr) (vars' : NameMap FVarId) : m Expr :=
  pure <| mkApp tgt ret |> ctx.muts.fold fun e n _ => mkApp e <| .fvar <| vars'.find! n

def Continuation.markUnreachable : Continuation → TermElabM Unit
  | .id _ => return
  | .then ref _ | .bind ref .. | .discard ref .. | .pure ref .. =>
    unless ref.isMissing do
      logWarningAt ref "`do` element is unreachable"

def removeUpdates (vars : Array Ident) (updates : NameSet) : NameSet :=
  vars.foldl (·.erase ·.getId) updates

def withSyntaxBinder (vars : Array Ident) (stx : Ident → TermElabM Syntax) (k : M CodeBlock) : M CodeBlock := do
  let name ← mkFreshUserName `rhs
  let m := (← mkFreshExprMVar none .syntheticOpaque name).mvarId!
  let code ← elabTerm (← stx (mkIdent name)) (← read).returnType
  let res ← m.withContext k
  m.assign res.code
  pure { res with code, updates := removeUpdates vars res.updates }

def Continuation.run (k : Continuation) : M CodeBlock := fun ctx => do
  match k with
  | .then _ k => k ctx
  | .bind _ (.ident x ty) k =>
    withLocalDeclD x.getId ty fun val => do
      let res ← k ctx
      let code := res.code.replaceFVar val (← mkConstWithFreshMVarLevels ``PUnit.unit)
      return { res with code, updates := res.updates.erase x.getId }
  | .bind _ (.term pat) k => do
    withSyntaxBinder (← getPatternVarsEx pat) (fun rhs => `(let $pat := (); ?$rhs)) k ctx
  | .discard _ _ k => return { code := ← k ctx.muts }
  | .pure _ _ k => return { code := ← k (← mkConstWithFreshMVarLevels ``PUnit.unit) ctx.muts }
  | .id _ => return { code := ← mkConstWithFreshMVarLevels ``PUnit.unit }

def Continuation.getType : Continuation → M Expr
  | .then .. => mkConstWithFreshMVarLevels ``PUnit
  | .bind _ (.ident _ ty) _ | .discard _ ty _ | .pure _ ty _ | .id ty => return ty
  | .bind _ (.term _) _ => mkFreshExprMVar none

def Continuation.toFun (k : Continuation) : M CodeBlock := fun ctx => do
  match k with
  | .then _ k =>
    let α ← mkConstWithFreshMVarLevels ``PUnit
    let res ← k ctx
    return { res with code := mkLambda `_ .default α res.code }
  | .bind _ (.ident x ty) k =>
    let mty ← exprToSyntax ty
    withSyntaxBinder #[x] (fun rhs => `(fun $x : $mty => ?$rhs)) k ctx
  | .bind _ (.term pat) k =>
    withSyntaxBinder (← getPatternVarsEx pat) (fun rhs => `(fun $pat => ?$rhs)) k ctx
  | .discard _ ty k => return { code := mkLambda `_ .default ty (← k ctx.muts) }
  | .pure _ ty k =>
    withLocalDeclD (← mkFreshBinderName) ty fun x => do
      return { code := ← mkLambdaFVars #[x] <| ← k x ctx.muts }
  | .id ty => do
    let x ← mkFreshBinderName
    return { code := .lam x ty (.bvar 0) .default }

def Continuation.apply (lhs : CodeBlock) (k : Continuation) : M CodeBlock := fun ctx => do
  if let .id _ := k then
    return lhs
  let rhs ← k.toFun ctx
  return {
    code := ← mkAppOptM ``Bind.bind #[ctx.m, none, none, none, lhs.code, rhs.code]
    updates := lhs.updates.union rhs.updates
    exits := lhs.exits.union rhs.exits
  }

def withDoExpr (val : Syntax) (k : Continuation) : M CodeBlock := fun ctx => do
  let α ← k.getType ctx
  k.apply { code := ← elabTerm val (mkApp ctx.m α) } ctx

def addVars (newVars : Array Ident) (muts : NameMap FVarId) : TermElabM (NameMap FVarId) :=
  newVars.foldlM (init := muts) fun muts var => do
    pure $ muts.insert var.getId (← getLocalDeclFromUserName var.getId).fvarId

def Continuation.map (f : ∀ {α}, (NameMap FVarId → TermElabM α) → (NameMap FVarId → TermElabM α)) :
    Continuation → Continuation
  | .then ref k => .then ref <| fun ctx => do f (fun muts => k { ctx with muts }) ctx.muts
  | .bind ref bi k => .bind ref bi <| fun ctx => do f (fun muts => k { ctx with muts }) ctx.muts
  | .discard ref ty k => .discard ref ty <| f k
  | .pure ref ty k => .pure ref ty <| f ∘ k
  | .id ty => .pure .missing ty fun e => f fun _ => return e

def Continuation.map' (f : ∀ {α}, TermElabM α → TermElabM α) : Continuation → Continuation :=
  .map fun k muts => f <| k muts

def Continuation.withContext (mvarId : MVarId) : Continuation → Continuation :=
  .map' mvarId.withContext

def withNewMutableVars (newVars : Array Ident) (yes := true) : Continuation → Continuation :=
  if yes then .map fun k muts => addVars newVars muts >>= k else id

def withReassign (vars : Array Ident) (origLCtx : LocalContext) (tail : Continuation) : M CodeBlock := do
  let muts := (← read).muts
  for x in vars do
    let v := x.getId
    let some ldecl := origLCtx.findFromUserName? v
      | throwError "unknown local declaration '{v}'"
    unless muts.find? v == some ldecl.fvarId do
      let v := v.simpMacroScopes; throwErrorAt x
        "`{v}` cannot be mutated, only variables declared using `let mut` can be mutated.{"\n"
        }If you did not intend to mutate but define `{v}`, consider using `let {v}` instead"
  let lctx ← getLCtx
  let res ← Continuation.run <| tail.map fun k muts =>
    k <| vars.foldl (init := muts) fun s v =>
      s.insert v.getId (lctx.findFromUserName? v.getId).get!.fvarId
  pure { res with updates := vars.foldl (·.insert ·.getId) res.updates }

def withNewJP (ty : Expr) (k : Expr → Expr → M (CodeBlock × α)) :
    M (CodeBlock × Array Expr × α) := do
  let ctx ← read
  let jpName ← mkFreshUserName `__do_jp
  let jpBodyType ← mkFreshTypeMVar
  let fvars := ctx.muts.fold (fun fvars _ fvarId => fvars.push (.fvar fvarId)) #[]
  let mvarType ← mkArrow ty (← mkForallFVars fvars ctx.returnType)
  withLocalDeclD jpName (← mkArrow ty jpBodyType) fun jp => do
    let mvar ← mkFreshExprMVar mvarType .syntheticOpaque
    let (res, a) ← k mvar jpBodyType
    let fvars' := res.updates.toArray.map (.fvar <| ctx.muts.find! ·)
    jpBodyType.mvarId!.assign <| ← mkForallFVars fvars' ctx.returnType
    withLocalDeclD (← mkFreshUserName `ret) ty fun ret => do
      mvar.mvarId!.assign <| ← mkLambdaFVars (#[ret] ++ fvars) <| mkAppN (mkApp jp ret) fvars'
    pure ({ res with code := ← mkLambdaFVars #[jp] res.code }, fvars', a)

def Continuation.withJP (K : Continuation → M CodeBlock) (k : Continuation) : M CodeBlock :=
  match k with
  | .discard .. | .pure .. | .id _ => K k
  | _ => do
    let ctx ← read
    let (res, fvars', jpBodyType) ← withNewJP ctx.expectedType fun mvar jpBodyType => do
      let res ← K <| .pure .missing ctx.expectedType (jumpToJP ctx mvar)
      Pure.pure (res, jpBodyType)
    let res' ← match k with
    | .discard .. | .pure .. | .id _ => unreachable!
    | .bind _ (Binder.ident xStx ty) k =>
      withLocalDeclD xStx.getId ty fun x => do
        addLocalVarInfo xStx x
        let res' ← k
        let code' ← mkLambdaFVars (#[x] ++ fvars') res'.code
        Pure.pure { res' with code := code', updates := res'.updates.erase xStx.getId }
    | .bind _ (Binder.term pat) k =>
      let vars ← getPatternVarsEx pat
      let name ← mkFreshUserName `rhs
      let m ← mkFreshExprMVar none .syntheticOpaque name
      let code ← elabTerm
        (← `(fun $pat:term => ?$(mkIdent name)))
        (← mkArrow ctx.expectedType jpBodyType)
      let res' ← m.mvarId!.withContext k
      m.mvarId!.assign (← mkLambdaFVars fvars' res'.code)
      Pure.pure { res' with code, updates := removeUpdates vars res'.updates }
    | .then _ k =>
      let res' ← k
      let code' ← mkLambdaFVars fvars' res'.code
      Pure.pure { res' with code := mkForall `x .default ctx.expectedType code' }
    Pure.pure {
      code := mkLetFunAnnotation <| mkApp res.code res'.code
      updates := res.updates.union res'.updates
      exits := res.exits.union res'.exits
    }

def Continuation.withJP'
    (K : (ty : Expr) → (k : Expr → NameMap FVarId → TermElabM Expr) → M CodeBlock)
    (k : Continuation) : M CodeBlock :=
  k.withJP fun
  | .discard _ ty k' => K ty fun _ => k'
  | .pure _ ty k' => K ty k'
  | .id ty => K ty fun e _ => return e
  | _ => unreachable!

def doExit (exit : Exit) (value : Expr) (tail : Continuation) : M CodeBlock := fun ctx => do
  tail.markUnreachable
  let some jp := ctx.exits.find? exit
    | throwError "exit point not found, perhaps you are using `break` outside of a loop?"
  pure { code := ← jp.jump value ctx.muts, exits := RBTree.empty.insert exit }

def doReturn (value : Option Term) (tail : Continuation) : M CodeBlock := fun ctx => do
  tail.markUnreachable
  let value ← ensureHasType ctx.returnType <| ← match value with
    | some e => elabTerm e ctx.returnType
    | none => mkConstWithFreshMVarLevels ``PUnit.unit
  let jp := ctx.exits.find! .return
  pure { code := ← jp.jump value ctx.muts, exits := RBTree.empty.insert .return }

def withMatch
    (gen : Option (TSyntax ``generalizingParam))
    (motive : Option (TSyntax ``motive))
    (discr : Syntax.TSepArray ``matchDiscr ",")
    (patsss : Array (Array (Syntax.TSepArray `term ",")))
    (ks : Array (M CodeBlock)) : M CodeBlock := do
  let mut stxs := #[]
  let mut varss := #[]
  for patss in patsss do
    let name ← mkFreshUserName `rhs
    let m := (← mkFreshExprMVar none .syntheticOpaque name).mvarId!
    let vars :: rest ← patss.toList.mapM (getPatternsVarsEx ·.getElems) | unreachable!
    unless rest.all (vars == ·) do throwError "all patterns must bind the same variables"
    varss := varss.push <| (m, ← getPatternsVarsEx vars)
    stxs := stxs.push <| ← `(?$(mkIdent name))
  let stx ← `(match $[$gen]? $[$motive]? $discr,* with $[| $[$patsss,*]|* => $stxs]*)
  let code ← elabTerm stx (← read).returnType
  let mut updates : NameSet := {}
  let mut exits : RBTree Exit compare := {}
  for (m, vars) in varss, k in ks do
    let res ← m.withContext k
    m.assign res.code
    exits := exits.union res.exits
    updates := updates.union (removeUpdates vars res.updates)
  pure { code, exits, updates }

initialize withDoElemRef : IO.Ref (TSyntax `doElem → Continuation → M CodeBlock) ←
  IO.mkRef fun _ _ => throwError "undefined"

partial def withDoElem (doElem : TSyntax `doElem) (tail : Continuation) : M CodeBlock :=
  withIncRecDepth <| withRef doElem do
    checkMaxHeartbeats "`do`-expander"
    if let some doElem ← liftMacroM <| expandMacro? doElem then
      return (← withDoElem doElem tail)
    if hasLiftMethod doElem then
      let (doElem, doElemsNewRev) ← (expandLiftMethodAux false false doElem).run []
      let mut ref := .missing
      let mut k := withDoElem doElem tail
      for elem in doElemsNewRev do
        k := withDoElem elem (.then ref k)
        ref := elem
      return ← k
    (← withDoElemRef.get) doElem tail

def withDoSeq (doSeq : TSyntax ``doSeq) (x : Continuation) : Continuation :=
  if doSeq.raw.getKind == ``Parser.Term.doSeqBracketed then
    doSeq.raw[1].getArgs.foldr (fun a k => .then a $ withDoElem ⟨a[0]⟩ k) x
  else if doSeq.raw.getKind == ``Parser.Term.doSeqIndent then
    doSeq.raw[0].getArgs.foldr (fun a k => .then a $ withDoElem ⟨a[0]⟩ k) x
  else
    x

def runDoSeq (doSeq : TSyntax ``doSeq) (k : Continuation) : M CodeBlock :=
  (withDoSeq doSeq k).run

def withIfLet (pat discr : Term) (k₁ k₂ : M CodeBlock) : M CodeBlock := do
  withMatch none none #[discr] #[#[#[pat]], #[#[← `(_)]]] #[k₁, k₂]

def withIf (ifTk : Syntax) (cond : TSyntax ``doIfCond) (k₁ k₂ : M CodeBlock) :
    M CodeBlock := withRef ifTk do
  match cond with
  | `(doIfCond| $[$h :]? $cond) =>
    let n₁ ← mkFreshUserName `rhs₁; let m₁ := (← mkFreshExprMVar none .syntheticOpaque n₁).mvarId!
    let n₂ ← mkFreshUserName `rhs₂; let m₂ := (← mkFreshExprMVar none .syntheticOpaque n₂).mvarId!
    let mut vars := #[]
    let stx ← if let some h := h then
      vars := #[h]
      `(if $h : $cond then ?$(mkIdent n₁) else ?$(mkIdent n₂))
    else
      `(if $cond then ?$(mkIdent n₁) else ?$(mkIdent n₂))
    let code ← elabTerm stx (← read).returnType
    let res₁ ← m₁.withContext k₁; m₁.assign res₁.code
    let res₂ ← m₂.withContext k₂; m₂.assign res₂.code
    pure {
      code
      exits := res₁.exits.union res₂.exits
      updates := removeUpdates vars <| res₁.updates.union res₂.updates
    }
  | `(doIfCond| let $pat := $discr) => withIfLet pat discr k₁ k₂
  | `(doIfCond| let $pat ← $discr) =>
    let a ← mkFreshIdent discr
    withDoElem (← `(doElem| let $a ← $discr)) <| .then .missing (withIfLet pat a k₁ k₂)
  | _ => throwUnsupportedSyntax

def withIfChain (ifTk : Syntax) (cond : TSyntax ``doIfCond) (t : TSyntax ``doSeq)
  (elif : List (Syntax × TSyntax ``doIfCond × TSyntax ``doSeq))
  (els : Option (TSyntax ``doSeq)) (tail : Continuation) : M CodeBlock :=
  match elif with
  | [] => withIf ifTk cond (runDoSeq t tail) <| match els with
    | none => tail.run
    | some els => runDoSeq els tail
  | (if₂, cond₂, els₂)::is =>
    withIf ifTk cond (runDoSeq t tail) <| withIfChain if₂ cond₂ els₂ is els tail

def withDoFor (h? : Option Ident) (x xs : Term)
    (body : TSyntax ``doSeq) (tail : Continuation) : M CodeBlock := tail.withJP' fun bTy tail => do
  let ctx ← read
  let unit ← mkConstWithFreshMVarLevels ``PUnit
  let xs ← elabTerm xs none
  let vars ← getPatternVarsEx x
  let (res, fvars', code, m, α, inst) ← withNewJP unit fun cont monadTy => do
    withReader (fun ctx => { ctx with
      exits := ctx.exits
        |>.insert (.continue none) { ty := unit, jump := jumpToJP ctx cont }
        |>.insert (.break none) { ty := bTy, jump := tail }
      expectedType := unit
    }) do
      let αName ← mkFreshUserName `α
      let α ← mkFreshTypeMVar (userName := αName)
      let name ← mkFreshUserName `rhs
      let m := (← mkFreshExprMVar none .syntheticOpaque name).mvarId!
      let (inst, stx) ← match h? with
      | none =>
        let inst ← synthInstance <| ← mkAppM ``ForM #[← mkAppM ``Cont #[monadTy], xs, α]
        pure (inst, ← `(fun $x : ?$(mkIdent αName) => ?$(mkIdent name)))
      | some h =>
        let memName ← mkFreshUserName `mem
        let mem ← mkFreshTypeMVar (userName := memName)
        let inst ← synthInstance <| ← mkAppM ``ForM' #[← mkAppM ``Cont #[monadTy], xs, α, mem]
        pure (inst, ← `(
          fun ($x : ?$(mkIdent αName))
              ($h : $(mkIdent memName) $x $(← exprToSyntax xs)) => ?$(mkIdent name)))
      let code' ← elabTerm stx none
      m.withContext do
        let res ← runDoSeq body <| .pure .missing unit (jumpToJP ctx cont)
        let updates := removeUpdates vars res.updates
        let fvars' := updates.toArray.map (Expr.fvar <| ctx.muts.find! ·)
        pure ({ res with code := ← mkLambdaFVars fvars' res.code, updates }, code', m, α, inst)
  m.assign res.code
  let main ← match h? with
  | none => mkAppOptM ``forM #[none, none, α, inst, none, xs, code]
  | some _ => mkAppOptM ``ForM'.forM' #[none, none, α, none, inst, xs, code]
  let r ← mkLambdaFVars fvars' (← tail (← mkConstWithFreshMVarLevels ``PUnit.unit) ctx.muts)
  pure { res with code := mkAppN (mkApp main (.lam `_ unit r .default)) fvars' }


def withDoParallelFor (start : M CodeBlock → M CodeBlock)
    (args : List (Option Ident × Term × Term))
    (body : TSyntax ``doSeq) (tail : Continuation) : M CodeBlock :=
  match args with
  | [] => panic! "empty for"
  | [(h, x, xs)] => start (withDoFor h x xs body tail)
  | (some h, _, _) :: _ => throwErrorAt h "proofs not supported in this position"
  | (none, y, ys) :: rest => withFreshMacroScope do
    let elem ← `(doElem| let mut s := toStream $ys)
    let body' ← `(doElem| match Stream.next? s with
      | none => break
      | some ($y, s') => s := s'; $body)
    withDoParallelFor (withDoElem elem ∘ .then  .missing ∘ start) rest body' tail

def withDoTryCatch
    (body : Continuation → M CodeBlock)
    (catch_ : TSyntax [``doCatch, ``doCatchMatch])
    (tail : Continuation) : M CodeBlock := do
  let α := (← read).expectedType
  let body ← body (.id α) -- FIXME
  let name ← mkFreshUserName `rhs
  let m := (← mkFreshExprMVar none .syntheticOpaque name).mvarId!
  let εName ← mkFreshUserName `ε
  let ε ← mkFreshTypeMVar (userName := εName)
  let funTy ← mkArrow ε α
  let (knownTy, code, handler) ← match catch_ with
  | `(doCatch| catch $x $[: $ty]? => $handler) =>
    if let some ty := ty then
      ε.mvarId!.assign (← elabType ty)
    let code ← elabTerm (← `(fun $x => ?$(mkIdent name))) funTy
    let handler ← m.withContext do
      runDoSeq handler (.id α)
    let updates := if x.raw.getKind == `ident then
      handler.updates.erase x.getId
    else
      handler.updates
    pure (ty.isSome, code, { handler with updates })
  | `(doCatchMatch| catch $[| $[$patsss,*]|* => $val]*) =>
    withFreshMacroScope do
      let code ← elabTerm (← `(fun e => ?$(mkIdent name))) funTy
      let handler ← m.withContext do
        withDoElem (← `(match e with $[| $[$patsss,*]|* => $val]*)) (.id α)
      pure (false, code, handler)
  | _ => throwUnsupportedSyntax
  m.assign handler.code
  let code ← mkAppOptM (if knownTy then ``tryCatchThe else ``tryCatch)
    #[ε, (← read).m, none, α, body.code, code]
  tail.apply {
    code
    updates := body.updates.union handler.updates
    exits := body.exits.union handler.exits
  }

def withDoTryFinally
    (body : Continuation → M CodeBlock)
    (fin : TSyntax ``doSeq)
    (tail : Continuation) : M CodeBlock := do
  let mut exits := {}
  let mut mvars := #[]
  let ctx ← read
  let fvars := ctx.muts.fold (fun fvars _ fvarId => fvars.push (.fvar fvarId)) #[]
  let contTy ← mkForallFVars fvars ctx.returnType
  for (exit, k) in ctx.exits do
    let mvarType ← mkArrow k.ty contTy
    let mvar ← mkFreshExprMVar mvarType .syntheticOpaque
    mvars := mvars.push mvar
    exits := exits.insert exit { k with jump := jumpToJP ctx mvar }
  let α := (← read).expectedType
  let res ← body (.id α) { ctx with exits }
  let unit ← mkConstWithFreshMVarLevels ``PUnit
  let finalizerRetTy ← mkArrow unit contTy
  let (res', fvars', _) ← withNewJP finalizerRetTy fun mvar _ => do
    let res' ← runDoSeq fin <| .pure .missing unit (jumpToJP ctx mvar)
    pure (res', ())
  let jpBodyType ← mkForallFVars fvars' ctx.returnType
  let handlerTy ← mkArrow finalizerRetTy jpBodyType
  withLocalDeclD (← mkFreshUserName `handler) handlerTy fun handlerJP => do
    for (exit, k) in ctx.exits, mvar in mvars do
      if res.exits.contains exit then
        let arg ← withLocalDeclD (← mkFreshUserName `ret) k.ty fun ret => do
          mkLambdaFVars (#[ret] ++ fvars) <| ← k.jump ret ctx.muts
        mvar.mvarId!.assign <| mkAppN (mkApp handlerJP arg) fvars
    let main ← mkAppOptM ``tryFinally
      #[none, α, none, none, res.code, mkAppN handlerJP fvars'] -- FIXME
    tail.apply {
      code := mkLetFunAnnotation <|
        mkApp (← mkLambdaFVars #[handlerJP] (mkAppN main fvars')) res'.code
      updates := res.updates.union res'.updates
      exits := res.exits.union res'.exits
    }

def withDoTry (tryTk : Syntax)
    (body : TSyntax ``doSeq)
    (catches : Array (TSyntax [``doCatch, ``doCatchMatch]))
    (fin : Option (TSyntax ``doSeq))
    (tail : Continuation) : M CodeBlock := withRef tryTk do
  if catches.isEmpty && fin.isNone then
    throwError "invalid `try`, it must have a `catch` or `finally`"
  let body := catches.foldl (init := runDoSeq body) withDoTryCatch
  if let some fin := fin then
    withDoTryFinally body fin tail
  else
    body tail

def withDoElemCore (doElem : TSyntax `doElem) (tail : Continuation) : M CodeBlock := do
  match doElem with
  | `(doElem| let $[mut%$tk]? $decl:letDecl) =>
    let vars ← getLetDeclVars decl
    withSyntaxBinder vars (fun rhs => `(let $decl:letDecl; ?$rhs)) <|
      (withNewMutableVars vars tk.isSome tail).run
  | `(doElem| have $decl:haveDecl) =>
    let vars ← getHaveDeclVars decl
    withSyntaxBinder vars (fun rhs => `(have $decl:haveDecl; ?$rhs)) tail.run
  | `(doElem| let rec $decl:letRecDecls) =>
    let vars ← getLetRecDeclsVars decl
    withSyntaxBinder vars (fun rhs => `(let rec $decl:letRecDecls; ?$rhs)) tail.run
  | `(doElem| $x:ident $[: $ty]? := $rhs) => do
    let lctx ← getLCtx
    withDoElem (← `(doElem| let $x:ident $[: $ty]? :=
      ensure_type_of% $x $(quote "invalid reassignment, value") $rhs)) <| .then .missing <|
    withReassign #[x] lctx tail
  | `(doElem| $pat:term $[: $ty]? := $rhs) =>
    let vars ← getPatternVarsEx pat
    let lctx ← getLCtx
    withDoElem (← `(doElem| let $pat:term $[: $ty]? :=
      ensure_type_of% $pat $(quote "invalid reassignment, value") $rhs)) <| .then .missing <|
    withReassign vars lctx tail
  | `(doElem| let $[mut%$tk]? $x:ident $[: $ty]? ← $rhs) =>
    checkLetArrowRHS rhs
    let ty ← elabType (← if let some ty := ty then pure ty else `(_))
    let ctx ← read
    withReader (fun _ => { ctx with expectedType := ty }) <|
      withDoElem rhs <| .bind .missing (.ident x ty) <|
        (withNewMutableVars #[x] tk.isSome tail).run ctx
  | `(doElem| let $[mut%$tk]? $pat:term ← $rhs) =>
    checkLetArrowRHS rhs
    let vars ← getPatternVarsEx pat
    let ty ← mkFreshTypeMVar
    let ctx ← read
    withReader (fun _ => { ctx with expectedType := ty }) <|
      withDoElem rhs <| .bind .missing (.term pat) <|
        (withNewMutableVars vars tk.isSome tail).run ctx
  | `(doElem| let $[mut%$tk]? $pat:term ← $rhs | $els) =>
    checkLetArrowRHS rhs
    let a ← mkFreshIdent rhs
    withDoElem (← `(doElem| let $a ← $rhs)) <| .then .missing do
      withDoElem (← `(doElem| let $[mut%$tk]? $pat := $a | $els)) tail
  | `(doElem| let $[mut%$tk]? $pat:term := $rhs | $els) => panic! "unimplemented"
  | `(doElem| $x:ident $[: $ty]? ← $rhs) => do
    let lctx ← getLCtx
    let m := (← read).mStx
    withDoElem (← `(doElem| let $x:ident $[: $ty]? ←
      (ensure_expected_type% "invalid reassignment, value" $rhs : $m (type_of% $x)))) <|
    .then .missing <| withReassign #[x] lctx tail
  | `(doElem| $pat:term ← $rhs) => do
    let vars ← getPatternVarsEx pat
    let lctx ← getLCtx
    let m := (← read).mStx
    withDoElem (← `(doElem| let $pat:term ←
      (ensure_expected_type% "invalid reassignment, value" $rhs : $m (type_of% $pat)))) <|
    .then .missing <| withReassign vars lctx tail
  | `(doElem| $pat:term ← $rhs | $els) => panic! "unimplemented"
  | `(doElem| if%$i $cond:doIfCond then $t
      $[else if%$is $conds:doIfCond then $ts]* $[else $e?]?) =>
    tail.withJP <| withIfChain i cond t (is.zip $ conds.zip ts).toList e?
  | `(doElem| unless%$i $cond:term do $t) =>
    tail.withJP fun tail => withIf i cond tail.run (runDoSeq t tail)
  | `(doElem| for $[$[$h :]? $x in $xs],* do $t) =>
    tail.withJP <| withDoParallelFor id (h.zip $ x.zip xs).reverse.toList t
  | `(doElem| match $[$gen]? $[$motive]? $discr,* with $[| $[$patsss,*]|* => $val]*) =>
    tail.withJP fun tail => withMatch gen motive discr patsss (val.map (runDoSeq · tail))
  | `(doElem| break) =>
    doExit (.break none) (← mkConstWithFreshMVarLevels ``PUnit.unit) tail
  | `(doElem| continue) =>
    doExit (.continue none) (← mkConstWithFreshMVarLevels ``PUnit.unit) tail
  | `(doElem| return $(e)?) => doReturn e tail
  | `(doElem| dbg_trace $msg) =>
    withSyntaxBinder #[] (fun rhs => `(dbg_trace $msg; ?$rhs)) tail.run
  | `(doElem| assert! $msg) =>
    withSyntaxBinder #[] (fun rhs => `(assert! $msg; ?$rhs)) tail.run
  | `(doElem| do $elems) => runDoSeq elems tail
  | `(doElem| $e:term) => withDoExpr e tail |>.run
  | _ =>
    let doElem := doElem.raw
    if doElem.getKind == ``Parser.Term.doTry then
      -- the way try is defined makes it impossible to match against
      withDoTry doElem[0] doElem[1] doElem[2].getArgs doElem[3].getOptional? tail
    else throwError "unexpected do-element of kind {doElem.getKind}:\n{doElem}"

initialize withDoElemRef.set withDoElemCore

elab "do'" seq:doSeq : term <= expectedType => do
  let { m, returnType, .. } ← extractBind expectedType
  let mStx ← exprToSyntax m
  let ref ← getRef
  let codeBlock ← runDoSeq seq (.id returnType)
    { ref, mStx, m, returnType, expectedType := returnType }
  pure codeBlock.code

end Do
