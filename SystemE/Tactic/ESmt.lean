import Lean

import SystemE.Tactic.Translate
import Smt.Tactic.Smt
-- import SystemE.Tactic.EQuery
import SystemE.Tactic.Attr
-- import SystemE.Tactic.Translate
import Qq

namespace Smt

open Qq
open Lean hiding Command
open Elab Tactic Qq
open Smt Translate Query Reconstruct Util


#check Lean.Meta.withLocalDeclsD
def prepareSmtQuery' (oldGoalExprs : List Expr) (hs : List Expr) (goalType : Expr) (fvNames : Std.HashMap FVarId String) (initialState : QueryBuilderM.State := { : QueryBuilderM.State }) : MetaM (List Command) := do
  let goalId ← Lean.mkFreshMVarId
  Lean.Meta.withLocalDeclD goalId.name (mkNot goalType) fun g => do
    return (← (Query.generateQuery' oldGoalExprs g hs fvNames initialState)).2

/- Unsound axiom we use to admit results from the solvers
   Dangerous!
 -/
universe u
axiom SMT_VERIF (α : Sort u) (synthetic := false) : α


def mkSMT_VERIF (type : Expr) (synthetic : Bool) : MetaM Expr := do
  let u ← Meta.getLevel type
  return mkApp2 (mkConst ``SMT_VERIF [u]) type (toExpr synthetic)

#check Meta.mkSorry

open cvc5 in
def solve' (query : String) (timeout' : Option Nat) : IO (Except Error cvc5.Proof) := do
  Solver.run (← TermManager.new) do
    if let some t := timeout' then
      Solver.setOption "tlimit" (toString (1000 * t))
    -- Solver.setOption "dag-thresh" "0"
    Solver.setOption "simplification" "none"
    Solver.setOption "enum-inst" "true"
    Solver.setOption "cegqi-midpoint" "true"
    -- Solver.setOption "produce-models" "true"
    Solver.setOption "produce-proofs" "true"
    -- Solver.setOption "proof-elim-subtypes" "true"
    -- Solver.setOption "proof-granularity" "dsl-rewrite"

    Solver.parse query
    let r ← Solver.checkSat
    if r.isUnsat then
      let ps ← Solver.getProof
      if h : 0 < ps.size then
        return ps[0]
    throw (self := instMonadExceptOfMonadExceptOf _ _) (Error.error s!"Expected unsat, got {r}")

/-
  asTask but with a timeout
-/
def withTimeout {α : Type} (act : IO α) (timeoutMs : Nat) (prio := Task.Priority.default) : IO (Except IO.Error (Option α)) := do
  let task ← IO.asTask (do return some (← act)) prio
  let timeoutTask ← IO.asTask (do
    IO.sleep timeoutMs.toUInt32
    return (none : Option α)
  )
  IO.waitAny [task, timeoutTask]

#check smt
def esmt (oldGoalExprs : List Expr) (mv : MVarId) (ac : List Command) (st : QueryBuilderM.State) (hs : List Expr) (timeout' : Option Nat := none) : MetaM (List MVarId) := mv.withContext do
  -- 1. Process the hints passed to the tactic.
    withProcessedHints mv hs fun mv hs => mv.withContext do
    let (hs, mv) ← Preprocess.elimIff mv hs
    mv.withContext do
    let goalType : Q(Prop) ← mv.getType
  -- 2. Generate the SMT query.
    let (fvNames₁, fvNames₂) ← genUniqueFVarNames
  -- let (st, _) ← prepareSmtQuery' as (← mv.getType) fvNames₁
    let cmds ← prepareSmtQuery' oldGoalExprs hs (← mv.getType) fvNames₁ st
    -- let cmds ← prepareSmtQuery (oldGoalExprs ++ hs) (← mv.getType) fvNames₁
    -- let shortCmds ← prepareSmtQuery hs (← mv.getType) fvNames₁
    let cmds := .setLogic "ALL" :: cmds
    trace[smt] "goal: {goalType}"
    trace[smt] "num commands {cmds.length}"
    trace[smt] "\nquery:\n{Command.cmdsAsQuery (cmds ++ [.checkSat])}"
  -- parse the commands
    let time1 ← IO.monoMsNow
    let query := Command.cmdsAsQuery cmds
    let time2 ← IO.monoMsNow
    dbg_trace f!"parsing time: {time2 - time1}"
  -- 3. Run the solver.

    let res : Except cvc5.Error (Option cvc5.Proof) ← (
      match none with
      | some x => do
        match ← withTimeout (solve' query (some x)) (x * 1000) with
        | .ok none => pure (.ok none)
        | .ok (some x) => pure x
        | .error e =>
          pure <| .error (cvc5.Error.error e.toString)
      | none => do
        match ← solve' query none with
        | .ok x => pure <| .ok (some x)
        | .error e => pure (.error e)
    )
    let time3 ← IO.monoMsNow
    dbg_trace f!"solving time: {time3 - time2}"
  -- 4. Print the result.
  -- trace[smt] "\nresult: {res}"
    match res with
    | .error e =>
      -- 4a. Print error reason.
      trace[smt] "\nerror reason:\n{repr e}\n"
        throwError "unable to prove goal, either it is false or you need to define more symbols with `smt [foo, bar]`"
    | .ok pf =>
      let goalType ← mv.getType
      let lsorry ← mkSMT_VERIF goalType (synthetic := true)
      mv.assign lsorry
      return []

-- open Lean hiding Command
open Elab Tactic Qq
open Smt Translate Query Reconstruct Util

namespace Tactic

syntax (name := esmt) "esmt" smtHints smtTimeout : tactic

#check Tactic.evalRunTac
#check Tactic.evalTactic
#check Tactic.elabTerm

/-
  if no hints are given the entire local context is used
-/
@[tactic esmt]
def evalESmt : Tactic := fun stx => withMainContext do
  let ⟨st, oldGoals, cmds⟩ := euclidExtension.getState (← getEnv)
  let userHints ← parseHints ⟨stx[1]⟩

  -- If hints are empty, fall back to all local declarations
  let hints ← if userHints.isEmpty then
    let lctx ← getLCtx
    lctx.foldlM (init := []) fun acc decl =>
      if decl.isImplementationDetail || decl.isAuxDecl then
        pure acc
      else do
        let type ← instantiateMVars decl.type
        if ← Meta.isProp type then
          pure (acc.concat <| ← instantiateMVars decl.toExpr)
        else
          pure acc
  else
    pure userHints

  -- for goalExpr in oldGoals do
  --   let goalStx ← Term.exprToSyntax goalExpr
  --   evalTactic <| ← `(tactic| have := $goalStx)

  let mvs ← Smt.esmt oldGoals (← Tactic.getMainGoal) cmds st (hints) (← parseTimeout ⟨stx[2]⟩)
  Tactic.replaceMainGoal mvs
