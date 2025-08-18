import Lean

import Smt.Tactic.Smt
import SystemE.Tactic.Attr
import Qq

namespace Smt

open Qq
open Lean hiding Command
open Elab Tactic Qq
open Smt Translate Query Reconstruct Util

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

def esmt (oldGoalExprs : List Expr) (mv : MVarId) (ac : List Command) (st : QueryBuilderM.State) (hs : List Expr) (timeout' : Option Nat := none) : MetaM (List MVarId) := mv.withContext do
  -- 1. Process the hints passed to the tactic.
  withProcessedHints mv hs fun mv hs => mv.withContext do
  let (hs, mv) ← Preprocess.elimIff mv hs
  mv.withContext do
  let goalType : Q(Prop) ← mv.getType
  -- 2. Generate the SMT query.
  let (fvNames₁, fvNames₂) ← genUniqueFVarNames
  let cmds ← prepareSmtQuery' oldGoalExprs hs (← mv.getType) fvNames₁ st
  let cmds := .setLogic "ALL" :: cmds
  trace[smt] "goal: {goalType}"
  trace[smt] "num commands {cmds.length}"
  trace[smt] "\nquery:\n{Command.cmdsAsQuery (cmds ++ [.checkSat])}"
  -- parse the commands
  let query := Command.cmdsAsQuery cmds
  -- 3. Run the solver.

  let res : Except cvc5.Error (Option cvc5.Proof) ← (
    match ← solve query timeout' with
    | .ok x => pure <| .ok (some x)
    | .error e => pure (.error e)
  )
  -- 4. Print the result.
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
