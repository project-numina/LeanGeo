import SystemE.Tactic.ESmt
import Lean
import Batteries
import SystemE.Tactic.Util

open Lean Meta Elab Tactic SystemE.Tactics

elab "euclid_finish" : tactic => do
  -- Try simp_all safely
  try
    evalTactic (← `(tactic| simp_all))
  catch _ =>
    pure ()

  -- Try split_ands safely
  try
    evalTactic (← `(tactic| split_ands))
  catch _ =>
    pure ()

  -- Always run esmt on all goals
  evalTactic (← `(tactic| all_goals esmt))

/-
  Main function for `euclid_apply`
-/
def EuclidApply (rule : Term) (idents : Array Ident)  : TacticM Unit := do
  if (← getGoals).length != 1 then
    throwError "euclid_apply only works when there is a single goal"
  let hnm ← getUnusedUserName `h
  let τ ← inferType (← elabTerm rule none) >>= instantiateMVars

  let ⟨e, proof⟩ : Expr × Term := ← (do
    match τ with
    | .forallE _ hole P _ =>
      if P.hasLooseBVars then  --  τ is an ∀
        return ⟨τ, rule⟩
      else  -- τ is an implication, rather than ∀
        dbg_trace rule
        return ⟨P, ← `(term| $rule (by dsimp at *; esmt))⟩
    | _ => return ⟨τ, rule⟩
  )
  elimAllConjunctions

  match e.getAppFnArgs with
  | (``Exists, _) =>  -- τ is `∃ x, ...`
    evalTactic $ ← `(tactic| obtain ⟨$idents,*, hnm⟩ := $proof)
  | _ =>
    evalTactic $ ← `(tactic| obtain $(mkIdent hnm) := $proof)

  elimAllConjunctions

syntax "euclid_apply" term : tactic
syntax "euclid_apply" term "as" ident : tactic
syntax "euclid_apply" term "as" "(" ident,+ ")" : tactic

elab_rules : tactic
  | `(tactic| euclid_apply $t as $i) =>
    withMainContext $ EuclidApply t #[i]
  | `(tactic| euclid_apply $t as ($is,*)) =>
    withMainContext $ EuclidApply t is
  | `(tactic| euclid_apply $t) =>
    withMainContext $ EuclidApply t #[]

syntax "euclid_assert" term : tactic

macro_rules
  | `(tactic| euclid_assert $t) => `(tactic| have : $t := by euclid_finish)
