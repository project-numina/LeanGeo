import SystemE.Tactic.Translate
import SystemE.Theory
import Smt
import Smt.Real

theorem womp (a b c : Point): 2 + 2 = 4 := by
  have h1 : ∠ a:b:c = ∠ a:b:c := by rfl
  have h2 : (Segment.endpoints a b).length = 2 := sorry
  smt_show [h1, h2]
