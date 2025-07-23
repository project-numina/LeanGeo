import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let P be a point inside circle ω. Consider the set of chords of ω that contain P . Prove that their midpoints all lie on a circle.
theorem Canada_1991_3 :
  ∀ (P O : Point) (Ω : Circle),
    P.insideCircle Ω ∧ O.isCentre Ω →
    ∃ (Γ : Circle), ∀ (A B M : Point),
      (A.onCircle Ω ∧ B.onCircle Ω ∧ between A P B ∧ MidPoint A M B) →
      M.onCircle Γ := by
    sorry
