import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem tangent_parallel_to_chord_collinear:
  ∀ (Ω : Circle) (L_AB L_T : Line) (O A B M T: Point),
    O.isCentre Ω ∧
    A.onCircle Ω ∧ B.onCircle Ω ∧ T.onCircle Ω ∧
    A ≠ B ∧
    MidPoint A M B ∧
    distinctPointsOnLine A B L_AB ∧
    TangentLineCircleAtPoint T O L_T Ω ∧
    (¬ L_AB.intersectsLine L_T)
    → Coll O M T := by
  sorry

end LeanGeo
