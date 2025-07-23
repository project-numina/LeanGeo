import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

theorem IMO_p2 : ∀ (M N A B C D P E F O hp hm hn: Point) (MN AP L PM PN: Line) (Ω Γ BEF: Circle), M.isCentre Ω ∧ N.isCentre Γ ∧ (rad Ω) < (rad Γ) ∧ CirclesIntersectAtTwoPoints Ω Γ A B ∧
  distinctPointsOnLine M N MN ∧ C.onLine MN ∧ C.onCircle Ω ∧ D.onLine MN ∧ D.onCircle Γ ∧ between C M N ∧ between M N D ∧
  Circumcentre P A C D ∧ distinctPointsOnLine A P AP ∧ LineIntersectsCircleAtTwoPoints A E AP Ω ∧ LineIntersectsCircleAtTwoPoints A F AP Γ ∧
  Orthocentre H P M N hp hm hn PM MN PN ∧ H.onLine L ∧ ¬ L.intersectsLine AP ∧ Circumcircle BEF B E F ∧ O.isCentre BEF
  → ∃ (Q : Point), TangentLineCircleAtPoint Q O L BEF := by
  sorry
end LeanGeo
