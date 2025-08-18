import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem library9 :
∀ (L M T : Line) (A B C D : Point),
  TwoLinesIntersectAtPoint L T A ∧
  TwoLinesIntersectAtPoint M T B ∧
  C.onLine L ∧
  D.onLine M ∧
  C.sameSide D T ∧ A ≠ B
  ∧ ∠ C:A:B + ∠ A:B:D = ∟ + ∟ → (¬ L.intersectsLine M) := by
  euclid_intros
  euclid_apply parallel_if_supp_consecutiveAngles
  euclid_finish
