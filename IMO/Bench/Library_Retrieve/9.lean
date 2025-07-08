import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem librar9 :
∀ (L M T : Line) (A B C D : Point),
  twoLinesIntersectAtPoint L T A ∧
  twoLinesIntersectAtPoint M T B ∧
  C.onLine L ∧
  D.onLine M ∧
  C.sameSide D T ∧ A ≠ B
  ∧ ∠ C:A:B + ∠ A:B:D = ∟ + ∟ → (¬ L.intersectsLine M) := by
  euclid_intros
  obtain ⟨c', hc'⟩ := extend_point L C A (by euclid_finish)
  obtain ⟨d', hd'⟩ := extend_point M D B (by euclid_finish)
  obtain ⟨a', ha'⟩ := extend_point T B A (by euclid_finish)
  obtain ⟨b', hb'⟩ := extend_point T A B (by euclid_finish)
  have := parallel_if c' C d' D a' b' A B L M T (by euclid_finish)
  euclid_finish
