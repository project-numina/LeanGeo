import SystemE
import LeanGeo
namespace LeanGeo
theorem try3 : ∀ (A_1 B_1 C_1 D_1 : Point) (AB BC CD DA : Line), (formQuadrilateral A_1 B_1 C_1 D_1 AB BC CD DA) ∧ (distinctPointsOnLine A_1 C_1 AC) ∧ (distinctPointsOnLine B_1 D_1 BD) ∧ (∃(H_1: Point),perpPoint A_1 B_1 C_1 H_1) → AC.intersectsLine BD:= by
  euclid_intros
  euclid_finish
