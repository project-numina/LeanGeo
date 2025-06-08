import SystemE
import LeanGeo
namespace LeanGeo
theorem womp : ∃ (A B : Point) (L : Line), perpBisector A B L ∧ A.opposingSides B L := by
  euclid_intros
  euclid_finish
