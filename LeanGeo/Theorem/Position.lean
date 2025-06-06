import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle
namespace LeanGeo
theorem angleBisector_opposingsides : ∀ (A B C I : Point) (AI : Line), (distinctPointsOnLine A I AI)∧ triangle A B C ∧ ∠ I:A:B = ∠ I:A:C →  B.opposingSides C AI := by
  euclid_intros
  by_contra
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points A B as AB
  euclid_finish

theorem opposingsides_inside_triangle :  ∀ (A B C I : Point) (AB BC CA AI BI CI : Line), (formTriangle A B C AB BC CA) ∧ (distinctPointsOnLine B I BI) ∧ (distinctPointsOnLine C I CI) ∧ A.opposingSides C BI ∧ B.opposingSides C AI → insideTriangle I A B C AB BC CA:= by
  euclid_intros
  sorry
theorem quadrilateral_line_from_side_sameside : ∀ (A B C D E F: Point) (AB BC CD DA EF: Line), formQuadrilateral A B C D AB BC CD DA ∧ distinctPointsOnLine E F EF ∧ between B E C ∧ between A F D → A.sameSide B EF := by
  sorry
theorem perp_foot: ∀ (A B C: Point) (l : Line), ¬ A.onLine l ∧ distinctPointsOnLine B C l ∧ ∠A:B:C = ∟ → foot A B l:= by
  euclid_intros
  euclid_apply angle_between_transfer
  euclid_finish
end LeanGeo
