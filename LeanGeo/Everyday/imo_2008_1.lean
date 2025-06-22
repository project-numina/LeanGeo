import SystemE
import LeanGeo

open SystemE
namespace LeanGeo
set_option maxHeartbeats 0
/-theorem power_cyclic: ∀ (a b c d e: Point),distinctFourPoints a b c d ∧ (coll a b e) ∧ (coll c d e) ∧ |(e─a)| * |(e─b)| = |(e─c)| * |(e─d)| → cyclic a b c d := by
  sorry

theorem cyclic_power: ∀ (a b c d e: Point),distinctFourPoints a b c d ∧ cyclic a b c d ∧ (coll a b e) ∧ (coll c d e) → |(e─a)| * |(e─b)| = |(e─c)| * |(e─d)| := by
  sorry -/

theorem triangle_median_line_parallel' : ∀ (a b c d e : Point) (AB BC CA DE: Line), formTriangle a b c AB BC CA ∧ distinctPointsOnLine d e DE ∧ midpoint a d b ∧ midpoint a e c →  ¬ BC.intersectsLine DE:= by
  euclid_intros
  euclid_assert |(a─b)| * |(a─e)| = |(a─c)| * |(a─d)|
  euclid_assert triangle a d e
  euclid_assert (△ a:b:c).similar_test ((△ a:d:e))
  euclid_apply (△ a:b:c).similar_property ((△ a:d:e))
  euclid_assert ∠a:b:c = ∠a:d:e
  euclid_apply eqAlternateExteriorAngle_parallel e d c b a DE BC AB
  euclid_finish


theorem sameSide_eqAngle_coll : ∀(A B C D: Point) (AB : Line), distinctPointsOnLine A B AB ∧ (∠A:B:C = ∠A:B:D) ∧ D.sameSide C AB → coll B C D := by
  sorry
theorem perp_same_line_coll : ∀ (A B C: Point) (l AB AC : Line), (perpLine l AB ∧ perpLine l AC) ∧ (distinctPointsOnLine A B AB) ∧ (distinctPointsOnLine A C AC) → coll A B C := by
  euclid_intros
  euclid_apply intersection_lines AB l as P
  euclid_apply exists_distincts_points_on_line l P as Q
  euclid_apply unique_perpLine A l as L
  sorry
  --euclid_assert AB = L
  --euclid_assert AC = L
  --euclid_assert AB = AC
  --euclid_finish
  --euclid_apply sameSide_eqAngle_coll P Q A B l

theorem imo_08 : ∀ (A B C H E F C1 C2 B1 B2 H X: Point) (AB BC CA : Line) (ΓA ΓB :Circle), (ΓA.intersectsCircle ΓB ) ∧ formTriangle A B C AB BC CA ∧ midpoint A F B ∧ midpoint A E C ∧ C1.onCircle ΓA ∧ C2.onCircle ΓA ∧ B1.onCircle ΓB ∧ B2.onCircle ΓB ∧ orthoCentre H A B C ∧ between A C1 F ∧ between C1 F C2 ∧ between A B1 E ∧ between B1 E B2 ∧ H.onCircle ΓA ∧ H.onCircle ΓB  ∧ circlesIntersectsAtTwoPoints ΓA ΓB X H ∧ (X ≠ H) ∧ insideTriangle X A B C AB BC CA ∧ insideTriangle H A B C AB BC CA ∧ E.isCentre ΓB ∧ F.isCentre ΓA→ cyclic C1 C2 B2 B1 := by
  euclid_intros
  euclid_assert cyclic C1 C2 X H
  euclid_assert cyclic B1 B2 H X
  euclid_apply line_from_points E F as EF
  have h: coll A X H := by
    euclid_apply intersecting_circles_perpendicular_bisector ΓA ΓB F E X H EF
    euclid_apply line_from_points X H as XH
    euclid_apply line_from_points A H as AH
    euclid_apply intersection_lines AH BC as P
    euclid_assert perpLine AH BC
    euclid_apply triangle_median_line_parallel A B C F E AB BC CA EF
    euclid_apply (perpBisector_equiv X H EF).1 as (Q, L2)
    euclid_assert perpLine XH EF
    euclid_apply perpLine_parallel_perpLine BC AH EF
    euclid_apply perp_same_line_coll H X A EF XH AH
    euclid_finish
  euclid_apply cyclic_power B1 B2 X H A
  euclid_apply cyclic_power C1 C2 X H A
  have h2 : |(A─B1)| * |(A─B2)| = |(A─C1)| * |(A─C2)| := by
    euclid_finish
  euclid_apply power_cyclic C1 C2 B1 B2 A
  euclid_finish

end LeanGeo
