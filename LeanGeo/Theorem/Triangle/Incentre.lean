import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import LeanGeo.Theorem.Triangle.Basic
import LeanGeo.Theorem.Metrics.Trigonometry

set_option maxHeartbeats 0
open Elements.Book1
namespace LeanGeo

theorem exists_incentre : ∀ (A B C: Point), Triangle A B C → ∃ (I : Point), Incentre I A B C := by
  euclid_intros
  euclid_apply exists_angleBisector A B C as lb
  euclid_apply exists_angleBisector B C A as lc
  euclid_apply exists_angleBisector C A B as la
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points A C as AC
  have hh0 : la.intersectsLine BC := by
    by_contra
    euclid_apply point_on_line_same_side AC la B as P
    euclid_finish
  have hh1 : lb.intersectsLine AC := by
    by_contra
    euclid_apply point_on_line_same_side AB lb C as P
    euclid_finish
  have hh2 : lc.intersectsLine AB := by
    by_contra
    euclid_apply point_on_line_same_side BC lc A as P
    euclid_finish
  euclid_apply intersection_lines la BC as D
  euclid_apply intersection_lines lb AC as E
  euclid_apply intersection_lines lc AB as F
  have hh3 : la.intersectsLine lc := by
    by_contra
    euclid_apply point_on_line_same_side AC la B as P
    euclid_apply point_on_line_same_side AC lc B as Q
    euclid_finish
  euclid_apply intersection_lines la lc as I
  have aux : Real.sin (∠D:A:B) * Real.sin (∠E:B:C) * Real.sin (∠F:C:A) = Real.sin (∠D:A:C) * Real.sin (∠E:B:A) * Real.sin (∠F:C:B) := by
    have aux_h: ∠D:A:B = ∠D:A:C ∧ ∠E:B:C = ∠E:B:A ∧ ∠F:C:A = ∠F:C:B := by
      euclid_finish
    rw[aux_h.1, aux_h.2.1, aux_h.2.2]
  euclid_apply CevaTheorem_converse_to_sine A B C D E F I
  use I
  simp
  euclid_finish

end LeanGeo
