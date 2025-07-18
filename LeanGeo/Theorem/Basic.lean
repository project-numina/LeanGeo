import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom

namespace LeanGeo

theorem triangle_ineqaulity_eql : ∀ (a b c : Point), distinctThreePoints a b c ∧ |(a─b)| = |(b─c)| + |(c─a)| → between b c a  := by
  euclid_intros
  split_ands
  have h_coll : coll a b c := by
    by_contra h_not_coll
    have h_tri : triangle a b c := by
      euclid_finish
    euclid_apply triangle_inequality a b c
    euclid_finish
  have h_not_abc : ¬ between a b c := by
    by_contra h_abc
    euclid_finish
  have h_not_cab : ¬ between c a b := by
    by_contra h_cab
    euclid_finish
  euclid_finish

theorem line_ratio_unique : ∀ (A B C D : Point), between A C B ∧ between A D B ∧ |(A─C)|/|(C─B)| = |(A─D)|/|(D─B)| → C = D := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

end LeanGeo
