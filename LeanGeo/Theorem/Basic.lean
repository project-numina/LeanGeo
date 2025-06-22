import SystemE
import LeanGeo.Abbre

open SystemE
namespace LeanGeo


axiom triangle_inequality : ∀ (a b c : Point), triangle a b c →
|(a─b)| < |(b─c)| + |(c─a)|

axiom triangle_inequality_le : ∀ (a b c : Point),
|(a─b)| ≤  |(b─c)| + |(c─a)|

theorem triangle_ineqaulity_eql : ∀ (a b c : Point), distinctThreePoints a b c ∧ |(a─b)| = |(b─c)| + |(c─a)| → between b c a  := by
  sorry

theorem line_ratio_unique : ∀ (A B C D : Point), between A C B ∧ between A D B ∧ |(A─C)|/|(C─B)| = |(A─D)|/|(D─B)| → C = D := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

end LeanGeo
