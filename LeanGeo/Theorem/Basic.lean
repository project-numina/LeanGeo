import SystemE
import LeanGeo.Abbre

namespace LeanGeo


axiom triangle_inequality : ∀ (a b c : Point), triangle a b c →
|(a─b)| < |(b─c)| + |(c─a)|

axiom triangle_inequality_le : ∀ (a b c : Point),
|(a─b)| ≤  |(b─c)| + |(c─a)|

theorem triangle_ineqaulity_eql : ∀ (a b c : Point), distinctThreePoints a b c ∧ |(a─b)| = |(b─c)| + |(c─a)| → between b c a  := by
  sorry

end LeanGeo
