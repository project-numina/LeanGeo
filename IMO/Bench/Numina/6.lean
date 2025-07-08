import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--2. Let $I$ be the center of the inscribed circle in triangle $ABC$. Prove that the center of the circle circumscribed around triangle $AIC$ lies on the circle circumscribed around triangle $ABC$.-/
theorem Numina_Geometry_850 : ∀ (A B C I O : Point) (Ω : Circle), (triangle A B C) ∧ (inCentre I A B C) ∧ (circumCentre O A I C) ∧ (circumCircle Ω A B C) → O.onCircle Ω := by
  sorry
