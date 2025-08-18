import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--2. Let $I$ be the center of the inscribed circle in Triangle $ABC$. Prove that the center of the circle circumscribed around Triangle $AIC$ lies on the circle circumscribed around Triangle $ABC$.-/
theorem Numina_Geometry_850 : ∀ (A B C I O : Point) (Ω : Circle), (Triangle A B C) ∧ (Incentre I A B C) ∧ (Circumcentre O A I C) ∧ (Circumcircle Ω A B C) → O.onCircle Ω := by
  sorry
