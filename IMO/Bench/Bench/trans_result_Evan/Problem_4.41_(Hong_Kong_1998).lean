import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $P Q R S$ be a Cyclic quadrilateral with $\angle P S R=90^{\circ}$ and let $H$ and $K$ be the feet of the altitudes from $Q$ to lines $P R$ and $P S$. Prove that $\overline{H K}$ bisects $\overline{Q S}$.
theorem Problem_4_41_Hong_Kong_1998 :
  ∀ (P Q R S H K : Point) (PQ QR RS SP HK QS : Line) (Ω :Circle),
    CyclicQuadrilateral P Q R S PQ QR RS SP Ω ∧
    ∠ P:S:R = ∟ ∧
    distinctPointsOnLine P R PR ∧
    Foot Q H PR ∧
    Foot Q K SP ∧
    distinctPointsOnLine H K HK ∧
    distinctPointsOnLine Q S QS →
  ∃ (X : Point), X.onLine HK ∧ X.onLine QS ∧ MidPoint Q X S := by
  sorry
