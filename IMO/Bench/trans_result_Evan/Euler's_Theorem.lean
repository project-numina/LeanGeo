import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Lemma 2.22 (Euler's Theorem). Let ABC be a triangle. Let $R$ and $r$ denote its circumradius and inradius, respectively. Let $O$ and $I$ denote its circumcenter and incenter. Then $O I^2=R(R-2 r)$. In particular, $R \geq 2 r$.
theorem Euler's_Theorem :
  ∀ (A B C O I D : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    circumCentre O A B C ∧
    inCentre I A B C ∧
    foot I D BC →
    (|(O─I)| * |(O─I)| = |(O─A)| * (|(O─A)| - 2 * |(I─D)|)) ∧ (|(O─A)| ≥ 2 * |(I─D)|) := by
  sorry