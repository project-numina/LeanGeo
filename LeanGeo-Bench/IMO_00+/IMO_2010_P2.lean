import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Given a Triangle $ABC$, with $I$ as its incenter and $\Gamma$ as its circumcircle, $AI$ intersects $\Gamma$ again at $D$. Let $E$ be a point on the arc $BDC$, and $F$ a point on the segment $BC$, such that $\angle BAF=\angle CAE < \dfrac12\angle BAC$. If $G$ is the MidPoint of $IF$, prove that the meeting point of the lines $EI$ and $DG$ lies on $\Gamma$.
theorem IMO_2010_P2 :
  ∀ (A B C D E F G I X : Point) (Γ : Circle) (AB BC CA AI EI DG : Line),
    formTriangle A B C AB BC CA ∧
    Incentre I A B C ∧
    Circumcircle Γ A B C ∧
    distinctPointsOnLine A I AI ∧
    D.onCircle Γ ∧
    D.onLine AI ∧
    D ≠ A ∧
    distinctPointsOnLine E I EI ∧
    E.onCircle Γ ∧
    E.opposingSides A BC ∧
    between B F C ∧
    ∠ B:A:F = ∠ C:A:E ∧
    (∠ B:A:F + ∠ B:A:F < ∠ B:A:C) ∧
    MidPoint I G F ∧
    distinctPointsOnLine D G DG ∧
    X.onLine EI ∧
    X.onLine DG →
    X.onCircle Γ := by
  sorry
