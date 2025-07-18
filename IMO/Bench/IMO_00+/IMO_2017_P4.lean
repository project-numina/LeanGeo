import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $R$ and $S$ be different points on a circle $\Omega$ such that $RS$ is not a diameter. Let $\ell$ be the tangent line to $\Omega$ at $R$. Point $T$ is such that $S$ is the midpoint of the line segment $RT$. Point $J$ is chosen on the shorter arc $RS$ of $\Omega$ so that the circumcircle $\Gamma$ of triangle $JST$ intersects $\ell$ at two distinct points. Let $A$ be the common point of $\Gamma$ and $\ell$ that is closer to $R$. Line $AJ$ meets $\Omega$ again at $K$. Prove that the line $KT$ is tangent to $\Gamma$.
theorem IMO_2017_P4 :
  ∀ (R S T J A B K O P : Point) (Ω Γ : Circle) (l KT : Line),
    R.onCircle Ω ∧
    S.onCircle Ω ∧
    R ≠ S ∧
    tangentAtPoint R O l Ω ∧
    ¬ coll R O S ∧
    midpoint R S T ∧
    J.onCircle Ω ∧
    J ≠ R ∧
    J ≠ S ∧
    ∠R:J:S > ∟ ∧
    circumCircle Γ J S T ∧
    A.onLine l ∧
    A.onCircle Γ ∧
    B.onLine l ∧
    B.onCircle Γ ∧
    A ≠ B ∧
    |(R─A)| < |(R─B)| ∧
    coll A J K ∧
    K.onCircle Ω ∧
    K ≠ J ∧ distinctPointsOnLine K T KT →
  tangentAtPoint T P KT Γ := by
  sorry
