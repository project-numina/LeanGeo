import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $R$ and $S$ be different points on a circle $\Omega$ such that $RS$ is not a diameter. Let $\ell$ be the tangent line to $\Omega$ at $R$. Point $T$ is such that $S$ is the midpoint of the line segment $RT$. Point $J$ is chosen on the shorter arc $RS$ of $\Omega$ so that the circumcircle $\Gamma$ of triangle $JST$ intersects $\ell$ at two distinct points. Let $A$ be the common point of $\Gamma$ and $\ell$ that is closer to $R$. Line $AJ$ meets $\Omega$ again at $K$. Prove that the line $KT$ is tangent to $\Gamma$.
theorem IMO_2017_P4 :
  ∀ (R S T J A B K O P : Point) (Ω Γ : Circle) (ℓ AJline KTline : Line),
    R.onCircle Ω ∧
    S.onCircle Ω ∧
    R ≠ S ∧
    tangentAtPoint R O ℓ Ω ∧
    midpoint R S T ∧
    J.onCircle Ω ∧
    J ≠ R ∧
    J ≠ S ∧
    circumCircle Γ J S T ∧
    A.onLine ℓ ∧
    A.onCircle Γ ∧
    B.onLine ℓ ∧
    B.onCircle Γ ∧
    A ≠ B ∧
    |(R─A)| < |(R─B)| ∧
    coll A J K ∧
    K.onCircle Ω ∧
    K ≠ J →
  tangentAtPoint T P KTline Γ := by
  sorry
