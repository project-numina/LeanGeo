import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be a Triangle with $AB < AC < BC$. Let the incenter and incircle of Triangle $ABC$ be $I$ and $\omega$, respectively. Let $X$ be the point on line $BC$ different from $C$ such that the line through $X$ parallel to $AC$ is tangent to $\omega$. Similarly, let $Y$ be the point on line $BC$ different from $B$ such that the line through $Y$ parallel to $AB$ is tangent to $\omega$. Let $AI$ intersect the circumcircle of Triangle $ABC$ at $P ≠ A$. Let $K$ and $L$ be the midpoints of $AC$ and $AB$, respectively. Prove that $\angle KIL + \angle YPX = 180^{\circ}$.
theorem IMO_2024_P4 :
  ∀ (A B C I X Y P K L : Point) (AB BC AC AI LX LY : Line) (Ω Γ : Circle),
    formTriangle A B C AB BC AC ∧
    |(A─B)| < |(A─C)| ∧
    |(A─C)| < |(B─C)| ∧
    Incentre I A B C ∧
    I.isCentre Ω ∧
    Incircle Ω A B C AB BC AC ∧
    distinctPointsOnLine X C BC ∧
    X.onLine LX ∧
    ¬ LX.intersectsLine AC ∧
    TangentLineCircle LX Ω ∧
    distinctPointsOnLine Y B BC ∧
    Y.onLine LY ∧
    ¬ LY.intersectsLine AB ∧
    TangentLineCircle LY Ω ∧
    Circumcircle Γ A B C ∧
    distinctPointsOnLine A I AI ∧
    P.onLine AI ∧
    P.onCircle Γ ∧
    P ≠ A ∧
    MidPoint A K C ∧
    MidPoint A L B →
  ∠ K:I:L + ∠ Y:P:X = ∟ + ∟ := by
  sorry
