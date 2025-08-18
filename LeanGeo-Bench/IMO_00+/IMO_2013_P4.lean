import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be an acute Triangle with orthocenter $H$, and let $W$ be a point on the side $BC$, lying strictly between $B$ and $C$. The points $M$ and $N$ are the feet of the altitudes from $B$ and $C$, respectively. Denote by $\omega_1$ is the circumcircle of $BWN$, and let $X$ be the point on $\omega_1$ such that $WX$ is a Diameter of $\omega_1$. Analogously, denote by $\omega_2$ the circumcircle of Triangle $CWM$, and let $Y$ be the point such that $WY$ is a Diameter of $\omega_2$. Prove that $X,Y$ and $H$ are collinear.
theorem IMO_2013_P4 :
  ∀ (A B C H W M N X Y O1 O2 : Point) (AB BC CA : Line) (ω1 ω2 : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    between B W C ∧
    Foot B M CA ∧
    Foot C N AB ∧
    Coll B H M ∧
    Coll C H N ∧
    Circumcircle ω1 B W N ∧
    Diameter W X O1 ω1 ∧
    Circumcircle ω2 C W M ∧
    Diameter W Y O2 ω2 →
    Coll X H Y := by
  sorry
