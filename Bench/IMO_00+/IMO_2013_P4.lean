import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be an acute triangle with orthocenter $H$, and let $W$ be a point on the side $BC$, lying strictly between $B$ and $C$. The points $M$ and $N$ are the feet of the altitudes from $B$ and $C$, respectively. Denote by $\omega_1$ is the circumcircle of $BWN$, and let $X$ be the point on $\omega_1$ such that $WX$ is a diameter of $\omega_1$. Analogously, denote by $\omega_2$ the circumcircle of triangle $CWM$, and let $Y$ be the point such that $WY$ is a diameter of $\omega_2$. Prove that $X,Y$ and $H$ are collinear.
theorem IMO_2013_P4 :
  ∀ (A B C H W M N X Y O1 O2 : Point) (AB BC CA : Line) (ω1 ω2 : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    between B W C ∧
    foot B M CA ∧
    foot C N AB ∧
    coll B H M ∧
    coll C H N ∧
    circumCircle ω1 B W N ∧
    diameter W X O1 ω1 ∧
    circumCircle ω2 C W M ∧
    diameter W Y O2 ω2 →
    coll X H Y := by
  sorry