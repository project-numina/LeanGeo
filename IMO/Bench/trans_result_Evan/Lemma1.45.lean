import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--(Right Angles on Incircle Chord). The incircle of △ABC is tangent to BC, CA, AB at D, E, F, respectively. Let M and N be the midpoints of BC and AC, respectively. I is the incenter of triangle ABC. Ray BI meets line EF at K. Show that BK ⊥ CK. Then show K lies on line MN.
theorem Lemma1_45 :
  ∀ (A B C D E F M N I K : Point) (AB BC CA EF BI MN : Line) (Ω : Circle),
    formTriangle A B C AB BC CA ∧
    inCentre I A B C ∧
    inCircle Ω AB BC CA ∧
    tangentAtPoint D I BC Ω ∧
    tangentAtPoint E I CA Ω ∧
    tangentAtPoint F I AB Ω ∧
    midpoint B M C ∧
    midpoint A N C ∧
    distinctPointsOnLine B I BI ∧
    distinctPointsOnLine E F EF ∧
    twoLinesIntersectAtPoint BI EF K ∧
    distinctPointsOnLine M N MN →
  perpPoint B K C K ∧
  K.onLine MN := by
  sorry
