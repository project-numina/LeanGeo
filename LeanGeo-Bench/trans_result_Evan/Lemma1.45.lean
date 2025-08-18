import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--(Right Angles on Incircle Chord). The incircle of △ABC is tangent to BC, CA, AB at D, E, F, respectively. Let M and N be the midpoints of BC and AC, respectively. I is the incenter of Triangle ABC. Ray BI meets line EF at K. Show that BK ⊥ CK. Then show K lies on line MN.
theorem Lemma1_45 :
  ∀ (A B C D E F M N I K : Point) (AB BC CA EF BI MN : Line) (Ω : Circle),
    formTriangle A B C AB BC CA ∧
    Incentre I A B C ∧
    Incircle Ω A B C AB BC CA ∧
    TangentLineCircleAtPoint D I BC Ω ∧
    TangentLineCircleAtPoint E I CA Ω ∧
    TangentLineCircleAtPoint F I AB Ω ∧
    MidPoint B M C ∧
    MidPoint A N C ∧
    distinctPointsOnLine B I BI ∧
    distinctPointsOnLine E F EF ∧
    TwoLinesIntersectAtPoint BI EF K ∧
    distinctPointsOnLine M N MN →
  PerpFourPoints B K C K ∧
  K.onLine MN := by
  sorry
