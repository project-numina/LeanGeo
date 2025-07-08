import SystemE
import LeanGeo
open LeanGeo LeanGeo
set_option maxHeartbeats 0

theorem equal_chords_equidistant_from_center :
  ∀ (A B C D O M N : Point) (Ω : Circle) (AB CD : Line),
    O.isCentre Ω ∧
    A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ D.onCircle Ω ∧
    distinctPointsOnLine A B AB ∧ distinctPointsOnLine C D CD ∧
    midpoint A M B ∧ midpoint C N D ∧
    ¬(O.onLine AB) ∧ ¬(O.onLine CD) ∧
    |(A─B)| = |(C─D)|
    → |(O─M)| = |(O─N)| := by
  euclid_intros
  have h_pyth_OMA : |(O─A)| * |(O─A)| = |(O─M)| * |(O─M)| + |(A─M)| * |(A─M)| := by
    have h_foot_M : foot O M AB := by
      euclid_apply chord_midpoint_foot O A B M Ω AB
      euclid_finish
    have h_right_OMA: rightTriangle M O A := by
      euclid_finish
    euclid_apply pythagorean_point M O A
    euclid_finish
  have h_pyth_ONC : |(O─C)| * |(O─C)| = |(O─N)| * |(O─N)| + |(C─N)| * |(C─N)| := by
    have h_foot_N : foot O N CD := by
      euclid_apply chord_midpoint_foot O C D N Ω CD
      euclid_finish
    have h_right_ONC: rightTriangle N O C := by
      euclid_finish
    euclid_apply pythagorean_point N O C
    euclid_finish
  have h_half_chords_eq : |(A─M)| = |(C─N)| := by
    euclid_finish
  have h_radii_eq : |(O─A)| = |(O─C)| := by
    euclid_finish
  euclid_finish
