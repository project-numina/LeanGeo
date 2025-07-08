import Mathlib
import SystemE
import LeanGeo
open LeanGeo LeanGeo
theorem point_on_circumcircle_equidistant_from_circumcenter : ∀ (A B C O D : Point) (Ω : Circle),   triangle A B C  ∧  circumCentre O A B C ∧    circumCircle Ω A B C ∧   D.onCircle Ω   → |(O─D)| = |(O─A)| := by
  euclid_intros
  have h_O_is_centre : O.isCentre Ω := by
    euclid_apply circumCentre_isCentre_circumCircle A B C O Ω
    euclid_finish
  have h_A_on_Omega : A.onCircle Ω := by
    euclid_finish
  euclid_finish
