import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

set_option maxHeartbeats 0

/--3. In an acute-angled Triangle $ABC$, two altitudes $AD$ and $CE$ are drawn. Perpendiculars $AM$ and $CN$ are dropped from points $A$ and $C$ to the line $DE$. Prove that $ME = DN$.-/
theorem Numina_Geometry_1001 :
  ∀ (A B C D E M N : Point) (AB BC CA DE: Line),
    formAcuteTriangle A B C AB BC CA ∧
    Foot A D BC ∧
    Foot C E AB ∧
    distinctPointsOnLine D E DE ∧
    Foot A M DE ∧
    Foot C N DE →
    |(M─E)| = |(D─N)| := by
  euclid_intros
  euclid_apply exists_midpoint A C as O
  euclid_apply circle_from_points O A as Ω
  have h1: between A E B := by
    euclid_apply acuteTriangle_foot_between C A B E AB
    euclid_finish
  have h2: between B D C := by
    euclid_apply acuteTriangle_foot_between A B C D BC
    euclid_finish
  have h3: E.onCircle Ω := by
    euclid_apply rightAngle_imp_diameter_onCircle A C E O Ω
    euclid_finish
  have h4: D.onCircle Ω := by
    euclid_apply rightAngle_imp_diameter_onCircle A C D O Ω
    euclid_finish
  euclid_apply line_from_points A M as AM
  euclid_apply line_from_points C N as CN
  have h5: between M E D := by
    euclid_apply obtuseTriangle_foot_between A E D M DE
    euclid_finish
  have h7: between N D E := by
    euclid_apply obtuseTriangle_foot_between C D E N DE
    euclid_finish
  have h9: ¬(AM.intersectsLine CN):= by
    euclid_apply parallel_if_supp_consecutiveAngles AM CN DE M N A C
    euclid_finish
  euclid_apply exists_midpoint M N as P
  euclid_apply line_from_points P O as PO
  have h10: ¬(PO.intersectsLine CN) := by
    euclid_apply trapezoid_midsegment_parallel_base A M N C P O AM DE CN CA PO
    euclid_finish
  have h11: Foot O P DE := by
    have h12: ∠O:P:N = ∟ := by
      euclid_apply parallel_imp_supp_consecutiveAngles PO CN DE P N O C
      euclid_finish
    euclid_apply foot_if_rightAngle O P N DE
    euclid_finish
  have h13: MidPoint E P D := by
    euclid_apply chord_midpoint_if_foot O D E P Ω DE
    euclid_finish
  euclid_finish
