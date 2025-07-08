import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem generate_theorem_1:
  ∀ (O A B C D M N : Point) (Ω : Circle) (L_AB L_CD : Line),
    O.isCentre Ω ∧
    A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ D.onCircle Ω ∧
    distinctPointsOnLine A B L_AB ∧
    distinctPointsOnLine C D L_CD ∧
    |(A─B)| = |(C─D)| ∧
    foot O M L_AB ∧
    foot O N L_CD
    → |(O─M)| = |(O─N)| := by
  euclid_intros
  have h_iso_OAB : isoTriangle O A B := by euclid_finish
  have h_M_midpoint_AB : midpoint A M B := by
    euclid_apply isoTriangle_threeLine_concidence_foot O A B M L_AB
    euclid_finish
  have h_iso_OCD : isoTriangle O C D := by euclid_finish
  have h_N_midpoint_CD : midpoint C N D := by
    euclid_apply isoTriangle_threeLine_concidence_foot O C D N L_CD
    euclid_finish
  have h_len_AM_half : |(A─B)| = 2 * |(A─M)| := by euclid_finish
  have h_len_CN_half : |(C─D)| = 2 * |(C─N)| := by euclid_finish
  have h_legs_eq : |(A─M)| = |(C─N)| := by euclid_finish
  have h_rt_OAM : rightTriangle M A O := by euclid_finish
  have h_rt_OCN : rightTriangle N C O := by euclid_finish
  have h_hyps_eq : |(A─O)| = |(C─O)| := by euclid_finish
  have h_cong : congruentTriangle M A O N C O := by
    euclid_apply HL_congruent M A O N C O
    euclid_finish
  euclid_finish