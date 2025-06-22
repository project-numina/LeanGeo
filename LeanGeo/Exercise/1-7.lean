import SystemE
import LeanGeo

open SystemE
namespace LeanGeo
--Problem 1.7. Let O and H denote the circumcenter and orthocenter of an acute ΔA B C, respectively, as in Figure 1.1D. Show that ∠B A H = ∠C A O. Hints: 540 373
theorem problem_1_7 : ∀ (A B C O H : Point) (AB BC CA : Line),
  (formAcuteTriangle A B C AB BC CA) ∧
  (circumCentre O A B C) ∧
  (perpPoint A H B C) ∧
  (perpPoint B H A C) →
  ∠B:A:H = ∠C:A:O := by
sorry
