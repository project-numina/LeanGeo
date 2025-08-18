import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem Similar4 : ∀ (E F G H I : Point) (EF GH EG FH : Line),
  formTriangle E F I EF FH EG ∧
  formTriangle G H I GH FH EG ∧
  between E I G ∧
  between H I F ∧
  ∠ H:G:I = ∠ F:E:I →
  similarTriangle E I F G I H :=
by
  euclid_intros
  have : ∠ E:I:F = ∠ G:I:H := by
    euclid_apply opposite_angles_same H G I E F
    euclid_finish
  euclid_apply similar_AA G I H E I F
  euclid_finish
