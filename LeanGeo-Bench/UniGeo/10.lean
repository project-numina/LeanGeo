import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem Triangle18 : ∀ (S T V R U W : Point) (ST TV VS RU UW WR : Line),
  formTriangle S T V ST TV VS ∧
  formTriangle R U W RU UW WR ∧
  ∠ S:V:T = ∠ W:R:U ∧
  ∠ V:S:T = ∠ R:W:U →
  |(S─V)| * |(R─U)| = |(T─V)| * |(R─W)|  :=
by
  euclid_intros
  euclid_apply similar_AA S V T W R U
  euclid_finish
