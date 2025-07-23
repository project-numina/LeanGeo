import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem Congruent15 : ∀ (S T U V : Point) (ST TU UV SV SU : Line),
  formTriangle S T U ST TU SU ∧
  formTriangle S U V SU UV SV ∧
  V.opposingSides T SU ∧
  ∠ U:V:S = ∟ ∧
  ∠ U:S:V = ∠ S:U:T ∧
  ∠ S:T:U = ∟ →
  |(U─V)| = |(S─T)| :=
by
  euclid_intros
  euclid_apply congruentTriangles_AAS U S V S U T
  euclid_finish
