import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem Triangle10 : ∀ (Q S T R U V : Point) (QS ST TQ RU UV VR : Line),
  formTriangle Q S T QS ST TQ ∧
  formTriangle R U V RU UV VR ∧
  ∠ U:R:V = ∠ S:T:Q ∧
  |(R─V)| * |(S─T)|  = |(R─U)| * |(Q─T)| →
  ∠ R:U:V = ∠ Q:S:T :=
by
  euclid_intros
  euclid_apply similar_SAS U R V S T Q
  euclid_finish
