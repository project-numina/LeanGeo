import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem Quadrilateral11: ∀ (S T U V : Point) (ST UV SU TV: Line),
  formQuadrilateral S T V U ST TV UV SU ∧
  |(U─V)| = |(S─U)| ∧
 ∠ S:U:T = ∠ V:U:T  → |(S─T)| = |(T─V)|:=
by
  euclid_intros
  euclid_apply congruentTriangles_SAS S U T V U T
  euclid_finish
