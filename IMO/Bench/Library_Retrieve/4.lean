import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem library4: ∀ (A B C D E : Point) (Ω: Circle),
  A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ D.onCircle Ω ∧
  distinctFourPoints A B C D ∧
  between A E B ∧ between C E D → |(A─E)| * |(E─B)| = |(C─E)| * |(E─D)|:= by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points C D as CD
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points B D as BD
  have h1: ∠C:B:E = ∠A:D:E := by
    euclid_apply cyclic_eqAngle A C B D AC Ω
    euclid_apply angle_between_transfer
    euclid_finish
  have h2: ∠B:C:E = ∠D:A:E := by
    euclid_apply cyclic_eqAngle B D A C BD Ω
    euclid_apply angle_between_transfer
    euclid_finish
  euclid_apply similar_AA C B E A D E
  euclid_finish
