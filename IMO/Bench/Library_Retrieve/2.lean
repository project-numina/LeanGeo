import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem library2 : ∀ (A B C D: Point) (AB:Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ A.onCircle Ω ∧ B.onCircle Ω ∧  C.onCircle Ω ∧ ∠B:C:A + ∠B:D:A = ∟ + ∟ ∧ C.opposingSides D AB → D.onCircle Ω:= by
  euclid_intros
  euclid_apply exists_point_opposing_arc A B C AB Ω as E
  have h1:∠A:D:B = ∠A:E:B := by
    euclid_apply cyclic_complementary A B C E AB Ω
    euclid_finish
  euclid_apply eqAngle_cyclic A B E D AB Ω
  euclid_finish
