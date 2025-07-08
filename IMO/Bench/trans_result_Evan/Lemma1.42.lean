import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--(Three Tangents). Let ABC be an acute triangle. Let BE and CF be altitudes of △ABC, and denote by M the midpoint of BC. Prove that ME, MF are all tangents to the circumcircle of AEF.
theorem Lemma1_42 :
  ∀ (A B C I X Y Z D E F : Point) (AB BC CA XY YZ ZX : Line) (Ω : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    circumCircle Ω A B C ∧
    X.onCircle Ω ∧ |(X─B)| = |(X─C)| ∧ opposingSides X A BC ∧
    Y.onCircle Ω ∧ |(Y─C)| = |(Y─A)| ∧ opposingSides Y B CA ∧
    Z.onCircle Ω ∧ |(Z─A)| = |(Z─B)| ∧ opposingSides Z C AB ∧
    inCentre I A B C ∧
    foot X D YZ ∧
    foot Y E ZX ∧
    foot Z F XY ∧
    coll X I D ∧
    coll Y I E ∧
    coll Z I F →
  orthoCentre I X Y Z D E F YZ ZX XY := by
  sorry