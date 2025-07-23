import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem day156 : ∀ (A B M N O P : Point) (AB NP OP : Line) (C: Circle),
Diameter A B O C ∧ P.onCircle C ∧ O.isCentre C∧ ∠A:O:P = ∟ ∧ between A M O ∧ between N M P ∧ N.onCircle C ∧
distinctPointsOnLine A B AB ∧ distinctPointsOnLine N P NP ∧ distinctPointsOnLine O P OP →    |(A─B)| * |(A─B)| = 2* |(P─M)| * |(N─P)| := by
  sorry
