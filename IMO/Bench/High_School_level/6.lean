import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem day156 : ∀ (A B M N O P : Point) (AB NP OP : Line) (C: Circle),
diameter A B O C ∧ P.onCircle C ∧ O.isCentre C∧ ∠A:O:P = ∟ ∧ between A M O ∧ between N M P ∧ N.onCircle C ∧
distinctPointsOnLine A B AB ∧ distinctPointsOnLine N P NP ∧ distinctPointsOnLine O P OP →    |(A─B)| * |(A─B)| = 2* |(P─M)| * |(N─P)| := by
  euclid_intros
  euclid_assert P ≠ O
  euclid_assert P ≠ M
  by_cases (O = M)
  · sorry
  · euclid_assert triangle P O M
    euclid_apply angle_between_transfer A M O P
    euclid_assert ∠M:O:P = ∟
    euclid_apply pythagorean_point O P M
    euclid_apply intersecting_chord A B P N M C
    euclid_assert |(P─N)| = |(P─M)| + |(M─N)|
    euclid_assert |(A─M)| + |(O─M)|= |(A─O)|
    euclid_assert |(M─B)| = |(O─M)| + |(B─O)|
    euclid_assert |(A─O)| = |(P─O)|
    euclid_assert |(B─O)| = |(P─O)|
    have h1: |(P─M)| * (|(P─M)| + |(M─N)|) = |(P─M)| * |(P─N)| := by
      simp_all
    have h2: |(P─M)| * |(P─N)| = 2 * |(P─O)| * |(P─O)| := by
      calc
        |(P─M)| * |(P─N)| = |(P─M)| * (|(P─M)| + |(M─N)|) := by simp_all
        _ = |(P─M)| * |(P─M)| + |(P─M)| * |(M─N)|:= by ring
        _ = |(P─O)| * |(P─O)| + |(O─M)| * |(O─M)| + |(A─M)| * |(M─B)| := by simp_all
        _ = |(P─O)| * |(P─O)| + |(O─M)| * |(O─M)| + (|(A─O)| - |(O─M)|) * |(M─B)| := by sorry
        _ = |(P─O)| * |(P─O)| + |(O─M)| * |(O─M)| + (|(A─O)| - |(O─M)|) * (|(B─O)|+ |(O─M)|) := by sorry
        _ = |(P─O)| * |(P─O)| + |(O─M)| * |(O─M)| + (|(P─O)| - |(O─M)|) * (|(P─O)|+ |(O─M)|) := by simp_all
        _ = _ := by ring
    euclid_assert |(A─B)| = 2 * |(P─O)|
    sorry
