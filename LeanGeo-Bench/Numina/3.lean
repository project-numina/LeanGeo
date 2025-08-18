import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--3. Let AC be the largest side of Triangle ABC. Points M and N are chosen on side AC such that AM = AB, CN = CB. Prove that if BM = BN, then Triangle ABC is isosceles.-/
theorem Numina_Geometry_1011 :
  ∀ (A B C M N : Point),
    (Triangle A B C) ∧
    (|(A─C)| > |(B─C)| ∧ |(A─C)| > |(A─B)|) ∧
    (between A M C) ∧
    (between A N C) ∧
    (|(A─M)| = |(A─B)|) ∧
    (|(C─N)| = |(C─B)|) ∧
    (|(B─M)| = |(B─N)|) →
    IsoTriangle B A C := by
  sorry
