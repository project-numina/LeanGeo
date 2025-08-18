import SystemE
import LeanGeo.Abbre
import Book
open Elements.Book1
namespace LeanGeo

axiom triangle_area_foot :∀ (a b c d: Point) (BC: Line),b.onLine BC ∧ c.onLine BC ∧ (Triangle a b c) ∧ Foot a d BC → (△a:b:c).area = |(a─d)| * |(b─c)|/2

axiom threePoints_existCircle : ∀ (A B C : Point),
  Triangle A B C →
  ∃ (Ω : Circle),
    (A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω)

axiom exists_centre : ∀ (O: Circle), ∃ (C : Point), C.isCentre O

axiom rightAngle_eq_pi_div_two : ∟ = Real.pi / 2

axiom rightTriangle_sin : ∀ (A B C : Point), RightTriangle A B C → Real.sin (∠A:B:C) = |(A─C)| / |(B─C)|

axiom rightTriangle_cos : ∀ (A B C : Point), RightTriangle A B C → Real.cos (∠A:B:C) = |(A─B)| / |(B─C)|

axiom similar_AA : ∀ (A B C D E F : Point), Triangle A B C ∧ Triangle D E F ∧  ∠ A:B:C = ∠ D:E:F ∧ ∠ B:A:C = ∠ E:D:F → SimilarTriangles A B C D E F

axiom similar_SAS : ∀ (A B C D E F : Point), Triangle A B C ∧ Triangle D E F ∧  ∠ A:B:C = ∠ D:E:F ∧ |(A─B)| * |(E─F)| = |(B─C)| * |(D─E)| → SimilarTriangles A B C D E F

axiom similar_SSS : ∀ (A B C D E F : Point), Triangle A B C ∧ Triangle D E F ∧ |(A─B)| * |(E─F)| = |(B─C)| * |(D─E)| ∧ |(B─C)| * |(F─D)| = |(C─A)| * |(E─F)| → SimilarTriangles A B C D E F

end LeanGeo
