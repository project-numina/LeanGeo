import SystemE
import LeanGeo.Abbre
namespace LeanGeo

axiom triangle_area_foot :∀ (a b c d: Point) (BC: Line),b.onLine BC ∧ c.onLine BC ∧ (triangle a b c) ∧ foot a d BC → (△a:b:c).area = |(a─d)| * |(b─c)|/2

axiom triangle_inequality : ∀ (a b c : Point), triangle a b c →
|(a─b)| < |(b─c)| + |(c─a)|

axiom triangle_inequality_le : ∀ (a b c : Point),
|(a─b)| ≤  |(b─c)| + |(c─a)|

axiom threePoints_existCircle : ∀ (A B C : Point),
  triangle A B C →
  ∃ (Ω : Circle),
    (A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω)

axiom exists_centre : ∀ (O: Circle), ∃ (C : Point), C.isCentre O

axiom rightAngle_eq_pi_div_two : ∟ = Real.pi / 2

axiom rightTriangle_sin : ∀ (A B C : Point), rightTriangle A B C → Real.sin (∠A:B:C) = |(A─C)| / |(B─C)|

axiom rightTriangle_cos : ∀ (A B C : Point), rightTriangle A B C → Real.cos (∠A:B:C) = |(A─B)| / |(B─C)|

axiom similar_AA : ∀ (A B C D E F : Point), triangle A B C ∧ triangle D E F ∧  ∠ A:B:C = ∠ D:E:F ∧ ∠ B:A:C = ∠ E:D:F → similarTriangle A B C D E F

axiom similar_SAS : ∀ (A B C D E F : Point), triangle A B C ∧ triangle D E F ∧  ∠ A:B:C = ∠ D:E:F ∧ |(A─B)| * |(E─F)| = |(B─C)| * |(D─E)| → similarTriangle A B C D E F

axiom similar_SSS : ∀ (A B C D E F : Point), triangle A B C ∧ triangle D E F ∧ |(A─B)| * |(E─F)| = |(B─C)| * |(D─E)| ∧ |(B─C)| * |(F─D)| = |(C─A)| * |(E─F)| → similarTriangle A B C D E F

end LeanGeo
