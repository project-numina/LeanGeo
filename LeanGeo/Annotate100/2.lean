import Mathlib
import SystemE
import LeanGeo

open SystemE
namespace LeanGeo
/--9.5. Point $D$ outside an acute-angled triangle $ABC$ is such that $\angle ABC + \angle ABD = \angle ACB + \angle ACD = 180^{\circ}$. Prove that the center of the circumcircle of triangle $ABC$ lies on the segment
## $AD$. (6 points)-/
theorem opposingsides_inside_triangle :  ∀ (A B C I : Point) (AB BC CA AI BI CI : Line), (formTriangle A B C AB BC CA) ∧ (distinctPointsOnLine B I BI) ∧ (distinctPointsOnLine C I CI) ∧ A.opposingSides C BI ∧ B.opposingSides C AI → insideTriangle I A B C AB BC CA:= by
  euclid_intros
  sorry

theorem angleBisector_opposingsides : ∀ (A B C I : Point) (AI : Line), (distinctPointsOnLine A I AI)∧ triangle A B C ∧ ∠ I:A:B = ∠ I:A:C →  B.opposingSides C AI := by
  euclid_intros
  by_contra
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points A B as AB
  euclid_finish


theorem incenter_inside : ∀ (A B C I : Point) (AB BC CA : Line), (formTriangle A B C AB BC CA) ∧ (inCentre I A B C) → insideTriangle I A B C AB BC CA := by
  euclid_intros
  euclid_apply line_from_points A I as AI
  euclid_apply line_from_points B I as BI
  euclid_apply line_from_points C I as CI
  euclid_apply angleBisector_opposingsides A B C I AI
  euclid_apply angleBisector_opposingsides C A B I CI
  euclid_apply angleBisector_opposingsides B C A I BI
  euclid_apply opposingsides_inside_triangle A B C I AB BC CA AI BI CI
  euclid_finish
theorem exists_inCentre : ∀ (A B C: Point), triangle A B C → ∃ (I : Point), inCentre I A B C := by
  sorry

theorem exCentre_inCentre_coll : ∀ (A B C I J: Point), triangle A B C ∧ inCentre I A B C ∧ exCentre J A B C → between A I J := by
  sorry

theorem circumCentre_isCentre_circumCircle : ∀ (A B C O : Point) (Ω : Circle), triangle A B C ∧ circumCircle Ω A B C ∧ circumCentre O A B C → O.isCentre Ω := by
  euclid_intros
  sorry
theorem Numina_Geometry_1293 :
  ∀ (A B C D O : Point) (AB BC CA : Line),
    formAcuteTriangle A B C AB BC CA ∧
    circumCentre O A B C ∧
    (∠A:B:C + ∠A:B:D = ∟ + ∟) ∧
    (∠A:C:B + ∠A:C:D = ∟ + ∟) →
    between A O D := by
    euclid_intros
    euclid_assert triangle D B C
    euclid_apply exists_inCentre D B C as I
    euclid_apply line_from_points B D as BD
    euclid_apply line_from_points C D as CD
    --euclid_assert formTriangle B C D BC CD BD
    euclid_apply incenter_inside B C D I BC CD BD
    euclid_assert ∠I:B:C + ∠I:B:D = ∠ C:B:D
    have h1: ∠A:B:D = ∠A:B:C + ∠C:B:D := by
      sorry
    have h2: ∠A:C:D = ∠A:C:B + ∠B:C:D := by
      sorry
    euclid_assert ∠I:B:A = ∟
    euclid_assert ∠I:C:A = ∟
    euclid_apply exCentre_inCentre_coll D B C I A
    euclid_apply line_from_points B I as BI
    euclid_apply line_from_points C I as CI
    euclid_assert formQuadrilateral A C I B CA CI BI AB
    euclid_apply cyclic_test A C I B CA CI BI AB as Ω
    euclid_apply circumCentre_isCentre_circumCircle A B C O Ω
    euclid_apply rightAngle_diameter B I A O Ω
    euclid_finish
