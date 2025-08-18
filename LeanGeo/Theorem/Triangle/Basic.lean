import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import LeanGeo.Theorem.Basic.Angle
import LeanGeo.Theorem.Basic.Parallel
import LeanGeo.Theorem.Basic.Construction
import LeanGeo.Theorem.Basic.Position

set_option maxHeartbeats 0
open Elements.Book1
namespace LeanGeo

theorem triangle_angle_positive : ∀(A B C : Point) , Triangle A B C → ∠A:B:C > 0 ∧ ∠A:C:B > 0 ∧ ∠C:A:B > 0 := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem PythagoreanTheorem : ∀ (a b c: Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| :=
by
  euclid_intros
  euclid_apply proposition_47
  euclid_finish

theorem PythagoreanTheorem_point : ∀ (a b c: Point), (Triangle a b c) ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by
  euclid_intros
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points b c as BC
  euclid_apply line_from_points c a as CA
  have h_form_tri : formTriangle a b c AB BC CA := by
    euclid_finish
  euclid_apply PythagoreanTheorem a b c AB BC CA
  euclid_finish

theorem PythagoreanTheorem_to_acuteAngle : ∀ (A B C : Point), Triangle A B C ∧ ∠B:A:C < ∟ → |(A─B)| * |(A─B)| + |(A─C)| * |(A─C)| > |(C─B)| * |(C─B)| := by
  euclid_intros
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply exists_foot B AC as D
  euclid_apply line_from_points D B as BD
  have h_0 : LiesOnRay A C D := by
    by_contra
    euclid_apply proposition_17 B D A BD AC AB
    by_cases D = A
    · euclid_finish
    · euclid_apply coll_supp_angles B D A C
      euclid_finish
  euclid_apply PythagoreanTheorem D B A BD AB AC
  by_cases D = C
  · euclid_finish
  · euclid_apply PythagoreanTheorem D B C BD BC AC
    euclid_finish

theorem PythagoreanTheorem_to_obtuseAngle : ∀ (A B C : Point), Triangle A B C ∧ ∠B:A:C > ∟ → |(A─B)| * |(A─B)| + |(A─C)| * |(A─C)| < |(C─B)| * |(C─B)| := by
  euclid_intros
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply exists_foot B AC as D
  euclid_apply line_from_points D B as BD
  have h_0 : between D A C := by
    euclid_apply proposition_17 B D A BD AC AB
    euclid_finish
  euclid_apply PythagoreanTheorem D B A BD AB AC
  euclid_apply PythagoreanTheorem D B C BD BC AC
  euclid_finish

theorem triangle_ex_angle_eq : ∀ (a b c d: Point), (Triangle a b c) ∧ (between a b d) → ∠d:b:c = ∠b:c:a + ∠c:a:b := by
  euclid_intros
  euclid_apply triangle_angles_sum a b c
  euclid_apply coll_supp_angles c a b d
  euclid_finish

theorem acuteTriangle_foot_between : ∀(A B C D: Point) (BC: Line), distinctPointsOnLine B C BC ∧ Foot A D BC ∧ ∠A:B:C < ∟ ∧ ∠ A:C:B < ∟ → between B D C := by
  euclid_intros
  have h2: ¬(between D B C):= by
    by_contra
    euclid_apply triangle_ex_angle_eq D B A C
    euclid_finish
  have h3: ¬(between B C D):= by
    by_contra
    euclid_apply triangle_ex_angle_eq D C A B
    euclid_finish
  euclid_finish

theorem obtuseTriangle_foot_between: ∀(A B C D: Point) (BC : Line), distinctPointsOnLine B C BC ∧ Foot A D BC ∧ ∠A:B:C > ∟ → between D B C := by
  euclid_intros
  have h2: ¬(between B C D):= by
    by_contra
    euclid_apply coll_angles_eq B C D A
    euclid_apply triangle_angles_sum A B D
    euclid_finish
  have h3: ¬(between B D C):= by
    by_contra
    euclid_apply coll_angles_eq B D C A
    euclid_apply triangle_angles_sum A B D
    euclid_finish
  have h4: D ≠ C := by
    euclid_apply triangle_angles_sum A B D
    euclid_finish
  euclid_finish

theorem congruentTriangles_SAS : ∀ (A B C D E F : Point), Triangle A B C ∧ Triangle D E F ∧ |(A─B)| = |(D─E)| ∧ ∠ A:B:C = ∠ D:E:F ∧ |(B─C)| = |(E─F)| → CongruentTriangles A B C D E F := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points C A as CA
  euclid_apply line_from_points D E as DE
  euclid_apply line_from_points E F as EF
  euclid_apply line_from_points F D as FD
  euclid_apply proposition_4 B A C E D F AB CA BC DE FD EF
  euclid_finish

theorem congruentTriangles_SSS : ∀ (A B C D E F : Point), Triangle A B C ∧ Triangle D E F ∧ |(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(C─A)| = |(F─D)| → CongruentTriangles A B C D E F := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points C A as CA
  euclid_apply line_from_points D E as DE
  euclid_apply line_from_points E F as EF
  euclid_apply line_from_points F D as FD
  euclid_apply proposition_8 A B C D E F AB BC CA DE EF FD
  euclid_apply congruentTriangles_SAS B A C E D F
  euclid_finish

theorem congruentTriangles_ASA : ∀ (A B C D E F : Point), Triangle A B C ∧ Triangle D E F ∧ |(A─B)| = |(D─E)| ∧ ∠ A:B:C = ∠ D:E:F ∧ ∠ B:A:C = ∠ E:D:F → CongruentTriangles A B C D E F := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points C A as CA
  euclid_apply line_from_points D E as DE
  euclid_apply line_from_points E F as EF
  euclid_apply line_from_points F D as FD
  euclid_apply proposition_26 C B A F E D BC AB CA EF DE FD
  euclid_finish

theorem congruentTriangles_AAS : ∀ (A B C D E F : Point), Triangle A B C ∧ Triangle D E F ∧ |(A─B)| = |(D─E)| ∧ ∠ A:B:C = ∠ D:E:F ∧ ∠ A:C:B = ∠ D:F:E → CongruentTriangles A B C D E F := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points C A as CA
  euclid_apply line_from_points D E as DE
  euclid_apply line_from_points E F as EF
  euclid_apply line_from_points F D as FD
  euclid_apply proposition_26 A B C D E F AB BC CA DE EF FD
  euclid_finish

--nlinarith makes it very slow in this proof.
theorem congruentTriangles_HL : ∀ (a b c d e f : Point) ,  RightTriangle a b c ∧ RightTriangle d e f ∧ |(a─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)| → CongruentTriangles a b c d e f := by
  euclid_intros
  euclid_apply PythagoreanTheorem_point a b c
  euclid_apply PythagoreanTheorem_point d e f
  have h1 : |(a─b)| = |(d─e)| := by
    euclid_finish
  have h2 : |(b─c)| = |(e─f)| := by
    euclid_finish
  have h4 : |(e─f)| * |(e─f)| = |(d─e)| * |(d─e)| + |(d─f)| * |(d─f)| := by
    euclid_finish
  have h3 : |(b─c)| * |(b─c)| = |(a─b)| * |(a─b)| + |(a─c)| * |(a─c)| := by
    euclid_finish
  have h5 : |(a─c)| = |(d─f)| := by
    rw [h1, h2] at h3
    have h6 : |(a─c)| * |(a─c)| = |(d─f)| * |(d─f)| := by linarith
    have h7 : |(a─c)| > 0 := by euclid_finish
    have h8 : |(d─f)| > 0 := by euclid_finish
    euclid_finish
  euclid_apply congruentTriangles_SSS a b c d e f
  euclid_finish

theorem triangleMidsegment_parallel_base : ∀ (a b c d e : Point) (AB BC CA DE: Line), formTriangle a b c AB BC CA ∧ distinctPointsOnLine d e DE ∧ MidPoint a d b ∧ MidPoint a e c →  ¬ BC.intersectsLine DE:= by
  euclid_intros
  euclid_apply similar_SAS d a e b a c
  euclid_apply parallel_if_eq_alternateExteriorAngles
  euclid_finish

theorem triangleMidsegment_half_len : ∀ (a b c d e : Point), Triangle a b c ∧ MidPoint a d b ∧ MidPoint a e c → |(b─c)| = |(d─e)| * 2:= by
  euclid_intros
  euclid_apply line_from_points
  euclid_apply similar_SAS d a e b a c
  have h1: |(b─a)| = |(d─a)| * 2 := by
    euclid_apply midpoint_half_len
    euclid_finish
  euclid_finish

theorem insideTriangle_angles_sum_eq_fullAngle : ∀ (A B C O : Point) (AB BC CA: Line), formTriangle A B C AB BC CA ∧ InsideTriangle O A B C AB BC CA → ∠A:O:C + ∠ C:O:B + ∠ B:O:A = ∟ + ∟ +  ∟ + ∟ := by
  euclid_intros
  euclid_apply triangle_angles_sum A O B
  euclid_apply triangle_angles_sum C O B
  euclid_apply triangle_angles_sum A O C
  euclid_apply triangle_angles_sum A B C
  euclid_finish

theorem rightTriangle_midLine_eq_half_hypotenuse: ∀ (A B C D: Point), RightTriangle A B C ∧ MidPoint B D C → |(A─D)| = |(B─D)| := by
  euclid_intros
  euclid_apply exists_midpoint A C as E
  euclid_apply line_from_points A C as CA
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points D E as DE
  have h1: ∠C:E:D = ∟ := by
    euclid_apply triangleMidsegment_parallel_base C A B E D  CA AB BC DE
    euclid_apply parallel_imp_eq_alternateExteriorAngles  D E B A C DE AB CA
    euclid_finish
  euclid_apply congruentTriangles_SAS D E A D E C
  euclid_finish

theorem rightTriangle_hypotenuse_gt_leg : ∀(A B C : Point), RightTriangle A B C → |(B─C)| > |(A─B)| ∧  |(B─C)| > |(A─C)| := by
  euclid_intros
  euclid_apply PythagoreanTheorem_point A B C
  euclid_finish

theorem insideTriangle_angles_sum: ∀ (A B C O : Point) (AB BC CA: Line), formTriangle A B C AB BC CA ∧ InsideTriangle O A B C AB BC CA → ∠B:O:C = ∠O:B:A + ∠B:A:C + ∠A:C:O := by
  euclid_intros
  euclid_apply triangle_angles_sum A O B
  euclid_apply triangle_angles_sum C O B
  euclid_apply triangle_angles_sum A O C
  euclid_apply triangle_angles_sum A B C
  euclid_finish

theorem similarTriangles_with_opposite_angles: ∀ (a b c d e: Point),¬ Coll a b c ∧ (between a c e) ∧ (between b c d) ∧ |(e─c)| * |(a─c)| = |(b─c)| * |(c─d)| → SimilarTriangles a c b d c e := by
  euclid_intros
  euclid_apply line_from_points a c as AC
  euclid_apply line_from_points b d as BD
  euclid_assert Triangle a b c
  euclid_apply eq_opposite_angles a b c d e
  euclid_apply similar_SAS a c b d c e
  euclid_finish

theorem similarTriangles_with_same_angle: ∀ (a b c d e: Point),¬ Coll a b c ∧ (between e a b) ∧ (between e c d) ∧ |(e─a)| * |(e─b)| = |(e─c)| * |(e─d)| → SimilarTriangles e a c e d b := by
  euclid_intros
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points c d as CD
  euclid_assert Triangle e a c
  have h1: ∠a:e:c = ∠d:e:b := by
    euclid_apply coll_angles_eq
    euclid_finish
  euclid_apply similar_SAS a e c d e b
  euclid_finish

theorem similarTriangles_perm : ∀ (A B C D E F : Point), SimilarTriangles A B C D E F → SimilarTriangles A C B D F E ∧ SimilarTriangles B A C E D F ∧ SimilarTriangles B C A E F D ∧ SimilarTriangles C A B F D E ∧ SimilarTriangles C B A F E D := by
  euclid_intros
  euclid_apply similar_AA A C B D F E
  euclid_apply similar_AA B A C E D F
  euclid_apply similar_AA B C A E F D
  euclid_apply similar_AA C A B F D E
  euclid_apply similar_AA C B A F E D
  euclid_finish

theorem similarTriangles_trans :  ∀ (A B C D E F G H I : Point), SimilarTriangles A B C D E F ∧ SimilarTriangles D E F G H I → SimilarTriangles A B C G H I := by
  euclid_intros
  euclid_apply similar_AA A B C G H I
  euclid_finish

theorem similarTriangles_from_rotary_similarTriangles : ∀ (A B C D E : Point), SimilarTriangles A B C A D E ∧ (¬ Coll A B D ∨ ¬ Coll A C E) ∧ ∠B:A:D = ∠C:A:E → SimilarTriangles A B D A C E := by
  euclid_intros
  have h_0 : ¬ Coll A B D ∧ ¬ Coll A C E := by
    by_cases Coll A B D
    · euclid_apply nondegenerate_angle_if C A E
      euclid_apply nondegenerate_angle_onlyif B A D
      euclid_finish
    · euclid_apply nondegenerate_angle_if B A D
      euclid_apply nondegenerate_angle_onlyif C A E
      euclid_finish
  euclid_apply similar_SAS B A D C A E
  euclid_apply similarTriangles_perm B A D C A E
  euclid_finish

theorem parallel_bases_imp_similarTriangles : ∀ (A B C D E: Point) (BC DE : Line), Triangle A B C ∧ distinctPointsOnLine B C BC ∧ distinctPointsOnLine D E DE ∧ ¬ BC.intersectsLine DE ∧ Coll A B D ∧ Coll A C E → SimilarTriangles A B C A D E := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points A C as AC
  have h1: between A D B ∨ between A B D ∨ between B A D ∨ D = B := by
    euclid_finish
  rcases h1 with h2|h3|h4|h5
  · euclid_apply parallel_imp_eq_alternateExteriorAngles E D C B A DE BC AB
    euclid_apply similar_AA A D E A B C
    euclid_finish
  · euclid_apply parallel_imp_eq_alternateExteriorAngles C B E D A BC DE AB
    euclid_apply similar_AA A D E A B C
    euclid_finish
  · euclid_apply parallel_imp_eq_alternateAngles BC DE AB B D C E
    have h6: ∠ E:A:D = ∠B:A:C := by
      euclid_apply eq_opposite_angles D E A C B
      euclid_finish
    euclid_apply similar_AA A D E A B C
    euclid_finish
  · euclid_finish

theorem triangle_gt_side_gt_angle : ∀ (a b c : Point) ,
  Triangle a b c ∧ (|(a─c)| > |(a─b)|) →
  (∠ a:b:c > ∠ b:c:a) :=
by
  euclid_intros
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points b c as BC
  euclid_apply line_from_points c a as CA
  euclid_apply proposition_18 a b c AB BC CA
  euclid_finish

theorem triangle_parallel_bases_eq_ratio: ∀ (A B C D E F G: Point) (BC DE : Line), Triangle A B C ∧ distinctPointsOnLine B C BC ∧ distinctPointsOnLine D E DE ∧ ¬ BC.intersectsLine DE ∧ Coll A B D ∧ Coll A C E ∧ F.onLine BC ∧ G.onLine DE ∧ Coll A G F ∧ F ≠ B ∧ F ≠ C ∧ G ≠ D ∧ G ≠ E → |(D─G)| * |(B─C)|  =|(D─E)| *|(B─F)| := by
  euclid_intros
  euclid_apply parallel_bases_imp_similarTriangles A B C D E BC DE
  euclid_apply parallel_bases_imp_similarTriangles A B F D G BC DE
  have h1: |(D─G)| * |(A─B)| = |(B─F)| * |(A─D)| := by
    euclid_finish
  have h2: |(D─E)| * |(A─B)| = |(B─C)| * |(A─D)| := by
    euclid_finish
  have h3: |(A─B)| * |(A─D)| > 0 := by
    euclid_finish
  have h5: |(D─G)| * |(B─C)| * (|(A─B)| * |(A─D)|) =|(D─E)| * |(B─F)| * (|(A─B)| * |(A─D)|) := by
    calc
      _ = (|(D─G)| * |(A─B)|) * (|(B─C)| * |(A─D)|) := by linarith
      _ = (|(B─F)| * |(A─D)|) * (|(D─E)| * |(A─B)|) := by rw[h1,h2]
      _ = _ := by linarith
  euclid_finish

end LeanGeo
