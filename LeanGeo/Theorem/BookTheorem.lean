
import SystemE

namespace LeanGeo
theorem Book_proposition_33 : ∀ (a b c d : Point) (AB CD AC BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧
  (a.sameSide c BD) ∧ ¬(AB.intersectsLine CD) ∧ |(a─b)| = |(c─d)| →
  AC ≠ BD ∧ ¬(AC.intersectsLine BD) ∧ |(a─c)|= |(b─d)| :=
by
sorry




theorem Book_proposition_5 : ∀ (a b c d e : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) ∧
  (between a b d) ∧ (between a c e) →
  (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e) :=
by
sorry


theorem Book_isoTriangle_eqAngle : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) →
  (∠ a:b:c = ∠ a:c:b) :=
by
sorry




theorem Book_vertical_eqAngle : ∀ (a b c d e : Point) (AB CD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ e.onLine AB ∧ e.onLine CD ∧
  CD ≠ AB ∧ (between d e c) ∧ (between a e b) →
  (∠ a:e:c = ∠ d:e:b) ∧ (∠ c:e:b = ∠ a:e:d) :=
by
sorry




theorem Book_adjacentAngle_straight : ∀ (a b c d : Point) (AB BC BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧ distinctPointsOnLine b d BD ∧ (c.opposingSides d AB) ∧
  (∠ a:b:c + ∠ a:b:d) = ∟ + ∟ →
  BC = BD :=
by
sorry




theorem Book_perpBisector_oppossingSide : ∀ (a b c d : Point) (AB AC CB AD DB : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine a c AC ∧ distinctPointsOnLine c b CB ∧
  distinctPointsOnLine a d AD ∧ distinctPointsOnLine d b DB ∧  c ≠ d ∧
  (|(a─c)| = |(a─d)|) ∧ (|(c─b)| = |(d─b)|) → c.opposingSides d AB :=
by
sorry




theorem Book_extAngle_gt_intAngle : ∀ (a b c d : Point) (AB BC AC: Line),
  formTriangle a b c AB BC AC ∧ (between b c d) →
  (∠ a:c:d > ∠ c:b:a) ∧ (∠ a:c:d > ∠ b:a:c) :=
by
sorry




theorem Book_exists_foot : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(c.onLine AB) →
  exists h : Point, h.onLine AB ∧ (∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟) :=
by
sorry




theorem Book_pythagoras_converse : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| →
  ∠ b:a:c = ∟ :=
by
sorry




theorem Book_aas_congruence : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (∠ a:b:c = ∠ d:e:f) ∧ (∠ b:c:a = ∠ e:f:d) ∧ (|(b─c)| = |(e─f)| ∨ |(a─b)| = |(d─e)|) →
  (|(a─b)| = |(d─e)|) ∧ (|(b─c)| = |(e─f)|) ∧ (|(a─c)| = |(d─f)|) ∧ (∠ b:a:c = ∠ e:d:f) :=
by
sorry




theorem Book_exists_angle_bisector : ∀ (a b c : Point) (AB AC : Line),
  formRectilinearAngle b a c AB AC ∧ AB ≠ AC →
  ∃ f : Point, f ≠ a ∧ (∠ b:a:f = ∠ c:a:f) :=
by
sorry


theorem Book_exists_angle_bisector_ss : ∀ (a b c : Point) (AB AC : Line),
  formRectilinearAngle b a c AB AC ∧ AB ≠ AC →
  ∃ f : Point, (f.sameSide c AB) ∧ (f.sameSide b AC) ∧ (∠ b:a:f = ∠ c:a:f) :=
by
sorry





theorem Book_parallel_angle_tranverse : ∀ (a b d g h : Point) (AB CD GH : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine g h GH ∧
  (between a g b) ∧ (b.sameSide d GH) ∧ ¬(AB.intersectsLine CD) →
  ∠ a:g:h = ∠ g:h:d ∧ ∠ b:g:h + ∠ g:h:d = ∟ + ∟ :=
by
sorry


theorem Book_angle_tranverse_parallel : ∀ (a d g h : Point) (AB CD GH : Line),
  distinctPointsOnLine a g AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine g h GH ∧
  a.opposingSides d GH ∧ ¬(AB.intersectsLine CD) →
  ∠ a:g:h = ∠ g:h:d :=
by
sorry


theorem Book_parrallel_angle_tranverse_2 : ∀ (b d e g h : Point) (AB CD EF : Line),
  distinctPointsOnLine g b AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine e h EF ∧
  between e g h ∧ b.sameSide d EF ∧ ¬(AB.intersectsLine CD) →
  ∠ e:g:b = ∠ g:h:d :=
by
sorry


theorem Book_parrallel_angle_tranverse_3 : ∀ (b d g h : Point) (AB CD EF : Line),
  distinctPointsOnLine g b AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine g h EF ∧
  b.sameSide d EF ∧ ¬(AB.intersectsLine CD) →
  ∠ b:g:h + ∠ g:h:d = ∟ + ∟ :=
by
sorry




theorem Book_pythagoras : ∀ (a b c: Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| :=
by
sorry




theorem Book_exists_square_on_segment : ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB →
  ∃ (d e : Point) (DE AD BE : Line), formParallelogram d e a b DE AB AD BE ∧
  |(d─e)| = |(a─b)| ∧ |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧
  (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟) :=
by
sorry


theorem Book_exists_square_on_segment_opposite : ∀ (a b x : Point) (AB : Line), ¬(x.onLine AB) ∧ distinctPointsOnLine a b AB →
  ∃ (d e : Point) (DE AD BE : Line), d.opposingSides x AB ∧ formParallelogram d e a b DE AB AD BE ∧
  |(d─e)| = |(a─b)| ∧ |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧
  (∠ b:a:d : ℝ) = ∟ ∧ (∠ a:d:e : ℝ) = ∟ ∧ (∠ a:b:e : ℝ) = ∟ ∧ (∠ b:e:d : ℝ) = ∟ :=
by
sorry




theorem Book_sas_congruence : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ (∠ b:a:c = ∠ e:d:f) →
  |(b─c)| = |(e─f)| ∧ (∠ a:b:c = ∠ d:e:f) ∧ (∠ a:c:b = ∠ d:f:e) :=
by
sorry




theorem Book_enangle_isosceles : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c = ∠ a:c:b) →
  |(a─b)| = |(a─c)| :=
by
sorry




theorem Book_parallelogram_area_decompose : ∀ (a b c d e₁ e₂ e₃ : Point) (AB BC CD AD DB E₁₂ E₂₃ : Line),
  formTriangle a b d AB DB AD ∧ formTriangle b c d BC CD DB ∧ a.opposingSides c DB ∧
  formRectilinearAngle e₁ e₂ e₃ E₁₂ E₂₃ ∧ ∠ e₁:e₂:e₃ > 0 ∧ ∠ e₁:e₂:e₃ < ∟ + ∟ →
  ∃ (f l k m : Point) (FL KM FK LM : Line), formParallelogram f l k m FL KM FK LM ∧
  (∠ f:k:m = ∠ e₁:e₂:e₃) ∧ (Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c) :=
by
sorry




theorem Book_parallelogram_reshape_eqArea: ∀ (a b c d e f g h : Point) (AH BG AB CD EF HG : Line),
  formParallelogram a d b c AH BG AB CD ∧ formParallelogram e h f g AH BG EF HG ∧
  |(b─c)| = |(f─g)| ∧ (between a d h) ∧ (between a e h) →
  Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:f:h + Triangle.area △ h:f:g :=
by
sorry




theorem Book_equal_area_parallel : ∀  (a b c d e : Point) (AB BC AC CD DE AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d c e CD BC DE ∧ a.sameSide d BC ∧ b ≠ e ∧ |(b─c)| = |(c─e)| ∧
  distinctPointsOnLine a d AD ∧ (Triangle.area △ a:b:c = Triangle.area △ d:c:e) →
  ¬(AD.intersectsLine BC) :=
by
sorry




theorem Book_internal_angle_gt_side_lt : ∀ (a b c d : Point) (AB BC AC BD DC : Line),
  formTriangle a b c AB BC AC ∧ (a.sameSide d BC) ∧ (c.sameSide d AB) ∧ (b.sameSide d AC) ∧
  distinctPointsOnLine b d BD ∧ distinctPointsOnLine d c DC →
  (|(b─d)| + |(d─c)| < |(b─a)| + |(a─c)|) ∧ (∠ b:d:c > ∠ b:a:c) :=
by
sorry




theorem Book_parallel_tranverse : ∀ (AB CD EF : Line),
  AB ≠ CD ∧ CD ≠ EF ∧ EF ≠ AB ∧ ¬(AB.intersectsLine EF) ∧ ¬(CD.intersectsLine EF) →
  ¬(AB.intersectsLine CD) :=
by
sorry




theorem Book_internal_angleSum_lt_straight : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC →
  ∠ a:b:c + ∠ b:c:a < ∟ + ∟ :=
by
sorry





theorem Book_parallel_eqArea : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ distinctPointsOnLine a d AD ∧
  ¬(AD.intersectsLine BC) →
  Triangle.area △ a:b:c = Triangle.area △ d:b:c :=
by
sorry




theorem Book_SSS_congrent : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ |(b─c)| = |(e─f)| →
  ∠ b:a:c = ∠ e:d:f :=
by
sorry




theorem Book_exists_eqTriangle : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| :=
by
sorry


theorem Book_exists_eqTriangle_opposite : ∀ (a b x : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(x.onLine AB) →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| ∧ (c.opposingSides x AB) :=
by
sorry




theorem Book_parallel_area_partition : ∀ (a b c d e f g h k : Point) (AD BC AB CD AC EF GH : Line),
  formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC ∧ k.onLine AC ∧
  between a h d ∧ formParallelogram a h e k AD EF AB GH ∧ formParallelogram k f g c EF BC GH CD →
  (Triangle.area △ e:b:g + Triangle.area △ e:g:k = Triangle.area △ h:k:f + Triangle.area △ h:f:d) :=
by
sorry




theorem Book_exists_triangle : ∀ (a a' b b' c c' : Point) (A B C : Line),
  distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧
  (|(a─a')| + |(b─b')| > |(c─c')|) ∧
  (|(a─a')| + |(c─c')| > |(b─b')|) ∧
  (|(b─b')| + |(c─c')| > |(a─a')|) →
  ∃ (k f g : Point), (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|) :=
by
sorry


theorem Book_exists_triangle_2 : ∀ (a a' b b' c c' f e : Point) (A B C FE : Line),
  distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧ distinctPointsOnLine f e FE ∧
  (|(a─a')| + |(b─b')| > |(c─c')|) ∧
  (|(a─a')| + |(c─c')| > |(b─b')|) ∧
  (|(b─b')| + |(c─c')| > |(a─a')|) →
  ∃ (k g : Point), g.onLine FE ∧ ¬(between g f e) ∧
  (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|) :=
by
sorry


theorem Book_exists_triangle_3 : ∀ (a a' b b' c c' f e x : Point) (A B C FE : Line),
  distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧ distinctPointsOnLine f e FE ∧ ¬(x.onLine FE) ∧
  (|(a─a')| + |(b─b')| > |(c─c')|) ∧
  (|(a─a')| + |(c─c')| > |(b─b')|) ∧
  (|(b─b')| + |(c─c')| > |(a─a')|) →
  ∃ (k g : Point), g.onLine FE ∧ ¬(between g f e) ∧ (k.sameSide x FE) ∧
  (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|) :=
by
sorry




theorem Book_exists_perpLine_from_point_between : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  exists f : Point, ¬(f.onLine AB) ∧ (∠ a:c:f = ∟) :=
by
sorry


theorem Book_exists_perpLine_from_point_between_opposite : ∀ (a b c x : Point) (AB : Line),
  (distinctPointsOnLine a b AB) ∧ (between a c b) ∧ ¬(x.onLine AB) →
  exists f : Point, (f.sameSide x AB) ∧ (∠ a:c:f = ∟) :=
by
sorry


theorem Book_exists_perpLine_from_point : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  exists (f : Point), ¬(f.onLine AB) ∧ (∠ f:a:b = ∟) :=
by
sorry


theorem Book_exists_perpLine_from_point_opposite : ∀ (a b x : Point) (AB : Line),
  ¬(x.onLine AB) ∧ (distinctPointsOnLine a b AB) →
  exists (f : Point), ¬(f.onLine AB) ∧ (f.opposingSides x AB) ∧ (∠ f:a:b = ∟) :=
by
sorry




theorem Book_triangle_angleSum : ∀ (a b c d : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (between b c d) →
  ∠ a:c:d = ∠ c:a:b + ∠ a:b:c ∧
  ∠ a:b:c + ∠ b:c:a + ∠ c:a:b = ∟ + ∟ :=
by
sorry




theorem Book_parallelogram_equal_triangle_angle : ∀ (a b c₁ c₂ c₃ d₁ d₂ d₃ : Point) (AB C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ : Line),
  formTriangle c₁ c₂ c₃ C₁₂ C₂₃ C₃₁ ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ distinctPointsOnLine a b AB ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (m l : Point) (BM AL ML : Line), formParallelogram b m a l BM AL AB ML ∧
  (∠ a:b:m = ∠ d₁:d₂:d₃) ∧ (Triangle.area △ a:b:m + Triangle.area △ a:l:m = Triangle.area △ c₁:c₂:c₃) :=
by
sorry


theorem Book_parallelogram_equal_triangle_angle_os : ∀ (a b c₁ c₂ c₃ d₁ d₂ d₃ x : Point) (AB C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ : Line),
  formTriangle c₁ c₂ c₃ C₁₂ C₂₃ C₃₁ ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ distinctPointsOnLine a b AB ∧ ¬(x.onLine AB) ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (m l : Point) (BM AL ML : Line), Point.opposingSides m x AB ∧ formParallelogram b m a l BM AL AB ML ∧
  (∠ a:b:m : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ a:b:m) + (Triangle.area △ a:l:m) = (Triangle.area △ c₁:c₂:c₃) :=
by
sorry




theorem Book_exists_midPoint : ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB →
  ∃ d : Point, (between a d b) ∧ (|(a─d)| = |(d─b)|) :=
by
sorry




theorem Book_proposition_42 : ∀ (a b c d₁ d₂ d₃ : Point) (AB BC AC D₁₂ D₂₃: Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (f g e c' : Point) (FG EC EF CG : Line), formParallelogram f g e c' FG EC EF CG ∧
  (∠ c':e:f = ∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:e:c' + Triangle.area △ f:c':g = Triangle.area △ a:b:c) :=
by
sorry


theorem Book_proposition_42' : ∀ (a b c d₁ d₂ d₃ e : Point) (AB BC AC D₁₂ D₂₃: Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ between b e c ∧ (|(b─e)| = |(e─c)|) ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (f g : Point) (FG EF CG : Line), a.sameSide f BC ∧ formParallelogram f g e c FG BC EF CG ∧
  (∠ c:e:f : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:e:c : ℝ) + (Triangle.area △ f:c:g) = (Triangle.area △ a:b:c) :=
by
sorry


theorem Book_proposition_42'' : ∀ (a b c d₁ d₂ d₃ h i : Point) (AB BC AC D₁₂ D₂₃ HI : Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ ∧ distinctPointsOnLine h i HI →
  ∃ (f g j : Point) (FG FI GJ : Line), between h i j ∧ formParallelogram f g i j FG HI FI GJ ∧
  (∠ j:i:f : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:i:j : ℝ) + (Triangle.area △ f:j:g) = (Triangle.area △ a:b:c) :=
by
sorry


theorem Book_proposition_42''' : ∀ (a b c d₁ d₂ d₃ h i x : Point) (AB BC AC D₁₂ D₂₃ HI : Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ ¬(x.onLine HI) ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ ∧ distinctPointsOnLine h i HI →
  ∃ (f g j : Point) (FG FI GJ : Line), f.sameSide x HI ∧ between h i j ∧ formParallelogram f g i j FG HI FI GJ ∧
  (∠ j:i:f : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:i:j : ℝ) + (Triangle.area △ f:j:g) = (Triangle.area △ a:b:c) :=
by
sorry




theorem Book_segment_transfer : ∀ (a b c : Point) (BC : Line),
  distinctPointsOnLine b c BC →
  ∃ l : Point, |(a─l)| = |(b─c)| :=
by
sorry




theorem Book_greater_angle_greater_base : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (|(a─b)| = |(d─e)|) ∧ (|(a─c)| = |(d─f)|) ∧ (∠ b:a:c > ∠ e:d:f) →
  |(b─c)| > |(e─f)| :=
by
sorry




theorem Book_proposition_35 : ∀ (a b c d e f g : Point) (AF BC AB CD EB FC : Line),
  formParallelogram a d b c AF BC AB CD ∧ formParallelogram e f b c AF BC EB FC ∧
  between a d e ∧ between d e f ∧ g.onLine CD ∧ g.onLine EB →
  Triangle.area △a:b:d + Triangle.area △d:b:c = Triangle.area △e:b:c + Triangle.area △ e:c:f :=
by
sorry


theorem Book_proposition_35' : ∀ (a b c d e f : Point) (AF BC AB CD EB FC : Line),
  formParallelogram a d b c AF BC AB CD ∧ formParallelogram e f b c AF BC EB FC →
  Triangle.area △a:b:d  + Triangle.area △d:b:c = Triangle.area △e:b:c + Triangle.area △ e:c:f :=
by
sorry




theorem Book_proposition_34 : ∀ (a b c d : Point) (AB CD AC BD BC : Line),
  formParallelogram a b c d AB CD AC BD ∧ distinctPointsOnLine b c BC →
  |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧
  ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c  = ∠ c:d:b ∧
  Triangle.area △ a:b:c = Triangle.area △ d:c:b :=
by
sorry


theorem Book_parallelogram_props_basic : ∀ (a b c d : Point) (AB CD AC BD : Line),
  formParallelogram a b c d AB CD AC BD →
  |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧
  ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c = ∠ c:d:b :=
by
sorry




theorem Book_greater_base_greater_angle : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (|(a─b)| = |(d─e)|) ∧ (|(a─c)| = |(d─f)|) ∧ (|(b─c)| > |(e─f)|) →
  (∠ b:a:c > ∠ e:d:f) :=
by
sorry




theorem Book_altAngle_equal_parallel : ∀ (a d e f : Point) (AE FD EF : Line),
  distinctPointsOnLine a e AE ∧ distinctPointsOnLine f d FD ∧ distinctPointsOnLine e f EF ∧
  a.opposingSides d EF ∧ (∠ a:e:f = ∠ e:f:d) →
  ¬(AE.intersectsLine FD) :=
by
sorry




theorem Book_coAangles_equal_parallel : ∀ (a b c d e f g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine e f EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (between g h f) ∧ (b.sameSide d EF) ∧
  (∠ e:g:b = ∠ g:h:d ∨ ∠ b:g:h + ∠ g:h:d = ∟ + ∟) →
  ¬(AB.intersectsLine CD) :=
by
sorry




theorem Book_greater_side_greater_angle : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─c)| > |(a─b)|) →
  (∠ a:b:c > ∠ b:c:a) :=
by
sorry




theorem Book_greater_angle_greater_side : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c > ∠ b:c:a) →
  (|(a─c)| > |(a─b)|) :=
by
sorry




theorem Book_proposition_38 : ∀ (a b c d e f: Point) (AD BF AB AC DE DF : Line),
  a.onLine AD ∧ d.onLine AD ∧ formTriangle a b c AB BF AC ∧ formTriangle d e f DE BF DF ∧
  ¬(AD.intersectsLine BF) ∧ (between b c f) ∧ (between b e f) ∧ |(b─c)| = |(e─f)| →
  Triangle.area △ a:b:c = Triangle.area △ d:e:f :=
by
sorry




theorem Book_triangle_inequality : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC → |(b─a)| + |(a─c)| > |(b─c)| :=
by
sorry




theorem Book_between_angleSum : ∀ (a b c d : Point) (AB CD : Line),
  AB ≠ CD ∧ distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ between d b c →
  ∠ c:b:a + ∠ a:b:d = ∟ + ∟ :=
by
sorry




theorem Book_proposition_41 : ∀ (a b c d e : Point) (AE BC AB CD BE CE : Line),
  formParallelogram a d b c AE BC AB CD ∧ formTriangle e b c BE BC CE ∧ e.onLine AE ∧ ¬(AE.intersectsLine  BC) →
  (Triangle.area △ a:b:c : ℝ) + (Triangle.area △ a:c:d) = (Triangle.area △ e:b:c) + (Triangle.area △ e :b :c) :=
by
sorry




theorem Book_proposition_23 : ∀ (a b c d e : Point) (AB CD CE : Line),
  distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE →
  ∃ f : Point, f ≠ a ∧ (∠ f:a:b = ∠ d:c:e) :=
by
sorry


theorem Book_proposition_23' : ∀ (a b c d e x : Point) (AB CD CE : Line),
  distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE ∧ ¬(x.onLine AB) →
  ∃ f : Point, f ≠ a ∧ (f.onLine AB ∨ f.sameSide x AB) ∧ (∠ f:a:b = ∠ d:c:e) :=
by
sorry




theorem Book_proposition_39 : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ a.sameSide d BC ∧
  (△ a:b:c : ℝ) = (△ d:b:c) ∧ distinctPointsOnLine a d AD →
  ¬(AD.intersectsLine BC) :=
by
sorry




theorem Book_proposition_31 : ∀ (a b c : Point) (BC : Line),
  distinctPointsOnLine b c BC ∧ ¬(a.onLine BC) →
  ∃ EF : Line, a.onLine EF ∧ ¬(EF.intersectsLine BC) :=
by
sorry




theorem Book_proposition_3 : ∀ (a b c₀ c₁ : Point) (AB C : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c₀ c₁ C ∧ |(a─b)| > |(c₀─c₁)| →
  ∃ e : Point, between a e b ∧ |(a─e)| = |(c₀─c₁)| :=
by
sorry

end LeanGeo
