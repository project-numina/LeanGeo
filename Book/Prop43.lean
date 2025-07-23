import SystemE
import Smt.Real
import Book.Prop34


namespace Elements.Book1
open LeanGeo

theorem proposition_43 : ∀ (a b c d e f g h k : Point) (AD BC AB CD AC EF GH : Line),
  formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC ∧ k.onLine AC ∧
  between a h d ∧ formParallelogram a h e k AD EF AB GH ∧ formParallelogram k f g c EF BC GH CD →
  (triangle.area △ e:b:g + triangle.area △ e:g:k = triangle.area △ h:k:f + triangle.area △ h:f:d) :=
by
  euclid_intros
  euclid_apply (proposition_34 d a c b AD BC CD AB AC)
  euclid_apply (proposition_34 h a k e AD EF GH AB AC)
  euclid_apply (proposition_34 f k c g EF BC CD GH AC)
  euclid_assert (triangle.area △ a:e:k : ℝ) + (triangle.area △ k:g:c) = (triangle.area △ a:h:k) + (triangle.area △ k:f:c)
  euclid_assert (triangle.area △ a:h:k : ℝ) + (triangle.area △ k:f:c) + (triangle.area △ h:k:f) + (triangle.area △ h:f:d) = (triangle.area △ d:a:c)
  euclid_finish

end Elements.Book1
