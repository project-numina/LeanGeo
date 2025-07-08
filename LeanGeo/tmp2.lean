import Mathlib
section
open Complex

lemma my_favorite_theorem (x y :ℂ ) : sin (x + y) = sin x *cos y + cos x * sin y := by
  sorry
end

open Real
lemma my_favorite_theorem2 (x y : ℝ) : sin (x + y) = sin x * cos y + cos x * sin y := by
  rw [my_favorite_theorem x y]
