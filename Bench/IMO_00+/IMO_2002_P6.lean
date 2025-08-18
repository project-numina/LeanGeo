import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--Let $n\geq3$ be a positive integer. Let $C_1,C_2,C_3,\ldots,C_n$ be unit circles in the plane, with centres $O_1,O_2,O_3,\ldots,O_n$ respectively. If no line meets more than two of the circles, prove that[ \sum\limits^{}_{1\leq i j leq n}{1\over O_iO_j}\leq{(n-1)\pi\over 4}.   -/
import Mathlib

open Real

theorem my_favorite_theorem (n : ℕ) (hn : 3 ≤ n) (C : Fin n → (EuclideanSpace ℝ (Fin 2)))
    (hC : ∀ i, C i ∈ Metric.sphere 0 1) (hC1 : ∀ i j, i ≠ j → Disjoint {x | ∃ t : ℝ, x = C i + t • (C j - C i)} {x | ∃ u : ℝ, x = C j + u • (C i - C j)}) :
    ∑ i, ∑ j, (if i < j then (1 / dist (C i) (C j)) else 0) ≤ ((n - 1) * π) / 4 := by sorry
