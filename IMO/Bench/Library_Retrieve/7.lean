import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem library7 : ∀ (a b c d e : Point), triangle a b c ∧ midpoint a d b ∧ midpoint a e c → |(b─c)| = |(d─e)| * 2:= by
  euclid_intros
  euclid_apply line_from_points
  euclid_apply similar_SAS d a e b a c
  have h1: |(b─a)| = |(d─a)| * 2 := by
    euclid_apply midpoint_twice
    euclid_finish
  euclid_finish
