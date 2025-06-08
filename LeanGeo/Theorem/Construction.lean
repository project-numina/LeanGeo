import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle

import Book

open Elements.Book1

namespace LeanGeo
theorem construct_perpBisector' (a b : Point) : (a ≠ b) →  ∃ L, perpBisector a b L ∧ ∃ M : Point, M.onLine L ∧ midpoint a M b := by
  intro hab
  obtain ⟨AB, ha, hb⟩ := line_from_points a b hab
  euclid_apply (proposition_1 a b AB) as c
  euclid_apply (line_from_points c a) as AC
  euclid_apply (line_from_points c b ) as BC
  euclid_apply (proposition_9' c a b AC BC) as d'
  euclid_apply (line_from_points c d') as CD
  use CD
  have crux : perpBisector a b CD := by
    use hab
    intro x hx
    cases em (c = x) with
    | inl hl =>
      rw [← hl]
      euclid_finish
    | inr hr =>
      obtain ⟨AX, ha', hx⟩ := line_from_points a x (by euclid_finish)
      obtain ⟨XC, hx', hc'⟩ := line_from_points x c (fun a => hr (id (Eq.symm a)))
      obtain  ⟨BX, hx'', hb'⟩ := line_from_points b x (by euclid_finish)
      have : ∠ a:c:x = ∠ b:c:x := by
        have : x.sameSide d' AC ∧ x.sameSide d' BC ∨ x.opposingSides d' AC ∧ x.opposingSides d' BC := by euclid_finish
        cases this with
        | inl hrl => euclid_finish
        | inr hrr =>
          have : ∠ a:c:x + ∠ a:c:d' = ∟ + ∟ := by
            apply supplementaryAngle_line
            euclid_finish
          have : ∠ b:c:x + ∠ b:c:d' = ∟ + ∟ := by
            apply supplementaryAngle_line
            euclid_finish
          euclid_finish
      euclid_apply proposition_4 c a x c b x AC AX XC BC BX XC
      euclid_finish
  apply And.intro
  · tauto
  · euclid_apply (intersection_lines CD AB) as d
    use d
    euclid_finish

theorem construct_perpBisector (a b : Point) : (a ≠ b) →  ∃ L, perpBisector a b L := by
  intro hab
  obtain ⟨L, hL⟩ := construct_perpBisector' a b hab
  use L
  exact hL.1

theorem centre_if_equidistant (a b c o : Point) (C : Circle) (ha : a.onCircle C) (hb : b.onCircle C) (hc : c.onCircle C) : |(o─a)| = |(o─b)| ∧ |(o─b)| = |(o─c)| → o.isCentre C := by sorry

theorem exists_centre : ∀ (O: Circle), ∃ (C : Point), C.isCentre O := by
  euclid_intros
  obtain ⟨A, hA⟩ : ∃ A : Point, A.onCircle O := exists_point_on_circle O
  obtain ⟨B, hAB, hB⟩ := exists_distinct_point_on_circle O A
  obtain ⟨AB, hAB1, hAB2⟩ := line_from_points A B hAB.symm
  obtain ⟨L, ⟨hL, M, hM⟩⟩ := construct_perpBisector' A B hAB.symm
  have : M.insideCircle O := by euclid_finish
  have := intersection_circle_line_2 M O L (by euclid_finish)
  obtain ⟨C1, C2, hC11, hC12, hC21, hC22, hC1C2⟩ := intersections_circle_line O L this
  obtain ⟨L', ⟨hL',M', hM'⟩⟩ := construct_perpBisector' C1 B (by euclid_finish)
  obtain ⟨C1B, hC1, hB⟩ := line_from_points C1 B (by euclid_finish)
  have : L'.intersectsLine L := by
    apply by_contra
    intro hh
    -- have : ∠ B:C1:M < ∟ := by euclid_finish
    sorry
  obtain ⟨E, hE⟩ := intersection_lines L' L this
  use E
  euclid_apply centre_if_equidistant
  euclid_finish

theorem exists_midpoint : ∀ (A B : Point), A ≠ B → ∃(P : Point), midpoint A P B := by
  intro A B h
  obtain ⟨AB, hA, hB⟩ := line_from_points A B h
  obtain ⟨L, hL⟩ := construct_perpBisector' A B h
  obtain ⟨M, hM1, hM2⟩ := intersection_lines AB L (by euclid_finish)
  use M
  euclid_finish

--theorem exists_foot : ∀ (A : Point) (l : Line), ∃(P : Point), P.onLine l ∧
--(∀ Q:Point, Q.onLine l → ∠A:P:Q = ∟) := by
--  sorry
theorem midpoint_twice: ∀ (A B P : Point), midpoint A P B → |(A─B)| * 1/2 = |(P─B)|  := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem exists_foot : ∀ (c: Point) (AB : Line),
   ¬(c.onLine AB) →
  ∃ h : Point, foot c h AB :=
by
  intro P AB hh
  obtain ⟨P1, hP1⟩ := line_nonempty AB
  obtain ⟨PP1, hP, hP1'⟩ := line_from_points P P1 (by euclid_finish)
  obtain ⟨P2, h1, h2, h3⟩ := extend_point_longer PP1 P P1 (P─P1) (by euclid_finish)
  obtain ⟨C, hC⟩ := circle_from_points P P2 (by euclid_finish)
  have := intersection_circle_line_2 P1 C AB (by euclid_finish)
  obtain ⟨A, B, hA1, hA2, hB1, hB2⟩ := intersections_circle_line C AB this
  obtain ⟨L, hL, ⟨M, hM⟩⟩ := construct_perpBisector' A B (by tauto)
  use M
  sorry

theorem exists_angleBisection : ∀ (A B C : Point),
(A ≠ B) ∧ (A ≠ C) ∧ ¬(coll A B C)
→ ∃ (L : Line), ∀ (P: Point), P.onLine L ↔ ∠ A:B:P = ∠ P:B:C
:= by
  euclid_intros
  obtain ⟨AB, hA, hB⟩ := line_from_points A B (by euclid_finish)
  obtain ⟨AC, hA', hC⟩ := line_from_points A C (by euclid_finish)
  obtain ⟨f, hf⟩ := proposition_9' A B C AB AC (by euclid_finish)
  obtain ⟨L, hL⟩ := line_from_points B f (by euclid_finish)
  use L
  intro P
  apply Iff.intro
  · intro hh
    sorry
  · intro hh
    sorry

theorem unique_perpLine : ∀ (A : Point) (L : Line),
  ¬(A.onLine L)
  → ∃! (M : Line),
    A.onLine M
    ∧ perpLine L M
    :=
by
  intro A L hAL
  obtain ⟨A', hA'⟩ := exists_foot A L (by euclid_finish)
  obtain ⟨M, hM⟩ := line_from_points A A' (by euclid_finish)
  use M
  apply And.intro
  · euclid_finish
  · intro M' hM'
    suffices ∀ x : Point, x.onLine M' → x.onLine M by
      euclid_finish
    intro x hx
    sorry

example (A B : Prop) : (A ↔ B) ↔ ((A → B) ∧ (B → A)) :=
  iff_iff_implies_and_implies A B

theorem exists_inCentre : ∀ (A B C: Point), triangle A B C → ∃ (I : Point), inCentre I A B C := by
  intro A B C hABC
  obtain ⟨L1, hL1⟩ := exists_angleBisection A B C (by euclid_finish)
  simp [iff_iff_implies_and_implies] at hL1
  obtain ⟨L2, hL2⟩ := exists_angleBisection A C B (by euclid_finish)
  simp [iff_iff_implies_and_implies] at hL2
  have : L1.intersectsLine L2 := by sorry
  obtain ⟨I, hI⟩ := intersection_lines L1 L2 this
  use I
  sorry

end LeanGeo
