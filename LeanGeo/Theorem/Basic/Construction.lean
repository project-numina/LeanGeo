import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import LeanGeo.Theorem.Basic.Angle
import LeanGeo.Theorem.Basic.Distance
import Book

set_option maxHeartbeats 0
open Elements.Book1
namespace LeanGeo

theorem exists_perpBisector' (a b : Point) : (a ≠ b) →  ∃ L, PerpBisector a b L ∧ ∃ M : Point, M.onLine L ∧ MidPoint a M b := by
  intro hab
  obtain ⟨AB, ha, hb⟩ := line_from_points a b hab
  euclid_apply (proposition_1 a b AB) as c
  euclid_apply (line_from_points c a) as AC
  euclid_apply (line_from_points c b ) as BC
  euclid_apply (proposition_9' c a b AC BC) as d'
  euclid_apply (line_from_points c d') as CD
  use CD
  have crux : PerpBisector a b CD := by
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
            apply coll_supp_angles
            euclid_finish
          have : ∠ b:c:x + ∠ b:c:d' = ∟ + ∟ := by
            apply coll_supp_angles
            euclid_finish
          euclid_finish
      euclid_apply proposition_4 c a x c b x AC AX XC BC BX XC
      euclid_finish
  apply And.intro
  · tauto
  · euclid_apply (intersection_lines CD AB) as d
    use d
    euclid_finish

theorem exists_perpBisector (a b : Point) : (a ≠ b) →  ∃ L, PerpBisector a b L := by
  intro hab
  obtain ⟨L, hL⟩ := exists_perpBisector' a b hab
  use L
  exact hL.1

theorem exists_midpoint : ∀ (A B : Point), A ≠ B → ∃(P : Point), MidPoint A P B := by
  intro A B h
  obtain ⟨AB, hA, hB⟩ := line_from_points A B h
  obtain ⟨L, hL⟩ := exists_perpBisector' A B h
  obtain ⟨M, hM1, hM2⟩ := intersection_lines AB L (by euclid_finish)
  use M
  euclid_finish

theorem exists_foot : ∀ (c: Point) (AB : Line),
   ¬(c.onLine AB) →
  ∃ h : Point, Foot c h AB :=
by
  euclid_intros
  euclid_apply line_nonempty AB as a
  euclid_apply exists_distincts_points_on_line AB a as b
  euclid_apply proposition_12' a b c AB as h
  by_cases (h ≠ a ∧ ∠ a:h:c = ∟)
  · euclid_apply coll_angles_eq
    euclid_finish
  · euclid_apply coll_angles_eq
    euclid_finish

theorem exists_perpLine : ∀ (P : Point) (L : Line), ∃ (M : Line), P.onLine M ∧ PerpLine M L := by
    euclid_intros
    by_cases h: P.onLine L
    · euclid_apply exists_distincts_points_on_line L P as R
      euclid_apply extend_point L R P as T
      euclid_apply proposition_11 T R P L as Q
      euclid_apply line_from_points P Q as PQ
      use PQ
      euclid_finish
    · obtain ⟨A', hA'⟩ := exists_foot P L (by euclid_finish)
      obtain ⟨M, hM⟩ := line_from_points P A' (by euclid_finish)
      use M
      euclid_finish

theorem exists_angleBisector : ∀ (A B C : Point),
(A ≠ B) ∧ (B ≠ C) ∧ ¬(Coll A B C)
→ ∃ (L : Line), B.onLine L ∧ (∀ (P: Point), P ≠ B → (P.onLine L ↔ ∠ A:B:P = ∠ P:B:C))
:= by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply proposition_9' B A C AB BC as P'
  euclid_apply line_from_points P' B as L
  use L
  constructor
  · euclid_finish
  · euclid_intros
    constructor
    · intros
      have h0 : between P B P' ∨ between B P P' ∨ between B P' P ∨ P = B ∨ P = P' := by
        euclid_finish
      rcases h0 with h1|h2|h3|h4|h5
      · euclid_apply coll_angles_eq P B P' A
        euclid_apply coll_angles_eq P B P' C
        euclid_finish
      · euclid_apply coll_angles_eq B P P' A
        euclid_apply coll_angles_eq B P P' C
        euclid_finish
      · euclid_apply coll_angles_eq B P' P A
        euclid_apply coll_angles_eq B P' P C
        euclid_finish
      · euclid_finish
      · euclid_finish
    · intros
      euclid_apply line_from_points P B as PB
      by_cases P.sameSide P' AB
      · euclid_apply coll_if_eq_angles A B P' P AB
        euclid_finish
      · euclid_apply point_on_line_same_side AB PB P' as P''
        euclid_apply coll_if_eq_angles A B P' P'' AB
        euclid_finish

theorem exists_point_not_on_line : ∀ (L : Line), ∃ (A : Point), ¬ A.onLine L := by
    euclid_intros
    euclid_apply line_nonempty L as B
    euclid_apply exists_distincts_points_on_line L B as C
    euclid_apply proposition_1 B C L as A
    euclid_finish

theorem exists_point_on_line_not_on_line : ∀ (L M : Line), L ≠ M → ∃ (A : Point), A.onLine L ∧ ¬ A.onLine M := by
    euclid_intros
    euclid_apply line_nonempty L as B
    euclid_apply exists_distincts_points_on_line L B as C
    euclid_apply exists_point_between_points_not_on_line L M B C as A
    euclid_finish

end LeanGeo
