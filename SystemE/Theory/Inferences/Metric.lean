import SystemE.Theory.Sorts
import SystemE.Theory.Relations
import SystemE.Tactic.Attr
-- chaining imports is necessary for euclid attribute to work properly
import SystemE.Theory.Inferences.Diagrammatic

namespace LeanGeo
--
-- Metric inferences defined in Sec. 3.5 of Avigad et al., 2009
-- Generally speaking, they are not used explicitly in the tactics written by humans.
-- *
--   + is associative and commutative, with identity 0.

--   < is a linear ordering with least element 0

--   For any x, y, and z, if x < y then x + z < y + z

--
-- 1.
-- ab = 0 if and only if a = b.
--



@[euclid]
axiom zero_segment_if :
  ∀ (a b : Point),  |(a ─ b)| = 0 → a = b


@[euclid]
axiom zero_segment_onlyif : ∀ (a b : Point),
  a = b → |(a─b)| = 0

-- --
-- 2.
-- ab ≥ 0
--
@[euclid]
axiom segment_gte_zero : ∀ (a b : Point),
  0 ≤ length a b

--
-- 3.
-- ab = ba.
--
@[simp, euclid]
axiom segment_symmetric : ∀ (a b : Point),
  |(a─b)| = |(b─a)|
--


@[euclid]
axiom angle_symm : ∀ (a b c : Point),
  (a ≠ b) ∧ (b ≠ c) → ((∠ a:b:c) = (∠ c:b:a))

--
-- 5.
-- 0 ≤ \abc and \abc ≤ right-angle + right-angle.
-- --
@[simp, euclid]
axiom angle_range : ∀ (a b c : Point), a ≠ b ∧ b ≠ c → 0 ≤ ∠ a:b:c ∧ ∠ a:b:c ≤ ∟ + ∟
-- this actually can't be proven because Angle.ofPoints don't require points to be distinct
-- := fun a b c => angle_range (Angle.ofPoints a b c)

--
-- 6.
-- △aab = 0. △
--
@[simp, euclid]
axiom degenerated_area : ∀ (a b : Point), area' a a b = 0

--
-- 7.
-- △abc ≥ 0.
-- --
@[simp, euclid]
axiom area_gte_zero : ∀ a b c : Point, 0 ≤ area' a b c

--
-- 8.
-- △abc = △cab and △abc = △acb.
--
@[simp, euclid]
axiom area_symm_1 : ∀ (a b c : Point),
    area' a b c = area' c a b

@[simp, euclid]
axiom area_symm_2 : ∀ (a b c : Point),
    area' a b c = area' a c b

--
-- 9.
-- If ab = a′b′, bc = b′c′, ca = c′a′, \abc = \a′b′c′, \bca = \b′c′a′, and
-- \cab = \c′a′b′, then △abc = △a′b′c′.
--

@[euclid]
axiom area_congruence : ∀ (a b c a' b' c' : Point),
    |(a─b)| = |(a'─b')| ∧
    |(b─c)| = |(b'─c')| ∧
    |(c─a)| = |(c'─a')| ∧
    ∠ a:b:c = ∠ a':b':c' ∧
    ∠ b:c:a = ∠ b':c':a' ∧
    ∠ c:a:b = ∠ c':a':b'
    → area' a b c = area' a' b' c'

@[euclid, metric]
axiom radius_withCentre : ∀ (A O : Point) (Ω : Circle),
    O.isCentre Ω ∧ A.onCircle Ω → |(O─A)| = rad Ω

@[euclid, metric]
axiom circlePower_withCentre: ∀ (A O : Point) (Ω : Circle),
    O.isCentre Ω → Pow(A, Ω) = |(A─O)| * |(A─O)| - (rad Ω) * (rad Ω)

#euclid_post

end LeanGeo
