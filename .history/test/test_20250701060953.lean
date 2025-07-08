import SystemE
import LeanGeo
open LeanGeo LeanGeo

/--In a triangle HIJ, HI = HJ. K is a point on segment IJ such that \angle IHK = \angle JHK. Prove that \angle HKI = \angle HKJ.-/
theorem problem_UniGeo_Triangle3 : ∀ (H I J K : Point) (HI IJ JH HK : Line),
  formTriangle H I J HI IJ JH ∧
  distinctPointsOnLine H K HK ∧
  IJ.intersectsLine HK ∧ K.onLine IJ ∧ between I K J ∧
  ∠ I:H:K = ∠ J:H:K ∧
  |(H─I)| = |(H─J)| →
  ∠ H:K:I = ∠ H:K:J :=
by
  euclid_intros
  have h_tri_IHK : triangle I H K := by
    euclid_finish
  have h_tri_JHK : triangle J H K := by
    euclid_finish
  euclid_apply congruent_SAS I H K J H K
  euclid_finish
