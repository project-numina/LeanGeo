import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem Quadrilateral4 : ∀ (G H I J : Point) (GH IJ GJ GI : Line),
  formQuadrilateral G H J I GH HJ IJ GI ∧ distinctPointsOnLine G J GJ ∧
  |(I─J)| = |(G─H)| ∧
  ¬ GH.intersectsLine IJ →
  |(H─J)| = |(G─I)|  :=
by
  euclid_intros
  have h1: ∠ H:G:J = ∠ G:J:I := by
    euclid_apply parallel_imp_eq_alternateAngles GH IJ GJ G J H I
    euclid_finish
  euclid_apply congruentTriangles_SAS H G J I J G
  euclid_finish
