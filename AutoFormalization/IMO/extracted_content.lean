import SystemE 
import UniGeo.Relations
 import Book

theorem Parallel_Thm16 : ∀ (T V W U X : Point) (TV TW UX VW : Line),
  distinctPointsOnLine T V TV ∧
  distinctPointsOnLine T W TW ∧
  distinctPointsOnLine U X UX ∧
  distinctPointsOnLine V W VW ∧
  TV.intersectsLine UX ∧ U.onLine TV ∧ between T U V ∧
  TW.intersectsLine UX ∧ X.onLine TW ∧ between T X W ∧
  TV.intersectsLine VW ∧
  TW.intersectsLine VW ∧
  ∠ T:U:X = ∠ T:W:V ∧
  ¬ UX.intersectsLine VW →
  ∠ U:V:W = ∠ T:W:V :=
by
  euclid_intros
  have : ∠ U:V:W = ∠ T:U:X := by
    euclid_apply Elements.Book1.proposition_29'''' X W T U V UX VW TV
    euclid_finish
  euclid_finish




theorem Parallel_Thm03 : ∀ (R T U W Q X S V : Point) (RT UW QX : Line),
  distinctPointsOnLine R T RT ∧
  distinctPointsOnLine U W UW ∧
  distinctPointsOnLine Q X QX ∧
  twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ between Q S V ∧
  twoLinesIntersectAtPoint UW QX V ∧ between U V W ∧ between S V X ∧
  R.sameSide U QX ∧
  T.sameSide W QX ∧
  ∠ T:S:V + ∠ S:V:W = ∟ + ∟ →
  ¬ UW.intersectsLine RT :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_28 R T U W Q X S V RT UW QX
  euclid_finish




theorem Parallel_Thm08 : ∀ (T V W Y S Z U X : Point) (TV WY SZ : Line),
  distinctPointsOnLine T V TV ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine S Z SZ ∧
  twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between S U X ∧
  twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧
  T.sameSide W SZ ∧
  V.sameSide Y SZ ∧
  ∠ V:U:X + ∠ U:X:Y = ∟ + ∟ →
  ¬ TV.intersectsLine WY :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_28 T V W Y S Z U X TV WY SZ
  euclid_finish




theorem Parallel_Thm15 : ∀ (G I S U V X R Y H T W : Point) (GI SU VX RY : Line),
  distinctPointsOnLine G I GI ∧
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine R Y RY ∧
  twoLinesIntersectAtPoint GI RY H ∧ between G H I ∧ between R H T ∧
  twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between H T W ∧
  twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between T W Y ∧
  G.sameSide S RY ∧
  S.sameSide V RY ∧
  I.sameSide U RY ∧
  U.sameSide X RY ∧
  ¬ VX.intersectsLine GI ∧
  ¬ GI.intersectsLine SU →
  ∠ X:W:Y + ∠ R:T:U = ∟ + ∟ :=
by
  euclid_intros
  have : ∠ R:T:U = ∠ I:H:R := by
    euclid_apply Elements.Book1.proposition_29'''' I U R H T GI SU RY
    euclid_finish
  have : ∠ I:H:R + ∠ X:W:Y = ∟ + ∟:= by
    euclid_apply Elements.Book1.proposition_29'''' I X R H W GI VX RY
    euclid_apply Elements.Book1.proposition_13 X W Y R VX RY
    euclid_finish
  euclid_finish




theorem Parallel_Thm17 : ∀ (S V T U W : Point) (SV TU SU TV : Line),
  distinctPointsOnLine S V SV ∧
  distinctPointsOnLine T U TU ∧
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine T V TV ∧
  twoLinesIntersectAtPoint SU TV W ∧ between S W U ∧ between T W V ∧
  ∠ T:U:W = ∠ U:T:W ∧
  ¬ SV.intersectsLine TU →
  ∠ W:V:S = ∠ W:S:V :=
by
  euclid_intros
  have : ∠ W:S:V = ∠ T:U:W := by
    euclid_apply Elements.Book1.proposition_29''' T V U S TU SV SU
    euclid_finish
  have : ∠ U:T:W = ∠ W:V:S := by
    euclid_apply Elements.Book1.proposition_29''' U S T V TU SV TV
    euclid_finish
  euclid_finish




theorem Parallel_Thm14 : ∀ (H J W Y T V S Z I X U : Point) (HJ WY TV SZ : Line),
  distinctPointsOnLine H J HJ ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine T V TV ∧
  distinctPointsOnLine S Z SZ ∧
  twoLinesIntersectAtPoint HJ SZ I ∧ between H I J ∧ between S U X ∧
  twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X I ∧
  twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between X I Z ∧
  V.sameSide Y SZ ∧
  Y.sameSide J SZ ∧
  T.sameSide W SZ ∧
  W.sameSide H SZ ∧
  ¬ HJ.intersectsLine WY ∧
  ¬ TV.intersectsLine HJ →
  ∠ S:X:Y = ∠ T:U:Z :=
by
  euclid_intros
  have : ∠ S:X:Y = ∠ J:I:S := by
    euclid_apply Elements.Book1.proposition_29'''' Y J S X I WY HJ SZ
    euclid_finish
  have : ∠ J:I:S = ∠ T:U:Z := by
    euclid_apply Elements.Book1.proposition_29''' J T I U HJ TV SZ
    euclid_finish
  euclid_finish




theorem Parallel_Thm02 : ∀ (R T U W Q X S V : Point) (RT UW QX : Line),
  distinctPointsOnLine R T RT ∧
  distinctPointsOnLine U W UW ∧
  distinctPointsOnLine Q X QX ∧
  twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ between Q S V ∧
  twoLinesIntersectAtPoint UW QX V ∧ between U V W ∧ between S V X ∧
  T.sameSide W QX ∧
  R.sameSide U QX ∧
  ¬ RT.intersectsLine UW →
  ∠ T:S:V + ∠ S:V:W = ∟ + ∟ :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29 R T U W Q X S V RT UW QX
  euclid_finish




theorem Parallel_Thm11 : ∀ (Q T R S U : Point) (QT RS QS RT : Line),
  distinctPointsOnLine Q T QT ∧
  distinctPointsOnLine R S RS ∧
  distinctPointsOnLine Q S QS ∧
  distinctPointsOnLine R T RT ∧
  twoLinesIntersectAtPoint QS RT U ∧ between Q U S ∧ between R U T ∧
  ¬ RS.intersectsLine QT ∧
  ∠ T:Q:U = ∠ Q:T:U →
  ∠ R:S:U = ∠ S:R:U :=
by
  euclid_intros
  have : ∠ T:Q:U = ∠ R:S:U := by
    euclid_apply Elements.Book1.proposition_29''' R T S Q RS QT QS
    euclid_finish
  have : ∠ S:R:U = ∠ Q:T:U := by
    euclid_apply Elements.Book1.proposition_29''' Q S T R QT RS RT
    euclid_finish
  euclid_finish




theorem Parallel_Thm01 : ∀ (T V W Y S Z U X : Point) (TV WY SZ : Line),
  distinctPointsOnLine T V TV ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine S Z SZ ∧
  twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between S U X ∧
  twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧
  T.sameSide W SZ ∧
  V.sameSide Y SZ ∧
  ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ →
  ¬ WY.intersectsLine TV :=
by
  euclid_intros
  have : ∠ S:U:T + ∠ T:U:X = ∟ + ∟ := by
    euclid_apply Elements.Book1.proposition_13 T U S X TV SZ
    euclid_finish
  euclid_assert ∠ W:X:Z = ∠ T:U:X
  euclid_apply Elements.Book1.proposition_28 Y W V T Z S X U WY TV SZ
  euclid_finish




theorem Parallel_Thm20 : ∀ (W X V Y Z : Point) (WX VY VX WY : Line),
  distinctPointsOnLine W X WX ∧
  distinctPointsOnLine V Y VY ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine W Y WY ∧
  twoLinesIntersectAtPoint VX WY Z ∧ between W Z X ∧ between W Z Y ∧
  (∠ Y:V:Z) = (∠ V:Y:Z) ∧
  ¬ WX.intersectsLine VY →
  (∠ X:W:Z) = (∠ W:X:Z) :=
by
  euclid_intros
  have : ∠ Y:V:Z = ∠ W:X:Z := by
    euclid_apply Elements.Book1.proposition_29''' W Y X V WX VY VX
    euclid_finish
  have : ∠ X:W:Z = ∠ V:Y:Z := by
    euclid_apply Elements.Book1.proposition_29''' X V W Y WX VY WY
    euclid_finish
  euclid_finish




theorem Parallel_Thm09 : ∀ (R T U W Q X S V : Point) (RT UW QX : Line),
  distinctPointsOnLine R T RT ∧
  distinctPointsOnLine U W UW ∧
  distinctPointsOnLine Q X QX ∧
  twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ between Q S V ∧
  twoLinesIntersectAtPoint UW QX V ∧ between U V W ∧ between S V X ∧
  W.sameSide T QX ∧
  U.sameSide R QX ∧
  ∠ Q:S:R + ∠ U:V:X = ∟ + ∟ →
  ¬ RT.intersectsLine UW :=
by
  euclid_intros
  have : ∠ Q:S:R + ∠ R:S:V = ∟ + ∟ := by
    euclid_apply Elements.Book1.proposition_13 R S Q V RT QX
    euclid_finish
  euclid_assert ∠ U:V:X = ∠ R:S:V
  euclid_apply Elements.Book1.proposition_28 W U T R X Q V S UW RT QX
  euclid_finish




theorem Parallel_Thm13 : ∀ (Q S T R U : Point) (QS QT ST RU : Line),
  distinctPointsOnLine Q S QS ∧
  distinctPointsOnLine Q T QT ∧
  distinctPointsOnLine S T ST ∧
  distinctPointsOnLine R U RU ∧
  QS.intersectsLine RU ∧ R.onLine QS ∧ between Q R S ∧
  QT.intersectsLine RU ∧ U.onLine QT ∧ between Q U T ∧
  QS.intersectsLine ST ∧
  QT.intersectsLine ST ∧
  ∠ Q:R:U = ∠ Q:U:R ∧
  ¬ ST.intersectsLine RU →
  ∠ R:S:T = ∠ S:T:Q :=
by
  euclid_intros
  have : ∠ U:T:S = ∠ Q:U:R := by
    euclid_apply Elements.Book1.proposition_29'''' R S Q U T RU ST QT
    euclid_finish
  have : ∠ R:S:T = ∠ Q:R:U := by
    euclid_apply Elements.Book1.proposition_29'''' U T Q R S RU ST QS
    euclid_finish
  euclid_finish




theorem Parallel_Thm18 : ∀ (V X Y W Z : Point) (VX VY WZ XY : Line),
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine V Y VY ∧
  distinctPointsOnLine W Z WZ ∧
  distinctPointsOnLine X Y XY ∧
  VX.intersectsLine WZ ∧ W.onLine VX ∧ between V W X ∧
  VY.intersectsLine WZ ∧ Z.onLine VY ∧ between V Z Y ∧
  VX.intersectsLine XY ∧
  VY.intersectsLine XY ∧
  ¬ XY.intersectsLine WZ ∧
  ∠ V:Y:X = ∠ W:X:Y →
  ∠ V:W:Z = ∠ V:Z:W :=
by
  euclid_intros
  have : ∠ V:Y:X = ∠ V:Z:W := by
    euclid_apply Elements.Book1.proposition_29'''' W X V Z Y WZ XY VY
    euclid_finish
  have : ∠ W:X:Y = ∠ V:W:Z := by
    euclid_apply Elements.Book1.proposition_29'''' Z Y V W X WZ XY VX
    euclid_finish
  euclid_finish




theorem Parallel_Thm19 : ∀ (P R T V W Y S Z Q U X : Point) (PR TV WY SZ : Line),
  distinctPointsOnLine P R PR ∧
  distinctPointsOnLine T V TV ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine S Z SZ ∧
  twoLinesIntersectAtPoint PR SZ Q ∧ between P Q R ∧ between S Q U ∧
  twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between Q U X ∧
  twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧
  R.sameSide V SZ ∧
  V.sameSide Y SZ ∧
  P.sameSide T SZ ∧
  T.sameSide W SZ ∧
  ¬ PR.intersectsLine TV ∧
  ¬ WY.intersectsLine PR →
  (∠ S:X:W) = (∠ V:U:Z) :=
by
  euclid_intros
  have : ∠ V:U:Z = ∠ R:Q:Z := by
    euclid_apply Elements.Book1.proposition_29'''' V R Z U Q TV PR SZ
    euclid_finish
  have : ∠ R:Q:Z = ∠ S:X:W := by
    euclid_apply Elements.Book1.proposition_29''' R W Q X PR WY SZ
    euclid_finish
  euclid_finish




theorem Parallel_Thm06 : ∀ (S U V X R Y T W : Point) (SU VX RY : Line),
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine R Y RY ∧
  twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between R T W ∧
  twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between T W Y ∧
  V.sameSide S RY ∧
  U.sameSide X RY ∧
  ∠ S:T:W + ∠ T:W:V = ∟ + ∟ →
  ¬ VX.intersectsLine SU :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_28 U S X V R Y T W SU VX RY
  euclid_finish




theorem Parallel_Thm10 : ∀ (V Y W X Z : Point) (VY WX WY VX : Line),
  distinctPointsOnLine V Y VY ∧
  distinctPointsOnLine W X WX ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine V X VX ∧
  twoLinesIntersectAtPoint WY VX Z ∧ between W Z Y ∧ between V Z X ∧
  ¬ WX.intersectsLine VY ∧
  ∠ Y:V:Z = ∠ Z:Y:V →
  ∠ X:W:Z = ∠ W:X:Z :=
by
  euclid_intros
  have : ∠ Y:V:Z= ∠ W:X:Z := by
    euclid_apply Elements.Book1.proposition_29''' W Y X V WX VY VX
    euclid_finish
  have : ∠ X:W:Z = ∠ V:Y:Z := by
    euclid_apply Elements.Book1.proposition_29''' V X Y W VY WX WY
    euclid_finish
  euclid_finish




theorem Parallel_Thm05 : ∀ (S U V X R Y T W : Point) (SU VX RY : Line),
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine R Y RY ∧
  twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between T W Y ∧
  twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between R T W ∧
  V.sameSide S RY ∧
  X.sameSide U RY ∧
  ∠ R:T:S + ∠ V:W:Y = ∟ + ∟ →
  ¬ VX.intersectsLine SU :=
by
  euclid_intros
  have : ∠ R:T:S + ∠ S:T:W = ∟ + ∟ := by
    euclid_apply Elements.Book1.proposition_13 S T R W SU RY
    euclid_finish
  euclid_assert ∠ V:W:Y = ∠ S:T:W
  euclid_apply Elements.Book1.proposition_28 X V U S Y R W T VX SU RY
  euclid_finish




theorem Parallel_Thm12 : ∀ (P R T V W Y S Z Q U X : Point) (PR TV WY SZ : Line),
  distinctPointsOnLine P R PR ∧
  distinctPointsOnLine T V TV ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine S Z SZ ∧
  twoLinesIntersectAtPoint PR SZ Q ∧ between P Q R ∧ between S Q U ∧
  twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between Q U X ∧
  twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧
  R.sameSide V SZ ∧
  V.sameSide Y SZ ∧
  P.sameSide T SZ ∧
  T.sameSide W SZ ∧
  ¬ WY.intersectsLine PR ∧
  ¬ TV.intersectsLine PR →
  ¬ WY.intersectsLine TV :=
by
  euclid_intros
  have : ∠ S:U:T = ∠ P:Q:S := by
    euclid_apply Elements.Book1.proposition_29'''' P T S Q U PR TV SZ
    euclid_finish
  have : ∠ P:Q:S = ∠ S:X:W := by
    euclid_apply Elements.Book1.proposition_29'''' P W S Q X PR WY SZ
    euclid_finish
  euclid_assert ∠ S:U:T = ∠ S:X:W
  euclid_apply Elements.Book1.proposition_28 V T Y W S Z U X TV WY SZ
  euclid_finish




theorem Parallel_Thm07 : ∀ (S U V X R Y T W : Point) (SU VX RY : Line),
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine R Y RY ∧
  twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between R T W ∧
  twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between T W Y ∧
  U.sameSide X RY ∧
  V.sameSide S RY ∧
  ¬ VX.intersectsLine SU →
  ∠ T:W:X = ∠ S:T:W :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29 S U V X R Y T W SU VX RY
  euclid_finish




theorem Parallel_Thm04 : ∀ (S U V X R Y T W : Point) (SU VX RY : Line),
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine R Y RY ∧
  twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between T W Y ∧
  twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between R T W ∧
  V.sameSide S RY ∧
  X.sameSide U RY ∧
  ¬ VX.intersectsLine SU →
  ∠ S:T:W = ∠ T:W:X :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29 X V U S Y R W T VX SU RY
  euclid_finish




theorem Quadrilateral_Thm16 : ∀ (F G H I : Point) (FG HI GH FI FH : Line),
  formQuadrilateral F G I H FG HI FI GH ∧
  distinctPointsOnLine F H FH ∧
  |(F─I)| = |(G─H)| ∧
  |(H─I)| = |(F─G)| →
  ∠ F:H:I = ∠ G:F:H :=
by
  euclid_intros
  euclid_assert (△ F:G:H).congruent (△ H:I:F)
  euclid_apply Triangle.congruent_if (△ F:G:H) (△ H:I:F)
  euclid_finish




theorem Quadrilateral_Thm03 : ∀ (W X Y Z : Point) (WX YZ XY WZ WY : Line),
  formQuadrilateral W X Z Y WX YZ WZ XY ∧
  distinctPointsOnLine W Y WY ∧
  |(X─Y)| = |(W─Z)| ∧
  |(Y─Z)| = |(W─X)| →
  ∠ Y:W:Z = ∠ W:Y:X :=
by
  euclid_intros
  euclid_assert (△ W:X:Y).congruent (△ Y:Z:W)
  euclid_apply Triangle.congruent_if (△ W:X:Y) (△ Y:Z:W)
  euclid_finish




theorem Quadrilateral_Thm08 : ∀ (V W X Y : Point) (VW XY WX VY VX : Line),
  formQuadrilateral V W Y X VW XY VY WX ∧
  distinctPointsOnLine V X VX ∧
  ∠ X:Y:V = ∟ ∧
  ¬ VW.intersectsLine XY ∧
  ∠ V:W:X = ∟ →
  |(V─Y)| = |(W─X)| :=
by
  euclid_intros
  have : ∠ W:V:X = ∠ V:X:Y := by
    euclid_apply Elements.Book1.proposition_29''' W Y V X VW XY VX
    euclid_finish
  euclid_assert (△ V:X:Y).congruent (△ X:V:W)
  euclid_apply Triangle.congruent_if (△ V:X:Y) (△ X:V:W)
  euclid_finish




theorem Quadrilateral_Thm15 : ∀ (Q R S T : Point) (QR ST RS QT QS : Line),
  formQuadrilateral Q R T S QR ST QT RS ∧
  distinctPointsOnLine Q S QS ∧
  ∠ S:Q:T = ∠ Q:S:R ∧
  ∠ Q:T:S = ∟ ∧
  ∠ Q:R:S = ∟ →
  |(R─S)| = |(Q─T)| :=
by
  euclid_intros
  euclid_assert (△ Q:S:T).congruent (△ S:Q:R)
  euclid_apply Triangle.congruent_if (△ Q:S:T) (△ S:Q:R)
  euclid_finish




theorem Quadrilateral_Thm17 : ∀ (P Q R S : Point) (PQ RS QR PS PR : Line),
  formQuadrilateral P Q S R PQ RS PS QR ∧
  distinctPointsOnLine P R PR ∧
  ∠ Q:P:R = ∠ S:P:R ∧
  ∠ P:R:Q = ∠ P:R:S →
  |(R─S)| = |(Q─R)| :=
by
  euclid_intros
  euclid_assert (△ P:Q:R).congruent (△ P:S:R)
  euclid_apply Triangle.congruent_if (△ P:Q:R) (△ P:S:R)
  euclid_finish




theorem Quadrilateral_Thm14 : ∀ (G H I J : Point) (GH IJ HI GJ GI : Line),
  formQuadrilateral G H J I GH IJ GJ HI ∧
  distinctPointsOnLine G I GI ∧
  ∠ I:G:H = ∠ I:G:J ∧
  ∠ G:H:I = ∠ G:J:I →
  |(G─J)| = |(G─H)| :=
by
  euclid_intros
  euclid_assert (△ G:H:I).congruent (△ G:J:I)
  euclid_apply Triangle.congruent_if (△ G:H:I) (△ G:J:I)
  euclid_finish




theorem Quadrilateral_Thm02 : ∀ (E F G H : Point) (EF GH FG EH EG : Line),
  formQuadrilateral E F H G EF GH EH FG ∧
  distinctPointsOnLine E G EG ∧
  ¬ GH.intersectsLine EF ∧
  |(E─F)| = |(G─H)| →
  ∠ E:F:G = ∠ E:H:G :=
by
  euclid_intros
  have : ∠ E:G:H = ∠ F:E:G := by
    euclid_apply Elements.Book1.proposition_29''' H F G E GH EF EG
    euclid_finish
  euclid_assert (△ E:F:G).congruent (△ G:H:E)
  euclid_apply Triangle.congruent_if (△ E:F:G) (△ G:H:E)
  euclid_finish




theorem Quadrilateral_Thm11 : ∀ (S T U V : Point) (ST UV TU SV SU : Line),
  formQuadrilateral S T V U ST UV SV TU ∧
  distinctPointsOnLine S U SU ∧
  |(U─V)| = |(T─U)| ∧
  |(S─T)| = |(S─V)| →
  ∠ S:V:U = ∠ S:T:U :=
by
  euclid_intros
  euclid_assert (△ S:T:U).congruent (△ S:V:U)
  euclid_apply Triangle.congruent_if (△ S:T:U) (△ S:V:U)
  euclid_finish




theorem Quadrilateral_Thm01 : ∀ (Q R S T : Point) (QR ST RS QT QS : Line),
  formQuadrilateral Q R T S QR ST QT RS ∧
  distinctPointsOnLine Q S QS ∧
  ∠ Q:R:S = ∟ ∧
  ∠ Q:T:S = ∟ ∧
  ∠ Q:S:R = ∠ S:Q:T →
  |(S─T)| = |(Q─R)| :=
by
  euclid_intros
  euclid_assert  (△ Q:S:T).congruent (△ S:Q:R)
  euclid_apply Triangle.congruent_if (△ Q:S:T) (△ S:Q:R)
  euclid_finish




theorem Quadrilateral_Thm20 : ∀ (Q R S T U : Point) (QR ST RS QT QS RT : Line),
  formQuadrilateral Q R T S QR ST QT RS ∧
  distinctPointsOnLine Q S QS ∧
  distinctPointsOnLine R T RT ∧
  twoLinesIntersectAtPoint QS RT U ∧
  ∠ Q:T:S = ∠ Q:R:S ∧
  ∠ R:S:T = ∠ R:Q:T →
  ¬ QT.intersectsLine RS :=
by
  euclid_intros
  have : ∠ R:Q:T + ∠ Q:R:S + ∠ R:S:T + ∠ Q:T:S = ∟ + ∟ + ∟ + ∟ := by
    euclid_apply quadrilateralAnglesSum Q R T S QR ST QT RS
    euclid_finish
  euclid_assert ∠ R:Q:T + ∠ Q:R:S = ∟ + ∟

  euclid_apply extend_point QT T Q as W
  euclid_apply extend_point RS S R as X
  euclid_apply extend_point QR Q R as Y
  euclid_apply extend_point QR R Q as Z

  euclid_apply Elements.Book1.proposition_28 W T X S Z Y Q R QT RS QR
  euclid_finish




theorem Quadrilateral_Thm09 : ∀ (F G H I : Point) (FG HI GH FI FH : Line),
  formQuadrilateral F G I H FG HI FI GH ∧
  distinctPointsOnLine F H FH ∧
  ¬ HI.intersectsLine FG ∧
  ∠ H:I:F = ∟ ∧
  ∠ F:G:H = ∟ →
  |(H─I)| = |(F─G)| :=
by
  euclid_intros
  have : ∠ G:F:H = ∠ F:H:I := by
    euclid_apply Elements.Book1.proposition_29''' G I F H FG HI FH
    euclid_finish
  euclid_assert (△ F:H:I).congruent (△ H:F:G)
  euclid_apply Triangle.congruent_if (△ F:H:I) (△ H:F:G)
  euclid_finish




theorem Quadrilateral_Thm13 : ∀ (H I J K : Point) (HI JK IJ HK HJ : Line),
  formQuadrilateral H I K J HI JK HK IJ ∧
  distinctPointsOnLine H J HJ ∧
  |(J─K)| = |(H─I)| ∧
  |(H─K)| = |(I─J)| →
  ∠ H:K:J = ∠ H:I:J :=
by
  euclid_intros
  euclid_assert (△ H:I:J).congruent (△ J:K:H)
  euclid_apply Triangle.congruent_if (△ H:I:J) (△ J:K:H)
  euclid_finish




theorem Quadrilateral_Thm18 : ∀ (E F G H : Point) (EF GH FG EH EG : Line),
  formQuadrilateral E F H G EF GH EH FG ∧
  distinctPointsOnLine E G EG ∧
  |(G─H)| = |(E─F)| ∧
  ¬ GH.intersectsLine EF →
  ∠ G:E:H = ∠ E:G:F :=
by
  euclid_intros
  have : ∠ E:G:H = ∠ F:E:G := by
    euclid_apply Elements.Book1.proposition_29''' H F G E GH EF EG
    euclid_finish
  euclid_assert (△ E:F:G).congruent (△ G:H:E)
  euclid_apply Triangle.congruent_if (△ E:F:G) (△ G:H:E)
  euclid_finish




theorem Quadrilateral_Thm19 : ∀ (U V W X Y : Point) (UV WX VW UX UW VX UY XY : Line),
  formQuadrilateral U V X W UV WX UX VW ∧
  distinctPointsOnLine U W UW ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine U Y UY ∧
  distinctPointsOnLine X Y XY ∧
  Y.opposingSides W UX ∧
  ¬ UY.intersectsLine VX ∧
  ¬ WX.intersectsLine UV ∧
  ¬ XY.intersectsLine UV ∧
  |(V─X)| = |(U─W)| →
  ∠ V:W:X = ∠ U:X:W :=
by
  euclid_intros
  have : |(V─X)| = |(U─Y)| := by
    euclid_apply Elements.Book1.proposition_34' U V Y X UV XY UY VX
    euclid_finish

  euclid_assert |(U─Y)| = |(U─W)|

  have : ∠ U:W:Y = ∠ U:Y:W := by
    euclid_apply Elements.Book1.proposition_5' U W Y UW XY UY
    euclid_finish

  have : ∠ V:X:W = ∠ U:Y:X := by
    euclid_apply Elements.Book1.proposition_29'''' V U W X Y VX UY WX
    euclid_finish

  euclid_assert ∠ V:X:W = ∠ U:W:Y
  euclid_assert (△ U:W:X).congruent (△ V:X:W)
  euclid_apply Triangle.congruent_if (△ U:W:X) (△ V:X:W)
  euclid_finish




theorem Quadrilateral_Thm06 : ∀ (F G H I : Point) (FG HI GH FI FH : Line),
  formQuadrilateral F G I H FG HI FI GH ∧
  distinctPointsOnLine F H FH ∧
  |(F─G)| = |(H─I)| ∧
  ¬ HI.intersectsLine FG →
  |(G─H)| = |(F─I)| :=
by
  euclid_intros
  have : ∠ F:H:I = ∠ G:F:H := by
    euclid_apply Elements.Book1.proposition_29''' I G H F HI FG FH
    euclid_finish
  euclid_assert (△ F:G:H).congruent (△ H:I:F)
  euclid_apply Triangle.congruent_if (△ F:G:H) (△ H:I:F)
  euclid_finish




theorem Quadrilateral_Thm10 : ∀ (T U V W : Point) (TU VW UV TW TV : Line),
  formQuadrilateral T U W V TU VW TW UV ∧
  distinctPointsOnLine T V TV ∧
  ¬ TU.intersectsLine VW ∧
  |(V─W)| = |(T─U)| →
  ∠ V:T:W = ∠ T:V:U :=
by
  euclid_intros
  have : ∠ T:V:W = ∠ U:T:V := by
    euclid_apply Elements.Book1.proposition_29''' W U V T VW TU TV
    euclid_finish
  euclid_assert (△ T:U:V).congruent (△ V:W:T)
  euclid_apply Triangle.congruent_if (△ T:U:V) (△ V:W:T)
  euclid_finish




theorem Quadrilateral_Thm05 : ∀ (E F G H : Point) (EF GH FG EH EG : Line),
  formQuadrilateral E F H G EF GH EH FG ∧
  distinctPointsOnLine E G EG ∧
  |(E─F)| = |(G─H)| ∧
  ¬ GH.intersectsLine EF →
  ∠ E:G:F = ∠ G:E:H :=
by
  euclid_intros
  have : ∠ E:G:H = ∠ F:E:G := by
    euclid_apply Elements.Book1.proposition_29''' H F G E GH EF EG
    euclid_finish
  euclid_assert (△ E:F:G).congruent (△ G:H:E)
  euclid_apply Triangle.congruent_if (△ E:F:G) (△ G:H:E)
  euclid_finish




theorem Quadrilateral_Thm12 : ∀ (T U V W : Point) (TU VW UV TW TV : Line),
  formQuadrilateral T U W V TU VW TW UV ∧
  distinctPointsOnLine T V TV ∧
  ∠ T:V:U = ∠ V:T:W ∧
  ∠ T:U:V = ∟ ∧
  ∠ V:W:T = ∟ →
  |(T─U)| = |(V─W)| :=
by
  euclid_intros
  euclid_assert (△ T:V:W).congruent (△ V:T:U)
  euclid_apply Triangle.congruent_if (△ T:V:W) (△ V:T:U)
  euclid_finish




theorem Quadrilateral_Thm07 : ∀ (H I J K : Point) (HI JK IJ HK HJ : Line),
  formQuadrilateral H I K J HI JK HK IJ ∧
  distinctPointsOnLine H J HJ ∧
  |(J─K)| = |(H─I)| ∧
  ¬ JK.intersectsLine HI →
  ∠ H:K:J = ∠ H:I:J :=
by
  euclid_intros
  have : ∠ H:J:K = ∠ I:H:J := by
    euclid_apply Elements.Book1.proposition_29''' K I J H JK HI HJ
    euclid_finish
  euclid_assert (△ H:I:J).congruent (△ J:K:H)
  euclid_apply Triangle.congruent_if (△ H:I:J) (△ J:K:H)
  euclid_finish




theorem Quadrilateral_Thm04 : ∀ (G H I J : Point) (GH IJ HI GJ GI : Line),
  formQuadrilateral G H J I GH IJ GJ HI ∧
  distinctPointsOnLine G I GI ∧
  |(I─J)| = |(G─H)| ∧
  ¬ GH.intersectsLine IJ →
  |(H─I)| = |(G─J)| :=
by
  euclid_intros
  have : ∠ G:I:J = ∠ H:G:I := by
    euclid_apply Elements.Book1.proposition_29''' H J G I GH IJ GI
    euclid_finish
  euclid_assert (△ G:H:I).congruent (△ I:J:G)
  euclid_apply Triangle.congruent_if (△ G:H:I) (△ I:J:G)
  euclid_finish




theorem Triangle_Thm16 : ∀ (F H K G I J : Point) (FH HK KF GI IJ JG : Line),
  formTriangle F H K FH HK KF ∧
  formTriangle G I J GI IJ JG ∧
  ∠ F:H:K = ∠ I:G:J ∧
  |(H─K)| / |(G─J)| = |(F─H)| / |(G─I)| →
  ∠ H:F:K = ∠ G:I:J :=
by
  euclid_intros
  euclid_assert (△ F:H:K).similar (△ I:G:J)
  euclid_apply Triangle.similar_if (△ F:H:K) (△ I:G:J)
  euclid_finish




theorem Triangle_Thm03 : ∀ (H I J K : Point) (HI IJ JH HK : Line),
  formTriangle H I J HI IJ JH ∧
  distinctPointsOnLine H K HK ∧
  IJ.intersectsLine HK ∧ K.onLine IJ ∧ between I K J ∧
  ∠ I:H:K = ∠ J:H:K ∧
  |(H─I)| = |(H─J)| →
  ∠ H:K:I = ∠ H:K:J :=
by
  euclid_intros
  euclid_assert (△ H:I:K).congruent (△ H:J:K)
  euclid_apply Triangle.congruent_if (△ H:I:K) (△ H:J:K)
  euclid_finish




theorem Triangle_Thm08 : ∀ (U X Y V W Z : Point) (UX XY YU VW WZ ZV : Line),
  formTriangle U X Y UX XY YU ∧
  formTriangle V W Z VW WZ ZV ∧
  ∠ V:Z:W = ∠ X:U:Y ∧
  |(V─Z)| / |(U─X)| = |(W─Z)| / |(U─Y)| →
  ∠ V:W:Z = ∠ U:Y:X :=
by
  euclid_intros
  euclid_assert (△ V:W:Z).similar (△ X:Y:U)
  euclid_apply Triangle.similar_if (△ V:W:Z) (△ X:Y:U)
  euclid_finish




theorem Triangle_Thm15 : ∀ (S T V Q R U : Point) (ST TV VS QR RU UQ : Line),
  formTriangle S T V ST TV VS ∧
  formTriangle Q R U QR RU UQ ∧
  ∠ T:S:V = ∠ R:U:Q ∧
  |(S─V)| / |(Q─U)| = |(S─T)| / |(R─U)| →
  ∠ S:T:V = ∠ Q:R:U :=
by
  euclid_intros
  euclid_assert (△ S:T:V).similar (△ U:R:Q)
  euclid_apply Triangle.similar_if (△ S:T:V) (△ U:R:Q)
  euclid_finish




theorem Triangle_Thm17 : ∀ (U W X S T V : Point) (UW WX XU ST TV VS : Line),
  formTriangle U W X UW WX XU ∧
  formTriangle S T V ST TV VS ∧
  ∠ U:X:W = ∠ T:V:S ∧
  |(W─X)| / |(S─V)| = |(U─X)| / |(T─V)| →
  ∠ U:W:X = ∠ T:S:V :=
by
  euclid_intros
  euclid_assert (△ U:W:X).similar (△ T:S:V)
  euclid_apply Triangle.similar_if (△ U:W:X) (△ T:S:V)
  euclid_finish




theorem Triangle_Thm14 : ∀ (I G H F J K : Point) (IG GH HI FJ JK KF : Line),
  formTriangle I G H IG GH HI ∧
  formTriangle F J K FJ JK KF ∧
  ∠ G:I:H = ∠ J:K:F ∧
  ∠ G:H:I = ∠ J:F:K →
  |(G─I)| / |(J─K)| = |(G─H)| / |(F─J)| :=
by
  euclid_intros
  euclid_assert (△ G:H:I).similar (△ J:F:K)
  euclid_apply Triangle.similar_if (△ G:H:I) (△ J:F:K)
  euclid_finish




theorem Triangle_Thm02 : ∀ (R S T U : Point) (RS ST TR RU : Line),
  formTriangle R S T RS ST TR ∧
  distinctPointsOnLine R U RU ∧
  ST.intersectsLine RU ∧ U.onLine ST ∧ between S U T ∧
  |(S─U)| = |(T─U)| ∧
  ∠ R:U:S = ∟ ∧ ∠ R:U:T = ∟ →
  ∠ T:R:U = ∠ S:R:U :=
by
  euclid_intros
  euclid_assert (△ R:S:U).congruent (△ R:T:U)
  euclid_apply Triangle.congruent_if (△ R:S:U) (△ R:T:U)
  euclid_finish




theorem Triangle_Thm11 : ∀ (V W X T U Y : Point) (VW WX XV TU UY YT : Line),
  formTriangle V W X VW WX XV ∧
  formTriangle T U Y TU UY YT ∧
  ∠ X:V:W = ∠ U:T:Y ∧
  ∠ V:W:X = ∠ T:Y:U →
  |(W─X)| / |(U─Y)| = |(V─W)| / |(T─Y)| :=
by
  euclid_intros
  euclid_assert (△ V:W:X).similar (△ T:Y:U)
  euclid_apply Triangle.similar_if (△ V:W:X) (△ T:Y:U)
  euclid_finish




theorem Triangle_Thm01 : ∀ (H I J K : Point) (HI IJ JH HK : Line),
  formTriangle H I J HI IJ JH ∧
  distinctPointsOnLine H K HK ∧
  IJ.intersectsLine HK ∧ K.onLine IJ ∧ between I K J ∧
  |(H─I)| = |(H─J)| ∧
  |(K─I)| = |(K─J)| →
  ∠ H:K:J = ∠ H:K:I :=
by
  euclid_intros
  euclid_assert (△ H:I:K).congruent (△ H:J:K)
  euclid_apply Triangle.congruent_if (△ H:I:K) (△ H:J:K)
  euclid_finish




theorem Triangle_Thm20 : ∀ (P R T S U Q : Point) (PR RT TP SU UQ QS : Line),
  formTriangle P R T PR RT TP ∧
  formTriangle S U Q SU UQ QS ∧
  ∠ P:R:T = ∠ S:U:Q ∧
  ∠ P:T:R = ∠ S:Q:U →
  |(R─T)| / |(Q─U)| = |(P─T)| / |(Q─S)| :=
by
  euclid_intros
  euclid_assert (△ P:R:T).similar (△ S:U:Q)
  euclid_apply Triangle.similar_if (△ P:R:T) (△ S:U:Q)
  euclid_finish




theorem Triangle_Thm09 : ∀ (U W Z V X Y : Point) (UW WZ ZU VX XY YV : Line),
  formTriangle U W Z UW WZ ZU ∧
  formTriangle V X Y VX XY YV ∧
  ∠ W:U:Z = ∠ V:Y:X ∧
  ∠ U:W:Z = ∠ Y:V:X →
  |(U─W)| / |(V─Y)| = |(W─Z)| / |(V─X)| :=
by
  euclid_intros
  euclid_assert (△ U:W:Z).similar (△ Y:V:X)
  euclid_apply Triangle.similar_if (△ U:W:Z) (△ Y:V:X)
  euclid_finish




theorem Triangle_Thm13 : ∀ (U W X T V Y : Point) (UW WX XU TV VY YT : Line),
  formTriangle U W X UW WX XU ∧
  formTriangle T V Y TV VY YT ∧
  ∠ T:Y:V = ∠ W:U:X ∧
  ∠ Y:T:V = ∠ U:W:X →
  |(V─Y)| / |(U─X)| = |(T─V)| / |(W─X)| :=
by
  euclid_intros
  euclid_assert (△ T:V:Y).similar (△ W:X:U)
  euclid_apply Triangle.similar_if (△ T:V:Y) (△ W:X:U)
  euclid_finish




theorem Triangle_Thm18 : ∀ (S T V R U W : Point) (ST TV VS RU UW WR : Line),
  formTriangle S T V ST TV VS ∧
  formTriangle R U W RU UW WR ∧
  ∠ S:V:T = ∠ W:R:U ∧
  ∠ V:S:T = ∠ R:W:U →
  |(S─V)| / |(R─W)| = |(T─V)| / |(R─U)| :=
by
  euclid_intros
  euclid_assert (△ S:T:V).similar (△ W:U:R)
  euclid_apply Triangle.similar_if (△ S:T:V) (△ W:U:R)
  euclid_finish




theorem Triangle_Thm19 : ∀ (V W X S U T : Point) (VW WX XV SU UT TS : Line),
  formTriangle V W X VW WX XV ∧
  formTriangle S U T SU UT TS ∧
  ∠ W:V:X = ∠ U:S:T ∧
  ∠ V:W:X = ∠ S:U:T →
  |(W─X)| / |(T─U)| = |(V─X)| / |(S─T)| :=
by
  euclid_intros
  euclid_assert (△ V:W:X).similar (△ S:U:T)
  euclid_apply Triangle.similar_if (△ V:W:X) (△ S:U:T)
  euclid_finish




theorem Triangle_Thm06 : ∀ (G H I J K : Point) (GK HJ GI HK : Line),
  distinctPointsOnLine G K GK ∧
  distinctPointsOnLine H J HJ ∧
  distinctPointsOnLine G I GI ∧
  distinctPointsOnLine H K HK ∧
  GK ≠ GI ∧
  HK ≠ GK ∧
  HJ ≠ HK ∧
  H.onLine GI ∧ between G H I ∧
  GI.intersectsLine HK ∧
  GI.intersectsLine HJ ∧ J.sameSide K GI ∧
  ¬ GK.intersectsLine HJ →
  ∠ H:G:K + ∠ H:K:G + ∠ G:H:K = ∟ + ∟ :=
by
  euclid_intros
  have : ∠ H:G:K = ∠ I:H:J := by
    euclid_apply Elements.Book1.proposition_29'''' J K I H G HJ GK GI
    euclid_finish
  have : ∠ G:K:H = ∠ J:H:K := by
    euclid_apply Elements.Book1.proposition_29''' J G H K HJ GK HK
    euclid_finish
  euclid_assert ∠ I:H:K = ∠ H:G:K + ∠ G:K:H
  have : ∠ G:H:K + ∠ I:H:K = ∟ + ∟ := by
    euclid_apply Elements.Book1.proposition_13 K H I G HK GI
    euclid_finish
  euclid_finish




theorem Triangle_Thm10 : ∀ (Q S T R U V : Point) (QS ST TQ RU UV VR : Line),
  formTriangle Q S T QS ST TQ ∧
  formTriangle R U V RU UV VR ∧
  ∠ U:R:V = ∠ S:T:Q ∧
  |(R─V)| / |(Q─T)| = |(R─U)| / |(S─T)| →
  ∠ R:U:V = ∠ Q:S:T :=
by
  euclid_intros
  euclid_assert (△ R:U:V).similar (△ T:S:Q)
  euclid_apply Triangle.similar_if (△ R:U:V) (△ T:S:Q)
  euclid_finish




theorem Triangle_Thm05 : ∀ (E F G H : Point) (EF FG GE EH : Line),
  formTriangle E F G EF FG GE ∧
  distinctPointsOnLine E H EH ∧
  FG.intersectsLine EH ∧ H.onLine FG ∧ between F H G ∧
  ∠ H:E:F = ∠ H:E:G ∧
  |(E─G)| = |(E─F)| →
  |(G─H)| = |(F─H)| :=
by
  euclid_intros
  euclid_assert (△ E:F:H).congruent (△ E:G:H)
  euclid_apply Triangle.congruent_if (△ E:F:H) (△ E:G:H)
  euclid_finish




theorem Triangle_Thm12 : ∀ (I J K F G H : Point) (IJ JK KI FG GH HF : Line),
  formTriangle I J K IJ JK KI ∧
  formTriangle F G H FG GH HF ∧
  ∠ J:I:K = ∠ H:F:G ∧
  ∠ I:K:J = ∠ F:G:H →
  |(I─K)| / |(F─G)| = |(J─K)| / |(G─H)| :=
by
  euclid_intros
  euclid_assert (△ I:J:K).similar (△ F:H:G)
  euclid_apply (△ I:J:K).similar_if (△ F:H:G)
  euclid_finish




theorem Triangle_Thm07 : ∀ (T W Y U V X : Point) (TW WY YT UV VX XU : Line),
  formTriangle T W Y TW WY YT ∧
  formTriangle U V X UV VX XU ∧
  ∠ W:T:Y = ∠ U:V:X ∧
  |(T─Y)| / |(U─V)| = |(T─W)| / |(V─X)| →
  ∠ T:W:Y = ∠ U:X:V :=
by
  euclid_intros
  euclid_assert (△ T:W:Y).similar (△ V:X:U)
  euclid_apply Triangle.similar_if (△ T:W:Y) (△ V:X:U)
  euclid_finish




theorem Triangle_Thm04 : ∀ (U V W X : Point) (UV VW WU UX : Line),
  formTriangle U V W UV VW WU ∧
  distinctPointsOnLine U X UX ∧
  VW.intersectsLine UX ∧ X.onLine VW ∧ between V X W ∧
  ∠ U:V:W = ∠ U:W:V ∧
  ∠ U:X:V = ∟ ∧ ∠ U:X:W = ∟ →
  |(U─W)| = |(U─V)| :=
by
  euclid_intros
  euclid_assert (△ U:V:X).congruent (△ U:W:X)
  euclid_apply Triangle.congruent_if (△ U:V:X) (△ U:W:X)
  euclid_finish




theorem Congruent_Thm16 : ∀ (P Q R S T : Point) (PQ QR RS ST PT PS QS : Line),
  formTriangle P S T PS ST PT ∧
  formTriangle Q R S QR RS QS ∧
  formTriangle P Q S PQ QS PS ∧
  P.opposingSides R QS ∧ Q.sameSide R PS ∧
  Q.opposingSides T PS ∧ P.sameSide T QS ∧
  |(S─T)| = |(R─S)| ∧
  ∠ Q:R:S = ∟ ∧
  ∠ Q:S:R = ∠ P:S:T ∧
  ∠ P:T:S = ∟ →
  |(P─T)| = |(Q─R)| :=
by
  euclid_intros
  euclid_assert (△ P:S:T).congruent (△ Q:S:R)
  euclid_apply Triangle.congruent_if (△ P:S:T) (△ Q:S:R)
  euclid_finish




theorem Congruent_Thm03 : ∀ (P Q R S T : Point) (PS ST PT RS RT : Line),
  formTriangle P S T PS ST PT ∧
  formTriangle R S T RS ST RT ∧
  P.sameSide R ST ∧
  twoLinesIntersectAtPoint PS RT Q ∧
  ∠ S:P:T = ∠ T:R:S ∧
  ∠ R:S:T = ∟ ∧
  ∠ P:T:S = ∟ →
  (△ R:S:T).congruent (△ P:T:S) :=
by
  euclid_intros
  euclid_assert ∠ P:T:S = ∠ R:S:T
  euclid_finish




theorem Congruent_Thm08 : ∀ (P Q R S T : Point) (PQ QR RS ST PT PS QS : Line),
  formTriangle P S T PS ST PT ∧
  formTriangle Q R S QR RS QS ∧
  formTriangle P Q S PQ QS PS ∧
  P.opposingSides R QS ∧ Q.sameSide R PS ∧
  Q.opposingSides T PS ∧ P.sameSide T QS ∧
  ∠ R:Q:S = ∠ S:P:T ∧
  |(P─T)| = |(Q─R)| ∧
  |(P─Q)| = |(Q─S)| ∧
  |(Q─S)| = |(S─P)| →
  (△ P:S:T).congruent (△ Q:S:R) :=
by
  euclid_intros
  euclid_finish




theorem Congruent_Thm15 : ∀ (S T U V : Point) (ST TU UV SV SU : Line),
  formTriangle S T U ST TU SU ∧
  formTriangle S U V SU UV SV ∧
  V.opposingSides T SU ∧
  ∠ U:V:S = ∟ ∧
  ∠ U:S:V = ∠ S:U:T ∧
  ∠ S:T:U = ∟ →
  |(U─V)| = |(S─T)| :=
by
  euclid_intros
  euclid_assert (△ S:U:V).congruent (△ U:S:T)
  euclid_apply Triangle.congruent_if (△ S:U:V) (△ U:S:T)
  euclid_finish




theorem Congruent_Thm17 : ∀ (R S T U V : Point) (RT SU ST RU : Line),
  formTriangle R U V RU SU RT ∧
  formTriangle S T V ST RT SU ∧
  between R V T ∧
  between S V U ∧
  |(U─V)| = |(T─V)| ∧
  |(S─V)| = |(R─V)| →
  |(R─U)| = |(S─T)| :=
by
  euclid_intros
  have : ∠ R:V:U = ∠ S:V:T := by
    euclid_apply Elements.Book1.proposition_15 R T U S V RT SU
    euclid_finish
  euclid_assert (△ R:U:V).congruent (△ S:T:V)
  euclid_apply Triangle.congruent_if (△ R:U:V) (△ S:T:V)
  euclid_finish




theorem Congruent_Thm14 : ∀ (U V W X Y : Point) (UW VX UX VW : Line),
  formTriangle U X Y UX VX UW ∧
  formTriangle V W Y VW UW VX ∧
  between U Y W ∧
  between V Y X ∧
  |(U─Y)| = |(W─Y)| ∧
  |(U─X)| = |(V─W)| ∧
  |(X─Y)| = |(V─Y)| →
  ∠ V:W:Y = ∠ X:U:Y :=
by
  euclid_intros
  euclid_assert (△ U:X:Y).congruent (△ W:V:Y)
  euclid_apply Triangle.congruent_if (△ U:X:Y) (△ W:V:Y)
  euclid_finish




theorem Congruent_Thm02 : ∀ (T U V W : Point) (TU UV TV VW TW : Line),
  formTriangle T U V TU UV TV ∧
  formTriangle T V W TV VW TW ∧
  U.opposingSides W TV ∧
  |(T─U)| = |(V─W)| ∧
  ¬ TU.intersectsLine VW →
  (△ T:U:V).congruent (△ V:W:T) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29''' U W T V TU VW TV
  euclid_finish




theorem Congruent_Thm11 : ∀ (T U V W : Point) (TU UV VW TW TV : Line),
  formTriangle T U V TU UV TV ∧
  formTriangle T V W TV VW TW ∧
  U.opposingSides W TV ∧
  |(T─U)| = |(V─W)| ∧
  ¬ TU.intersectsLine VW →
  (△ T:U:V).congruent (△ V:W:T) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29''' U W T V TU VW TV
  euclid_finish




theorem Congruent_Thm01 : ∀ (A B C D : Point) (AB BC CD DA : Line), ( formQuadrilateral A B C D AB BC CD DA) → (A ≠ C) → (∠ D:A:C = ∠ D:B:C) → ∠ C : D : A + ∠ C : B : A = ∟ + ∟ := by
  euclid_intros
  euclid_apply (cyclic_judge A B C D AB BC CD DA) as P
  euclid_apply (cyclic_property A B C D AB BC CD DA)
  euclid_finish




theorem Congruent_Thm20 : ∀ (F G H I J : Point) (FH FI IG GJ JH : Line),
  formTriangle F I G FI IG FH ∧
  formTriangle G J H GJ JH FH ∧
  between F G H ∧
  I.sameSide J FH ∧
  |(F─G)| = |(H─G)| ∧
  |(G─J)| = |(F─I)| ∧
  |(G─I)| = |(H─J)| →
  ∠ G:J:H = ∠ F:I:G :=
by
  euclid_intros
  euclid_assert (△ F:G:I).congruent (△ G:H:J)
  euclid_apply Triangle.congruent_if (△ F:G:I) (△ G:H:J)
  euclid_finish




theorem Congruent_Thm09 : ∀ (U V W X Y : Point) (UW VX VW UX : Line),
  formTriangle U X Y UX VX UW ∧
  formTriangle V W Y VW UW VX ∧
  between U Y W ∧
  between V Y X ∧
  ∠ V:W:Y = ∠ X:U:Y ∧
  |(W─Y)| = |(U─Y)| →
  (△ V:W:Y).congruent (△ X:U:Y) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_15 U W X V Y UW VX
  euclid_finish




theorem Congruent_Thm13 : ∀ (G H I J K : Point) (GI GJ JH HK KI : Line),
  formTriangle G J H GJ JH GI ∧
  formTriangle H K I HK KI GI ∧
  between G H I ∧
  J.sameSide K GI ∧
  |(G─J)| = |(H─K)| ∧
  ∠ H:K:I = ∠ G:J:H ∧
  ¬ GJ.intersectsLine HK →
  (△ H:I:K).congruent (△ G:H:J) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29'''' K J I H G HK GJ GI
  euclid_finish




theorem Congruent_Thm18 : ∀ (E F G H I : Point) (EG FH EH FG : Line),
  formTriangle E H I EH FH EG ∧
  formTriangle F G I FG EG FH ∧
  between E I G ∧
  between F I H ∧
  |(E─I)| = |(G─I)| ∧
  ¬ EH.intersectsLine FG →
  |(H─I)| = |(F─I)| :=
by
  euclid_intros
  have : ∠ I:E:H = ∠ I:G:F := by
    euclid_apply Elements.Book1.proposition_29''' F H G E FG EH EG
    euclid_finish
  have : ∠ I:F:G = ∠ I:H:E := by
    euclid_apply Elements.Book1.proposition_29''' G E F H FG EH FH
    euclid_finish
  euclid_assert (△ E:H:I).congruent (△ G:F:I)
  euclid_apply Triangle.congruent_if (△ E:H:I) (△ G:F:I)
  euclid_finish




theorem Congruent_Thm19 : ∀ (R S T U : Point) (RS ST RT RU : Line),
  formTriangle R S U RS ST RU ∧
  formTriangle R T U RT ST RU ∧
  between S U T ∧
  |(S─U)| = |(T─U)| ∧
  |(R─S)| = |(R─T)| →
  ∠ R:T:U = ∠ R:S:U :=
by
  euclid_intros
  euclid_assert (△ R:S:U).congruent (△ R:T:U)
  euclid_apply Triangle.congruent_if (△ R:S:U) (△ R:T:U)
  euclid_finish




theorem Congruent_Thm06 : ∀ (R S T U V : Point) (RT SU ST RU : Line),
  formTriangle R U V RU SU RT ∧
  formTriangle S T V ST RT SU ∧
  between R V T ∧
  between S V U ∧
  ∠ S:T:R = ∟ ∧
  |(S─T)| = |(R─U)| ∧
  ∠ U:R:T = ∟ →
  (△ S:T:V).congruent (△ U:R:V) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_15 R T S U V RT SU
  euclid_finish




theorem Congruent_Thm10 : ∀ (Q R S T U : Point) (QS RT QT RS : Line),
  formTriangle Q T U QT RT QS ∧
  formTriangle R S U RS QS RT ∧
  between Q U S ∧
  between R U T ∧
  ∠ R:S:Q = ∟ ∧
  ∠ S:Q:T = ∟ ∧
  |(S─U)| = |(Q─U)| →
  (△ R:S:U).congruent (△ T:Q:U) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_15 Q S T R U QS RT
  euclid_finish




theorem Congruent_Thm05 : ∀ (P Q R S T U : Point) (PR PT QT RU : Line),
  formTriangle P R U PR RU PT ∧
  formTriangle P Q T PR QT PT ∧
  twoLinesIntersectAtPoint QT RU S ∧
  between P Q R ∧
  between P U T ∧
  ∠ P:R:U = ∠ P:T:Q ∧
  |(Q─T)| = |(R─U)| →
  (△ P:R:U).congruent (△ P:T:Q) :=
by
  euclid_intros
  euclid_assert ∠ U:P:R = ∠ Q:P:T
  euclid_finish




theorem Congruent_Thm12 : ∀ (Q R S T U : Point) (QS RT QT RS : Line),
  formTriangle Q T U QT RT QS ∧
  formTriangle R S U RS QS RT ∧
  between Q U S ∧
  between R U T ∧
  ∠ S:Q:T = ∟ ∧
  ∠ Q:S:R = ∟ ∧
  |(Q─U)| = |(S─U)| →
  (△ Q:T:U).congruent (△ S:R:U) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_15 R T S Q U RT QS
  euclid_finish




theorem Congruent_Thm07 : ∀ (W X Y Z : Point) (WX XY WY YZ WZ : Line),
  formTriangle W X Y WX XY WY ∧
  formTriangle W Y Z WY YZ WZ ∧
  X.opposingSides Z WY ∧
  |(W─X)| = |(Y─Z)| ∧
  ¬ WX.intersectsLine YZ →
  (△ W:Y:Z).congruent (△ Y:W:X) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29''' X Z W Y WX YZ WY
  euclid_finish




theorem Congruent_Thm04 : ∀ (U V W X Y : Point) (UW VX UX WY VY : Line),
  formTriangle U V X UW VX UX ∧
  formTriangle V W Y UW WY VY ∧
  between U V W ∧
  X.sameSide Y UW ∧
  ∠ V:Y:W = ∠ U:X:V ∧
  |(U─X)| = |(V─Y)| ∧
  ¬ UX.intersectsLine VY →
  (△ V:W:Y).congruent (△ U:V:X) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29'''' Y X W V U VY UX UW
  euclid_finish




theorem Similarity_Thm16 : ∀ (Q R S T U : Point) (QS SU QU RT : Line),
  formTriangle Q S U QS SU QU ∧
  formTriangle R T U RT QU SU ∧
  between Q T U ∧
  between S R U ∧
  |(R─U)| / |(S─U)| = |(T─U)| / |(Q─U)| →
  (△ R:T:U).similar (△ S:Q:U) :=
by
  euclid_intros
  euclid_finish




theorem Similarity_Thm03 : ∀ (V W X Y Z : Point) (VW WZ VZ XY : Line),
  formTriangle V W Z VW WZ VZ ∧
  formTriangle X Y Z XY VZ WZ ∧
  between W X Z ∧
  between V Y Z ∧
  ¬ XY.intersectsLine VW →
  (△ X:Y:Z).similar (△ W:V:Z) :=
by
  euclid_intros
  have : ∠ X:Y:Z = ∠ W:V:Z := by
    euclid_apply Elements.Book1.proposition_29'''' X W Z Y V XY VW VZ
    euclid_finish
  euclid_finish




theorem Similarity_Thm08 : ∀ (G H I J K : Point) (GH GI HI JK : Line),
  formTriangle G H I GH HI GI ∧
  formTriangle G J K GH JK GI ∧
  between G J H ∧
  between G K I ∧
  |(G─J)| / |(G─H)| = |(G─K)| / |(G─I)| →
  (△ G:J:K).similar (△ G:H:I) :=
by
  euclid_intros
  euclid_finish




theorem Similarity_Thm15 : ∀ (V W X Y Z : Point) (VY WX VW XY : Line),
  formTriangle V Y Z VY XY VW ∧
  formTriangle W X Z WX XY VW ∧
  between V Z W ∧
  between X Z Y ∧
  ∠ X:W:Z = ∠ V:Y:Z →
  (△ W:X:Z).similar (△ Y:V:Z) :=
by
  euclid_intros
  have : ∠ V:Z:Y = ∠ W:Z:X := by
    euclid_apply Elements.Book1.proposition_15 V W X Y Z VW XY
    euclid_finish
  euclid_finish




theorem Similarity_Thm17 : ∀ (G H I J : Point) (GJ IJ GI HJ : Line),
  formTriangle G H J GI HJ GJ ∧
  formTriangle H I J GI IJ HJ ∧
  between G H I ∧
  ∠ G:J:I = ∟ ∧
  ∠ J:H:I = ∟ ∧ ∠ G:H:J = ∟ →
  (△ H:I:J).similar (△ H:J:G) :=
by
  euclid_intros
  -- euclid_assert ∠ I:H:J = ∠ G:H:J
  have : ∠ I:G:J + ∠ G:I:J = ∟ := by
    euclid_apply extend_point GI G I as X
    euclid_apply Elements.Book1.proposition_32 J G I X GJ GI IJ
    euclid_finish
  have : ∠ I:G:J + ∠ G:J:H = ∟ := by
    euclid_apply extend_point GJ G J as Y
    euclid_apply Elements.Book1.proposition_32 H G J Y GI GJ HJ
    euclid_finish
  -- euclid_assert ∠ G:J:H = ∠ G:I:J
  euclid_finish




theorem Similarity_Thm14 : ∀ (V W X Y Z : Point) (VZ XY VY XZ : Line),
  formTriangle V W Z VY XZ VZ ∧
  formTriangle W X Y XZ XY VY ∧
  between V W Y ∧
  between X W Z ∧
  |(W─Z)| / |(W─X)| = |(V─W)| / |(W─Y)| →
  (△ V:W:Z).similar (△ Y:W:X) :=
by
  euclid_intros
  have : ∠ X:W:Y = ∠ V:W:Z := by
    euclid_apply Elements.Book1.proposition_15 X Z V Y W XZ VY
    euclid_finish
  euclid_finish




theorem Similarity_Thm02 : ∀ (R S T U V : Point) (ST UV SV TU : Line),
  formTriangle S T R ST TU SV ∧
  formTriangle U V R UV SV TU ∧
  between T R U ∧
  between S R V ∧
  ¬ UV.intersectsLine ST →
  (△ R:U:V).similar (△ R:T:S) :=
by
  euclid_intros
  have : ∠ S:R:T = ∠ U:R:V := by
    euclid_apply Elements.Book1.proposition_15 T U V S R TU SV
    euclid_finish
  have : ∠ V:U:R = ∠ R:T:S := by
    euclid_apply Elements.Book1.proposition_29''' V S U T UV ST TU
    euclid_finish
  euclid_finish




theorem Similarity_Thm11 : ∀ (U V W X Y : Point) (VX WY VY WX : Line),
  formTriangle U V X VY VX WX ∧
  formTriangle U W Y WX WY VY ∧
  between V U Y ∧
  between W U X ∧
  |(U─V)| / |(U─W)| = |(U─X)| / |(U─Y)| →
  (△ U:V:X).similar (△ U:W:Y) :=
by
  euclid_intros
  have : ∠ W:U:Y = ∠ V:U:X := by
    euclid_apply Elements.Book1.proposition_15 X W V Y U WX VY
    euclid_finish
  euclid_finish




theorem Similarity_Thm01 : ∀ (E F G H I : Point) (EI FH EF HI : Line),
  formTriangle E F G EF FH EI ∧
  formTriangle H I G HI EI FH ∧
  between E G I ∧
  between F G H ∧
  ∠ H:I:G = ∠ E:F:G →
  (△ G:H:I).similar (△ G:E:F) :=
by
  euclid_intros
  have : ∠ E:G:F = ∠ H:G:I := by
    euclid_apply Elements.Book1.proposition_15 E I H F G EI FH
    euclid_finish
  euclid_finish




theorem Similarity_Thm20 : ∀ (F G H I : Point) (FH FI HI GI : Line),
  formTriangle F G I FH GI FI ∧
  formTriangle G H I FH HI GI ∧
  between F G H ∧
  ∠ F:G:I = ∟ ∧ ∠ I:G:H = ∟ ∧
  ∠ H:I:F = ∟ →
  (△ F:H:I).similar (△ I:H:G) :=
by
  euclid_intros
  -- euclid_assert ∠ H:I:F = ∠ H:G:I
  euclid_finish




theorem Similarity_Thm09 : ∀ (P Q R S T : Point) (PR QS PS QR : Line),
  formTriangle P R T PR QR PS ∧
  formTriangle Q S T QS PS QR ∧
  between P T S ∧
  between Q T R ∧
  ¬ QS.intersectsLine PR →
  (△ Q:S:T).similar (△ R:P:T) :=
by
  euclid_intros
  have : ∠ P:T:R = ∠ Q:T:S := by
    euclid_apply Elements.Book1.proposition_15 P S Q R T PS QR
    euclid_finish
  have : ∠ Q:S:T = ∠ R:P:T := by
    euclid_apply Elements.Book1.proposition_29''' Q R S P QS PR PS
    euclid_finish
  euclid_finish




theorem Similarity_Thm13 : ∀ (P Q R S T : Point) (PR QS PS QR : Line),
  formTriangle P R T PR QR PS ∧
  formTriangle Q S T QS PS QR ∧
  between P T S ∧
  between Q T R ∧
  ¬ PR.intersectsLine QS →
  (△ P:R:T).similar (△ S:Q:T) :=
by
  euclid_intros
  have : ∠ Q:T:S = ∠ P:T:R := by
    euclid_apply Elements.Book1.proposition_15 P S R Q T PS QR
    euclid_finish
  have: ∠ R:P:T = ∠ Q:S:T := by
    euclid_apply Elements.Book1.proposition_29''' R Q P S PR QS PS
    euclid_finish
  euclid_finish




theorem Similarity_Thm18 : ∀ (T U V W : Point) (UV VW UW TW : Line),
  formTriangle T V W UV VW TW ∧
  formTriangle T U W UV UW TW ∧
  between U T V ∧
  ∠ V:W:U = ∟ ∧
  ∠ W:T:U = ∟ ∧ ∠ V:T:W = ∟ →
  (△ T:U:W).similar (△ T:W:V) :=
by
  euclid_intros
  -- euclid_assert ∠ U:T:W = ∠ V:T:W
  have : ∠ W:V:U + ∠ V:U:W = ∟ := by
    euclid_apply extend_point UV V U as X
    euclid_apply Elements.Book1.proposition_32 W V U X VW UV UW
    euclid_finish
  have : ∠ W:V:U + ∠ T:W:V = ∟ := by
    euclid_apply extend_point TW W T as Y
    euclid_apply Elements.Book1.proposition_32 V W T Y VW TW UV
    euclid_finish
  -- euclid_assert ∠ T:W:V = ∠ V:U:W
  euclid_finish




theorem Similarity_Thm19 : ∀ (H I J K : Point) (HI IJ HJ IK : Line),
  formTriangle H I K HI IK HJ ∧
  formTriangle I J K IJ HJ IK ∧
  between H K J ∧
  ∠ H:K:I = ∟ ∧ ∠ I:K:J = ∟ ∧
  ∠ H:I:J = ∟ →
  (△ I:J:K).similar (△ H:I:K) :=
by
  euclid_intros
  -- euclid_assert ∠ I:K:J = ∠ H:K:I
  have : ∠ K:H:I + ∠ H:I:K = ∟ := by
    euclid_apply extend_point HJ H K as X
    euclid_apply Elements.Book1.proposition_32 I H K X HI HJ IK
    euclid_finish
  have : ∠ I:H:J + ∠ H:J:I = ∟ := by
    euclid_apply extend_point HJ H J as Y
    euclid_apply Elements.Book1.proposition_32 I H J Y HI HJ IJ
    euclid_finish
  -- euclid_assert ∠ H:I:K = ∠ H:J:I
  euclid_finish




theorem Similarity_Thm06 : ∀ (U V W X Y : Point) (VY WX VW XY : Line),
  formTriangle U V Y VW VY XY ∧
  formTriangle U W X VW WX XY ∧
  between V U W ∧
  between X U Y ∧
  ¬ WX.intersectsLine VY →
  (△ U:W:X).similar (△ U:V:Y) :=
by
  euclid_intros
  have : ∠ V:U:Y = ∠ W:U:X := by
    euclid_apply Elements.Book1.proposition_15 V W X Y U VW XY
    euclid_finish
  have : ∠ U:X:W = ∠ U:Y:V := by
    euclid_apply Elements.Book1.proposition_29''' W V X Y WX VY XY
    euclid_finish
  euclid_finish




theorem Similarity_Thm10 : ∀ (P Q R S T : Point) (PQ ST PT QS : Line),
  formTriangle P R T PQ ST PT ∧
  formTriangle Q S R QS ST PQ ∧
  between P R Q ∧
  between S R T ∧
  ∠ R:P:T = ∠ R:S:Q →
  (△ P:R:T).similar (△ S:R:Q) :=
by
  euclid_intros
  have : ∠ Q:R:S = ∠ P:R:T := by
    euclid_apply Elements.Book1.proposition_15 S T P Q R ST PQ
    euclid_finish
  euclid_finish




theorem Similarity_Thm05 : ∀ (F G H I J : Point) (FI GH FH GI : Line),
  formTriangle F I J FI GI FH ∧
  formTriangle G H J GH FH GI ∧
  between F J H ∧
  between G J I ∧
  ¬ FI.intersectsLine GH →
  (△ F:I:J).similar (△ H:G:J) :=
by
  euclid_intros
  have : ∠ G:J:H = ∠ F:J:I := by
    euclid_apply Elements.Book1.proposition_15 G I H F J GI FH
    euclid_finish
  have : ∠ J:F:I = ∠ G:H:J := by
    euclid_apply Elements.Book1.proposition_29''' G I H F GH FI FH
    euclid_finish
  euclid_finish




theorem Similarity_Thm12 : ∀ (S T U V W : Point) (ST TW SW UV : Line),
  formTriangle S T W ST TW SW ∧
  formTriangle U V W UV TW SW ∧
  between S U W ∧
  between T V W ∧
  ∠ S:T:W + ∠ T:V:U = ∟ + ∟ →
  (△ U:V:W).similar (△ S:T:W) :=
by
  euclid_intros
  have : ∠ U:V:W + ∠ T:V:U = ∟ + ∟ := by
    euclid_apply Elements.Book1.proposition_13 U V T W UV TW
    euclid_finish
  -- euclid_assert ∠ U:V:W = ∠ S:T:V
  euclid_finish




theorem Similarity_Thm07 : ∀ (E F G H I : Point) (EF HI EI FH : Line),
  formTriangle E F G EF FH EI ∧
  formTriangle H I G HI EI FH ∧
  between E G I ∧
  between F G H ∧
  |(F─G)| / |(G─H)| = |(E─G)| / |(G─I)| →
  (△ E:F:G).similar (△ I:H:G) :=
by
  euclid_intros
  have : ∠ H:G:I = ∠ E:G:F := by
    euclid_apply Elements.Book1.proposition_15 E I H F G EI FH
    euclid_finish
  euclid_finish




theorem Similarity_Thm04 : ∀ (E F G H I : Point) (EF GH EG FH : Line),
  formTriangle E F I EF FH EG ∧
  formTriangle G H I GH FH EG ∧
  between E I G ∧
  between H I F ∧
  ∠ H:G:I = ∠ F:E:I →
  (△ G:H:I).similar (△ E:F:I) :=
by
  euclid_intros
  have : ∠ E:I:F = ∠ G:I:H := by
    euclid_apply Elements.Book1.proposition_15 E G H F I EG FH
    euclid_finish
  euclid_finish



