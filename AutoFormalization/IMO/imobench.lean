import SystemE
import UniGeo.Relations
import UniGeo.Abbre
theorem problem_imo_2020_p1:
  ∀ (A B C D P Q R Z X : Point) (AB BC CD DA DQ l CR: Line),
  (formQuadrilateral A B C D AB BC CD DA) ∧
  (P.sameSide C AB) ∧ (P.sameSide A CD) ∧ (P.sameSide D BC) ∧
  (P.sameSide B DA) ∧ (B ≠ P) ∧ (A ≠ P) ∧ (C ≠ P) ∧ (D ≠ P) ∧
  (2 * (∠P : A : D : ℝ) = (∠P : B : A : ℝ)) ∧
  (3 * (∠P : A : D : ℝ) = (∠D : P : A : ℝ)) ∧
  (2 * (∠C : B : P : ℝ) = (∠C : A : P : ℝ)) ∧
  (3 * (∠C : B : P : ℝ) = (∠B : P : C : ℝ)) ∧
  (∠Q : D : A : ℝ) = (∠Q : D : P : ℝ) ∧
  (∠R : C : B : ℝ) = (∠R : C : B : ℝ) ∧
  (perpBisector A B l) ∧
  (distinctPointsOnLine D Q DQ) ∧
  (distinctPointsOnLine C R CR) →
  concurrent DQ CR l := by
  sorry

theorem problem_imo_2021_p3: ∀ (A B C D E F X O₁ O₂: Point) (AB BC CA: Line), formAcuteTriangle A B C AB BC CA ∧
D.sameSide A BC ∧
D.sameSide C AB ∧
D.sameSide B CA ∧
|(A─B)| > |(A─C)| ∧
E.onLine AC ∧ ∠A:D:E = ∠B:C:D ∧
F.onLine AB ∧ ∠F:D:A = ∠D:B:C ∧
X.onLine AC ∧ |(C─X)| = |(B─X)| ∧
circumCentre O₁ A D C ∧ circumCentre O₂ E X D → concurrent BC EF O₁O₂ := by
  sorry

theorem problem_imo_2021_p4 : ∀ (A B C D Y T Z X : Point) (AB BC CD DA: Line) (Γ Ω: Circle), formQuadrilateral A B C D AB BC CD DA ∧
tangentLine AB Γ ∧ tangentLine BC Γ ∧ tangentLine CD Γ ∧ tangentLine DA Γ ∧
circumCircle Ω A I C ∧
X.onLine AB ∧ X.onCircle Ω ∧
Z.onLine BC ∧ Z.onCircle Ω ∧
Y.onLine DA ∧ Y.onCircle Ω ∧
T.onLine CD ∧ T.onCircle Ω → |(A─D)| + |(D─T)| + |(T─X)| + |(X─A)| = |(C─D)| + |(D─Y)| + |(Y─Z)| + |(Z─C)|:= by
  sorry

theorem problem_imo_2022_p4 : ∀ (A B C D T Y T R S: Point) (AB BC CD DE EA EA CT: Line), (formPentagon A B C D E AB BC CD DE EA) ∧
|(T─B)|=|(T─D)| ∧ |(T─C)|=|(T─E)| ∧ |(T─B)|=|(T─D)| ∧ ∠A:B:T = ∠T:E:A ∧
twoLinesIntersectAtPoint AB CD P ∧ distinctPointsOnLine C T CT ∧ twoLinesIntersectAtPoint AB CT Q ∧
between P B A ∧ between B A Q ∧
distinctPointsOnLine D T DT ∧
twoLinesIntersectAtPoint CD EA R
∧ twoLinesIntersectAtPoint DT EA S
∧ between R E A ∧ between E A S
→ cyclic P S Q R := by
sorry

theorem problem_imo_2023_p2 : ∀ (A B C D E S L P X: Point) (AB BC CA ADE BE DL l BS: Line) (Ω ω: Circle), formAcuteTriangle A B C AB BC CA ∧
|(A─B)| < |(A─C)| ∧ circumCircle Ω A B C ∧
S.onCircle Ω ∧ |(S─C)| = |(S─B)| ∧ S.sameSide A BC
∧ threePointsOnLine A D E ADE ∧ perpLine ADE BC ∧
D.onLine BS ∧ E.onCircle Ω ∧ threePointsOnLine B E L BE ∧
distinctPointsOnLine D L DL ∧ ¬(BE.intersectsLine DL) ∧
circumCircle ω B D L ∧
P.onCircle Ω ∧ P.onCircle ω ∧ P ≠ B ∧
distinctPointsOnLine B S BS ∧
tangentAtPoint l ω P ∧ twoLinesIntersectAtPoint l BS X
 → ∠ X:A:B = ∠X:A:C := by
sorry

theorem problem_isl_2023_p2 : ∀ (A B C P S D Q E O : Point)
  (AB BC CA SP BP CQ DQ AE BE : Line)
  (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  |(A─C)| > |(B─C)| ∧
  circumCircle Ω A B C ∧
  circumCentre O A B C ∧
  O.isCentre Ω ∧
  P.onLine CA ∧
  |(B─C)| = |(C─P)| ∧
  S.onLine AB ∧
  distinctPointsOnLine S P SP ∧
  perpLine SP AB ∧
  distinctPointsOnLine B P BP ∧
  D.onLine BP ∧
  D.onCircle Ω ∧
  Q.onLine SP ∧
  |(P─Q)| = |(O─A)| ∧
  between S P Q ∧
  distinctPointsOnLine C Q CQ ∧
  distinctPointsOnLine D Q DQ ∧
  perpLine AE CQ ∧
  perpLine BE DQ
  → E.onCircle Ω := by
  sorry

theorem problem_Elements_Prop6 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c = ∠ a:c:b) →
  |(a─b)| = |(a─c)| :=
by
  sorry

theorem problem_Elements_Prop37 : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ distinctPointsOnLine a d AD ∧
  ¬(AD.intersectsLine BC) ∧ d.sameSide c AB →
  Triangle.area △ a:b:c = Triangle.area △ d:b:c :=
by
  sorry

theorem problem_UniGeo_Quadrilateral1 : ∀ (Q R S T : Point) (QR ST RS QT QS : Line),
  formQuadrilateral Q R T S QR ST QT RS ∧
  distinctPointsOnLine Q S QS ∧
  ∠ Q:R:S = ∟ ∧
  ∠ Q:T:S = ∟ ∧
  ∠ Q:S:R = ∠ S:Q:T →
  |(S─T)| = |(Q─R)| := by
  sorry

theorem problem_UniGeo_Similarity20 : ∀ (F G H I : Point) (FH FI HI GI : Line),
  formTriangle F G I FH GI FI ∧
  formTriangle G H I FH HI GI ∧
  between F G H ∧
  ∠ F:G:I = ∟ ∧ ∠ I:G:H = ∟ ∧
  ∠ H:I:F = ∟ →
  (△ F:H:I).similar (△ I:H:G) :=
by
  sorry

theorem problem_UniGeo_Triangle3 : ∀ (H I J K : Point) (HI IJ JH HK : Line),
  formTriangle H I J HI IJ JH ∧
  distinctPointsOnLine H K HK ∧
  IJ.intersectsLine HK ∧ K.onLine IJ ∧ between I K J ∧
  ∠ I:H:K = ∠ J:H:K ∧
  |(H─I)| = |(H─J)| →
  ∠ H:K:I = ∠ H:K:J :=
by
  sorry

theorem problem_imo_2004_p5 :
∀ (A B C D P : Point) (AB BC CD DA BD : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  distinctPointsOnLine B D BD ∧
  ¬(∠A:B:D = ∠D:B:C) ∧
  ¬(∠C:D:B = ∠B:D:A) ∧
  ∠P:B:C = ∠D:B:A ∧
  ∠P:D:C = ∠B:D:A
→ (cyclic A B C D ↔ |(A─P)| = |(C─P)|) :=
by sorry

theorem problem_imo_2008_p6 :
  ∀ (A B C D : Point) (AB BC CD DA AC : Line) (ω₁ ω₂ ω : Circle),
    formQuadrilateral A B C D AB BC CD DA ∧
    formTriangle A B C AB BC AC ∧
    formTriangle A D C DA DC AC ∧
    tangentLine AB ω₁ ∧ tangentLine BC ω₁ ∧ tangentLine AC ω₁ ∧
    tangentLine DA ω₂ ∧ tangentLine DC ω₂ ∧ tangentLine AC ω₂ ∧
    tangentLine AB ω ∧ tangentLine BC ω ∧ tangentLine DA ω ∧ tangentLine CD ω
    →
    ∃ (P : Point) (L₁ L₂ : Line),
      tangentLine L₁ ω₁ ∧
      tangentLine L₁ ω₂ ∧
      tangentLine L₂ ω₁ ∧
      tangentLine L₂ ω₂ ∧
      (L₁ ≠ L₂) ∧
      twoLinesIntersectAtPoint L₁ L₂ P ∧
      P.onCircle ω
:= by
  sorry

theorem problem_imo_2005_p5 :
∀ (A B C D M P: Point)
  (AB BC CD DA AC BD : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  (|(B─C)| = |(D─A)|) ∧
  twoLinesIntersectAtPoint BC DA M ∧
  twoLinesIntersectAtPoint AC BD P →
  (∃ (S: Point),S ≠ P ∧ ∀(E F Q R : Point) (EF : Line), E.onLine BC ∧ F.onLine DA ∧
  (|(B─E)| = |(D─F)|) ∧ twoLinesIntersectAtPoint BD EF Q ∧
  twoLinesIntersectAtPoint EF AC R → cyclic P Q R S)
:= by
  sorry

theorem problem_imo_2004_p1 :
∀ (A B C M N O R : Point) (AB BC CA : Line) (ω Ω₁ Ω₂ : Circle),
  formAcuteTriangle A B C AB BC CA ∧
  ¬ (|(A─B)| = |(A─C)|) ∧
  midpoint B O C ∧
  O.isCentre ω ∧
  B.onCircle ω ∧
  C.onCircle ω ∧
  M.onLine AB ∧
  M.onCircle ω ∧
  N.onLine AC ∧
  N.onCircle ω ∧
  (∠ B:A:R = ∠ R:A:C) ∧
  (∠ M:O:R = ∠ R:O:N) ∧
  circumCircle Ω₁ B M R ∧
  circumCircle Ω₂ C N R
→ ∃ (X : Point),
  X.onCircle Ω₁ ∧
  X.onCircle Ω₂ ∧
  X.onLine BC
:= by
  sorry

--CO20
--As shown in the figure, in an isosceles triangle $ABC$ with $AB = BC$, $I$ is the incenter, $M$ is the midpoint of $BI$, $P$ is a point on side $AC$ such that $AP = 3PC$, and $PI$ is extended to a point $H$ such that $MH \perp PH$. $Q$ is the midpoint of $AB$ on the circumcircle of $\triangle ABC$. Prove: $BH \perp QH$.
theorem problem_CO20 :
∀ (A B C I M P H Q : Point) (AB BC CA PH MH BH QH: Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(B─C)| ∧
  inCentre I A B C ∧
  midpoint B M I ∧
  between A P C  ∧
  (|(A─P)| = 3 * |(P─C)|) ∧
  between P I H ∧
  distinctPointsOnLine P H PH ∧
  distinctPointsOnLine M H MH ∧
  distinctPointsOnLine B H BH ∧
  distinctPointsOnLine Q H QH ∧
  perpLine PH MH ∧
  cyclic Q B C A ∧
  |(A─Q)| = |(B─Q)|
  → perpLine BH QH :=
by
  sorry

--MP19
--In quadrilateral $ABCD$, $AE \perp BD$ at point $E$, $CF \perp BD$ at point $F$, and point $P$ is the midpoint of $AC$. Prove that $PE = PF$.
theorem problem_MP19 :
∀ (A B C D E F P : Point)
  (AB BC CD DA BD AE CF AC : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  distinctPointsOnLine B D BD ∧
  distinctPointsOnLine A E AE ∧
  E.onLine BD ∧
  perpLine AE BD ∧
  distinctPointsOnLine C F CF ∧
  twoLinesIntersectAtPoint CF BD F ∧
  perpLine CF BD ∧
  distinctPointsOnLine A C AC ∧
  midpoint A P C
→ |(P─E)| = |(P─F)| :=
by sorry

--MP97
--In convex quadrilateral $ABCD$, $\angle BAD = \angle ADC$, and there exists point $E$ on side $BC$ such that $BE = AB$ and $CE = CD$. Draw $EF \parallel AB$, intersecting $AC$ and $AD$ at points $G$ and $F$, respectively. Prove that $EG = GF$.
theorem problem_MP97 :
∀ (A B C D E F G : Point) (AB BC CD DA AC AD EF : Line),
  (formQuadrilateral A B C D AB BC CD DA)
  ∧ (∠B:A:D = ∠A:D:C)
  ∧ (E.onLine BC)
  ∧ (between B E C)
  ∧ (|(B─E)| = |(A─B)|)
  ∧ (|(C─E)| = |(C─D)|)
  ∧ (¬(EF.intersectsLine AB))
  ∧ distinctPointsOnLine E F EF
  ∧ distinctPointsOnLine A C AC
  ∧ (twoLinesIntersectAtPoint EF AC G)
  ∧ (twoLinesIntersectAtPoint EF AD F)
  → (|(E─G)| = |(G─F)|)
:= by
  sorry


--HP71
--Given that in $\triangle ABC$, lines $AD$, $BE$, and $CF$ are the altitudes of $\triangle ABC$. Point $H$ is the orthocenter of $\triangle ABC$, and point $O$ is the circumcenter of $\triangle ABC$. Line $ED$ intersects line $AB$ at point $M$, and line $FD$ intersects line $AC$ at point $N$. Prove that $OH \perp MN$.
theorem problem_HP71 :
  ∀ (A B C D E F H O M N : Point)
    (AB BC CA AD BE CF ED FD MN OH: Line),
    formTriangle A B C AB BC CA ∧
    distinctPointsOnLine A D AD ∧
    distinctPointsOnLine B E BE ∧
    distinctPointsOnLine C F CF ∧
    twoLinesIntersectAtPoint BC AD D ∧ perpLine BC AD ∧
    twoLinesIntersectAtPoint CA BE E ∧ perpLine CA BE ∧
    twoLinesIntersectAtPoint AB CF F ∧ perpLine AB CF ∧
    twoLinesIntersectAtPoint AD BE H ∧ H.onLine CF ∧
    circumCentre O A B C ∧
    orthoCentre H A B C ∧
    distinctPointsOnLine D E ED ∧
    distinctPointsOnLine F D FD ∧
    twoLinesIntersectAtPoint ED AB M ∧
    twoLinesIntersectAtPoint FD AC N ∧
    distinctPointsOnLine O H OH ∧
    distinctPointsOnLine M N MN
  → perpLine OH MN
:= by
  sorry

--HP97
--Given that in $\triangle ABC$, $O$ is the circumcenter, and $I$ is the incenter. Line $OI$ is perpendicular to line $AI$. Prove that $AB + AC = 2BC$.
theorem problem_HP97 :
  ∀ (A B C O I : Point) (AB BC CA OI AI : Line),
  formTriangle A B C AB BC CA ∧
  circumCentre O A B C ∧
  inCentre I A B C ∧
  distinctPointsOnLine O I OI ∧
  distinctPointsOnLine A I AI ∧
  perpLine OI AI
  → (|(A─B)| + |(A─C)|) = (|(B─C)| + |(B─C)|) := by
sorry

--CO21
--As shown in the figure, in an acute-angled triangle $ABC$, $M$ is the midpoint of side $BC$, and point $P$ lies on side $AB$ such that $AP$ bisects $\\angle BAC$. The line $MP$ intersects the excircles of $\\triangle ABP$ and $\\triangle ACP$ at points $D$ and $E$, respectively. Prove: If $DE = MP$, then $BC = 2BP$.
theorem problem_CO19 :
  ∀ (A B C M P D E : Point) (AB BC CA AP MP : Line) (ω₁ ω₂ : Circle),
  formAcuteTriangle A B C AB BC CA ∧
  midpoint M B C ∧
  insideTriangle P A B C AB BC CA ∧
  distinctPointsOnLine A P AP ∧
  ∠B:A:P=∠C:A:P ∧
  distinctPointsOnLine M P MP ∧
  circumCircle ω₁ A B P ∧
  circumCircle ω₂ A C P ∧
  D.onLine MP ∧ D.onCircle ω₁ ∧
  E.onLine MP ∧ E.onCircle ω₂ ∧
  |(D─E)| = |(M─P)|
  → (|(B─C)| = 2 * |(B─P)|) := by
  sorry

--MP9
--In $\triangle ABC$, $\angle A = 3\angle C$ and $BC = 2AB$. Prove that $\angle BAC = 90^\circ$.
theorem problem_MP9 :
  ∀ (A B C : Point) (AB BC CA : Line),
  (formTriangle A B C AB BC CA)
  ∧ (∠ B:A:C = ∠ A:C:B + ∠ A:C:B + ∠ A:C:B)
  ∧ (|(B─C)| = |(A─B)| + |(A─B)|)
  → ∠ B:A:C = ∟
:= by
  sorry

--MP75
--In convex quadrilateral $ABCD$, diagonals $AC$ and $BD$ intersect at point $O$, $AB + AC = DB + DC$, and $OB > OC$. Prove that $OA > OD$.
theorem problem_MP75 :
  ∀ (A B C D O : Point) (AB BC CD DA AC BD : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    distinctPointsOnLine A C AC ∧
    distinctPointsOnLine B D BD ∧
    twoLinesIntersectAtPoint AC BD O ∧
    (|(A─B)| + |(A─C)| = |(D─B)| + |(D─C)|) ∧
    (|(O─B)| > |(O─C)|)
  → (|(O─A)| > |(O─D)|) := by
  sorry

--MP12
--In $\triangle ABC$, $AB = AC$, $\angle A = 20^\circ$, and the angle bisector of $\angle ABC$ intersects $AC$ at point $D$. Prove that $AD = BD + BC$.
theorem problem_MP12 :
∀ (A B C D : Point) (AB BC CA : Line),
  (formTriangle A B C AB BC CA)
  ∧ (|(A─B)| = |(A─C)|)
  ∧ (∠B:A:C = 2/9 * ∟)
  ∧ D.onLine CA
  ∧ between A D C
  ∧ (∠A:B:D = ∠D:B:C)
  → |(A─D)| = (|(B─D)| + |(B─C)|)
:= by
  sorry

--MP10
--In $\triangle ABC$, $AB = AC$ and point $D$ is the midpoint of $AC$. Given that $\angle ABD = 30^\circ$, prove that $\triangle ABC$ is an equilateral triangle.
theorem problem_MP10 : ∀
(A B C D : Point)
(AB BC CA : Line),
formTriangle A B C AB BC CA ∧
|(A─B)| = |(A─C)| ∧
midpoint A D C ∧
(∠A:B:D * 3= ∟ )
→ (|(A─B)|=|(B─C)| ∧ |(B─C)|=|(C─A)|) := by
sorry

--CMO24
-- In triangle \( ABC \), \( I \) is the incenter, and points \( L, M, N \) are the midpoints of segments \( AI, AC, CI \), respectively. Point \( D \) lies on line segment \( AM \), such that \( BC = BD \). In triangle \( ABD \), the incircle touches \( AD, BD \) at points \( E, F \), respectively. Point \( J \) is the circumcenter of triangle \( AIC \), and \( \omega \) is the circumcircle of triangle \( JMD \). Line \( MN \) intersects \( \omega \) again at point \( Q \). Prove: The lines \( PQ, LN, EF \) are concurrent.}

theorem problem_CMO24 :
  ∀ (A B C I L M N D P Q: Point) (AB BC CA AI AC CI AM BD MN JL EF PQ LN: Line),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  midpoint A L I ∧
  midpoint C M A ∧
  midpoint I N C ∧
  between A D M ∧
  distinctPointsOnLine B D BD ∧
  |(B─C)| = |(B─D)| ∧
  inCircle ω AB CA BD ∧
  tangentAtPoint AC ω E ∧
  tangentAtPoint BD ω F ∧
  circumCentre J A I C ∧
  circumCircle ω J M D ∧
  distinctPointsOnLine M N MN ∧
  P.onLine MN ∧
  P.onCircle ω ∧
  distinctPointsOnLine J L JL ∧
  Q.onLine JL ∧
  Q.onCircle ω ∧
  distinctPointsOnLine E F EF ∧
  distinctPointsOnLine L N LN ∧
  distinctPointsOnLine P Q PQ
  → concurrent PQ LN EF := by
  sorry

--HP13
--Given that in $\triangle ABC$, points $D$ and $E$ lie on sides $AB$ and $AC$, respectively, such that $DE \parallel BC$. Lines $BE$ and $CD$ intersect at point $F$. The circumcircle of $\triangle BDF$ is $\odot O$, and the circumcircle of $\triangle CEF$ is $\odot P$. These two circles intersect at point $G$. Prove that $\angle BAF = \angle CAG$.
theorem problem_HP13 :
  ∀ (A B C D E F G : Point) (AB BC CA DE BE CD : Line) (O P : Circle),
  formTriangle A B C AB BC CA ∧
  D.onLine AB ∧ between A D B ∧
  E.onLine AC ∧ between A E C ∧
  distinctPointsOnLine D E DE ∧
  ¬(DE.intersectsLine BC) ∧
  distinctPointsOnLine B E BE ∧
  distinctPointsOnLine C D CD ∧
  twoLinesIntersectAtPoint BE CD F ∧
  circumCircle O B D F ∧
  circumCircle P C E F ∧
  G.onCircle O ∧
  G.onCircle P ∧ G ≠ F
  → ∠B:A:F = ∠C:A:G
:= by
  sorry

--MP35
--In convex quadrilateral $ABCD$, $BC = CD$, $\angle ADB = 30^\circ$, and $\angle ABD - \angle DBC = 60^\circ$. Find $\angle CAD$.
theorem problem_MP35 : ∀
  (A B C D : Point)
  (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  |(B─C)| = |(C─D)| ∧
  ∠A:D:B = 1/3 * ∟ ∧
  ∠A:B:D = ∠D:B:C + 2/3 * ∟
  → ∠C:A:D = 1/3 * ∟ := by
sorry

--MP22
--In equilateral triangle $\triangle ABC$, point $D$ is on side $AB$, and point $E$ is on the extension of $CB$ such that $AD = BE$. Prove that $CD = ED$.
theorem problem_MP22 :
∀ (A B C D E : Point) (AB BC CA : Line),
  (formTriangle A B C AB BC CA)
  ∧ (|(A─B)| = |(B─C)|)
  ∧ (|(B─C)| = |(C─A)|)
  ∧ between A D B
  ∧ between C B E
  ∧ (|(A─D)| = |(B─E)|)
  → (|(C─D)| = |(E─D)|) := by
  sorry

--HP23
--Given that $O$ is the circumcenter of $\triangle ABC$, and points $D$ and $E$ lie on sides $AB$ and $AC$, respectively. Line $OF$ is perpendicular to line $DE$ at point $F$. Points $L$, $M$, and $N$ are the midpoints of line segments $DE$, $BE$, and $CD$, respectively. Prove that points $F$, $L$, $M$, and $N$ are concyclic.
theorem problem_HP23 :
∀ (A B C O D E F L M N : Point) (AB BC CA DE OF : Line),
  formTriangle A B C AB BC CA ∧
  circumCentre O A B C ∧
  between A D B ∧
  between A E C ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine O F OF ∧
  twoLinesIntersectAtPoint OF DE F ∧
  perpLine OF DE ∧
  midpoint D L E ∧
  midpoint B M E ∧
  midpoint C N D
  → cyclic F L M N
:= by
  sorry
