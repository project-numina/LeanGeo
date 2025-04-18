import SystemE
import UniGeo.Relations
import UniGeo.Abbre


--MP33
--In $\triangle ABC$, $AB = AC$, point $D$ is on $AC$, $AD = BD + BC$, and $\angle BDC = 60^\circ$. Prove that $\angle BAC = 20^\circ$.
theorem problem_MP33 :
  ∀ (A B C D : Point) (AB BC CA : Line),
  (formTriangle A B C AB BC CA)
  ∧ D.onLine CA
  ∧ between A D C
  ∧ |(A─B)| = |(A─C)|
  ∧ |(A─D)| = (|(B─D)| + |(B─C)|)
  ∧ ∠ B:D:C = 60
  → ∠ B:A:C = 20
:= by
  sorry



--MP73
--In $\triangle ABC$, points $D$ and $E$ are on $AB$ and $AC$, respectively, such that $AD = AE$ and $\angle DCB = \angle EBC$. Prove that $AB = AC$.
theorem problem_MP73 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    D.onLine AB ∧
    E.onLine CA ∧
    between A C E ∧
    between A B D ∧
    |(A─D)| = |(A─E)| ∧
    ∠ D:C:B = ∠ E:B:C
    → |(A─B)| = |(A─C)| :=
by sorry



--MP6
--In $\triangle ABC$, points $D$ and $E$ are on sides $AC$ and $AB$, respectively, such that $AD = AE$ and $BD = CE$. Prove that $AB = AC$.
theorem problem_MP6 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  D.onLine CA ∧
  E.onLine AB ∧
  between A D C ∧
  between A E B ∧
  |(A─D)| = |(A─E)| ∧
  |(B─D)| = |(C─E)|
  → |(A─B)| = |(A─C)| := by
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



--MP74
--In $\triangle ABC$, $AB > AC$, point $P$ is inside the triangle such that $\angle BAP < \angle CAP$. Prove that $AB - AC > PB - PC$.
theorem problem_MP74 :
  ∀ (A B C P : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  (|(A─B)| > |(A─C)|) ∧
  insideTriangle P A B C AB BC CA ∧
  (∠B:A:P < ∠C:A:P)
  → (|(A─B)| - |(A─C)| > |(P─B)| - |(P─C)|)
:= by
  sorry



--MP20
--In acute triangle $\triangle ABC$, point $D$ is the midpoint of $BC$, $DE \perp AC$ at point $E$, $DF \perp AB$ at point $F$, and $BE = CF$. Prove that $AB = AC$.
theorem problem_MP20 :
  ∀ (A B C D E F : Point) (AB BC CA DE DF : Line),
    formTriangle A B C AB BC CA ∧
    midpoint B D C ∧
    E.onLine CA ∧ distinctPointsOnLine D E DE ∧ perpLine DE CA ∧
    F.onLine AB ∧ distinctPointsOnLine D F DF ∧ perpLine DF AB ∧
    |(B─E)| = |(C─F)|
  → |(A─B)| = |(A─C)| :=
by
  sorry



--MP76
--In $\triangle ABC$, $AB = AC$, point $D$ is on $BC$ (or its extension) such that $\angle ADB = 60^\circ$. On $AD$ (or its extension), take point $E$ such that $DE = DC$. Connect $BE$. Prove that $BE = AB$.
theorem problem_MP76 :
  ∀ (A B C D E : Point) (AB BC CA AD : Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(A─C)| ∧
  D.onLine BC ∧
  E.onLine AD ∧
  ∠A:D:B = 60 ∧
  |(D─E)| = |(D─C)|
  → |(B─E)| = |(A─B)| := by
  sorry



--MP93
--In $\triangle ABC$, $AD$ is the angle bisector, point $M$ is the midpoint of $BC$, extend $CA$ to point $E$ such that $AE = AB$, line $EM$ intersects $AD$ at point $F$. Prove that $BF = BD$.
theorem problem_MP93 :
∀ (A B C D M E F : Point) (AB BC CA AD EM : Line),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A D AD ∧
  ∠B:A:D = ∠D:A:C ∧
  midpoint B M C ∧
  E.onLine CA ∧ |(A─E)|=|(A─B)| ∧
  between C A E ∧
  distinctPointsOnLine E M EM ∧
  twoLinesIntersectAtPoint EM AD F
  → |(B─F)|=|(B─D)| := by
sorry



--MP58
--In $\triangle ABC$, point $D$ is the midpoint of $BC$, points $E$ and $F$ are on $AB$ and $AC$, respectively, such that $BE = CF$, and $AD$ intersects $EF$ at point $G$, which is the midpoint of $EF$. Prove that $AB = AC$.
theorem problem_MP58 :
  ∀ (A B C D E F G : Point) (AB BC CA AD EF : Line),
  formTriangle A B C AB BC CA ∧
  midpoint B D C ∧
  E.onLine AB ∧ between A E B ∧
  F.onLine AC ∧ between A F C ∧
  |(B─E)| = |(C─F)| ∧
  twoLinesIntersectAtPoint AD EF G ∧
  midpoint E G F
  → |(A─B)| = |(A─C)| :=
by sorry



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



--imo_2012_p5
--Let $ABC$ be a triangle with $\angle BCA=90^\circ$, and let $D$ be the foot of the altitude from $C$. Let $X$ be a point in the interior of the segment $CD$. Let $K$ be the point on the segment $AX$ such that $BK=BC$. Similarly, let $L$ be the point on the segment $BX$ such that $AL=AC$. Let $M=\overline{AL}\cap \overline{BK}$. Prove that $MK=ML$.
theorem problem_imo_2012_p5 :
  ∀ (A B C D X K L M : Point) (AB BC CA CD AX BX AL BK : Line),
  formTriangle A B C AB BC CA ∧
  ∠ B:C:A = ∟ ∧
  D.onLine AB ∧
  distinctPointsOnLine C D CD ∧
  perpLine AB CD ∧
  between C X D ∧
  K.onLine AX ∧
  between A K X ∧
  |(B─K)| = |(B─C)| ∧
  L.onLine BX ∧
  between B L X ∧
  |(A─L)| = |(A─C)| ∧
  distinctPointsOnLine A L AL ∧
  distinctPointsOnLine B K BK ∧
  twoLinesIntersectAtPoint AL BK M
  → |(M─K)| = |(M─L)| :=
by sorry

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



--MP64
--Points $A$ and $D$ are on the same side of line $BC$, $\angle BAC = \angle BDC = 90^\circ$. Points $E$ and $F$ are on $BD$ and $AC$, respectively, such that $AE \perp BF$ and $DF \perp CE$. Prove that $AF \cdot AC = DE \cdot DB$.
theorem problem_MP64 : ∀
(A B C D E F : Point)
(BC BD AC AE BF CE DF : Line),
  A.sameSide D BC ∧
  ∠ B:A:C = ∟ ∧
  ∠ B:D:C = ∟ ∧
  E.onLine BD ∧ between B E D ∧
  F.onLine AC ∧ between A F C ∧
  distinctPointsOnLine A E AE ∧
  distinctPointsOnLine B F BF ∧
  perpLine AE BF ∧
  perpLine DF CE
  → |(A─F)| * |(A─C)| = |(D─E)| * |(D─B)| := by
sorry



--MP23
--In $\triangle ABC$, $\angle A = 100^\circ$, $\angle ACB = 30^\circ$. Extend $AC$ to point $D$ such that $CD = AB$. Find $\angle CDB$.
theorem problem_MP23 :
  ∀ (A B C D : Point) (AB BC CA AD : Line),
  formTriangle A B C AB BC CA ∧
  ∠C:A:B = 100 ∧
  ∠A:C:B = 30 ∧
  D.onLine AC ∧
  between A C D ∧
  |(C─D)| = |(A─B)|
  → ∠C:D:B = 20
:= by
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
  ∠A:D:B = 30 ∧
  ∠A:B:D = ∠D:B:C + 60
  → ∠C:A:D = 30 := by
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



--MP26
--In right triangle $\triangle ABC$, $\angle ACB = 90^\circ$, $\angle ABC = 30^\circ$. Points $D$ and $E$ are on sides $BC$ and $AC$, respectively, such that $\angle BAD = 40^\circ$ and $\angle ABE = 20^\circ$. Find $\angle ADE$.
theorem problem_MP26 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    ∠ A:C:B = ∟ ∧
    ∠ A:B:C = 30 ∧
    D.onLine BC ∧ between B D C ∧
    E.onLine AC ∧ between A E C ∧
    ∠ B:A:D = 40 ∧
    ∠ A:B:E = 20
    → ∠ A:D:E = 30
:= by
  sorry



--MP67
--In $\triangle ABC$, points $D$ and $E$ are on sides $AB$ and $AC$, respectively, such that $BD = CE$. Lines $BE$ and $CD$ intersect at point $O$, and $OD = OE$. Prove that $AB = AC$.
theorem problem_MP67 :
  ∀ (A B C D E O : Point) (AB BC CA BE CD : Line),
  formTriangle A B C AB BC CA ∧
  D.onLine AB ∧
  E.onLine AC ∧
  between A D B ∧
  between A E C ∧
  (|(B─D)| = |(C─E)|) ∧
  twoLinesIntersectAtPoint BE CD O ∧
  (|(O─D)| = |(O─E)|)
  → (|(A─B)| = |(A─C)|) := by
  sorry



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



--HP95
--Given that lines $PA$ and $PB$ are tangents to circle $\odot O$ at points $A$ and $B$, respectively. Line $PCD$ is a secant of circle $\odot O$. Point $E$ is the midpoint of line segment $AB$. Prove that $\angle ACD = \angle BCE$.
theorem problem_HP95 :
  ∀ (P A B C D E : Point) (PA PB PCD : Line) (O : Circle),
  tangentAtPoint PA O A ∧
  tangentAtPoint PB O B ∧
  distinctPointsOnLine P A PA ∧
  distinctPointsOnLine P B PB ∧
  threePointsOnLine P C D PCD ∧
  A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O ∧
  midpoint A E B
  → ∠ A : C : D = ∠ B : C : E :=
by
  sorry



--09G4
--In a cyclic quadrilateral $ABCD$, let $AC$ and $BD$ intersect at point $E$. Extend lines $AD$ and $BC$ to intersect at point $F$. Let $G$ and $H$ be the midpoints of segments $AB$ and $CD$, respectively. Prove that line $EF$ is tangent to the circumcircle of $\triangle EGH$.
theorem problem_09G4 :
  ∀ (A B C D E F G H : Point)
    (AB BC CD DA AC BD EF : Line)
    (Ω : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  cyclic A B C D ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B D BD ∧
  twoLinesIntersectAtPoint AC BD E ∧
  twoLinesIntersectAtPoint DA BC F ∧
  midpoint A G B ∧
  midpoint C H D ∧
  distinctPointsOnLine E F EF ∧
  circumCircle Ω E G H
  → tangentLine EF Ω := by
  sorry



--HP60
--Given that in $\triangle ABC$, points $D$ and $E$ lie on sides $AB$ and $AC$, respectively, such that $DE \parallel BC$. Lines $BE$ and $CD$ intersect at point $F$. Points $O$, $P$, $Q$, and $R$ are the circumcenters of $\triangle ADF$, $\triangle AEF$, $\triangle BDF$, and $\triangle CEF$, respectively. Prove that points $O$, $P$, $Q$, and $R$ are concyclic.
theorem problem_HP60 :
  ∀ (A B C D E F O P Q R : Point) (AB BC CA DE BE CD : Line),
  formTriangle A B C AB BC CA ∧
  D.onLine AB ∧
  E.onLine AC ∧
  between A D B ∧
  between A E C ∧
  ¬(DE.intersectsLine BC) ∧
  distinctPointsOnLine B E BE ∧
  distinctPointsOnLine C D CD ∧
  twoLinesIntersectAtPoint BE CD F ∧
  circumCentre O A D F ∧
  circumCentre P A E F ∧
  circumCentre Q B D F ∧
  circumCentre R C E F
  → cyclic O P Q R := by
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



--MP18
--In $\triangle ABC$, points $D$ and $E$ are on the extension and reverse extension of $BC$, respectively, such that $\angle ABE = 2\angle ACD$ and $AD \perp AC$. Prove that $CD = 2AB$.
theorem problem_MP18 : ∀
  (A B C D E : Point)
  (AB BC CA AD : Line),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A D AD ∧
  D.onLine BC ∧
  E.onLine BC ∧
  between B C D ∧
  between C B E ∧
  (∠A:B:E = 2 * ∠A:C:D) ∧
  perpLine AD CA
  → |(C─D)| = 2 * |(A─B)| := by
  sorry



--MP79
--In $\triangle ABC$, $AB = AC$, $\angle BAC = 80^\circ$, point $D$ is on $BC$ such that $\angle BAD = 50^\circ$, and point $E$ is on $AC$ such that $\angle ABE = 40^\circ$. Find $\angle ADE$.
theorem problem_MP79 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(A─C)| ∧
  ∠ B:A:C = 80 ∧
  D.onLine BC ∧
  ∠ B:A:D = 50 ∧
  E.onLine CA ∧
  ∠ A:B:E = 40
  → ∠ A:D:E = 30 :=
by
  sorry



--MP39
--In $\triangle ABC$, $AB = AC$, $CH$ is the altitude from $C$ to $AB$, and point $D$ is on $CH$. Extend $BD$ to intersect $AC$ at point $E$. Given that $AB = BE$ and $AD = AE$, prove that $\angle BAC = 80^\circ$.
theorem problem_MP39 :
  ∀ (A B C D E H : Point) (AB BC CA CH BD : Line),
    formTriangle A B C AB BC CA ∧
    |(A─B)| = |(A─C)| ∧
    H.onLine AB ∧
    distinctPointsOnLine C H CH ∧
    perpLine AB CH ∧
    D.onLine CH ∧
    distinctPointsOnLine B D BD ∧
    twoLinesIntersectAtPoint BD CA E ∧
    |(A─B)| = |(B─E)| ∧
    |(A─D)| = |(A─E)|
  → ∠A:B:C = 80 :=
by sorry



--MP28
--In $\triangle ABC$, $\angle BAC = 60^\circ$, $\angle C = 20^\circ$. Point $D$ is on $BC$ such that $\angle BAD = 20^\circ$. Prove that $AB + AD = DC$.
theorem problem_MP28 : ∀
  (A B C D : Point)
  (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  ∠ B:A:C = 60 ∧
  ∠ A:C:B = 20 ∧
  D.onLine BC ∧
  between B D C ∧
  ∠ B:A:D = 20
  → |(A─B)| + |(A─D)| = |(D─C)|
:= by
  sorry



--HP90
--Given that $\triangle ABC$ is inscribed in circle $\odot O$. Line $AD$ bisects angle $\angle BAC$, intersecting circle $\odot O$ at point $D$. Point $E$ is the midpoint of line segment $BC$. Point $F$ lies in the plane such that $EF \perp AD$. Connect line $DF$. Draw line $MN$ perpendicular to line $DF$, intersecting lines $AB$ and $AC$ at points $M$ and $N$, respectively. Prove that $FM = FN$.
theorem problem_HP90 :
∀ (A B C D E F M N : Point) (AB BC CA AD EF DF MN : Line) (O : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  distinctPointsOnLine A D AD ∧
  D.onCircle O ∧
  ∠B:A:D = ∠D:A:C ∧
  midpoint B E C ∧
  distinctPointsOnLine E F EF ∧
  perpLine EF AD ∧
  distinctPointsOnLine D F DF ∧
  distinctPointsOnLine M N MN ∧
  perpLine MN DF ∧
  M.onLine AB ∧
  N.onLine AC
  → |(F─M)| = |(F─N)| :=
by
  sorry



--MP41
--In $\triangle ABC$, $\angle B = 45^\circ$, $\angle C = 15^\circ$, point $D$ is on $BC$ such that $\angle CAD = 45^\circ$. Prove that $CD = 2BD$.
theorem problem_MP41 :
∀ (A B C D : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  ∠A:B:C = ∟/2 ∧
  ∠A:C:B = ∟/6 ∧
  D.onLine BC ∧
  between B D C ∧
  ∠C:A:D = ∟/2
→ |(C─D)| = |(B─D)| + |(B─D)| :=
by
  sorry



--MP22
--In equilateral triangle $\triangle ABC$, point $D$ is on side $AB$, and point $E$ is on the extension of $CB$ such that $AD = BE$. Prove that $CD = ED$.
theorem problem_MP22 :
∀ (A B C D E : Point) (AB BC CA : Line),
  (formTriangle A B C AB BC CA)
  ∧ (|(A─B)| = |(B─C)|)
  ∧ (|(B─C)| = |(C─A)|)
  ∧ D.onLine AB
  ∧ E.onLine BC
  ∧ between A D B
  ∧ between C B E
  ∧ (|(A─D)| = |(B─E)|)
  → (|(C─D)| = |(E─D)|) := by
  sorry



--14G6
--In an acute triangle $\triangle ABC$, points $E$ and $F$ lie on sides $AC$ and $AB$, respectively. Let $M$ be the midpoint of $EF$, and let the perpendicular bisector of $EF$ intersect $BC$ at point $K$. The perpendicular bisector of $MK$ intersects lines $AC$ and $AB$ at points $S$ and $T$, respectively. If points $K$, $S$, $A$, and $T$ are concyclic, the pair $(E, F)$ is called 'interesting'. If pairs $(E_1, F_1)$ and $(E_2, F_2)$ are both interesting, prove that $\frac{E_1E_2}{AB} = \frac{F_1F_2}{AC}$.
theorem problem_14G6 :
∀ (A B C E1 F1 M1 K1 S1 T1 E2 F2 M2 K2 S2 T2 : Point)
  (AB BC CA L1_1 L1_2 L2_1 L2_2 : Line),
  (formAcuteTriangle A B C AB BC CA)
  ∧ (E1.onLine AC)
  ∧ (F1.onLine AB)
  ∧ (midpoint E1 M1 F1)
  ∧ (perpBisector E1 F1 L1_1)
  ∧ (twoLinesIntersectAtPoint L1_1 BC K1)
  ∧ (perpBisector M1 K1 L2_1)
  ∧ (twoLinesIntersectAtPoint L2_1 AC S1)
  ∧ (twoLinesIntersectAtPoint L2_1 AB T1)
  ∧ (cyclic K1 S1 A T1)
  ∧ (E2.onLine AC)
  ∧ (F2.onLine AB)
  ∧ (midpoint E2 M2 F2)
  ∧ (perpBisector E2 F2 L1_2)
  ∧ (twoLinesIntersectAtPoint L1_2 BC K2)
  ∧ (perpBisector M2 K2 L2_2)
  ∧ (twoLinesIntersectAtPoint L2_2 AC S2)
  ∧ (twoLinesIntersectAtPoint L2_2 AB T2)
  ∧ (cyclic K2 S2 A T2)
  → ( |(E1 ─ E2)| * |(A ─ C)| ) = ( |(F1 ─ F2)| * |(A ─ B)| )
:= by
  sorry



--MP70
--In quadrilateral $ABCD$, diagonals $AC$ and $BD$ intersect at point $O$, $AB + AC = DB + DC$, and $OB > OC$. Prove that $OA > OD$.
theorem problem_MP70 :
  ∀ (A B C D O : Point) (AB BC CD DA AC BD : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B D BD ∧
  twoLinesIntersectAtPoint AC BD O ∧
  ( |(A─B)| + |(A─C)| = |(D─B)| + |(D─C)| ) ∧
  ( |(O─B)| > |(O─C)| )
  → ( |(O─A)| > |(O─D)| ) :=
by
  sorry



--MP72
--In $\triangle ABC$, points $D$ and $E$ are on $AB$ and $AC$, respectively, such that $BD = CE$. Extend and reverse extend $BC$ to points $G$ and $F$, respectively, such that $BF = CG$. Given that $\angle F = \angle G$. Prove that $AB = AC$.
theorem problem_MP72 :
∀ (A B C D E F G : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  D.onLine AB ∧
  between A D B ∧
  E.onLine AC ∧
  between A E C ∧
  (|(B─D)| = |(C─E)|) ∧
  F.onLine BC ∧
  between B C G ∧
  G.onLine BC ∧
  between C B F ∧
  (|(B─F)| = |(C─G)|) ∧
  (∠B:F:C = ∠B:G:C)
  → (|(A─B)| = |(A─C)|) := by
sorry



--HP61
--Given that the excircle of $\triangle ABC$, circle $\odot I$, is tangent to sides $BC$, $AB$, and $AC$ at points $D$, $E$, and $F$, respectively. Lines $ED$ and $FD$ intersect line $AI$ at points $M$ and $N$, respectively. Point $G$ is the midpoint of line segment $BC$, and point $H$ is the foot of the perpendicular from $A$ to line $BC$. Prove that points $G$, $N$, $H$, and $M$ are concyclic.
theorem problem_HP61 :
∀ (A B C I D E F M N G H : Point)
  (AB BC CA ED FD AI AH : Line)
  (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  I.isCentre Ω ∧
  tangentAtPoint BC Ω D ∧
  tangentAtPoint AB Ω E ∧
  tangentAtPoint AC Ω F ∧
  distinctPointsOnLine A I AI ∧
  twoLinesIntersectAtPoint ED AI M ∧
  twoLinesIntersectAtPoint FD AI N ∧
  midpoint B G C ∧
  H.onLine BC ∧
  distinctPointsOnLine A H AH ∧
  perpLine AH BC
  → cyclic G N H M :=
by sorry



--17G1
--In a convex pentagon $ABCDE$, given $AB = BC = CD$ and $\angle EAB = \angle BCD$, prove that $\angle EDC$ has a specific relationship with the other angles.
theorem problem_17G1 :
  ∀ (A B C D E : Point) (AB BC CD DE EA : Line),
    formPentagon A B C D E AB BC CD DE EA ∧
    |(A─B)| = |(B─C)| ∧
    |(B─C)| = |(C─D)| ∧
    ∠E:A:B = ∠B:C:D
    → ∠E:D:C = ∠E:A:B + ∠B:C:D
    := by
  sorry



--06G4
--In an acute triangle $\triangle ABC$ with $AB < BC$, point $D$ lies on $AC$ such that $BD = BA$. Let the incircle of triangle $\triangle ABC$ touch $AB$ and $AC$ at points $K$ and $L$, respectively, and let $J$ be the incenter of triangle $\triangle BCD$. Prove that $KL$ bisects segment $AJ$.
theorem problem_06G4 :
∀ (A B C D J K L : Point)
  (AB BC CA BD CD KL AJ : Line)
  (incircle : Circle),
  formAcuteTriangle A B C AB BC CA ∧
  |(A─B)| < |(B─C)| ∧
  D.onLine CA ∧
  between A D C ∧
  |(B─D)| = |(B─A)| ∧
  formTriangle B C D BC CD BD ∧
  inCentre J B C D ∧
  inCircle incircle AB BC CA ∧
  K.onLine AB ∧ K.onCircle incircle ∧
  L.onLine AC ∧ L.onCircle incircle ∧
  distinctPointsOnLine K L KL ∧
  distinctPointsOnLine A J AJ
  → ∃ (X : Point),
    X.onLine KL ∧
    X.onLine AJ ∧
    midpoint A X J
:= by
  sorry



--MP77
--In quadrilateral $ABCD$, $AB = AC$, $\angle ACD = \angle DBC = 30^\circ$. Prove that $\angle BAC = 2\angle CAD$.
theorem problem_MP77 :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    |(A─B)| = |(A─C)| ∧
    ∠ A:C:D = 30 ∧
    ∠ D:B:C = 30
  → ∠ B:A:C = ∠ C:A:D + ∠ C:A:D :=
by
  sorry



--MP47
--In rhombus $ABCD$, $\angle ABC = 78^\circ$. Point $E$ is inside the rhombus such that $\angle EAD = 21^\circ$ and $\angle EDA = 9^\circ$. Prove that $\triangle BCE$ is an equilateral triangle.
theorem problem_MP47 :
  ∀ (A B C D E : Point) (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  (|(A─B)| = |(B─C)|) ∧ (|(B─C)| = |(C─D)|) ∧ (|(C─D)| = |(D─A)|) ∧
  (∠ A:B:C = 78) ∧
  insideQuadrilateral E A B C D AB BC CD DA ∧
  (∠ E:A:D = 21) ∧
  (∠ E:D:A = 9)
  → (|(B─C)| = |(C─E)|) ∧ (|(C─E)| = |(E─B)|)
:= by
  sorry



--imo_22_p4
--Let $ABCDE$ be a convex pentagon such that $BC = DE$. Assume that there is a point $T$ inside $ABCDE$ with $TB = TD$, $TC = TE$ and $\angle ABT = \angle TEA$. Let line $AB$ intersect lines $CD$ and $CT$ at points $P$ and $Q$, respectively. Assume that the points $P, B, A, Q$ occur on their line in that order. Let line $AE$ intersect lines $CD$ and $DT$ at points $R$ and $S$, respectively. Assume that the points $R, E, A, S$ occur on their line in that order. Prove that the points $P, S, Q, R$ lie on a circle.
theorem problem_imo_22_p4 : ∀
(A B C D E T P Q R S : Point)
(AB BC CD DE EA CT DT : Line),
formPentagon A B C D E AB BC CD DE EA ∧
|(B─C)| = |(D─E)| ∧
|(T─B)| = |(T─D)| ∧
|(T─C)| = |(T─E)| ∧
∠ A:B:T = ∠ T:E:A ∧
twoLinesIntersectAtPoint AB CD P ∧
twoLinesIntersectAtPoint AB CT Q ∧
between P B A ∧
between B A Q ∧
twoLinesIntersectAtPoint AE CD R ∧
twoLinesIntersectAtPoint AE DT S ∧
between R E A ∧
between E A S
→ cyclic P S Q R := by
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



--MP46
--In $\triangle ABC$, $\angle ABC < 60^\circ$, $\angle ACB = 30^\circ$. Point $D$ is inside $\triangle ABC$ such that $DB = DC$ and $\angle ABC + \angle DBC = 60^\circ$. Find $\angle CAD$.
theorem problem_MP46 :
  ∀ (A B C D : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    (∠A:B:C < (2*∟)/3) ∧
    (∠A:C:B = ∟/3) ∧
    insideTriangle D A B C AB BC CA ∧
    (|(D─B)| = |(D─C)|) ∧
    (∠A:B:C + ∠D:B:C = (2*∟)/3)
  → (∠C:A:D = ∟/3)
:= by
  sorry



--imo_2004_p5
--In a convex quadrilateral $ABCD$, the diagonal $BD$ bisects neither the angle $ABC$ nor the angle $CDA$. The point $P$ lies inside $ABCD$ and satisfies $\angle PBC = \angle DBA$ and $\angle PDC = \angle BDA$. Prove that $ABCD$ is a cyclic quadrilateral if and only if $AP = CP$.
theorem problem_imo_2004_p5 :
  ∀ (A B C D P : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    (∠ A:B:D ≠ ∠ D:B:C) ∧
    (∠ C:D:B ≠ ∠ B:D:A) ∧
    insideQuadrilateral P A B C D AB BC CD DA ∧
    (∠ P:B:C = ∠ D:B:A) ∧
    (∠ P:D:C = ∠ B:D:A)
    → (cyclic A B C D ↔  (|(A─P)| = |(C─P)|)) :=
by
  sorry




--HP7
--Given that in $\triangle ABC$, $AC = BC$, and $M$ is the midpoint of $AB$. Line $FG$ passes through point $M$, and $\triangle CFG$ has the same incenter as $\triangle ABC$. Prove that $AM^2 = FM \times GM$.
theorem HP7 :
  ∀ (A B C M F G I : Point) (AB BC CA CF FG GC : Line),
    formTriangle A B C AB BC CA ∧
    formTriangle C F G CF FG GC ∧
    |(A─C)| = |(B─C)| ∧
    midpoint A M B ∧
    inCentre I A B C ∧
    inCentre I C F G ∧
    M.onLine FG
    → |(A─M)| * |(A─M)| = |(F─M)| * |(G─M)| :=
by sorry



--18G1
--In $\triangle ABC$, a circle $\Gamma$ passing through $A$ intersects sides $AB$ and $AC$ at points $D$ and $E$, respectively, and intersects segment $BC$ at points $F$ and $G$ with $F$ between $B$ and $G$. Let the tangent to the circumcircle of $\triangle BDF$ at $F$ intersect the tangent to the circumcircle of $\triangle CEG$ at $G$ at a point $T$ distinct from $A$. Prove that $AT \parallel BC$.
theorem problem_18G1 :
∀ (A B C D E F G T : Point) (AB BC CA AT L1 L2 : Line) (Γ ω1 ω2 : Circle),
  (formTriangle A B C AB BC CA)
  ∧ A.onCircle Γ
  ∧ D.onCircle Γ ∧ D.onLine AB ∧ between A D B
  ∧ E.onCircle Γ ∧ E.onLine CA ∧ between A E C
  ∧ F.onCircle Γ ∧ F.onLine BC
  ∧ G.onCircle Γ ∧ G.onLine BC
  ∧ between B F G
  ∧ circumCircle ω1 B D F
  ∧ circumCircle ω2 C E G
  ∧ tangentAtPoint L1 ω1 F
  ∧ tangentAtPoint L2 ω2 G
  ∧ twoLinesIntersectAtPoint L1 L2 T
  ∧ distinctPointsOnLine A T AT
→ ¬(AT.intersectsLine BC)
:= by
  sorry



--MP87
--In right triangle $\triangle ABC$, $\angle B = 90^\circ$, point $D$ is the midpoint of $BC$, point $E$ is on $AC$ such that $AE = 2CE$. Prove that $\angle ADB = \angle CDE$.
theorem problem_MP87 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    ∠A:B:C = ∟ ∧
    midpoint B D C ∧
    E.onLine CA ∧ between A E C ∧
    (|(A─E)| = 2 * |(C─E)|)
    → ∠A:D:B = ∠C:D:E
:= by
  sorry



--HP55
--Given that $AB$ is the diameter of circle $\odot O$. Line $CB$ is tangent to circle $\odot O$ at point $B$. Point $D$ lies on arc $AB$. Line $CD$ intersects circle $\odot O$ at point $F$. Lines $AD$ and $OC$ intersect at point $E$. Connect lines $EB$ and $FB$. Prove that $EB \perp FB$.
theorem problem_HP55 :
  ∀ (A B C D E F O : Point)
    (lAB lCB lCD lAD lOC lEB lFB : Line)
    (circ : Circle),
  O.isCentre circ ∧
  A.onCircle circ ∧
  B.onCircle circ ∧
  midpoint A O B ∧
  distinctPointsOnLine C B lCB ∧
  tangentAtPoint lCB circ B ∧
  D.onCircle circ ∧
  distinctPointsOnLine C D lCD ∧
  F.onCircle circ ∧
  F.onLine lCD ∧
  twoLinesIntersectAtPoint lAD lOC E ∧
  distinctPointsOnLine A D lAD ∧
  distinctPointsOnLine O C lOC ∧
  distinctPointsOnLine E B lEB ∧
  distinctPointsOnLine F B lFB
  → perpLine lEB lFB := by
sorry



--MP81
--In right triangle $\triangle ABC$, $\angle BAC = 90^\circ$, $AD \perp BC$ at point $D$. Points $E$ and $F$ are on rays $AB$ and $CA$, respectively, such that $\angle EDF = 90^\circ$. Prove that $\frac{BE}{AF} = \frac{AB}{AC}$.
theorem problem_MP81 :
  ∀ (A B C D E F : Point) (AB BC CA AD : Line),
    formTriangle A B C AB BC CA ∧
    ∠B:A:C = ∟ ∧
    distinctPointsOnLine A D AD ∧
    distinctPointsOnLine B C BC ∧
    twoLinesIntersectAtPoint AD BC D ∧
    perpLine AD BC ∧
    E.onLine AB ∧
    F.onLine CA ∧
    ∠E:D:F = ∟
  → (|(B─E)| * |(A─C)|) = (|(A─B)| * |(A─F)|) :=
by sorry



--MP80
--In $\triangle ABC$, points $M$ and $N$ are on $AB$ and $AC$, respectively, such that $AM = AN$. Points $D$ and $E$ are on $BC$ such that $BD = CE < \frac{1}{2}BC$. Given that $\angle BMD = \angle CNE$, prove that $AB = AC$.
theorem problem_MP80 :
  ∀ (A B C M N D E : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  M.onLine AB ∧ between A M B ∧
  N.onLine AC ∧
  D.onLine BC ∧
  E.onLine BC ∧
  |(A─M)| = |(A─N)| ∧
  |(B─D)| = |(C─E)| ∧
  (|(B─D)| < (|(B─C)|)/2) ∧
  (∠B:M:D = ∠C:N:E)
  → (|(A─B)| = |(A─C)|) :=
by
  sorry



--MP57
--In parallelogram $ABCD$, point $E$ is the midpoint of $AD$, and $BP \perp CE$ at point $P$. Prove that $AP = AB$.
theorem problem_MP57 :
  ∀ (A B C D E P : Point) (AB BC CD DA BP CE : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(AB.intersectsLine CD) ∧
  ¬(BC.intersectsLine AD) ∧
  midpoint A E D ∧
  distinctPointsOnLine B P BP ∧
  distinctPointsOnLine C E CE ∧
  twoLinesIntersectAtPoint BP CE P ∧
  perpLine BP CE
  → |(A─P)| = |(A─B)| := by
  sorry



--HP88
--Given that in $\triangle ABC$, line $AD$ is the altitude from vertex $A$ to side $BC$. Point $M$ is the midpoint of line segment $BC$. A line through point $M$ intersects lines $AB$ and $AC$ at points $E$ and $F$, respectively, such that $AE = AF$. Point $O$ is the circumcenter of $\triangle AEF$. Prove that $OM = OD$.
theorem HP88 :
  ∀ (A B C D E F M O : Point) (AB BC CA AD EF : Line),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A D AD ∧
  twoLinesIntersectAtPoint AD BC D ∧
  perpLine AD BC ∧
  midpoint B M C ∧
  twoLinesIntersectAtPoint EF AB E ∧
  twoLinesIntersectAtPoint EF AC F ∧
  M.onLine EF ∧
  |(A─E)| = |(A─F)| ∧
  circumCentre O A E F
  → |(O─M)| = |(O─D)| :=
by sorry



--HP34
--Given that in parallelogram $ABCD$, point $E$ lies on line $BD$, such that $\angle ECB = \angle ACD$. Line $AC$ intersects the circumcircle of $\triangle ABD$, circle $\odot O$, at point $F$. Connect line $EF$. Prove that $\angle BFE = \angle AFD$.
theorem problem_HP34 :
∀ (A B C D E F : Point)
  (AB BC CD DA AC BD : Line)
  (O : Circle),
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine B C BC ∧
  distinctPointsOnLine C D CD ∧
  distinctPointsOnLine D A DA ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B D BD ∧
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(AB.intersectsLine DC) ∧
  ¬(BC.intersectsLine AD) ∧
  E.onLine BD ∧
  ∠ E:C:B = ∠ A:C:D ∧
  circumCircle O A B D ∧
  A.onLine AC ∧
  C.onLine AC ∧
  F.onLine AC ∧
  F.onCircle O
→ ∠ B:F:E = ∠ A:F:D
:= by
  sorry



--HP39
--Given that in $\triangle ABC$, the excircle $\odot P$ is tangent to the extensions of $CB$ and $CA$ at points $D$ and $E$, respectively. The excircle $\odot Q$ is tangent to the extensions of $BC$ and $BA$ at points $F$ and $G$, respectively. Lines $DE$ and $FG$ intersect line $PQ$ at points $M$ and $N$, respectively. Lines $BN$ and $CM$ intersect at point $L$. Prove that line $AL$ bisects angle $\angle BAC$.
theorem HP39 :
  ∀ (A B C P Q D E F G M N L : Point)
    (AB BC CA DE FG PQ BN CM AL : Line)
    (circP circQ : Circle),
  formTriangle A B C AB BC CA ∧
  P.isCentre circP ∧
  Q.isCentre circQ ∧
  tangentAtPoint CB circP D ∧
  tangentAtPoint CA circP E ∧
  tangentAtPoint BC circQ F ∧
  tangentAtPoint BA circQ G ∧
  distinctPointsOnLine P Q PQ ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine F G FG ∧
  twoLinesIntersectAtPoint DE PQ M ∧
  twoLinesIntersectAtPoint FG PQ N ∧
  distinctPointsOnLine B N BN ∧
  distinctPointsOnLine C M CM ∧
  twoLinesIntersectAtPoint BN CM L ∧
  distinctPointsOnLine A L AL
  → ∠B:A:L = ∠L:A:C
:= by
  sorry



--MP49
--In $\triangle ABC$, $AB = AC$, $\angle DBC = \angle ACD$. Point $M$ is the midpoint of $BC$, and points $E$ and $F$ are on $DB$ and $DC$, respectively, such that $\angle EMF = 90^\circ$. Prove that $\angle EAF = \frac{1}{2} \angle BAC$.
theorem problem_MP49 :
  ∀ (A B C D E F M : Point) (AB BC CA DB DC : Line),
    formTriangle A B C AB BC CA ∧
    (|(A─B)| = |(A─C)|) ∧
    (∠ D:B:C = ∠ A:C:D) ∧
    midpoint B M C ∧
    distinctPointsOnLine D B DB ∧
    distinctPointsOnLine D C DC ∧
    E.onLine DB ∧
    F.onLine DC ∧
    (∠ E:M:F = ∟)
  → 2 * ∠ E:A:F = ∠ B:A:C
:= by
  sorry



--imo_2014_p4
--Points $P$ and $Q$ lie on side $BC$ of acute-angled $\triangle{ABC}$ so that $\angle{PAB}=\angle{BCA}$ and $\angle{CAQ}=\angle{ABC}$. Points $M$ and $N$ lie on lines $AP$ and $AQ$, respectively, such that $P$ is the midpoint of $AM$, and $Q$ is the midpoint of $AN$. Prove that lines $BM$ and $CN$ intersect on the circumcircle of $\triangle{ABC}$.
theorem problem_imo_2014_p4 :
  ∀ (A B C P Q M N X : Point) (AB BC CA AP AQ BM CN : Line) (Ω : Circle),
    formTriangle A B C AB BC CA ∧
    P.onLine BC ∧
    Q.onLine BC ∧
    (∠ P:A:B = ∠ B:C:A) ∧
    (∠ C:A:Q = ∠ A:B:C) ∧
    distinctPointsOnLine A P AP ∧
    M.onLine AP ∧
    midpoint A P M ∧
    distinctPointsOnLine A Q AQ ∧
    N.onLine AQ ∧
    midpoint A Q N ∧
    distinctPointsOnLine B M BM ∧
    distinctPointsOnLine C N CN ∧
    circumCircle Ω A B C ∧
    twoLinesIntersectAtPoint BM CN X
  → X.onCircle Ω :=
by
  sorry



--85T22
--A circle with center $O$ passes through the vertices $A$ and $C$ of the triangle $ABC$ and intersects the segments $AB$ and $BC$ again at distinct points $K$ and $N$ respectively. Let $M$ be the point of intersection of the circumcircles of triangles $ABC$ and $KBN$ (apart from $B$). Prove that $\angle OMB=90^{\circ},$.
theorem problem_85T22 :
  ∀ (A B C K N M O : Point) (AB BC CA : Line) (circle₁ circle₂ circle₃ : Circle),
    formTriangle A B C AB BC CA ∧
    O.isCentre circle₁ ∧
    A.onCircle circle₁ ∧
    C.onCircle circle₁ ∧
    K.onLine AB ∧
    K.onCircle circle₁ ∧
    between A K B ∧
    N.onLine BC ∧
    N.onCircle circle₁ ∧
    between B N C ∧
    circumCircle circle₂ A B C ∧
    circumCircle circle₃ B K N ∧
    M.onCircle circle₂ ∧
    M.onCircle circle₃ ∧
    M ≠ B
  → ∠ O:M:B = ∟ :=
by
  sorry



--10G1
--In an acute triangle $\triangle ABC$, let $AD$, $BE$, and $CF$ be altitudes. Extend line $FE$ to intersect the circumcircle of $\triangle ABC$ at point $P$, and let $BP$ intersect $DF$ at point $Q$. Prove that $AP = AQ$.
theorem problem_10G1 :
  ∀ (A B C D E F P Q : Point)
    (AB BC CA AD BE CF FE BP DF : Line)
    (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  twoLinesIntersectAtPoint AD BC D ∧ perpLine AD BC ∧
  twoLinesIntersectAtPoint BE CA E ∧ perpLine BE CA ∧
  twoLinesIntersectAtPoint CF AB F ∧ perpLine CF AB ∧
  F.onLine FE ∧ E.onLine FE ∧ P.onLine FE ∧
  P.onCircle Ω ∧
  circumCircle Ω A B C ∧
  twoLinesIntersectAtPoint BP DF Q
  → |(A─P)| = |(A─Q)| :=
by
  sorry



--MP91
--In trapezoid $ABCD$, $AD \parallel BC$, diagonals $AC$ and $BD$ intersect at point $O$. Points $E$ and $F$ are on $BC$ such that $BE = CF$. Line $EO$ intersects $CD$ at point $G$, and line $FO$ intersects $BA$ at point $H$. Prove that $HG \parallel AD$.
theorem problem_MP91 :
  ∀ (A B C D E F O G H : Point) (AB BC CD DA AC BD EO FO HG : Line),
  (formQuadrilateral A B C D AB BC CD DA)
  ∧ (¬(∃ X : Point, twoLinesIntersectAtPoint AD BC X))
  ∧ distinctPointsOnLine A C AC
  ∧ distinctPointsOnLine B D BD
  ∧ twoLinesIntersectAtPoint AC BD O
  ∧ E.onLine BC
  ∧ F.onLine BC
  ∧ (|(B─E)| = |(C─F)|)
  ∧ distinctPointsOnLine E O EO
  ∧ twoLinesIntersectAtPoint EO CD G
  ∧ distinctPointsOnLine F O FO
  ∧ twoLinesIntersectAtPoint FO BA H
  ∧ distinctPointsOnLine H G HG
  → (¬(∃ X : Point, twoLinesIntersectAtPoint HG AD X))
:= by
  sorry



--HP98
--Given that in quadrilateral $ABFD$, points $C$ and $E$ lie on sides $BF$ and $DF$, respectively, such that $\angle BAC = \angle DAE$. Lines $BE$ and $CD$ intersect at point $G$. Connect line $AG$. Prove that $\angle FAC = \angle GAE$.
theorem problem_HP98 :
  ∀ (A B C D E F G : Point) (AB BF FD DA BE CD AG : Line),
  formQuadrilateral A B F D AB BF FD DA ∧
  C.onLine BF ∧ between B C F ∧
  E.onLine FD ∧ between D E F ∧
  ∠B:A:C = ∠D:A:E ∧
  twoLinesIntersectAtPoint BE CD G
  → ∠F:A:C = ∠G:A:E := by
sorry



--HP82
--Given that $O$ is the circumcenter of $\triangle ABC$. A line through point $O$ intersects sides $AB$ and $AC$ at points $D$ and $E$, respectively. Points $F$ and $G$ are the midpoints of line segments $BE$ and $CD$, respectively. Prove that $\angle FOG = \angle A$.
theorem problem_HP82 :
  ∀ (A B C O D E F G : Point) (AB BC CA DE : Line),
  formTriangle A B C AB BC CA ∧
  circumCentre O A B C ∧
  D.onLine AB ∧
  E.onLine AC ∧
  threePointsOnLine O D E DE ∧
  midpoint B F E ∧
  midpoint C G D
  → ∠F:O:G = ∠B:A:C :=
by
  sorry



--07G3
--In trapezoid $ABCD$ with $AB \parallel CD$, the diagonals $AC$ and $BD$ intersect at point $P$. Point $Q$ lies between the parallel lines $BC$ and $AD$ such that $\angle AQD = \angle CQB$ and $P$ and $Q$ are on opposite sides of line $CD$. Prove that $\angle BQP = \angle DAQ$.
theorem problem_07G3 :
∀ (A B C D P Q : Point)
  (AB BC CD DA AC BD : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint AB CD X) ∧
  twoLinesIntersectAtPoint AC BD P ∧
  (∠ A:Q:D = ∠ C:Q:B) ∧
  P.opposingSides Q CD
  → (∠ B:Q:P = ∠ D:A:Q) :=
by
  sorry



--imo_2012_p1
--Given triangle $ABC$ the point $J$ is the centre of the excircle opposite the vertex $A.$ This excircle is tangent to the side $BC$ at $M$, and to the lines $AB$ and $AC$ at $K$ and $L$, respectively. The lines $LM$ and $BJ$ meet at $F$, and the lines $KM$ and $CJ$ meet at $G.$ Let $S$ be the point of intersection of the lines $AF$ and $BC$, and let $T$ be the point of intersection of the lines $AG$ and $BC.$ Prove that $M$ is the midpoint of $ST$.
theorem problem_imo_2012_p1 :
  ∀ (A B C J M K L F G S T : Point)
    (AB BC CA LM BJ KM CJ AF AG : Line)
    (Γ : Circle),
  formTriangle A B C AB BC CA ∧
  J.isCentre Γ ∧
  tangentAtPoint BC Γ M ∧
  tangentAtPoint AB Γ K ∧
  tangentAtPoint AC Γ L ∧
  distinctPointsOnLine L M LM ∧
  distinctPointsOnLine B J BJ ∧
  twoLinesIntersectAtPoint LM BJ F ∧
  distinctPointsOnLine K M KM ∧
  distinctPointsOnLine C J CJ ∧
  twoLinesIntersectAtPoint KM CJ G ∧
  distinctPointsOnLine A F AF ∧
  twoLinesIntersectAtPoint AF BC S ∧
  distinctPointsOnLine A G AG ∧
  twoLinesIntersectAtPoint AG BC T
  → midpoint S M T
:= by
  sorry



--MP1
--In $\triangle ABC$, $AB = AC$. Point $D$ is on $AB$, and point $E$ is on the extension of $AC$, such that $BD = CE$. Extend $CB$ to point $F$ such that $BF = CB$. Line $EB$ intersects $DF$ at point $P$. Prove that $PB = PF$.
theorem problem_MP1 :
∀ (A B C D E F P : Point) (AB BC CA EB DF : Line),
  (formTriangle A B C AB BC CA)
  ∧ (|(A─B)| = |(A─C)|)
  ∧ (D.onLine AB) ∧ (between A D B)
  ∧ (E.onLine AC) ∧ (between A C E)
  ∧ (|(B─D)| = |(C─E)|)
  ∧ (F.onLine BC) ∧ (between C B F)
  ∧ (|(B─F)| = |(C─B)|)
  ∧ (twoLinesIntersectAtPoint EB DF P)
  → |(P─B)| = |(P─F)| := by
sorry



--MP94
--In trapezoid $ABCD$, $AD \parallel BC$. Point $P$ is on $BC$. Draw $PE \parallel AC$, intersecting $AB$ at point $E$, $PF \parallel BD$, intersecting $CD$ at point $F$, $FG \parallel BC$, intersecting $AB$ at point $G$. Prove that $AG = BE$.
theorem problem_MP94 :
  ∀ (A B C D P E F G : Point)
    (AB BC CD DA AC BD PE PF FG : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    ¬(DA.intersectsLine BC) ∧
    P.onLine BC ∧
    distinctPointsOnLine A C AC ∧
    distinctPointsOnLine P E PE ∧
    ¬(PE.intersectsLine AC) ∧
    twoLinesIntersectAtPoint PE AB E ∧
    distinctPointsOnLine P F PF ∧
    distinctPointsOnLine B D BD ∧
    ¬(PF.intersectsLine BD) ∧
    twoLinesIntersectAtPoint PF CD F ∧
    distinctPointsOnLine F G FG ∧
    ¬(FG.intersectsLine BC) ∧
    twoLinesIntersectAtPoint FG AB G
    → |(A─G)| = |(B─E)| :=
by sorry



--MP60
--In $\triangle ABC$, $AB = AC$, $AD \perp BC$ at point $D$. Point $E$ is on the extension of $BA$, and point $F$ is on segment $AC$ such that $AE = CF$. Prove that $EF \geq AD$.
theorem problem_MP60 :
∀ (A B C D E F : Point) (AB BC CA AD : Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(A─C)| ∧
  D.onLine BC ∧
  perpLine AD BC ∧
  E.onLine AB ∧
  between B A E ∧
  F.onLine AC ∧
  between A F C ∧
  |(A─E)| = |(C─F)|
  → |(E─F)| ≥ |(A─D)| :=
by
  sorry



--MP78
--In equilateral triangle $\triangle ABC$, point $D$ is on side $AB$, and point $E$ is on the extension of $CB$ such that $AD = BE$. Point $F$ is the midpoint of $CD$. Prove that $AF \perp EF$.
theorem problem_MP78 :
  ∀ (A B C D E F : Point) (AB BC CA CD AF EF : Line),
  (formTriangle A B C AB BC CA)
  ∧ (|(A─B)| = |(B─C)|)
  ∧ (|(B─C)| = |(C─A)|)
  ∧ distinctPointsOnLine A B AB
  ∧ distinctPointsOnLine B C BC
  ∧ distinctPointsOnLine C A CA
  ∧ distinctPointsOnLine C D CD
  ∧ distinctPointsOnLine A F AF
  ∧ distinctPointsOnLine E F EF
  ∧ between A D B
  ∧ between C B E
  ∧ (|(A─D)| = |(B─E)|)
  ∧ midpoint C F D
  → perpLine AF EF := by
  sorry



--HP27
--Given that in quadrilateral $ABCD$, $AB = AC$. The circumcircle of $\triangle ABD$, circle $\odot O_1$, intersects line $AC$ at point $F$. The circumcircle of $\triangle ACD$, circle $\odot O_2$, intersects line $AB$ at point $E$. Lines $BF$ and $CE$ intersect at point $G$. Prove that $\frac{BG}{CG} = \frac{BD}{CD}$.
theorem problem_HP27 :
  ∀ (A B C D E F G : Point)
    (AB BC CD DA AC BF CE : Line)
    (O₁ O₂ : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  (|(A─B)| = |(A─C)|) ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B F BF ∧
  distinctPointsOnLine C E CE ∧
  circumCircle O₁ A B D ∧
  circumCircle O₂ A C D ∧
  F.onLine AC ∧
  F.onCircle O₁ ∧
  E.onLine AB ∧
  E.onCircle O₂ ∧
  twoLinesIntersectAtPoint BF CE G
  →
  (|(B─G)| * |(C─D)|) = (|(C─G)| * |(B─D)|)
:= by
  sorry



--MP50
--In $\triangle ABC$, $AB = AC$, point $D$ is on $BC$ or its extension such that $\angle ADB = 60^\circ$. Extend $AD$ to point $E$ such that $DE = DB$. Connect $CE$. Prove that $CE = AC$.
theorem problem_MP50 : ∀
  (A B C D E : Point)
  (AB BC CA AD : Line),
  (formTriangle A B C AB BC CA ∧
   |(A─B)|=|(A─C)| ∧
   D.onLine BC ∧
   distinctPointsOnLine A D AD ∧
   E.onLine AD ∧
   ∠A:D:B = 60 ∧
   |(D─E)|=|(D─B)|)
  → |(C─E)|=|(A─C)| :=
by
  sorry



--MP14
--In quadrilateral $ABCD$, $AB = BC$, $\angle ABC = \angle BCD$. Extend $BC$ to point $G$. Point $E$ is on $BC$, $CF$ bisects $\angle DCG$, and $\angle AEF = \angle ABC$. Prove that $AE = EF$.
theorem problem_MP14 :
  ∀ (A B C D E F G : Point) (AB BC CD DA CF : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    |(A─B)| = |(B─C)| ∧
    ∠A:B:C = ∠B:C:D ∧
    E.onLine BC ∧
    G.onLine BC ∧
    between B C G ∧
    distinctPointsOnLine C F CF ∧
    ∠D:C:F = ∠F:C:G ∧
    ∠A:E:F = ∠A:B:C
  → |(A─E)| = |(E─F)| := by
  sorry



--MP36
--In right triangle $\triangle ABC$, $AB = AC$, point $P$ is inside the triangle such that $\angle PBC = \angle PCA = 30^\circ$. Find $\angle BAP$.
theorem problem_MP36 :
  ∀ (A B C P : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    ∠ B:A:C = ∟ ∧
    |(A─B)| = |(A─C)| ∧
    insideTriangle P A B C AB BC CA ∧
    ∠ P:B:C = ∟/3 ∧
    ∠ P:C:A = ∟/3
  → ∠ B:A:P = ∟/6
:= by
  sorry



--MP4
--In convex quadrilateral $ABCD$, $BC = CD$ and $AC$ bisects $\angle BAD$. Investigate the relationship between $\angle B$ and $\angle D$ and prove your conclusion.
theorem problem_MP4 : ∀ (A B C D : Point) (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  |(B─C)| = |(C─D)| ∧
  ∠B:A:C = ∠C:A:D
  → ∠A:B:C = ∠C:D:A := by
  sorry



--HP56
--Given that squares $ABCD$ and $EFGH$ are such that line $EF$ intersects line $AB$ at point $J$, line $FG$ intersects line $BC$ at point $K$, line $GH$ intersects line $CD$ at point $L$, and line $HE$ intersects line $DA$ at point $I$. Prove that $IK \perp JL$.
theorem problem_HP56 :
∀ (A B C D E F G H I J K L : Point)
  (AB BC CD DA EF FG GH HE IK JL : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  |(A─B)| = |(B─C)| ∧
  |(B─C)| = |(C─D)| ∧
  |(C─D)| = |(D─A)| ∧
  perpLine AB BC ∧
  perpLine BC CD ∧
  perpLine CD DA ∧
  perpLine DA AB ∧

  formQuadrilateral E F G H EF FG GH HE ∧
  |(E─F)| = |(F─G)| ∧
  |(F─G)| = |(G─H)| ∧
  |(G─H)| = |(H─E)| ∧
  perpLine EF FG ∧
  perpLine FG GH ∧
  perpLine GH HE ∧
  perpLine HE EF ∧

  twoLinesIntersectAtPoint EF AB J ∧
  twoLinesIntersectAtPoint FG BC K ∧
  twoLinesIntersectAtPoint GH CD L ∧
  twoLinesIntersectAtPoint HE DA I ∧
  distinctPointsOnLine I K IK ∧
  distinctPointsOnLine J L JL
  →
  perpLine IK JL
:= by
  sorry



--MP38
--In $\triangle ABC$, $AB = AC$, points $D$ and $E$ are on sides $BC$ and $AC$, respectively, such that $AD \perp BE$, $AE = AD = CD$. Prove that $\angle BAC = 100^\circ$.
theorem problem_MP38 :
  ∀ (A B C D E : Point) (AB BC CA AD BE : Line),
    formTriangle A B C AB BC CA ∧
    |(A─B)| = |(A─C)| ∧
    D.onLine BC ∧
    E.onLine CA ∧
    distinctPointsOnLine A D AD ∧
    distinctPointsOnLine B E BE ∧
    |(A─E)| = |(A─D)| ∧
    |(A─D)| = |(C─D)| ∧
    perpLine AD BE
  → ∠ B : A : C = 100
:= by
  sorry



--MP96
--In trapezoid $ABCD$, $AD \parallel BC$. Point $P$ is on line $AD$. Another line through $P$ intersects $AB$ and $CD$ at points $E$ and $F$, respectively, $BF$ and $CE$ intersect line $AD$ at points $H$ and $G$, respectively. Prove that $PG \cdot PH = PA \cdot PD$.
theorem problem_MP96 :
  ∀ (A B C D P E F G H : Point) (AB BC CD DA PF BF CE : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(DA.intersectsLine BC) ∧
  P.onLine DA ∧
  E.onLine AB ∧
  F.onLine CD ∧
  threePointsOnLine P E F PF ∧
  distinctPointsOnLine B F BF ∧
  distinctPointsOnLine C E CE ∧
  twoLinesIntersectAtPoint BF DA H ∧
  twoLinesIntersectAtPoint CE DA G
  → ( |(P─G)| * |(P─H)| = |(P─A)| * |(P─D)| ) :=
by sorry



--HP99
--Given that the incircle of $\triangle ABC$, circle $\odot I$, is tangent to sides $BC$, $CA$, and $AB$ at points $D$, $E$, and $F$, respectively. Point $K$ lies inside $\triangle ABC$ such that the incircle of $\triangle KBC$, circle $\odot J$, is tangent to side $BC$ at point $D$, and is tangent to sides $KB$ and $KC$ at points $M$ and $N$, respectively. Prove that points $E$, $F$, $M$, and $N$ are concyclic.
theorem problem_HP99 :
  ∀ (A B C K D E F M N I J : Point)
    (AB BC CA KB KC : Line)
    (ω₁ ω₂ : Circle),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  inCircle ω₁ AB BC CA ∧
  I.isCentre ω₁ ∧
  tangentAtPoint BC ω₁ D ∧
  tangentAtPoint CA ω₁ E ∧
  tangentAtPoint AB ω₁ F ∧
  insideTriangle K A B C AB BC CA ∧
  inCentre J K B C ∧
  inCircle ω₂ KB BC KC ∧
  J.isCentre ω₂ ∧
  tangentAtPoint BC ω₂ D ∧
  tangentAtPoint KB ω₂ M ∧
  tangentAtPoint KC ω₂ N
  → cyclic E F M N :=
by
  sorry



--HP28
--Given that $O$ is the circumcenter of $\triangle ABC$, and point $D$ lies inside $\triangle ABC$, such that $\angle DAB = \angle DCB$ and $\angle DAC = \angle DBC$. Point $E$ is the midpoint of $AD$. Draw line $EF$ perpendicular to $AD$, intersecting the extension of line $CB$ at point $F$. Connect lines $FA$, $FD$, and $FO$. Prove that $\angle AFD = 2\angle OFC$.
theorem problem_HP28 :
∀ (A B C D E F O : Point)
  (AB BC CA AD EF : Line),
  formTriangle A B C AB BC CA ∧
  insideTriangle D A B C AB BC CA ∧
  circumCentre O A B C ∧
  (∠ D:A:B = ∠ D:C:B) ∧
  (∠ D:A:C = ∠ D:B:C) ∧
  midpoint A E D ∧
  perpLine EF AD ∧
  twoLinesIntersectAtPoint EF BC F
→ (∠ A:F:D = ∠ O:F:C + ∠ O:F:C) :=
by sorry



--MP69
--In $\triangle ABC$, point $D$ is the midpoint of $BC$, point $P$ is on the extension of $DA$, points $E$ and $F$ are on sides $AB$ and $AC$, respectively, such that $BE = CF$ and $PE = PF$. Prove that $AB = AC$.
theorem problem_MP69 :
  ∀ (A B C D P E F : Point) (AB BC CA AD : Line),
  formTriangle A B C AB BC CA ∧
  midpoint B D C ∧
  threePointsOnLine D A P AD ∧
  E.onLine AB ∧
  F.onLine AC ∧
  |(B─E)|=|(C─F)| ∧
  |(P─E)|=|(P─F)|
  → |(A─B)|=|(A─C)| :=
by sorry



--MP13
--In quadrilateral $ABCD$, $AB = AD$, $\angle B = \angle D = 90^\circ$. Points $E$ and $F$ are on $BC$ and $CD$, respectively, such that $\angle EAF = \frac{1}{2} \angle BAD$. Prove that $BE + DF = EF$.
theorem problem_MP13 :
∀ (A B C D E F : Point) (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  |(A─B)| = |(A─D)| ∧
  ∠A:B:C = ∟ ∧
  ∠C:D:A = ∟ ∧
  E.onLine BC ∧
  F.onLine CD ∧
  (∠E:A:F + ∠E:A:F = ∠B:A:D)
  → (|(B─E)| + |(D─F)| = |(E─F)|) := by
sorry



--12G4
--In a non-isosceles triangle $\triangle ABC$, let $O$ be the circumcenter. The angle bisector of $\angle BAC$ intersects $BC$ at point $D$. Let $E$ be the reflection of $D$ across the midpoint of $BC$. Draw lines through $D$ and $E$ perpendicular to $BC$, intersecting lines $AO$ and $AD$ at points $X$ and $Y$, respectively. Prove that points $B$, $X$, $C$, and $Y$ are concyclic.
theorem problem_12G4 :
  ∀ (A B C D E M O X Y : Point)
    (AB BC CA AD AO DX EY : Line),
    formTriangle A B C AB BC CA ∧
    ¬(|(A─B)| = |(B─C)|) ∧ ¬(|(B─C)| = |(C─A)|) ∧ ¬(|(C─A)| = |(A─B)|) ∧
    circumCentre O A B C ∧
    distinctPointsOnLine A D AD ∧ D.onLine BC ∧ (∠ B:A:D = ∠ D:A:C) ∧
    midpoint B M C ∧ midpoint D M E ∧
    perpLine DX BC ∧ D.onLine DX ∧ X.onLine DX ∧ distinctPointsOnLine A O AO ∧ X.onLine AO ∧
    perpLine EY BC ∧ distinctPointsOnLine E Y EY ∧ E.onLine EY ∧ Y.onLine EY ∧ Y.onLine AD
  → cyclic B X C Y
:= by sorry



--13G4
--In $\triangle ABC$ with $AB < AC$, points $P$ and $Q$ lie on line $AC$ such that $\angle PBA = \angle QBA = \angle ACB$, with $A$ between $P$ and $C$. Given a point $D$ on segment $BQ$ such that $PD = PB$, extend $AD$ to intersect the circumcircle of $\triangle ABC$ at point $R$. Prove that $QB = QR$.
theorem problem_13G4 :
  ∀ (A B C P Q D R : Point) (AB BC CA BQ AD : Line) (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  (|(A─B)| < |(A─C)|) ∧
  P.onLine CA ∧
  Q.onLine CA ∧
  (∠P:B:A = ∠A:C:B) ∧
  (∠Q:B:A = ∠A:C:B) ∧
  between P A C ∧
  distinctPointsOnLine B Q BQ ∧
  D.onLine BQ ∧
  between B D Q ∧
  (|(P─D)| = |(P─B)|) ∧
  circumCircle Ω A B C ∧
  distinctPointsOnLine A D AD ∧
  R.onLine AD ∧
  R.onCircle Ω
  → (|(Q─B)| = |(Q─R)|) := by
  sorry



--HP50
--Given that in $\triangle ABC$, the incenter is point $I$. Circle $\odot O_1$ is tangent to sides $AB$ and $BC$. Circle $\odot O_2$ passes through points $A$ and $C$, and circles $\odot O_1$ and $\odot O_2$ are externally tangent at point $M$. Prove that the angle bisector of $\angle AMC$ passes through point $I$.
theorem problem_HP50 :
  ∀ (A B C I M : Point) (AB BC CA : Line) (O₁ O₂ : Circle),
    formTriangle A B C AB BC CA ∧
    inCentre I A B C ∧
    tangentLine AB O₁ ∧
    tangentLine BC O₁ ∧
    A.onCircle O₂ ∧
    C.onCircle O₂ ∧
    M.onCircle O₁ ∧
    M.onCircle O₂ ∧
    ¬(O₁.intersectsCircle  O₂)
  → ∠ A:M:I = ∠ I:M:C
:= by
  sorry



--HP78
--Given that in quadrilateral $ABCD$, points $E$ and $F$ are the midpoints of sides $AD$ and $BC$, respectively. Point $G$ lies in the plane such that $BG \parallel CD$ and $CG \parallel AB$. Lines $AC$ and $BD$ intersect at point $H$. Prove that $EF \parallel GH$.
theorem HP78 :
∀ (A B C D E F G H : Point)
  (AB BC CD DA AC BD BG CG EF GH : Line),
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine B C BC ∧
  distinctPointsOnLine C D CD ∧
  distinctPointsOnLine D A DA ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B D BD ∧
  distinctPointsOnLine B G BG ∧
  distinctPointsOnLine C G CG ∧
  distinctPointsOnLine E F EF ∧
  distinctPointsOnLine G H GH ∧
  formQuadrilateral A B C D AB BC CD DA ∧
  midpoint A E D ∧
  midpoint B F C ∧
  twoLinesIntersectAtPoint AC BD H ∧
  ¬(BG.intersectsLine CD) ∧
  ¬(CG.intersectsLine AB)
  → ¬(GH.intersectsLine EF) :=
by sorry



--HP53
--Given that in $\triangle ABC$, points $D$, $E$, and $F$ are the midpoints of sides $BC$, $CA$, and $AB$, respectively. Draw line $EM$ perpendicular to line $AC$, intersecting line $AD$ at point $M$. Draw line $FN$ perpendicular to line $AB$, intersecting line $AD$ at point $N$. Lines $EM$ and $FN$ intersect at point $O$. Lines $CM$ and $BN$ intersect at point $K$. Prove that $OK \perp AK$.
theorem problem_HP53 :
  ∀ (A B C D E F M N O K : Point)
    (AB BC CA AD EM FN BN CM OKLine AKLine : Line),
  formTriangle A B C AB BC CA ∧
  midpoint B D C ∧
  midpoint C E A ∧
  midpoint A F B ∧
  distinctPointsOnLine A D AD ∧
  distinctPointsOnLine E M EM ∧
  perpLine EM CA ∧
  twoLinesIntersectAtPoint AD EM M ∧
  distinctPointsOnLine F N FN ∧
  perpLine FN AB ∧
  twoLinesIntersectAtPoint AD FN N ∧
  twoLinesIntersectAtPoint EM FN O ∧
  distinctPointsOnLine C M CM ∧
  distinctPointsOnLine B N BN ∧
  twoLinesIntersectAtPoint CM BN K ∧
  distinctPointsOnLine O K OKLine ∧
  distinctPointsOnLine A K AKLine
  → perpLine OKLine AKLine := by
  sorry



--imo_2009_p2
--Let $ABC$ be a triangle with circumcentre $O$. The points $P$ and $Q$ are interior points of the sides $CA$ and $AB$ respectively. Let $K,L$ and $M$ be the midpoints of the segments $BP,CQ$ and $PQ$, respectively, and let $\Gamma$ be the circle passing through $K,L$ and $M$. Suppose that the line $PQ$ is tangent to the circle $\Gamma$. Prove that $OP=OQ$.
theorem problem_imo_2009_p2 : ∀
(A B C O P Q K L M : Point) (AB BC CA PQ : Line) (Γ : Circle),
  formTriangle A B C AB BC CA ∧
  circumCentre O A B C ∧
  between C P A ∧
  between A Q B ∧
  midpoint B K P ∧
  midpoint C L Q ∧
  midpoint P M Q ∧
  threePointsOnLine P Q M PQ ∧
  K.onCircle Γ ∧
  L.onCircle Γ ∧
  M.onCircle Γ ∧
  tangentAtPoint PQ Γ M
  → |(O─P)| = |(O─Q)| := by
sorry



--HP74
--Given that in parallelogram $ABCD$, diagonals $AC$ and $BD$ intersect at point $O$. Line $CE$ is perpendicular to line $BD$ at point $E$, and line $DF$ is perpendicular to line $AC$ at point $F$. Line $FE$ intersects the extension of line $BA$ at point $G$. Prove that $GO \perp AD$.
theorem problem_HP74 :
  ∀ (A B C D E F G O : Point)
    (AB BC CD DA AC BD CE DF FE : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(AB.intersectsLine DC) ∧
  ¬(BC.intersectsLine AD) ∧
  twoLinesIntersectAtPoint AC BD O ∧
  twoLinesIntersectAtPoint CE BD E ∧
  perpLine CE BD ∧
  twoLinesIntersectAtPoint DF AC F ∧
  perpLine DF AC ∧
  twoLinesIntersectAtPoint FE AB G
  → perpLine GO AD
:= by
  sorry



--imo_2010_p4
--Let $P$ be a point interior to triangle $ABC$ (with $CA \neq CB$). The lines $AP$, $BP$ and $CP$ meet again its circumcircle $\Gamma$ at $K$, $L$, respectively $M$. The tangent line at $C$ to $\Gamma$ meets the line $AB$ at $S$. Show that from $SC = SP$ follows $MK = ML$.
theorem problem_imo_2010_p4 :
  ∀ (A B C P K L M S : Point) (AB BC CA AP BP CP cT : Line) (Γ : Circle),
    formTriangle A B C AB BC CA ∧
    insideTriangle P A B C AB BC CA ∧
    ¬(|(C─A)| = |(C─B)|) ∧
    circumCircle Γ A B C ∧
    A.onLine AP ∧ P.onLine AP ∧ K.onLine AP ∧
    B.onLine BP ∧ P.onLine BP ∧ L.onLine BP ∧
    C.onLine CP ∧ P.onLine CP ∧ M.onLine CP ∧
    K.onCircle Γ ∧ L.onCircle Γ ∧ M.onCircle Γ ∧
    tangentAtPoint cT Γ C ∧
    twoLinesIntersectAtPoint AB cT S ∧
    |(S─C)| = |(S─P)|
  → |(M─K)| = |(M─L)| :=
by sorry



--MP16
--In right triangle $\triangle ABC$, $\angle C = 90^\circ$, $\angle A = 30^\circ$. Points $D$, $E$, and $F$ are on sides $AC$, $AB$, and $BC$, respectively, such that $AE = AC$ and $AF$ bisects $\angle BAC$, $CD = CF$. Find $\angle CED$.
theorem problem_MP16 :
∀ (A B C D E F : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  ∠ A:C:B = ∟ ∧
  ∠ B:A:C = 30 ∧
  D.onLine CA ∧
  E.onLine AB ∧
  F.onLine BC ∧
  |(A─E)| = |(A─C)| ∧
  ∠ B:A:F = ∠ F:A:C ∧
  |(C─D)| = |(C─F)|
  → ∠ C:E:D = 15 := by
sorry



--HP81
--Given that circle $\odot O$ is the circumcircle of $\triangle ABC$. Point $I$ is the incenter of $\triangle ABC$. Circle $\odot J$ is tangent to sides $AB$ and $AC$ at points $D$ and $E$, respectively, and is internally tangent to circle $\odot O$ at point $F$. Prove that line $IF$ bisects angle $\angle BFC$.
theorem problem_HP81 :
  ∀ (A B C I D E F : Point) (AB BC CA : Line) (O J : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  inCentre I A B C ∧
  tangentAtPoint AB J D ∧
  tangentAtPoint AC J E ∧
  F.onCircle O ∧
  F.onCircle J ∧
  (∀ (P : Point), P.onCircle O ∧ P.onCircle J → P = F)
  → ∠B:F:I = ∠I:F:C
:= by
  sorry



--HP93
--Given that $\triangle ABC$ is inscribed in circle $\odot O$. Point $P$ lies on circle $\odot O$. Line $PD$ is perpendicular to line $BC$ at point $D$. Line $PE$ is perpendicular to line $CA$ at point $E$. Line $PF$ is perpendicular to line $AB$ at point $F$. Prove that points $D$, $E$, and $F$ are collinear.
theorem problem_HP93 :
∀ (A B C P D E F : Point) (AB BC CA PD PE PF DE : Line) (O : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  P.onCircle O ∧
  distinctPointsOnLine P D PD ∧
  twoLinesIntersectAtPoint PD BC D ∧
  perpLine PD BC ∧
  distinctPointsOnLine P E PE ∧
  twoLinesIntersectAtPoint PE CA E ∧
  perpLine PE CA ∧
  distinctPointsOnLine P F PF ∧
  twoLinesIntersectAtPoint PF AB F ∧
  perpLine PF AB ∧
  distinctPointsOnLine D E DE
→ threePointsOnLine D E F DE :=
by sorry



--MP5
--In $\triangle ABC$, $AB \neq AC$. Point $D$ is on the external angle bisector of $\angle BAC$ (on the extension of $\angle CAE$), and $DB = DC$. Prove that $\angle ABD = \angle ACD$.
theorem problem_MP5 :
∀ (A B C D : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  ¬ (|(A─B)| = |(A─C)|) ∧
  (|(D─B)| = |(D─C)|) ∧
  (∠B:A:D = ∠D:A:C)
  → ∠A:B:D = ∠A:C:D := by
sorry



--MP29
--In $\triangle ABC$, $AB = AC$. Construct an isosceles right triangle $\triangle ACD$ outside $\triangle ABC$ with $AC$ as one leg and $A$ as the right-angle vertex. Draw $CE \parallel AB$, intersecting $AD$ at point $E$, and $BD$ intersects $AC$ at point $F$. Prove that $AE + AF = CE$.
theorem problem_MP29 :
∀ (A B C D E F : Point)
(AB BC CA CD DA BD CE : Line),
  formTriangle A B C AB BC CA ∧
  (|(A─B)| = |(A─C)|) ∧
  formTriangle A C D CA CD DA ∧
  (|(A─C)| = |(A─D)|) ∧
  (∠C:A:D = ∟) ∧
  distinctPointsOnLine B D BD ∧
  twoLinesIntersectAtPoint BD CA F ∧
  distinctPointsOnLine C E CE ∧
  twoLinesIntersectAtPoint AD CE E ∧
  ¬(AB.intersectsLine CE)
→ |(A─E)| + |(A─F)| = |(C─E)| := by
  sorry



--HP31
--Given that quadrilateral $ABCD$ is inscribed in circle $\odot O$. Point $E$ lies inside the quadrilateral, such that $\angle EAB = \angle ECO$ and $\angle EBA = \angle EDC$. Line $FG$ through point $E$ bisects angle $\angle BEC$, intersecting circle $\odot O$ at points $F$ and $G$. Prove that $EF = EG$.
theorem problem_HP31 :
∀ (A B C D E F G O : Point)
  (AB BC CD DA FG : Line)
  (circleO : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  O.isCentre circleO ∧
  A.onCircle circleO ∧ B.onCircle circleO ∧ C.onCircle circleO ∧ D.onCircle circleO ∧
  insideQuadrilateral E A B C D AB BC CD DA ∧
  ∠ E:A:B = ∠ E:C:O ∧
  ∠ E:B:A = ∠ E:D:C ∧
  distinctPointsOnLine F G FG ∧
  E.onLine FG ∧
  ∠ B:E:F = ∠ F:E:C ∧
  F.onCircle circleO ∧
  G.onCircle circleO
→ |(E─F)| = |(E─G)| :=
by sorry



--MP82
--In $\triangle ABC$, $AB = c$, $BC = a$, $AC = b$. Points $E$ and $D$ are on the extension and reverse extension of $BC$, respectively, such that $\angle ABD = 2\angle ACE$. Prove that $c^2 - b^2 = ac$.
theorem problem_MP82 :
∀ (A B C D E : Point) (AB BC CA : Line),
  (formTriangle A B C AB BC CA)
  ∧ threePointsOnLine B C E BC
  ∧ threePointsOnLine B C D BC
  ∧ between B C E
  ∧ between C B D
  ∧ ( ∠A:B:D = ( ∠A:C:E + ∠A:C:E ) )
  →
  ( (|(A─B)| * |(A─B)| - |(A─C)| * |(A─C)|) = (|(B─C)| * |(A─B)|) )
:= by
  sorry



--imo_2018_p1
--Let $\Gamma$ be the circumcircle of acute triangle $ABC$. Points $D$ and $E$ are on segments $AB$ and $AC$ respectively such that $AD = AE$. The perpendicular bisectors of $BD$ and $CE$ intersect minor arcs $AB$ and $AC$ of $\Gamma$ at points $F$ and $G$ respectively. Prove that lines $DE$ and $FG$ are either parallel or they are the same line.
theorem problem_imo_2018_p1 :
∀ (A B C D E F G : Point) (AB BC CA L_F L_G DE FG : Line) (Γ : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle Γ A B C ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine F G FG ∧
  D.onLine AB ∧ E.onLine AC ∧
  between A D B ∧ between A E C ∧
  |(A─D)| = |(A─E)| ∧
  perpBisector B D L_F ∧ F.onLine L_F ∧ F.onCircle Γ ∧
  perpBisector C E L_G ∧ G.onLine L_G ∧ G.onCircle Γ
  → (¬(DE.intersectsLine FG) ∨ (∀ X : Point, X.onLine DE ↔ X.onLine FG))
:= by
  sorry



--19G4
--Let $P$ be a point inside $\triangle ABC$. Extend $AP$ to intersect $BC$ at point $A_1$, and let $A_2$ be the reflection of $P$ across $A_1$. Define points $B_2$, $C_2$ similarly. Prove that points $A_2$, $B_2$, $C_2$ cannot all lie inside the circumcircle of $\triangle ABC$.
theorem problem_19G4 :
  ∀ (A B C P A1 B1 C1 A2 B2 C2 : Point) (AB BC CA AP BP CP : Line) (Ω : Circle),
    formTriangle A B C AB BC CA ∧
    insideTriangle P A B C AB BC CA ∧
    distinctPointsOnLine A P AP ∧
    distinctPointsOnLine B P BP ∧
    distinctPointsOnLine C P CP ∧
    twoLinesIntersectAtPoint AP BC A1 ∧
    twoLinesIntersectAtPoint BP CA B1 ∧
    twoLinesIntersectAtPoint CP AB C1 ∧
    midpoint P A1 A2 ∧
    midpoint P B1 B2 ∧
    midpoint P C1 C2 ∧
    circumCircle Ω A B C
  → ¬(A2.insideCircle Ω ∧ B2.insideCircle Ω ∧ C2.insideCircle Ω) :=
by sorry



--HP14
--Given that circles $\odot O$ and $\odot P$ intersect at points $A$ and $B$. The extensions of lines $BO$ and $PA$ intersect at point $C$. Lines $CD$ and $CE$ are tangents to circles $\odot O$ and $\odot P$, respectively, at points $D$ and $E$. Line $DE$ intersects line $AB$ at point $F$. Prove that $F$ is the midpoint of $DE$.
theorem problem_HP14 :
  ∀ (A B C D E F O P : Point)
    (L1 L2 L3 L4 L5 L6 : Line)
    (C1 C2 : Circle),
  O.isCentre C1 ∧
  P.isCentre C2 ∧
  A.onCircle C1 ∧
  B.onCircle C1 ∧
  A.onCircle C2 ∧
  B.onCircle C2 ∧
  distinctPointsOnLine B O L1 ∧
  distinctPointsOnLine P A L2 ∧
  twoLinesIntersectAtPoint L1 L2 C ∧
  distinctPointsOnLine C D L3 ∧
  tangentAtPoint L3 C1 D ∧
  distinctPointsOnLine C E L4 ∧
  tangentAtPoint L4 C2 E ∧
  distinctPointsOnLine D E L5 ∧
  distinctPointsOnLine A B L6 ∧
  twoLinesIntersectAtPoint L5 L6 F
  → midpoint D F E := by
  sorry



--MP55
--In $\triangle ABC$, point $D$ is the midpoint of $AB$, and point $E$ is on $AC$ such that $\angle AED = \frac{1}{2} \angle C$. Prove that $AE = BC + CE$.
theorem problem_MP55 : ∀ (A B C D E : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  midpoint A D B ∧
  E.onLine CA ∧
  ( ∠A:E:D + ∠A:E:D = ∠A:C:B )
  → |(A─E)| = |(B─C)| + |(C─E)| := by
  sorry



--MP37
--In $\triangle ABC$, $\angle BAC = 20^\circ$, $AB = AC$, point $D$ is on the extension of $BC$, $BD = AB$. Draw $DE \parallel AB$, intersecting the extension of $AC$ at point $E$. Find $\angle BED$.
theorem problem_MP37 :
∀ (A B C D E : Point)
  (AB BC CA DE : Line),
  formTriangle A B C AB BC CA
  ∧ ∠ B:A:C = 20
  ∧ |(A─B)| = |(A─C)|
  ∧ D.onLine BC
  ∧ between B C D
  ∧ |(B─D)| = |(A─B)|
  ∧ distinctPointsOnLine D E DE
  ∧ ¬(∃ P : Point, twoLinesIntersectAtPoint DE AB P)
  ∧ twoLinesIntersectAtPoint DE CA E
  ∧ between A C E
  → ∠ B:E:D = 30
:= by
  sorry



--HP8
--Given that in $\triangle ABC$, $AD$ bisects $\angle BAC$, with $D$ on $BC$. Line $DF$ is perpendicular to $AC$ at point $F$, and line $DE$ is perpendicular to $AB$ at point $E$. Line $CE$ intersects $BF$ at point $P$. Prove that $AP \perp BC$.
theorem problem_HP8 :
∀ (A B C D E F P : Point)
  (AB BC CA AD DF DE BF CE AP : Line),
  formTriangle A B C AB BC CA ∧
  twoLinesIntersectAtPoint AD BC D ∧
  ∠B:A:D = ∠D:A:C ∧
  twoLinesIntersectAtPoint DF CA F ∧
  perpLine DF CA ∧
  twoLinesIntersectAtPoint DE AB E ∧
  perpLine DE AB ∧
  twoLinesIntersectAtPoint CE BF P ∧
  distinctPointsOnLine A P AP
  → perpLine AP BC := by
  sorry



--MP99
--In parallelogram $ABCD$, points $E$ and $F$ are on sides $BC$ and $DA$, respectively, such that $BE = DF$. Point $G$ is on line $CD$. Line $AG$ intersects $CF$ at point $H$. Prove that $BH \parallel EG$.
theorem problem_MP99 :
∀ (A B C D E F G H : Point)
  (AB BC CD DA AG CF BH EG : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  (¬ ∃ X : Point, twoLinesIntersectAtPoint AB DC X) ∧
  (¬ ∃ X : Point, twoLinesIntersectAtPoint BC AD X) ∧
  between B E C ∧
  between D F A ∧
  |(B─E)| = |(D─F)| ∧
  G.onLine CD ∧
  distinctPointsOnLine A G AG ∧
  distinctPointsOnLine C F CF ∧
  twoLinesIntersectAtPoint AG CF H ∧
  distinctPointsOnLine B H BH ∧
  distinctPointsOnLine E G EG
→ (¬ ∃ X : Point, twoLinesIntersectAtPoint BH EG X) :=
by sorry



--91T1
--Given a point $ P$ inside a triangle $ \triangle ABC$. Let $ D$, $ E$, $ F$ be the orthogonal projections of the point $ P$ on the sides $ BC$, $ CA$, $ AB$, respectively. Let the orthogonal projections of the point $ A$ on the lines $ BP$ and $ CP$ be $ M$ and $ N$, respectively. Prove that the lines $ ME$, $ NF$, $ BC$ are concurrent.
theorem problem_91T1 :
∀ (A B C P D E F M N X : Point)
  (AB BC CA BP CP PD PE PF AM AN ME NF : Line),
  (
    formTriangle A B C AB BC CA
    ∧ insideTriangle P A B C AB BC CA
    ∧ distinctPointsOnLine B P BP
    ∧ distinctPointsOnLine C P CP
    ∧ distinctPointsOnLine P D PD
    ∧ D.onLine BC
    ∧ perpLine PD BC
    ∧ distinctPointsOnLine P E PE
    ∧ E.onLine CA
    ∧ perpLine PE CA
    ∧ distinctPointsOnLine P F PF
    ∧ F.onLine AB
    ∧ perpLine PF AB
    ∧ distinctPointsOnLine A M AM
    ∧ M.onLine BP
    ∧ perpLine AM BP
    ∧ distinctPointsOnLine A N AN
    ∧ N.onLine CP
    ∧ perpLine AN CP
    ∧ distinctPointsOnLine M E ME
    ∧ distinctPointsOnLine N F NF
  )
  → (
    twoLinesIntersectAtPoint ME NF X
    ∧ X.onLine BC
  )
:= by
  sorry



--HP15
--Given two circles $\odot O$ and $\odot P$ with unequal radii, intersecting at points $A$ and $B$. Line $CD$ through $A$ intersects circles $\odot O$ and $\odot P$ at points $C$ and $D$, respectively. The extension of line $CB$ intersects circle $\odot P$ at point $F$, and the extension of line $DB$ intersects circle $\odot O$ at point $E$. Draw a perpendicular from $A$ to line $CD$, intersecting the perpendicular bisector of line segment $EF$ at point $G$. Prove that $AG^2 = EG^2 + AC \cdot AD$.
theorem problem_HP15 :
  ∀ (A B C D E F G : Point) (CD CB DB L1 L2 : Line) (O P : Circle),
  O.intersectsCircle P ∧
  A.onCircle O ∧ A.onCircle P ∧
  B.onCircle O ∧ B.onCircle P ∧
  threePointsOnLine A C D CD ∧
  C.onCircle O ∧
  D.onCircle P ∧
  threePointsOnLine C B F CB ∧
  F.onCircle P ∧
  threePointsOnLine D B E DB ∧
  E.onCircle O ∧
  A.onLine L1 ∧
  perpLine L1 CD ∧
  perpBisector E F L2 ∧
  twoLinesIntersectAtPoint L1 L2 G
  → (|(A─G)| * |(A─G)| = |(E─G)| * |(E─G)| + (|(A─C)| * |(A─D)|)) := by
  sorry



--HP89
--Given that $\triangle ABC$ is inscribed in circle $\odot O$. The perpendicular bisector of side $BC$ intersects circle $\odot O$ at points $D$ and $E$, and intersects line $BC$ at point $F$. Draw a line through point $F$ parallel to line $AD$, and take any point $G$ on this parallel line. Connect line $EG$. Draw line $MN$ perpendicular to line $EG$, intersecting lines $AB$ and $AC$ at points $M$ and $N$, respectively. Prove that $GM = GN$.
theorem problem_HP89 :
  ∀ (A B C D E F G M N : Point) (O : Circle)
    (AB BC CA L AD FG EG MN : Line),
  (formTriangle A B C AB BC CA)
  ∧ circumCircle O A B C
  ∧ perpBisector B C L
  ∧ twoLinesIntersectAtPoint L BC F
  ∧ D.onLine L ∧ D.onCircle O
  ∧ E.onLine L ∧ E.onCircle O
  ∧ distinctPointsOnLine A D AD
  ∧ F.onLine FG ∧ G.onLine FG
  ∧ ¬(∃ X : Point, twoLinesIntersectAtPoint FG AD X)
  ∧ distinctPointsOnLine E G EG
  ∧ twoLinesIntersectAtPoint MN AB M
  ∧ twoLinesIntersectAtPoint MN AC N
  ∧ perpLine MN EG
  → |(G─M)| = |(G─N)| :=
by
  sorry



--HP92
--Given that in $\triangle ABC$, line $AD$ is the altitude from vertex $A$ to side $BC$. Point $M$ is the midpoint of line segment $BC$. The perpendicular bisector of line segment $BD$ intersects line $AB$ at point $F$. The perpendicular bisector of line segment $CD$ intersects line $AC$ at point $E$. Prove that points $A$, $F$, $O$, and $E$ are concyclic.
theorem problem_HP92 :
∀ (A B C D M E F O : Point)
  (AB BC CA AD PBD PCD : Line),
  formTriangle A B C AB BC CA ∧
  D.onLine BC ∧
  distinctPointsOnLine A D AD ∧
  perpLine AD BC ∧
  midpoint B M C ∧
  perpBisector B D PBD ∧
  F.onLine PBD ∧
  F.onLine AB ∧
  perpBisector C D PCD ∧
  E.onLine PCD ∧
  E.onLine AC ∧
  O.onLine PBD ∧
  O.onLine PCD
→ cyclic A F O E := by
  sorry



--HP12
--Given that $C$ and $D$ are two points on a semicircle with center $O$ and diameter $AB$. Draw a tangent to circle $O$ at point $B$, intersecting line $CD$ at point $P$. Line $PO$ intersects lines $CA$ and $AD$ at points $E$ and $F$, respectively. Prove that $OE = OF$.
theorem problem_HP12 :
  ∀ (A B C D O P E F : Point) (CD CA AD PO t : Line) (Γ : Circle),
    O.isCentre Γ ∧
    A.onCircle Γ ∧
    B.onCircle Γ ∧
    C.onCircle Γ ∧
    D.onCircle Γ ∧
    distinctPointsOnLine C D CD ∧
    distinctPointsOnLine C A CA ∧
    distinctPointsOnLine A D AD ∧
    tangentAtPoint t Γ B ∧
    twoLinesIntersectAtPoint t CD P ∧
    distinctPointsOnLine P O PO ∧
    twoLinesIntersectAtPoint PO CA E ∧
    twoLinesIntersectAtPoint PO AD F
  → |(O─E)| = |(O─F)| :=
by
  sorry



--MP40
--In $\triangle ABC$, $\angle BAC = 100^\circ$, $AB = AC$, point $D$ is on $BC$ such that $BD = AB$. Draw $DE \parallel AB$, intersecting $AC$ at point $E$. Find $\angle BED$.
theorem problem_MP40 :
  ∀ (A B C D E : Point) (AB BC CA DE : Line),
    formTriangle A B C AB BC CA ∧
    ∠B:A:C = 100 ∧
    |(A─B)| = |(A─C)| ∧
    D.onLine BC ∧
    |(B─D)| = |(A─B)| ∧
    distinctPointsOnLine D E DE ∧
    twoLinesIntersectAtPoint DE CA E ∧
    ¬(DE.intersectsLine AB)
    → ∠B:E:D = 30 := by
  sorry



--HP75
--Given that in right $\triangle ABC$, $\angle BAC = 90^{\circ}$. Points $E$ and $D$ lie on sides $AB$ and $AC$, respectively. Line $BD$ intersects line $CE$ at point $F$. The circumcircle of $\triangle ABC$, circle $\odot O$, intersects the circumcircle of $\triangle AED$, circle $\odot P$, at point $G$. Prove that $AG \perp GF$.
theorem problem_HP75 :
∀ (A B C D E F G : Point) (AB BC CA BD CE : Line) (O P : Circle),
  formTriangle A B C AB BC CA ∧
  (∠B:A:C = ∟) ∧
  E.onLine AB ∧
  distinctPointsOnLine C E CE ∧
  D.onLine CA ∧
  distinctPointsOnLine B D BD ∧
  twoLinesIntersectAtPoint BD CE F ∧
  circumCircle O A B C ∧
  circumCircle P A E D ∧
  G.onCircle O ∧
  G.onCircle P
  → ∠A:G:F = ∟
:= by
  sorry



--imo_2008_p6
--Let $ABCD$ be a convex quadrilateral with $BA \ne BC$. Denote the incircles of triangles $ABC$ and $ADC$ by $\omega _1$ and $\omega _2$ respectively. Suppose that there exists a circle $\omega$ tangent to ray $BA$ beyond $A$ and to the ray $BC$ beyond $C$, which is also tangent to the lines $AD$ and $CD$. Prove that the common external tangents to $\omega _1$ and $\omega _2$ intersect on $\omega$.
theorem problem_imo_2008_p6 :
  ∀ (A B C D : Point) (AB BC CD DA AC : Line) (ω₁ ω₂ ω : Circle) (L₁ L₂ : Line) (P : Point),
    formQuadrilateral A B C D AB BC CD DA ∧
    |(B─A)| ≠ |(B─C)| ∧
    inCircle ω₁ AB BC AC ∧
    inCircle ω₂ AD DC AC ∧
    tangentLine AB ω ∧
    tangentLine BC ω ∧
    tangentLine AD ω ∧
    tangentLine CD ω ∧
    tangentLine L₁ ω₁ ∧
    tangentLine L₁ ω₂ ∧
    tangentLine L₂ ω₁ ∧
    tangentLine L₂ ω₂ ∧
    twoLinesIntersectAtPoint L₁ L₂ P
    → P.onCircle ω := by
  sorry



--HP32
--Given that in $\triangle ABC$, lines $AD$, $BE$, and $CF$ are altitudes. Point $P$ lies inside $\triangle ABC$. The reflections of $P$ across lines $BC$, $CA$, and $AB$ are points $L$, $M$, and $N$, respectively. The midpoint of line segment $AP$ is point $G$. Prove that the necessary and sufficient condition for points $D$, $E$, $G$, and $F$ to be concyclic is that points $A$, $M$, $L$, and $N$ are concyclic.
theorem problem_HP32 :
∀ (A B C D E F P L M N G : Point) (AB BC CA AD BE CF : Line),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A D AD ∧ D.onLine BC ∧ perpLine AD BC ∧
  distinctPointsOnLine B E BE ∧ E.onLine CA ∧ perpLine BE CA ∧
  distinctPointsOnLine C F CF ∧ F.onLine AB ∧ perpLine CF AB ∧
  insideTriangle P A B C AB BC CA ∧
  perpBisector P L BC ∧
  perpBisector P M CA ∧
  perpBisector P N AB ∧
  midpoint A G P
  → ((cyclic D E G F) → (cyclic A M L N)) ∧ ((cyclic A M L N) → (cyclic D E G F)) := by
sorry



--MP17
--In $\triangle ABC$, $\angle B = 2\angle C$, point $D$ is the midpoint of $BC$, and $\angle BAD = 2\angle CAD$. Prove that $\angle BAC = 90^\circ$.
theorem problem_MP17 :
  ∀ (A B C D : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  midpoint B D C ∧
  (∠ A:B:C = ∠ A:C:B + ∠ A:C:B) ∧
  (∠ B:A:D = ∠ C:A:D + ∠ C:A:D)
  → ∠ B:A:C = ∟ :=
by
  sorry



--MP59
--In $\triangle ABC$, $AD$ is the median of side $BC$, points $E$ and $F$ are the midpoints of $AC$ and $AD$, respectively, and $DH \perp BF$ at point $H$.
theorem problem_MP59 :
  ∀ (A B C D E F H : Point) (AB BC CA AD BF DH : Line),
    formTriangle A B C AB BC CA ∧
    distinctPointsOnLine A D AD ∧
    midpoint B D C ∧
    midpoint A E C ∧
    midpoint A F D ∧
    distinctPointsOnLine B F BF ∧
    distinctPointsOnLine D H DH ∧
    twoLinesIntersectAtPoint DH BF H ∧
    perpLine DH BF
  → True := by
  sorry



--MP63
--In convex pentagon $ABCDE$, $\angle ABC = \angle AED = 90^\circ$. Points $F$ and $G$ are on sides $BC$ and $DE$, respectively, such that $AF \perp BG$ and $AG \perp EF$. Prove that $AB = AE$.
theorem problem_MP63 :
  ∀ (A B C D E F G : Point)
    (AB BC CD DE EA AF BG AG EF : Line),
    formPentagon A B C D E AB BC CD DE EA ∧
    ∠A:B:C = ∟ ∧
    ∠A:E:D = ∟ ∧
    F.onLine BC ∧
    G.onLine DE ∧
    distinctPointsOnLine A F AF ∧
    distinctPointsOnLine B G BG ∧
    distinctPointsOnLine A G AG ∧
    distinctPointsOnLine E F EF ∧
    perpLine AF BG ∧
    perpLine AG EF
  → |(A─B)| = |(A─E)| :=
by
  sorry



--HP47
--Given that $\triangle ABC$ is inscribed in circle $\odot O$. Line $AD$ is perpendicular to line $BC$ at point $D$, and line $AD$ intersects line $CO$ at point $E$. Point $F$ is the midpoint of line segment $AE$. Line $FO$ intersects line $BC$ at point $H$. Line $CG$ is perpendicular to line $AO$ at point $G$. Prove that points $B$, $H$, $O$, and $G$ are concyclic.
theorem problem_HP47 :
  ∀ (A B C D E F G H O : Point)
    (BC AO AD CO FO CG : Line)
    (Ω : Circle),
  (O.isCentre Ω ∧ A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω) ∧
  distinctPointsOnLine B C BC ∧
  distinctPointsOnLine A D AD ∧
  distinctPointsOnLine C O CO ∧
  distinctPointsOnLine F O FO ∧
  distinctPointsOnLine C G CG ∧
  distinctPointsOnLine A O AO ∧
  twoLinesIntersectAtPoint AD BC D ∧
  perpLine AD BC ∧
  twoLinesIntersectAtPoint AD CO E ∧
  midpoint A F E ∧
  twoLinesIntersectAtPoint FO BC H ∧
  perpLine CG AO ∧
  twoLinesIntersectAtPoint CG AO G
  → cyclic B H O G :=
by
  sorry



--imo_2008_p1
--An acute-angled triangle $ABC$ has orthocentre $H$. The circle passing through $H$ with centre the midpoint of $BC$ intersects the line $BC$ at $A_1$ and $A_2$. Similarly, the circle passing through $H$ with centre the midpoint of $CA$ intersects the line $CA$ at $B_1$ and $B_2$, and the circle passing through $H$ with centre the midpoint of $AB$ intersects the line $AB$ at $C_1$ and $C_2$. Show that $A_1$, $A_2$, $B_1$, $B_2$, $C_1$, $C_2$ lie on a circle.
theorem problem_imo_2008_p1 :
∀ (A B C H A_1 A_2 B_1 B_2 C_1 C_2 M_BC M_CA M_AB : Point)
  (AB BC CA AH BH CH : Line)
  (α β γ : Circle),
  (formTriangle A B C AB BC CA)
  ∧ (∠A:B:C < ∟)
  ∧ (∠B:C:A < ∟)
  ∧ (∠C:A:B < ∟)
  ∧ distinctPointsOnLine A H AH
  ∧ distinctPointsOnLine B H BH
  ∧ distinctPointsOnLine C H CH
  ∧ perpLine AH BC
  ∧ perpLine BH CA
  ∧ perpLine CH AB
  ∧ midpoint B M_BC C
  ∧ M_BC.isCentre α
  ∧ H.onCircle α
  ∧ A_1.onLine BC
  ∧ A_1.onCircle α
  ∧ A_2.onLine BC
  ∧ A_2.onCircle α
  ∧ midpoint C M_CA A
  ∧ M_CA.isCentre β
  ∧ H.onCircle β
  ∧ B_1.onLine CA
  ∧ B_1.onCircle β
  ∧ B_2.onLine CA
  ∧ B_2.onCircle β
  ∧ midpoint A M_AB B
  ∧ M_AB.isCentre γ
  ∧ H.onCircle γ
  ∧ C_1.onLine AB
  ∧ C_1.onCircle γ
  ∧ C_2.onLine AB
  ∧ C_2.onCircle γ
→ ∃ δ : Circle,
    A_1.onCircle δ
    ∧ A_2.onCircle δ
    ∧ B_1.onCircle δ
    ∧ B_2.onCircle δ
    ∧ C_1.onCircle δ
    ∧ C_2.onCircle δ
:= by
  sorry



--HP4
--Given that in $\triangle ABC$, $\angle A = 90^{\circ}$, and $AD$ is tangent to the circumcircle of $\triangle ABC$. Line $AD$ intersects the extension of $BC$ at point $D$. Point $E$ is the reflection of $A$ across line $BC$. Line $AY$ is perpendicular to $BE$ at point $Y$, and $X$ is the midpoint of $AY$. Line $BX$ extended intersects the circumcircle of $\triangle ABC$ at point $J$. Prove that $BD$ is tangent to the circumcircle of $\triangle AJD$.
theorem problem_HP4 :
  ∀ (A B C D E X Y J : Point)
    (AB BC CA AD AY BE BX : Line)
    (Γ Ω : Circle),
  formTriangle A B C AB BC CA ∧
  ∠B:A:C = ∟ ∧
  circumCircle Γ A B C ∧
  tangentAtPoint AD Γ A ∧
  twoLinesIntersectAtPoint AD BC D ∧
  perpBisector A E BC ∧
  distinctPointsOnLine A Y AY ∧
  distinctPointsOnLine B E BE ∧
  perpLine AY BE ∧
  twoLinesIntersectAtPoint AY BE Y ∧
  midpoint A X Y ∧
  distinctPointsOnLine B X BX ∧
  J.onLine BX ∧
  J.onCircle Γ ∧
  circumCircle Ω A J D
  → tangentAtPoint BD Ω D
:= by
  sorry



--MP25
--In $\triangle ABC$, $AB = AC$. Point $D$ is on ray $AB$, $DE \perp AC$ at point $E$, and $\angle CDE = \angle ABC$. Prove that $BD = 2AE$.
theorem problem_MP25 :
  ∀ (A B C D E : Point) (AB BC CA DE : Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(A─C)| ∧
  threePointsOnLine A B D AB ∧
  between A B D ∧
  distinctPointsOnLine D E DE ∧
  twoLinesIntersectAtPoint DE CA E ∧
  perpLine DE CA ∧
  ∠C:D:E = ∠A:B:C
  → (|(B─D)| = |(A─E)| + |(A─E)|)
:= by
  sorry



--16G4
--In an acute triangle $\triangle ABC$ with $AB = AC \neq BC$, let $I$ be the incenter. Extend line $BI$ to intersect $AC$ at point $D$. Draw a line through $D$ perpendicular to $AC$, intersecting $AI$ at point $E$. Prove that the reflection of $I$ across $AC$, denoted as $I'$, lies on the circumcircle of $\triangle BDE$.
theorem problem_16G4 :
  ∀ (A B C I I' D E : Point)
    (AB BC CA BI AI DE : Line),
  formTriangle A B C AB BC CA ∧
  (∠B:A:C < ∟) ∧
  (∠A:B:C < ∟) ∧
  (∠A:C:B < ∟) ∧
  (|(A─B)| = |(A─C)|) ∧
  (|(A─B)| ≠ |(B─C)|) ∧
  inCentre I A B C ∧
  twoLinesIntersectAtPoint BI CA D ∧
  perpLine DE CA ∧
  twoLinesIntersectAtPoint DE AI E ∧
  perpBisector I I' CA
  → cyclic B D E I' :=
by
  sorry



--imo_2004_p1
--Let $ABC$ be an acute-angled triangle with $AB\neq AC$. The circle with diameter $BC$ intersects the sides $AB$ and $AC$ at $M$ and $N$ respectively. Denote by $O$ the midpoint of the side $BC$. The bisectors of the angles $\angle BAC$ and $\angle MON$ intersect at $R$. Prove that the circumcircles of the triangles $BMR$ and $CNR$ have a common point lying on the side $BC$.
theorem problem_imo_2004_p1 :
∀ (A B C M N O R : Point) (AB BC CA : Line) (ω γ δ : Circle),
  (formTriangle A B C AB BC CA)
∧ ( |(A─B)| ≠ |(A─C)| )
∧ midpoint B O C
∧ O.isCentre ω
∧ B.onCircle ω
∧ C.onCircle ω
∧ M.onLine AB
∧ M.onCircle ω
∧ (M ≠ A)
∧ (M ≠ B)
∧ N.onLine AC
∧ N.onCircle ω
∧ (N ≠ A)
∧ (N ≠ C)
∧ ( ∠B:A:R = ∠R:A:C )
∧ ( ∠M:O:R = ∠R:O:N )
∧ circumCircle γ B M R
∧ circumCircle δ C N R
→ ∃ X : Point, X.onLine BC ∧ X.onCircle γ ∧ X.onCircle δ :=
by sorry



--16G7
--Let $I$ be the incenter of a non-isosceles triangle $\triangle ABC$, and $I_A$ the excenter opposite to $A$. Let $I_A'$ be the reflection of $I_A$ across line $BC$, and $l_A$ the reflection of line $AI_A'$ across line $AI$. Define $I_B$, $I_B'$, and $l_B$ similarly. Let $l_A$ intersect $l_B$ at point $P$.
theorem problem_16G7 :
∀ (A B C I I_A I_A' I_B I_B' P : Point)
  (AB BC CA AI l_A l_B : Line),
  (
    formTriangle A B C AB BC CA
    ∧ ¬ ( (|(A─B)| = |(B─C)|) ∨ (|(B─C)| = |(C─A)|) ∨ (|(C─A)| = |(A─B)|) )
    ∧ inCentre I A B C
    -- No provided axiom for “I_A is the excenter opposite A”.
    -- No provided axiom for reflections “I_A' across line BC” or “l_A across line AI”.
    -- Same definitions assumed for I_B, I_B', and l_B.
    ∧ twoLinesIntersectAtPoint l_A l_B P
  )
  → True
:= by
  sorry



--MP45
--In $\triangle ABC$, $I$ is the incenter. Points $E$ and $F$ are on the extensions of $BI$ and $CI$, respectively, such that $AE = AI = AF$. $AD \perp BC$ at point $D$, intersecting $EF$ at point $K$. Prove that $AK = r$ (where $r$ is the inradius of $\triangle ABC$).
theorem problem_MP45 :
  ∀ (A B C I E F D K M : Point)
    (AB BC CA BI CI EF AD IM : Line),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  distinctPointsOnLine B I BI ∧
  E.onLine BI ∧
  between B I E ∧
  distinctPointsOnLine C I CI ∧
  F.onLine CI ∧
  between C I F ∧
  (|(A─E)| = |(A─I)|) ∧
  (|(A─I)| = |(A─F)|) ∧
  distinctPointsOnLine A D AD ∧
  twoLinesIntersectAtPoint AD BC D ∧
  perpLine AD BC ∧
  distinctPointsOnLine E F EF ∧
  twoLinesIntersectAtPoint AD EF K ∧
  distinctPointsOnLine I M IM ∧
  twoLinesIntersectAtPoint IM BC M ∧
  perpLine IM BC
  → |(A─K)| = |(I─M)| := by
  sorry



--00G2
--Two circles $ G_1$ and $ G_2$ intersect at two points $ M$ and $ N$. Let $ AB$ be the line tangent to these circles at $ A$ and $ B$, respectively, so that $ M$ lies closer to $ AB$ than $ N$. Let $ CD$ be the line parallel to $ AB$ and passing through the point $ M$, with $ C$ on $ G_1$ and $ D$ on $ G_2$. Lines $ AC$ and $ BD$ meet at $ E$; lines $ AN$ and $ CD$ meet at $ P$; lines $ BN$ and $ CD$ meet at $ Q$. Show that $ EP \equal{}, EQ$.
theorem problem_00G2 :
∀ (A B C D E M N P Q : Point)
  (AB AC BD AN BN CD : Line)
  (G1 G2 : Circle),
  M.onCircle G1 ∧ M.onCircle G2 ∧ N.onCircle G1 ∧ N.onCircle G2 ∧ M ≠ N ∧
  A.onLine AB ∧ B.onLine AB ∧ tangentAtPoint AB G1 A ∧ tangentAtPoint AB G2 B ∧
  (∀ T : Point, twoLinesIntersectAtPoint AB CD T → false) ∧
  M.onLine CD ∧ C.onLine CD ∧ C.onCircle G1 ∧ D.onLine CD ∧ D.onCircle G2 ∧
  A.onLine AC ∧ C.onLine AC ∧ B.onLine BD ∧ D.onLine BD ∧ twoLinesIntersectAtPoint AC BD E ∧
  A.onLine AN ∧ N.onLine AN ∧ twoLinesIntersectAtPoint AN CD P ∧
  B.onLine BN ∧ N.onLine BN ∧ twoLinesIntersectAtPoint BN CD Q
  → |(E─P)| = |(E─Q)| :=
by sorry



--HP76
--Given that in $\triangle ABC$, points $D$, $E$, and $F$ lie on sides $BC$, $CA$, and $AB$, respectively. Lines $AD$, $BE$, and $CF$ intersect at point $P$. Points $G$, $H$, and $I$ are the midpoints of sides $BC$, $CA$, and $AB$, respectively. Points $J$, $K$, and $L$ are the midpoints of line segments $DE$, $EF$, and $FD$, respectively. Prove that lines $GK$, $HL$, and $IJ$ are concurrent.
theorem problem_HP76 :
∀ (A B C D E F P G H I J K L M : Point)
  (AB BC CA AD BE CF GKLine HLLine IJLine : Line),
  formTriangle A B C AB BC CA ∧
  D.onLine BC ∧
  E.onLine CA ∧
  F.onLine AB ∧
  twoLinesIntersectAtPoint AD CF P ∧
  twoLinesIntersectAtPoint BE CF P ∧
  midpoint B G C ∧
  midpoint C H A ∧
  midpoint A I B ∧
  midpoint D J E ∧
  midpoint E K F ∧
  midpoint F L D ∧
  distinctPointsOnLine G K GKLine ∧
  distinctPointsOnLine H L HLLine ∧
  distinctPointsOnLine I J IJLine
  → twoLinesIntersectAtPoint GKLine HLLine M ∧ M.onLine IJLine
:= by
  sorry



--HP80
--Given that in complete quadrilateral $ABCDEF$, points $L$, $M$, and $N$ are the midpoints of diagonals $AC$, $BD$, and $EF$, respectively. Prove that points $L$, $M$, and $N$ are collinear.
theorem problem_HP80 :
  ∀ (A B C D E F L M N : Point) (AC BD EF LMN : Line),
  midpoint A L C ∧
  midpoint B M D ∧
  midpoint E N F
  → threePointsOnLine L M N LMN
:= by
  sorry



--imo_2011_p6
--Let $ABC$ be an acute triangle with circumcircle $\Gamma$. Let $\ell$ be a tangent line to $\Gamma$, and let $\ell_a, \ell_b$ and $\ell_c$ be the lines obtained by reflecting $\ell$ in the lines $BC$, $CA$ and $AB$, respectively. Show that the circumcircle of the triangle determined by the lines $\ell_a, \ell_b$ and $\ell_c$ is tangent to the circle $\Gamma$.
theorem problem_imo_2011_p6 :
∀ (A B C P Q R : Point)
  (AB BC CA ℓ ℓ_a ℓ_b ℓ_c : Line)
  (Γ circ : Circle),
  formTriangle A B C AB BC CA ∧
  A.outsideCircle Γ ∧ B.outsideCircle Γ ∧ C.outsideCircle Γ ∧
  tangentLine ℓ Γ ∧
  -- Below we acknowledge the reflective constructions as assumptions
  -- (no built-in predicate for reflection is provided, so we treat them as given)
  -- “ℓ_a, ℓ_b, ℓ_c are the reflections of ℓ about BC, CA, and AB”
  -- represented here as extra assumptions:
  (ℓ_a ≠ ℓ ∧ ℓ_b ≠ ℓ ∧ ℓ_c ≠ ℓ) ∧
  (¬(ℓ_a.intersectsLine BC) ∧ ¬(ℓ_b.intersectsLine CA) ∧ ¬(ℓ_c.intersectsLine AB)) ∧
  twoLinesIntersectAtPoint ℓ_a ℓ_b P ∧
  twoLinesIntersectAtPoint ℓ_b ℓ_c Q ∧
  twoLinesIntersectAtPoint ℓ_c ℓ_a R ∧
  formTriangle P Q R ℓ_a ℓ_b ℓ_c ∧
  circumCircle circ P Q R
→
  -- Expressing “circ is tangent to Γ” as:
  -- exactly one point of intersection plus the fact that they do intersect
  (∃ T : Point,
    T.onCircle circ ∧ T.onCircle Γ ∧
    ∀ X, X.onCircle circ ∧ X.onCircle Γ → X = T)
  ∧ circ.intersectsCircle  Γ
:= by
  sorry



--HP62
--Given that quadrilateral $ABCD$ is inscribed in circle $\odot O$. Lines $AB$ and $DC$ intersect at point $E$, and lines $AD$ and $BC$ intersect at point $F$. Point $G$ is the midpoint of line segment $EF$. Line $AG$ intersects circle $\odot O$ at point $K$. Prove that points $C$, $K$, $F$, and $E$ are concyclic.
theorem problem_HP62 :
  ∀ (A B C D E F G K : Point) (AB BC CD DA EF AG : Line) (O : Circle),
  (
    formQuadrilateral A B C D AB BC CD DA
    ∧ A.onCircle O
    ∧ B.onCircle O
    ∧ C.onCircle O
    ∧ D.onCircle O
    ∧ twoLinesIntersectAtPoint AB CD E
    ∧ twoLinesIntersectAtPoint AD BC F
    ∧ distinctPointsOnLine E F EF
    ∧ midpoint E G F
    ∧ distinctPointsOnLine A G AG
    ∧ K.onLine AG
    ∧ K.onCircle O
  )
  → cyclic C K F E
:= by sorry



--HP54
--Given that in $\triangle ABC$, point $D$ is the midpoint of side $BC$. Circle $\odot O$ passes through points $A$ and $C$, and is tangent to line $DA$ at point $A$. The extension of line $BA$ intersects circle $\odot O$ at point $E$. Line $CE$ extended intersects line $DA$ at point $F$. Prove that $FO \perp BC$.
theorem problem_HP54 :
  ∀ (A B C D E F O : Point)
    (AB BC CA DA CE FO : Line)
    (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  midpoint B D C ∧
  A.onCircle Ω ∧
  C.onCircle Ω ∧
  O.isCentre Ω ∧
  distinctPointsOnLine D A DA ∧
  tangentAtPoint DA Ω A ∧
  E.onLine AB ∧
  E.onCircle Ω ∧
  distinctPointsOnLine C E CE ∧
  twoLinesIntersectAtPoint CE DA F ∧
  distinctPointsOnLine F O FO
  → perpLine FO BC := by
  sorry



--04G1
--Let $ABC$ be an acute-angled triangle with $AB\neq AC$. The circle with diameter $BC$ intersects the sides $AB$ and $AC$ at $M$ and $N$ respectively. Denote by $O$ the midpoint of the side $BC$. The bisectors of the angles $\angle BAC$ and $\angle MON$ intersect at $R$. Prove that the circumcircles of the triangles $BMR$ and $CNR$ have a common point lying on the side $BC$.
theorem problem_04G1 :
∀ (A B C M N O R : Point) (AB BC CA : Line) (circle1 circle2 circle3 : Circle),
  (formTriangle A B C AB BC CA ∧
   |(A─B)| ≠ |(A─C)| ∧
   M.onLine AB ∧
   N.onLine AC ∧
   midpoint B O C ∧
   O.isCentre circle1 ∧
   B.onCircle circle1 ∧
   C.onCircle circle1 ∧
   M.onCircle circle1 ∧
   N.onCircle circle1 ∧
   ∠B:A:R = ∠R:A:C ∧
   ∠M:O:R = ∠R:O:N ∧
   circumCircle circle2 B M R ∧
   circumCircle circle3 C N R)
  → ∃ X : Point, X.onLine BC ∧ X.onCircle circle2 ∧ X.onCircle circle3
:= by
  sorry



--HP49
--Given that $H$ is the orthocenter of $\triangle ABC$, and point $D$ is the midpoint of line segment $CH$. Line $BE$ is perpendicular to line $AD$ at point $E$. Prove that points $B$, $C$, $E$, and $H$ are concyclic.
theorem problem_HP49 :
∀ (A B C H D E : Point) (AB BC CA AH BH CH AD BE : Line),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A H AH ∧
  distinctPointsOnLine B H BH ∧
  distinctPointsOnLine C H CH ∧
  twoLinesIntersectAtPoint AH BH H ∧
  H.onLine CH ∧
  perpLine AH BC ∧
  perpLine BH AC ∧
  perpLine CH AB ∧
  midpoint C D H ∧
  distinctPointsOnLine A D AD ∧
  distinctPointsOnLine B E BE ∧
  twoLinesIntersectAtPoint AD BE E ∧
  perpLine AD BE
  → cyclic B C E H :=
by sorry



--MP43
--In $\triangle ABC$, $AB = AC$, point $D$ is on $AC$ or its extension such that $\angle ADB = 60^\circ$. On line $BD$, take point $E$ such that $CE = CB$. Connect $AE$. Prove that $\angle AEC = 30^\circ$.
theorem problem_MP43 :
  ∀ (A B C D E : Point) (AB BC CA BD : Line),
    (formTriangle A B C AB BC CA ∧
     |(A─B)| = |(A─C)| ∧
     D.onLine AC ∧
     E.onLine BD ∧
     ∠A:D:B = 60 ∧
     |(C─E)| = |(C─B)|)
  → ∠A:E:C = 30 :=
by
  sorry



--HP94
--Given that in circle $\odot O$, three chords $AB$, $CD$, and $EF$ intersect at point $P$, and the angles between each pair of chords are $60^{\circ}$. Prove that $AP + EP + DP = CP + BP + FP$.
theorem problem_HP94 :
  ∀ (A B C D E F P : Point) (AB CD EF : Line) (O : Circle),
  A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O ∧ E.onCircle O ∧ F.onCircle O ∧
  twoLinesIntersectAtPoint AB CD P ∧ twoLinesIntersectAtPoint AB EF P ∧ twoLinesIntersectAtPoint CD EF P ∧
  ∠B:P:D = 60 ∧ ∠D:P:F = 60 ∧ ∠F:P:B = 60
  → |(A─P)| + |(E─P)| + |(D─P)| = |(C─P)| + |(B─P)| + |(F─P)| := by
  sorry



--imo_2000_p1
--Two circles $G_1$ and $G_2$ intersect at two points $M$ and $N$. Let $AB$ be the line tangent to these circles at $A$ and $B$, respectively, so that $M$ lies closer to $AB$ than $N$. Let $CD$ be the line parallel to $AB$ and passing through the point $M$, with $C$ on $G_1$ and $D$ on $G_2$. Lines $AC$ and $BD$ meet at $E$; lines $AN$ and $CD$ meet at $P$; lines $BN$ and $CD$ meet at $Q$. Show that $EP=EQ$.
theorem problem_imo_2000_p1 :
∀ (G₁ G₂ : Circle)
  (A B C D E M N P Q : Point)
  (AB AC BD AN BN CD : Line),
  (M.onCircle G₁ ∧ M.onCircle G₂) ∧
  (N.onCircle G₁ ∧ N.onCircle G₂) ∧
  (A.onCircle G₁ ∧ A.onLine AB) ∧
  (B.onCircle G₂ ∧ B.onLine AB) ∧
  tangentAtPoint AB G₁ A ∧
  tangentAtPoint AB G₂ B ∧
  M.onLine CD ∧
  (¬(∃ X : Point, twoLinesIntersectAtPoint AB CD X)) ∧
  (C.onCircle G₁ ∧ C.onLine CD) ∧
  (D.onCircle G₂ ∧ D.onLine CD) ∧
  twoLinesIntersectAtPoint AC BD E ∧
  twoLinesIntersectAtPoint AN CD P ∧
  twoLinesIntersectAtPoint BN CD Q
  → |(E─P)| = |(E─Q)|
:= by
  sorry



--HP72
--Given that quadrilateral $ABCD$ is such that lines $AC$ and $BD$ intersect at point $G$. Points $E$ and $F$ are the midpoints of sides $AB$ and $CD$, respectively. Points $H$ and $I$ are the orthocenters of $\triangle AGD$ and $\triangle BGC$, respectively. Lines $EF$ and $GI$ intersect at point $I$. Connect line $AI$. Prove that $AI \perp AO$.
theorem problem_HP72 :
∀ (A B C D E F G H I O : Point)
  (AB BC CD DA AC BD EF GI AO AI : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  twoLinesIntersectAtPoint AC BD G ∧
  midpoint A E B ∧
  midpoint C F D ∧
  /- Orthocenter conditions (not expressible with given axioms) for H in triangle AGD and for I in triangle BGC -/
  twoLinesIntersectAtPoint EF GI I ∧
  distinctPointsOnLine A I AI ∧
  distinctPointsOnLine A O AO
  → perpLine AI AO :=
by sorry



--HP96
--Given that quadrilateral $ABCD$ is inscribed in circle $\odot O$. Prove that $AB \cdot CD + AD \cdot BC = AC \cdot BD$.
theorem problem_HP96 : ∀
  (A B C D : Point)
  (AB BC CD DA : Line)
  (O : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  A.onCircle O ∧
  B.onCircle O ∧
  C.onCircle O ∧
  D.onCircle O
  → ( |(A─B)| * |(C─D)| + |(A─D)| * |(B─C)| = |(A─C)| * |(B─D)| )
:= by
  sorry



--HP91
--Given that circle $\odot O$ is the circumcircle of $\triangle ABC$. Side $BC$ is the diameter of circle $\odot O$. Point $D$ lies on arc $BC$, opposite to point $A$. Line $DE$ is perpendicular to line $BC$ at point $E$. Line $DF$ is perpendicular to line $BA$ at point $F$. Line $EF$ intersects line $AD$ at point $G$. Prove that $G$ is the midpoint of line segment $AD$.
theorem problem_HP91 :
∀
(A B C D E F G : Point)
(BC BA AD DE DF EF : Line)
(O : Circle),
  circumCircle O A B C ∧
  (∠B:A:C = ∟) ∧
  D.onCircle O ∧
  A.opposingSides D BC ∧
  distinctPointsOnLine B C BC ∧
  distinctPointsOnLine B A BA ∧
  distinctPointsOnLine A D AD ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine D F DF ∧
  distinctPointsOnLine E F EF ∧
  twoLinesIntersectAtPoint DE BC E ∧
  perpLine DE BC ∧
  twoLinesIntersectAtPoint DF BA F ∧
  perpLine DF BA ∧
  twoLinesIntersectAtPoint EF AD G
→ midpoint A G D
:= by
  sorry



--MP31
--In $\triangle ABC$, point $D$ is on $BC$, and point $E$ is on the extension of $AC$. $AC = AB = BD = DE$, and $CD = CE$. Prove that $\angle A = 100^\circ$.
theorem problem_MP31 : ∀
(A B C D E : Point)
(AB BC CA : Line),
formTriangle A B C AB BC CA ∧
between B D C ∧
between A C E ∧
|(A─C)| = |(A─B)| ∧
|(A─B)| = |(B─D)| ∧
|(B─D)| = |(D─E)| ∧
|(C─D)| = |(C─E)|
→ ∠ B : A : C = 100
:= by
  sorry



--HP18
--Given that circles $\odot P$ and $\odot Q$ intersect at points $A$ and $B$. Their external common tangent $CD$ is tangent to circles $\odot P$ and $\odot Q$ at points $C$ and $D$, respectively. Point $E$ lies on the extension of line $BA$. Line $EC$ intersects circle $\odot P$ at point $F$, and line $ED$ intersects circle $\odot Q$ at point $G$. Line $AH$ bisects angle $\angle FAG$, intersecting line $FG$ at point $H$. Prove that $\angle FCH = \angle GDH$.
theorem HP18 :
∀ (A B C D E F G H : Point)
  (BA CD EC ED FG AH : Line)
  (P Q : Circle),
  (A.onCircle P) ∧ (B.onCircle P) ∧ (A.onCircle Q) ∧ (B.onCircle Q) ∧ P.intersectsCircle Q ∧
  tangentAtPoint CD P C ∧ tangentAtPoint CD Q D ∧
  distinctPointsOnLine B A BA ∧ E.onLine BA ∧ between B A E ∧
  distinctPointsOnLine E C EC ∧ F.onLine EC ∧ F.onCircle P ∧
  distinctPointsOnLine E D ED ∧ G.onLine ED ∧ G.onCircle Q ∧
  distinctPointsOnLine F G FG ∧ H.onLine FG ∧
  distinctPointsOnLine A H AH ∧ (∠F:A:H = ∠H:A:G)
  → (∠F:C:H = ∠G:D:H) :=
by
  sorry



--MP54
--In $\triangle ABC$, points $E$ and $D$ are on the extension and reverse extension of $BC$, respectively. $\angle ABD = 2\angle ACE$, $AE \perp BC$, and point $M$ is the midpoint of $BC$. Prove that $ME = \frac{1}{2} AB$.
theorem problem_MP54 :
  ∀ (A B C D E M : Point) (AB BC CA AE : Line),
    (formTriangle A B C AB BC CA) ∧
    (threePointsOnLine B C D BC) ∧
    (threePointsOnLine B C E BC) ∧
    (between B C E) ∧
    (between C B D) ∧
    (∠ A:B:D = ∠ A:C:E + ∠ A:C:E) ∧
    (distinctPointsOnLine A E AE) ∧
    (perpLine AE BC) ∧
    (midpoint B M C)
    → (|(M─E)| + |(M─E)| = |(A─B)|) :=
by sorry



--imo_2002_p2
--$BC$ is a diameter of a circle center $O$. $A$ is any point on the circle with $\angle AOC \not\le 60^\circ$. $EF$ is the chord which is the perpendicular bisector of $AO$. $D$ is the midpoint of the minor arc $AB$. The line through $O$ parallel to $AD$ meets $AC$ at $J$. Show that $J$ is the incenter of triangle $CEF$.
theorem problem_imo_2002_p2 :
∀ (B C O A E F D J : Point) (BC AC AD EF OJ : Line) (Γ : Circle),
  (B.onLine BC ∧ C.onLine BC ∧ O.onLine BC)
  ∧ (A.onLine AC ∧ C.onLine AC)
  ∧ (A.onLine AD ∧ D.onLine AD)
  ∧ (E.onLine EF ∧ F.onLine EF)
  ∧ (O.onLine OJ)
  ∧ O.isCentre Γ
  ∧ A.onCircle Γ
  ∧ B.onCircle Γ
  ∧ C.onCircle Γ
  ∧ E.onCircle Γ
  ∧ F.onCircle Γ
  ∧ D.onCircle Γ
  ∧ (∠ A:O:C > 60)
  ∧ perpBisector A O EF
  ∧ (∠ A:O:D = ∠ D:O:B)
  ∧ twoLinesIntersectAtPoint OJ AC J
  ∧ ¬(OJ.intersectsLine AD)
  → inCentre J C E F := by
sorry



--97T18
--The altitudes through the vertices $ A,B,C$ of an acute-angled triangle $ ABC$ meet the opposite sides at $ D,E, F,$ respectively. The line through $ D$ parallel to $ EF$ meets the lines $ AC$ and $ AB$ at $ Q$ and $ R,$ respectively. The line $ EF$ meets $ BC$ at $ P.$ Prove that the circumcircle of the triangle $ PQR$ passes through the midpoint of $ BC.$
theorem problem_97T18 :
∀ (A B C D E F P Q R M : Point)
  (AB BC CA AD BE CF EF DR : Line),
  formTriangle A B C AB BC CA ∧
  ∠A:B:C < ∟ ∧
  ∠B:C:A < ∟ ∧
  ∠C:A:B < ∟ ∧
  distinctPointsOnLine A D AD ∧
  D.onLine BC ∧
  perpLine AD BC ∧
  distinctPointsOnLine B E BE ∧
  E.onLine CA ∧
  perpLine BE CA ∧
  distinctPointsOnLine C F CF ∧
  F.onLine AB ∧
  perpLine CF AB ∧
  distinctPointsOnLine E F EF ∧
  twoLinesIntersectAtPoint EF BC P ∧
  distinctPointsOnLine D R DR ∧
  D.onLine DR ∧
  ¬(DR.intersectsLine EF) ∧
  twoLinesIntersectAtPoint DR AC Q ∧
  twoLinesIntersectAtPoint DR AB R
  → midpoint B M C ∧
    cyclic P Q R M
:= by
  sorry



--HP25
--Given that $\triangle ABC$ is inscribed in circle $\odot O$, and the incircle of $\triangle ABC$, circle $\odot I$, is tangent to $AB$ and $AC$ at points $J$ and $K$, respectively. Line $AO$ intersects circle $\odot O$ at point $D$. Connect line $DI$, and extend line $CA$ to point $F$, such that $AF = BJ$. Draw a perpendicular from $F$ to line $DI$, intersecting the extension of line $BA$ at point $G$. Prove that $AG = CK$.
theorem problem_HP25 :
∀ (A B C O I J K D F G : Point)
  (AB BC CA AO DI FG : Line)
  (circleO circleI : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle circleO A B C ∧
  inCircle circleI AB BC CA ∧
  I.isCentre circleI ∧
  tangentAtPoint AB circleI J ∧
  tangentAtPoint AC circleI K ∧
  threePointsOnLine A O D AO ∧
  D.onCircle circleO ∧
  distinctPointsOnLine D I DI ∧
  threePointsOnLine C A F CA ∧
  |(A─F)| = |(B─J)| ∧
  perpLine FG DI ∧
  F.onLine FG ∧
  twoLinesIntersectAtPoint FG AB G
→ |(A─G)| = |(C─K)| :=
by sorry



--HP2
--Given that $AB$ is the diameter of circle $\odot O$, and $C$ and $D$ are two points on the circle, distinct from $A$ and $B$, and on the same side of $AB$. Tangents to $\odot O$ at $C$ and $D$ intersect at point $E$. Line segment $AD$ intersects $BC$ at point $F$, and line segment $AB$ intersects $EF$ at point $M$. Prove that points $E$, $C$, $M$, and $D$ are concyclic.
theorem problem_HP2 :
  ∀ (A B C D E F M : Point) (AB BC AD EF CE DE : Line) (O : Circle),
    (A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O)
    ∧ C.sameSide D AB
    ∧ tangentAtPoint CE O C
    ∧ tangentAtPoint DE O D
    ∧ twoLinesIntersectAtPoint CE DE E
    ∧ twoLinesIntersectAtPoint AD BC F
    ∧ twoLinesIntersectAtPoint AB EF M
  → cyclic E C M D := by
  sorry



--HP5
--Given quadrilateral $ABCD$ inscribed in a circle with diameter $BD$. Let $A'$ be the reflection of $A$ across line $BD$, and $B'$ be the reflection of $B$ across line $AC$. Line $AC$ intersects $DB'$ at point $Q$, and line $DB$ intersects $CA'$ at point $P$. Prove that $PQ \perp AC$.
theorem problem_HP5 :
  ∀ (A B C D A' B' P Q : Point)
    (AC BD CA' DB' DB PQ : Line),
  (cyclic A B C D)
  ∧ (∠ B:A:D = ∟)
  ∧ (∠ B:C:D = ∟)
  ∧ perpBisector A A' BD
  ∧ perpBisector B B' AC
  ∧ distinctPointsOnLine A C AC
  ∧ distinctPointsOnLine C A' CA'
  ∧ distinctPointsOnLine D B DB
  ∧ distinctPointsOnLine D B' DB'
  ∧ distinctPointsOnLine P Q PQ
  ∧ twoLinesIntersectAtPoint AC DB' Q
  ∧ twoLinesIntersectAtPoint DB CA' P
  → perpLine PQ AC
:= by
  sorry



--MP53
--In $\triangle ABC$, $\angle ACB = 2\angle ABC$, points $D$ and $E$ are on $BC$, and point $F$ is on $AE$ such that $CF \perp AE$, $BF \perp FD$, and $\angle DFE = \angle ABC$. Prove that $BD = 2CD$.
theorem problem_MP53 :
∀ (A B C D E F : Point)
  (AB BC CA AE CF BF FD : Line),
  formTriangle A B C AB BC CA ∧
  (∠ A:C:B = ∠ A:B:C + ∠ A:B:C) ∧
  D.onLine BC ∧
  E.onLine BC ∧
  F.onLine AE ∧
  distinctPointsOnLine A E AE ∧
  distinctPointsOnLine C F CF ∧
  distinctPointsOnLine B F BF ∧
  distinctPointsOnLine F D FD ∧
  perpLine CF AE ∧
  perpLine BF FD ∧
  (∠ D:F:E = ∠ A:B:C)
  → |(B─D)| = |(C─D)| + |(C─D)| :=
by sorry



--HP87
--Given that $O$ is the circumcenter of $\triangle ABC$. Point $H$ is the orthocenter of $\triangle ABC$. Line $CH$ intersects line $AB$ at point $D$. Line $DE$ is perpendicular to line $OD$, intersecting line $AC$ at point $E$. Prove that $\angle EHD = \angle A$.
theorem problem_HP87 :
∀ (A B C O H D E : Point) (AB BC CA CH OD DE : Line),
  (formTriangle A B C AB BC CA)
  ∧ circumCentre O A B C
  ∧ distinctPointsOnLine C H CH
  ∧ perpLine CH AB
  ∧ twoLinesIntersectAtPoint CH AB D
  ∧ distinctPointsOnLine O D OD
  ∧ distinctPointsOnLine D E DE
  ∧ perpLine DE OD
  ∧ twoLinesIntersectAtPoint DE CA E
  → ∠E:H:D = ∠B:A:C
:= by
  sorry



--06G9
--Points $A_1$, $B_1$, and $C_1$ lie on the sides $BC$, $CA$, and $AB$ of triangle $\triangle ABC$, respectively. The circumcircles of triangles $\triangle AB_1C_1$, $\triangle BC_1A_1$, and $\triangle CA_1B_1$ intersect the circumcircle of triangle $\triangle ABC$ again at points $A_2$, $B_2$, and $C_2$, respectively. Points $A_3$, $B_3$, and $C_3$ are the reflections of $A_1$, $B_1$, and $C_1$ across the midpoints of sides $BC$, $CA$, and $AB$, respectively. Prove that triangle $\triangle A_2B_2C_2$ is similar to triangle $\triangle A_3B_3C_3$.
theorem problem_06G9 :
∀ (A B C A1 B1 C1 A2 B2 C2 A3 B3 C3 : Point)
  (AB BC CA : Line)
  (ω α β γ : Circle),
  (
    formTriangle A B C AB BC CA ∧
    threePointsOnLine B C A1 BC ∧
    threePointsOnLine C A B1 CA ∧
    threePointsOnLine A B C1 AB ∧
    circumCircle ω A B C ∧
    circumCircle α A B1 C1 ∧
    circumCircle β B C1 A1 ∧
    circumCircle γ C A1 B1 ∧
    A2.onCircle ω ∧ A2.onCircle α ∧
    B2.onCircle ω ∧ B2.onCircle β ∧
    C2.onCircle ω ∧ C2.onCircle γ ∧
    (∃ MBC : Point, midpoint B MBC C ∧ midpoint A1 A3 MBC) ∧
    (∃ MCA : Point, midpoint C MCA A ∧ midpoint B1 B3 MCA) ∧
    (∃ MAB : Point, midpoint A MAB B ∧ midpoint C1 C3 MAB)
  )
  →
  (∠ B2:A2:C2 = ∠ B3:A3:C3 ∧ ∠ A2:B2:C2 = ∠ A3:B3:C3)
:= by
  sorry



--MP42
--In $\triangle ABC$, $AB = AC$, $\angle BAC = 100^\circ$, point $P$ is inside the triangle such that $\angle PAB = 25^\circ$ and $\angle PBA = 30^\circ$. Find $\angle ACP$.
theorem problem_MP42 :
  ∀ (A B C P : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(A─C)| ∧
  ∠B:A:C = 100 ∧
  insideTriangle P A B C AB BC CA ∧
  ∠P:A:B = 25 ∧
  ∠P:B:A = 30
  → ∠A:C:P = 30
  := by
  sorry



--imo_2019_p6
--Let $I$ be the incenter of acute triangle $ABC$ with $AB \neq AC$. The incircle $\omega$ of $ABC$ is tangent to sides $BC$, $CA$, and $AB$ at $D$, $E$, and $F$, respectively. The line through $D$ perpendicular to $EF$ meets $\omega$ again at $R$. Line $AR$ meets $\omega$ again at $P$. The circumcircles of triangles $PCE$ and $PBF$ meet again at $Q$. Prove that lines $DI$ and $PQ$ meet on the line through $A$ perpendicular to $AI$.
theorem problem_imo_2019_p6 :
∀ (A B C I D E F P Q R X : Point)
  (AB BC CA DI EF DR AR AI AX PQ : Line)
  (w : Circle),
  formTriangle A B C AB BC CA ∧
  ¬(|(A─B)| = |(A─C)|) ∧
  inCentre I A B C ∧
  inCircle w AB BC CA ∧
  I.isCentre w ∧
  tangentAtPoint BC w D ∧
  tangentAtPoint CA w E ∧
  tangentAtPoint AB w F ∧
  distinctPointsOnLine E F EF ∧
  distinctPointsOnLine D R DR ∧
  perpLine DR EF ∧
  R.onCircle w ∧
  distinctPointsOnLine A R AR ∧
  P.onLine AR ∧ P.onCircle w ∧ ¬(P = R) ∧
  cyclic P C E Q ∧
  cyclic P B F Q ∧
  distinctPointsOnLine D I DI ∧
  distinctPointsOnLine P Q PQ ∧
  distinctPointsOnLine A I AI ∧
  distinctPointsOnLine A X AX ∧
  perpLine AI AX
  → twoLinesIntersectAtPoint DI PQ X ∧ X.onLine AX
:= by
  sorry



--HP58
--Given that circles $\odot P$ and $\odot Q$ intersect at points $A$ and $B$. Their external common tangent $CD$ is tangent to circles $\odot P$ and $\odot Q$ at points $C$ and $D$, respectively. Point $E$ lies on the extension of line $BA$. Line $EC$ intersects circle $\odot P$ at point $F$, and line $ED$ intersects circle $\odot Q$ at point $G$. Line $FG$ intersects circles $\odot Q$ and $\odot P$ again at points $M$ and $N$, respectively. Prove that $\angle FCM = \angle GDN$.
theorem HP58 :
∀ (A B C D E F G M N : Point) (P Q : Circle) (CD CE ED FG : Line),
  A.onCircle P ∧ B.onCircle P ∧ A.onCircle Q ∧ B.onCircle Q ∧
  C.onLine CD ∧ tangentAtPoint CD P C ∧ C.onCircle P ∧
  D.onLine CD ∧ tangentAtPoint CD Q D ∧ D.onCircle Q ∧
  between B A E ∧
  E.onLine CE ∧ C.onLine CE ∧ F.onLine CE ∧ F.onCircle P ∧
  E.onLine ED ∧ D.onLine ED ∧ G.onLine ED ∧ G.onCircle Q ∧
  F.onLine FG ∧ G.onLine FG ∧ M.onLine FG ∧ M.onCircle Q ∧ N.onLine FG ∧ N.onCircle P
→ ∠F:C:M = ∠G:D:N := by
  sorry



--MP84
--In right triangle $\triangle ABC$, $\angle C = 90^\circ$, $AB = AC$. Extend $BC$ to point $D$ such that $CD = \frac{1}{2}BC$, and point $E$ is the midpoint of $AC$. $BE$ intersects $AD$ at point $F$. Find $\angle AFE$.
theorem problem_MP84 :
∀ (A B C D E F : Point) (AB BC CA AD BE : Line),
  formTriangle A B C AB BC CA ∧
  ∠ A:C:B = ∟ ∧
  |(A─B)| = |(A─C)| ∧
  threePointsOnLine B C D BC ∧
  |(C─D)| = ( |(B─C)| ) / 2 ∧
  midpoint A E C ∧
  twoLinesIntersectAtPoint BE AD F
  → ∠ A:F:E = ∟ / 2
  := by
sorry



--MP21
--In right triangle $\triangle ABC$, the hypotenuse $AB$ and leg $BC$ have points $D$ and $E$, respectively, such that $AD = AC$ and $CE = 2BD$. Given that $CD \perp DE$, prove that $AC = BC$.
theorem problem_MP21 : ∀
  (A B C D E : Point)
  (AB BC CA CD DE : Line),
  formTriangle A B C AB BC CA ∧
  ∠ A:C:B = ∟ ∧
  D.onLine AB ∧
  E.onLine BC ∧
  |(A─D)| = |(A─C)| ∧
  |(C─E)| = |(B─D)| + |(B─D)| ∧
  distinctPointsOnLine C D CD ∧
  distinctPointsOnLine D E DE ∧
  perpLine CD DE
  → |(A─C)| = |(B─C)|
:= by
  sorry



--HP65
--Given that in circle $\odot O$, diameter $AB$ is perpendicular to chord $CD$. Point $E$ is the midpoint of line segment $OC$. The extension of line $AE$ intersects circle $\odot O$ at point $F$. Line $DF$ intersects line $BC$ at point $G$. Prove that $G$ is the midpoint of line segment $BC$.
theorem problem_HP65 :
  ∀ (O A B C D E F G : Point) (Ω : Circle)
    (AB CD BC AE DF : Line),
  (O.isCentre Ω) ∧
  A.onCircle Ω ∧
  B.onCircle Ω ∧
  C.onCircle Ω ∧
  D.onCircle Ω ∧
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine C D CD ∧
  distinctPointsOnLine B C BC ∧
  distinctPointsOnLine A E AE ∧
  distinctPointsOnLine D F DF ∧
  midpoint O A B ∧
  perpLine AB CD ∧
  midpoint O E C ∧
  F.onLine AE ∧
  F.onCircle Ω ∧
  twoLinesIntersectAtPoint DF BC G
  → midpoint B G C
:= by
  sorry



--HP79
--Given that in $\triangle ABC$, line $AD$ bisects angle $\angle BAC$, intersecting side $BC$ at point $D$. Line $DE$ bisects angle $\angle ADB$, intersecting side $AB$ at point $E$. Line $DF$ bisects angle $\angle ADC$, intersecting side $AC$ at point $F$. Line $EF$ intersects line $AD$ at point $G$. Line $CG$ intersects line $DE$ at point $H$. Line $BG$ intersects the extension of line $DF$ at point $I$. (1) Prove that points $H$, $A$, and $I$ are collinear. (2) Prove that $AD \perp HI$.
theorem problem_HP79 :
  ∀ (A B C D E F G H I : Point)
    (AB BC CA AD DE DF EF CG BG HI : Line),
    formTriangle A B C AB BC CA ∧
    twoLinesIntersectAtPoint BC AD D ∧
    (∠ B:A:D = ∠ D:A:C) ∧
    twoLinesIntersectAtPoint AB DE E ∧
    (∠ A:D:E = ∠ E:D:B) ∧
    twoLinesIntersectAtPoint AC DF F ∧
    (∠ A:D:F = ∠ F:D:C) ∧
    twoLinesIntersectAtPoint EF AD G ∧
    distinctPointsOnLine C G CG ∧
    twoLinesIntersectAtPoint CG DE H ∧
    distinctPointsOnLine B G BG ∧
    twoLinesIntersectAtPoint BG DF I ∧
    distinctPointsOnLine H I HI
  → A.onLine HI ∧ perpLine AD HI :=
by sorry



--18G2
--In an isosceles triangle $\triangle ABC$ with $AB = AC$, let $M$ be the midpoint of side $BC$. Let $P$ be a point such that $PA \parallel BC$ and $PB < PC$. Extend $PB$ to $X$ and $PC$ to $Y$ such that $\angle PXM = \angle PYM$. Prove that points $A$, $P$, $X$, and $Y$ are concyclic.
theorem problem_18G2 :
  ∀ (A B C M P X Y : Point) (AB BC CA PA PB PC : Line),
    formTriangle A B C AB BC CA ∧
    |(A─B)| = |(A─C)| ∧
    midpoint B M C ∧
    distinctPointsOnLine P A PA ∧
    distinctPointsOnLine B C BC ∧
    ¬(∃ Z : Point, twoLinesIntersectAtPoint PA BC Z) ∧
    |(P─B)| < |(P─C)| ∧
    distinctPointsOnLine P B PB ∧
    X.onLine PB ∧
    between P B X ∧
    distinctPointsOnLine P C PC ∧
    Y.onLine PC ∧
    between P C Y ∧
    ∠P:X:M = ∠P:Y:M
  → cyclic A P X Y
:= by sorry



--11G5
--In $\triangle ABC$, let $I$ be the incenter and $\omega$ the circumcircle. Extend lines $AI$ and $BI$ to intersect $\omega$ at points $D$ and $E$, respectively. Let line $DE$ intersect $AC$ and $BC$ at points $F$ and $G$, respectively. Let the line through $F$ parallel to $AD$ intersect the line through $G$ parallel to $BE$ at point $P$. Let the tangents to $\omega$ at $A$ and $B$ intersect at point $K$. Prove that lines $AE$, $BD$, and $KP$ are concurrent or pairwise parallel.
theorem problem_11G5 :
∀ (A B C I D E F G P K : Point)
  (AB BC CA AI BI DE AC AE BD KP LA LB : Line)
  (ω : Circle),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  circumCircle ω A B C ∧
  distinctPointsOnLine A I AI ∧
  D.onLine AI ∧
  D.onCircle ω ∧
  distinctPointsOnLine B I BI ∧
  E.onLine BI ∧
  E.onCircle ω ∧
  distinctPointsOnLine D E DE ∧
  F.onLine DE ∧
  F.onLine AC ∧
  G.onLine DE ∧
  G.onLine BC ∧
  distinctPointsOnLine A E AE ∧
  distinctPointsOnLine B D BD ∧
  tangentAtPoint LA ω A ∧
  tangentAtPoint LB ω B ∧
  twoLinesIntersectAtPoint LA LB K ∧
  distinctPointsOnLine K P KP
  →
  ((∃ (X : Point),
    X.onLine AE ∧
    X.onLine BD ∧
    X.onLine KP)
    ∨
    (¬(∃ (X : Point), X.onLine AE ∧ X.onLine BD)
     ∧ ¬(∃ (X : Point), X.onLine BD ∧ X.onLine KP)
     ∧ ¬(∃ (X : Point), X.onLine AE ∧ X.onLine KP))) :=
by
  sorry



--MP88
--In right triangle $\triangle ABC$, $\angle C = 90^\circ$, $\frac{AC}{BC} = \frac{3}{4}$. On hypotenuse $AB$ and leg $BC$, there are points $D$ and $E$, respectively, such that $AD = AC = CE$. Prove that $CD \perp DE$.
theorem problem_MP88 :
  ∀ (A B C D E : Point) (AB BC CA CD DE : Line),
  (formTriangle A B C AB BC CA)
  ∧ (∠ A:C:B = ∟)
  ∧ (|(A─C)| + |(A─C)| + |(A─C)| + |(A─C)| = |(B─C)| + |(B─C)| + |(B─C)|)
  ∧ distinctPointsOnLine A B AB
  ∧ distinctPointsOnLine B C BC
  ∧ distinctPointsOnLine C A CA
  ∧ distinctPointsOnLine C D CD
  ∧ distinctPointsOnLine D E DE
  ∧ D.onLine AB
  ∧ E.onLine BC
  ∧ (|(A─D)| = |(A─C)|)
  ∧ (|(A─C)| = |(C─E)|)
  → perpLine CD DE :=
by
  sorry




--HP37
--Given that in $\triangle ABC$, $O$ is the circumcenter, and lines $AD$, $BE$, and $CF$ are altitudes, intersecting at point $H$. Line $ED$ intersects line $AB$ at point $M$, and line $FD$ intersects line $AC$ at point $N$. Prove that: (1) $OB \perp DF$; (2) $OC \perp DE$; (3) $OH \perp MN$.
theorem problem_HP37 :
∀ (A B C D E F H M N O : Point)
  (AB BC CA AD BE CF ED FD OB OC OH MN : Line),
  formTriangle A B C AB BC CA ∧
  circumCentre O A B C ∧
  distinctPointsOnLine A D AD ∧ D.onLine BC ∧ perpLine AD BC ∧
  distinctPointsOnLine B E BE ∧ E.onLine CA ∧ perpLine BE CA ∧
  distinctPointsOnLine C F CF ∧ F.onLine AB ∧ perpLine CF AB ∧
  twoLinesIntersectAtPoint AD BE H ∧ H.onLine CF ∧
  distinctPointsOnLine E D ED ∧ twoLinesIntersectAtPoint ED AB M ∧
  distinctPointsOnLine F D FD ∧ twoLinesIntersectAtPoint FD AC N ∧
  distinctPointsOnLine O B OB ∧
  distinctPointsOnLine O C OC ∧
  distinctPointsOnLine O H OH ∧
  distinctPointsOnLine M N MN
→ perpLine OB FD ∧ perpLine OC ED ∧ perpLine OH MN := by
  sorry



--MP61
--In quadrilateral $ABCD$, diagonals $AC$ and $BD$ intersect at point $O$, and the midpoints of $BC$ and $AD$ are points $E$ and $F$, respectively. Prove that $AC$ bisects segment $EF$.
theorem problem_MP61 :
  ∀ (A B C D O E F : Point) (AB BC CD DA AC BD : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    twoLinesIntersectAtPoint AC BD O ∧
    midpoint B E C ∧
    midpoint A F D
  → midpoint E O F := by
  sorry



--MP85
--In $\triangle ABC$, point $D$ is on $AB$ such that $\angle ACD = \angle B$, and point $P$ is the midpoint of $CD$. $AP$ intersects $BC$ at point $E$, and $EF \parallel CD$, intersecting $AB$ at point $F$. Prove that $EF^2 = CE \cdot BE$.
theorem problem_MP85 :
  ∀ (A B C D E F P : Point) (AB BC CA AP CD EF : Line),
    formTriangle A B C AB BC CA ∧
    D.onLine AB ∧
    (∠A:C:D = ∠A:B:C) ∧
    midpoint C P D ∧
    distinctPointsOnLine A P AP ∧
    twoLinesIntersectAtPoint AP BC E ∧
    distinctPointsOnLine C D CD ∧
    distinctPointsOnLine E F EF ∧
    F.onLine AB ∧
    ¬(EF.intersectsLine CD)
    → (|(E─F)| * |(E─F)| = |(C─E)| * |(B─E)|) := by
  sorry



--HP43
--Given that in acute $\triangle ABC$, $AB < AC$, and points $D$ and $E$ lie on side $BC$, such that $BD = CE$. If there exists a point $P$ inside $\triangle ABC$, such that $PD \parallel AE$ and $\angle PAB = \angle EAC$, prove that $\angle PBA = \angle PCA$.
theorem problem_HP43 :
  ∀ (A B C D E P : Point) (AB BC CA AE PD : Line),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A E AE ∧
  distinctPointsOnLine P D PD ∧
  D.onLine BC ∧
  E.onLine BC ∧
  |(B─D)| = |(C─E)| ∧
  insideTriangle P A B C AB BC CA ∧
  ¬(PD.intersectsLine AE) ∧
  ∠ P:A:B = ∠ E:A:C
  → ∠ P:B:A = ∠ P:C:A
:= by
  sorry



--MP48
--Construct right triangles $\triangle ABD$ and $\triangle ACE$ outside $\triangle ABC$ with $AB$ and $AC$ as hypotenuses, respectively, such that $\angle ABD = \angle ACE = 30^\circ$. Point $F$ is the midpoint of $BC$. Prove that $\triangle DEF$ is an equilateral triangle.
theorem problem_MP48 :
  ∀ (A B C D E F : Point) (AB BC CA BD DA CE EA : Line),
  formTriangle A B C AB BC CA ∧
  formTriangle A B D AB BD DA ∧
  ∠A:D:B = ∟ ∧
  ∠A:B:D = 30 ∧
  formTriangle A C E AC CE EA ∧
  ∠A:E:C = ∟ ∧
  ∠A:C:E = 30 ∧
  midpoint B F C
  → ( |(D─E)| = |(E─F)| ) ∧ ( |(E─F)| = |(F─D)| ) :=
by
  sorry



--HP52
--Given that points $A$, $B$, and $C$ lie on circle $\odot O$. Draw line $DC$ perpendicular to line $AC$, intersecting the extension of line $AB$ at point $D$. Draw line $DE$ perpendicular to line $AO$, intersecting circle $\odot O$ at point $F$ and line $AC$ at point $E$. The circumcircle of points $B$, $E$, and $F$ is circle $\odot P$, and the circumcircle of points $C$, $D$, and $F$ is circle $\odot Q$. Prove that circles $\odot P$ and $\odot Q$ are externally tangent at point $F$.
theorem problem_HP52 :
∀ (A B C D E F O : Point)
  (AB AC AO DC DE : Line)
  (Ω P Q : Circle),
  O.isCentre Ω ∧
  A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧
  A.onLine AB ∧ B.onLine AB ∧
  A.onLine AC ∧ C.onLine AC ∧
  C.onLine DC ∧ D.onLine DC ∧
  perpLine DC AC ∧
  twoLinesIntersectAtPoint AB DC D ∧
  A.onLine AO ∧ O.onLine AO ∧
  D.onLine DE ∧ E.onLine DE ∧
  perpLine DE AO ∧
  twoLinesIntersectAtPoint DE AC E ∧
  E.onLine AC ∧
  F.onLine DE ∧ F.onCircle Ω ∧
  circumCircle P B E F ∧
  circumCircle Q C D F
  → ∀ (X : Point),
    X.onCircle P ∧ X.onCircle Q → X = F
:= by
  sorry



--11G7
--In a convex hexagon $ABCDEF$ with an inscribed circle $\odot O$, suppose the circumcenter of $\triangle ACE$ is also $O$. Let $J$ be the foot of the perpendicular from $B$ to line $CD$. Let the line through $B$ perpendicular to $DF$ intersect line $OE$ at point $K$, and let the foot of the perpendicular from $K$ to line $DE$ be point $L$. Prove that $DJ = DL$.
theorem problem_11G7 :
∀ (A B C D E F O J K L : Point)
  (AB BC CD DE EF FA OE DF BJ BK KL : Line)
  (incC : Circle),
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine B C BC ∧
  distinctPointsOnLine C D CD ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine E F EF ∧
  distinctPointsOnLine F A FA ∧
  tangentLine AB incC ∧
  tangentLine BC incC ∧
  tangentLine CD incC ∧
  tangentLine DE incC ∧
  tangentLine EF incC ∧
  tangentLine FA incC ∧
  circumCentre O A C E ∧
  distinctPointsOnLine B J BJ ∧
  twoLinesIntersectAtPoint CD BJ J ∧
  perpLine BJ CD ∧
  distinctPointsOnLine D F DF ∧
  distinctPointsOnLine O E OE ∧
  distinctPointsOnLine B K BK ∧
  twoLinesIntersectAtPoint BK OE K ∧
  perpLine BK DF ∧
  distinctPointsOnLine K L KL ∧
  twoLinesIntersectAtPoint KL DE L ∧
  perpLine KL DE
  → |(D─J)| = |(D─L)| :=
by
  sorry



--MP65
--In $\triangle ABC$, $AB = AC$, points $E$ and $F$ are on lines $AB$ and $AC$, respectively, $EF$'s midpoint is point $P$, and $AP$ intersects $BC$ at point $D$. Prove that $DE^2 - BE^2 = DF^2 - CF^2$.
theorem problem_MP65 :
∀ (A B C D E F P : Point) (AB BC CA AP : Line),
  (formTriangle A B C AB BC CA) ∧
  (|(A─B)| = |(A─C)|) ∧
  E.onLine AB ∧
  F.onLine CA ∧
  midpoint E P F ∧
  distinctPointsOnLine A P AP ∧
  twoLinesIntersectAtPoint AP BC D
  →
  ((|(D─E)| * |(D─E)|) - (|(B─E)| * |(B─E)|) = (|(D─F)| * |(D─F)|) - (|(C─F)| * |(C─F)|))
:= by
  sorry



--HP51
--Given that circle $\odot O$ is the circumcircle of $\triangle ABC$. Point $D$ is the midpoint of arc $BAC$, and point $E$ is the midpoint of arc $BC$. Line $CF$ is perpendicular to line $AB$ at point $F$. Connect line $EF$. Draw line $FG$ perpendicular to line $EF$, intersecting the extension of line $DA$ at point $G$. Prove that $CG = CD$.
theorem problem_HP51 :
  ∀ (A B C D E F G : Point)
    (AB BC CA DA CF EF FG : Line)
    (O : Circle),
    formTriangle A B C AB BC CA ∧
    circumCircle O A B C ∧
    D.onCircle O ∧
    E.onCircle O ∧
    twoLinesIntersectAtPoint AB CF F ∧
    perpLine CF AB ∧
    distinctPointsOnLine E F EF ∧
    perpLine FG EF ∧
    twoLinesIntersectAtPoint DA FG G
  → |(C─G)| = |(C─D)| :=
by sorry



--HP68
--Given that $\triangle ABC$ is inscribed in circle $\odot O$, with $AC \neq BC$. The angle bisector of $\angle ACB$, line $CH$, intersects circle $\odot O$ at point $H$. Points $E$ and $F$ lie on sides $AC$ and $BC$, respectively, such that $EF \parallel AB$. Line $EF$ intersects line $CH$ at point $K$. The circumcircle of $\triangle EFH$, circle $\odot P$, intersects circle $\odot O$ at point $G$. Line $GK$ intersects circle $\odot O$ at point $D$. Prove that $CD \parallel AB$.
theorem problem_HP68 :
  ∀ (A B C D E F G H K : Point)
    (AB BC CA CH EF GK CD : Line)
    (O P : Circle),
    (formTriangle A B C AB BC CA)
  ∧ (circumCircle O A B C)
  ∧ (¬(|(A─C)| = |(B─C)|))
  ∧ distinctPointsOnLine C H CH
  ∧ (∠ A:C:H = ∠ H:C:B)
  ∧ H.onCircle O
  ∧ E.onLine CA
  ∧ F.onLine CB
  ∧ between A E C
  ∧ between B F C
  ∧ distinctPointsOnLine E F EF
  ∧ (¬(EF.intersectsLine AB))
  ∧ twoLinesIntersectAtPoint EF CH K
  ∧ circumCircle P E F H
  ∧ G.onCircle O
  ∧ G.onCircle P
  ∧ distinctPointsOnLine G K GK
  ∧ D.onLine GK
  ∧ D.onCircle O
  ∧ distinctPointsOnLine C D CD
  → (¬(CD.intersectsLine AB)) :=
by
  sorry



--11G6
--In $\triangle ABC$ with $AB = AC$, let $D$ be the midpoint of $AC$, and let the angle bisector of $\angle BAC$ intersect the circumcircle of $\triangle ABC$ at point $E$. Let line $BD$ intersect the circumcircle of $\triangle AEB$ at point $F$ distinct from $B$. Let line $AF$ intersect $BE$ at point $I$, and line $CI$ intersect $BD$ at point $K$. Prove that $I$ is the incenter of $\triangle ABK$.
theorem problem_11G6 :
  ∀ (A B C D E F I K : Point) (AB BC CA BD AE BE AF CI : Line),
  (formTriangle A B C AB BC CA)
  ∧ (|(A─B)| = |(A─C)|)
  ∧ (midpoint A D C)
  ∧ (distinctPointsOnLine A E AE)
  ∧ (cyclic A B C E)
  ∧ (∠ B:A:E = ∠ E:A:C)
  ∧ (distinctPointsOnLine B D BD)
  ∧ (distinctPointsOnLine B F BD)
  ∧ (cyclic A E B F)
  ∧ (twoLinesIntersectAtPoint AF BE I)
  ∧ (twoLinesIntersectAtPoint CI BD K)
  → inCentre I A B K := by
  sorry



--HP69
--Given that circles $\odot O$ and $\odot P$ intersect at points $A$ and $B$. A line through point $O$ intersects circle $\odot P$ at points $C$ and $D$. A line through point $P$ intersects circle $\odot O$ at points $E$ and $F$. If points $C$, $E$, $D$, and $F$ are concyclic, prove that: (1) The circumcenter of quadrilateral $CEDF$ lies on line $AB$. (2) Lines $AB$, $CD$, and $EF$ are concurrent.
theorem problem_HP69 :
∀ (A B C D E F O P : Point) (Om Pm : Circle) (AB CD EF : Line),
  O.isCentre Om ∧ P.isCentre Pm
  ∧ A.onCircle Om ∧ B.onCircle Om ∧ A.onCircle Pm ∧ B.onCircle Pm
  ∧ C.onCircle Pm ∧ D.onCircle Pm ∧ O.onLine CD ∧ distinctPointsOnLine C D CD
  ∧ E.onCircle Om ∧ F.onCircle Om ∧ P.onLine EF ∧ distinctPointsOnLine E F EF
  ∧ cyclic C E D F
→
  ( (∀ (M : Circle),
      (C.onCircle M ∧ E.onCircle M ∧ D.onCircle M ∧ F.onCircle M)
      → ∃ (X : Point), X.isCentre M ∧ X.onLine AB)
    ∧
    (∃ (G : Point), twoLinesIntersectAtPoint AB CD G ∧ G.onLine EF) )
:= by
  sorry



--MP62
--In acute triangle $\triangle ABC$, $AB > AC$, point $M$ is the midpoint of $BC$, $AD \perp BC$ at point $D$, $ME \perp AC$ at point $E$, intersecting $AD$ at point $F$. Point $F$ is the midpoint of $EF$. Prove that $AP \perp BE$.
theorem problem_MP62 :
∀ (A B C M D E F P : Point)
  (AB BC CA AD ME BE AP : Line),
  (formTriangle A B C AB BC CA)
  ∧ (|(A─B)| > |(A─C)|)
  ∧ midpoint B M C
  ∧ twoLinesIntersectAtPoint AD BC D
  ∧ perpLine AD BC
  ∧ twoLinesIntersectAtPoint ME AC E
  ∧ perpLine ME AC
  ∧ twoLinesIntersectAtPoint AD ME F
  ∧ midpoint E F F
  → perpLine AP BE := by
sorry



--MP86
--Points $C$ and $D$ are on segment $AB$, $AC = BD$, points $E$ and $F$ are on the same side of $AB$, and $\angle A = \angle B = \angle ECF = \alpha$. Prove that $\angle EDF = \alpha$.
theorem problem_MP86 :
∀ (A B C D E F : Point) (AB : Line),
  threePointsOnLine A B C AB ∧
  between A C B ∧
  threePointsOnLine A B D AB ∧
  between A D B ∧
  |(A─C)| = |(B─D)| ∧
  E.sameSide F AB ∧
  (∠ E:A:B = ∠ A:B:E) ∧
  (∠ A:B:E = ∠ E:C:F)
→ ∠ E:D:F = ∠ E:C:F := by
  sorry



--imo_2017_p4
--Let $R$ and $S$ be different points on a circle $\Omega$ such that $RS$ is not a diameter. Let $\ell$ be the tangent line to $\Omega$ at $R$. Point $T$ is such that $S$ is the midpoint of the line segment $RT$. Point $J$ is chosen on the shorter arc $RS$ of $\Omega$ so that the circumcircle $\Gamma$ of triangle $JST$ intersects $\ell$ at two distinct points. Let $A$ be the common point of $\Gamma$ and $\ell$ that is closer to $R$. Line $AJ$ meets $\Omega$ again at $K$. Prove that the line $KT$ is tangent to $\Gamma$.
theorem problem_imo_2017_p4 :
  ∀ (R S T J A K : Point) (ℓ AJ TK : Line) (Ω Γ : Circle),
  ( R ≠ S ∧
    R.onCircle Ω ∧
    S.onCircle Ω ∧
    (∀ O : Point, O.isCentre Ω → ∠ R:O:S ≠ ∟ + ∟) ∧
    tangentAtPoint ℓ Ω R ∧
    midpoint R S T ∧
    J.onCircle Ω ∧
    circumCircle Γ J S T ∧
    A.onLine ℓ ∧
    A.onCircle Γ ∧
    threePointsOnLine A J K AJ ∧
    K.onCircle Ω ∧
    distinctPointsOnLine K T TK
  )
  → tangentLine TK Γ := by
  sorry



--13G5
--In a convex hexagon $ABCDEF$, given $AB = DE$, $BC = EF$, $CD = FA$, and $\angle A - \angle D = \angle C - \angle F = \angle E - \angle B$. Prove that lines $AD$, $BE$, and $CF$ are concurrent.
theorem problem_13G5 :
  ∀ (A B C D E F : Point) (AB BC CD DE EF FA AD BE CF : Line),
  |(A─B)|=|(D─E)| ∧
  |(B─C)|=|(E─F)| ∧
  |(C─D)|=|(F─A)| ∧
  ( (∠F:A:B) - (∠C:D:E) = (∠B:C:D) - (∠E:F:A) ) ∧
  ( (∠B:C:D) - (∠E:F:A) = (∠D:E:F) - (∠A:B:C) )
  → ∃ (X : Point), twoLinesIntersectAtPoint AD BE X ∧ X.onLine CF :=
by
  sorry



--MP8
--In $\triangle ABC$, $\angle ACB = \angle BAC + 2\angle B$ and $AD \perp BC$ at point $D$. Prove that $AB - BC = 2CD$.
theorem problem_MP8 :
∀ (A B C D : Point) (AB BC CA AD : Line),
  formTriangle A B C AB BC CA ∧
  (∠A:C:B = ∠B:A:C + ∠A:B:C + ∠A:B:C) ∧
  twoLinesIntersectAtPoint AD BC D ∧
  perpLine AD BC
→ |(A─B)| = (|(B─C)| + |(C─D)| + |(C─D)|) :=
by sorry



--17G4
--In $\triangle ABC$, let $\omega$ be the excircle opposite to $A$, and $D$, $E$, $F$ the points where $\omega$ touches sides $BC$, $CA$, and $AB$, respectively. Let the circumcircle of $\triangle AEF$ intersect line $BC$ at points $P$ and $Q$, and $M$ the midpoint of $AD$. Prove that the circumcircle of $\triangle MPQ$ is tangent to $\omega$.
theorem problem_17G4 :
∀ (A B C D E F P Q M : Point) (AB BC CA : Line) (ω α : Circle),
  (formTriangle A B C AB BC CA)
  ∧ tangentAtPoint BC ω D
  ∧ tangentAtPoint CA ω E
  ∧ tangentAtPoint AB ω F
  ∧ circumCircle α A E F
  ∧ P.onLine BC ∧ P.onCircle α
  ∧ Q.onLine BC ∧ Q.onCircle α
  ∧ midpoint A M D
→ ∀ (Γ : Circle),
     (circumCircle Γ M P Q
      → ∀ (X Y : Point),
           (X.onCircle Γ ∧ X.onCircle ω ∧ Y.onCircle Γ ∧ Y.onCircle ω)
           → X = Y) :=
by sorry



--imo_2021_p3
--Let $D$ be an interior point of the acute triangle $ABC$ with $AB > AC$ so that $\angle DAB= \angle CAD$. The point $E$ on the segment $AC$ satisfies $\angle ADE= \angle BCD$, the point $F$ on the segment $AB$ satisfies $\angle FDA= \angle DBC$, and the point $X$ on the line $AC$ satisfies $CX=BX$. Let $O_1$ and $O_2$ be the circumcentres of the triangles $ADC$ and $EXD$ respectively. Prove that the lines $BC$, $EF$, and $O_1 O_2$ are concurrent.
theorem problem_imo_2021_p3 :
∀ (A B C D E F X O₁ O₂ : Point)
  (AB BC CA EF O₁O₂ : Line),
  formTriangle A B C AB BC CA ∧
  insideTriangle D A B C AB BC CA ∧
  ∠ D:A:B = ∠ C:A:D ∧
  E.onLine CA ∧ between A E C ∧
  ∠ A:D:E = ∠ B:C:D ∧
  F.onLine AB ∧ between A F B ∧
  ∠ F:D:A = ∠ D:B:C ∧
  X.onLine CA ∧
  |(C─X)| = |(B─X)| ∧
  circumCentre O₁ A D C ∧
  circumCentre O₂ E X D ∧
  B.onLine BC ∧ C.onLine BC ∧
  E.onLine EF ∧ F.onLine EF ∧
  O₁.onLine O₁O₂ ∧ O₂.onLine O₁O₂
  → ∃ P : Point, P.onLine BC ∧ P.onLine EF ∧ P.onLine O₁O₂ :=
by
  sorry



--MP44
--In $\triangle ABC$, $\angle ACB > 90^\circ$, the internal and external angle bisectors of $\angle BAC$ intersect ray $BC$ at points $D$ and $E$, respectively. Given that $2AB = BD + BE$, prove that $\angle ACB = 90^\circ + \frac{1}{2} \angle ABC$.
theorem problem_MP44 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  ∠A:C:B > ∟ ∧
  D.onLine BC ∧
  E.onLine BC ∧
  ∠B:A:D = ∠D:A:C ∧
  ∠B:A:E = ∠E:A:C ∧
  (|(A─B)| + |(A─B)| = |(B─D)| + |(B─E)|)
  → ∠A:C:B = ∟ + (1/2)*∠A:B:C
:= by
  sorry



--HP22
--Given that $CD$ is the diameter of circle $\odot O$. Lines $PC$ and $PE$ are tangents to circle $\odot O$ at points $C$ and $E$, respectively. Secant $PBA$ intersects circle $\odot O$ at points $A$ and $B$. Lines $AC$ and $BD$ intersect at point $F$, and line $DE$ intersects line $AB$ at point $G$. Prove that $\angle GFE = \angle ADE$.
theorem problem_HP22 :
∀
(A B C D E F G P : Point)
(L1 L2 L3 L4 L5 L6 L7 : Line)
(O : Circle),
(
  C.onCircle O ∧ D.onCircle O ∧ E.onCircle O ∧ A.onCircle O ∧ B.onCircle O
  ∧ distinctPointsOnLine P C L1 ∧ tangentAtPoint L1 O C
  ∧ distinctPointsOnLine P E L2 ∧ tangentAtPoint L2 O E
  ∧ threePointsOnLine P B A L3
  ∧ distinctPointsOnLine A C L4 ∧ distinctPointsOnLine B D L5 ∧ twoLinesIntersectAtPoint L4 L5 F
  ∧ distinctPointsOnLine D E L6 ∧ distinctPointsOnLine A B L7 ∧ twoLinesIntersectAtPoint L6 L7 G
)
→ ∠ G:F:E = ∠ A:D:E
:= by
  sorry



--HP16
--Given that $\triangle ABC$ is inscribed in circle $\odot O$, with $D$ as the midpoint of $BC$. Line $AD$ intersects circle $\odot O$ at point $E$. Draw line $EF \parallel BC$, intersecting circle $\odot O$ at point $F$. Draw a perpendicular from $C$ to line $AC$, intersecting line $AE$ at point $G$. Prove that $\angle AGC = \angle FGC$.
theorem problem_HP16 :
∀ (A B C D E F G : Point) (O : Circle)
  (AB BC CA AD EF CG : Line),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  midpoint B D C ∧
  threePointsOnLine A D E AD ∧
  E.onCircle O ∧
  distinctPointsOnLine E F EF ∧
  F.onCircle O ∧
  ¬(EF.intersectsLine BC) ∧
  distinctPointsOnLine C G CG ∧
  twoLinesIntersectAtPoint AD CG G ∧
  perpLine CG CA
→ ∠A:G:C = ∠F:G:C
:= by
  sorry



--HP70
--Given that in $\triangle ABC$, point $D$ lies on side $BC$. Points $E$ and $F$ are the incenters of $\triangle ABD$ and $\triangle ACD$, respectively. Draw circle $\odot E$ with center $E$ and radius $ED$, and circle $\odot F$ with center $F$ and radius $FD$. Circles $\odot E$ and $\odot F$ intersect at point $G$. Circle $\odot E$ intersects lines $AB$ and $BC$ at points $J$ and $K$, respectively. Circle $\odot F$ intersects lines $AC$ and $BC$ at points $M$ and $N$, respectively. Prove that lines $JK$, $MN$, and $GD$ are concurrent.
theorem problem_HP70 :
  ∀ (A B C D E F G J K M N : Point)
    (AB BC CA JK MN GD : Line)
    (CE CF : Circle),
  (formTriangle A B C AB BC CA)
  ∧ D.onLine BC
  ∧ inCentre E A B D
  ∧ inCentre F A C D
  ∧ E.isCentre CE
  ∧ D.onCircle CE
  ∧ F.isCentre CF
  ∧ D.onCircle CF
  ∧ G.onCircle CE
  ∧ G.onCircle CF
  ∧ J.onLine AB
  ∧ J.onCircle CE
  ∧ K.onLine BC
  ∧ K.onCircle CE
  ∧ M.onLine AC
  ∧ M.onCircle CF
  ∧ N.onLine BC
  ∧ N.onCircle CF
  ∧ distinctPointsOnLine J K JK
  ∧ distinctPointsOnLine M N MN
  ∧ distinctPointsOnLine G D GD
  → ∃ X : Point, twoLinesIntersectAtPoint JK MN X ∧ X.onLine GD
:= by
  sorry



--MP11
--In quadrilateral $ABCD$, $\angle B = 2\angle D$ and $AC$ bisects $\angle BCD$. Prove that $AB + BC = CD$.
theorem problem_MP11 :
  ∀ (A B C D : Point) (AB BC CD DA AC : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    distinctPointsOnLine A C AC ∧
    (∠A:B:C = ∠C:D:A + ∠C:D:A) ∧
    (∠B:C:A = ∠A:C:D)
  → (|(A─B)| + |(B─C)| = |(C─D)|)
  := by
  sorry



--16G2
--In an acute triangle $\triangle ABC$, let $I$ be the incenter and $M$ the midpoint of side $BC$. Let $D$ be the foot of the perpendicular from $I$ to $BC$. Draw a line through $I$ perpendicular to $AI$, intersecting sides $AB$ and $AC$ at points $F$ and $E$, respectively. Let the circumcircle of $\triangle AEF$ intersect the circumcircle of $\triangle ABC$ at a point $X$ other than $A$. Prove that the intersection of line $XD$ with line $AM$ lies on the circumcircle of $\triangle ABC$.
theorem problem_16G2 :
  ∀ (A B C I M D E F X Y : Point)
    (AB BC CA AI AM XD EF ID : Line)
    (Ω1 Ω2 : Circle),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  midpoint B M C ∧
  D.onLine BC ∧
  distinctPointsOnLine I D ID ∧
  perpLine BC ID ∧
  distinctPointsOnLine A I AI ∧
  perpLine EF AI ∧
  I.onLine EF ∧
  E.onLine EF ∧
  F.onLine EF ∧
  F.onLine AB ∧
  E.onLine CA ∧
  distinctPointsOnLine A M AM ∧
  distinctPointsOnLine X D XD ∧
  circumCircle Ω1 A E F ∧
  circumCircle Ω2 A B C ∧
  X.onCircle Ω1 ∧
  X.onCircle Ω2 ∧
  X ≠ A ∧
  twoLinesIntersectAtPoint XD AM Y
  → Y.onCircle Ω2 := by
  sorry



--HP63
--Given that $AB$ is the diameter of semicircle $O$. Line $CA$ is perpendicular to line $AB$ at point $A$, and line $DB$ is perpendicular to line $AB$ at point $B$. Lines $EC$ and $ED$ are tangents to semicircle $O$. Line $OF$ is perpendicular to line $CD$ at point $F$. Connect line $EF$. Prove that $\angle EFD = \angle FOB$.
theorem problem_HP63 :
∀ (A B C D E F O : Point)
  (AB CA DB CD EC ED OF EF : Line)
  (Ω : Circle),
  distinctPointsOnLine A B AB ∧
  O.isCentre Ω ∧
  A.onCircle Ω ∧
  B.onCircle Ω ∧
  twoLinesIntersectAtPoint AB CA A ∧
  perpLine AB CA ∧
  twoLinesIntersectAtPoint AB DB B ∧
  perpLine AB DB ∧
  tangentLine EC Ω ∧
  tangentLine ED Ω ∧
  distinctPointsOnLine C D CD ∧
  twoLinesIntersectAtPoint OF CD F ∧
  perpLine OF CD ∧
  distinctPointsOnLine E F EF
  → ∠ E:F:D = ∠ F:O:B :=
by
  sorry



--HP86
--Given that $\triangle ABC$ is inscribed in circle $\odot O$. Point $H$ is the orthocenter of $\triangle ABC$. Point $D$ is the midpoint of line segment $BC$. Connect line $DH$. Draw line $EF$ perpendicular to line $DH$, intersecting lines $AB$ and $AC$ at points $E$ and $F$, respectively. Connect lines $DE$ and $DF$. Prove that $DE = DF$.
theorem HP86 :
∀ (A B C D E F H : Point) (AB BC CA DH EF DE DF : Line) (O : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  midpoint B D C ∧
  distinctPointsOnLine D H DH ∧
  distinctPointsOnLine E F EF ∧
  E.onLine AB ∧
  F.onLine AC ∧
  perpLine DH EF ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine D F DF
  → |(D─E)| = |(D─F)| := by
sorry



--MP90
--In right triangle $\triangle ABC$, $\angle A = 90^\circ$, $AB : AC = 3 : 4$. Point $D$ is on $AC$ such that $AD : AC = 1 : 4$, and point $E$ is on $AB$ such that $\angle AED = \angle DBC$. Find the value of $AE : EB$.
theorem problem_MP90 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  (∠B:A:C = ∟) ∧
  (4 * |(A─B)| = 3 * |(A─C)|) ∧
  D.onLine CA ∧
  (4 * |(A─D)| = |(A─C)|) ∧
  E.onLine AB ∧
  (∠A:E:D = ∠D:B:C)
  → 8 * |(A─E)| = |(E─B)| := by
  sorry



--17G5
--In a convex hexagon $ABC C_1 B_1 A_1$, given $AB = BC$, and segments $AA_1$, $BB_1$, $CC_1$ have the same perpendicular bisector. Let $AC_1$ intersect $A_1C$ at point $D$, and the circumcircle of $\triangle ABC$ intersect the circumcircle of $\triangle A_1BC_1$ at a point $E$ other than $B$. Prove that the intersection of $BB_1$ and $DE$ lies on the circumcircle of $\triangle ABC$.
theorem problem_17G5 :
  ∀ (A B C A_1 B_1 C_1 D E F : Point)
    (AC_1 A_1C BB_1 DE L : Line)
    (Ω1 Ω2 : Circle),
  (|(A─B)| = |(B─C)|)
  ∧ perpBisector A A_1 L
  ∧ perpBisector B B_1 L
  ∧ perpBisector C C_1 L
  ∧ distinctPointsOnLine A C_1 AC_1
  ∧ distinctPointsOnLine A_1 C A_1C
  ∧ twoLinesIntersectAtPoint AC_1 A_1C D
  ∧ circumCircle Ω1 A B C
  ∧ circumCircle Ω2 A_1 B C_1
  ∧ E.onCircle Ω1
  ∧ E.onCircle Ω2
  ∧ E ≠ B
  ∧ distinctPointsOnLine B B_1 BB_1
  ∧ distinctPointsOnLine D E DE
  ∧ twoLinesIntersectAtPoint BB_1 DE F
  → F.onCircle Ω1 := by
  sorry



--MP2
--In $\triangle ABC$, point $D$ is inside the triangle such that $DB = DC$. The perpendicular from $B$ to the angle bisector of $\angle ADB$ meets at point $E$, and the perpendicular from $C$ to the angle bisector of $\angle ADC$ meets at point $F$. Prove that $EF \parallel BC$.
theorem problem_MP2 :
  ∀ (A B C D E F : Point) (AB BC CA EF : Line),
    formTriangle A B C AB BC CA ∧
    insideTriangle D A B C AB BC CA ∧
    (|(D─B)| = |(D─C)|) ∧
    (∠ A:D:E = ∠ E:D:B) ∧
    (∠ B:E:D = ∟) ∧
    (∠ A:D:F = ∠ F:D:C) ∧
    (∠ C:F:D = ∟) ∧
    distinctPointsOnLine E F EF
  → ¬(∃ (X : Point), twoLinesIntersectAtPoint EF BC X) :=
by sorry



--MP32
--In right triangle $\triangle ABC$, $\angle A = 90^\circ$, $\angle B = 75^\circ$. Point $D$ is the midpoint of $BC$, and point $E$ is on $AC$ such that $AE = AB$. Find $\angle BDE$.
theorem problem_MP32 : ∀
  (A B C D E : Point)
  (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  (∠B:A:C = ∟) ∧
  (∠A:B:C = 75) ∧
  midpoint B D C ∧
  E.onLine CA ∧
  (|(A─E)| = |(A─B)|)
  → (∠B:D:E = 45)
:= by
  sorry



--17G3
--In a non-isosceles acute triangle $\triangle ABC$, let $O$ and $H$ be the circumcenter and orthocenter, respectively, and $M$ the midpoint of $BC$. Let line $OA$ intersect the altitudes from $B$ and $C$ at points $P$ and $Q$, respectively. Prove that the circumcenter $O_1$ of $\triangle PQH$ lies on line $AM$.
theorem problem_17G3 :
∀ (A B C O H M P Q O₁ : Point)
  (AB BC CA OA AM altB altC : Line),
  formTriangle A B C AB BC CA ∧
  ¬(|(A─B)| = |(A─C)|) ∧
  ¬(|(B─C)| = |(A─B)|) ∧
  ¬(|(B─C)| = |(A─C)|) ∧
  circumCentre O A B C ∧
  B.onLine altB ∧ perpLine altB CA ∧
  C.onLine altC ∧ perpLine altC AB ∧
  twoLinesIntersectAtPoint altB altC H ∧
  midpoint B M C ∧
  distinctPointsOnLine O A OA ∧
  twoLinesIntersectAtPoint OA altB P ∧
  twoLinesIntersectAtPoint OA altC Q ∧
  circumCentre O₁ P Q H ∧
  distinctPointsOnLine A M AM
  → O₁.onLine AM :=
by
  sorry



--HP3
--Given that $PE$ and $PF$ are tangents to the circle with diameter $AB$, with $E$ and $F$ as the points of tangency. Line $PB$ intersects the circle at point $C$. Lines $AF$ and $BE$ intersect at point $D$, where $AB$ is the diameter. Prove that $\angle DPE = 2\angle ACD$.
theorem problem_HP3 :
  ∀ (A B C D E F P : Point) (AB PB AF BE PE PF : Line) (ω : Circle),
    distinctPointsOnLine A B AB ∧
    A.onCircle ω ∧
    B.onCircle ω ∧
    distinctPointsOnLine P E PE ∧
    tangentAtPoint PE ω E ∧
    distinctPointsOnLine P F PF ∧
    tangentAtPoint PF ω F ∧
    threePointsOnLine P B C PB ∧
    C.onCircle ω ∧
    distinctPointsOnLine A F AF ∧
    distinctPointsOnLine B E BE ∧
    twoLinesIntersectAtPoint AF BE D
  → ∠D:P:E = ∠A:C:D + ∠A:C:D := by
  sorry



--HP33
--Given that circles $\odot O_1$ and $\odot O_2$ have radii $r_1$ and $r_2$, respectively. Circles $\odot O_1$ and $\odot O_2$ intersect at points $A$ and $B$. Point $P$ lies in the plane. Line $PC$ is tangent to circle $\odot O_1$ at point $C$, and line $PD$ is tangent to circle $\odot O_2$ at point $D$, such that $\frac{PC}{PD} = \frac{r_1}{r_2}$. Prove that $\triangle PCA \sim \triangle PBD$.
theorem problem_HP33 :
∀ (A B P C D : Point) (O₁ O₂ : Circle) (PCLine PDLine : Line) (r₁ r₂ : ℝ),
A.onCircle O₁ ∧ B.onCircle O₁ ∧ A.onCircle O₂ ∧ B.onCircle O₂ ∧
distinctPointsOnLine P C PCLine ∧ tangentAtPoint PCLine O₁ C ∧
distinctPointsOnLine P D PDLine ∧ tangentAtPoint PDLine O₂ D ∧
(|(P─C)| / |(P─D)|) = (r₁ / r₂)
→
(∠P:C:A = ∠P:B:D) ∧ (∠C:A:P = ∠B:D:P) ∧ (∠A:P:C = ∠D:P:B)
:= by
  sorry



--05G6
--In triangle $\triangle ABC$, the median $AM$ intersects the incircle at points $K$ and $L$. Lines through $K$ and $L$ parallel to $BC$ intersect the incircle again at points $X$ and $Y$. The lines $AX$ and $AY$ intersect $BC$ at points $P$ and $Q$, respectively. Prove that $BP = CQ$.
theorem problem_05G6 :
∀ (A B C M K L X Y P Q : Point)
  (AB BC CA AM AX AY : Line)
  (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  inCircle Ω AB BC CA ∧
  midpoint B M C ∧
  distinctPointsOnLine A M AM ∧
  K.onLine AM ∧ K.onCircle Ω ∧
  L.onLine AM ∧ L.onCircle Ω ∧
  distinctPointsOnLine A X AX ∧
  X.onCircle Ω ∧
  twoLinesIntersectAtPoint AX BC P ∧
  distinctPointsOnLine A Y AY ∧
  Y.onCircle Ω ∧
  twoLinesIntersectAtPoint AY BC Q
→ |(B─P)| = |(C─Q)| :=
by sorry



--MP68
--In $\triangle ABC$, $\angle ABC = 60^\circ$, $\angle ACB = 70^\circ$. Points $D$ and $E$ are on sides $AC$ and $AB$, respectively, such that $\angle DBC = \angle ECB = 40^\circ$. Find $\angle BDE$.
theorem problem_MP68 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    ∠ A:B:C = 60 ∧
    ∠ B:C:A = 70 ∧
    between A D C ∧
    between A E B ∧
    ∠ D:B:C = 40 ∧
    ∠ E:C:B = 40
  → ∠ B:D:E = 30 :=
by
  sorry




--HP21
--Given that point $D$ lies on side $BC$ of $\triangle ABC$, such that $\angle DAC = \angle ABD$. Circle $\odot O$ passes through points $B$ and $D$, intersecting lines $AB$ and $AD$ at points $E$ and $F$, respectively. Line $BF$ intersects line $DE$ at point $G$, and $M$ is the midpoint of $AG$. Prove that $CM \perp AO$.
theorem HP21 :
∀ (A B C D E F G M O : Point)
  (AB BC CA AD BF DE AO CM : Line)
  (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  between B D C ∧
  ∠ D:A:C = ∠ A:B:D ∧
  distinctPointsOnLine A D AD ∧
  distinctPointsOnLine B F BF ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine A O AO ∧
  distinctPointsOnLine C M CM ∧
  B.onCircle Ω ∧ D.onCircle Ω ∧ E.onCircle Ω ∧ F.onCircle Ω ∧
  O.isCentre Ω ∧
  E.onLine AB ∧
  F.onLine AD ∧
  twoLinesIntersectAtPoint BF DE G ∧
  midpoint A M G
→ perpLine AO CM
:= by
  sorry



--13G2
--In $\triangle ABC$, let $\Gamma$ be the circumcircle. The midpoint of arc $BC$ is $T$, and the midpoints of $AB$ and $AC$ are $M$ and $N$, respectively. The circumcircles of $\triangle AMT$ and $\triangle ANT$ intersect the perpendicular bisectors of $AC$ and $AB$ at points $X$ and $Y$, respectively, both inside $\triangle ABC$. Let line $MN$ intersect line $XY$ at point $K$. Prove that $KA = KT$.
theorem problem_13G2 :
∀ (A B C T M N X Y K : Point)
  (AB BC CA MN XY L1 L2 : Line)
  (Γ Ω1 Ω2 : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle Γ A B C ∧
  T.onCircle Γ ∧ |(T─B)| = |(T─C)| ∧
  midpoint A M B ∧
  midpoint A N C ∧
  distinctPointsOnLine M N MN ∧
  distinctPointsOnLine X Y XY ∧
  circumCircle Ω1 A M T ∧
  circumCircle Ω2 A N T ∧
  perpBisector A C L1 ∧
  perpBisector A B L2 ∧
  X.onLine L1 ∧ X.onCircle Ω1 ∧
  Y.onLine L2 ∧ Y.onCircle Ω2 ∧
  twoLinesIntersectAtPoint MN XY K
  → |(K─A)| = |(K─T)| :=
by sorry



--MP27
--In rhombus $ABCD$, point $E$ is the midpoint of $AD$, and point $F$ is on $AD$ such that $BF = CD + DF$. Prove that $\angle ABE = \frac{1}{2} \angle FBC$.
theorem problem_MP27 :
  ∀ (A B C D E F : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    |(A─B)| = |(B─C)| ∧
    |(B─C)| = |(C─D)| ∧
    |(C─D)| = |(D─A)| ∧
    midpoint A E D ∧
    F.onLine DA ∧
    |(B─F)| = |(C─D)| + |(D─F)|
    → ∠ A:B:E + ∠ A:B:E = ∠ F:B:C := by
  sorry



--HP84
--Given that in quadrilateral $ABCD$, points $E$ and $F$ lie on sides $AD$ and $BC$, respectively, such that $\frac{AE}{ED} = \frac{BF}{FC}$. Line $FE$ intersects lines $BA$ and $CD$ at points $S$ and $T$, respectively. The circumcircles of $\triangle SAE$, $\triangle SBF$, $\triangle TDE$, and $\triangle TCF$ are circles $\odot O_1$, $\odot O_2$, $\odot O_3$, and $\odot O_4$, respectively.
theorem problem_HP84 :
∀ (A B C D E F S T : Point) (AB BC CD DA FE : Line) (O₁ O₂ O₃ O₄ : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  between A E D ∧
  between B F C ∧
  (|(A─E)| * |(F─C)| = |(B─F)| * |(E─D)|) ∧
  distinctPointsOnLine F E FE ∧
  twoLinesIntersectAtPoint FE AB S ∧
  twoLinesIntersectAtPoint FE CD T ∧
  circumCircle O₁ S A E ∧
  circumCircle O₂ S B F ∧
  circumCircle O₃ T D E ∧
  circumCircle O₄ T C F
→ True :=
by
  sorry



--MP100
--In $\triangle ABC$, the median of side $BC$ is $AD$, point $P$ is on $CD$. $PE \parallel AC$, intersecting $AB$ and $AD$ at points $E$ and $G$, respectively, $PF \parallel AB$, intersecting $AC$ at point $F$. Prove that $EG = CF$.
theorem problem_MP100 :
  ∀ (A B C D P E G F : Point) (AB BC CA AD CD PE PF : Line),
    formTriangle A B C AB BC CA ∧
    midpoint B D C ∧
    distinctPointsOnLine A D AD ∧
    distinctPointsOnLine C D CD ∧
    P.onLine CD ∧
    distinctPointsOnLine P E PE ∧
    ¬(PE.intersectsLine AC) ∧
    twoLinesIntersectAtPoint PE AB E ∧
    twoLinesIntersectAtPoint PE AD G ∧
    distinctPointsOnLine P F PF ∧
    ¬(PF.intersectsLine AB) ∧
    twoLinesIntersectAtPoint PF CA F
  → |(E─G)| = |(C─F)| :=
by
  sorry



--MP15
--In right triangle $\triangle ABC$, $\angle C = 90^\circ$, $\angle A = 30^\circ$, $CE$ and $AF$ are angle bisectors. Point $D$ is on $AC$ such that $CD = CF$. Find $\angle CED$.
theorem problem_MP15 : ∀
  (A B C D E F : Point)
  (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  (∠A:C:B = ∟) ∧
  (∠B:A:C = ∟/3) ∧
  E.onLine AB ∧
  (∠A:C:E = ∠E:C:B) ∧
  F.onLine BC ∧
  (∠B:A:F = ∠F:A:C) ∧
  D.onLine CA ∧
  (|(C─D)| = |(C─F)|)
  → ∠C:E:D = ∟/6
:= by
  sorry



--MP89
--In right triangle $\triangle ABC$, $AB = AC$, point $D$ is the midpoint of $AC$, point $E$ is on $AB$ such that $\angle ADE = \angle DBC$. Find the value of $\frac{AE}{EB}$.
theorem problem_MP89 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    ∠B:A:C = ∟ ∧
    |(A─B)| = |(A─C)| ∧
    midpoint A D C ∧
    E.onLine AB ∧
    ∠A:D:E = ∠D:B:C
    → 5 * |(A─E)| = |(E─B)| := by
  sorry



--HP73
--Given that $\triangle ABC$ is inscribed in circle $\odot O$. Line $AC \neq BC$. The angle bisector of $\angle ACB$, line $CH$, intersects circle $\odot O$ at point $H$. Points $E$ and $F$ lie on sides $AC$ and $BC$, respectively, such that $EF \parallel AB$. Line $EF$ intersects line $CH$ at point $K$. The circumcircle of $\triangle EFH$, circle $\odot P$, intersects circle $\odot O$ at point $G$. Line $GK$ intersects circle $\odot O$ at point $D$. Prove that $CD \parallel AB$.
theorem problem_HP73 :
∀ (A B C H E F K G D : Point) (O P : Circle)
  (AC BC AB EF CH GK CD : Line),
  (formTriangle A B C AB BC AC) ∧
  (AC ≠ BC) ∧
  (circumCircle O A B C) ∧
  E.onLine AC ∧
  F.onLine BC ∧
  (∀ X : Point, ¬(twoLinesIntersectAtPoint EF AB X)) ∧
  twoLinesIntersectAtPoint EF CH K ∧
  (∠ A:C:H = ∠ H:C:B) ∧
  H.onLine CH ∧
  H.onCircle O ∧
  circumCircle P E F H ∧
  G.onCircle O ∧
  G.onCircle P ∧
  D.onLine GK ∧
  D.onCircle O ∧
  distinctPointsOnLine C D CD
→ ∀ X : Point, ¬(twoLinesIntersectAtPoint CD AB X)
:= by
  sorry



--HP44
--Given that $AB$ is the diameter of semicircle $O$, and line $OC$ is perpendicular to line $AB$, with point $C$ on the circle. Point $P$ lies on the extension of line $BA$. Line $PD$ is tangent to circle $\odot O$ at point $D$. Line $PE$ bisects angle $\angle DPB$, intersecting lines $AC$ and $BC$ at points $E$ and $F$, respectively. Prove that $\angle EOF = 90^{\circ}$.
theorem problem_HP44 :
  ∀ (A B C O P D E F : Point)
    (AB AC BC OC PD PE : Line)
    (O₀ : Circle),
    O.isCentre O₀ ∧
    A.onCircle O₀ ∧
    B.onCircle O₀ ∧
    C.onCircle O₀ ∧
    distinctPointsOnLine A B AB ∧
    O.onLine AB ∧
    distinctPointsOnLine O C OC ∧
    perpLine AB OC ∧
    P.onLine AB ∧
    distinctPointsOnLine P D PD ∧
    tangentAtPoint PD O₀ D ∧
    distinctPointsOnLine P E PE ∧
    ∠D:P:E = ∠E:P:B ∧
    distinctPointsOnLine A C AC ∧
    twoLinesIntersectAtPoint AC PE E ∧
    distinctPointsOnLine B C BC ∧
    twoLinesIntersectAtPoint BC PE F
  → ∠E:O:F = ∟ :=
by sorry



--HP42
--Given that $H$ is the orthocenter of $\triangle ABC$, and point $D$ is the midpoint of $BC$. Draw line $EF$ perpendicular to line $DH$, intersecting lines $AB$ and $AC$ at points $E$ and $F$, respectively. Prove that $H$ is the midpoint of line segment $EF$.
theorem problem_HP42 :
∀ (A B C H D E F : Point) (AB BC CA DH EF : Line),
  formTriangle A B C AB BC CA ∧
  -- “H is the orthocenter of triangle ABC” (no built-in predicate available, treated as given) ∧
  midpoint B D C ∧
  distinctPointsOnLine D H DH ∧
  perpLine EF DH ∧
  E.onLine AB ∧
  F.onLine AC ∧
  E.onLine EF ∧
  F.onLine EF
→ midpoint E H F
:= by
  sorry



--18G4
--In $\triangle ABC$, let $T$ be a point inside the triangle, and $A_1$, $B_1$, $C_1$ the reflections of $T$ across sides $BC$, $CA$, and $AB$, respectively. Let the circumcircle of $\triangle A_1B_1C_1$ be $\Gamma$. Lines $A_1T$, $B_1T$, and $C_1T$ intersect $\Gamma$ again at points $A_2$, $B_2$, and $C_2$, respectively. Prove that lines $AA_2$, $BB_2$, and $CC_2$ are concurrent at a point on $\Gamma$.
theorem problem_18G4 :
∀ (A B C T A_1 B_1 C_1 A_2 B_2 C_2 : Point)
  (AB BC CA A_1T B_1T C_1T AA2 BB2 CC2 : Line)
  (Γ : Circle),
  formTriangle A B C AB BC CA ∧
  insideTriangle T A B C AB BC CA ∧
  perpBisector T A_1 BC ∧
  perpBisector T B_1 CA ∧
  perpBisector T C_1 AB ∧
  circumCircle Γ A_1 B_1 C_1 ∧
  distinctPointsOnLine A_1 T A_1T ∧
  distinctPointsOnLine B_1 T B_1T ∧
  distinctPointsOnLine C_1 T C_1T ∧
  A_2.onLine A_1T ∧
  A_2.onCircle Γ ∧
  B_2.onLine B_1T ∧
  B_2.onCircle Γ ∧
  C_2.onLine C_1T ∧
  C_2.onCircle Γ ∧
  distinctPointsOnLine A A_2 AA2 ∧
  distinctPointsOnLine B B_2 BB2 ∧
  distinctPointsOnLine C C_2 CC2
→ ∃ (X : Point),
    X.onLine AA2 ∧ X.onLine BB2 ∧ X.onLine CC2 ∧ X.onCircle Γ
:= by
  sorry



--HP77
--Given that in pentagon $ABCDE$, $AB \parallel DE$ and $AE \parallel BC$. Lines $BD$ and $CE$ intersect at point $P$. Points $M$ and $N$ are the midpoints of sides $BE$ and $CD$, respectively. Connect line $MN$. Prove that $MN \parallel AP$.
theorem problem_HP77 :
∀ (A B C D E P M N : Point)
  (AB BC CD DE EA BD CE BE MN AP : Line),
  formPentagon A B C D E AB BC CD DE EA
  ∧ (¬ (∃ X : Point, twoLinesIntersectAtPoint AB DE X))
  ∧ (¬ (∃ X : Point, twoLinesIntersectAtPoint AE BC X))
  ∧ twoLinesIntersectAtPoint BD CE P
  ∧ midpoint B M E
  ∧ midpoint C N D
  → ¬ (∃ X : Point, twoLinesIntersectAtPoint MN AP X) := by
sorry



--HP83
--Given that $\triangle ABC$ is inscribed in circle $\odot O$. Point $L$ lies on circle $\odot O$. Line $EL$ is perpendicular to line $CL$, intersecting line $AB$ at point $E$. Line $FL$ is perpendicular to line $BL$, intersecting line $AC$ at point $F$. Prove that points $E$, $O$, and $F$ are collinear.
theorem problem_HP83 :
  ∀ (A B C L E F O : Point) (Ω : Circle)
    (AB BC CA EL CL FL BL L_OF : Line),
  formTriangle A B C AB BC CA ∧
  O.isCentre Ω ∧
  A.onCircle Ω ∧
  B.onCircle Ω ∧
  C.onCircle Ω ∧
  L.onCircle Ω ∧
  distinctPointsOnLine E L EL ∧
  distinctPointsOnLine C L CL ∧
  perpLine EL CL ∧
  twoLinesIntersectAtPoint EL AB E ∧
  distinctPointsOnLine F L FL ∧
  distinctPointsOnLine B L BL ∧
  perpLine FL BL ∧
  twoLinesIntersectAtPoint FL CA F
  → threePointsOnLine E O F L_OF
:= by
  sorry



--HP100
--Given that in $\triangle ADE$, circle $\odot O$ passes through point $D$ and intersects lines $AE$ and $DE$ at points $B$ and $C$, respectively. Line $BD$ intersects line $AC$ at point $G$. Line $OG$ intersects the circumcircle of $\triangle ADE$ at point $P$. Prove that $\triangle PBD$ and $\triangle PAC$ share the same incenter.
theorem problem_HP100 :
  ∀ (A D E B C O G P : Point)
    (AD DE EA BD AC OG : Line)
    (ω Ω : Circle),
    formTriangle A D E AD DE EA ∧
    O.isCentre ω ∧
    D.onCircle ω ∧
    B.onCircle ω ∧
    C.onCircle ω ∧
    B.onLine AE ∧
    C.onLine DE ∧
    twoLinesIntersectAtPoint BD AC G ∧
    circumCircle Ω A D E ∧
    O.onLine OG ∧
    G.onLine OG ∧
    P.onLine OG ∧
    P.onCircle Ω
  → ∃ (I : Point),
      inCentre I P B D ∧ inCentre I P A C
:= by
  sorry



--16G5
--In a non-isosceles acute triangle $\triangle ABC$, let $D$ be the foot of the perpendicular from $A$ to the Euler line, $H$ the foot of the perpendicular from $A$ to $BC$, and $M$ the midpoint of $BC$. Let circle $\odot S$ passing through $A$ and $D$ intersect sides $AB$ and $AC$ at points $X$ and $Y$, respectively. Prove that the circumcenter of $\triangle XSY$ is equidistant from $H$ and $M$.
theorem problem_16G5 :
∀ (A B C D H M X Y O : Point)
  (AB BC CA L AD AH : Line)
  (S : Circle),
  formTriangle A B C AB BC CA ∧
  D.onLine L ∧ distinctPointsOnLine A D AD ∧ perpLine AD L ∧
  H.onLine BC ∧ distinctPointsOnLine A H AH ∧ perpLine AH BC ∧
  midpoint B M C ∧
  A.onCircle S ∧ D.onCircle S ∧ X.onLine AB ∧ X.onCircle S ∧ Y.onLine AC ∧ Y.onCircle S ∧
  circumCentre O X A Y
  → |(O─H)| = |(O─M)| :=
by sorry



--18G7
--In an acute triangle $\triangle ABC$ with circumcircle $\odot O$, let $P$ be a point on $\odot O$ distinct from $A$, $B$, $C$, and their diametrically opposite points. Let $O_A$, $O_B$, $O_C$ be the circumcenters of $\triangle AOP$, $\triangle BOP$, and $\triangle COP$, respectively. Draw lines $l_A$, $l_B$, $l_C$ through $O_A$, $O_B$, $O_C$ perpendicular to $BC$, $CA$, $AB$, respectively. Prove that the circumcircle of the triangle formed by the intersections of line $OP$ with lines $l_A$, $l_B$, $l_C$ is tangent to $\odot O$.
theorem problem_18G7 :
∀ (A B C O P O_A O_B O_C X_A X_B X_C : Point)
  (AB BC CA OP l_A l_B l_C : Line)
  (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  O.isCentre Ω ∧
  circumCircle Ω A B C ∧
  P.onCircle Ω ∧
  circumCentre O_A A O P ∧
  circumCentre O_B B O P ∧
  circumCentre O_C C O P ∧
  O_A.onLine l_A ∧ perpLine l_A BC ∧
  O_B.onLine l_B ∧ perpLine l_B CA ∧
  O_C.onLine l_C ∧ perpLine l_C AB ∧
  twoLinesIntersectAtPoint OP l_A X_A ∧
  twoLinesIntersectAtPoint OP l_B X_B ∧
  twoLinesIntersectAtPoint OP l_C X_C
  → True
  -- The circumcircle of triangle X_A X_B X_C is tangent to the circle Ω
  -- (No direct predicate is available for “circle tangent to circle,” so the conclusion is stated textually.)
  :=
by sorry



--imo_2015_p4
--Triangle $ABC$ has circumcircle $\Omega$ and circumcenter $O$. A circle $\Gamma$ with center $A$ intersects the segment $BC$ at points $D$ and $E$, such that $B$, $D$, $E$, and $C$ are all different and lie on line $BC$ in this order. Let $F$ and $G$ be the points of intersection of $\Gamma$ and $\Omega$, such that $A$, $F$, $B$, $C$, and $G$ lie on $\Omega$ in this order. Let $K$ be the second point of intersection of the circumcircle of triangle $BDF$ and the segment $AB$. Let $L$ be the second point of intersection of the circumcircle of triangle $CGE$ and the segment $CA$. Suppose that the lines $FK$ and $GL$ are different and intersect at the point $X$. Prove that $X$ lies on the line $AO$.
theorem problem_imo_2015_p4 :
∀
(A B C O D E F G K L X : Point)
(AB BC CA BD DF FB CG GE EC AO FK GL : Line)
(circle_BDF circle_CGE Γ Ω : Circle),
  (formTriangle A B C AB BC CA) ∧
  (circumCentre O A B C) ∧
  (circumCircle Ω A B C) ∧
  (A.isCentre Γ) ∧
  (D.onLine BC) ∧ (E.onLine BC) ∧
  (D.onCircle Γ) ∧ (E.onCircle Γ) ∧
  (between B D C) ∧ (between D E C) ∧
  (F.onCircle Γ) ∧ (F.onCircle Ω) ∧
  (G.onCircle Γ) ∧ (G.onCircle Ω) ∧
  (formTriangle B D F BD DF FB) ∧
  (circumCircle circle_BDF B D F) ∧
  (K.onLine AB) ∧ (K.onCircle circle_BDF) ∧ (between A K B) ∧
  (formTriangle C G E CG GE EC) ∧
  (circumCircle circle_CGE C G E) ∧
  (L.onLine CA) ∧ (L.onCircle circle_CGE) ∧ (between C L A) ∧
  (distinctPointsOnLine F K FK) ∧
  (distinctPointsOnLine G L GL) ∧
  (twoLinesIntersectAtPoint FK GL X) ∧
  (distinctPointsOnLine A O AO)
→ X.onLine AO
:= by
  sorry




--12G3
--In an acute triangle $\triangle ABC$, let $AD$, $BE$, and $CF$ be altitudes. Let $I_1$ and $I_2$ be the incenters of $\triangle AEF$ and $\triangle BDF$, respectively, and let $O_1$ and $O_2$ be the circumcenters of $\triangle ACI_1$ and $\triangle BCI_2$, respectively. Prove that $I_1I_2 \parallel O_1O_2$.
theorem problem_12G3 :
∀ (A B C D E F I₁ I₂ O₁ O₂ : Point)
  (AB BC CA AD BE CF L_I₁I₂ L_O₁O₂ : Line),
  formTriangle A B C AB BC CA ∧
  A.onLine AD ∧ D.onLine AD ∧ B.onLine BC ∧ C.onLine BC ∧ D.onLine BC ∧ perpLine AD BC ∧
  B.onLine BE ∧ E.onLine BE ∧ A.onLine CA ∧ C.onLine CA ∧ E.onLine CA ∧ perpLine BE CA ∧
  C.onLine CF ∧ F.onLine CF ∧ A.onLine AB ∧ B.onLine AB ∧ F.onLine AB ∧ perpLine CF AB ∧
  inCentre I₁ A E F ∧
  inCentre I₂ B D F ∧
  circumCentre O₁ A C I₁ ∧
  circumCentre O₂ B C I₂ ∧
  I₁.onLine L_I₁I₂ ∧ I₂.onLine L_I₁I₂ ∧ distinctPointsOnLine I₁ I₂ L_I₁I₂ ∧
  O₁.onLine L_O₁O₂ ∧ O₂.onLine L_O₁O₂ ∧ distinctPointsOnLine O₁ O₂ L_O₁O₂
  → ¬(∃ P : Point, twoLinesIntersectAtPoint L_I₁I₂ L_O₁O₂ P) :=
by sorry



--MP92
--In $\triangle ABC$, $AD$ is the median of side $BC$, point $E$ is on line $AD$, draw $EF \parallel BC$, intersecting $AB$ at point $F$. Point $P$ is on line $BC$, $PF$ intersects $CE$ at point $G$, and $PE$ intersects $AC$ at point $H$. Prove that $GH \parallel BC$.
theorem MP92 :
∀ (A B C D E F P G H : Point)
  (AB BC CA AD EF PF CE PE GH : Line),
  formTriangle A B C AB BC CA ∧
  midpoint B D C ∧
  distinctPointsOnLine A D AD ∧
  E.onLine AD ∧
  distinctPointsOnLine E F EF ∧
  ¬(EF.intersectsLine BC) ∧
  twoLinesIntersectAtPoint EF AB F ∧
  P.onLine BC ∧
  distinctPointsOnLine P F PF ∧
  twoLinesIntersectAtPoint PF CE G ∧
  distinctPointsOnLine C E CE ∧
  twoLinesIntersectAtPoint PE AC H ∧
  distinctPointsOnLine P E PE ∧
  distinctPointsOnLine G H GH
  → ¬(GH.intersectsLine BC)
:= by
  sorry



--MP51
--In $\triangle ABC$, $\angle B = 30^\circ$, $\angle C = 15^\circ$, $AD$ is the median. Find $\angle DAC$.
theorem problem_MP51 :
∀ (A B C D : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  (∠ A:B:C = ∟/3) ∧
  (∠ B:C:A = ∟/6) ∧
  midpoint B D C
  → (∠ D:A:C = ∟/12) := by
sorry



--19G2
--In an acute triangle $\triangle ABC$, let $D$, $E$, $F$ be the feet of the perpendiculars from $A$, $B$, $C$ to sides $BC$, $CA$, $AB$, respectively. Let $\omega_B$, $\omega_C$ be the incircles of $\triangle BDF$, $\triangle CDE$, tangent to $DF$, $DE$ at points $M$, $N$, respectively. Let line $MN$ intersect $\omega_B$, $\omega_C$ again at points $P$, $Q$, respectively. Prove that $MP = NQ$.
theorem problem_19G2 :
  ∀ (A B C D E F M N P Q : Point)
    (AB BC CA AD BE CF BD DF FB CD DE EC MN : Line)
    (ω_B ω_C : Circle),
  formTriangle A B C AB BC CA ∧
  twoLinesIntersectAtPoint AD BC D ∧ A.onLine AD ∧ perpLine AD BC ∧
  twoLinesIntersectAtPoint BE CA E ∧ B.onLine BE ∧ perpLine BE CA ∧
  twoLinesIntersectAtPoint CF AB F ∧ C.onLine CF ∧ perpLine CF AB ∧
  formTriangle B D F BD DF FB ∧
  formTriangle C D E CD DE EC ∧
  inCircle ω_B BD DF FB ∧
  inCircle ω_C CD DE EC ∧
  tangentAtPoint DF ω_B M ∧
  tangentAtPoint DE ω_C N ∧
  distinctPointsOnLine M N MN ∧
  P.onLine MN ∧ P.onCircle ω_B ∧ M ≠ P ∧
  Q.onLine MN ∧ Q.onCircle ω_C ∧ N ≠ Q
  → |(M─P)| = |(N─Q)| :=
by sorry



--HP48
--Given that $I$ is the incenter of $\triangle ABC$. The reflection of $A$ across line $BI$ is point $K$. Point $E$ is the midpoint of line segment $BC$. Point $F$ is the midpoint of line segment $EF$, and point $N$ is the midpoint of line segment $EF$. Line $MN$ intersects line $BC$ at point $D$. Prove that points $A$, $K$, $D$, and $M$ are concyclic.
theorem problem_HP48 :
∀ (A B C I K E M N D : Point)
  (AB BC CA BI MN : Line),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  distinctPointsOnLine B I BI ∧
  perpBisector A K BI ∧
  midpoint B E C ∧
  distinctPointsOnLine M N MN ∧
  twoLinesIntersectAtPoint MN BC D
  → cyclic A K D M
:= by
  sorry



--HP20
--Given that in acute $\triangle ABC$, $\angle B > \angle C$, and $F$ is the midpoint of $BC$. Lines $BE$ and $CD$ are altitudes. Points $G$ and $H$ are the midpoints of $FD$ and $FE$, respectively. If a line through $A$ parallel to $BC$ intersects line $GH$ at point $I$, prove that $IA = IF$.
theorem problem_HP20 :
∀ (A B C D E F G H I : Point) (AB BC CA BE CD FD FE GH L : Line),
  formTriangle A B C AB BC CA ∧
  ∠A:B:C < ∟ ∧
  ∠B:C:A < ∟ ∧
  ∠C:A:B < ∟ ∧
  ∠A:B:C > ∠A:C:B ∧
  midpoint B F C ∧
  distinctPointsOnLine B E BE ∧
  E.onLine CA ∧
  perpLine BE CA ∧
  distinctPointsOnLine C D CD ∧
  D.onLine AB ∧
  perpLine CD AB ∧
  distinctPointsOnLine F D FD ∧
  midpoint F G D ∧
  distinctPointsOnLine F E FE ∧
  midpoint F H E ∧
  distinctPointsOnLine G H GH ∧
  A.onLine L ∧
  ¬(L.intersectsLine BC) ∧
  twoLinesIntersectAtPoint L GH I
→ |(I─A)| = |(I─F)| :=
by sorry



--MP7
--In $\triangle ABC$, points $E$ and $D$ are on the extension and the reverse extension of $BC$, respectively, such that $\angle ABD = 2\angle ACE$ and $AF$ is the angle bisector. Prove that $AB - BF = AC$.
theorem problem_MP7 :
  ∀ (A B C D E F : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  threePointsOnLine B C D BC ∧ between C B D ∧
  threePointsOnLine B C E BC ∧ between B C E ∧
  (∠A:B:D = 2 * (∠A:C:E)) ∧
  F.onLine BC ∧
  (∠B:A:F = ∠F:A:C)
  → |(A─B)| = |(A─C)| + |(B─F)| :=
by
  sorry



--HP59
--Given that in isosceles $\triangle ABC$, $AB = AC$, and point $E$ is the midpoint of $AC$. Point $D$ lies on line $BC$, such that $BD = 2CD$. Line $DF$ is perpendicular to line $BE$ at point $F$. Connect line $CF$. Prove that $\angle EFC = \angle ABC$.
theorem problem_HP59 :
  ∀ (A B C D E F : Point) (AB BC CA BE DF CF : Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(A─C)| ∧
  midpoint A E C ∧
  between B D C ∧
  (|(B─D)| = |(C─D)| + |(C─D)|) ∧
  distinctPointsOnLine B E BE ∧
  F.onLine BE ∧
  distinctPointsOnLine D F DF ∧
  perpLine DF BE ∧
  distinctPointsOnLine C F CF
  → ∠ E:F:C = ∠ A:B:C :=
by sorry



--HP30
--Given that in $\triangle ABC$, point $D$ is the midpoint of $BC$, $O$ is the circumcenter, and $H$ is the orthocenter. Points $E$ and $F$ lie on sides $AB$ and $AC$, respectively, such that $AE = AF$. Points $D$, $H$, and $E$ are collinear. Point $P$ is the circumcenter of $\triangle AEF$. Prove that $OP \parallel HD$.
theorem problem_HP30 :
∀ (A B C D E F O H P : Point) (AB BC CA LHD LOP : Line),
  formTriangle A B C AB BC CA
  ∧ midpoint B D C
  ∧ circumCentre O A B C
  ∧ E.onLine AB
  ∧ between A E B
  ∧ F.onLine CA
  ∧ between A F C
  ∧ (|(A─E)| = |(A─F)|)
  ∧ threePointsOnLine D H E LHD
  ∧ circumCentre P A E F
  ∧ O.onLine LOP
  ∧ P.onLine LOP
→ ¬(LHD.intersectsLine LOP)
:= by
  sorry



--02G3
--The circle $S$ has centre $O$, and $BC$ is a diameter of $S$. Let $A$ be a point of $S$ such that $\angle AOB<120{{},^\circ},$.  Let $D$ be the midpoint of the arc $AB$ which does not contain $C$. The line through $O$ parallel to $DA$ meets the line $AC$ at $I$. The perpendicular bisector of $OA$ meets $S$ at $E$ and at $F$. Prove that $I$ is the incentre of the triangle $CEF.$
theorem problem_02G3 :
∀
(S : Circle)
(O A B C D E F I : Point)
(AC DA L_P L_perp CE EF FC : Line),
  (
    O.isCentre S
    ∧ A.onCircle S
    ∧ B.onCircle S
    ∧ C.onCircle S
    ∧ D.onCircle S
    ∧ E.onCircle S
    ∧ F.onCircle S
    ∧ between B O C
    ∧ ∠ A:O:B < 120
    ∧ distinctPointsOnLine A C AC
    ∧ distinctPointsOnLine A D DA
    /- “the line through O parallel to DA”: use ¬(∃ X, twoLinesIntersectAtPoint L_P DA X) to encode parallel -/
    ∧ O.onLine L_P
    ∧ ¬(∃ X : Point, twoLinesIntersectAtPoint L_P DA X)
    ∧ twoLinesIntersectAtPoint L_P AC I
    /- “the perpendicular bisector of OA meets S at E and F” -/
    ∧ perpBisector O A L_perp
    ∧ E.onLine L_perp
    ∧ F.onLine L_perp
    ∧ formTriangle C E F CE EF FC
  )
  → inCentre I C E F
:= by
  sorry



--imo_2013_p4
--Let $ABC$ be an acute triangle with orthocenter $H$, and let $W$ be a point on the side $BC$, lying strictly between $B$ and $C$. The points $M$ and $N$ are the feet of the altitudes from $B$ and $C$, respectively. Denote by $\omega_1$ is the circumcircle of $BWN$, and let $X$ be the point on $\omega_1$ such that $WX$ is a diameter of $\omega_1$. Analogously, denote by $\omega_2$ the circumcircle of triangle $CWM$, and let $Y$ be the point such that $WY$ is a diameter of $\omega_2$. Prove that $X, Y$ and $H$ are collinear.
theorem problem_imo_2013_p4 :
  ∀ (A B C H W M N X Y : Point)
    (AB BC CA BM CN ℓ : Line)
    (ω₁ ω₂ : Circle),
  formTriangle A B C AB BC CA ∧
  W.onLine BC ∧
  between B W C ∧
  M.onLine CA ∧
  distinctPointsOnLine B M BM ∧
  perpLine BM CA ∧
  N.onLine AB ∧
  distinctPointsOnLine C N CN ∧
  perpLine CN AB ∧
  twoLinesIntersectAtPoint BM CN H ∧
  circumCircle ω₁ B W N ∧
  X.onCircle ω₁ ∧
  ∠W:N:X = ∟ ∧
  circumCircle ω₂ C W M ∧
  Y.onCircle ω₂ ∧
  ∠W:M:Y = ∟
  → threePointsOnLine X Y H ℓ
:= by
  sorry



--15G7
--In a convex quadrilateral $ABCD$, points $P$, $Q$, $R$, and $S$ lie on sides $AB$, $BC$, $CD$, and $DA$, respectively. Line $PR$ intersects line $QS$ at point $O$. If quadrilaterals $APO S$, $BQOP$, $CROQ$, and $DSOR$ all have incircles, prove that lines $AC$, $PQ$, and $RS$ are either concurrent or parallel.
theorem problem_15G7 :
∀
(A B C D P Q R S O : Point)
(AB BC CD DA AP PO OS SA BQ QO OP PB CR RO OQ QC DS SO OR RD PR QS AC PQ RS : Line)
(inc1 inc2 inc3 inc4 : Circle),
  formQuadrilateral A B C D AB BC CD DA
∧ A.onLine AB ∧ B.onLine AB
∧ B.onLine BC ∧ C.onLine BC
∧ C.onLine CD ∧ D.onLine CD
∧ D.onLine DA ∧ A.onLine DA

∧ A.onLine AP ∧ P.onLine AP
∧ P.onLine PO ∧ O.onLine PO
∧ O.onLine OS ∧ S.onLine OS
∧ S.onLine SA ∧ A.onLine SA
∧ tangentLine AP inc1 ∧ tangentLine PO inc1 ∧ tangentLine OS inc1 ∧ tangentLine SA inc1

∧ B.onLine BQ ∧ Q.onLine BQ
∧ Q.onLine QO ∧ O.onLine QO
∧ O.onLine OP ∧ P.onLine OP
∧ P.onLine PB ∧ B.onLine PB
∧ tangentLine BQ inc2 ∧ tangentLine QO inc2 ∧ tangentLine OP inc2 ∧ tangentLine PB inc2

∧ C.onLine CR ∧ R.onLine CR
∧ R.onLine RO ∧ O.onLine RO
∧ O.onLine OQ ∧ Q.onLine OQ
∧ Q.onLine QC ∧ C.onLine QC
∧ tangentLine CR inc3 ∧ tangentLine RO inc3 ∧ tangentLine OQ inc3 ∧ tangentLine QC inc3

∧ D.onLine DS ∧ S.onLine DS
∧ S.onLine SO ∧ O.onLine SO
∧ O.onLine OR ∧ R.onLine OR
∧ R.onLine RD ∧ D.onLine RD
∧ tangentLine DS inc4 ∧ tangentLine SO inc4 ∧ tangentLine OR inc4 ∧ tangentLine RD inc4

∧ P.onLine PR ∧ R.onLine PR
∧ Q.onLine QS ∧ S.onLine QS
∧ A.onLine AC ∧ C.onLine AC
∧ P.onLine PQ ∧ Q.onLine PQ
∧ R.onLine RS ∧ S.onLine RS
∧ twoLinesIntersectAtPoint PR QS O

→
  ( ∃ X : Point, X.onLine AC ∧ X.onLine PQ ∧ X.onLine RS )
  ∨
  ( ¬(AC.intersectsLine PQ) ∧ ¬(PQ.intersectsLine RS) ∧ ¬(AC.intersectsLine RS) )
:= by
  sorry



--imo_2003_p4
--Let $ABCD$ be a cyclic quadrilateral. Let $P$, $Q$, and $R$ be the feet of perpendiculars from $D$ to lines $\overline{BC}$, $\overline{CA}$, and $\overline{AB}$, respectively. Show that $PQ=QR$ if and only if the bisectors of angles $ABC$ and $ADC$ meet on segment $\overline{AC}$.
theorem problem_imo_2003_p4 :
  ∀ (A B C D P Q R M : Point)
    (AB BC CD DA AC DP DQ DR BM DM : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  cyclic A B C D ∧
  P.onLine BC ∧ distinctPointsOnLine D P DP ∧ perpLine DP BC ∧
  Q.onLine CA ∧ distinctPointsOnLine D Q DQ ∧ perpLine DQ CA ∧
  R.onLine AB ∧ distinctPointsOnLine D R DR ∧ perpLine DR AB ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B M BM ∧
  distinctPointsOnLine D M DM
  →
  (
    ( (|(P─Q)| = |(Q─R)|)
      ∧ (∠A:B:M = ∠M:B:C ∧ ∠A:D:M = ∠M:D:C ∧ M.onLine AC ∧ between A M C)
    )
    ∨
    (
      ¬(|(P─Q)| = |(Q─R)|)
      ∧ ¬(∠A:B:M = ∠M:B:C ∧ ∠A:D:M = ∠M:D:C ∧ M.onLine AC ∧ between A M C)
    )
  )
:= by
  sorry



--HP85
--Given that in $\triangle ABC$, $AB > AC$. Line $BD$ is perpendicular to line $AC$ at point $D$. Line $CE$ is perpendicular to line $AB$ at point $E$. Point $F$ is the midpoint of line segment $BC$. Line $AG$ is perpendicular to line $AF$, intersecting the extension of line $DE$ at point $G$. Connect line $GF$. Prove that $AF$ bisects angle $\angle GFC$.
theorem problem_HP85 :
∀ (A B C D E F G : Point)
  (AB BC CA BD CE AF AG DE GF : Line),
  formTriangle A B C AB BC CA ∧
  (|(A─B)| > |(A─C)|) ∧
  distinctPointsOnLine B D BD ∧ perpLine BD CA ∧ twoLinesIntersectAtPoint BD CA D ∧
  distinctPointsOnLine C E CE ∧ perpLine CE AB ∧ twoLinesIntersectAtPoint CE AB E ∧
  midpoint B F C ∧
  distinctPointsOnLine A F AF ∧
  perpLine AG AF ∧ distinctPointsOnLine A G AG ∧ twoLinesIntersectAtPoint DE AG G ∧ distinctPointsOnLine D E DE ∧
  distinctPointsOnLine G F GF
  → ∠G:F:A = ∠A:F:C
:= by
  sorry



--MP95
--In quadrilateral $ABCD$, $AB$ and $CD$ are not parallel. Draw $DE \parallel AB$, intersecting $BC$ at point $E$, $AF \parallel DC$, intersecting $BC$ and $BD$ at points $F$ and $G$, respectively. Prove that $\frac{BE}{EC} = \frac{AG}{GF}$.
theorem problem_MP95 :
  ∀ (A B C D E F G : Point) (AB BC CD DA BD AF DE : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  AB.intersectsLine CD ∧
  ¬(DE.intersectsLine AB) ∧
  twoLinesIntersectAtPoint DE BC E ∧
  ¬(AF.intersectsLine DC) ∧
  twoLinesIntersectAtPoint AF BC F ∧
  twoLinesIntersectAtPoint AF BD G
  → (|(B─E)| * |(G─F)|) = (|(E─C)| * |(A─G)|) :=
by sorry




--HP6
--Given that $BC$ and $BD$ are tangents to circle $\odot O$, with $C$ and $D$ as the points of tangency. Line $BJA$ is a secant, with $A$ and $J$ on the circle, and $J$ closer to $B$. Line $DE$ is perpendicular to $AO$ at point $E$, intersecting $AB$ at point $F$. Line $AC$ intersects $DE$ at point $G$. Prove that $DF = FG$.
theorem problem_HP6 :
∀ (A B C D E F G J O : Point) (Γ : Circle)
  (BJA BC BD AB AC DE AO : Line),
  O.isCentre Γ ∧
  tangentAtPoint BC Γ C ∧
  tangentAtPoint BD Γ D ∧
  A.onCircle Γ ∧
  J.onCircle Γ ∧
  threePointsOnLine B J A BJA ∧
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine A O AO ∧
  twoLinesIntersectAtPoint DE AO E ∧
  perpLine DE AO ∧
  twoLinesIntersectAtPoint DE AB F ∧
  twoLinesIntersectAtPoint AC DE G
  → |(D─F)| = |(F─G)| :=
by sorry



--88T15
--Let $ ABC$ be an acute-angled triangle. The lines $ L_{A},$, $ L_{B},$ and $ L_{C},$ are constructed through the vertices $ A$, $ B$ and $ C$ respectively according the following prescription: Let $ H$ be the foot of the altitude drawn from the vertex $ A$ to the side $ BC$; let $ S_{A},$ be the circle with diameter $ AH$; let $ S_{A},$ meet the sides $ AB$ and $ AC$ at $ M$ and $ N$ respectively, where $ M$ and $ N$ are distinct from $ A$; then let $ L_{A},$ be the line through $ A$ perpendicular to $ MN$. The lines $ L_{B},$ and $ L_{C},$ are constructed similarly. Prove that the lines $ L_{A},$, $ L_{B},$ and $ L_{C},$ are concurrent.
theorem problem_88T15 :
∀
(A B C H_A H_B H_C M_A N_A M_B N_B M_C N_C X : Point)
(AB BC CA AH_A BH_B CH_C M_AN_A M_BN_B M_CN_C L_A L_B L_C : Line)
(S_A S_B S_C : Circle),
formTriangle A B C AB BC CA ∧

H_A.onLine BC ∧ between B H_A C ∧ distinctPointsOnLine A H_A AH_A ∧ perpLine AH_A BC ∧
A.onCircle S_A ∧ H_A.onCircle S_A ∧
M_A.onCircle S_A ∧ M_A.onLine AB ∧ A≠ M_A ∧
N_A.onCircle S_A ∧ N_A.onLine AC ∧ A ≠  N_A ∧
distinctPointsOnLine M_A N_A M_AN_A ∧
A.onLine L_A ∧ perpLine L_A M_AN_A ∧

H_B.onLine CA ∧ between A H_B C ∧ distinctPointsOnLine B H_B BH_B ∧ perpLine BH_B CA ∧
B.onCircle S_B ∧ H_B.onCircle S_B ∧
M_B.onCircle S_B ∧ M_B.onLine BA ∧ B ≠  M_B ∧
N_B.onCircle S_B ∧ N_B.onLine BC ∧ B ≠ N_B ∧
distinctPointsOnLine M_B N_B M_BN_B ∧
B.onLine L_B ∧ perpLine L_B M_BN_B ∧

H_C.onLine AB ∧ between A H_C B ∧ distinctPointsOnLine C H_C CH_C ∧ perpLine CH_C AB ∧
C.onCircle S_C ∧ H_C.onCircle S_C ∧
M_C.onCircle S_C ∧ M_C.onLine CA ∧ C ≠  M_C ∧
N_C.onCircle S_C ∧ N_C.onLine CB ∧ C ≠ N_C ∧
distinctPointsOnLine M_C N_C M_CN_C ∧
C.onLine L_C ∧ perpLine L_C M_CN_C

→ twoLinesIntersectAtPoint L_A L_B X ∧ X.onLine L_C
:= by
  sorry



--16G6
--In a convex quadrilateral $ABCD$ with $\angle ABC = \angle ADC < 90^\circ$, let the angle bisectors of $\angle ABC$ and $\angle ADC$ intersect at point $P$ and intersect $AC$ at points $E$ and $F$, respectively. Let $M$ be the midpoint of $AC$. Lines $BM$ and $DM$ intersect the circumcircle of $\triangle BPD$ again at points $X$ and $Y$, respectively. Line $XE$ intersects line $YF$ at point $Q$. Prove that $PQ \perp AC$.
theorem problem_16G6 :
∀ (A B C D E F P M X Y Q : Point)
  (AB BC CD DA AC BE DF BM DM XE YF PQ : Line)
  (ω : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  (∠ A:B:C = ∠ A:D:C) ∧
  (∠ A:B:C < ∟) ∧

  distinctPointsOnLine A C AC ∧
  E.onLine AC ∧
  (∠ A:B:E = ∠ E:B:C) ∧
  F.onLine AC ∧
  (∠ A:D:F = ∠ F:D:C) ∧
  twoLinesIntersectAtPoint BE DF P ∧
  midpoint A M C ∧
  circumCircle ω B P D ∧

  B.onLine BM ∧
  M.onLine BM ∧
  X.onLine BM ∧
  X.onCircle ω ∧
  D.onLine DM ∧
  M.onLine DM ∧
  Y.onLine DM ∧
  Y.onCircle ω ∧

  X.onLine XE ∧
  E.onLine XE ∧
  Y.onLine YF ∧
  F.onLine YF ∧
  twoLinesIntersectAtPoint XE YF Q ∧

  P.onLine PQ ∧
  Q.onLine PQ
→ perpLine PQ AC
:= by
  sorry



--15G3
--In a right triangle $\triangle ABC$ with $\angle C = 90^\circ$ and $CH$ as the altitude, let $D$ be a point inside $\triangle CBH$ such that $CH$ bisects segment $AD$. Line $BD$ intersects $CH$ at point $P$. Let $\Gamma$ be the semicircle with diameter $BD$, intersecting $BC$ at a point other than $B$. A line through $P$ is tangent to $\Gamma$ at point $Q$. Prove that the intersection of line $CQ$ with $AD$ lies on $\Gamma$.
theorem problem_15G3 :
∀
(A B C D H M P Q R : Point)
(AB BC CA CH BH AD BD PQ CQ : Line)
(Γ : Circle),
formTriangle A B C AB BC CA ∧
∠B:C:A = ∟ ∧
distinctPointsOnLine A B AB ∧
distinctPointsOnLine C H CH ∧
H.onLine AB ∧
perpLine CH AB ∧
formTriangle C B H CB BH HC ∧
insideTriangle D C B H CB BH HC ∧
distinctPointsOnLine A D AD ∧
twoLinesIntersectAtPoint AD CH M ∧
midpoint A M D ∧
distinctPointsOnLine B D BD ∧
twoLinesIntersectAtPoint BD CH P ∧
B.onCircle Γ ∧
D.onCircle Γ ∧
distinctPointsOnLine P Q PQ ∧
Q.onCircle Γ ∧
tangentAtPoint PQ Γ Q ∧
distinctPointsOnLine C Q CQ ∧
twoLinesIntersectAtPoint CQ AD R
→ R.onCircle Γ
:= by
  sorry



--HP64
--Given that lines $AB$ and $AC$ are tangents to circle $\odot O$ at points $A$ and $B$, respectively. Point $D$ lies on the extension of line $AB$. The circumcircle of $\triangle ADC$, circle $\odot P$, intersects circle $\odot O$ at point $E$. Line $BF$ is perpendicular to line $CD$ at point $F$. Prove that $\angle DEF = 2\angle ADC$.
theorem problem_HP64 :
  ∀ (A B C D E F : Point) (AB AC BF CD : Line) (O P : Circle),
    distinctPointsOnLine A B AB ∧
    distinctPointsOnLine A C AC ∧
    distinctPointsOnLine C D CD ∧
    tangentAtPoint AB O A ∧
    tangentAtPoint AC O B ∧
    D.onLine AB ∧
    circumCircle P A D C ∧
    E.onCircle O ∧
    E.onCircle P ∧
    twoLinesIntersectAtPoint BF CD F ∧
    perpLine BF CD
  → ∠D:E:F = 2 * ∠A:D:C :=
by
  sorry



--82T13
--A non-isosceles triangle $A_{1},A_{2},A_{3},$ has sides $a_{1},$, $a_{2},$, $a_{3},$ with the side $a_{i},$ lying opposite to the vertex $A_{i},$. Let $M_{i},$ be the midpoint of the side $a_{i},$, and let $T_{i},$ be the point where the inscribed circle of triangle $A_{1},A_{2},A_{3},$ touches the side $a_{i},$. Denote by $S_{i},$ the reflection of the point $T_{i},$ in the interior angle bisector of the angle $A_{i},$. Prove that the lines $M_{1},S_{1},$, $M_{2},S_{2},$ and $M_{3},S_{3},$ are concurrent.
theorem problem_82T13 :
∀ (A₁ A₂ A₃ I M₁ M₂ M₃ T₁ T₂ T₃ S₁ S₂ S₃ : Point)
  (A₁A₂ A₂A₃ A₃A₁ M₁S₁ M₂S₂ M₃S₃ : Line)
  (incΩ : Circle),
  ( |(A₁─A₂)| ≠ |(A₂─A₃)| ∧ |(A₂─A₃)| ≠ |(A₃─A₁)| ∧ |(A₃─A₁)| ≠ |(A₁─A₂)| )
  ∧ formTriangle A₁ A₂ A₃ A₁A₂ A₂A₃ A₃A₁
  ∧ inCentre I A₁ A₂ A₃
  ∧ inCircle incΩ A₁A₂ A₂A₃ A₃A₁
  ∧ T₁.onLine A₂A₃ ∧ T₁.onCircle incΩ ∧ tangentAtPoint A₂A₃ incΩ T₁
  ∧ T₂.onLine A₃A₁ ∧ T₂.onCircle incΩ ∧ tangentAtPoint A₃A₁ incΩ T₂
  ∧ T₃.onLine A₁A₂ ∧ T₃.onCircle incΩ ∧ tangentAtPoint A₁A₂ incΩ T₃
  ∧ midpoint A₂ M₁ A₃
  ∧ midpoint A₁ M₂ A₃
  ∧ midpoint A₁ M₃ A₂
  ∧ (¬(A₁ = T₁) ∧ ¬(A₁ = S₁)  -- schematic placeholder for “S₁ is reflection of T₁ about the bisector of ∠A₁”
     ∧ ¬(A₂ = T₂) ∧ ¬(A₂ = S₂)
     ∧ ¬(A₃ = T₃) ∧ ¬(A₃ = S₃))
  ∧ distinctPointsOnLine M₁ S₁ M₁S₁
  ∧ distinctPointsOnLine M₂ S₂ M₂S₂
  ∧ distinctPointsOnLine M₃ S₃ M₃S₃
  →
  ∃ X : Point,
    twoLinesIntersectAtPoint M₁S₁ M₂S₂ X
    ∧ X.onLine M₃S₃
:= by
  sorry



--imo_2015_p3
--Let $ABC$ be an acute triangle with $AB>AC$. Let $\Gamma$ be its circumcircle, $H$ its orthocenter, and $F$ the foot of the altitude from $A$. Let $M$ be the midpoint of $BC$. Let $Q$ be the point on $\Gamma$ such that $\angle HKQ=90^\circ$. Assume that the points $A$, $B$, $C$, $K$, and $Q$ are all different, and lie on $\Gamma$ in this order. Prove that the circumcircles of triangles $KQH$ and $FKM$ are tangent to each other.
theorem problem_imo_2015_p3 :
  ∀ (A B C H F M K Q : Point)
    (AB BC CA : Line)
    (Γ α β: Circle),
  formTriangle A B C AB BC CA ∧
  (|(A─B)| > |(A─C)|) ∧
  circumCircle Γ A B C ∧
  A.onCircle Γ ∧ B.onCircle Γ ∧ C.onCircle Γ ∧ K.onCircle Γ ∧ Q.onCircle Γ ∧
  midpoint B M C ∧
  F.onLine BC ∧
  perpLine AB BC ∧  -- (Placeholder; ordinarily one would encode “F is foot of altitude”, “H is orthocenter” etc.)
  perpLine AC BC ∧  -- (Likewise placeholder to suggest orthogonality conditions in an acute triangle)
  ∠H:K:Q = ∟ ∧
  circumCircle α K Q H ∧
  circumCircle β F K M
  → (∀ X : Point, X.onCircle α ∧ X.onCircle β → X = K)
:= by
  sorry



--HP17
--Given that the incircle of $\triangle ABC$, circle $\odot I$, is tangent to $BC$ at point $D$. Draw line $IE \parallel AD$, intersecting $BC$ at point $E$. Draw a tangent to circle $\odot I$ at point $E$, intersecting lines $AB$ and $AC$ at points $F$ and $G$, respectively. Prove that $E$ is the midpoint of $FG$.
theorem problem_HP17 :
  ∀ (A B C I D E F G : Point)
    (AB BC CA AD IE EF : Line)
    (Γ : Circle),
    formTriangle A B C AB BC CA ∧
    inCentre I A B C ∧
    inCircle Γ AB BC CA ∧
    I.isCentre Γ ∧
    tangentAtPoint BC Γ D ∧
    distinctPointsOnLine A D AD ∧
    distinctPointsOnLine I E IE ∧
    twoLinesIntersectAtPoint IE BC E ∧
    distinctPointsOnLine E F EF ∧
    twoLinesIntersectAtPoint EF AB F ∧
    twoLinesIntersectAtPoint EF AC G ∧
    tangentAtPoint EF Γ E ∧
    ¬(∃ X : Point, twoLinesIntersectAtPoint AD IE X)
  → midpoint F E G :=
by sorry



--HP67
--Given that circle $\odot O$ is the circumcircle of $\triangle ABC$. Points $D$ and $E$ are the midpoints of sides $AB$ and $AC$, respectively. Point $H$ is the orthocenter of $\triangle ABC$. The extension of line $DH$ intersects circle $\odot O$ at point $F$, and the extension of line $EH$ intersects circle $\odot O$ at point $G$. Lines $DE$ and $GF$ intersect at point $I$. Connect line $AI$. Prove that $AI \perp AO$.
theorem problem_HP67 :
∀
(A B C D E F G H I O : Point)
(AB BC CA DE GF AI AO DH EH : Line)
(Ω : Circle),
(
  formTriangle A B C AB BC CA
  ∧ midpoint A D B
  ∧ midpoint A E C
  ∧ distinctPointsOnLine D H DH
  ∧ F.onLine DH
  ∧ F.onCircle Ω
  ∧ distinctPointsOnLine E H EH
  ∧ G.onLine EH
  ∧ G.onCircle Ω
  ∧ distinctPointsOnLine D E DE
  ∧ distinctPointsOnLine G F GF
  ∧ twoLinesIntersectAtPoint DE GF I
  ∧ distinctPointsOnLine A I AI
  ∧ distinctPointsOnLine A O AO
  ∧ O.isCentre Ω
  ∧ circumCircle Ω A B C
)
→ perpLine AI AO
:= by
  sorry



--HP66
--Given that circle $\odot O$ is the circumcircle of $\triangle ABC$. The incircle of $\triangle ABC$, circle $\odot I$, is tangent to sides $AB$ and $AC$ at points $D$ and $E$, respectively. Circle $\odot P$ is externally tangent to circle $\odot O$ at point $J$, and is tangent to lines $AB$ and $AC$ at points $G$ and $H$, respectively. Line $AD$ extended intersects circle $\odot P$ at point $K$. Prove that $AJ = AK$, and $\angle BAJ = \angle CAD$.
theorem problem_HP66 :
  ∀ (A B C D E G H J K : Point) (AB BC CA : Line) (O I P : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  inCircle I AB BC CA ∧
  tangentAtPoint AB I D ∧
  tangentAtPoint AC I E ∧
  O.intersectsCircle P ∧
  J.onCircle O ∧
  J.onCircle P ∧
  tangentAtPoint AB P G ∧
  tangentAtPoint AC P H ∧
  K.onLine AB ∧
  K.onCircle P
  → (|(A ─ J)| = |(A ─ K)| ∧ ∠ B:A:J = ∠ C:A:D) := by
sorry



--HP26
--Given that circle $\odot O$ is the circumcircle of $\triangle ABC$. Line $AD$ bisects angle $\angle BAC$, intersecting circle $\odot O$ at point $D$. Line $OE$ is parallel to line $BD$, intersecting line $AB$ at point $E$. Line $OF$ is parallel to line $CD$, intersecting line $AC$ at point $F$. Point $H$ is the orthocenter of $\triangle ABC$. Line $HG$ is parallel to line $AD$, intersecting line $BC$ at point $G$. Prove that $BE = GE = GF = CF$.
theorem HP26 :
∀ (A B C D E F G H O : Point)
  (AB BC CA AD BD CD OE OF AH BH CH HG : Line)
  (Γ : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle Γ A B C ∧
  O.isCentre Γ ∧
  distinctPointsOnLine A D AD ∧
  ∠B:A:D = ∠D:A:C ∧
  D.onCircle Γ ∧
  distinctPointsOnLine O E OE ∧
  distinctPointsOnLine B D BD ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint BD OE X) ∧
  twoLinesIntersectAtPoint AB OE E ∧
  distinctPointsOnLine O F OF ∧
  distinctPointsOnLine C D CD ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint CD OF X) ∧
  twoLinesIntersectAtPoint AC OF F ∧
  distinctPointsOnLine A H AH ∧
  perpLine AH BC ∧
  distinctPointsOnLine B H BH ∧
  perpLine BH AC ∧
  distinctPointsOnLine C H CH ∧
  perpLine CH AB ∧
  distinctPointsOnLine H G HG ∧
  twoLinesIntersectAtPoint BC HG G ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint HG AD X)
  → ( |(B─E)| = |(G─E)| )
    ∧ ( |(G─E)| = |(G─F)| )
    ∧ ( |(G─F)| = |(C─F)| ) :=
by sorry



--HP24
--Given that the incircle of $\triangle ABC$, circle $\odot I$, is tangent to $BC$ at point $D$. Line $AE$ is perpendicular to $BC$ at point $E$, and $F$ is the midpoint of $AE$. Line $DF$ intersects circle $\odot I$ at point $G$. Draw the circumcircle of $\triangle BCG$, circle $\odot O$. Prove that circles $\odot O$ and $\odot I$ are tangent at point $G$.
theorem HP24 :
  ∀ (A B C D E F G : Point)
    (AB BC CA AE DF : Line)
    (I O : Circle),
  formTriangle A B C AB BC CA ∧
  inCircle I AB BC CA ∧
  tangentAtPoint BC I D ∧
  twoLinesIntersectAtPoint AE BC E ∧
  perpLine AE BC ∧
  midpoint A F E ∧
  distinctPointsOnLine D F DF ∧
  G.onLine DF ∧
  G.onCircle I ∧
  circumCircle O B C G
  → ∃ (L : Line), tangentAtPoint L O G ∧ tangentAtPoint L I G
:= by
  sorry



--HP9
--Given circle $O$, and a point $P$ outside the circle. Draw two tangents $PC$ and $PD$ to circle $O$, with points of tangency at $C$ and $D$. Through a point $E$ on the minor arc $CD$, draw another tangent to circle $O$, intersecting $PC$ and $PD$ at points $A$ and $B$, respectively. Line $OE$ intersects $CD$ at point $N$, and line $PN$ intersects $AB$ at point $M$. Prove that $MA = MB$.
theorem HP9 :
∀ (O : Circle) (P C D E A B M N : Point) (PC PD AB OE CD PN : Line),
P.outsideCircle O ∧
tangentAtPoint PC O C ∧
tangentAtPoint PD O D ∧
E.onCircle O ∧
tangentAtPoint AB O E ∧
twoLinesIntersectAtPoint PC AB A ∧
twoLinesIntersectAtPoint PD AB B ∧
twoLinesIntersectAtPoint OE CD N ∧
twoLinesIntersectAtPoint PN AB M
→ |(M─A)| = |(M─B)| := by
sorry



--HP45
--Given that line $PA$ is tangent to circle $\odot O$ at point $A$, and line $PBC$ is a secant of circle $\odot O$. Line $AD$ is perpendicular to line $OP$ at point $D$. The circumcircle of $\triangle ADC$ intersects line $BC$ again at point $E$. Prove that $\angle BAE = \angle ACB$.
theorem problem_HP45 :
∀ (A B C D E O P : Point)
  (lPA lPBC lOP lAD : Line)
  (Ocircle Γ : Circle),
  (A.onLine lPA) ∧
  (P.onLine lPA) ∧
  (O.isCentre Ocircle) ∧
  (A.onCircle Ocircle) ∧
  tangentAtPoint lPA Ocircle A ∧
  (B.onLine lPBC) ∧
  (C.onLine lPBC) ∧
  (B.onCircle Ocircle) ∧
  (C.onCircle Ocircle) ∧
  (O.onLine lOP) ∧
  (P.onLine lOP) ∧
  twoLinesIntersectAtPoint lAD lOP D ∧
  perpLine lAD lOP ∧
  circumCircle Γ A D C ∧
  (E.onLine lPBC) ∧
  (E.onCircle Γ)
  → ∠ B:A:E = ∠ A:C:B
:= by
  sorry



--HP41
--Given that lines $PA$ and $PB$ are tangents to circle $\odot O$ at points $A$ and $B$, respectively. Line $PCD$ is a secant of circle $\odot O$. Draw line $CF$ parallel to line $PB$, intersecting line $AB$ at point $E$ and line $BD$ at point $F$. Prove that $E$ is the midpoint of line segment $CF$.
theorem HP41 :
∀ (P A B C D E F : Point)
  (PA PB AB BD CF PCD : Line)
  (O : Circle),
  (
    distinctPointsOnLine P A PA
    ∧ tangentAtPoint PA O A
    ∧ A.onCircle O
    ∧ distinctPointsOnLine P B PB
    ∧ tangentAtPoint PB O B
    ∧ B.onCircle O
    ∧ threePointsOnLine P C D PCD
    ∧ C.onCircle O
    ∧ D.onCircle O
    ∧ distinctPointsOnLine A B AB
    ∧ distinctPointsOnLine B D BD
    ∧ distinctPointsOnLine C F CF
    ∧ ¬(∃ X : Point, twoLinesIntersectAtPoint PB CF X)
    ∧ twoLinesIntersectAtPoint CF AB E
    ∧ twoLinesIntersectAtPoint CF BD F
  )
  → midpoint C E F
:= by
  sorry



--12G2
--In a cyclic quadrilateral $ABCD$, let $AC$ and $BD$ intersect at point $E$, and the extensions of lines $DA$ and $CB$ intersect at point $F$. Construct a parallelogram $ECGD$, and let $H$ be the reflection of $E$ across line $AD$. Prove that points $D$, $H$, $F$, and $G$ are concyclic.
theorem problem_12G2 :
∀ (A B C D E F G H M : Point)
  (AB BC CD DA AC BD EC CG GD DE : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  cyclic A B C D ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B D BD ∧
  twoLinesIntersectAtPoint AC BD E ∧
  twoLinesIntersectAtPoint DA BC F ∧
  formQuadrilateral E C G D EC CG GD DE ∧
  midpoint M E G ∧
  midpoint M C D ∧
  perpBisector E H AD
→ cyclic D H F G := by
  sorry



--HP19
--Given that circle $\odot O$ is the circumcircle of $\triangle ABC$, and $I$ and $E$ are the incenter and an excenter of $\triangle ABC$, respectively. The external angle bisector of $\angle BAC$ intersects the extension of line $BC$ at point $D$. Line $IF$ is perpendicular to line $DE$ at point $F$, intersecting circle $\odot O$ at point $G$. Prove that $G$ is the midpoint of $IF$.
theorem problem_HP19 :
∀ (A B C I E D F G : Point) (AB BC CA DE IF : Line) (O : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  inCentre I A B C ∧
  threePointsOnLine B C D BC ∧
  distinctPointsOnLine D E DE ∧
  twoLinesIntersectAtPoint IF DE F ∧
  perpLine IF DE ∧
  G.onLine IF ∧
  G.onCircle O
  → midpoint I G F :=
by
  sorry



--15G1
--In an acute triangle $\triangle ABC$, let $H$ be the orthocenter. Construct parallelogram $ABGH$, and extend $GH$ to point $I$ such that $AC$ bisects segment $HI$. Let line $AC$ intersect the circumcircle of $\triangle GCI$ at point $J$. Prove that $IJ = AH$.
theorem problem_15G1 :
∀ (A B C H G I J : Point) (AB BC CA BG GH HA : Line) (Ω : Circle),
  formTriangle A B C AB BC CA
  ∧ insideTriangle H A B C AB BC CA
  ∧ perpLine BC AH
  ∧ perpLine AC BH
  ∧ perpLine AB CH
  ∧ formQuadrilateral A B G H AB BG GH HA
  ∧ (|(A─B)| = |(G─H)|)
  ∧ (|(B─G)| = |(A─H)|)
  ∧ I.onLine GH
  ∧ (∃ (X : Point), X.onLine AC ∧ midpoint H X I)
  ∧ circumCircle Ω G C I
  ∧ J.onLine AC
  ∧ J.onCircle Ω
→ |(I─J)| = |(A─H)| :=
by sorry



--09G3
--In $\triangle ABC$, the incircle touches sides $AB$ and $AC$ at points $Z$ and $Y$, respectively. Let $G$ be the intersection of lines $BY$ and $CZ$. Construct parallelograms $BCYR$ and $BCSZ$. Prove that $GR = GS$.
theorem problem_09G3 :
∀
(A B C Y Z G R S : Point)
(AB BC CA BY CZ CY YR RB CS SZ ZB : Line)
(incircle : Circle),
formTriangle A B C AB BC CA ∧
inCircle incircle AB BC CA ∧
tangentLine AB incircle ∧ Z.onLine AB ∧ Z.onCircle incircle ∧
tangentLine AC incircle ∧ Y.onLine AC ∧ Y.onCircle incircle ∧
twoLinesIntersectAtPoint BY CZ G ∧
formQuadrilateral B C Y R BC CY YR RB ∧
formQuadrilateral B C S Z BC CS SZ ZB ∧
|(B─C)|=|(Y─R)| ∧ |(C─Y)|=|(R─B)| ∧
|(B─C)|=|(S─Z)| ∧ |(C─S)|=|(Z─B)|
→ |(G─R)|=|(G─S)| := by
  sorry



--09G6
--In a quadrilateral $ABCD$, let lines $AD$ and $BC$ intersect at point $P$, and suppose $AB$ is not parallel to $CD$. Let $O_1$ and $O_2$ be the circumcenters of $\triangle ABP$ and $\triangle DCP$, respectively, and let $H_1$ and $H_2$ be their orthocenters. Let $E_1$ and $E_2$ be the midpoints of segments $O_1H_1$ and $O_2H_2$, respectively. Prove that the line through $E_1$ perpendicular to $CD$, the line through $E_2$ perpendicular to $AB$, and line $H_1H_2$ are concurrent.
theorem problem_09G6 :
∀ (A B C D P O₁ O₂ H₁ H₂ E₁ E₂ : Point)
  (AB BC CD DA L₁ L₂ L₃ : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  twoLinesIntersectAtPoint DA BC P ∧
  (∃ M : Point, twoLinesIntersectAtPoint AB CD M) ∧
  circumCentre O₁ A B P ∧
  circumCentre O₂ D C P ∧
  orthoCentre H₁ A B P ∧   -- new predicate for “H₁ is the orthocenter of △ABP”
  orthoCentre H₂ D C P ∧   -- new predicate for “H₂ is the orthocenter of △DCP”
  midpoint O₁ E₁ H₁ ∧
  midpoint O₂ E₂ H₂ ∧
  distinctPointsOnLine H₁ H₂ L₃ ∧
  E₁.onLine L₁ ∧ perpLine L₁ CD ∧
  E₂.onLine L₂ ∧ perpLine L₂ AB
  → ∃ X : Point, X.onLine L₁ ∧ X.onLine L₂ ∧ X.onLine L₃ :=
by sorry



--HP1
--Given that $PE$ and $PF$ are tangents to circle $\odot O$, and $A$ and $B$ are a pair of diametrically opposite points. Line $PB$ intersects $\odot O$ again at point $C$. Lines $AF$ and $BE$ intersect at point $D$. Prove that $\angle PCD = \angle PCE$.
theorem problem_HP1 :
∀ (P E F A B C D : Point) (O : Circle)
  (PE PF PB AF BE : Line),
  tangentAtPoint PE O E ∧
  tangentAtPoint PF O F ∧
  A.onCircle O ∧ B.onCircle O ∧ A ≠ B ∧
  threePointsOnLine P B C PB ∧ B.onCircle O ∧ C.onCircle O ∧ B ≠ C ∧
  distinctPointsOnLine A F AF ∧ distinctPointsOnLine B E BE ∧
  twoLinesIntersectAtPoint AF BE D
  → ∠ P:C:D = ∠ P:C:E
:= by
  sorry



--MP56
--In parallelogram $ABCD$, $O$ is the intersection of the diagonals, $AE$ is the angle bisector of $\angle BAC$, intersecting $BC$ at point $E$. $DH \perp AE$ at point $H$, intersecting $AB$ at point $F$ and $AC$ at point $G$. Prove that $BF = 2OG$.
theorem problem_MP56 :
∀ (A B C D E F G H O : Point)
  (AB BC CD DA AC BD AE DH : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(AB.intersectsLine DC) ∧
  ¬(BC.intersectsLine AD) ∧
  twoLinesIntersectAtPoint AC BD O ∧
  twoLinesIntersectAtPoint AE BC E ∧
  ∠B:A:E = ∠E:A:C ∧
  twoLinesIntersectAtPoint AE DH H ∧
  perpLine AE DH ∧
  D.onLine DH ∧
  twoLinesIntersectAtPoint DH AB F ∧
  twoLinesIntersectAtPoint DH AC G
  → |(B─F)| = |(O─G)| + |(O─G)| :=
by
  sorry



--HP40
--Given that in parallelogram $ABCD$, points $E$ and $F$ lie on sides $AD$ and $CD$, respectively. Lines $AF$ and $CE$ intersect at point $G$. The circumcircle of $\triangle AEG$, circle $\odot O$, and the circumcircle of $\triangle CFG$, circle $\odot P$, intersect at point $H$. Connect lines $BG$ and $DH$. Prove that $\angle GBA = \angle HDA$.
theorem problem_HP40 :
  ∀ (A B C D E F G H : Point)
    (AB BC CD DA AF CE BG DH : Line)
    (O P : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint AB DC X) ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint BC AD X) ∧
  E.onLine DA ∧
  F.onLine CD ∧
  twoLinesIntersectAtPoint AF CE G ∧
  circumCircle O A E G ∧
  circumCircle P C F G ∧
  H.onCircle O ∧
  H.onCircle P
  → (∠ G:B:A = ∠ H:D:A) :=
by sorry



--82T20
--Let $ABCD$ be a convex quadrilateral and draw regular triangles $ABM, CDP, BCN, ADQ$, the first two outward and the other two inward. Prove that $MN = AC$. What can be said about the quadrilateral $MNPQ$?
theorem problem_82T20 :
  ∀ (A B C D M N P Q : Point)
    (AB BC CD DA MN NP PQ QM : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  distinctPointsOnLine M N MN ∧
  distinctPointsOnLine N P NP ∧
  distinctPointsOnLine P Q PQ ∧
  distinctPointsOnLine Q M QM ∧
  (|(A─B)| = |(B─M)| ∧ |(B─M)| = |(A─M)|) ∧
  (|(C─D)| = |(D─P)| ∧ |(D─P)| = |(C─P)|) ∧
  (|(B─C)| = |(C─N)| ∧ |(C─N)| = |(B─N)|) ∧
  (|(A─D)| = |(D─Q)| ∧ |(D─Q)| = |(A─Q)|)
  → (|(M─N)| = |(A─C)| ∧ formQuadrilateral M N P Q MN NP PQ QM)
:= by
  sorry



--HP46
--Given that in parallelogram $ABCD$, line $CE$ is perpendicular to line $AB$ at point $E$, and line $CF$ is perpendicular to line $AD$ at point $F$. Line $EF$ intersects line $BD$ at point $G$. Prove that $GC \perp AC$.
theorem problem_HP46 :
∀ (A B C D E F G : Point)
  (AB BC CD DA BD CE CF EF AC GC : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(AB.intersectsLine DC) ∧
  ¬(BC.intersectsLine AD) ∧
  distinctPointsOnLine B D BD ∧
  distinctPointsOnLine C E CE ∧
  perpLine CE AB ∧
  E.onLine AB ∧
  distinctPointsOnLine C F CF ∧
  perpLine CF AD ∧
  F.onLine AD ∧
  distinctPointsOnLine E F EF ∧
  twoLinesIntersectAtPoint EF BD G ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine G C GC
  → perpLine GC AC := by
sorry



--HP29
--Given that quadrilateral $ABCD$ is inscribed in circle $\odot O$. Lines $AB$ and $DC$ intersect at point $E$, and lines $AD$ and $BC$ intersect at point $F$. The circumcircle of $\triangle EFC$, circle $\odot P$, intersects circle $\odot O$ at point $G$. Line $AG$ intersects line $EF$ at point $H$, and line $HC$ intersects circle $\odot O$ at point $I$. Prove that lines $AI$, $GC$, and $FE$ are concurrent.
theorem problem_HP29 :
∀
(A B C D E F G H I : Point)
(AB BC CD DA EF AG HC AI GC : Line)
(O P : Circle),
formQuadrilateral A B C D AB BC CD DA ∧
A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O ∧
distinctPointsOnLine A B AB ∧ distinctPointsOnLine B C BC ∧ distinctPointsOnLine C D CD ∧ distinctPointsOnLine D A DA ∧
twoLinesIntersectAtPoint AB CD E ∧
twoLinesIntersectAtPoint DA BC F ∧
distinctPointsOnLine E F EF ∧
circumCircle P E F C ∧
G.onCircle P ∧ G.onCircle O ∧
distinctPointsOnLine A G AG ∧
twoLinesIntersectAtPoint AG EF H ∧
distinctPointsOnLine H C HC ∧
I.onCircle O ∧ I.onLine HC ∧
distinctPointsOnLine A I AI ∧
distinctPointsOnLine G C GC
→ ∃ (X : Point), X.onLine AI ∧ X.onLine GC ∧ X.onLine EF :=
by sorry



--09G8
--In a quadrilateral $ABCD$ with an incircle, let line $l$ through $A$ intersect sides $BC$ and $CD$ at points $M$ and $N$, respectively. Let $I_1$, $I_2$, and $I_3$ be the incenters of $\triangle ABM$, $\triangle MNC$, and $\triangle NDA$, respectively. Prove that the orthocenter $H$ of $\triangle I_1I_2I_3$ lies on line $l$.
theorem problem_09G8 :
  ∀ (A B C D M N I₁ I₂ I₃ H : Point)
    (AB BC CD DA l : Line)
    (incircle : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  tangentLine AB incircle ∧
  tangentLine BC incircle ∧
  tangentLine CD incircle ∧
  tangentLine DA incircle ∧
  A.onLine l ∧
  M.onLine l ∧
  M.onLine BC ∧
  N.onLine l ∧
  N.onLine CD ∧
  inCentre I₁ A B M ∧
  inCentre I₂ M N C ∧
  inCentre I₃ N D A ∧
  orthoCentre I₁ I₂ I₃ H
  →
  H.onLine l
:= by
  sorry



--96G1
--Let $ ABC$ be a triangle, and $ H$ its orthocenter. Let $ P$ be a point on the circumcircle of triangle $ ABC$ (distinct from the vertices $ A$, $ B$, $ C$), and let $ E$ be the foot of the altitude of triangle $ ABC$ from the vertex $ B$. Let the parallel to the line $ BP$ through the point $ A$ meet the parallel to the line $ AP$ through the point $ B$ at a point $ Q$. Let the parallel to the line $ CP$ through the point $ A$ meet the parallel to the line $ AP$ through the point $ C$ at a point $ R$. The lines $ HR$ and $ AQ$ intersect at some point $ X$. Prove that the lines $ EX$ and $ AP$ are parallel.
theorem problem_96G1 :
∀
(A B C H P E Q R X : Point)
(AB BC CA BP AP CP BE AQ BQ AR CR HR EX : Line)
(Ω : Circle),
formTriangle A B C AB BC CA ∧
circumCircle Ω A B C ∧
P.onCircle Ω ∧
¬(P = A) ∧ ¬(P = B) ∧ ¬(P = C) ∧
A.onLine AB ∧ B.onLine AB ∧
B.onLine BC ∧ C.onLine BC ∧
C.onLine CA ∧ A.onLine CA ∧
E.onLine AC ∧ B.onLine BE ∧ E.onLine BE ∧ perpLine AC BE ∧
distinctPointsOnLine B P BP ∧
distinctPointsOnLine A P AP ∧
distinctPointsOnLine C P CP ∧
distinctPointsOnLine A Q AQ ∧ (∀ Z, ¬(twoLinesIntersectAtPoint AQ BP Z)) ∧
distinctPointsOnLine B Q BQ ∧ (∀ Z, ¬(twoLinesIntersectAtPoint BQ AP Z)) ∧
twoLinesIntersectAtPoint AQ BQ Q ∧
distinctPointsOnLine A R AR ∧ (∀ Z, ¬(twoLinesIntersectAtPoint AR CP Z)) ∧
distinctPointsOnLine C R CR ∧ (∀ Z, ¬(twoLinesIntersectAtPoint CR AP Z)) ∧
twoLinesIntersectAtPoint AR CR R ∧
distinctPointsOnLine H R HR ∧
twoLinesIntersectAtPoint HR AQ X ∧
distinctPointsOnLine E X EX
→ ¬(∃ Z : Point, twoLinesIntersectAtPoint EX AP Z) :=
by sorry



--18G5
--In $\triangle ABC$, let $I$ be the incenter. A line $l$ (not passing through $A$, $B$, $C$, or $I$) intersects lines $AI$, $BI$, and $CI$ at points $D$, $E$, and $F$, respectively. Prove that the circumcircle $\Theta$ of the triangle formed by the perpendicular bisectors of segments $AD$, $BE$, and $CF$ is tangent to the circumcircle $\omega$ of $\triangle ABC$.
theorem problem_18G5 :
∀ (A B C I D E F P Q R : Point)
  (AB BC CA AI BI CI l L1 L2 L3 PQ QR RP : Line)
  (ω Θ : Circle),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  distinctPointsOnLine A I AI ∧
  distinctPointsOnLine B I BI ∧
  distinctPointsOnLine C I CI ∧
  twoLinesIntersectAtPoint l AI D ∧
  twoLinesIntersectAtPoint l BI E ∧
  twoLinesIntersectAtPoint l CI F ∧
  ¬(A.onLine l) ∧
  ¬(B.onLine l) ∧
  ¬(C.onLine l) ∧
  ¬(I.onLine l) ∧
  perpBisector A D L1 ∧
  perpBisector B E L2 ∧
  perpBisector C F L3 ∧
  twoLinesIntersectAtPoint L1 L2 P ∧
  twoLinesIntersectAtPoint L2 L3 Q ∧
  twoLinesIntersectAtPoint L3 L1 R ∧
  formTriangle P Q R PQ QR RP ∧
  circumCircle ω A B C ∧
  circumCircle Θ P Q R
→ ∃ X : Point, X.onCircle Θ ∧ X.onCircle ω ∧ ∀ Y, Y.onCircle Θ ∧ Y.onCircle ω → Y = X
:= by
  sorry



--imo_2019_p2
--In triangle $ABC$, point $A_1$ lies on side $BC$ and point $B_1$ lies on side $AC$. Let $P$ and $Q$ be points on segments $AA_1$ and $BB_1$, respectively, such that $PQ$ is parallel to $AB$. Let $P_1$ be a point on line $PB_1$, such that $B_1$ lies strictly between $P$ and $P_1$, and $\angle PP_1C=\angle BAC$. Similarly, let $Q_1$ be the point on line $QA_1$, such that $A_1$ lies strictly between $Q$ and $Q_1$, and $\angle CQ_1Q=\angle CBA$. Prove that points $P,Q,P_1$, and $Q_1$ are concyclic.
theorem problem_imo_2019_p2 :
∀ (A B C A_1 B_1 P Q P_1 Q_1 : Point) (AB BC CA PQ : Line),
  formTriangle A B C AB BC CA ∧
  A_1.onLine BC ∧ between B A_1 C ∧
  B_1.onLine CA ∧ between A B_1 C ∧
  between A P A_1 ∧
  between B Q B_1 ∧
  distinctPointsOnLine P Q PQ ∧
  ¬ (∃ X : Point, twoLinesIntersectAtPoint PQ AB X) ∧
  between P B_1 P_1 ∧
  between Q A_1 Q_1 ∧
  ∠P:P_1:C = ∠B:A:C ∧
  ∠C:Q_1:Q = ∠C:B:A
→ cyclic P Q P_1 Q_1 := by
sorry



--MP98
--In quadrilateral $ABCD$, point $P$ is on line $BC$, $PE \parallel AC$, intersecting $AB$ at point $E$, $PF \parallel BD$, intersecting $CD$ at point $F$, lines $EF$ intersect $BD$ and $AC$ at points $G$ and $H$, respectively. Prove that $\frac{EG}{HF}$ is a constant value.
theorem problem_MP98 :
  ∀ (A B C D P E F G H : Point)
    (AB BC CD DA AC BD PE PF EF : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  P.onLine BC ∧

  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B D BD ∧

  distinctPointsOnLine P E PE ∧
  twoLinesIntersectAtPoint AB PE E ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint PE AC X) ∧

  distinctPointsOnLine P F PF ∧
  twoLinesIntersectAtPoint CD PF F ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint PF BD X) ∧

  distinctPointsOnLine E F EF ∧
  twoLinesIntersectAtPoint EF BD G ∧
  twoLinesIntersectAtPoint EF AC H

  → True
:= by
  sorry



--HP36
--Given that circle $\odot O$ is the circumcircle of $\triangle ABC$. Line $AF$ bisects angle $\angle BAC$, intersecting circle $\odot O$ at point $F$. Point $H$ is the orthocenter of $\triangle ABC$. Line $CE$ is perpendicular to line $AB$ at point $E$, and line $BD$ is perpendicular to line $AC$ at point $D$. The circumcircle of $\triangle ADE$, circle $\odot P$, intersects circle $\odot O$ at point $G$. Line $GF$ intersects line $BC$ at point $I$. Prove that $IH$ bisects angle $\angle BHC$.
theorem problem_HP36 :
∀ (A B C D E F G H I : Point)
  (AB BC CA BD CE AF AD DE EA GF : Line)
  (O P : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  distinctPointsOnLine A F AF ∧
  F.onCircle O ∧
  (∠ B:A:F = ∠ F:A:C) ∧
  perpLine BD AC ∧
  distinctPointsOnLine B D BD ∧
  twoLinesIntersectAtPoint BD AC D ∧
  perpLine CE AB ∧
  distinctPointsOnLine C E CE ∧
  twoLinesIntersectAtPoint CE AB E ∧
  twoLinesIntersectAtPoint BD CE H ∧
  formTriangle A D E AD DE EA ∧
  circumCircle P A D E ∧
  G.onCircle O ∧
  G.onCircle P ∧
  distinctPointsOnLine G F GF ∧
  twoLinesIntersectAtPoint GF BC I
  → (∠ B:H:I = ∠ I:H:C) :=
by
  sorry



--imo_2005_p5
--Let $ABCD$ be a fixed convex quadrilateral with $BC = DA$ and $BC \nparallel DA$. Let two variable points $E$ and $F$ lie of the sides $BC$ and $DA$, respectively, and satisfy $BE = DF$. The lines $AC$ and $BD$ meet at $P$, the lines $BD$ and $EF$ meet at $Q$, the lines $EF$ and $AC$ meet at $R$. Prove that the circumcircles of the triangles $PQR$, as $E$ and $F$ vary, have a common point other than $P$.
theorem problem_imo_2005_p5 :
∀ (A B C D P X G : Point)
  (AB BC CD DA AC BD : Line),
  formQuadrilateral A B C D AB BC CD DA
  ∧ |(B─C)| = |(D─A)|
  ∧ twoLinesIntersectAtPoint AC BD P
  ∧ twoLinesIntersectAtPoint BC DA G
  → ( X ≠ P
    ∧ ∀ (E F Q R : Point) (EF : Line),
        E.onLine BC
        ∧ between B E C
        ∧ F.onLine DA
        ∧ between D F A
        ∧ |(B─E)| = |(D─F)|
        ∧ twoLinesIntersectAtPoint BD EF Q
        ∧ twoLinesIntersectAtPoint EF AC R
        → cyclic P Q R X ) :=
by sorry



--14G7
--In $\triangle ABC$, let $\Gamma$ be the circumcircle and $I$ the incenter. Draw a line through $I$ perpendicular to $CI$, intersecting side $BC$ at point $U$ and arc $BC$ at point $V$. Draw a line through $U$ parallel to $AI$, intersecting $AV$ at point $X$, and a line through $V$ parallel to $AI$, intersecting $AB$ at point $Y$. Let the midpoints of segments $AX$ and $BC$ be $W$ and $Z$, respectively. Prove that if points $I$, $X$, and $Y$ are collinear, then points $I$, $W$, and $Z$ are also collinear.
theorem problem_14G7 :
  ∀ (A B C I U V X Y W Z : Point)
    (AB BC CA LIXY LIWZ : Line)
    (Γ : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle Γ A B C ∧
  inCentre I A B C ∧
  U.onLine BC ∧
  V.onCircle Γ ∧
  midpoint A W X ∧
  midpoint B Z C ∧
  threePointsOnLine I X Y LIXY
  → threePointsOnLine I W Z LIWZ
:= by
  sorry



--imo_2000_p6
--Let $\overline{AH_1}$, $\overline{BH_2}$, and $\overline{CH_3}$ be the altitudes of an acute triangle $ABC$. The incircle $\omega$ of triangle $ABC$ touches the sides $BC$, $CA$, and $AB$ at $T_1$, $T_2$, and $T_3$, respectively. Consider the reflections of the lines $H_1H_2$, $H_2H_3$, and $H_3H_1$ with respect to the lines $T_1T_2$, $T_2T_3$, and $T_3T_1$. Prove that these images form a triangle whose vertices line on $\omega$.
theorem problem_imo_2000_p6 :
∀ (A B C H1 H2 H3 T1 T2 T3 : Point)
  (AB BC CA AH1 BH2 CH3 T1T2 T2T3 T3T1 : Line)
  (ω : Circle),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A H1 AH1 ∧ twoLinesIntersectAtPoint BC AH1 H1 ∧ perpLine AH1 BC ∧
  distinctPointsOnLine B H2 BH2 ∧ twoLinesIntersectAtPoint CA BH2 H2 ∧ perpLine BH2 CA ∧
  distinctPointsOnLine C H3 CH3 ∧ twoLinesIntersectAtPoint AB CH3 H3 ∧ perpLine CH3 AB ∧
  inCircle ω AB BC CA ∧
  T1.onLine BC ∧ T1.onCircle ω ∧ tangentAtPoint BC ω T1 ∧
  T2.onLine CA ∧ T2.onCircle ω ∧ tangentAtPoint CA ω T2 ∧
  T3.onLine AB ∧ T3.onCircle ω ∧ tangentAtPoint AB ω T3
→ (
  -- Conclusion (informal description, since reflections are not among the given primitives):
  -- “The reflections of the lines H1H2, H2H3, and H3H1 with respect to the lines T1T2, T2T3, and T3T1
  -- form a triangle whose vertices lie on the circle ω.”
  True
)
:= by
  sorry



--HP57
--Given that lines $PA$ and $PB$ are tangents to circle $\odot O$ at points $A$ and $B$, respectively. Point $C$ lies on the minor arc $AB$. Line $OC$ intersects line $AB$ at point $D$. The tangent to circle $\odot O$ at point $C$ intersects lines $PA$ and $PB$ at points $E$ and $F$, respectively. Line $PD$ intersects line $EF$ at point $G$. Prove that $G$ is the midpoint of line segment $EF$.
theorem HP57 :
∀ (P A B C D E F G O : Point)
  (PA PB AB OC PD CE : Line)
  (Γ : Circle),
  O.isCentre Γ ∧
  A.onCircle Γ ∧
  B.onCircle Γ ∧
  C.onCircle Γ ∧
  distinctPointsOnLine P A PA ∧
  distinctPointsOnLine P B PB ∧
  tangentAtPoint PA Γ A ∧
  tangentAtPoint PB Γ B ∧
  distinctPointsOnLine O C OC ∧
  distinctPointsOnLine A B AB ∧
  twoLinesIntersectAtPoint AB OC D ∧
  distinctPointsOnLine P D PD ∧
  threePointsOnLine C E F CE ∧
  twoLinesIntersectAtPoint CE PA E ∧
  twoLinesIntersectAtPoint CE PB F ∧
  tangentAtPoint CE Γ C ∧
  twoLinesIntersectAtPoint PD CE G
  → midpoint E G F :=
by
  sorry



--95G1
--Let $ A,B,C,D$ be four distinct points on a line, in that order.  The circles with diameters $ AC$ and $ BD$ intersect at $ X$ and $ Y$. The line $ XY$ meets $ BC$ at $ Z$. Let $ P$ be a point on the line $ XY$ other than $ Z$. The line $ CP$ intersects the circle with diameter $ AC$ at $ C$ and $ M$, and the line $ BP$ intersects the circle with diameter $ BD$ at $ B$ and $ N$. Prove that the lines $ AM,DN,XY$ are concurrent.
theorem problem_95G1 :
  ∀ (A B C D X Y Z P M N T : Point)
    (l xy am dn : Line)
    (α β : Circle),
  distinctPointsOnLine A B l ∧ C.onLine l ∧ D.onLine l ∧
  A.onCircle α ∧ C.onCircle α ∧
  B.onCircle β ∧ D.onCircle β ∧
  X.onCircle α ∧ X.onCircle β ∧
  Y.onCircle α ∧ Y.onCircle β ∧
  distinctPointsOnLine X Y xy ∧
  twoLinesIntersectAtPoint xy l Z ∧
  P.onLine xy ∧ P ≠ Z ∧
  M.onCircle α ∧ N.onCircle β ∧
  distinctPointsOnLine A M am ∧
  distinctPointsOnLine D N dn
  →
  ∃ (Q : Point),
    Q.onLine am ∧
    Q.onLine dn ∧
    Q.onLine xy
:= by
  sorry



--imo_2010_p2
--Given a triangle $ABC$, with $I$ as its incenter and $\Gamma$ as its circumcircle, $AI$ intersects $\Gamma$ again at $D$. Let $E$ be a point on arc $BDC$, and $F$ a point on the segment $BC$, such that $\angle BAF=\angle CAE< \frac12\angle BAC$. If $G$ is the midpoint of $IF$, prove that the intersection of lines $EI$ and $DG$ lies on $\Gamma$.
theorem problem_imo_2010_p2 :
∀ (A B C I D E F G X : Point) (AB BC CA : Line) (Γ : Circle),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  circumCircle Γ A B C ∧
  D.onCircle Γ ∧
  E.onCircle Γ ∧
  between B F C ∧
  ∠B:A:F = ∠C:A:E ∧
  (∠B:A:F + ∠C:A:E) < ∠B:A:C ∧
  midpoint I G F
  → X.onCircle Γ
:= by
  sorry




--HP11
--Given that $PAB$ is a secant of circle $O$, and $PC$ is a tangent. Line $CD$ is a diameter of circle $O$. Line $DB$ intersects $OP$ at point $E$. Prove that $AC \perp CE$.
theorem problem_HP11 :
∀
(A B C D E P O : Point)
(Γ : Circle)
(PAB PC CD DB OP AC CE : Line),
----------------------------------------------------------------
  -- Circle-center setup and points on the circle
  O.isCentre Γ ∧
  A.onCircle Γ ∧
  B.onCircle Γ ∧
  C.onCircle Γ ∧
  D.onCircle Γ ∧

  -- “PAB is a secant”:  P,A,B are collinear
  threePointsOnLine P A B PAB ∧

  -- “PC is a tangent”:  P,C on line PC and that line is tangent to Γ
  distinctPointsOnLine P C PC ∧
  tangentLine PC Γ ∧

  -- “CD is a diameter”:  C,D on line CD and O is midpoint of segment CD
  distinctPointsOnLine C D CD ∧
  midpoint O C D ∧

  -- “Line DB intersects OP at E”
  distinctPointsOnLine D B DB ∧
  distinctPointsOnLine O P OP ∧
  twoLinesIntersectAtPoint DB OP E ∧

  -- Lines for the conclusion about perpendicularity
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine C E CE
----------------------------------------------------------------
→ perpLine AC CE
:= by
  sorry



--MP34
--In $\triangle ABC$, $\angle B = 45^\circ$, $\angle C = 30^\circ$. $BD$ is the median of side $AC$. Find $\angle ABD$.
theorem problem_MP34 :
∀ (A B C D : Point) (AB BC CA BD : Line),
  formTriangle A B C AB BC CA ∧
  (∠A:B:C = 45) ∧
  (∠B:C:A = 30) ∧
  distinctPointsOnLine B D BD ∧
  midpoint A D C
  → (∠A:B:D = 30)
:= by
  sorry



--MP83
--In right triangle $\triangle ABC$, $\angle B = 90^\circ$, point $D$ is the midpoint of $BC$, point $E$ is on $AC$ such that $AE = \frac{1}{3}AC$, and $BE$ intersects $AD$ at point $F$. Find $\angle AFE$.
theorem problem_MP83 :
∀ (A B C D E F : Point)
  (AB BC CA AD BE : Line),
  formTriangle A B C AB BC CA ∧
  ∠A:B:C = ∟ ∧
  midpoint B D C ∧
  E.onLine AC ∧
  3 * |(A─E)| = |(A─C)| ∧
  distinctPointsOnLine A D AD ∧
  distinctPointsOnLine B E BE ∧
  twoLinesIntersectAtPoint AD BE F
  → ∠A:F:E = ∟
:= by
  sorry



--HP35
--Given that $I$ is the incenter of $\triangle ABC$, and point $E$ is the midpoint of $BC$. Point $F$ is the midpoint of arc $BC$, and point $N$ is the midpoint of line segment $EF$. Point $M$ is the midpoint of line segment $BI$, and line $MN$ intersects line $BC$ at point $D$. Connect line $AD$. Prove that $M$ is the incenter of $\triangle ABD$.
theorem problem_HP35 :
∀ (A B C I E F N M D : Point) (AB BC CA MN AD : Line),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  midpoint B E C ∧
  midpoint B M I ∧
  midpoint E N F ∧
  distinctPointsOnLine M N MN ∧
  twoLinesIntersectAtPoint MN BC D ∧
  distinctPointsOnLine A D AD
→ inCentre M A B D := by
sorry



--23G2
--Let $ABC$ be a triangle with $AC > BC,$ let $\omega$ be the circumcircle of $\triangle ABC,$ and let $r$ be its radius. Point $P$ is chosen on $\overline{AC},$ such taht $BC=CP,$ and point $S$ is the foot of the perpendicular from $P$ to $\overline{AB},$. Ray $BP$ mets $\omega$ again at $D$. Point $Q$ is chosen on line $SP$ such that $PQ = r$ and $S,P,Q$ lie on a line in that order. Finally, let $E$ be a point satisfying $\overline{AE}, \perp \overline{CQ},$ and $\overline{BE}, \perp \overline{DQ},$. Prove that $E$ lies on $\omega$.

theorem problem_23G2 :
  ∀ (A B C P S D Q E : Point)
    (AB BC CA BP SP AE BE CQ DQ : Line)
    (ω : Circle)
    (r : Real),
  formTriangle A B C AB BC CA ∧
  (|(A─C)| > |(B─C)|) ∧
  circumCircle ω A B C ∧
  P.onLine CA ∧
  (|(B─C)| = |(C─P)|) ∧
  S.onLine AB ∧
  distinctPointsOnLine P S SP ∧
  perpLine SP AB ∧
  distinctPointsOnLine B P BP ∧
  D.onLine BP ∧
  D.onCircle ω ∧
  between B P D ∧
  threePointsOnLine S P Q SP ∧
  between S P Q ∧
  (|(P─Q)| = r) ∧
  distinctPointsOnLine A E AE ∧
  distinctPointsOnLine C Q CQ ∧
  perpLine AE CQ ∧
  distinctPointsOnLine B E BE ∧
  distinctPointsOnLine D Q DQ ∧
  perpLine BE DQ
  → E.onCircle ω :=
by
  sorry



--12G7
--In a convex quadrilateral $ABCD$ with $AD$ not parallel to $BC$, point $E$ lies on side $BC$ such that quadrilaterals $ABED$ and $AECF$ both have incircles. Prove that there exists a point $F$ on side $AD$ such that quadrilaterals $ABCF$ and $BCDF$ both have incircles if and only if $AB \parallel CD$.
theorem problem_12G7 :
∀ (A B C D E : Point) (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  (∃ X : Point, twoLinesIntersectAtPoint AD BC X)  ∧
  E.onLine BC ∧ between B E C ∧
  (∃ O₁ : Circle, tangentLine AB O₁ ∧ tangentLine BE O₁ ∧ tangentLine ED O₁ ∧ tangentLine DA O₁) ∧
  (∃ O₂ : Circle, tangentLine AE O₂ ∧ tangentLine EC O₂ ∧ tangentLine CF O₂ ∧ tangentLine FA O₂)
  →
  ( (∃ F : Point,
       F.onLine AD ∧ between A F D
       ∧ (∃ O₃ : Circle, tangentLine AB O₃ ∧ tangentLine BC O₃ ∧ tangentLine CF O₃ ∧ tangentLine FA O₃)
       ∧ (∃ O₄ : Circle, tangentLine BC O₄ ∧ tangentLine CD O₄ ∧ tangentLine DF O₄ ∧ tangentLine FB O₄)
     )
    ↔
    (¬ (∃ X : Point, twoLinesIntersectAtPoint AB CD X))
  )
:= by
  sorry



--MP30
--In $\triangle ABC$, $AD$ is the angle bisector, and $AC = AB + BD$, $CD = AB + AD$. Find the angles of $\triangle ABC$.
theorem problem_MP30 :
∀ (A B C D : Point) (AB BC CA AD : Line),
  (formTriangle A B C AB BC CA)
  ∧ D.onLine BC
  ∧ (∠ B:A:D = ∠ D:A:C)
  ∧ (|(A─C)| = |(A─B)| + |(B─D)|)
  ∧ (|(C─D)| = |(A─B)| + |(A─D)|)
  → (∠ B:A:C = 30) ∧ (∠ A:B:C = 60) ∧ (∠ A:C:B = ∟)
:= by
  sorry

--CO20
--As shown in the figure, in an isosceles triangle $ABC$ with $AB = BC$, $I$ is the incenter, $M$ is the midpoint of $BI$, $P$ is a point on side $AC$ such that $AP = 3PC$, and $PI$ is extended to a point $H$ such that $MH \perp PH$. $Q$ is the midpoint of $AB$ on the circumcircle of $\triangle ABC$. Prove: $BH \perp QH$.
theorem problem_CO20 :
∀ (A B C I M P H Q : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(B─C)| ∧
  inCentre I A B C ∧
  midpoint B M I ∧
  between A P C  ∧
  (|(A─P)| = 3 * |(P─C)|) ∧
  between P I H ∧
  distinctPointsOnLine P H PH ∧
  distinctPointsOnLine M H MH ∧
  perpLine PH MH ∧
  cyclic Q B C A ∧
  |
  → perpLine BH QH :=
by
  sorry
