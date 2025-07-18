# LeanGeo: Core Geometry Theorems Library

This directory contains the foundational geometry theorems and definitions used throughout the LeanEuclid project. It provides a comprehensive collection of geometric results, from basic angle relationships to advanced triangle theorems and quadrilateral properties.

## File Structure

### Core Files
- **Abbre.lean**: Abbreviations and common geometric definitions
- **Theorem.lean**: Main theorems organized by geometric topic
- **extract.py**: Python utility for extracting theorem data to JSON
- **extracted_data.json**: Generated data file containing theorem information

### Theorem Categories

#### Angle.lean
Fundamental angle relationships and properties:
- Angle coinciding with zero when points are identical
- Supplementary angles on straight lines
- Angle bisector theorems
- Opposite angles and transversal relationships
- Betweenness conditions for angles

#### Basic.lean
Core geometric axioms and basic theorems:
- Triangle inequality (strict and non-strict forms)
- Line ratio uniqueness
- Collinearity conditions
- Basic point-line relationships

#### BookTheorem.lean
Euclid's Elements propositions and related theorems:
- SAS, SSS, AAS congruence criteria
- Pythagorean theorem and its converse
- Parallelogram properties and area relationships
- Triangle construction theorems
- Midpoint existence theorems
- Parallel line properties and transversal theorems

#### Additional Theorem Files
- **Area.lean**: Area calculations and relationships
- **Circle.lean**: Circle theorems and properties
- **CirclePosition.lean**: Point-circle and line-circle relationships
- **CircumCenter.lean**: Circumcenter properties and constructions
- **Construction.lean**: Geometric construction theorems
- **Miquel.lean**: Miquel's theorem and related results
- **OrthoCenter.lean**: Orthocenter properties
- **Parallel.lean**: Parallel line theorems
- **PerpBisector.lean**: Perpendicular bisector properties
- **Position.lean**: Point positioning relationships
- **Quadrilateral.lean**: Quadrilateral theorems and properties
- **Triangle.lean**: Triangle-specific theorems
- **TriangleCenter.lean**: Triangle centers (centroid, incenter, etc.)
- **Trigonometry.lean**: Trigonometric relationships in geometry

## Key Abbreviations (from Abbre.lean)

### Basic Concepts
- `triangle A B C`: Non-collinear points forming a triangle
- `coll A B C`: Collinearity condition
- `midpoint A P B`: P is the midpoint of segment AB
- `perpLine L M`: Lines L and M are perpendicular
- `foot A B l`: B is the foot of perpendicular from A to line l

### Triangle Types
- `acuteTriangle A B C`: All angles less than 90°
- `isoTriangle A B C`: Isosceles triangle with |AB| = |AC|
- `rightTriangle A B C`: Right-angled triangle

### Quadrilaterals
- `parallelogram A B C D`: Standard parallelogram
- `rectangle A B C D`: Rectangle with all angles 90°
- `rhombus A B C D`: Rhombus with all sides equal
- `square A B C D`: Square with equal sides and 90° angles
- `trapezoid A B C D`: Trapezoid with one pair of parallel sides

### Centers and Circles
- `circumCentre O A B C`: O is equidistant from A, B, C
- `inCentre I A B C`: I is the incenter of triangle ABC
- `circumCircle Ω A B C`: Circle through three points
- `cyclic A B C D`: Four points lie on a common circle

## Notation Guide

### Geometric Objects
- **Points**: Capital letters (A, B, C, ...)
- **Lines**: Capital letters with optional segment notation (AB, BC, ...)
- **Circles**: Greek letters (Ω, O, ...)

### Measurements
- `|A─B|`: Distance between points A and B
- `∠A:B:C`: Angle at vertex B with rays BA and BC
- `∟`: Right angle (90 degrees)

### Relationships
- `.onLine l`: Point lies on line l
- `.onCircle C`: Point lies on circle C
- `.sameSide P l`: Point is on the same side of line l as point P
- `.opposingSides P l`: Point is on the opposite side of line l from point P

## Usage Examples

### Basic Theorem Usage
```lean
theorem angle_coincide_zero : ∀ (a o : Point), (a ≠ o) → ∠a:o:a = 0
```

### Triangle Congruence
```lean
theorem congruentTriangle (A B C D E F: Point) : Prop :=
  triangle A B C ∧ triangle D E F ∧ 
  |(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(A─C)| = |(D─F)| ∧
  ∠A:B:C = ∠D:E:F ∧ ∠B:A:C = ∠E:D:F ∧ ∠A:C:B = ∠D:F:E
```

### Construction Theorems
Many theorems provide existence results for geometric constructions:
- `Book_exists_eqTriangle`: Construct equilateral triangle on segment
- `Book_exists_midPoint`: Find midpoint of segment
- `Book_exists_angle_bisector`: Construct angle bisector

## Proof Style

The theorems use the SystemE formal system with tactics:
- `euclid_intros`: Introduction of geometric objects
- `euclid_apply`: Apply geometric constructions
- `euclid_finish`: Automated proof completion using SMT solvers
- `euclid_assert`: State intermediate geometric facts

## Data Extraction

The `extract.py` script processes Lean files to extract:
- Theorem names and formal statements
- Proof states (complete, with sorry, etc.)
- Used lemmas and dependencies
- Source file locations

Run with:
```bash
python extract.py
```

This generates `extracted_data.json` containing structured theorem information for analysis and external tools.