/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Projection

/-!
# Oriented angles and orthogonal projection.

This file proves lemmas relating to oriented angles involving orthogonal projections.

-/

public section


namespace EuclideanGeometry

open Module
open scoped Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
variable [NormedAddTorsor V P] [hd2 : Fact (finrank Real V = 2)] [Module.Oriented Real V (Fin 2)]

/--
lemma `oangle_self_orthogonalProjection` / 引理 `oangle_self_orthogonalProjection`

English:
lemma oangle_self_orthogonalProjection
  statement: (p : P) {p' : P} {s : AffineSubspace Real P}
  proof: ⟨p', h⟩
    ∡ p (orthogonalProjection s p) p' = (π / 2 : Real) ∨
      ∡ p (orthogonalProjection s p) p' = (-π / 2 : Real) := by
  have : Nonempty s := ⟨p', h⟩
  have hpne : p != orthogonalProjection s p := Ne.symm (orthogonalProjection_eq_self_iff.not.2 hp)
  have ha := oangle_eq_angle_or_eq_neg_an

中文:
引理 oangle_self_orthogonalProjection
  结论: (p : P) {p' : P} {s : AffineSubspace 实数 P}
  证明: ⟨p', h⟩
    ∡ p (orthogonalProjection s p) p' = (π / 2 : Real) ∨
      ∡ p (orthogonalProjection s p) p' = (-π / 2 : Real) := by
  have : Nonempty s := ⟨p', h⟩
  have hpne : p != orthogonalProjection s p := Ne.symm (orthogonalProjection_eq_self_iff.not.2 hp)
  have ha := oangle_eq_angle_or_eq_neg_an

Depends on / 依赖: orthogonalProjection
-/
lemma oangle_self_orthogonalProjection (p : P) {p' : P} {s : AffineSubspace Real P}
    [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' in s)
    (hp' : haveI : Nonempty s := ⟨p', h⟩; p' != orthogonalProjection s p) :
    haveI : Nonempty s := ⟨p', h⟩
    ∡ p (orthogonalProjection s p) p' = (π / 2 : Real) ∨
      ∡ p (orthogonalProjection s p) p' = (-π / 2 : Real) := by
  have : Nonempty s := ⟨p', h⟩
  have hpne : p != orthogonalProjection s p := Ne.symm (orthogonalProjection_eq_self_iff.not.2 hp)
  have ha := oangle_eq_angle_or_eq_neg_angle hpne hp'
  rw [angle_self_orthogonalProjection p h] at ha
  rwa [neg_div]

/--
lemma `oangle_orthogonalProjection_self` / 引理 `oangle_orthogonalProjection_self`

English:
lemma oangle_orthogonalProjection_self
  statement: (p : P) {p' : P} {s : AffineSubspace Real P}
  proof: ⟨p', h⟩
    ∡ p' (orthogonalProjection s p) p = (π / 2 : Real) ∨
      ∡ p' (orthogonalProjection s p) p = (-π / 2 : Real) := by
  rw [oangle_rev]; rw [neg_eq_iff_eq_neg]; rw [neg_eq_iff_eq_neg]; rw [or_comm]; rw [← Real.Angle.coe_neg]; rw [neg_div]; rw [neg_neg]; rw [← Real.Angle.coe_neg]; rw [← ne

中文:
引理 oangle_orthogonalProjection_self
  结论: (p : P) {p' : P} {s : AffineSubspace 实数 P}
  证明: ⟨p', h⟩
    ∡ p' (orthogonalProjection s p) p = (π / 2 : Real) ∨
      ∡ p' (orthogonalProjection s p) p = (-π / 2 : Real) := by
  rw [oangle_rev]; rw [neg_eq_iff_eq_neg]; rw [neg_eq_iff_eq_neg]; rw [or_comm]; rw [← Real.Angle.coe_neg]; rw [neg_div]; rw [neg_neg]; rw [← Real.Angle.coe_neg]; rw [← ne

Depends on / 依赖: orthogonalProjection
-/
lemma oangle_orthogonalProjection_self (p : P) {p' : P} {s : AffineSubspace Real P}
    [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' in s)
    (hp' : haveI : Nonempty s := ⟨p', h⟩; p' != orthogonalProjection s p) :
    haveI : Nonempty s := ⟨p', h⟩
    ∡ p' (orthogonalProjection s p) p = (π / 2 : Real) ∨
      ∡ p' (orthogonalProjection s p) p = (-π / 2 : Real) := by
  rw [oangle_rev]; rw [neg_eq_iff_eq_neg]; rw [neg_eq_iff_eq_neg]; rw [or_comm]; rw [← Real.Angle.coe_neg]; rw [neg_div]; rw [neg_neg]; rw [← Real.Angle.coe_neg]; rw [← neg_div]
  exact oangle_self_orthogonalProjection p hp h hp'

/--
lemma `two_zsmul_oangle_self_orthogonalProjection` / 引理 `two_zsmul_oangle_self_orthogonalProjection`

English:
lemma two_zsmul_oangle_self_orthogonalProjection
  statement: (p : P) {p' : P} {s : AffineSubspace Real P}
  proof: ⟨p', h⟩
    (2 : Int) • ∡ p (orthogonalProjection s p) p' = π := by
  rw [Real.Angle.two_zsmul_eq_pi_iff]
  exact oangle_self_orthogonalProjection p hp h hp'

中文:
引理 two_zsmul_oangle_self_orthogonalProjection
  结论: (p : P) {p' : P} {s : AffineSubspace 实数 P}
  证明: ⟨p', h⟩
    (2 : Int) • ∡ p (orthogonalProjection s p) p' = π := by
  rw [Real.Angle.two_zsmul_eq_pi_iff]
  exact oangle_self_orthogonalProjection p hp h hp'

Depends on / 依赖: orthogonalProjection
-/
lemma two_zsmul_oangle_self_orthogonalProjection (p : P) {p' : P} {s : AffineSubspace Real P}
    [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' in s)
    (hp' : haveI : Nonempty s := ⟨p', h⟩; p' != orthogonalProjection s p) :
    haveI : Nonempty s := ⟨p', h⟩
    (2 : Int) • ∡ p (orthogonalProjection s p) p' = π := by
  rw [Real.Angle.two_zsmul_eq_pi_iff]
  exact oangle_self_orthogonalProjection p hp h hp'

/--
lemma `two_zsmul_oangle_orthogonalProjection_self` / 引理 `two_zsmul_oangle_orthogonalProjection_self`

English:
lemma two_zsmul_oangle_orthogonalProjection_self
  statement: (p : P) {p' : P} {s : AffineSubspace Real P}
  proof: ⟨p', h⟩
    (2 : Int) • ∡ p' (orthogonalProjection s p) p = π := by
  rw [Real.Angle.two_zsmul_eq_pi_iff]
  exact oangle_orthogonalProjection_self p hp h hp'

中文:
引理 two_zsmul_oangle_orthogonalProjection_self
  结论: (p : P) {p' : P} {s : AffineSubspace 实数 P}
  证明: ⟨p', h⟩
    (2 : Int) • ∡ p' (orthogonalProjection s p) p = π := by
  rw [Real.Angle.two_zsmul_eq_pi_iff]
  exact oangle_orthogonalProjection_self p hp h hp'

Depends on / 依赖: orthogonalProjection
-/
lemma two_zsmul_oangle_orthogonalProjection_self (p : P) {p' : P} {s : AffineSubspace Real P}
    [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' in s)
    (hp' : haveI : Nonempty s := ⟨p', h⟩; p' != orthogonalProjection s p) :
    haveI : Nonempty s := ⟨p', h⟩
    (2 : Int) • ∡ p' (orthogonalProjection s p) p = π := by
  rw [Real.Angle.two_zsmul_eq_pi_iff]
  exact oangle_orthogonalProjection_self p hp h hp'

end EuclideanGeometry
