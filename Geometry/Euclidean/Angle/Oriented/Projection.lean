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

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-
**EuclideanGeometry.oangle_self_orthogonalProjection** 是 Mathlib 中的一个引理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：oangle_self_orthogonalProjection (p : P) {p' : P} {s : AffineSubspace Real
 P} [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' in s) (hp' : have
I : Nonempty s
参数：p : P；hp : p ∉ s；h : p' in s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `EuclideanGeometry.orthogonalProjection_eq_self_iff`：orthogonalProjection
_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalPro
jection] {p : P} : ↑(orthogonalProjectio…
· 使用定理 `EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle`：oangle_eq_angle_or_eq
_neg_angle {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) : ∡ p₁ p p₂ = ∠ p₁ p p₂
 ∨ ∡ p₁ p p₂ = -∠ p₁ p p₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `EuclideanGeometry.angle_self_orthogonalProjection`：∀ {V : Type u_1} {P :
 Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_
2 : MetricSpace P]   [inst_3 : NormedAd…
-/
lemma oangle_self_orthogonalProjection (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' ∈ s)
    (hp' : haveI : Nonempty s := ⟨p', h⟩; p' ≠ orthogonalProjection s p) :
    haveI : Nonempty s := ⟨p', h⟩
    ∡ p (orthogonalProjection s p) p' = (π / 2 : ℝ) ∨
      ∡ p (orthogonalProjection s p) p' = (-π / 2 : ℝ) := by
  have : Nonempty s := ⟨p', h⟩
  have hpne : p ≠ orthogonalProjection s p := Ne.symm (orthogonalProjection_eq_self_iff.not.2 hp)
  have ha := oangle_eq_angle_or_eq_neg_angle hpne hp'
  rw [angle_self_orthogonalProjection p h] at ha
  rwa [neg_div]
/-
**EuclideanGeometry.oangle_orthogonalProjection_self** 是 Mathlib 中的一个引理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：oangle_orthogonalProjection_self (p : P) {p' : P} {s : AffineSubspace Real
 P} [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' in s) (hp' : have
I : Nonempty s
参数：p : P；hp : p ∉ s；h : p' in s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rev`：oangle_rev (p₁ p₂ p₃ : P) : ∡ p₃ p₂ p₁ = -
∡ p₁ p₂ p₃
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.coe_neg`：coe_neg (x : Real) : ↑(-x : Real) = -(↑x : Angle)
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `EuclideanGeometry.oangle_self_orthogonalProjection`：oangle_self_orthogon
alProjection (p : P) {p' : P} {s : AffineSubspace Real P} [s.direction.HasOrthog
onalProjection] (hp : p ∉ s) (h : p' in …
-/
lemma oangle_orthogonalProjection_self (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' ∈ s)
    (hp' : haveI : Nonempty s := ⟨p', h⟩; p' ≠ orthogonalProjection s p) :
    haveI : Nonempty s := ⟨p', h⟩
    ∡ p' (orthogonalProjection s p) p = (π / 2 : ℝ) ∨
      ∡ p' (orthogonalProjection s p) p = (-π / 2 : ℝ) := by
  rw [oangle_rev, neg_eq_iff_eq_neg, neg_eq_iff_eq_neg, or_comm, ← Real.Angle.coe_neg, neg_div,
    neg_neg, ← Real.Angle.coe_neg, ← neg_div]
  exact oangle_self_orthogonalProjection p hp h hp'
/-
**EuclideanGeometry.two_zsmul_oangle_self_orthogonalProjection** 是 Mathlib 中的一个引
理，位于命名空间 `EuclideanGeometry`。
形式化陈述：two_zsmul_oangle_self_orthogonalProjection (p : P) {p' : P} {s : AffineSub
space Real P} [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' in s) (
hp' : haveI : Nonempty s
参数：p : P；hp : p ∉ s；h : p' in s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.two_zsmul_eq_pi_iff`：two_zsmul_eq_pi_iff {θ : Angle} : (2 : I
nt) • θ = π ↔ θ = (π / 2 : Real) ∨ θ = (-π / 2 : Real)
· 使用引理 `EuclideanGeometry.oangle_self_orthogonalProjection`：oangle_self_orthogon
alProjection (p : P) {p' : P} {s : AffineSubspace Real P} [s.direction.HasOrthog
onalProjection] (hp : p ∉ s) (h : p' in …
-/
lemma two_zsmul_oangle_self_orthogonalProjection (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' ∈ s)
    (hp' : haveI : Nonempty s := ⟨p', h⟩; p' ≠ orthogonalProjection s p) :
    haveI : Nonempty s := ⟨p', h⟩
    (2 : ℤ) • ∡ p (orthogonalProjection s p) p' = π := by
  rw [Real.Angle.two_zsmul_eq_pi_iff]
  exact oangle_self_orthogonalProjection p hp h hp'
/-
**EuclideanGeometry.two_zsmul_oangle_orthogonalProjection_self** 是 Mathlib 中的一个引
理，位于命名空间 `EuclideanGeometry`。
形式化陈述：two_zsmul_oangle_orthogonalProjection_self (p : P) {p' : P} {s : AffineSub
space Real P} [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' in s) (
hp' : haveI : Nonempty s
参数：p : P；hp : p ∉ s；h : p' in s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.two_zsmul_eq_pi_iff`：two_zsmul_eq_pi_iff {θ : Angle} : (2 : I
nt) • θ = π ↔ θ = (π / 2 : Real) ∨ θ = (-π / 2 : Real)
· 使用引理 `EuclideanGeometry.oangle_orthogonalProjection_self`：oangle_orthogonalPro
jection_self (p : P) {p' : P} {s : AffineSubspace Real P} [s.direction.HasOrthog
onalProjection] (hp : p ∉ s) (h : p' in …
-/
lemma two_zsmul_oangle_orthogonalProjection_self (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (hp : p ∉ s) (h : p' ∈ s)
    (hp' : haveI : Nonempty s := ⟨p', h⟩; p' ≠ orthogonalProjection s p) :
    haveI : Nonempty s := ⟨p', h⟩
    (2 : ℤ) • ∡ p' (orthogonalProjection s p) p = π := by
  rw [Real.Angle.two_zsmul_eq_pi_iff]
  exact oangle_orthogonalProjection_self p hp h hp'

end EuclideanGeometry

