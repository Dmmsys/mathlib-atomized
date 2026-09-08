/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Projection

/-!
# Angle bisectors.

This file proves lemmas relating to bisecting angles.

-/

public section


namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

/-- Auxiliary lemma for the degenerate case of `dist_orthogonalProjection_eq_iff_angle_eq` where
`p` lies in `s₁`. -/
/-
**EuclideanGeometry.dist_orthogonalProjection_eq_iff_angle_eq_aux** 是 Mathlib 中的
一个引理，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for the degenerate case of `dist_orthogonalProjection_eq_iff_ang
le_eq` where
`p` lies in `s₁`.
-/
private lemma dist_orthogonalProjection_eq_iff_angle_eq_aux₁ {p p' : P}
    {s₁ s₂ : AffineSubspace ℝ P}
    [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (hp'₁ : p' ∈ s₁) (hp'₂ : p' ∈ s₂) (h' : p ∈ s₁) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [orthogonalProjection_eq_self_iff.2 h'] at h ⊢
    rw [dist_self, zero_eq_dist, eq_comm, orthogonalProjection_eq_self_iff] at h
    rw [orthogonalProjection_eq_self_iff.2 h]
  · rw [orthogonalProjection_eq_self_iff.2 h'] at h ⊢
    rw [dist_self, zero_eq_dist, eq_comm, orthogonalProjection_eq_self_iff]
    obtain rfl | hpp' := eq_or_ne p p'
    · exact hp'₂
    · by_contra hn
      rw [angle_self_of_ne hpp', angle_comm,
        angle_eq_arcsin_of_angle_eq_pi_div_two (angle_self_orthogonalProjection p hp'₂),
        Real.zero_eq_arcsin_iff, div_eq_zero_iff] at h
      · simp only [dist_eq_zero, hpp', or_false] at h
        rw [eq_comm] at h
        simp [orthogonalProjection_eq_self_iff, hn] at h
      · exact .inl (Ne.symm (orthogonalProjection_eq_self_iff.symm.not.1 hn))

/-- Auxiliary lemma for the degenerate case of `dist_orthogonalProjection_eq_iff_angle_eq` where
`p` lies in `s₁` or `s₂`. -/
/-
**EuclideanGeometry.dist_orthogonalProjection_eq_iff_angle_eq_aux** 是 Mathlib 中的
一个引理，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for the degenerate case of `dist_orthogonalProjection_eq_iff_ang
le_eq` where
`p` lies in `s₁` or `s₂`.
-/
private lemma dist_orthogonalProjection_eq_iff_angle_eq_aux {p p' : P}
    {s₁ s₂ : AffineSubspace ℝ P}
    [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (hp'₁ : p' ∈ s₁) (hp'₂ : p' ∈ s₂) (h' : p ∈ s₁ ∨ p ∈ s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  rcases h' with h' | h'
  · exact dist_orthogonalProjection_eq_iff_angle_eq_aux₁ hp'₁ hp'₂ h'
  · nth_rw 1 [eq_comm]
    nth_rw 2 [eq_comm]
    exact dist_orthogonalProjection_eq_iff_angle_eq_aux₁ hp'₂ hp'₁ h'

/-- A point `p` is equidistant to two affine subspaces if and only if the angles at a point `p'`
in their intersection between `p` and its orthogonal projections onto the subspaces are equal. -/
/-
**EuclideanGeometry.dist_orthogonalProjection_eq_iff_angle_eq** 是 Mathlib 中的一个引理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_orthogonalProjection_eq_iff_angle_eq {p p' : P} {s₁ s₂ : AffineSubspa
ce Real P} [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalPro
jection] (hp'₁ : p' in s₁) (hp'₂ : p' in s₂) : haveI : Nonempty s₁
参数：hp'₁ : p' in s₁；hp'₂ : p' in s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Geometry.Euclidean.Angle.Bisector.0.EuclideanGeometry.d
ist_orthogonalProjection_eq_iff_angle_eq_aux`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.angle_eq_arcsin_of_angle_eq_pi_div_two`：angle_eq_arcsi
n_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ != p₂ 
∨ p₃ != p₂) : ∠ p₂ p₃ p₁ = Real.arcsin (dist p…
· 使用定理 `EuclideanGeometry.angle_self_orthogonalProjection`：∀ {V : Type u_1} {P :
 Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_
2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `EuclideanGeometry.orthogonalProjection_eq_self_iff`：orthogonalProjection
_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalPro
jection] {p : P} : ↑(orthogonalProjectio…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dist_pos`：dist_pos {x y : γ} : 0 < dist x y ↔ x != y
· 使用引理 `div_left_inj'`：div_left_inj' (hc : c != 0) : a / c = b / c ↔ a = b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.arcsin_inj`：arcsin_inj {x y : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) 
(hy₁ : -1 <= y) (hy₂ : y <= 1) : arcsin x = arcsin y ↔ x = y
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Mathlib.Meta.NormNum.isInt_le_true`：∀ {α : Type u_1} [inst : Ring α] [in
st_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℤ},   Mathlib.Meta.N
ormNum.IsInt a a' → Math…
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
A point `p` is equidistant to two affine subspaces if and only if the angles at 
a point `p'`
in their intersection between `p` and its orthogonal projections onto the subspa
ces are equal.
-/
lemma dist_orthogonalProjection_eq_iff_angle_eq {p p' : P} {s₁ s₂ : AffineSubspace ℝ P}
    [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (hp'₁ : p' ∈ s₁) (hp'₂ : p' ∈ s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  by_cases h' : p ∈ s₁ ∨ p ∈ s₂
  · exact dist_orthogonalProjection_eq_iff_angle_eq_aux hp'₁ hp'₂ h'
  rw [not_or] at h'
  rw [angle_comm,
    angle_eq_arcsin_of_angle_eq_pi_div_two (angle_self_orthogonalProjection p hp'₁)
      (.inl (Ne.symm (orthogonalProjection_eq_self_iff.symm.not.1 h'.1))),
    angle_comm,
    angle_eq_arcsin_of_angle_eq_pi_div_two (angle_self_orthogonalProjection p hp'₂)
      (.inl (Ne.symm (orthogonalProjection_eq_self_iff.symm.not.1 h'.2)))]
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [h]
    · have hp : p ≠ p' := by
        rintro rfl
        exact h'.1 hp'₁
      have hpd : 0 < dist p p' := dist_pos.2 hp
      rw [Real.arcsin_inj (le_trans (by norm_num : (-1 : ℝ) ≤ 0) (by positivity))
        ((div_le_one hpd).2 ?_)
        (le_trans (by norm_num : (-1 : ℝ) ≤ 0) (by positivity)) ((div_le_one hpd).2 ?_)] at h
      · rwa [div_left_inj' hpd.ne'] at h
      · rw [dist_orthogonalProjection_eq_infDist]
        exact Metric.infDist_le_dist_of_mem (SetLike.mem_coe.1 hp'₁)
      · rw [dist_orthogonalProjection_eq_infDist]
        exact Metric.infDist_le_dist_of_mem (SetLike.mem_coe.1 hp'₂)

section Oriented

open Module

variable [Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

-- See https://github.com/leanprover/lean4/issues/11182 for why hypotheses are after the colon.
/-- A point `p` is equidistant to two affine subspaces (typically lines, for this version of the
lemma) if the oriented angles at a point `p'` in their intersection between `p` and its orthogonal
projections onto the subspaces are equal. -/
/-
**EuclideanGeometry.dist_orthogonalProjection_eq_of_oangle_eq** 是 Mathlib 中的一个引理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_orthogonalProjection_eq_of_oangle_eq {p p' : P} {s₁ s₂ : AffineSubspa
ce Real P} (hp'₁ : p' in s₁) (hp'₂ : p' in s₂) : haveI : Nonempty s₁
参数：hp'₁ : p' in s₁；hp'₂ : p' in s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用引理 `FiniteDimensional.of_fact_finrank_eq_two`：of_fact_finrank_eq_two [Fact (
finrank K V = 2)] : FiniteDimensional K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.dist_orthogonalProjection_eq_iff_angle_eq`：dist_orthog
onalProjection_eq_iff_angle_eq {p p' : P} {s₁ s₂ : AffineSubspace Real P} [s₁.di
rection.HasOrthogonalProjection] [s₂.direction.Ha…
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用引理 `EuclideanGeometry.angle_eq_iff_oangle_eq_or_wbtw`：angle_eq_iff_oangle_eq
_or_wbtw {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ != p₂) (hp₄ : p₄ != p₂) : ∠ p₁ p₂ p₃ = ∠ p₃
 p₂ p₄ ↔ ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄ ∨ Wbt…

--- 原说明 ---
A point `p` is equidistant to two affine subspaces (typically lines, for this ve
rsion of the
lemma) if the oriented angles at a point `p'` in their intersection between `p` 
and its orthogonal
projections onto the subspaces are equal.
-/
lemma dist_orthogonalProjection_eq_of_oangle_eq {p p' : P} {s₁ s₂ : AffineSubspace ℝ P}
    (hp'₁ : p' ∈ s₁) (hp'₂ : p' ∈ s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    orthogonalProjection s₁ p ≠ p' →
    orthogonalProjection s₂ p ≠ p' →
    ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) →
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) := by
  intro hp₁ hp₂ h
  rw [dist_orthogonalProjection_eq_iff_angle_eq hp'₁ hp'₂, angle_comm,
      angle_eq_iff_oangle_eq_or_wbtw hp₁ hp₂]
  exact .inl h

-- See https://github.com/leanprover/lean4/issues/11182 for why hypotheses are after the colon.
/-- The oriented angles at a point `p'` in their intersection between `p` and its orthogonal
projections onto two affine subspaces (typically lines, for this version of the lemma) are equal
if `p` is equidistant to the two subspaces. -/
/-
**EuclideanGeometry.oangle_eq_of_dist_orthogonalProjection_eq** 是 Mathlib 中的一个引理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_eq_of_dist_orthogonalProjection_eq {p p' : P} {s₁ s₂ : AffineSubspa
ce Real P} (hp'₁ : p' in s₁) (hp'₂ : p' in s₂) : haveI : Nonempty s₁
参数：hp'₁ : p' in s₁；hp'₂ : p' in s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用引理 `FiniteDimensional.of_fact_finrank_eq_two`：of_fact_finrank_eq_two [Fact (
finrank K V = 2)] : FiniteDimensional K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.dist_orthogonalProjection_eq_dist_iff_eq_of_mem`：dist_
orthogonalProjection_eq_dist_iff_eq_of_mem {s : AffineSubspace 𝕜 P} [s.direction
.HasOrthogonalProjection] {p₁ p₂ : P} (hp₂ : p₂ in s) :…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Collinear.mem_affineSpan_of_mem_of_ne`：Collinear.mem_affineSpan_of_mem_o
f_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in
 s) (hp₃ : p₃ in s) (hp₁p₂ …
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `affineSpan_pair_le_of_mem_of_mem`：affineSpan_pair_le_of_mem_of_mem {p₁ p
₂ : P} {s : AffineSubspace k P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : line[k, p₁, p₂
] <= s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EuclideanGeometry.orthogonalProjection_orthogonalProjection_of_le`：ortho
gonalProjection_orthogonalProjection_of_le {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempt
y s₁] [Nonempty s₂] [s₁.direction.HasOrthogonalProjecti…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `EuclideanGeometry.orthogonalProjection_eq_self_iff`：orthogonalProjection
_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalPro
jection] {p : P} : ↑(orthogonalProjectio…
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用引理 `EuclideanGeometry.angle_eq_iff_oangle_eq_or_wbtw`：angle_eq_iff_oangle_eq
_or_wbtw {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ != p₂) (hp₄ : p₄ != p₂) : ∠ p₁ p₂ p₃ = ∠ p₃
 p₂ p₄ ↔ ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄ ∨ Wbt…
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用引理 `EuclideanGeometry.dist_orthogonalProjection_eq_iff_angle_eq`：dist_orthog
onalProjection_eq_iff_angle_eq {p p' : P} {s₁ s₂ : AffineSubspace Real P} [s₁.di
rection.HasOrthogonalProjection] [s₂.direction.Ha…
· 使用定理 `Wbtw.collinear`：Wbtw.collinear {x y z : P} (h : Wbtw R x y z) : Collinea
r R ({x, y, z} : Set P)
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}

--- 原说明 ---
The oriented angles at a point `p'` in their intersection between `p` and its or
thogonal
projections onto two affine subspaces (typically lines, for this version of the 
lemma) are equal
if `p` is equidistant to the two subspaces.
-/
lemma oangle_eq_of_dist_orthogonalProjection_eq {p p' : P} {s₁ s₂ : AffineSubspace ℝ P}
    (hp'₁ : p' ∈ s₁) (hp'₂ : p' ∈ s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    (orthogonalProjection s₁ p : P) ≠ orthogonalProjection s₂ p →
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) →
    ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) := by
  intro hne h
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  have : Nonempty (s₁ ⊓ s₂ : AffineSubspace ℝ P) := ⟨p', hp'₁, hp'₂⟩
  have hp₁ : orthogonalProjection s₁ p ≠ p' := by
    intro hp
    rw [hp, eq_comm, dist_orthogonalProjection_eq_dist_iff_eq_of_mem hp'₂] at h
    grind
  have hp₂ : orthogonalProjection s₂ p ≠ p' := by
    intro hp
    rw [hp, dist_orthogonalProjection_eq_dist_iff_eq_of_mem hp'₁] at h
    grind
  have hc : ¬ Collinear ℝ {p', (orthogonalProjection s₁ p : P),
      (orthogonalProjection s₂ p : P)} := by
    intro hc
    have h₁ : (orthogonalProjection s₁ p : P) ∈ line[ℝ, p', (orthogonalProjection s₂ p : P)] :=
      hc.mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) (by grind)
    have h₁' : (orthogonalProjection s₁ p : P) ∈ s₁ ⊓ s₂ :=
      ⟨orthogonalProjection_mem _,
        SetLike.le_def.1 (affineSpan_pair_le_of_mem_of_mem hp'₂ (orthogonalProjection_mem _)) h₁⟩
    have h₁'' : (orthogonalProjection s₁ p : P) = (orthogonalProjection (s₁ ⊓ s₂) p : P) := by
      rw [← orthogonalProjection_orthogonalProjection_of_le inf_le_left, eq_comm,
        orthogonalProjection_eq_self_iff]
      grind
    have h₂ : (orthogonalProjection s₂ p : P) ∈ line[ℝ, p', (orthogonalProjection s₁ p : P)] :=
      hc.mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) (by grind)
    have h₂' : (orthogonalProjection s₂ p : P) ∈ s₁ ⊓ s₂ :=
      ⟨SetLike.le_def.1 (affineSpan_pair_le_of_mem_of_mem hp'₁ (orthogonalProjection_mem _)) h₂,
        orthogonalProjection_mem _⟩
    have h₂'' : (orthogonalProjection s₂ p : P) = (orthogonalProjection (s₁ ⊓ s₂) p : P) := by
      rw [← orthogonalProjection_orthogonalProjection_of_le inf_le_right, eq_comm,
        orthogonalProjection_eq_self_iff]
      grind
    apply hne
    rw [h₁'', h₂'']
  rw [dist_orthogonalProjection_eq_iff_angle_eq hp'₁ hp'₂, angle_comm,
    angle_eq_iff_oangle_eq_or_wbtw hp₁ hp₂] at h
  rcases h with h | h | h
  · exact h
  · exfalso
    exact hc h.collinear
  · exfalso
    have h' := h.collinear
    rw [Set.pair_comm] at h'
    exact hc h'

-- See https://github.com/leanprover/lean4/issues/11182 for why hypotheses are after the colon.
/-- A point `p` is equidistant to two affine subspaces (typically lines, for this version of the
lemma) if and only if the oriented angles at a point `p'` in their intersection between `p` and
its orthogonal projections onto the subspaces are equal. -/
/-
**EuclideanGeometry.dist_orthogonalProjection_eq_iff_oangle_eq** 是 Mathlib 中的一个引
理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_orthogonalProjection_eq_iff_oangle_eq {p p' : P} {s₁ s₂ : AffineSubsp
ace Real P} (hp'₁ : p' in s₁) (hp'₂ : p' in s₂) : haveI : Nonempty s₁
参数：hp'₁ : p' in s₁；hp'₂ : p' in s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用引理 `FiniteDimensional.of_fact_finrank_eq_two`：of_fact_finrank_eq_two [Fact (
finrank K V = 2)] : FiniteDimensional K V
· 使用引理 `EuclideanGeometry.oangle_eq_of_dist_orthogonalProjection_eq`：oangle_eq_o
f_dist_orthogonalProjection_eq {p p' : P} {s₁ s₂ : AffineSubspace Real P} (hp'₁ 
: p' in s₁) (hp'₂ : p' in s₂) : haveI : Nonempty …
· 使用引理 `EuclideanGeometry.dist_orthogonalProjection_eq_of_oangle_eq`：dist_orthog
onalProjection_eq_of_oangle_eq {p p' : P} {s₁ s₂ : AffineSubspace Real P} (hp'₁ 
: p' in s₁) (hp'₂ : p' in s₂) : haveI : Nonempty …

--- 原说明 ---
A point `p` is equidistant to two affine subspaces (typically lines, for this ve
rsion of the
lemma) if and only if the oriented angles at a point `p'` in their intersection 
between `p` and
its orthogonal projections onto the subspaces are equal.
-/
lemma dist_orthogonalProjection_eq_iff_oangle_eq {p p' : P} {s₁ s₂ : AffineSubspace ℝ P}
    (hp'₁ : p' ∈ s₁) (hp'₂ : p' ∈ s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    (orthogonalProjection s₁ p : P) ≠ orthogonalProjection s₂ p →
    orthogonalProjection s₁ p ≠ p' →
    orthogonalProjection s₂ p ≠ p' →
    (dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p)) :=
  fun hne hp₁ hp₂ ↦ ⟨oangle_eq_of_dist_orthogonalProjection_eq hp'₁ hp'₂ hne,
   dist_orthogonalProjection_eq_of_oangle_eq hp'₁ hp'₂ hp₁ hp₂⟩

/-- A point `p` is equidistant to two affine subspaces (typically lines, for this version of the
lemma) if twice the oriented angles at a point `p'` in their intersection between `p` and its
orthogonal projections onto the subspaces are equal. -/
/-
**EuclideanGeometry.dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq** 是 Math
lib 中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq {p p' : P} {s₁ s₂ : Af
fineSubspace Real P} (hp'₁ : p' in s₁) (hp'₂ : p' in s₂) : haveI : Nonempty s₁
参数：hp'₁ : p' in s₁；hp'₂ : p' in s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用引理 `FiniteDimensional.of_fact_finrank_eq_two`：of_fact_finrank_eq_two [Fact (
finrank K V = 2)] : FiniteDimensional K V
· 使用引理 `EuclideanGeometry.oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_di
v_two`：oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_div_two {p₁ p₂ p₃ p₄ 
p₅ p₆ : P} (h : (2 : Int) • ∡ p₂ p₃ p₁ = (2 : Int) • ∡ p₄ p₆ p₅) (h…
· 使用定理 `EuclideanGeometry.angle_self_orthogonalProjection`：∀ {V : Type u_1} {P :
 Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_
2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `EuclideanGeometry.dist_orthogonalProjection_eq_of_oangle_eq`：dist_orthog
onalProjection_eq_of_oangle_eq {p p' : P} {s₁ s₂ : AffineSubspace Real P} (hp'₁ 
: p' in s₁) (hp'₂ : p' in s₂) : haveI : Nonempty …

--- 原说明 ---
A point `p` is equidistant to two affine subspaces (typically lines, for this ve
rsion of the
lemma) if twice the oriented angles at a point `p'` in their intersection betwee
n `p` and its
orthogonal projections onto the subspaces are equal.
-/
lemma dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq {p p' : P}
    {s₁ s₂ : AffineSubspace ℝ P} (hp'₁ : p' ∈ s₁) (hp'₂ : p' ∈ s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    -- after the colon as these need the `haveI`s above
    orthogonalProjection s₁ p ≠ p' →
    orthogonalProjection s₂ p ≠ p' →
    (2 : ℤ) • ∡ (orthogonalProjection s₁ p : P) p' p =
      (2 : ℤ) • ∡ p p' (orthogonalProjection s₂ p) →
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) := by
  intro hp₁ hp₂ h
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  have h' : ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) :=
    oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_div_two h
      (angle_self_orthogonalProjection _ hp'₁) (angle_self_orthogonalProjection _ hp'₂)
  exact dist_orthogonalProjection_eq_of_oangle_eq hp'₁ hp'₂ hp₁ hp₂ h'

/-- Auxiliary lemma for the special case of
`dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq` where the orthogonal projection of `p`
to the line `p₁ p₂` is `p₁`. -/
/-
**EuclideanGeometry.dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux
** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for the special case of
`dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq` where the orthogonal 
projection of `p`
to the line `p₁ p₂` is `p₁`.
-/
private lemma dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁ {p p₁ p₂ p₃ : P}
    (h₂ : p₁ ≠ p₂) (h : (2 : ℤ) • ∡ p₂ p₁ p = (2 : ℤ) • ∡ p p₁ p₃)
    (h' : orthogonalProjection line[ℝ, p₁, p₂] p = p₁) :
    dist p (orthogonalProjection line[ℝ, p₁, p₂] p) =
      dist p (orthogonalProjection line[ℝ, p₁, p₃] p) := by
  obtain rfl | hp := eq_or_ne p p₁
  · rw [h', dist_self, zero_eq_dist, eq_comm, orthogonalProjection_eq_self_iff]
    exact left_mem_affineSpan_pair _ _ _
  · rw [← h'] at h hp
    have hpm : p ∉ line[ℝ, p₁, p₂] := orthogonalProjection_eq_self_iff.not.1 (Ne.symm hp)
    rw [two_zsmul_oangle_orthogonalProjection_self _ hpm (right_mem_affineSpan_pair _ _ _)
          (h'.symm ▸ h₂.symm), eq_comm, oangle, Real.Angle.two_zsmul_eq_pi_iff, h'] at h
    replace h := (Orientation.eq_zero_or_oangle_eq_iff_inner_eq_zero _).1 (.inr (.inr h))
    congr 1
    rw [h', eq_comm, coe_orthogonalProjection_eq_iff_mem]
    refine ⟨left_mem_affineSpan_pair _ _ _, ?_⟩
    rw [Submodule.mem_orthogonal']
    intro u hu
    rw [direction_affineSpan, mem_vectorSpan_pair] at hu
    rcases hu with ⟨r, rfl⟩
    rw [inner_smul_right, ← inner_neg_neg, inner_neg_left]
    simp [h]

/-- Auxiliary lemma for the special case of
`dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq` where the orthogonal projection of `p`
to the line `p₁ p₂` or `p₁ p₃` is `p₁`. -/
/-
**EuclideanGeometry.dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux
** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for the special case of
`dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq` where the orthogonal 
projection of `p`
to the line `p₁ p₂` or `p₁ p₃` is `p₁`.
-/
private lemma dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₂ {p p₁ p₂ p₃ : P}
    (h₂ : p₁ ≠ p₂) (h₃ : p₁ ≠ p₃) (h : (2 : ℤ) • ∡ p₂ p₁ p = (2 : ℤ) • ∡ p p₁ p₃)
    (h' : orthogonalProjection line[ℝ, p₁, p₂] p = p₁ ∨
      orthogonalProjection line[ℝ, p₁, p₃] p = p₁) :
    dist p (orthogonalProjection line[ℝ, p₁, p₂] p) =
      dist p (orthogonalProjection line[ℝ, p₁, p₃] p) := by
  rcases h' with h' | h'
  · exact dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁ h₂ h h'
  · refine (dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁ h₃ ?_ h').symm
    rw [oangle_rev, smul_neg, ← h, oangle_rev, smul_neg, neg_neg]

/-- A point `p` is equidistant to two lines `p₁ p₂` and `p₁ p₃` if the oriented angles at `p₁`
are equal modulo `π`. -/
/-
**EuclideanGeometry.dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq** 是
 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq {p p₁ p₂ p₃ : P} 
(h₂ : p₁ != p₂) (h₃ : p₁ != p₃) (h : (2 : Int) • ∡ p₂ p₁ p = (2 : Int) • ∡ p p₁ 
p₃) : dist p (orthogonalProjection line[Real, p₁, p₂] p) = dist p (orthogonalPro
jection line[Real, p₁, p₃] p)
参数：h₂ : p₁ != p₂；h₃ : p₁ != p₃；h : (2 : Int) • ∡ p₂ p₁ p = (2 : Int) • ∡ p p₁ p₃
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemInsert`：∀ {α : Type u_1} (a : α) (s : Set α), Nonemp
ty ↑(insert a s)
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `_private.Mathlib.Geometry.Euclidean.Angle.Bisector.0.EuclideanGeometry.d
ist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₂`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `EuclideanGeometry.dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq`：d
ist_orthogonalProjection_eq_of_two_zsmul_oangle_eq {p p' : P} {s₁ s₂ : AffineSub
space Real P} (hp'₁ : p' in s₁) (hp'₂ : p' in s₂) : haveI :…
· 使用定理 `left_mem_affineSpan_pair`：left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in l
ine[k, p₁, p₂]
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `FiniteDimensional.of_fact_finrank_eq_two`：of_fact_finrank_eq_two [Fact (
finrank K V = 2)] : FiniteDimensional K V
· 使用定理 `Collinear.two_zsmul_oangle_eq_left`：∀ {V : Type u_1} {P : Type u_2} [ins
t : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace
 P]   [inst_3 : NormedAd…
· 使用定理 `collinear_insert_of_mem_affineSpan_pair`：collinear_insert_of_mem_affineS
pan_pair {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃]) : Collinear k ({p₁, p₂, p₃} 
: Set P)
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Collinear.two_zsmul_oangle_eq_right`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…

--- 原说明 ---
A point `p` is equidistant to two lines `p₁ p₂` and `p₁ p₃` if the oriented angl
es at `p₁`
are equal modulo `π`.
-/
lemma dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq {p p₁ p₂ p₃ : P} (h₂ : p₁ ≠ p₂)
    (h₃ : p₁ ≠ p₃) (h : (2 : ℤ) • ∡ p₂ p₁ p = (2 : ℤ) • ∡ p p₁ p₃) :
    dist p (orthogonalProjection line[ℝ, p₁, p₂] p) =
      dist p (orthogonalProjection line[ℝ, p₁, p₃] p) := by
  by_cases h' : orthogonalProjection line[ℝ, p₁, p₂] p = p₁ ∨
      orthogonalProjection line[ℝ, p₁, p₃] p = p₁
  · exact dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₂ h₂ h₃ h h'
  · rw [not_or] at h'
    refine dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq
      (left_mem_affineSpan_pair _ _ _) (left_mem_affineSpan_pair _ _ _) h'.1 h'.2 ?_
    rw [(collinear_insert_of_mem_affineSpan_pair
          (orthogonalProjection_mem p)).two_zsmul_oangle_eq_left h'.1 h₂.symm,
      (collinear_insert_of_mem_affineSpan_pair
        (orthogonalProjection_mem p)).two_zsmul_oangle_eq_right h'.2 h₃.symm, h]

/-- If a point `p` is equidistant to two different lines `p₁ p₂` and `p₁ p₃`, the oriented angles
at `p₁` are equal modulo `π`. -/
/-
**EuclideanGeometry.two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq** 是
 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq {p p₁ p₂ p₃ : P} 
(ha : AffineIndependent Real ![p₁, p₂, p₃]) (h : dist p (orthogonalProjection li
ne[Real, p₁, p₂] p) = dist p (orthogonalProjection line[Real, p₁, p₃] p)) : (2 :
 Int) • ∡ p₂ p₁ p = (2 : Int) • ∡ p p₁ p₃
参数：ha : AffineIndependent Real ![p₁, p₂, p₃]；h : dist p (orthogonalProjection li
ne[Real, p₁, p₂] p) = dist p (orthogonalProjection line[Real, p₁, p₃] p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemInsert`：∀ {α : Type u_1} (a : α) (s : Set α), Nonemp
ty ↑(insert a s)
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用引理 `EuclideanGeometry.orthogonalProjection_sup_of_orthogonalProjection_eq`：o
rthogonalProjection_sup_of_orthogonalProjection_eq {s₁ s₂ : AffineSubspace 𝕜 P} 
[Nonempty s₁] [Nonempty s₂] [s₁.direction.HasOrthogonalProj…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AffineIndependent.inf_affineSpan_eq_affineSpan_inter`：AffineIndependent.
inf_affineSpan_eq_affineSpan_inter [Nontrivial k] {p : ι -> P} (ha : AffineIndep
endent k p) (s₁ s₂ : Set ι) : affineSpan k…
· 使用定理 `AffineSubspace.span_union`：span_union (s t : Set P) : affineSpan k (s un
ion t) = affineSpan k s ⊔ affineSpan k t
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.union_insert`：union_insert : s union insert a t = insert a (s union 
t)
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Matrix.range_cons`：range_cons (x : α) (u : Fin n -> α) : Set.range (vecC
ons x u) = {x} union Set.range u
· 使用定理 `Matrix.range_empty`：range_empty (u : Fin 0 -> α) : Set.range u = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one`：AffineI
ndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one [FiniteDimensional k V]
 [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p…
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
If a point `p` is equidistant to two different lines `p₁ p₂` and `p₁ p₃`, the or
iented angles
at `p₁` are equal modulo `π`.
-/
lemma two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq {p p₁ p₂ p₃ : P}
    (ha : AffineIndependent ℝ ![p₁, p₂, p₃])
    (h : dist p (orthogonalProjection line[ℝ, p₁, p₂] p) =
      dist p (orthogonalProjection line[ℝ, p₁, p₃] p)) :
    (2 : ℤ) • ∡ p₂ p₁ p = (2 : ℤ) • ∡ p p₁ p₃ := by
  by_cases ho : (orthogonalProjection line[ℝ, p₁, p₂] p : P) =
      orthogonalProjection line[ℝ, p₁, p₃] p
  · suffices p = p₁ by simp [this]
    have hs := orthogonalProjection_sup_of_orthogonalProjection_eq ho
    have hinf : line[ℝ, p₁, p₂] ⊓ line[ℝ, p₁, p₃] = affineSpan ℝ {p₁} := by
      convert! (ha.inf_affineSpan_eq_affineSpan_inter {0, 1} {0, 2})
      · simp [Set.image_insert_eq]
      · simp [Set.image_insert_eq]
      · suffices {p₁} = ![p₁, p₂, p₃] '' {0} by grind
        simp
    have hsup : line[ℝ, p₁, p₂] ⊔ line[ℝ, p₁, p₃] = ⊤ := by
      rw [← AffineSubspace.span_union]
      convert! ha.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 ?_
      · simp
        grind
      · simpa using Fact.out
    have hp : orthogonalProjection (line[ℝ, p₁, p₂]) p = p₁ := by
      suffices (orthogonalProjection (line[ℝ, p₁, p₂]) p : P) ∈ affineSpan ℝ {p₁} by
        simpa using this
      have hi : (orthogonalProjection (line[ℝ, p₁, p₂]) p : P) ∈
          line[ℝ, p₁, p₂] ⊓ line[ℝ, p₁, p₃] :=
        ⟨orthogonalProjection_mem _, ho ▸ orthogonalProjection_mem _⟩
      rwa [hinf] at hi
    rw [← orthogonalProjection_sup_of_orthogonalProjection_eq ho] at hp
    rw [← hp, eq_comm, orthogonalProjection_eq_self_iff, hsup]
    exact AffineSubspace.mem_top ℝ V p
  · have hp := oangle_eq_of_dist_orthogonalProjection_eq
      (left_mem_affineSpan_pair _ _ _) (left_mem_affineSpan_pair _ _ _) ho h
    have h₂₁ : p₂ ≠ p₁ := ha.injective.ne (by decide : (1 : Fin 3) ≠ 0)
    have h₃₁ : p₃ ≠ p₁ := ha.injective.ne (by decide : (2 : Fin 3) ≠ 0)
    have hp₁ : orthogonalProjection line[ℝ, p₁, p₂] p ≠ p₁ := by
      intro hp
      rw [hp, eq_comm, dist_orthogonalProjection_eq_dist_iff_eq_of_mem
        (left_mem_affineSpan_pair ℝ _ p₃)] at h
      grind
    have hp₂ : orthogonalProjection line[ℝ, p₁, p₃] p ≠ p₁ := by
      intro hp
      rw [hp, dist_orthogonalProjection_eq_dist_iff_eq_of_mem
          (left_mem_affineSpan_pair ℝ _ p₂)] at h
      grind
    rw [← (collinear_insert_of_mem_affineSpan_pair
             (orthogonalProjection_mem p)).two_zsmul_oangle_eq_left hp₁ h₂₁,
        ← (collinear_insert_of_mem_affineSpan_pair
             (orthogonalProjection_mem p)).two_zsmul_oangle_eq_right hp₂ h₃₁, hp]

/-- A point `p` is equidistant to two different lines `p₁ p₂` and `p₁ p₃` if and only if the
oriented angles at `p₁` are equal modulo `π`. -/
/-
**EuclideanGeometry.dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle_eq** 
是 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle_eq {p p₁ p₂ p₃ : P}
 (ha : AffineIndependent Real ![p₁, p₂, p₃]) : dist p (orthogonalProjection line
[Real, p₁, p₂] p) = dist p (orthogonalProjection line[Real, p₁, p₃] p) ↔ (2 : In
t) • ∡ p₂ p₁ p = (2 : Int) • ∡ p p₁ p₃
参数：ha : AffineIndependent Real ![p₁, p₂, p₃]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemInsert`：∀ {α : Type u_1} (a : α) (s : Set α), Nonemp
ty ↑(insert a s)
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用引理 `EuclideanGeometry.two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_
eq`：two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq {p p₁ p₂ p₃ : P} (h
a : AffineIndependent Real ![p₁, p₂, p₃]) (h : dist p (orthogona…
· 使用引理 `EuclideanGeometry.dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_
eq`：dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq {p p₁ p₂ p₃ : P} (h
₂ : p₁ != p₂) (h₃ : p₁ != p₃) (h : (2 : Int) • ∡ p₂ p₁ p = (2 : …
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p

--- 原说明 ---
A point `p` is equidistant to two different lines `p₁ p₂` and `p₁ p₃` if and onl
y if the
oriented angles at `p₁` are equal modulo `π`.
-/
lemma dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle_eq {p p₁ p₂ p₃ : P}
    (ha : AffineIndependent ℝ ![p₁, p₂, p₃]) :
    dist p (orthogonalProjection line[ℝ, p₁, p₂] p) =
      dist p (orthogonalProjection line[ℝ, p₁, p₃] p) ↔
        (2 : ℤ) • ∡ p₂ p₁ p = (2 : ℤ) • ∡ p p₁ p₃ :=
  ⟨two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq ha,
    dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq
      (ha.injective.ne (by decide : (0 : Fin 3) ≠ 1))
      (ha.injective.ne (by decide : (0 : Fin 3) ≠ 2))⟩

end Oriented

end EuclideanGeometry

