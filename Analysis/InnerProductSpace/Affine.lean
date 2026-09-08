/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
/-!
# Normed affine spaces over an inner product space
-/

public section

variable {𝕜 V P : Type*}

section RCLike
variable [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [MetricSpace P]
variable [NormedAddTorsor V P]

open scoped InnerProductSpace

/-
**inner_vsub_left_eq_zero_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_vsub_left_eq_zero_symm {a b : P} {v : V} : ⟪a -ᵥ b, v⟫_𝕜 = 0 ↔ ⟪b -ᵥ
 a, v⟫_𝕜 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inner_vsub_left_eq_zero_symm {a b : P} {v : V} :
    ⟪a -ᵥ b, v⟫_𝕜 = 0 ↔ ⟪b -ᵥ a, v⟫_𝕜 = 0 := by
  rw [← neg_vsub_eq_vsub_rev, inner_neg_left, neg_eq_zero]
/-
**inner_vsub_right_eq_zero_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_vsub_right_eq_zero_symm {v : V} {a b : P} : ⟪v, a -ᵥ b⟫_𝕜 = 0 ↔ ⟪v, 
b -ᵥ a⟫_𝕜 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inner_vsub_right_eq_zero_symm {v : V} {a b : P} :
    ⟪v, a -ᵥ b⟫_𝕜 = 0 ↔ ⟪v, b -ᵥ a⟫_𝕜 = 0 := by
  rw [← neg_vsub_eq_vsub_rev, inner_neg_right, neg_eq_zero]

end RCLike

section Real
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

open scoped RealInnerProductSpace

/-!
In this section, the first `left`/`right` indicates where the common argument to `vsub` is,
and the section refers to the argument of `inner` that ends up in the `dist`.

The lemma shapes are such that the relevant argument of `inner` remains unchanged,
and that the other `vsub` preserves the position of the unchanging argument. -/

/-
**inner_vsub_vsub_left_eq_dist_sq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_vsub_vsub_left_eq_dist_sq_left_iff {a b c : P} : ⟪a -ᵥ b, a -ᵥ c⟫ = 
dist a b ^ 2 ↔ ⟪a -ᵥ b, b -ᵥ c⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `inner_eq_norm_sq_left_iff`：inner_eq_norm_sq_left_iff {v w : F} : ⟪v, w⟫_
Real = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_Real = 0
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用定理 `inner_vsub_right_eq_zero_symm`：inner_vsub_right_eq_zero_symm {v : V} {a 
b : P} : ⟪v, a -ᵥ b⟫_𝕜 = 0 ↔ ⟪v, b -ᵥ a⟫_𝕜 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
In this section, the first `left`/`right` indicates where the common argument to
 `vsub` is,
and the section refers to the argument of `inner` that ends up in the `dist`.

The lemma shapes are such that the relevant argument of `inner` remains unchange
d,
and that the other `vsub` preserves the position of the unchanging argument.
-/
theorem inner_vsub_vsub_left_eq_dist_sq_left_iff {a b c : P} :
    ⟪a -ᵥ b, a -ᵥ c⟫ = dist a b ^ 2 ↔ ⟪a -ᵥ b, b -ᵥ c⟫ = 0 := by
  rw [dist_eq_norm_vsub V, inner_eq_norm_sq_left_iff, vsub_sub_vsub_cancel_left,
    inner_vsub_right_eq_zero_symm]
/-
**inner_vsub_vsub_left_eq_dist_sq_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_vsub_vsub_left_eq_dist_sq_right_iff {a b c : P} : ⟪a -ᵥ b, a -ᵥ c⟫ =
 dist a c ^ 2 ↔ ⟪c -ᵥ b, a -ᵥ c⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `inner_vsub_vsub_left_eq_dist_sq_left_iff`：inner_vsub_vsub_left_eq_dist_s
q_left_iff {a b c : P} : ⟪a -ᵥ b, a -ᵥ c⟫ = dist a b ^ 2 ↔ ⟪a -ᵥ b, b -ᵥ c⟫ = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inner_vsub_vsub_left_eq_dist_sq_right_iff {a b c : P} :
    ⟪a -ᵥ b, a -ᵥ c⟫ = dist a c ^ 2 ↔ ⟪c -ᵥ b, a -ᵥ c⟫ = 0 := by
  rw [real_inner_comm, inner_vsub_vsub_left_eq_dist_sq_left_iff, real_inner_comm]
/-
**inner_vsub_vsub_right_eq_dist_sq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_vsub_vsub_right_eq_dist_sq_left_iff {a b c : P} : ⟪a -ᵥ c, b -ᵥ c⟫ =
 dist a c ^ 2 ↔ ⟪a -ᵥ c, b -ᵥ a⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `inner_eq_norm_sq_left_iff`：inner_eq_norm_sq_left_iff {v w : F} : ⟪v, w⟫_
Real = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_Real = 0
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `inner_vsub_right_eq_zero_symm`：inner_vsub_right_eq_zero_symm {v : V} {a 
b : P} : ⟪v, a -ᵥ b⟫_𝕜 = 0 ↔ ⟪v, b -ᵥ a⟫_𝕜 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inner_vsub_vsub_right_eq_dist_sq_left_iff {a b c : P} :
    ⟪a -ᵥ c, b -ᵥ c⟫ = dist a c ^ 2 ↔ ⟪a -ᵥ c, b -ᵥ a⟫ = 0 := by
  rw [dist_eq_norm_vsub V, inner_eq_norm_sq_left_iff, vsub_sub_vsub_cancel_right,
    inner_vsub_right_eq_zero_symm]
/-
**inner_vsub_vsub_right_eq_dist_sq_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_vsub_vsub_right_eq_dist_sq_right_iff {a b c : P} : ⟪a -ᵥ c, b -ᵥ c⟫ 
= dist b c ^ 2 ↔ ⟪a -ᵥ b, b -ᵥ c⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `inner_vsub_vsub_right_eq_dist_sq_left_iff`：inner_vsub_vsub_right_eq_dist
_sq_left_iff {a b c : P} : ⟪a -ᵥ c, b -ᵥ c⟫ = dist a c ^ 2 ↔ ⟪a -ᵥ c, b -ᵥ a⟫ = 
0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inner_vsub_vsub_right_eq_dist_sq_right_iff {a b c : P} :
    ⟪a -ᵥ c, b -ᵥ c⟫ = dist b c ^ 2 ↔ ⟪a -ᵥ b, b -ᵥ c⟫ = 0 := by
  rw [real_inner_comm, inner_vsub_vsub_right_eq_dist_sq_left_iff, real_inner_comm]

set_option backward.isDefEq.respectTransparency false in
/-- Squared distance between two points on lines from a common origin,
given orthogonality of the direction vectors. -/
/-
**dist_sq_lineMap_lineMap_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_sq_lineMap_lineMap_of_inner_eq_zero {a b c : P} (t₁ t₂ : Real) (h_inn
er : ⟪b -ᵥ a, c -ᵥ a⟫ = 0) : dist (AffineMap.lineMap a b t₁) (AffineMap.lineMap 
a c t₂) ^ 2 = t₁ ^ 2 * dist a b ^ 2 + t₂ ^ 2 * dist a c ^ 2
参数：t₁ t₂ : Real；h_inner : ⟪b -ᵥ a, c -ᵥ a⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `vadd_vsub_vadd_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : Add
Group G] [T : AddTorsor G P] (v₁ v₂ : G) (p : P),   (v₁ +ᵥ p) -ᵥ (v₂ +ᵥ p) = v₁ 
- v₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `norm_sub_sq_real`：norm_sub_sq_real (x y : F) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2
 * ⟪x, y⟫_Real + ‖y‖ ^ 2
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Squared distance between two points on lines from a common origin,
given orthogonality of the direction vectors.
-/
theorem dist_sq_lineMap_lineMap_of_inner_eq_zero {a b c : P} (t₁ t₂ : ℝ)
    (h_inner : ⟪b -ᵥ a, c -ᵥ a⟫ = 0) :
    dist (AffineMap.lineMap a b t₁) (AffineMap.lineMap a c t₂) ^ 2 =
      t₁ ^ 2 * dist a b ^ 2 + t₂ ^ 2 * dist a c ^ 2 := by
  have hvec : AffineMap.lineMap a b t₁ -ᵥ AffineMap.lineMap a c t₂ =
              t₁ • (b -ᵥ a) - t₂ • (c -ᵥ a) := by
    rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply, vadd_vsub_vadd_cancel_right]
  rw [dist_eq_norm_vsub V, hvec, norm_sub_sq_real, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, inner_smul_left, inner_smul_right, h_inner]
  simp only [mul_zero, sub_zero, mul_pow, sq_abs, ← dist_eq_norm_vsub' V]

set_option backward.isDefEq.respectTransparency false in
/-- Squared distance from `p` to a point on the line from `a` to `b`,
given that `p -ᵥ a` is orthogonal to `b -ᵥ a`. -/
/-
**dist_sq_lineMap_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_sq_lineMap_of_inner_eq_zero {a b p : P} (t : Real) (h_inner : ⟪p -ᵥ a
, b -ᵥ a⟫ = 0) : dist p (AffineMap.lineMap a b t) ^ 2 = dist p a ^ 2 + t ^ 2 * d
ist a b ^ 2
参数：t : Real；h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_sq_lineMap_lineMap_of_inner_eq_zero`：dist_sq_lineMap_lineMap_of_inn
er_eq_zero {a b c : P} (t₁ t₂ : Real) (h_inner : ⟪b -ᵥ a, c -ᵥ a⟫ = 0) : dist (A
ffineMap.lineMap a b t₁) (Affi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
Squared distance from `p` to a point on the line from `a` to `b`,
given that `p -ᵥ a` is orthogonal to `b -ᵥ a`.
-/
theorem dist_sq_lineMap_of_inner_eq_zero {a b p : P} (t : ℝ)
    (h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) :
    dist p (AffineMap.lineMap a b t) ^ 2 = dist p a ^ 2 + t ^ 2 * dist a b ^ 2 := by
  have h := dist_sq_lineMap_lineMap_of_inner_eq_zero (t₁ := 1) (t₂ := t) h_inner
  simp only [AffineMap.lineMap_apply_one, one_pow, one_mul] at h
  rwa [dist_comm a p] at h

/-- **Pythagorean theorem**: if `p -ᵥ a` is orthogonal to `b -ᵥ a`, then
`dist p b ^ 2 = dist p a ^ 2 + dist a b ^ 2`. -/
/-
**dist_sq_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_sq_of_inner_eq_zero {a b p : P} (h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) : di
st p b ^ 2 = dist p a ^ 2 + dist a b ^ 2
参数：h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `dist_sq_lineMap_of_inner_eq_zero`：dist_sq_lineMap_of_inner_eq_zero {a b 
p : P} (t : Real) (h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) : dist p (AffineMap.lineMap a
 b t) ^ 2 = dist p a ^…

--- 原说明 ---
**Pythagorean theorem**: if `p -ᵥ a` is orthogonal to `b -ᵥ a`, then
`dist p b ^ 2 = dist p a ^ 2 + dist a b ^ 2`.
-/
theorem dist_sq_of_inner_eq_zero {a b p : P}
    (h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) :
    dist p b ^ 2 = dist p a ^ 2 + dist a b ^ 2 := by
  simpa using dist_sq_lineMap_of_inner_eq_zero 1 h_inner

end Real

