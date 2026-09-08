/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.LinearAlgebra.Ray
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Rays in a real normed vector space

In this file we prove some lemmas about the `SameRay` predicate in case of a real normed space. In
this case, for two vectors `x y` in the same ray, the norm of their sum is equal to the sum of their
norms and `‖y‖ • x = ‖x‖ • y`.
-/

public section


open Real

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SameRay

variable {x y : E}

/-- If `x` and `y` are on the same ray, then the triangle inequality becomes the equality: the norm
of `x + y` is the sum of the norms of `x` and `y`. The converse is true for a strictly convex
space. -/
/-
**SameRay.norm_add** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：norm_add (h : SameRay Real x y) : ‖x + y‖ = ‖x‖ + ‖y‖
参数：h : SameRay Real x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.exists_eq_smul`：exists_eq_smul (h : SameRay R v₁ v₂) : exists (u
 : M) (a b : R), 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ v₁ = a • u ∧ v₂ = b • u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `norm_smul_of_nonneg`：norm_smul_of_nonneg {t : Real} (ht : 0 <= t) (x : E
) : ‖t • x‖ = t * ‖x‖
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R

--- 原说明 ---
If `x` and `y` are on the same ray, then the triangle inequality becomes the equ
ality: the norm
of `x + y` is the sum of the norms of `x` and `y`. The converse is true for a st
rictly convex
space.
-/
theorem norm_add (h : SameRay ℝ x y) : ‖x + y‖ = ‖x‖ + ‖y‖ := by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  rw [← add_smul, norm_smul_of_nonneg (add_nonneg ha hb), norm_smul_of_nonneg ha,
    norm_smul_of_nonneg hb, add_mul]
/-
**SameRay.norm_sub** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：norm_sub (h : SameRay Real x y) : ‖x - y‖ = |‖x‖ - ‖y‖|
参数：h : SameRay Real x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.exists_eq_smul`：exists_eq_smul (h : SameRay R v₁ v₂) : exists (u
 : M) (a b : R), 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ v₁ = a • u ∧ v₂ = b • u
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `norm_smul_of_nonneg`：norm_smul_of_nonneg {t : Real} (ht : 0 <= t) (x : E
) : ‖t • x‖ = t * ‖x‖
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
· 使用定理 `SameRay.sameRay_comm`：sameRay_comm : SameRay R x y ↔ SameRay R y x
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem norm_sub (h : SameRay ℝ x y) : ‖x - y‖ = |‖x‖ - ‖y‖| := by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  wlog hab : b ≤ a generalizing a b with H
  · rw [SameRay.sameRay_comm] at h
    rw [norm_sub_rev, abs_sub_comm]
    exact H b a hb ha h (le_of_not_ge hab)
  rw [← sub_nonneg] at hab
  rw [← sub_smul, norm_smul_of_nonneg hab, norm_smul_of_nonneg ha, norm_smul_of_nonneg hb, ←
    sub_mul, abs_of_nonneg (mul_nonneg hab (norm_nonneg _))]
/-
**SameRay.norm_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：norm_smul_eq (h : SameRay Real x y) : ‖x‖ • y = ‖y‖ • x
参数：h : SameRay Real x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.exists_eq_smul`：exists_eq_smul (h : SameRay R v₁ v₂) : exists (u
 : M) (a b : R), 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ v₁ = a • u ∧ v₂ = b • u
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_smul_of_nonneg`：norm_smul_of_nonneg {t : Real} (ht : 0 <= t) (x : E
) : ‖t • x‖ = t * ‖x‖
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem norm_smul_eq (h : SameRay ℝ x y) : ‖x‖ • y = ‖y‖ • x := by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  simp only [norm_smul_of_nonneg, *, mul_smul]
  rw [smul_comm, smul_comm b, smul_comm a b u]

end SameRay

variable {x y : F}

/-
**norm_injOn_ray_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_injOn_ray_left (hx : x != 0) : { y | SameRay Real x y }.InjOn norm
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.exists_nonneg_left`：exists_nonneg_left (h : SameRay R x y) (hx :
 x != 0) : exists r : R, 0 <= r ∧ r • x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
-/
theorem norm_injOn_ray_left (hx : x ≠ 0) : { y | SameRay ℝ x y }.InjOn norm := by
  rintro y hy z hz h
  rcases hy.exists_nonneg_left hx with ⟨r, hr, rfl⟩
  rcases hz.exists_nonneg_left hx with ⟨s, hs, rfl⟩
  rw [norm_smul, norm_smul, mul_left_inj' (norm_ne_zero_iff.2 hx), norm_of_nonneg hr,
    norm_of_nonneg hs] at h
  rw [h]
/-
**norm_injOn_ray_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_injOn_ray_right (hy : y != 0) : { x | SameRay Real x y }.InjOn norm
参数：hy : y != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_injOn_ray_left`：norm_injOn_ray_left (hx : x != 0) : { y | SameRay R
eal x y }.InjOn norm
-/
theorem norm_injOn_ray_right (hy : y ≠ 0) : { x | SameRay ℝ x y }.InjOn norm := by
  simpa only [SameRay.sameRay_comm] using norm_injOn_ray_left hy
/-
**sameRay_iff_norm_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_iff_norm_smul_eq : SameRay Real x y ↔ ‖x‖ • y = ‖y‖ • x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.norm_smul_eq`：norm_smul_eq (h : SameRay Real x y) : ‖x‖ • y = ‖y
‖ • x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sameRay_iff_norm_smul_eq : SameRay ℝ x y ↔ ‖x‖ • y = ‖y‖ • x :=
  ⟨SameRay.norm_smul_eq, fun h =>
    or_iff_not_imp_left.2 fun hx =>
      or_iff_not_imp_left.2 fun hy => ⟨‖y‖, ‖x‖, norm_pos_iff.2 hy, norm_pos_iff.2 hx, h.symm⟩⟩

/-- Two nonzero vectors `x y` in a real normed space are on the same ray if and only if the unit
vectors `‖x‖⁻¹ • x` and `‖y‖⁻¹ • y` are equal. -/
/-
**sameRay_iff_inv_norm_smul_eq_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_iff_inv_norm_smul_eq_of_ne (hx : x != 0) (hy : y != 0) : SameRay R
eal x y ↔ ‖x‖⁻¹ • x = ‖y‖⁻¹ • y
参数：hx : x != 0；hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_eq_iff₀`：inv_smul_eq_iff₀ (ha : a != 0) {x y : β} : a⁻¹ • x = y
 ↔ x = a • y
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sameRay_iff_norm_smul_eq`：sameRay_iff_norm_smul_eq : SameRay Real x y ↔ 
‖x‖ • y = ‖y‖ • x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two nonzero vectors `x y` in a real normed space are on the same ray if and only
 if the unit
vectors `‖x‖⁻¹ • x` and `‖y‖⁻¹ • y` are equal.
-/
theorem sameRay_iff_inv_norm_smul_eq_of_ne (hx : x ≠ 0) (hy : y ≠ 0) :
    SameRay ℝ x y ↔ ‖x‖⁻¹ • x = ‖y‖⁻¹ • y := by
  rw [inv_smul_eq_iff₀, smul_comm, eq_comm, inv_smul_eq_iff₀, sameRay_iff_norm_smul_eq] <;>
    rwa [norm_ne_zero_iff]

alias ⟨SameRay.inv_norm_smul_eq, _⟩ := sameRay_iff_inv_norm_smul_eq_of_ne

/-- Two vectors `x y` in a real normed space are on the ray if and only if one of them is zero or
the unit vectors `‖x‖⁻¹ • x` and `‖y‖⁻¹ • y` are equal. -/
/-
**sameRay_iff_inv_norm_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_iff_inv_norm_smul_eq : SameRay Real x y ↔ x = 0 ∨ y = 0 ∨ ‖x‖⁻¹ • 
x = ‖y‖⁻¹ • y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `sameRay_iff_inv_norm_smul_eq_of_ne`：sameRay_iff_inv_norm_smul_eq_of_ne (
hx : x != 0) (hy : y != 0) : SameRay Real x y ↔ ‖x‖⁻¹ • x = ‖y‖⁻¹ • y
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p

--- 原说明 ---
Two vectors `x y` in a real normed space are on the ray if and only if one of th
em is zero or
the unit vectors `‖x‖⁻¹ • x` and `‖y‖⁻¹ • y` are equal.
-/
theorem sameRay_iff_inv_norm_smul_eq : SameRay ℝ x y ↔ x = 0 ∨ y = 0 ∨ ‖x‖⁻¹ • x = ‖y‖⁻¹ • y := by
  rcases eq_or_ne x 0 with (rfl | hx); · simp [SameRay.zero_left]
  rcases eq_or_ne y 0 with (rfl | hy); · simp [SameRay.zero_right]
  simp only [sameRay_iff_inv_norm_smul_eq_of_ne hx hy, *, false_or]

/-- Two vectors of the same norm are on the same ray if and only if they are equal. -/
/-
**sameRay_iff_of_norm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_iff_of_norm_eq (h : ‖x‖ = ‖y‖) : SameRay Real x y ↔ x = y
参数：h : ‖x‖ = ‖y‖。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `SameRay.zero_right`：zero_right (x : M) : SameRay R x 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_injOn_ray_right`：norm_injOn_ray_right (hy : y != 0) : { x | SameRay
 Real x y }.InjOn norm
· 使用定理 `SameRay.rfl`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialO
rder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoi
d…

--- 原说明 ---
Two vectors of the same norm are on the same ray if and only if they are equal.
-/
theorem sameRay_iff_of_norm_eq (h : ‖x‖ = ‖y‖) : SameRay ℝ x y ↔ x = y := by
  obtain rfl | hy := eq_or_ne y 0
  · rw [norm_zero, norm_eq_zero] at h
    exact iff_of_true (SameRay.zero_right _) h
  · exact ⟨fun hxy => norm_injOn_ray_right hy hxy SameRay.rfl h, fun hxy => hxy ▸ SameRay.rfl⟩
/-
**not_sameRay_iff_of_norm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_sameRay_iff_of_norm_eq (h : ‖x‖ = ‖y‖) : ¬SameRay Real x y ↔ x != y
参数：h : ‖x‖ = ‖y‖。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `sameRay_iff_of_norm_eq`：sameRay_iff_of_norm_eq (h : ‖x‖ = ‖y‖) : SameRay
 Real x y ↔ x = y
-/
theorem not_sameRay_iff_of_norm_eq (h : ‖x‖ = ‖y‖) : ¬SameRay ℝ x y ↔ x ≠ y :=
  (sameRay_iff_of_norm_eq h).not

/-- If two points on the same ray have the same norm, then they are equal. -/
/-
**SameRay.eq_of_norm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SameRay.eq_of_norm_eq (h : SameRay Real x y) (hn : ‖x‖ = ‖y‖) : x = y
参数：h : SameRay Real x y；hn : ‖x‖ = ‖y‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sameRay_iff_of_norm_eq`：sameRay_iff_of_norm_eq (h : ‖x‖ = ‖y‖) : SameRay
 Real x y ↔ x = y

--- 原说明 ---
If two points on the same ray have the same norm, then they are equal.
-/
theorem SameRay.eq_of_norm_eq (h : SameRay ℝ x y) (hn : ‖x‖ = ‖y‖) : x = y :=
  (sameRay_iff_of_norm_eq hn).mp h

/-- The norms of two vectors on the same ray are equal if and only if they are equal. -/
/-
**SameRay.norm_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SameRay.norm_eq_iff (h : SameRay Real x y) : ‖x‖ = ‖y‖ ↔ x = y
参数：h : SameRay Real x y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.eq_of_norm_eq`：SameRay.eq_of_norm_eq (h : SameRay Real x y) (hn 
: ‖x‖ = ‖y‖) : x = y

--- 原说明 ---
The norms of two vectors on the same ray are equal if and only if they are equal
.
-/
theorem SameRay.norm_eq_iff (h : SameRay ℝ x y) : ‖x‖ = ‖y‖ ↔ x = y :=
  ⟨h.eq_of_norm_eq, fun h => h ▸ rfl⟩
