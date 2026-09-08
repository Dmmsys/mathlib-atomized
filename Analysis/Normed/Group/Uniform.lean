/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Normed groups are uniform groups

This file proves lipschitzness of normed group operations and shows that normed groups are uniform
groups.
-/

public section

variable {𝓕 E F : Type*}

open Filter Function Metric Bornology
open scoped ENNReal NNReal Uniformity Pointwise Topology

section SeminormedGroup
variable [SeminormedGroup E] [SeminormedGroup F] {s : Set E} {a b : E} {r : ℝ}

@[to_additive]
/-
**NormedGroup.to_isIsometricSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NormedGroup.to_isIsometricSMul : IsIsometricSMul E E
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用引理 `mul_inv_mul_mul_cancel`：mul_inv_mul_mul_cancel (a b c : G) : a * b⁻¹ * (
b * c) = a * c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance NormedGroup.to_isIsometricSMul : IsIsometricSMul E E :=
  ⟨fun a => Isometry.of_dist_eq fun b c => by simp [dist_eq_norm_inv_mul]⟩

@[to_additive]
/-
**Isometry.norm_map_of_map_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Isometry.norm_map_of_map_one {f : E -> F} (hi : Isometry f) (h₁ : f 1 = 1)
 (x : E) : ‖f x‖ = ‖x‖
参数：hi : Isometry f；h₁ : f 1 = 1；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
-/
theorem Isometry.norm_map_of_map_one {f : E → F} (hi : Isometry f) (h₁ : f 1 = 1) (x : E) :
    ‖f x‖ = ‖x‖ := by rw [← dist_one_right, ← h₁, hi.dist_eq, dist_one_right]

@[to_additive (attr := simp) norm_map]
/-
**norm_map'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_map' [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 𝓕 E F] (f : 𝓕
) (x : E) : ‖f x‖ = ‖x‖
参数：f : 𝓕；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.norm_map_of_map_one`：Isometry.norm_map_of_map_one {f : E -> F} 
(hi : Isometry f) (h₁ : f 1 = 1) (x : E) : ‖f x‖ = ‖x‖
· 使用定理 `IsometryClass.isometry`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β : 
outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpac
e β} {inst_2…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
-/
theorem norm_map' [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 𝓕 E F] (f : 𝓕) (x : E) :
    ‖f x‖ = ‖x‖ :=
  (IsometryClass.isometry f).norm_map_of_map_one (map_one f) x

@[to_additive (attr := simp) nnnorm_map]
/-
**nnnorm_map'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_map' [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 𝓕 E F] (f :
 𝓕) (x : E) : ‖f x‖₊ = ‖x‖₊
参数：f : 𝓕；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `norm_map'`：norm_map' [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 
𝓕 E F] (f : 𝓕) (x : E) : ‖f x‖ = ‖x‖
-/
theorem nnnorm_map' [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 𝓕 E F] (f : 𝓕) (x : E) :
    ‖f x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_map' f x

@[to_additive (attr := simp) enorm_map]
/-
**enorm_map'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_map' [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 𝓕 E F] (f : 
𝓕) (x : E) : ‖f x‖ₑ = ‖x‖ₑ
参数：f : 𝓕；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_map'`：nnnorm_map' [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomCl
ass 𝓕 E F] (f : 𝓕) (x : E) : ‖f x‖₊ = ‖x‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma enorm_map' [FunLike 𝓕 E F] [IsometryClass 𝓕 E F] [OneHomClass 𝓕 E F] (f : 𝓕) (x : E) :
    ‖f x‖ₑ = ‖x‖ₑ := by simp [enorm]

@[to_additive (attr := simp)]
/-
**dist_self_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_self_mul_right (a b : E) : dist b (b * a) = ‖a‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `dist_one_left`：dist_one_left (a : E) : dist 1 a = ‖a‖
· 使用定理 `dist_mul_left`：dist_mul_left [PseudoMetricSpace M] [Mul M] [IsIsometricS
Mul M M] (a b c : M) : dist (a * b) (a * c) = dist b c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem dist_self_mul_right (a b : E) : dist b (b * a) = ‖a‖ := by
  rw [← dist_one_left, ← dist_mul_left b 1 a, mul_one]

@[to_additive (attr := simp)]
/-
**dist_self_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_self_mul_left (a b : E) : dist (b * a) b = ‖a‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_self_mul_right`：dist_self_mul_right (a b : E) : dist b (b * a) = ‖a
‖
-/
theorem dist_self_mul_left (a b : E) : dist (b * a) b = ‖a‖ := by
  rw [dist_comm, dist_self_mul_right]

open Finset

variable [FunLike 𝓕 E F]

/-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant `C` such that
for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. The analogous condition for a linear map of
(semi)normed spaces is in `Mathlib/Analysis/Normed/Operator/Basic.lean`. -/
@[to_additive /-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant
`C` such that for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. The analogous condition for a linear map of
(semi)normed spaces is in `Mathlib/Analysis/Normed/Operator/Basic.lean`. -/]
/-
**MonoidHomClass.lipschitz_of_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHomClass.lipschitz_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : Real
) (h : forall x, ‖f x‖ <= C * ‖x‖) : LipschitzWith (Real.toNNReal C) f
参数：f : 𝓕；C : Real；h : forall x, ‖f x‖ <= C * ‖x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_dist_le'`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {f : α → β} {K : ℝ},   (∀ (x y : α), 
dist (f x) (f y…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
-/
theorem MonoidHomClass.lipschitz_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : LipschitzWith (Real.toNNReal C) f :=
  LipschitzWith.of_dist_le' fun x y => by
    simpa only [dist_eq_norm_inv_mul, map_mul, map_inv] using h (x⁻¹ * y)

@[to_additive]
/-
**lipschitzOnWith_iff_norm_inv_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzOnWith_iff_norm_inv_mul_le {f : E -> F} {C : Real>=0} : Lipschitz
OnWith C f s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> ‖(f x)⁻¹ * f y‖ <= C 
* ‖x⁻¹ * y‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lipschitzOnWith_iff_norm_inv_mul_le {f : E → F} {C : ℝ≥0} :
    LipschitzOnWith C f s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ‖(f x)⁻¹ * f y‖ ≤ C * ‖x⁻¹ * y‖ := by
  simp only [lipschitzOnWith_iff_dist_le_mul, dist_eq_norm_inv_mul]

alias ⟨LipschitzOnWith.norm_inv_mul_le, _⟩ := lipschitzOnWith_iff_norm_inv_mul_le

attribute [to_additive] LipschitzOnWith.norm_inv_mul_le

@[to_additive]
/-
**LipschitzOnWith.norm_inv_mul_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.norm_inv_mul_le_of_le {f : E -> F} {C : Real>=0} (h : Lips
chitzOnWith C f s) (ha : a in s) (hb : b in s) (hr : ‖a⁻¹ * b‖ <= r) : ‖(f a)⁻¹ 
* f b‖ <= C * r
参数：h : LipschitzOnWith C f s；ha : a in s；hb : b in s；hr : ‖a⁻¹ * b‖ <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LipschitzOnWith.norm_inv_mul_le`：∀ {E : Type u_2} {F : Type u_3} [inst :
 SeminormedGroup E] [inst_1 : SeminormedGroup F] {s : Set E} {f : E → F}   {C : 
NNReal}, LipschitzOnW…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
theorem LipschitzOnWith.norm_inv_mul_le_of_le {f : E → F} {C : ℝ≥0} (h : LipschitzOnWith C f s)
    (ha : a ∈ s) (hb : b ∈ s) (hr : ‖a⁻¹ * b‖ ≤ r) : ‖(f a)⁻¹ * f b‖ ≤ C * r :=
  (h.norm_inv_mul_le ha hb).trans <| by gcongr

@[to_additive]
/-
**lipschitzWith_iff_norm_inv_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzWith_iff_norm_inv_mul_le {f : E -> F} {C : Real>=0} : LipschitzWi
th C f ↔ forall x y, ‖(f x)⁻¹ * f y‖ <= C * ‖x⁻¹ * y‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lipschitzWith_iff_norm_inv_mul_le {f : E → F} {C : ℝ≥0} :
    LipschitzWith C f ↔ ∀ x y, ‖(f x)⁻¹ * f y‖ ≤ C * ‖x⁻¹ * y‖ := by
  simp only [lipschitzWith_iff_dist_le_mul, dist_eq_norm_inv_mul]

alias ⟨LipschitzWith.norm_inv_mul_le, _⟩ := lipschitzWith_iff_norm_inv_mul_le

attribute [to_additive] LipschitzWith.norm_inv_mul_le

@[to_additive]
/-
**LipschitzWith.norm_inv_mul_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.norm_inv_mul_le_of_le {f : E -> F} {C : Real>=0} (h : Lipsch
itzWith C f) (hr : ‖a⁻¹ * b‖ <= r) : ‖(f a)⁻¹ * f b‖ <= C * r
参数：h : LipschitzWith C f；hr : ‖a⁻¹ * b‖ <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LipschitzWith.norm_inv_mul_le`：∀ {E : Type u_2} {F : Type u_3} [inst : S
eminormedGroup E] [inst_1 : SeminormedGroup F] {f : E → F} {C : NNReal},   Lipsc
hitzWith C f → ∀ (x…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
theorem LipschitzWith.norm_inv_mul_le_of_le {f : E → F} {C : ℝ≥0} (h : LipschitzWith C f)
    (hr : ‖a⁻¹ * b‖ ≤ r) : ‖(f a)⁻¹ * f b‖ ≤ C * r :=
  (h.norm_inv_mul_le _ _).trans <| by gcongr

/-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C` such that
for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. -/
@[to_additive /-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant
`C` such that for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. -/]
/-
**MonoidHomClass.continuous_of_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHomClass.continuous_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : Rea
l) (h : forall x, ‖f x‖ <= C * ‖x‖) : Continuous f
参数：f : 𝓕；C : Real；h : forall x, ‖f x‖ <= C * ‖x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `MonoidHomClass.lipschitz_of_bound`：MonoidHomClass.lipschitz_of_bound [Mo
noidHomClass 𝓕 E F] (f : 𝓕) (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) : Lipsch
itzWith (Real.toNNReal …
-/
theorem MonoidHomClass.continuous_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : Continuous f :=
  (MonoidHomClass.lipschitz_of_bound f C h).continuous

@[to_additive]
/-
**MonoidHomClass.uniformContinuous_of_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHomClass.uniformContinuous_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (
C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) : UniformContinuous f
参数：f : 𝓕；C : Real；h : forall x, ‖f x‖ <= C * ‖x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `MonoidHomClass.lipschitz_of_bound`：MonoidHomClass.lipschitz_of_bound [Mo
noidHomClass 𝓕 E F] (f : 𝓕) (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) : Lipsch
itzWith (Real.toNNReal …
-/
theorem MonoidHomClass.uniformContinuous_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : UniformContinuous f :=
  (MonoidHomClass.lipschitz_of_bound f C h).uniformContinuous

@[to_additive]
/-
**MonoidHomClass.isometry_iff_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHomClass.isometry_iff_norm [MonoidHomClass 𝓕 E F] (f : 𝓕) : Isometry
 f ↔ forall x, ‖f x‖ = ‖x‖
参数：f : 𝓕。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
-/
theorem MonoidHomClass.isometry_iff_norm [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    Isometry f ↔ ∀ x, ‖f x‖ = ‖x‖ := by
  simp only [isometry_iff_dist_eq, dist_eq_norm_inv_mul, ← map_inv, ← map_mul]
  refine ⟨fun h x => ?_, fun h x y => h _⟩
  simpa using h x 1

alias ⟨_, MonoidHomClass.isometry_of_norm⟩ := MonoidHomClass.isometry_iff_norm

attribute [to_additive] MonoidHomClass.isometry_of_norm

section NNNorm

@[to_additive]
/-
**MonoidHomClass.lipschitz_of_bound_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHomClass.lipschitz_of_bound_nnnorm [MonoidHomClass 𝓕 E F] (f : 𝓕) (C
 : Real>=0) (h : forall x, ‖f x‖₊ <= C * ‖x‖₊) : LipschitzWith C f
参数：f : 𝓕；C : Real>=0；h : forall x, ‖f x‖₊ <= C * ‖x‖₊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHomClass.lipschitz_of_bound`：MonoidHomClass.lipschitz_of_bound [Mo
noidHomClass 𝓕 E F] (f : 𝓕) (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) : Lipsch
itzWith (Real.toNNReal …
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
-/
theorem MonoidHomClass.lipschitz_of_bound_nnnorm [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ≥0)
    (h : ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊) : LipschitzWith C f :=
  @Real.toNNReal_coe C ▸ MonoidHomClass.lipschitz_of_bound f C h

@[to_additive]
/-
**MonoidHomClass.antilipschitz_of_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHomClass.antilipschitz_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) {K : 
Real>=0} (h : forall x, ‖x‖ <= K * ‖f x‖) : AntilipschitzWith K f
参数：f : 𝓕；h : forall x, ‖x‖ <= K * ‖f x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.of_le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst 
: PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β}, 
  (∀ (x y : α), dist x…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
-/
theorem MonoidHomClass.antilipschitz_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ≥0}
    (h : ∀ x, ‖x‖ ≤ K * ‖f x‖) : AntilipschitzWith K f :=
  AntilipschitzWith.of_le_mul_dist fun x y => by
    simpa only [dist_eq_norm_inv_mul, map_inv, map_mul] using h (x⁻¹ * y)

@[to_additive LipschitzWith.norm_le_mul]
/-
**LipschitzWith.norm_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.norm_le_mul' {f : E -> F} {K : Real>=0} (h : LipschitzWith K
 f) (hf : f 1 = 1) (x) : ‖f x‖ <= K * ‖x‖
参数：h : LipschitzWith K f；hf : f 1 = 1；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
-/
theorem LipschitzWith.norm_le_mul' {f : E → F} {K : ℝ≥0} (h : LipschitzWith K f) (hf : f 1 = 1)
    (x) : ‖f x‖ ≤ K * ‖x‖ := by simpa only [dist_one_right, hf] using h.dist_le_mul x 1

@[to_additive LipschitzWith.nnorm_le_mul]
/-
**LipschitzWith.nnorm_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.nnorm_le_mul' {f : E -> F} {K : Real>=0} (h : LipschitzWith 
K f) (hf : f 1 = 1) (x) : ‖f x‖₊ <= K * ‖x‖₊
参数：h : LipschitzWith K f；hf : f 1 = 1；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.norm_le_mul'`：LipschitzWith.norm_le_mul' {f : E -> F} {K :
 Real>=0} (h : LipschitzWith K f) (hf : f 1 = 1) (x) : ‖f x‖ <= K * ‖x‖
-/
theorem LipschitzWith.nnorm_le_mul' {f : E → F} {K : ℝ≥0} (h : LipschitzWith K f) (hf : f 1 = 1)
    (x) : ‖f x‖₊ ≤ K * ‖x‖₊ :=
  h.norm_le_mul' hf x

@[to_additive AntilipschitzWith.le_mul_norm]
/-
**AntilipschitzWith.le_mul_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntilipschitzWith.le_mul_norm' {f : E -> F} {K : Real>=0} (h : Antilipschi
tzWith K f) (hf : f 1 = 1) (x) : ‖x‖ <= K * ‖f x‖
参数：h : AntilipschitzWith K f；hf : f 1 = 1；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AntilipschitzWith.le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst : P
seudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   A
ntilipschitzWith K …
-/
theorem AntilipschitzWith.le_mul_norm' {f : E → F} {K : ℝ≥0} (h : AntilipschitzWith K f)
    (hf : f 1 = 1) (x) : ‖x‖ ≤ K * ‖f x‖ := by
  simpa only [dist_one_right, hf] using h.le_mul_dist x 1

@[to_additive antilipschitzWith_iff_exists_mul_le_norm]
/-
**antilipschitzWith_iff_exists_mul_le_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antilipschitzWith_iff_exists_mul_le_norm' [MonoidHomClass 𝓕 E F] {f : 𝓕} :
 (exists K, AntilipschitzWith K f) ↔ exists c > 0, forall x, c * ‖x‖ <= ‖f x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `AntilipschitzWith.le_mul_norm'`：AntilipschitzWith.le_mul_norm' {f : E ->
 F} {K : Real>=0} (h : AntilipschitzWith K f) (hf : f 1 = 1) (x) : ‖x‖ <= K * ‖f
 x‖
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.le_eq_cancel_le`：le_eq_cancel_le {M : Type*} [M
onoidWithZero M] [PartialOrder M] [PosMulMono M] [PosMulReflectLE M] {e₁ e₂ f₁ f
₂ L : M} (H₁ : e₁ = L * f₁) (H…
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
（共 57 条，此处仅展示前 30 条）
-/
theorem antilipschitzWith_iff_exists_mul_le_norm' [MonoidHomClass 𝓕 E F] {f : 𝓕} :
    (∃ K, AntilipschitzWith K f) ↔ ∃ c > 0, ∀ x, c * ‖x‖ ≤ ‖f x‖ := by
  refine ⟨fun ⟨K, hK⟩ ↦ ⟨(K + 1)⁻¹, by positivity, fun x ↦ ?_⟩, fun ⟨c, hc0, hc⟩ ↦
    ⟨.mk c⁻¹ (by positivity), MonoidHomClass.antilipschitz_of_bound f fun x ↦ ?_⟩⟩
  · grw [hK.le_mul_norm' (map_one f), ← mul_assoc]
    exact mul_le_of_le_one_left (norm_nonneg' (f x)) (by simp [field])
  · grw [← hc, NNReal.coe_mk, inv_mul_cancel_left₀ hc0.ne']

@[to_additive AntilipschitzWith.le_mul_nnnorm]
/-
**AntilipschitzWith.le_mul_nnnorm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntilipschitzWith.le_mul_nnnorm' {f : E -> F} {K : Real>=0} (h : Antilipsc
hitzWith K f) (hf : f 1 = 1) (x) : ‖x‖₊ <= K * ‖f x‖₊
参数：h : AntilipschitzWith K f；hf : f 1 = 1；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.le_mul_norm'`：AntilipschitzWith.le_mul_norm' {f : E ->
 F} {K : Real>=0} (h : AntilipschitzWith K f) (hf : f 1 = 1) (x) : ‖x‖ <= K * ‖f
 x‖
-/
theorem AntilipschitzWith.le_mul_nnnorm' {f : E → F} {K : ℝ≥0} (h : AntilipschitzWith K f)
    (hf : f 1 = 1) (x) : ‖x‖₊ ≤ K * ‖f x‖₊ :=
  h.le_mul_norm' hf x

@[to_additive]
/-
**OneHomClass.bound_of_antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHomClass.bound_of_antilipschitz [OneHomClass 𝓕 E F] (f : 𝓕) {K : Real>=
0} (h : AntilipschitzWith K f) (x) : ‖x‖ <= K * ‖f x‖
参数：f : 𝓕；h : AntilipschitzWith K f；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.le_mul_nnnorm'`：AntilipschitzWith.le_mul_nnnorm' {f : 
E -> F} {K : Real>=0} (h : AntilipschitzWith K f) (hf : f 1 = 1) (x) : ‖x‖₊ <= K
 * ‖f x‖₊
· 使用定理 `OneHomClass.map_one`：∀ {F : Type u_10} {M : outParam (Type u_11)} {N : o
utParam (Type u_12)} {inst : One M} {inst_1 : One N}   {inst_2 : FunLike F M N} 
[self : O…
-/
theorem OneHomClass.bound_of_antilipschitz [OneHomClass 𝓕 E F] (f : 𝓕) {K : ℝ≥0}
    (h : AntilipschitzWith K f) (x) : ‖x‖ ≤ K * ‖f x‖ :=
  h.le_mul_nnnorm' (map_one f) x

@[to_additive]
/-
**Isometry.nnnorm_map_of_map_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Isometry.nnnorm_map_of_map_one {f : E -> F} (hi : Isometry f) (h₁ : f 1 = 
1) (x : E) : ‖f x‖₊ = ‖x‖₊
参数：hi : Isometry f；h₁ : f 1 = 1；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Isometry.norm_map_of_map_one`：Isometry.norm_map_of_map_one {f : E -> F} 
(hi : Isometry f) (h₁ : f 1 = 1) (x : E) : ‖f x‖ = ‖x‖
-/
theorem Isometry.nnnorm_map_of_map_one {f : E → F} (hi : Isometry f) (h₁ : f 1 = 1) (x : E) :
    ‖f x‖₊ = ‖x‖₊ :=
  Subtype.ext <| hi.norm_map_of_map_one h₁ x

end NNNorm

@[to_additive lipschitzWith_one_norm]
/-
**lipschitzWith_one_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzWith_one_norm' : LipschitzWith 1 (norm : E -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `dist_one`：dist_one : dist (1 : E) = norm
· 使用定理 `LipschitzWith.dist_right`：∀ {α : Type u} [inst : PseudoMetricSpace α] (x
 : α), LipschitzWith 1 (dist x)
-/
theorem lipschitzWith_one_norm' : LipschitzWith 1 (norm : E → ℝ) := by
  simpa using LipschitzWith.dist_right (1 : E)

@[to_additive lipschitzWith_one_nnnorm]
/-
**lipschitzWith_one_nnnorm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzWith_one_nnnorm' : LipschitzWith 1 (NNNorm.nnnorm : E -> Real>=0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lipschitzWith_one_norm'`：lipschitzWith_one_norm' : LipschitzWith 1 (norm
 : E -> Real)
-/
theorem lipschitzWith_one_nnnorm' : LipschitzWith 1 (NNNorm.nnnorm : E → ℝ≥0) :=
  lipschitzWith_one_norm'

@[to_additive (attr := fun_prop) uniformContinuous_norm]
/-
**uniformContinuous_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_norm' : UniformContinuous (norm : E -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `lipschitzWith_one_norm'`：lipschitzWith_one_norm' : LipschitzWith 1 (norm
 : E -> Real)
-/
theorem uniformContinuous_norm' : UniformContinuous (norm : E → ℝ) :=
  lipschitzWith_one_norm'.uniformContinuous

@[to_additive (attr := fun_prop) uniformContinuous_nnnorm]
/-
**uniformContinuous_nnnorm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_nnnorm' : UniformContinuous fun a : E => ‖a‖₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.subtype_mk`：UniformContinuous.subtype_mk {p : α -> Pro
p} [UniformSpace α] [UniformSpace β] {f : β -> α} (hf : UniformContinuous f) (h 
: forall x, p (f x…
· 使用定理 `uniformContinuous_norm'`：uniformContinuous_norm' : UniformContinuous (no
rm : E -> Real)
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
-/
theorem uniformContinuous_nnnorm' : UniformContinuous fun a : E => ‖a‖₊ :=
  uniformContinuous_norm'.subtype_mk _

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a₁ a₂ b₁ b₂ : E} {r₁ r₂ : ℝ}

@[to_additive]
/-
**NormedGroup.to_isIsometricSMul_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NormedGroup.to_isIsometricSMul_right : IsIsometricSMul Eᵐᵒᵖ E
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_mul_right`：dist_mul_right [Mul M] [PseudoMetricSpace M] [IsIsometri
cSMul Mᵐᵒᵖ M] (a b c : M) : dist (a * c) (b * c) = dist a b
· 使用定理 `IsIsometricSMul.opposite_of_comm`：∀ (M : Type u) (X : Type w) [inst : Ps
eudoEMetricSpace X] [inst_1 : SMul M X] [inst_2 : SMul Mᵐᵒᵖ X]   [IsCentralScala
r M X] [IsIsometricSMu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance NormedGroup.to_isIsometricSMul_right : IsIsometricSMul Eᵐᵒᵖ E :=
  ⟨fun a => Isometry.of_dist_eq fun b c => by simp⟩

@[to_additive (attr := simp)]
/-
**dist_mul_self_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_mul_self_right (a b : E) : dist a (b * a) = ‖b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `dist_one_left`：dist_one_left (a : E) : dist 1 a = ‖a‖
· 使用定理 `dist_mul_left`：dist_mul_left [PseudoMetricSpace M] [Mul M] [IsIsometricS
Mul M M] (a b c : M) : dist (a * b) (a * c) = dist b c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem dist_mul_self_right (a b : E) : dist a (b * a) = ‖b‖ := by
  rw [← dist_one_left, ← dist_mul_left a 1 b, mul_one, mul_comm]

@[to_additive (attr := simp)]
/-
**dist_mul_self_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_mul_self_left (a b : E) : dist (b * a) a = ‖b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_mul_self_right`：dist_mul_self_right (a b : E) : dist a (b * a) = ‖b
‖
-/
theorem dist_mul_self_left (a b : E) : dist (b * a) a = ‖b‖ := by
  rw [dist_comm, dist_mul_self_right]

@[to_additive (attr := simp 1001)] -- Increase priority because `simp` can prove this
/-
**dist_self_div_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_self_div_right (a b : E) : dist a (a / b) = ‖b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `dist_self_mul_right`：dist_self_mul_right (a b : E) : dist b (b * a) = ‖a
‖
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
-/
theorem dist_self_div_right (a b : E) : dist a (a / b) = ‖b‖ := by
  rw [div_eq_mul_inv, dist_self_mul_right, norm_inv']

@[to_additive (attr := simp 1001)] -- Increase priority because `simp` can prove this
/-
**dist_self_div_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_self_div_left (a b : E) : dist (a / b) a = ‖b‖
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_self_div_right`：dist_self_div_right (a b : E) : dist a (a / b) = ‖b
‖
-/
theorem dist_self_div_left (a b : E) : dist (a / b) a = ‖b‖ := by
  rw [dist_comm, dist_self_div_right]

@[to_additive (attr := simp)]
/-
**dist_div_eq_dist_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_div_eq_dist_mul_left (a b c : E) : dist (a / b) c = dist a (c * b)
参数：a b c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_mul_right`：dist_mul_right [Mul M] [PseudoMetricSpace M] [IsIsometri
cSMul Mᵐᵒᵖ M] (a b c : M) : dist (a * c) (b * c) = dist a b
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
-/
theorem dist_div_eq_dist_mul_left (a b c : E) : dist (a / b) c = dist a (c * b) := by
  rw [← dist_mul_right _ _ b, div_mul_cancel]

@[to_additive (attr := simp)]
/-
**dist_div_eq_dist_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_div_eq_dist_mul_right (a b c : E) : dist a (b / c) = dist (a * c) b
参数：a b c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_mul_right`：dist_mul_right [Mul M] [PseudoMetricSpace M] [IsIsometri
cSMul Mᵐᵒᵖ M] (a b c : M) : dist (a * c) (b * c) = dist a b
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
-/
theorem dist_div_eq_dist_mul_right (a b c : E) : dist a (b / c) = dist (a * c) b := by
  rw [← dist_mul_right _ _ c, div_mul_cancel]

@[to_additive]
/-
**dist_mul_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ * a₂) (b₁ * b₂) <= dist a₁ b₁
 + dist a₂ b₂
参数：a₁ a₂ b₁ b₂ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_mul_right`：dist_mul_right [Mul M] [PseudoMetricSpace M] [IsIsometri
cSMul Mᵐᵒᵖ M] (a b c : M) : dist (a * c) (b * c) = dist a b
· 使用定理 `dist_mul_left`：dist_mul_left [PseudoMetricSpace M] [Mul M] [IsIsometricS
Mul M M] (a b c : M) : dist (a * b) (a * c) = dist b c
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
-/
theorem dist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ * a₂) (b₁ * b₂) ≤ dist a₁ b₁ + dist a₂ b₂ := by
  simpa only [dist_mul_left, dist_mul_right] using dist_triangle (a₁ * a₂) (b₁ * a₂) (b₁ * b₂)

@[to_additive]
/-
**dist_mul_mul_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_mul_mul_le_of_le (h₁ : dist a₁ b₁ <= r₁) (h₂ : dist a₂ b₂ <= r₂) : di
st (a₁ * a₂) (b₁ * b₂) <= r₁ + r₂
参数：h₁ : dist a₁ b₁ <= r₁；h₂ : dist a₂ b₂ <= r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_mul_mul_le`：dist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ * a₂) (b₁ 
* b₂) <= dist a₁ b₁ + dist a₂ b₂
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem dist_mul_mul_le_of_le (h₁ : dist a₁ b₁ ≤ r₁) (h₂ : dist a₂ b₂ ≤ r₂) :
    dist (a₁ * a₂) (b₁ * b₂) ≤ r₁ + r₂ :=
  (dist_mul_mul_le a₁ a₂ b₁ b₂).trans <| add_le_add h₁ h₂

@[to_additive]
/-
**dist_div_div_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_div_div_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ / a₂) (b₁ / b₂) <= dist a₁ b₁
 + dist a₂ b₂
参数：a₁ a₂ b₁ b₂ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `dist_inv_inv`：dist_inv_inv [Group G] [PseudoMetricSpace G] [IsIsometricS
Mul G G] [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) : dist a⁻¹ b⁻¹ = dist a b
· 使用定理 `dist_mul_mul_le`：dist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ * a₂) (b₁ 
* b₂) <= dist a₁ b₁ + dist a₂ b₂
-/
theorem dist_div_div_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ / a₂) (b₁ / b₂) ≤ dist a₁ b₁ + dist a₂ b₂ := by
  simpa only [div_eq_mul_inv, dist_inv_inv] using dist_mul_mul_le a₁ a₂⁻¹ b₁ b₂⁻¹

@[to_additive]
/-
**dist_div_div_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_div_div_le_of_le (h₁ : dist a₁ b₁ <= r₁) (h₂ : dist a₂ b₂ <= r₂) : di
st (a₁ / a₂) (b₁ / b₂) <= r₁ + r₂
参数：h₁ : dist a₁ b₁ <= r₁；h₂ : dist a₂ b₂ <= r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_div_div_le`：dist_div_div_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ / a₂) (b₁ 
/ b₂) <= dist a₁ b₁ + dist a₂ b₂
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem dist_div_div_le_of_le (h₁ : dist a₁ b₁ ≤ r₁) (h₂ : dist a₂ b₂ ≤ r₂) :
    dist (a₁ / a₂) (b₁ / b₂) ≤ r₁ + r₂ :=
  (dist_div_div_le a₁ a₂ b₁ b₂).trans <| add_le_add h₁ h₂

@[to_additive]
/-
**abs_dist_sub_le_dist_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_dist_sub_le_dist_mul_mul (a₁ a₂ b₁ b₂ : E) : |dist a₁ b₁ - dist a₂ b₂|
 <= dist (a₁ * a₂) (b₁ * b₂)
参数：a₁ a₂ b₁ b₂ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_mul_right`：dist_mul_right [Mul M] [PseudoMetricSpace M] [IsIsometri
cSMul Mᵐᵒᵖ M] (a b c : M) : dist (a * c) (b * c) = dist a b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_mul_left`：dist_mul_left [PseudoMetricSpace M] [Mul M] [IsIsometricS
Mul M M] (a b c : M) : dist (a * b) (a * c) = dist b c
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `abs_dist_sub_le`：abs_dist_sub_le (x y z : α) : |dist x z - dist y z| <= 
dist x y
-/
theorem abs_dist_sub_le_dist_mul_mul (a₁ a₂ b₁ b₂ : E) :
    |dist a₁ b₁ - dist a₂ b₂| ≤ dist (a₁ * a₂) (b₁ * b₂) := by
  simpa only [dist_mul_left, dist_mul_right, dist_comm b₂] using
    abs_dist_sub_le (a₁ * a₂) (b₁ * b₂) (b₁ * a₂)

open Finset

@[to_additive]
/-
**nndist_mul_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : nndist (a₁ * a₂) (b₁ * b₂) <= nndist
 a₁ b₁ + nndist a₂ b₂
参数：a₁ a₂ b₁ b₂ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `dist_mul_mul_le`：dist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ * a₂) (b₁ 
* b₂) <= dist a₁ b₁ + dist a₂ b₂
-/
theorem nndist_mul_mul_le (a₁ a₂ b₁ b₂ : E) :
    nndist (a₁ * a₂) (b₁ * b₂) ≤ nndist a₁ b₁ + nndist a₂ b₂ :=
  NNReal.coe_le_coe.1 <| dist_mul_mul_le a₁ a₂ b₁ b₂

@[to_additive]
/-
**edist_mul_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : edist (a₁ * a₂) (b₁ * b₂) <= edist a₁
 b₁ + edist a₂ b₂
参数：a₁ a₂ b₁ b₂ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `nndist_mul_mul_le`：nndist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : nndist (a₁ * a₂
) (b₁ * b₂) <= nndist a₁ b₁ + nndist a₂ b₂
-/
theorem edist_mul_mul_le (a₁ a₂ b₁ b₂ : E) :
    edist (a₁ * a₂) (b₁ * b₂) ≤ edist a₁ b₁ + edist a₂ b₂ := by
  simp only [edist_nndist]
  norm_cast
  apply nndist_mul_mul_le

section PseudoEMetricSpace
variable {α E : Type*} [SeminormedCommGroup E] [PseudoEMetricSpace α] {K Kf Kg : ℝ≥0}
  {f g : α → E} {s : Set α}

@[to_additive (attr := simp)]
/-
**lipschitzWith_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lipschitzWith_inv_iff : LipschitzWith K f⁻¹ ↔ LipschitzWith K f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `edist_inv_inv`：edist_inv_inv [PseudoEMetricSpace G] [IsIsometricSMul G G
] [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) : edist a⁻¹ b⁻¹ = edist a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lipschitzWith_inv_iff : LipschitzWith K f⁻¹ ↔ LipschitzWith K f := by simp [LipschitzWith]

@[to_additive (attr := simp)]
/-
**antilipschitzWith_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antilipschitzWith_inv_iff : AntilipschitzWith K f⁻¹ ↔ AntilipschitzWith K 
f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `edist_inv_inv`：edist_inv_inv [PseudoEMetricSpace G] [IsIsometricSMul G G
] [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) : edist a⁻¹ b⁻¹ = edist a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma antilipschitzWith_inv_iff : AntilipschitzWith K f⁻¹ ↔ AntilipschitzWith K f := by
  simp [AntilipschitzWith]

@[to_additive (attr := simp)]
/-
**lipschitzOnWith_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lipschitzOnWith_inv_iff : LipschitzOnWith K f⁻¹ s ↔ LipschitzOnWith K f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `edist_inv_inv`：edist_inv_inv [PseudoEMetricSpace G] [IsIsometricSMul G G
] [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) : edist a⁻¹ b⁻¹ = edist a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lipschitzOnWith_inv_iff : LipschitzOnWith K f⁻¹ s ↔ LipschitzOnWith K f s := by
  simp [LipschitzOnWith]

@[to_additive (attr := simp)]
/-
**locallyLipschitz_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：locallyLipschitz_inv_iff : LocallyLipschitz f⁻¹ ↔ LocallyLipschitz f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma locallyLipschitz_inv_iff : LocallyLipschitz f⁻¹ ↔ LocallyLipschitz f := by
  simp [LocallyLipschitz]

@[to_additive (attr := simp)]
/-
**locallyLipschitzOn_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：locallyLipschitzOn_inv_iff : LocallyLipschitzOn s f⁻¹ ↔ LocallyLipschitzOn
 s f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma locallyLipschitzOn_inv_iff : LocallyLipschitzOn s f⁻¹ ↔ LocallyLipschitzOn s f := by
  simp [LocallyLipschitzOn]

@[to_additive] alias ⟨LipschitzWith.of_inv, LipschitzWith.inv⟩ := lipschitzWith_inv_iff
@[to_additive] alias ⟨AntilipschitzWith.of_inv, AntilipschitzWith.inv⟩ := antilipschitzWith_inv_iff
@[to_additive] alias ⟨LipschitzOnWith.of_inv, LipschitzOnWith.inv⟩ := lipschitzOnWith_inv_iff
@[to_additive] alias ⟨LocallyLipschitz.of_inv, LocallyLipschitz.inv⟩ := locallyLipschitz_inv_iff
@[to_additive]
alias ⟨LocallyLipschitzOn.of_inv, LocallyLipschitzOn.inv⟩ := locallyLipschitzOn_inv_iff

@[to_additive]
/-
**LipschitzOnWith.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.mul (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg
 g s) : LipschitzOnWith (Kf + Kg) (fun x => f x * g x) s
参数：hf : LipschitzOnWith Kf f s；hg : LipschitzOnWith Kg g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_mul_mul_le`：edist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : edist (a₁ * a₂) (
b₁ * b₂) <= edist a₁ b₁ + edist a₂ b₂
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
lemma LipschitzOnWith.mul (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s) :
    LipschitzOnWith (Kf + Kg) (fun x ↦ f x * g x) s := fun x hx y hy ↦
  calc
    edist (f x * g x) (f y * g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
      edist_mul_mul_le _ _ _ _
    _ ≤ Kf * edist x y + Kg * edist x y := add_le_add (hf hx hy) (hg hx hy)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm

@[to_additive]
/-
**LipschitzWith.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LipschitzWith.mul (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : Li
pschitzWith (Kf + Kg) fun x => f x * g x
参数：hf : LipschitzWith Kf f；hg : LipschitzWith Kg g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LipschitzOnWith.mul`：LipschitzOnWith.mul (hf : LipschitzOnWith Kf f s) (
hg : LipschitzOnWith Kg g s) : LipschitzOnWith (Kf + Kg) (fun x => f x * g x) s
· 使用定理 `LipschitzWith.lipschitzOnWith`：∀ {α : Type u} {β : Type v} [inst : Pseud
oEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β}   {s :
 Set α}, LipschitzW…
-/
lemma LipschitzWith.mul (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf + Kg) fun x ↦ f x * g x := by
  simpa [← lipschitzOnWith_univ] using hf.lipschitzOnWith.mul hg.lipschitzOnWith

@[to_additive]
/-
**LocallyLipschitzOn.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyLipschitzOn.mul (hf : LocallyLipschitzOn s f) (hg : LocallyLipschit
zOn s g) : LocallyLipschitzOn s fun x => f x * g x
参数：hf : LocallyLipschitzOn s f；hg : LocallyLipschitzOn s g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用引理 `LipschitzOnWith.mul`：LipschitzOnWith.mul (hf : LipschitzOnWith Kf f s) (
hg : LipschitzOnWith Kg g s) : LipschitzOnWith (Kf + Kg) (fun x => f x * g x) s
· 使用定理 `LipschitzOnWith.mono`：LipschitzOnWith.mono (hf : LipschitzOnWith K f t) 
(h : s subseteq t) : LipschitzOnWith K f s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma LocallyLipschitzOn.mul (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g) :
    LocallyLipschitzOn s fun x ↦ f x * g x := fun x hx ↦ by
  obtain ⟨Kf, t, ht, hKf⟩ := hf hx
  obtain ⟨Kg, u, hu, hKg⟩ := hg hx
  exact ⟨Kf + Kg, t ∩ u, inter_mem ht hu,
    (hKf.mono Set.inter_subset_left).mul (hKg.mono Set.inter_subset_right)⟩

@[to_additive]
/-
**LocallyLipschitz.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyLipschitz.mul (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
 LocallyLipschitz fun x => f x * g x
参数：hf : LocallyLipschitz f；hg : LocallyLipschitz g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LocallyLipschitzOn.mul`：LocallyLipschitzOn.mul (hf : LocallyLipschitzOn 
s f) (hg : LocallyLipschitzOn s g) : LocallyLipschitzOn s fun x => f x * g x
· 使用定理 `LocallyLipschitz.locallyLipschitzOn`：∀ {α : Type u} {β : Type v} [inst :
 PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {s : Set α} {f : α → β}, 
  LocallyLipschitz f → Lo…
-/
lemma LocallyLipschitz.mul (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x ↦ f x * g x := by
  simpa [← locallyLipschitzOn_univ] using hf.locallyLipschitzOn.mul hg.locallyLipschitzOn

@[to_additive]
/-
**LipschitzOnWith.div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.div (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg
 g s) : LipschitzOnWith (Kf + Kg) (fun x => f x / g x) s
参数：hf : LipschitzOnWith Kf f s；hg : LipschitzOnWith Kg g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `LipschitzOnWith.mul`：LipschitzOnWith.mul (hf : LipschitzOnWith Kf f s) (
hg : LipschitzOnWith Kg g s) : LipschitzOnWith (Kf + Kg) (fun x => f x * g x) s
· 使用定理 `LipschitzOnWith.inv`：∀ {α : Type u_4} {E : Type u_5} [inst : SeminormedC
ommGroup E] [inst_1 : PseudoEMetricSpace α] {K : NNReal} {f : α → E}   {s : Set 
α}, Lipsc…
-/
lemma LipschitzOnWith.div (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s) :
    LipschitzOnWith (Kf + Kg) (fun x ↦ f x / g x) s := by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

@[to_additive]
/-
**LipschitzWith.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.div (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : Li
pschitzWith (Kf + Kg) fun x => f x / g x
参数：hf : LipschitzWith Kf f；hg : LipschitzWith Kg g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `LipschitzWith.mul`：LipschitzWith.mul (hf : LipschitzWith Kf f) (hg : Lip
schitzWith Kg g) : LipschitzWith (Kf + Kg) fun x => f x * g x
· 使用定理 `LipschitzWith.inv`：∀ {α : Type u_4} {E : Type u_5} [inst : SeminormedCom
mGroup E] [inst_1 : PseudoEMetricSpace α] {K : NNReal} {f : α → E},   LipschitzW
ith K f…
-/
theorem LipschitzWith.div (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf + Kg) fun x => f x / g x := by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

@[to_additive]
/-
**LocallyLipschitzOn.div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyLipschitzOn.div (hf : LocallyLipschitzOn s f) (hg : LocallyLipschit
zOn s g) : LocallyLipschitzOn s fun x => f x / g x
参数：hf : LocallyLipschitzOn s f；hg : LocallyLipschitzOn s g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `LocallyLipschitzOn.mul`：LocallyLipschitzOn.mul (hf : LocallyLipschitzOn 
s f) (hg : LocallyLipschitzOn s g) : LocallyLipschitzOn s fun x => f x * g x
· 使用定理 `LocallyLipschitzOn.inv`：∀ {α : Type u_4} {E : Type u_5} [inst : Seminorm
edCommGroup E] [inst_1 : PseudoEMetricSpace α] {f : α → E} {s : Set α},   Locall
yLipschitzOn…
-/
lemma LocallyLipschitzOn.div (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g) :
    LocallyLipschitzOn s fun x ↦ f x / g x := by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

@[to_additive]
/-
**LocallyLipschitz.div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyLipschitz.div (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
 LocallyLipschitz fun x => f x / g x
参数：hf : LocallyLipschitz f；hg : LocallyLipschitz g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `LocallyLipschitz.mul`：LocallyLipschitz.mul (hf : LocallyLipschitz f) (hg
 : LocallyLipschitz g) : LocallyLipschitz fun x => f x * g x
· 使用定理 `LocallyLipschitz.inv`：∀ {α : Type u_4} {E : Type u_5} [inst : Seminormed
CommGroup E] [inst_1 : PseudoEMetricSpace α] {f : α → E},   LocallyLipschitz f →
 LocallyLi…
-/
lemma LocallyLipschitz.div (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x ↦ f x / g x := by
  simpa only [div_eq_mul_inv] using! hf.mul hg.inv

namespace AntilipschitzWith

@[to_additive]
/-
**AntilipschitzWith.mul_lipschitzWith** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWi
th`。
形式化陈述：mul_lipschitzWith (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg g) 
(hK : Kg < Kf⁻¹) : AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ fun x => f x * g x
参数：hf : AntilipschitzWith Kf f；hg : LipschitzWith Kg g；hK : Kg < Kf⁻¹。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.edist_ne_top`：AntilipschitzWith.edist_ne_top [PseudoEM
etricSpace α] [PseudoMetricSpace β] {K : Real>=0} {f : α -> β} (h : Antilipschit
zWith K f) (x y : α)…
· 使用定理 `AntilipschitzWith.of_le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst 
: PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β}, 
  (∀ (x y : α), dist x…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_inv`：∀ (r : NNReal), ↑r⁻¹ = (↑r)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `NNReal.coe_sub`：∀ {r₁ r₂ : NNReal}, r₂ ≤ r₁ → ↑(r₁ - r₂) = ↑r₁ - ↑r₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `sub_le_sub`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b c d : α},   a ≤ b → c ≤ d → a - d ≤ b - c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AntilipschitzWith.mul_le_dist`：mul_le_dist (hf : AntilipschitzWith K f) 
(x y : α) : (K⁻¹ * dist x y : Real) <= dist (f x) (f y)
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `abs_dist_sub_le_dist_mul_mul`：abs_dist_sub_le_dist_mul_mul (a₁ a₂ b₁ b₂ 
: E) : |dist a₁ b₁ - dist a₂ b₂| <= dist (a₁ * a₂) (b₁ * b₂)
-/
theorem mul_lipschitzWith (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg g) (hK : Kg < Kf⁻¹) :
    AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ fun x => f x * g x := by
  let : PseudoMetricSpace α := PseudoEMetricSpace.toPseudoMetricSpace hf.edist_ne_top
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  rw [NNReal.coe_inv, ← _root_.div_eq_inv_mul]
  rw [le_div_iff₀ (NNReal.coe_pos.2 <| tsub_pos_iff_lt.2 hK)]
  rw [mul_comm, NNReal.coe_sub hK.le, sub_mul]
  calc
    ↑Kf⁻¹ * dist x y - Kg * dist x y ≤ dist (f x) (f y) - dist (g x) (g y) :=
      sub_le_sub (hf.mul_le_dist x y) (hg.dist_le_mul x y)
    _ ≤ _ := le_trans (le_abs_self _) (abs_dist_sub_le_dist_mul_mul _ _ _ _)

@[to_additive]
/-
**AntilipschitzWith.mul_div_lipschitzWith** 是 Mathlib 中的一个定理，位于命名空间 `Antilipschi
tzWith`。
形式化陈述：mul_div_lipschitzWith (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg
 (g / f)) (hK : Kg < Kf⁻¹) : AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ g
参数：hf : AntilipschitzWith Kf f；hg : LipschitzWith Kg (g / f)；hK : Kg < Kf⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_div_cancel`：mul_div_cancel (a b : G) : a * (b / a) = b
· 使用定理 `AntilipschitzWith.mul_lipschitzWith`：mul_lipschitzWith (hf : Antilipschi
tzWith Kf f) (hg : LipschitzWith Kg g) (hK : Kg < Kf⁻¹) : AntilipschitzWith (Kf⁻
¹ - Kg)⁻¹ fun x => f x * …
-/
theorem mul_div_lipschitzWith (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg (g / f))
    (hK : Kg < Kf⁻¹) : AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ g := by
  simpa only [Pi.div_apply, mul_div_cancel] using hf.mul_lipschitzWith hg hK

@[to_additive le_mul_norm_sub]
/-
**AntilipschitzWith.le_mul_norm_div** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith
`。
形式化陈述：le_mul_norm_div {f : E -> F} (hf : AntilipschitzWith K f) (x y : E) : ‖x⁻¹
 * y‖ <= K * ‖(f x)⁻¹ * f y‖
参数：hf : AntilipschitzWith K f；x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AntilipschitzWith.le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst : P
seudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   A
ntilipschitzWith K …
-/
theorem le_mul_norm_div {f : E → F} (hf : AntilipschitzWith K f) (x y : E) :
    ‖x⁻¹ * y‖ ≤ K * ‖(f x)⁻¹ * f y‖ := by simp [← dist_eq_norm_inv_mul, hf.le_mul_dist x y]

end AntilipschitzWith
end PseudoEMetricSpace

-- See note [lower instance priority]
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SeminormedCommGroup.to_lipschitzMul : LipschitzMul E :=
  ⟨⟨1 + 1, LipschitzWith.prod_fst.mul LipschitzWith.prod_snd⟩⟩

-- See note [lower instance priority]
/-- A seminormed group is a uniform group, i.e., multiplication and division are uniformly
continuous. -/
@[to_additive /-- A seminormed group is a uniform additive group, i.e., addition and subtraction are
uniformly continuous. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SeminormedCommGroup.to_isUniformGroup : IsUniformGroup E :=
  ⟨(LipschitzWith.prod_fst.div LipschitzWith.prod_snd).uniformContinuous⟩

-- short-circuit type class inference
-- See note [lower instance priority]
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SeminormedCommGroup.toIsTopologicalGroup : IsTopologicalGroup E :=
  inferInstance

/-! ### SeparationQuotient -/

namespace SeparationQuotient

@[to_additive instNorm]
/-
**SeparationQuotient.instMulNorm** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
形式化陈述：instMulNorm : Norm (SeparationQuotient E) where norm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulNorm : Norm (SeparationQuotient E) where
  norm := lift Norm.norm fun _ _ h => h.norm_eq_norm'

set_option linter.docPrime false in
@[to_additive (attr := simp) norm_mk]
/-
**SeparationQuotient.norm_mk'** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：norm_mk' (p : E) : ‖mk p‖ = ‖p‖
参数：p : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_mk' (p : E) : ‖mk p‖ = ‖p‖ := rfl

@[to_additive]
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NormedCommGroup (SeparationQuotient E) where
  __ : CommGroup (SeparationQuotient E) := instCommGroup
  dist_eq := Quotient.ind₂ dist_eq_norm_inv_mul

@[to_additive]
/-
**SeparationQuotient.mk_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient
`。
形式化陈述：mk_eq_one_iff {p : E} : mk p = 1 ↔ ‖p‖ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeparationQuotient.norm_mk'`：norm_mk' (p : E) : ‖mk p‖ = ‖p‖
· 使用引理 `norm_eq_zero'`：norm_eq_zero' : ‖a‖ = 0 ↔ a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_eq_one_iff {p : E} : mk p = 1 ↔ ‖p‖ = 0 := by
  rw [← norm_mk', norm_eq_zero']

set_option linter.docPrime false in
@[to_additive (attr := simp) nnnorm_mk]
/-
**SeparationQuotient.nnnorm_mk'** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：nnnorm_mk' (p : E) : ‖mk p‖₊ = ‖p‖₊
参数：p : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nnnorm_mk' (p : E) : ‖mk p‖₊ = ‖p‖₊ := rfl

end SeparationQuotient

@[to_additive]
/-
**cauchySeq_prod_of_eventually_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_prod_of_eventually_eq {u v : Nat -> E} {N : Nat} (huv : forall n
 >= N, u n = v n) (hv : CauchySeq fun n => ∏ k in range (n + 1), v k) : CauchySe
q fun n => ∏ k in range (n + 1), u k
参数：huv : forall n >= N, u n = v n；hv : CauchySeq fun n => ∏ k in range (n + 1), 
v k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_div_distrib`：prod_div_distrib (f g : ι -> G) : ∏ x in s, f x
 / g x = (∏ x in s, f x) / ∏ x in s, g x
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.eventually_constant_prod`：eventually_constant_prod {u : Nat -> M}
 {N : Nat} (hu : forall n >= N, u n = 1) {n : Nat} (hn : N <= n) : (∏ k in range
 n, u k) = ∏ k in ran…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `CauchySeq.mul`：CauchySeq.mul {ι : Type*} [Preorder ι] {u v : ι -> α} (hu
 : CauchySeq u) (hv : CauchySeq v) : CauchySeq (u * v)
· 使用定理 `SeminormedCommGroup.to_isUniformGroup`：∀ {E : Type u_2} [inst : Seminorm
edCommGroup E], IsUniformGroup E
· 使用定理 `Filter.Tendsto.cauchySeq`：Filter.Tendsto.cauchySeq [SemilatticeSup β] [N
onempty β] {f : β -> α} {x} (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `tendsto_atTop_of_eventually_const`：tendsto_atTop_of_eventually_const {ι 
: Type*} [Preorder ι] {u : ι -> X} {i₀ : ι} (h : forall i >= i₀, u i = x) : Tend
sto u atTop (𝓝 x)
-/
theorem cauchySeq_prod_of_eventually_eq {u v : ℕ → E} {N : ℕ} (huv : ∀ n ≥ N, u n = v n)
    (hv : CauchySeq fun n => ∏ k ∈ range (n + 1), v k) :
    CauchySeq fun n => ∏ k ∈ range (n + 1), u k := by
  let d : ℕ → E := fun n => ∏ k ∈ range (n + 1), u k / v k
  rw [show (fun n => ∏ k ∈ range (n + 1), u k) = d * fun n => ∏ k ∈ range (n + 1), v k
      by ext n; simp [d]]
  suffices ∀ n ≥ N, d n = d N from (tendsto_atTop_of_eventually_const this).cauchySeq.mul hv
  intro n hn
  dsimp [d]
  rw [eventually_constant_prod (N := N + 1) _ (by gcongr)]
  intro m hm
  simp [huv m (le_of_lt hm)]

@[to_additive CauchySeq.norm_bddAbove]
/-
**CauchySeq.mul_norm_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CauchySeq.mul_norm_bddAbove {G : Type*} [SeminormedGroup G] {u : Nat -> G}
 (hu : CauchySeq u) : BddAbove (Set.range (fun n => ‖u n‖))
参数：hu : CauchySeq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_bdd`：cauchySeq_bdd {u : Nat -> α} (hu : CauchySeq u) : exists 
R > 0, forall m n, dist (u m) (u n) < R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_le_norm_add_norm_inv_mul`：norm_le_norm_add_norm_inv_mul (u v : E) :
 ‖u‖ <= ‖v‖ + ‖u⁻¹ * v‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SeminormedGroup.dist_eq`：∀ {E : Type u_8} [self : SeminormedGroup E] (x 
y : E), dist x y = ‖x⁻¹ * y‖
· 使用定理 `bddAbove_def`：bddAbove_def : BddAbove s ↔ exists x, forall y in s, y <= 
x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma CauchySeq.mul_norm_bddAbove {G : Type*} [SeminormedGroup G] {u : ℕ → G}
    (hu : CauchySeq u) : BddAbove (Set.range (fun n ↦ ‖u n‖)) := by
  obtain ⟨C, -, hC⟩ := cauchySeq_bdd hu
  simp_rw [SeminormedGroup.dist_eq] at hC
  have : ∀ n, ‖u n‖ ≤ C + ‖u 0‖ := by
    intro n
    rw [add_comm]
    refine (norm_le_norm_add_norm_inv_mul (u n) (u 0)).trans ?_
    simp [(hC _ _).le]
  rw [bddAbove_def]
  exact ⟨C + ‖u 0‖, by simpa using this⟩

@[to_additive]
/-
**lipschitzOnWith_iff_norm_div_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzOnWith_iff_norm_div_le {f : E -> F} {C : Real>=0} {s : Set E} : L
ipschitzOnWith C f s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> ‖f x / f y‖ <
= C * ‖x / y‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `lipschitzOnWith_iff_norm_inv_mul_le`：lipschitzOnWith_iff_norm_inv_mul_le
 {f : E -> F} {C : Real>=0} : LipschitzOnWith C f s ↔ forall ⦃x⦄, x in s -> fora
ll ⦃y⦄, y in s -> ‖(f x)⁻…
-/
theorem lipschitzOnWith_iff_norm_div_le {f : E → F} {C : ℝ≥0} {s : Set E} :
    LipschitzOnWith C f s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ‖f x / f y‖ ≤ C * ‖x / y‖ := by
  simpa [← norm_inv_mul] using lipschitzOnWith_iff_norm_inv_mul_le

alias ⟨LipschitzOnWith.norm_div_le, _⟩ := lipschitzOnWith_iff_norm_div_le

attribute [to_additive] LipschitzOnWith.norm_div_le

@[to_additive]
/-
**LipschitzOnWith.norm_div_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.norm_div_le_of_le {f : E -> F} {C : Real>=0} {s : Set E} {
a b : E} {r : Real} (h : LipschitzOnWith C f s) (ha : a in s) (hb : b in s) (hr 
: ‖a / b‖ <= r) : ‖f a / f b‖ <= C * r
参数：h : LipschitzOnWith C f s；ha : a in s；hb : b in s；hr : ‖a / b‖ <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LipschitzOnWith.norm_div_le`：∀ {E : Type u_2} {F : Type u_3} [inst : Sem
inormedCommGroup E] [inst_1 : SeminormedCommGroup F] {f : E → F} {C : NNReal}   
{s : Set E}, Lips…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
theorem LipschitzOnWith.norm_div_le_of_le {f : E → F} {C : ℝ≥0} {s : Set E} {a b : E} {r : ℝ}
    (h : LipschitzOnWith C f s) (ha : a ∈ s) (hb : b ∈ s) (hr : ‖a / b‖ ≤ r) :
    ‖f a / f b‖ ≤ C * r :=
  (h.norm_div_le ha hb).trans <| by gcongr

@[to_additive]
/-
**lipschitzWith_iff_norm_div_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzWith_iff_norm_div_le {f : E -> F} {C : Real>=0} : LipschitzWith C
 f ↔ forall x y, ‖f x / f y‖ <= C * ‖x / y‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_eq_norm_div`：dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lipschitzWith_iff_norm_div_le {f : E → F} {C : ℝ≥0} :
    LipschitzWith C f ↔ ∀ x y, ‖f x / f y‖ ≤ C * ‖x / y‖ := by
  simp only [lipschitzWith_iff_dist_le_mul, dist_eq_norm_div]

alias ⟨LipschitzWith.norm_div_le, _⟩ := lipschitzWith_iff_norm_div_le

attribute [to_additive] LipschitzWith.norm_div_le

@[to_additive]
/-
**LipschitzWith.norm_div_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.norm_div_le_of_le {f : E -> F} {C : Real>=0} {a b : E} {r : 
Real} (h : LipschitzWith C f) (hr : ‖a / b‖ <= r) : ‖f a / f b‖ <= C * r
参数：h : LipschitzWith C f；hr : ‖a / b‖ <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LipschitzWith.norm_div_le`：∀ {E : Type u_2} {F : Type u_3} [inst : Semin
ormedCommGroup E] [inst_1 : SeminormedCommGroup F] {f : E → F}   {C : NNReal}, L
ipschitzWith C …
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
theorem LipschitzWith.norm_div_le_of_le {f : E → F} {C : ℝ≥0} {a b : E} {r : ℝ}
    (h : LipschitzWith C f) (hr : ‖a / b‖ ≤ r) : ‖f a / f b‖ ≤ C * r :=
  (h.norm_div_le _ _).trans <| by gcongr

end SeminormedCommGroup

namespace Real
open Topology

/-
**Real.isometry_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isometry_intCast : Isometry ((↑) : Int -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
-/
theorem isometry_intCast : Isometry ((↑) : ℤ → ℝ) :=
  Isometry.of_dist_eq <| by tauto
/-
**Real.isClosedEmbedding_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isClosedEmbedding_intCast : IsClosedEmbedding ((↑) : Int -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.isClosedEmbedding`：isClosedEmbedding [CompleteSpace α] [EMetric
Space γ] {f : α -> γ} (hf : Isometry f) : IsClosedEmbedding f
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `Real.isometry_intCast`：isometry_intCast : Isometry ((↑) : Int -> Real)
-/
theorem isClosedEmbedding_intCast : IsClosedEmbedding ((↑) : ℤ → ℝ) :=
  isometry_intCast.isClosedEmbedding
/-
**Real.isClosed_range_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：isClosed_range_intCast : IsClosed (Set.range ((↑) : Int -> Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `Real.isClosedEmbedding_intCast`：isClosedEmbedding_intCast : IsClosedEmbe
dding ((↑) : Int -> Real)
-/
lemma isClosed_range_intCast : IsClosed (Set.range ((↑) : ℤ → ℝ)) :=
  isClosedEmbedding_intCast.isClosed_range
/-
**Real.isOpen_compl_range_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：isOpen_compl_range_intCast : IsOpen (Set.range ((↑) : Int -> Real))ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用引理 `Real.isClosed_range_intCast`：isClosed_range_intCast : IsClosed (Set.rang
e ((↑) : Int -> Real))
-/
lemma isOpen_compl_range_intCast : IsOpen (Set.range ((↑) : ℤ → ℝ))ᶜ :=
  Real.isClosed_range_intCast.isOpen_compl

end Real

