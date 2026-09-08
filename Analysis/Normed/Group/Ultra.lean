/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, David Loeffler
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Ultrametric norms

This file contains results on the behavior of norms in ultrametric groups.

## Main results

* `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`:
  a normed additive group has an ultrametric iff the norm is nonarchimedean
* `IsUltrametricDist.nonarchimedeanGroup` and its additive version: instance showing that a
  commutative group with a nonarchimedean seminorm is a nonarchimedean topological group (i.e.
  there is a neighbourhood basis of the identity consisting of open subgroups).

## Implementation details

Some results are proved first about `nnnorm : X → ℝ≥0` because the bottom element
in `NNReal` is 0, so easier to make statements about maxima of empty sets.

## Tags

ultrametric, nonarchimedean
-/

@[expose] public section
open Metric NNReal

namespace IsUltrametricDist

section Group

variable {S S' ι : Type*} [SeminormedGroup S] [SeminormedGroup S'] [IsUltrametricDist S]

@[to_additive]
/-
**IsUltrametricDist.norm_mul_le_max** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist
`。
形式化陈述：norm_mul_le_max (x y : S) : ‖x * y‖ <= max ‖x‖ ‖y‖
参数：x y : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsUltrametricDist.dist_triangle_max`：∀ {X : Type u_2} {inst : Dist X} [s
elf : IsUltrametricDist X] (x y z : X), dist x z ≤ max (dist x y) (dist y z)
-/
lemma norm_mul_le_max (x y : S) :
    ‖x * y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [le_max_iff, dist_eq_norm_inv_mul] using dist_triangle_max x⁻¹ 1 y

@[to_additive]
/-
**IsUltrametricDist.isUltrametricDist_of_forall_norm_mul_le_max_norm** 是 Mathlib
 中的一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：isUltrametricDist_of_forall_norm_mul_le_max_norm (h : forall x y : S', ‖x 
* y‖ <= max ‖x‖ ‖y‖) : IsUltrametricDist S' where dist_triangle_max x y z
参数：h : forall x y : S', ‖x * y‖ <= max ‖x‖ ‖y‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `mul_mul_inv_mul_cancel`：mul_mul_inv_mul_cancel (a b c : G) : a * b * (b⁻
¹ * c) = a * c
-/
lemma isUltrametricDist_of_forall_norm_mul_le_max_norm
    (h : ∀ x y : S', ‖x * y‖ ≤ max ‖x‖ ‖y‖) : IsUltrametricDist S' where
  dist_triangle_max x y z := by
    simpa [dist_eq_norm_inv_mul] using h (x⁻¹ * y) (y⁻¹ * z)
/-
**IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm** 是 Mathlib 中的一个引
理，位于命名空间 `IsUltrametricDist`。
形式化陈述：isUltrametricDist_of_isNonarchimedean_norm {S' : Type*} [SeminormedAddGrou
p S'] (h : IsNonarchimedean (norm : S' -> Real)) : IsUltrametricDist S'
参数：h : IsNonarchimedean (norm : S' -> Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm`：∀ {S
' : Type u_2} [inst : SeminormedAddGroup S'], (∀ (x y : S'), ‖x + y‖ ≤ max ‖x‖ ‖
y‖) → IsUltrametricDist S'
-/
lemma isUltrametricDist_of_isNonarchimedean_norm {S' : Type*} [SeminormedAddGroup S']
    (h : IsNonarchimedean (norm : S' → ℝ)) : IsUltrametricDist S' :=
  isUltrametricDist_of_forall_norm_add_le_max_norm h
/-
**IsUltrametricDist.isNonarchimedean_norm** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametr
icDist`。
形式化陈述：isNonarchimedean_norm {R} [SeminormedAddCommGroup R] [IsUltrametricDist R]
 : IsNonarchimedean (‖·‖ : R -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dist_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], dist 0 = norm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SeminormedAddGroup.dist_eq`：∀ {E : Type u_8} [self : SeminormedAddGroup 
E] (x y : E), dist x y = ‖-x + y‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `IsUltrametricDist.dist_triangle_max`：∀ {X : Type u_2} {inst : Dist X} [s
elf : IsUltrametricDist X] (x y z : X), dist x z ≤ max (dist x y) (dist y z)
-/
lemma isNonarchimedean_norm {R} [SeminormedAddCommGroup R] [IsUltrametricDist R] :
    IsNonarchimedean (‖·‖ : R → ℝ) := by
  intro x y
  convert! dist_triangle_max 0 x (x + y) using 1
  · simp
  · congr <;> simp [SeminormedAddGroup.dist_eq]
/-
**IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm** 是 Mathlib 中的一个
引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：isUltrametricDist_iff_isNonarchimedean_norm {R} [SeminormedAddCommGroup R]
 : IsUltrametricDist R ↔ IsNonarchimedean (‖·‖ : R -> Real)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.isNonarchimedean_norm`：isNonarchimedean_norm {R} [Semi
normedAddCommGroup R] [IsUltrametricDist R] : IsNonarchimedean (‖·‖ : R -> Real)
· 使用引理 `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`：isUltramet
ricDist_of_isNonarchimedean_norm {S' : Type*} [SeminormedAddGroup S'] (h : IsNon
archimedean (norm : S' -> Real)) : IsUltrametricDi…
-/
lemma isUltrametricDist_iff_isNonarchimedean_norm {R} [SeminormedAddCommGroup R] :
    IsUltrametricDist R ↔ IsNonarchimedean (‖·‖ : R → ℝ) :=
  ⟨fun h => h.isNonarchimedean_norm, IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm⟩

@[to_additive]
/-
**IsUltrametricDist.nnnorm_mul_le_max** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDi
st`。
形式化陈述：nnnorm_mul_le_max (x y : S) : ‖x * y‖₊ <= max ‖x‖₊ ‖y‖₊
参数：x y : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.norm_mul_le_max`：norm_mul_le_max (x y : S) : ‖x * y‖ <
= max ‖x‖ ‖y‖
-/
lemma nnnorm_mul_le_max (x y : S) :
    ‖x * y‖₊ ≤ max ‖x‖₊ ‖y‖₊ :=
  norm_mul_le_max _ _

@[to_additive]
/-
**IsUltrametricDist.isUltrametricDist_of_forall_nnnorm_mul_le_max_nnnorm** 是 Mat
hlib 中的一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：isUltrametricDist_of_forall_nnnorm_mul_le_max_nnnorm (h : forall x y : S',
 ‖x * y‖₊ <= max ‖x‖₊ ‖y‖₊) : IsUltrametricDist S'
参数：h : forall x y : S', ‖x * y‖₊ <= max ‖x‖₊ ‖y‖₊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.isUltrametricDist_of_forall_norm_mul_le_max_norm`：isUl
trametricDist_of_forall_norm_mul_le_max_norm (h : forall x y : S', ‖x * y‖ <= ma
x ‖x‖ ‖y‖) : IsUltrametricDist S' where dist_triangle_ma…
-/
lemma isUltrametricDist_of_forall_nnnorm_mul_le_max_nnnorm
    (h : ∀ x y : S', ‖x * y‖₊ ≤ max ‖x‖₊ ‖y‖₊) : IsUltrametricDist S' :=
  isUltrametricDist_of_forall_norm_mul_le_max_norm h
/-
**IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_nnnorm** 是 Mathlib 中的一
个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：isUltrametricDist_of_isNonarchimedean_nnnorm {S' : Type*} [SeminormedAddGr
oup S'] (h : IsNonarchimedean (nnnorm : S' -> Real>=0)) : IsUltrametricDist S'
参数：h : IsNonarchimedean (nnnorm : S' -> Real>=0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUltrametricDist.isUltrametricDist_of_forall_nnnorm_add_le_max_nnnorm`：
∀ {S' : Type u_2} [inst : SeminormedAddGroup S'], (∀ (x y : S'), ‖x + y‖₊ ≤ max 
‖x‖₊ ‖y‖₊) → IsUltrametricDist S'
-/
lemma isUltrametricDist_of_isNonarchimedean_nnnorm {S' : Type*} [SeminormedAddGroup S']
    (h : IsNonarchimedean (nnnorm : S' → ℝ≥0)) : IsUltrametricDist S' :=
  isUltrametricDist_of_forall_nnnorm_add_le_max_nnnorm h
/-
**IsUltrametricDist.isNonarchimedean_nnnorm** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrame
tricDist`。
形式化陈述：isNonarchimedean_nnnorm {R} [SeminormedAddCommGroup R] [IsUltrametricDist 
R] : IsNonarchimedean (‖·‖₊ : R -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.isNonarchimedean_norm`：isNonarchimedean_norm {R} [Semi
normedAddCommGroup R] [IsUltrametricDist R] : IsNonarchimedean (‖·‖ : R -> Real)
-/
lemma isNonarchimedean_nnnorm {R} [SeminormedAddCommGroup R] [IsUltrametricDist R] :
    IsNonarchimedean (‖·‖₊ : R → ℝ) := by
  simpa using isNonarchimedean_norm
/-
**IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_nnnorm** 是 Mathlib 中的
一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：isUltrametricDist_iff_isNonarchimedean_nnnorm {R} [SeminormedAddCommGroup 
R] : IsUltrametricDist R ↔ IsNonarchimedean (‖·‖₊ : R -> Real)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.isNonarchimedean_norm`：isNonarchimedean_norm {R} [Semi
normedAddCommGroup R] [IsUltrametricDist R] : IsNonarchimedean (‖·‖ : R -> Real)
· 使用引理 `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`：isUltramet
ricDist_of_isNonarchimedean_norm {S' : Type*} [SeminormedAddGroup S'] (h : IsNon
archimedean (norm : S' -> Real)) : IsUltrametricDi…
-/
lemma isUltrametricDist_iff_isNonarchimedean_nnnorm {R} [SeminormedAddCommGroup R] :
    IsUltrametricDist R ↔ IsNonarchimedean (‖·‖₊ : R → ℝ) :=
  ⟨fun h => h.isNonarchimedean_norm, IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm⟩

/-- All triangles are isosceles in an ultrametric normed group. -/
@[to_additive /-- All triangles are isosceles in an ultrametric normed additive group. -/]
/-
**IsUltrametricDist.norm_mul_eq_max_of_norm_ne_norm** 是 Mathlib 中的一个引理，位于命名空间 `I
sUltrametricDist`。
形式化陈述：norm_mul_eq_max_of_norm_ne_norm {x y : S} (h : ‖x‖ != ‖y‖) : ‖x * y‖ = max
 ‖x‖ ‖y‖
参数：h : ‖x‖ != ‖y‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用引理 `IsUltrametricDist.dist_eq_max_of_dist_ne_dist`：dist_eq_max_of_dist_ne_di
st (h : dist x y != dist y z) : dist x z = max (dist x y) (dist y z)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `dist_one`：dist_one : dist (1 : E) = norm
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `dist_one_left`：dist_one_left (a : E) : dist 1 a = ‖a‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
All triangles are isosceles in an ultrametric normed group.
-/
lemma norm_mul_eq_max_of_norm_ne_norm
    {x y : S} (h : ‖x‖ ≠ ‖y‖) : ‖x * y‖ = max ‖x‖ ‖y‖ := by
  rw [← inv_inv x, ← dist_eq_norm_inv_mul, dist_eq_max_of_dist_ne_dist _ 1 _ (by simp [h])]
  simp only [dist_one_right, dist_one_left, norm_inv']

@[to_additive]
/-
**IsUltrametricDist.norm_eq_of_mul_norm_lt_max** 是 Mathlib 中的一个引理，位于命名空间 `IsUltr
ametricDist`。
形式化陈述：norm_eq_of_mul_norm_lt_max {x y : S} (h : ‖x * y‖ < max ‖x‖ ‖y‖) : ‖x‖ = ‖
y‖
参数：h : ‖x * y‖ < max ‖x‖ ‖y‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `IsUltrametricDist.norm_mul_eq_max_of_norm_ne_norm`：norm_mul_eq_max_of_no
rm_ne_norm {x y : S} (h : ‖x‖ != ‖y‖) : ‖x * y‖ = max ‖x‖ ‖y‖
-/
lemma norm_eq_of_mul_norm_lt_max {x y : S} (h : ‖x * y‖ < max ‖x‖ ‖y‖) :
    ‖x‖ = ‖y‖ :=
  not_ne_iff.mp (h.ne ∘ norm_mul_eq_max_of_norm_ne_norm)

/-- All triangles are isosceles in an ultrametric normed group. -/
@[to_additive /-- All triangles are isosceles in an ultrametric normed additive group. -/]
/-
**IsUltrametricDist.nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm** 是 Mathlib 中的一个引理，位于命
名空间 `IsUltrametricDist`。
形式化陈述：nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm {x y : S} (h : ‖x‖₊ != ‖y‖₊) : ‖x * 
y‖₊ = max ‖x‖₊ ‖y‖₊
参数：h : ‖x‖₊ != ‖y‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_max`：coe_max (x y : Real>=0) : ((max x y : Real>=0) : Real) =
 max (x : Real) (y : Real)
· 使用引理 `IsUltrametricDist.norm_mul_eq_max_of_norm_ne_norm`：norm_mul_eq_max_of_no
rm_ne_norm {x y : S} (h : ‖x‖ != ‖y‖) : ‖x * y‖ = max ‖x‖ ‖y‖
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `NNReal.coe_injective`：Function.Injective NNReal.toReal

--- 原说明 ---
All triangles are isosceles in an ultrametric normed group.
-/
lemma nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm
    {x y : S} (h : ‖x‖₊ ≠ ‖y‖₊) : ‖x * y‖₊ = max ‖x‖₊ ‖y‖₊ := by
  simpa only [← NNReal.coe_inj, NNReal.coe_max] using!
    norm_mul_eq_max_of_norm_ne_norm (NNReal.coe_injective.ne h)

@[to_additive]
/-
**IsUltrametricDist.nnnorm_eq_of_mul_nnnorm_lt_max** 是 Mathlib 中的一个引理，位于命名空间 `Is
UltrametricDist`。
形式化陈述：nnnorm_eq_of_mul_nnnorm_lt_max {x y : S} (h : ‖x * y‖₊ < max ‖x‖₊ ‖y‖₊) : 
‖x‖₊ = ‖y‖₊
参数：h : ‖x * y‖₊ < max ‖x‖₊ ‖y‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `IsUltrametricDist.nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm`：nnnorm_mul_eq_m
ax_of_nnnorm_ne_nnnorm {x y : S} (h : ‖x‖₊ != ‖y‖₊) : ‖x * y‖₊ = max ‖x‖₊ ‖y‖₊
-/
lemma nnnorm_eq_of_mul_nnnorm_lt_max {x y : S} (h : ‖x * y‖₊ < max ‖x‖₊ ‖y‖₊) :
    ‖x‖₊ = ‖y‖₊ :=
  not_ne_iff.mp (h.ne ∘ nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm)

/-- All triangles are isosceles in an ultrametric normed group. -/
@[to_additive /-- All triangles are isosceles in an ultrametric normed additive group. -/]
/-
**IsUltrametricDist.norm_div_eq_max_of_norm_div_ne_norm_div** 是 Mathlib 中的一个引理，位
于命名空间 `IsUltrametricDist`。
形式化陈述：norm_div_eq_max_of_norm_div_ne_norm_div (x y z : S) (h : ‖x / y‖ != ‖y / z
‖) : ‖x / z‖ = max ‖x / y‖ ‖y / z‖
参数：x y z : S；h : ‖x / y‖ != ‖y / z‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_div_cancel`：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a
 / c
· 使用引理 `IsUltrametricDist.norm_mul_eq_max_of_norm_ne_norm`：norm_mul_eq_max_of_no
rm_ne_norm {x y : S} (h : ‖x‖ != ‖y‖) : ‖x * y‖ = max ‖x‖ ‖y‖

--- 原说明 ---
All triangles are isosceles in an ultrametric normed group.
-/
lemma norm_div_eq_max_of_norm_div_ne_norm_div (x y z : S) (h : ‖x / y‖ ≠ ‖y / z‖) :
    ‖x / z‖ = max ‖x / y‖ ‖y / z‖ := by
  simpa only [div_mul_div_cancel] using norm_mul_eq_max_of_norm_ne_norm h

/-- All triangles are isosceles in an ultrametric normed group. -/
@[to_additive /-- All triangles are isosceles in an ultrametric normed additive group. -/]
/-
**IsUltrametricDist.nnnorm_div_eq_max_of_nnnorm_div_ne_nnnorm_div** 是 Mathlib 中的
一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：nnnorm_div_eq_max_of_nnnorm_div_ne_nnnorm_div (x y z : S) (h : ‖x / y‖₊ !=
 ‖y / z‖₊) : ‖x / z‖₊ = max ‖x / y‖₊ ‖y / z‖₊
参数：x y z : S；h : ‖x / y‖₊ != ‖y / z‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_max`：coe_max (x y : Real>=0) : ((max x y : Real>=0) : Real) =
 max (x : Real) (y : Real)
· 使用引理 `IsUltrametricDist.norm_div_eq_max_of_norm_div_ne_norm_div`：norm_div_eq_m
ax_of_norm_div_ne_norm_div (x y z : S) (h : ‖x / y‖ != ‖y / z‖) : ‖x / z‖ = max 
‖x / y‖ ‖y / z‖
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `NNReal.coe_injective`：Function.Injective NNReal.toReal

--- 原说明 ---
All triangles are isosceles in an ultrametric normed group.
-/
lemma nnnorm_div_eq_max_of_nnnorm_div_ne_nnnorm_div (x y z : S) (h : ‖x / y‖₊ ≠ ‖y / z‖₊) :
    ‖x / z‖₊ = max ‖x / y‖₊ ‖y / z‖₊ := by
  simpa only [← NNReal.coe_inj, NNReal.coe_max] using!
    norm_div_eq_max_of_norm_div_ne_norm_div _ _ _ (NNReal.coe_injective.ne h)

@[to_additive]
/-
**IsUltrametricDist.nnnorm_pow_le** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：nnnorm_pow_le (x : S) (n : Nat) : ‖x ^ n‖₊ <= ‖x‖₊
参数：x : S；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `nnnorm_one'`：nnnorm_one' : ‖(1 : E)‖₊ = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用引理 `IsUltrametricDist.nnnorm_mul_le_max`：nnnorm_mul_le_max (x y : S) : ‖x * 
y‖₊ <= max ‖x‖₊ ‖y‖₊
-/
lemma nnnorm_pow_le (x : S) (n : ℕ) :
    ‖x ^ n‖₊ ≤ ‖x‖₊ := by
  induction n with
  | zero => simp
  | succ n hn => simpa [pow_add, hn] using nnnorm_mul_le_max (x ^ n) x

@[to_additive]
/-
**IsUltrametricDist.norm_pow_le** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：norm_pow_le (x : S) (n : Nat) : ‖x ^ n‖ <= ‖x‖
参数：x : S；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.nnnorm_pow_le`：nnnorm_pow_le (x : S) (n : Nat) : ‖x ^ 
n‖₊ <= ‖x‖₊
-/
lemma norm_pow_le (x : S) (n : ℕ) :
    ‖x ^ n‖ ≤ ‖x‖ :=
  nnnorm_pow_le x n

@[to_additive]
/-
**IsUltrametricDist.nnnorm_zpow_le** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist`
。
形式化陈述：nnnorm_zpow_le (x : S) (z : Int) : ‖x ^ z‖₊ <= ‖x‖₊
参数：x : S；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `IsUltrametricDist.nnnorm_pow_le`：nnnorm_pow_le (x : S) (n : Nat) : ‖x ^ 
n‖₊ <= ‖x‖₊
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `nnnorm_inv'`：nnnorm_inv' (a : E) : ‖a⁻¹‖₊ = ‖a‖₊
-/
lemma nnnorm_zpow_le (x : S) (z : ℤ) :
    ‖x ^ z‖₊ ≤ ‖x‖₊ := by
  cases z <;>
  simpa using nnnorm_pow_le _ _

@[to_additive]
/-
**IsUltrametricDist.norm_zpow_le** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：norm_zpow_le (x : S) (z : Int) : ‖x ^ z‖ <= ‖x‖
参数：x : S；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.nnnorm_zpow_le`：nnnorm_zpow_le (x : S) (z : Int) : ‖x 
^ z‖₊ <= ‖x‖₊
-/
lemma norm_zpow_le (x : S) (z : ℤ) :
    ‖x ^ z‖ ≤ ‖x‖ :=
  nnnorm_zpow_le x z

section nonarch

variable (S)
/--
In a group with an ultrametric norm, open balls around 1 of positive radius are open subgroups.
-/
@[to_additive /-- In an additive group with an ultrametric norm, open balls around 0 of
positive radius are open subgroups. -/]
/-
**IsUltrametricDist.ball_openSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `IsUltrametricDi
st`。
形式化陈述：ball_openSubgroup {r : Real} (hr : 0 < r) : OpenSubgroup S where carrier
参数：hr : 0 < r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ball_openSubgroup {r : ℝ} (hr : 0 < r) : OpenSubgroup S where
  carrier := Metric.ball (1 : S) r
  mul_mem' {x} {y} hx hy := by
    simp only [Metric.mem_ball, dist_eq_norm_inv_mul', inv_one, one_mul] at hx hy ⊢
    exact (norm_mul_le_max x y).trans_lt (max_lt hx hy)
  one_mem' := Metric.mem_ball_self hr
  inv_mem' := by simp only [Metric.mem_ball, dist_one_right, norm_inv', imp_self, implies_true]
  isOpen' := Metric.isOpen_ball

/--
In a group with an ultrametric norm, closed balls around 1 of positive radius are open subgroups.
-/
@[to_additive /-- In an additive group with an ultrametric norm, closed balls around 0 of positive
radius are open subgroups. -/]
/-
**IsUltrametricDist.closedBall_openSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `IsUltrame
tricDist`。
形式化陈述：closedBall_openSubgroup {r : Real} (hr : 0 < r) : OpenSubgroup S where car
rier
参数：hr : 0 < r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def closedBall_openSubgroup {r : ℝ} (hr : 0 < r) : OpenSubgroup S where
  carrier := Metric.closedBall (1 : S) r
  mul_mem' {x} {y} hx hy := by
    simp only [Metric.mem_closedBall, dist_eq_norm_inv_mul', inv_one, one_mul] at hx hy ⊢
    exact (norm_mul_le_max x y).trans (max_le hx hy)
  one_mem' := Metric.mem_closedBall_self hr.le
  inv_mem' := by simp only [mem_closedBall, dist_one_right, norm_inv', imp_self, implies_true]
  isOpen' := IsUltrametricDist.isOpen_closedBall _ hr.ne'

end nonarch

end Group

section CommGroup

variable {M ι : Type*} [SeminormedCommGroup M] [IsUltrametricDist M]

/-- A commutative group with an ultrametric group seminorm is nonarchimedean (as a topological
group, i.e. every neighborhood of 1 contains an open subgroup). -/
@[to_additive /-- A commutative additive group with an ultrametric group seminorm is nonarchimedean
(as a topological group, i.e. every neighborhood of 0 contains an open subgroup). -/]
/-
**IsUltrametricDist.nonarchimedeanGroup** 是 Mathlib 中的一个实例，位于命名空间 `IsUltrametric
Dist`。
形式化陈述：nonarchimedeanGroup : NonarchimedeanGroup M where is_nonarchimedean
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedCommGroup.toIsTopologicalGroup`：∀ {E : Type u_2} [inst : Semin
ormedCommGroup E], IsTopologicalGroup E
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance nonarchimedeanGroup : NonarchimedeanGroup M where
  is_nonarchimedean := by simpa only [Metric.mem_nhds_iff]
    using fun U ⟨ε, hεp, hεU⟩ ↦ ⟨ball_openSubgroup M hεp, hεU⟩

/-- Nonarchimedean norm of a product is less than or equal the norm of any term in the product.
This version is phrased using `Finset.sup'` and `Finset.Nonempty` due to `Finset.sup`
operating over an `OrderBot`, which `ℝ` is not. -/
@[to_additive /-- Nonarchimedean norm of a sum is less than or equal the norm of any term in the
sum. This version is phrased using `Finset.sup'` and `Finset.Nonempty` due to `Finset.sup`
operating over an `OrderBot`, which `ℝ` is not. -/]
/-
**IsUltrametricDist._root_.Finset.Nonempty.norm_prod_le_sup'_norm** 是 Mathlib 中的
一个引理，位于命名空间 `IsUltrametricDist`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Finset.Nonempty.norm_prod_le_sup'_norm {s : Finset ι} (hs : s.Nonempty) (f : ι → M) :
    ‖∏ i ∈ s, f i‖ ≤ s.sup' hs (‖f ·‖) := by
  simp only [Finset.le_sup'_iff]
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp only [Finset.mem_singleton, Finset.prod_singleton, exists_eq_left, le_refl]
  | cons j t hj _ IH =>
      simp only [Finset.prod_cons, Finset.mem_cons, exists_eq_or_imp]
      refine (le_total ‖∏ i ∈ t, f i‖ ‖f j‖).imp ?_ ?_ <;> intro h
      · exact (norm_mul_le_max _ _).trans (max_eq_left h).le
      · exact ⟨_, IH.choose_spec.left, (norm_mul_le_max _ _).trans <|
          ((max_eq_right h).le.trans IH.choose_spec.right)⟩

/-- Nonarchimedean norm of a product is less than or equal to the largest norm of a term in the
product. -/
@[to_additive /-- Nonarchimedean norm of a sum is less than or equal to the largest norm of a term
in the sum. -/]
/-
**IsUltrametricDist._root_.Finset.nnnorm_prod_le_sup_nnnorm** 是 Mathlib 中的一个引理，位
于命名空间 `IsUltrametricDist`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Finset.nnnorm_prod_le_sup_nnnorm (s : Finset ι) (f : ι → M) :
    ‖∏ i ∈ s, f i‖₊ ≤ s.sup (‖f ·‖₊) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · simpa only [← Finset.sup'_eq_sup hs, Finset.le_sup'_iff, coe_le_coe, coe_nnnorm']
      using! hs.norm_prod_le_sup'_norm f

/--
Generalised ultrametric triangle inequality for finite products in commutative groups with
an ultrametric norm.
-/
@[to_additive /-- Generalised ultrametric triangle inequality for finite sums in additive
commutative groups with an ultrametric norm. -/]
/-
**IsUltrametricDist.nnnorm_prod_le_of_forall_le** 是 Mathlib 中的一个引理，位于命名空间 `IsUlt
rametricDist`。
形式化陈述：nnnorm_prod_le_of_forall_le {s : Finset ι} {f : ι -> M} {C : Real>=0} (hC 
: forall i in s, ‖f i‖₊ <= C) : ‖∏ i in s, f i‖₊ <= C
参数：hC : forall i in s, ‖f i‖₊ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.nnnorm_prod_le_sup_nnnorm`：∀ {M : Type u_1} {ι : Type u_2} [inst 
: SeminormedCommGroup M] [IsUltrametricDist M] (s : Finset ι) (f : ι → M),   ‖∏ 
i ∈ s, f i‖₊ ≤ s.sup f…
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
-/
lemma nnnorm_prod_le_of_forall_le {s : Finset ι} {f : ι → M} {C : ℝ≥0}
    (hC : ∀ i ∈ s, ‖f i‖₊ ≤ C) : ‖∏ i ∈ s, f i‖₊ ≤ C :=
  (s.nnnorm_prod_le_sup_nnnorm f).trans <| Finset.sup_le hC

/--
Generalised ultrametric triangle inequality for nonempty finite products in commutative groups with
an ultrametric norm.
-/
@[to_additive /-- Generalised ultrametric triangle inequality for nonempty finite sums in additive
commutative groups with an ultrametric norm. -/]
/-
**IsUltrametricDist.norm_prod_le_of_forall_le_of_nonempty** 是 Mathlib 中的一个引理，位于命
名空间 `IsUltrametricDist`。
形式化陈述：norm_prod_le_of_forall_le_of_nonempty {s : Finset ι} (hs : s.Nonempty) {f 
: ι -> M} {C : Real} (hC : forall i in s, ‖f i‖ <= C) : ‖∏ i in s, f i‖ <= C
参数：hs : s.Nonempty；hC : forall i in s, ‖f i‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.norm_prod_le_sup'_norm`：∀ {M : Type u_1} {ι : Type u_2} 
[inst : SeminormedCommGroup M] [IsUltrametricDist M] {s : Finset ι} (hs : s.None
mpty)   (f : ι → M), ‖∏ i ∈ …
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
-/
lemma norm_prod_le_of_forall_le_of_nonempty {s : Finset ι} (hs : s.Nonempty) {f : ι → M} {C : ℝ}
    (hC : ∀ i ∈ s, ‖f i‖ ≤ C) : ‖∏ i ∈ s, f i‖ ≤ C :=
  (hs.norm_prod_le_sup'_norm f).trans (Finset.sup'_le hs _ hC)

/--
Generalised ultrametric triangle inequality for finite products in commutative groups with
an ultrametric norm.
-/
@[to_additive /-- Generalised ultrametric triangle inequality for finite sums in additive
commutative groups with an ultrametric norm. -/]
/-
**IsUltrametricDist.norm_prod_le_of_forall_le_of_nonneg** 是 Mathlib 中的一个引理，位于命名空
间 `IsUltrametricDist`。
形式化陈述：norm_prod_le_of_forall_le_of_nonneg {s : Finset ι} {f : ι -> M} {C : Real}
 (h_nonneg : 0 <= C) (hC : forall i in s, ‖f i‖ <= C) : ‖∏ i in s, f i‖ <= C
参数：h_nonneg : 0 <= C；hC : forall i in s, ‖f i‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `IsUltrametricDist.nnnorm_prod_le_of_forall_le`：nnnorm_prod_le_of_forall_
le {s : Finset ι} {f : ι -> M} {C : Real>=0} (hC : forall i in s, ‖f i‖₊ <= C) :
 ‖∏ i in s, f i‖₊ <= C
-/
lemma norm_prod_le_of_forall_le_of_nonneg {s : Finset ι} {f : ι → M} {C : ℝ}
    (h_nonneg : 0 ≤ C) (hC : ∀ i ∈ s, ‖f i‖ ≤ C) : ‖∏ i ∈ s, f i‖ ≤ C := by
  lift C to NNReal using h_nonneg
  exact nnnorm_prod_le_of_forall_le hC

/--
Given a function `f : ι → M` and a nonempty finite set `t ⊆ ι`, we can always find `i ∈ t` such that
`‖∏ j in t, f j‖ ≤ ‖f i‖`.
-/
@[to_additive /-- Given a function `f : ι → M` and a nonempty finite set `t ⊆ ι`, we can always find
`i ∈ t` such that `‖∑ j ∈ t, f j‖ ≤ ‖f i‖`. -/]
/-
**IsUltrametricDist.exists_norm_finsetProd_le_of_nonempty** 是 Mathlib 中的一个定理，位于命
名空间 `IsUltrametricDist`。
形式化陈述：exists_norm_finsetProd_le_of_nonempty {t : Finset ι} (ht : t.Nonempty) (f 
: ι -> M) : exists i in t, ‖∏ j in t, f j‖ <= ‖f i‖
参数：ht : t.Nonempty；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.exists_mem_eq_sup'`：exists_mem_eq_sup' (f : ι -> α) : exists i, i
 in s ∧ s.sup' H f = f i
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.Nonempty.norm_prod_le_sup'_norm`：∀ {M : Type u_1} {ι : Type u_2} 
[inst : SeminormedCommGroup M] [IsUltrametricDist M] {s : Finset ι} (hs : s.None
mpty)   (f : ι → M), ‖∏ i ∈ …
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem exists_norm_finsetProd_le_of_nonempty {t : Finset ι} (ht : t.Nonempty) (f : ι → M) :
    ∃ i ∈ t, ‖∏ j ∈ t, f j‖ ≤ ‖f i‖ :=
  match t.exists_mem_eq_sup' ht (‖f ·‖) with
  | ⟨j, hj, hj'⟩ => ⟨j, hj, (ht.norm_prod_le_sup'_norm f).trans (le_of_eq hj')⟩

@[deprecated (since := "2026-04-08")]
alias exists_norm_finset_sum_le_of_nonempty := exists_norm_finsetSum_le_of_nonempty

@[to_additive existing, deprecated (since := "2026-04-08")]
alias exists_norm_finset_prod_le_of_nonempty := exists_norm_finsetProd_le_of_nonempty

/--
Given a function `f : ι → M` and a finite set `t ⊆ ι`, we can always find `i : ι`, belonging to `t`
if `t` is nonempty, such that `‖∏ j ∈ t, f j‖ ≤ ‖f i‖`.
-/
@[to_additive /-- Given a function `f : ι → M` and a finite set `t ⊆ ι`, we can always find `i : ι`,
belonging to `t` if `t` is nonempty, such that `‖∑ j ∈ t, f j‖ ≤ ‖f i‖`. -/]
/-
**IsUltrametricDist.exists_norm_finsetProd_le** 是 Mathlib 中的一个定理，位于命名空间 `IsUltra
metricDist`。
形式化陈述：exists_norm_finsetProd_le (t : Finset ι) [Nonempty ι] (f : ι -> M) : exist
s i : ι, (t.Nonempty -> i in t) ∧ ‖∏ j in t, f j‖ <= ‖f i‖
参数：t : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_one'`：norm_one' : ‖(1 : E)‖ = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUltrametricDist.exists_norm_finsetProd_le_of_nonempty`：exists_norm_fin
setProd_le_of_nonempty {t : Finset ι} (ht : t.Nonempty) (f : ι -> M) : exists i 
in t, ‖∏ j in t, f j‖ <= ‖f i‖
-/
theorem exists_norm_finsetProd_le (t : Finset ι) [Nonempty ι] (f : ι → M) :
    ∃ i : ι, (t.Nonempty → i ∈ t) ∧ ‖∏ j ∈ t, f j‖ ≤ ‖f i‖ := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
  exact (fun ⟨i, h, h'⟩ => ⟨i, fun _ ↦ h, h'⟩) <| exists_norm_finsetProd_le_of_nonempty ht f

@[deprecated (since := "2026-04-08")] alias exists_norm_finset_sum_le := exists_norm_finsetSum_le

@[to_additive existing, deprecated (since := "2026-04-08")]
alias exists_norm_finset_prod_le := exists_norm_finsetProd_le

/--
Given a function `f : ι → M` and a multiset `t : Multiset ι`, we can always find `i : ι`, belonging
to `t` if `t` is nonempty, such that `‖(s.map f).prod‖ ≤ ‖f i‖`.
-/
@[to_additive /-- Given a function `f : ι → M` and a multiset `t : Multiset ι`, we can always find
`i : ι`, belonging to `t` if `t` is nonempty, such that `‖(s.map f).sum‖ ≤ ‖f i‖`. -/]
/-
**IsUltrametricDist.exists_norm_multiset_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `IsUl
trametricDist`。
形式化陈述：exists_norm_multiset_prod_le (s : Multiset ι) [Nonempty ι] {f : ι -> M} : 
exists i : ι, (s != 0 -> i in s) ∧ ‖(s.map f).prod‖ <= ‖f i‖
参数：s : Multiset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_one'`：norm_one' : ‖(1 : E)‖ = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `IsUltrametricDist.norm_mul_le_max`：norm_mul_le_max (x y : S) : ‖x * y‖ <
= max ‖x‖ ‖y‖
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem exists_norm_multiset_prod_le (s : Multiset ι) [Nonempty ι] {f : ι → M} :
    ∃ i : ι, (s ≠ 0 → i ∈ s) ∧ ‖(s.map f).prod‖ ≤ ‖f i‖ := by
  inhabit ι
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t hM =>
      obtain ⟨M, hMs, hM⟩ := hM
      by_cases! hMa : ‖f M‖ ≤ ‖f a‖
      · refine ⟨a, by simp, ?_⟩
        · rw [Multiset.map_cons, Multiset.prod_cons]
          exact le_trans (norm_mul_le_max _ _) (max_le (le_refl _) (le_trans hM hMa))
      · rcases eq_or_ne t 0 with rfl | ht
        · exact ⟨a, by simp, by simp⟩
        · refine ⟨M, ?_, ?_⟩
          · simp [hMs ht]
          rw [Multiset.map_cons, Multiset.prod_cons]
          exact le_trans (norm_mul_le_max _ _) (max_le hMa.le hM)

@[to_additive]
/-
**IsUltrametricDist.norm_tprod_le** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：norm_tprod_le (f : ι -> M) : ‖∏' i, f i‖ <= ⨆ i, ‖f i‖
参数：f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_empty`：tprod_empty [IsEmpty β] : ∏'[L] b, f b = 1
· 使用定理 `norm_one'`：norm_one' : ‖(1 : E)‖ = 0
· 使用定理 `Real.iSup_of_isEmpty`：∀ {ι : Sort u_1} [IsEmpty ι] (f : ι → ℝ), ⨆ i, f i
 = 0
· 使用定理 `Filter.Tendsto.bddAbove_range_of_cofinite`：Filter.Tendsto.bddAbove_range
_of_cofinite [IsDirectedOrder α] (h : Tendsto u cofinite (𝓝 a)) : BddAbove (Set.
range u)
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `Filter.Tendsto.norm'`：Filter.Tendsto.norm' (h : Tendsto f l (𝓝 a)) : Ten
dsto (fun x => ‖f x‖) l (𝓝 ‖a‖)
· 使用定理 `Multipliable.tendsto_cofinite_one`：Multipliable.tendsto_cofinite_one (hf
 : Multipliable f) : Tendsto f cofinite (𝓝 1)
· 使用定理 `NonarchimedeanGroup.toIsTopologicalGroup`：∀ {G : Type u_1} {inst : Group
 G} {inst_1 : TopologicalSpace G} [self : NonarchimedeanGroup G], IsTopologicalG
roup G
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用引理 `IsUltrametricDist.norm_prod_le_of_forall_le_of_nonneg`：norm_prod_le_of_f
orall_le_of_nonneg {s : Finset ι} {f : ι -> M} {C : Real} (h_nonneg : 0 <= C) (h
C : forall i in s, ‖f i‖ <= C) : ‖∏ i in s,…
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `tprod_eq_one_of_not_multipliable`：tprod_eq_one_of_not_multipliable (h : 
¬Multipliable f L) : ∏'[L] b, f b = 1
· 使用引理 `Real.iSup_of_not_bddAbove`：iSup_of_not_bddAbove (hf : ¬BddAbove (Set.ran
ge f)) : ⨆ i, f i = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma norm_tprod_le (f : ι → M) : ‖∏' i, f i‖ ≤ ⨆ i, ‖f i‖ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- Silly case #1 : the index type is empty
    simp only [tprod_empty, norm_one', Real.iSup_of_isEmpty, le_refl]
  by_cases h : Multipliable f; swap
  · -- Silly case #2 : the product is divergent
    rw [tprod_eq_one_of_not_multipliable h, norm_one']
    by_cases h_bd : BddAbove (Set.range fun i ↦ ‖f i‖)
    · exact le_ciSup_of_le h_bd hι.some (norm_nonneg' _)
    · rw [Real.iSup_of_not_bddAbove h_bd]
  -- now the interesting case
  have h_bd : BddAbove (Set.range fun i ↦ ‖f i‖) :=
    h.tendsto_cofinite_one.norm'.bddAbove_range_of_cofinite
  refine le_of_tendsto' h.hasProd.norm' (fun s ↦ norm_prod_le_of_forall_le_of_nonneg ?_ ?_)
  · exact le_ciSup_of_le h_bd hι.some (norm_nonneg' _)
  · exact fun i _ ↦ le_ciSup h_bd i

@[to_additive]
/-
**IsUltrametricDist.nnnorm_tprod_le** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist
`。
形式化陈述：nnnorm_tprod_le (f : ι -> M) : ‖∏' i, f i‖₊ <= ⨆ i, ‖f i‖₊
参数：f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_iSup`：coe_iSup {ι : Sort*} (s : ι -> Real>=0) : (↑(⨆ i, s i) 
: Real) = ⨆ i, ↑(s i)
· 使用引理 `IsUltrametricDist.norm_tprod_le`：norm_tprod_le (f : ι -> M) : ‖∏' i, f i
‖ <= ⨆ i, ‖f i‖
-/
lemma nnnorm_tprod_le (f : ι → M) : ‖∏' i, f i‖₊ ≤ ⨆ i, ‖f i‖₊ := by
  simpa only [← NNReal.coe_le_coe, coe_nnnorm', coe_iSup] using norm_tprod_le f

@[to_additive]
/-
**IsUltrametricDist.norm_tprod_le_of_forall_le** 是 Mathlib 中的一个引理，位于命名空间 `IsUltr
ametricDist`。
形式化陈述：norm_tprod_le_of_forall_le [Nonempty ι] {f : ι -> M} {C : Real} (h : foral
l i, ‖f i‖ <= C) : ‖∏' i, f i‖ <= C
参数：h : forall i, ‖f i‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `IsUltrametricDist.norm_tprod_le`：norm_tprod_le (f : ι -> M) : ‖∏' i, f i
‖ <= ⨆ i, ‖f i‖
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
-/
lemma norm_tprod_le_of_forall_le [Nonempty ι] {f : ι → M} {C : ℝ} (h : ∀ i, ‖f i‖ ≤ C) :
    ‖∏' i, f i‖ ≤ C :=
  (norm_tprod_le f).trans (ciSup_le h)

@[to_additive]
/-
**IsUltrametricDist.norm_tprod_le_of_forall_le_of_nonneg** 是 Mathlib 中的一个引理，位于命名
空间 `IsUltrametricDist`。
形式化陈述：norm_tprod_le_of_forall_le_of_nonneg {f : ι -> M} {C : Real} (hC : 0 <= C)
 (h : forall i, ‖f i‖ <= C) : ‖∏' i, f i‖ <= C
参数：hC : 0 <= C；h : forall i, ‖f i‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tprod_empty`：tprod_empty [IsEmpty β] : ∏'[L] b, f b = 1
· 使用定理 `norm_one'`：norm_one' : ‖(1 : E)‖ = 0
· 使用引理 `IsUltrametricDist.norm_tprod_le_of_forall_le`：norm_tprod_le_of_forall_le
 [Nonempty ι] {f : ι -> M} {C : Real} (h : forall i, ‖f i‖ <= C) : ‖∏' i, f i‖ <
= C
-/
lemma norm_tprod_le_of_forall_le_of_nonneg {f : ι → M} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖f i‖ ≤ C) :
    ‖∏' i, f i‖ ≤ C := by
  rcases isEmpty_or_nonempty ι
  · simpa only [tprod_empty, norm_one'] using hC
  · exact norm_tprod_le_of_forall_le h

@[to_additive]
/-
**IsUltrametricDist.nnnorm_tprod_le_of_forall_le** 是 Mathlib 中的一个引理，位于命名空间 `IsUl
trametricDist`。
形式化陈述：nnnorm_tprod_le_of_forall_le {f : ι -> M} {C : Real>=0} (h : forall i, ‖f 
i‖₊ <= C) : ‖∏' i, f i‖₊ <= C
参数：h : forall i, ‖f i‖₊ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `IsUltrametricDist.nnnorm_tprod_le`：nnnorm_tprod_le (f : ι -> M) : ‖∏' i,
 f i‖₊ <= ⨆ i, ‖f i‖₊
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
-/
lemma nnnorm_tprod_le_of_forall_le {f : ι → M} {C : ℝ≥0} (h : ∀ i, ‖f i‖₊ ≤ C) : ‖∏' i, f i‖₊ ≤ C :=
  (nnnorm_tprod_le f).trans (ciSup_le' h)

@[to_additive]
/-
**IsUltrametricDist.nnnorm_prod_eq_sup_of_pairwise_ne** 是 Mathlib 中的一个引理，位于命名空间 
`IsUltrametricDist`。
形式化陈述：nnnorm_prod_eq_sup_of_pairwise_ne {s : Finset ι} {f : ι -> M} (hs : Set.Pa
irwise s (fun i j => ‖f i‖₊ != ‖f j‖₊)) : ‖∏ i in s, f i‖₊ = s.sup (fun i => ‖f 
i‖₊)
参数：hs : Set.Pairwise s (fun i j => ‖f i‖₊ != ‖f j‖₊)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_one'`：nnnorm_one' : ‖(1 : E)‖₊ = 0
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
· 使用定理 `Finset.exists_mem_eq_sup`：exists_mem_eq_sup [OrderBot α] (s : Finset ι) 
(h : s.Nonempty) (f : ι -> α) : exists i, i in s ∧ s.sup f = f i
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用引理 `IsUltrametricDist.nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm`：nnnorm_mul_eq_m
ax_of_nnnorm_ne_nnnorm {x y : S} (h : ‖x‖₊ != ‖y‖₊) : ‖x * y‖₊ = max ‖x‖₊ ‖y‖₊
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
-/
lemma nnnorm_prod_eq_sup_of_pairwise_ne {s : Finset ι} {f : ι → M}
    (hs : Set.Pairwise s (fun i j ↦ ‖f i‖₊ ≠ ‖f j‖₊)) :
    ‖∏ i ∈ s, f i‖₊ = s.sup (fun i ↦ ‖f i‖₊) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha IH =>
    rcases s.eq_empty_or_nonempty with rfl | hs'
    · simp
    specialize IH (hs.mono (by simp))
    obtain ⟨j, hj, hj'⟩ : ∃ j ∈ s, ‖∏ i ∈ s, f i‖₊ = ‖f j‖₊ := by
      simpa [IH] using s.exists_mem_eq_sup hs' _
    suffices ‖f a‖₊ ≠ ‖∏ x ∈ s, f x‖₊ by simp [← IH, nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm this]
    rw [hj']
    apply hs <;> grind

@[to_additive]
/-
**IsUltrametricDist.norm_prod_eq_sup'_of_pairwise_ne** 是 Mathlib 中的一个定理，位于命名空间 `
IsUltrametricDist`。
形式化陈述：∀ {M : Type u_1} {ι : Type u_2} [inst : SeminormedCommGroup M] [IsUltramet
ricDist M] {s : Finset ι} {f : ι → M}   (hs' : s.Nonempty), ((↑s).Pairwise fun i
 j => ‖f i‖ ≠ ‖f j‖) → ‖∏ i ∈ s, f i‖ = s.sup' hs' fun i => ‖f i‖
参数：hs' : s.Nonempty；(↑s).Pairwise fun i j => ‖f i‖ ≠ ‖f j‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `coe_nnnorm'`：coe_nnnorm' (a : E) : (‖a‖₊ : Real) = ‖a‖
· 使用引理 `IsUltrametricDist.nnnorm_prod_eq_sup_of_pairwise_ne`：nnnorm_prod_eq_sup_
of_pairwise_ne {s : Finset ι} {f : ι -> M} (hs : Set.Pairwise s (fun i j => ‖f i
‖₊ != ‖f j‖₊)) : ‖∏ i in s, f i‖₊ = s.sup…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `Finset.apply_sup'_eq_sup'_comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Typ
e u_4} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup γ] {s : Finset β}   (H
 : s.Nonempty) {f : …
-/
lemma norm_prod_eq_sup'_of_pairwise_ne {s : Finset ι} {f : ι → M} (hs' : s.Nonempty)
    (hs : Set.Pairwise s (fun i j ↦ ‖f i‖ ≠ ‖f j‖)) :
    ‖∏ i ∈ s, f i‖ = s.sup' hs' (fun i ↦ ‖f i‖) := by
  rw [← coe_nnnorm', nnnorm_prod_eq_sup_of_pairwise_ne, ← Finset.sup'_eq_sup hs']
  · exact s.apply_sup'_eq_sup'_comp hs' _ (by tauto)
  · simpa [← NNReal.coe_inj] using hs

end CommGroup

end IsUltrametricDist

