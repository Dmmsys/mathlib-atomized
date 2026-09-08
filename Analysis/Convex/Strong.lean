/-
Copyright (c) 2023 Yaël Dillies, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Uniformly and strongly convex functions

In this file, we define uniformly convex functions and strongly convex functions.

For a real normed space `E`, a uniformly convex function with modulus `φ : ℝ → ℝ` is a function
`f : E → ℝ` such that `f (t • x + (1 - t) • y) ≤ t • f x + (1 - t) • f y - t * (1 - t) * φ ‖x - y‖`
for all `t ∈ [0, 1]`.

A `m`-strongly convex function is a uniformly convex function with modulus `fun r ↦ m / 2 * r ^ 2`.
If `E` is an inner product space, this is equivalent to `x ↦ f x - m / 2 * ‖x‖ ^ 2` being convex.

## TODO

Prove derivative properties of strongly convex functions.
-/

@[expose] public section

open Real

variable {E : Type*} [NormedAddCommGroup E]

section NormedSpace
variable [NormedSpace ℝ E] {φ ψ : ℝ → ℝ} {s : Set E} {m : ℝ} {f g : E → ℝ}

/-- A function `f` from a real normed space is uniformly convex with modulus `φ` if
`f (t • x + (1 - t) • y) ≤ t • f x + (1 - t) • f y - t * (1 - t) * φ ‖x - y‖` for all `t ∈ [0, 1]`.

`φ` is usually taken to be a monotone function such that `φ r = 0 ↔ r = 0`. -/
/-
**UniformConvexOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformConvexOn (s : Set E) (φ : Real -> Real) (f : E -> Real) : Prop
参数：s : Set E；φ : Real -> Real；f : E -> Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` from a real normed space is uniformly convex with modulus `φ` if
`f (t • x + (1 - t) • y) ≤ t • f x + (1 - t) • f y - t * (1 - t) * φ ‖x - y‖` fo
r all `t ∈ [0, 1]`.

`φ` is usually taken to be a monotone function such that `φ r = 0 ↔ r = 0`.
-/
def UniformConvexOn (s : Set E) (φ : ℝ → ℝ) (f : E → ℝ) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y - a * b * φ ‖x - y‖

/-- A function `f` from a real normed space is uniformly concave with modulus `φ` if
`t • f x + (1 - t) • f y + t * (1 - t) * φ ‖x - y‖ ≤ f (t • x + (1 - t) • y)` for all `t ∈ [0, 1]`.

`φ` is usually taken to be a monotone function such that `φ r = 0 ↔ r = 0`. -/
/-
**UniformConcaveOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformConcaveOn (s : Set E) (φ : Real -> Real) (f : E -> Real) : Prop
参数：s : Set E；φ : Real -> Real；f : E -> Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` from a real normed space is uniformly concave with modulus `φ` if
`t • f x + (1 - t) • f y + t * (1 - t) * φ ‖x - y‖ ≤ f (t • x + (1 - t) • y)` fo
r all `t ∈ [0, 1]`.

`φ` is usually taken to be a monotone function such that `φ r = 0 ↔ r = 0`.
-/
def UniformConcaveOn (s : Set E) (φ : ℝ → ℝ) (f : E → ℝ) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y + a * b * φ ‖x - y‖ ≤ f (a • x + b • y)
/-
**uniformConvexOn_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{s : Set E} {f : E → ℝ},   UniformConvexOn s 0 f ↔ ConvexOn ℝ s f
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma uniformConvexOn_zero : UniformConvexOn s 0 f ↔ ConvexOn ℝ s f := by
  simp [UniformConvexOn, ConvexOn]
/-
**uniformConcaveOn_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{s : Set E} {f : E → ℝ},   UniformConcaveOn s 0 f ↔ ConcaveOn ℝ s f
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma uniformConcaveOn_zero : UniformConcaveOn s 0 f ↔ ConcaveOn ℝ s f := by
  simp [UniformConcaveOn, ConcaveOn]

protected alias ⟨_, ConvexOn.uniformConvexOn_zero⟩ := uniformConvexOn_zero
protected alias ⟨_, ConcaveOn.uniformConcaveOn_zero⟩ := uniformConcaveOn_zero
/-
**UniformConvexOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformConvexOn.mono (hψφ : ψ <= φ) (hf : UniformConvexOn s φ f) : Uniform
ConvexOn s ψ f
参数：hψφ : ψ <= φ；hf : UniformConvexOn s φ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sub_le_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] [AddRightMono α] {a b : α},   a ≤ b → ∀ (c : α), c - b ≤ c - a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
-/
lemma UniformConvexOn.mono (hψφ : ψ ≤ φ) (hf : UniformConvexOn s φ f) : UniformConvexOn s ψ f :=
  ⟨hf.1, fun x hx y hy a b ha hb hab ↦ (hf.2 hx hy ha hb hab).trans <| by gcongr; apply hψφ⟩
/-
**UniformConcaveOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformConcaveOn.mono (hψφ : ψ <= φ) (hf : UniformConcaveOn s φ f) : Unifo
rmConcaveOn s ψ f
参数：hψφ : ψ <= φ；hf : UniformConcaveOn s φ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
-/
lemma UniformConcaveOn.mono (hψφ : ψ ≤ φ) (hf : UniformConcaveOn s φ f) : UniformConcaveOn s ψ f :=
  ⟨hf.1, fun x hx y hy a b ha hb hab ↦ (hf.2 hx hy ha hb hab).trans' <| by gcongr; apply hψφ⟩
/-
**UniformConvexOn.convexOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformConvexOn.convexOn (hf : UniformConvexOn s φ f) (hφ : 0 <= φ) : Conv
exOn Real s f
参数：hf : UniformConvexOn s φ f；hφ : 0 <= φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniformConvexOn.mono`：UniformConvexOn.mono (hψφ : ψ <= φ) (hf : UniformC
onvexOn s φ f) : UniformConvexOn s ψ f
-/
lemma UniformConvexOn.convexOn (hf : UniformConvexOn s φ f) (hφ : 0 ≤ φ) : ConvexOn ℝ s f := by
  simpa using hf.mono hφ
/-
**UniformConcaveOn.concaveOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformConcaveOn.concaveOn (hf : UniformConcaveOn s φ f) (hφ : 0 <= φ) : C
oncaveOn Real s f
参数：hf : UniformConcaveOn s φ f；hφ : 0 <= φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniformConcaveOn.mono`：UniformConcaveOn.mono (hψφ : ψ <= φ) (hf : Unifor
mConcaveOn s φ f) : UniformConcaveOn s ψ f
-/
lemma UniformConcaveOn.concaveOn (hf : UniformConcaveOn s φ f) (hφ : 0 ≤ φ) : ConcaveOn ℝ s f := by
  simpa using hf.mono hφ
/-
**UniformConvexOn.strictConvexOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformConvexOn.strictConvexOn (hf : UniformConvexOn s φ f) (hφ : forall r
, r != 0 -> 0 < φ r) : StrictConvexOn Real s f
参数：hf : UniformConvexOn s φ f；hφ : forall r, r != 0 -> 0 < φ r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `sub_lt_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] (a : α) {b : α}, 0 < b → a - b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
lemma UniformConvexOn.strictConvexOn (hf : UniformConvexOn s φ f) (hφ : ∀ r, r ≠ 0 → 0 < φ r) :
    StrictConvexOn ℝ s f := by
  refine ⟨hf.1, fun x hx y hy hxy a b ha hb hab ↦ (hf.2 hx hy ha.le hb.le hab).trans_lt <|
    sub_lt_self _ ?_⟩
  rw [← sub_ne_zero, ← norm_pos_iff] at hxy
  positivity [hφ _ hxy.ne']
/-
**UniformConcaveOn.strictConcaveOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformConcaveOn.strictConcaveOn (hf : UniformConcaveOn s φ f) (hφ : foral
l r, r != 0 -> 0 < φ r) : StrictConcaveOn Real s f
参数：hf : UniformConcaveOn s φ f；hφ : forall r, r != 0 -> 0 < φ r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
lemma UniformConcaveOn.strictConcaveOn (hf : UniformConcaveOn s φ f) (hφ : ∀ r, r ≠ 0 → 0 < φ r) :
    StrictConcaveOn ℝ s f := by
  refine ⟨hf.1, fun x hx y hy hxy a b ha hb hab ↦ (hf.2 hx hy ha.le hb.le hab).trans_lt' <|
    lt_add_of_pos_right _ ?_⟩
  rw [← sub_ne_zero, ← norm_pos_iff] at hxy
  positivity [hφ _ hxy.ne']
/-
**UniformConvexOn.add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformConvexOn.add (hf : UniformConvexOn s φ f) (hg : UniformConvexOn s ψ
 g) : UniformConvexOn s (φ + ψ) (f + g)
参数：hf : UniformConvexOn s φ f；hg : UniformConvexOn s ψ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_add_sub_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a - b + (c - d) = a + c - (b + d)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma UniformConvexOn.add (hf : UniformConvexOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConvexOn s (φ + ψ) (f + g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simpa [mul_add, add_add_add_comm, sub_add_sub_comm]
    using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
/-
**UniformConcaveOn.add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformConcaveOn.add (hf : UniformConcaveOn s φ f) (hg : UniformConcaveOn 
s ψ g) : UniformConcaveOn s (φ + ψ) (f + g)
参数：hf : UniformConcaveOn s φ f；hg : UniformConcaveOn s ψ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma UniformConcaveOn.add (hf : UniformConcaveOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f + g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simpa [mul_add, add_add_add_comm] using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
/-
**UniformConvexOn.neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformConvexOn.neg (hf : UniformConvexOn s φ f) : UniformConcaveOn s φ (-
f)
参数：hf : UniformConvexOn s φ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_of_neg_le_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dLeftMono α] {a b : α} [AddRightMono α], -a ≤ -b → b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma UniformConvexOn.neg (hf : UniformConvexOn s φ f) : UniformConcaveOn s φ (-f) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ le_of_neg_le_neg ?_⟩
  simpa [add_comm, -neg_le_neg_iff, le_sub_iff_add_le'] using hf.2 hx hy ha hb hab
/-
**UniformConcaveOn.neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformConcaveOn.neg (hf : UniformConcaveOn s φ f) : UniformConvexOn s φ (
-f)
参数：hf : UniformConcaveOn s φ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_of_neg_le_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dLeftMono α] {a b : α} [AddRightMono α], -a ≤ -b → b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma UniformConcaveOn.neg (hf : UniformConcaveOn s φ f) : UniformConvexOn s φ (-f) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ le_of_neg_le_neg ?_⟩
  simpa [add_comm, -neg_le_neg_iff, ← le_sub_iff_add_le', sub_eq_add_neg, neg_add]
    using hf.2 hx hy ha hb hab
/-
**UniformConvexOn.sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformConvexOn.sub (hf : UniformConvexOn s φ f) (hg : UniformConcaveOn s 
ψ g) : UniformConvexOn s (φ + ψ) (f - g)
参数：hf : UniformConvexOn s φ f；hg : UniformConcaveOn s ψ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniformConvexOn.add`：UniformConvexOn.add (hf : UniformConvexOn s φ f) (h
g : UniformConvexOn s ψ g) : UniformConvexOn s (φ + ψ) (f + g)
· 使用引理 `UniformConcaveOn.neg`：UniformConcaveOn.neg (hf : UniformConcaveOn s φ f)
 : UniformConvexOn s φ (-f)
-/
lemma UniformConvexOn.sub (hf : UniformConvexOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConvexOn s (φ + ψ) (f - g) := by simpa using! hf.add hg.neg
/-
**UniformConcaveOn.sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformConcaveOn.sub (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s
 ψ g) : UniformConcaveOn s (φ + ψ) (f - g)
参数：hf : UniformConcaveOn s φ f；hg : UniformConvexOn s ψ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniformConcaveOn.add`：UniformConcaveOn.add (hf : UniformConcaveOn s φ f)
 (hg : UniformConcaveOn s ψ g) : UniformConcaveOn s (φ + ψ) (f + g)
· 使用引理 `UniformConvexOn.neg`：UniformConvexOn.neg (hf : UniformConvexOn s φ f) : 
UniformConcaveOn s φ (-f)
-/
lemma UniformConcaveOn.sub (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f - g) := by simpa using! hf.add hg.neg

/-- A function `f` from a real normed space is `m`-strongly convex if it is uniformly convex with
modulus `φ(r) = m / 2 * r ^ 2`.

In an inner product space, this is equivalent to `x ↦ f x - m / 2 * ‖x‖ ^ 2` being convex. -/
/-
**StrongConvexOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StrongConvexOn (s : Set E) (m : Real) : (E -> Real) -> Prop
参数：s : Set E；m : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` from a real normed space is `m`-strongly convex if it is uniforml
y convex with
modulus `φ(r) = m / 2 * r ^ 2`.

In an inner product space, this is equivalent to `x ↦ f x - m / 2 * ‖x‖ ^ 2` bei
ng convex.
-/
def StrongConvexOn (s : Set E) (m : ℝ) : (E → ℝ) → Prop :=
  UniformConvexOn s fun r ↦ m / (2 : ℝ) * r ^ 2

/-- A function `f` from a real normed space is `m`-strongly concave if is strongly concave with
modulus `φ(r) = m / 2 * r ^ 2`.

In an inner product space, this is equivalent to `x ↦ f x + m / 2 * ‖x‖ ^ 2` being concave. -/
/-
**StrongConcaveOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StrongConcaveOn (s : Set E) (m : Real) : (E -> Real) -> Prop
参数：s : Set E；m : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` from a real normed space is `m`-strongly concave if is strongly c
oncave with
modulus `φ(r) = m / 2 * r ^ 2`.

In an inner product space, this is equivalent to `x ↦ f x + m / 2 * ‖x‖ ^ 2` bei
ng concave.
-/
def StrongConcaveOn (s : Set E) (m : ℝ) : (E → ℝ) → Prop :=
  UniformConcaveOn s fun r ↦ m / (2 : ℝ) * r ^ 2

variable {s : Set E} {f : E → ℝ} {m n : ℝ}

nonrec lemma StrongConvexOn.mono (hmn : m ≤ n) (hf : StrongConvexOn s n f) : StrongConvexOn s m f :=
  hf.mono fun r ↦ by gcongr

nonrec lemma StrongConcaveOn.mono (hmn : m ≤ n) (hf : StrongConcaveOn s n f) :
    StrongConcaveOn s m f := hf.mono fun r ↦ by gcongr
/-
**strongConvexOn_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{s : Set E} {f : E → ℝ},   StrongConvexOn s 0 f ↔ ConvexOn ℝ s f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma strongConvexOn_zero : StrongConvexOn s 0 f ↔ ConvexOn ℝ s f := by
  simp [StrongConvexOn, ← Pi.zero_def]
/-
**strongConcaveOn_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{s : Set E} {f : E → ℝ},   StrongConcaveOn s 0 f ↔ ConcaveOn ℝ s f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma strongConcaveOn_zero : StrongConcaveOn s 0 f ↔ ConcaveOn ℝ s f := by
  simp [StrongConcaveOn, ← Pi.zero_def]

nonrec lemma StrongConvexOn.strictConvexOn (hf : StrongConvexOn s m f) (hm : 0 < m) :
    StrictConvexOn ℝ s f := hf.strictConvexOn fun r hr ↦ by positivity

nonrec lemma StrongConcaveOn.strictConcaveOn (hf : StrongConcaveOn s m f) (hm : 0 < m) :
    StrictConcaveOn ℝ s f := hf.strictConcaveOn fun r hr ↦ by positivity

end NormedSpace

section InnerProductSpace
variable [InnerProductSpace ℝ E] {s : Set E} {a b m : ℝ} {x y : E} {f : E → ℝ}

/-
**aux_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_sub (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * (f x - m / (2 : ℝ) * ‖x‖ ^ 2) + b * (f y - m / (2 : ℝ) * ‖y‖ ^ 2) +
      m / (2 : ℝ) * ‖a • x + b • y‖ ^ 2
      = a * f x + b * f y - m / (2 : ℝ) * a * b * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    inner_smul_right, norm_of_nonneg ha, norm_of_nonneg hb, mul_pow, mul_pow]
  obtain rfl := eq_sub_of_add_eq hab
  ring_nf
/-
**aux_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_add (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * (f x + m / (2 : ℝ) * ‖x‖ ^ 2) + b * (f y + m / (2 : ℝ) * ‖y‖ ^ 2) -
      m / (2 : ℝ) * ‖a • x + b • y‖ ^ 2
      = a * f x + b * f y + m / (2 : ℝ) * a * b * ‖x - y‖ ^ 2 := by
  simpa [neg_div] using! aux_sub (E := E) (m := -m) ha hb hab
/-
**strongConvexOn_iff_convex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strongConvexOn_iff_convex : StrongConvexOn s m f ↔ ConvexOn Real s fun x =
> f x - m / (2 : Real) * ‖x‖ ^ 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `forall₄_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {p q : (a : α) → (b : β
 a)…
· 使用定理 `forall₅_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {ε : (a : α) → (b : β a
) →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `_private.Mathlib.Analysis.Convex.Strong.0.aux_sub`：∀ {E : Type u_1} [ins
t : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] {a b m : ℝ} {x y : E}
 {f : E → ℝ},   0 ≤ a →     0 ≤ b →    …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma strongConvexOn_iff_convex :
    StrongConvexOn s m f ↔ ConvexOn ℝ s fun x ↦ f x - m / (2 : ℝ) * ‖x‖ ^ 2 := by
  refine and_congr_right fun _ ↦ forall₄_congr fun x _ y _ ↦ forall₅_congr fun a b ha hb hab ↦ ?_
  simp_rw [sub_le_iff_le_add, smul_eq_mul, aux_sub ha hb hab, mul_assoc, mul_left_comm]
/-
**strongConcaveOn_iff_convex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strongConcaveOn_iff_convex : StrongConcaveOn s m f ↔ ConcaveOn Real s fun 
x => f x + m / (2 : Real) * ‖x‖ ^ 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `forall₄_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {p q : (a : α) → (b : β
 a)…
· 使用定理 `forall₅_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {ε : (a : α) → (b : β a
) →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `_private.Mathlib.Analysis.Convex.Strong.0.aux_add`：∀ {E : Type u_1} [ins
t : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] {a b m : ℝ} {x y : E}
 {f : E → ℝ},   0 ≤ a →     0 ≤ b →    …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma strongConcaveOn_iff_convex :
    StrongConcaveOn s m f ↔ ConcaveOn ℝ s fun x ↦ f x + m / (2 : ℝ) * ‖x‖ ^ 2 := by
  refine and_congr_right fun _ ↦ forall₄_congr fun x _ y _ ↦ forall₅_congr fun a b ha hb hab ↦ ?_
  simp_rw [← sub_le_iff_le_add, smul_eq_mul, aux_add ha hb hab, mul_assoc, mul_left_comm]

end InnerProductSpace

