/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Inheritance of normed algebraic structures by bounded continuous functions

For various types of normed algebraic structures `β`, we show in this file that the space of
bounded continuous functions from `α` to `β` inherits the same normed structure, by using
pointwise operations and checking that they are compatible with the uniform distance.
-/

@[expose] public section

assert_not_exists CStarRing

noncomputable section

open NNReal Set Function

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace BoundedContinuousFunction

section NormedAddCommGroup

variable [TopologicalSpace α] [SeminormedAddCommGroup β]
variable (f g : α →ᵇ β) {x : α} {C : ℝ}

/-
**BoundedContinuousFunction.instNorm** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuou
sFunction`。
形式化陈述：instNorm : Norm (α ->ᵇ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNorm : Norm (α →ᵇ β) := ⟨(dist · 0)⟩
/-
**BoundedContinuousFunction.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuou
sFunction`。
形式化陈述：norm_def : ‖f‖ = dist f 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def : ‖f‖ = dist f 0 := rfl

/-- The norm of a bounded continuous function is the supremum of `‖f x‖`.
We use `sInf` to ensure that the definition works if `α` has no elements. -/
/-
**BoundedContinuousFunction.norm_eq** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：norm_eq (f : α ->ᵇ β) : ‖f‖ = sInf { C : Real | 0 <= C ∧ forall x : α, ‖f 
x‖ <= C }
参数：f : α ->ᵇ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The norm of a bounded continuous function is the supremum of `‖f x‖`.
We use `sInf` to ensure that the definition works if `α` has no elements.
-/
theorem norm_eq (f : α →ᵇ β) : ‖f‖ = sInf { C : ℝ | 0 ≤ C ∧ ∀ x : α, ‖f x‖ ≤ C } := by
  simp [norm_def, BoundedContinuousFunction.dist_eq]

/-- When the domain is non-empty, we do not need the `0 ≤ C` condition in the formula for `‖f‖` as a
`sInf`. -/
/-
**BoundedContinuousFunction.norm_eq_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Bound
edContinuousFunction`。
形式化陈述：norm_eq_of_nonempty [h : Nonempty α] : ‖f‖ = sInf { C : Real | forall x : 
α, ‖f x‖ <= C }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.norm_eq`：norm_eq (f : α ->ᵇ β) : ‖f‖ = sInf { 
C : Real | 0 <= C ∧ forall x : α, ‖f x‖ <= C }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
When the domain is non-empty, we do not need the `0 ≤ C` condition in the formul
a for `‖f‖` as a
`sInf`.
-/
theorem norm_eq_of_nonempty [h : Nonempty α] : ‖f‖ = sInf { C : ℝ | ∀ x : α, ‖f x‖ ≤ C } := by
  obtain ⟨a⟩ := h
  rw [norm_eq]
  congr
  ext
  simp only [and_iff_right_iff_imp]
  exact fun h' => le_trans (norm_nonneg (f a)) (h' a)

@[simp]
/-
**BoundedContinuousFunction.norm_eq_zero_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `Bou
ndedContinuousFunction`。
形式化陈述：norm_eq_zero_of_empty [IsEmpty α] : ‖f‖ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.dist_zero_of_empty`：dist_zero_of_empty [IsEmpt
y α] : dist f g = 0
-/
theorem norm_eq_zero_of_empty [IsEmpty α] : ‖f‖ = 0 :=
  dist_zero_of_empty
/-
**BoundedContinuousFunction.norm_coe_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `BoundedC
ontinuousFunction`。
形式化陈述：norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
-/
theorem norm_coe_le_norm (x : α) : ‖f x‖ ≤ ‖f‖ :=
  calc
    ‖f x‖ = dist (f x) ((0 : α →ᵇ β) x) := by simp [dist_zero_right]
    _ ≤ ‖f‖ := dist_coe_le_dist _
/-
**BoundedContinuousFunction.neg_norm_le_apply** 是 Mathlib 中的一个引理，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：neg_norm_le_apply (f : α ->ᵇ Real) (x : α) : -‖f‖ <= f x
参数：f : α ->ᵇ Real；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖
-/
lemma neg_norm_le_apply (f : α →ᵇ ℝ) (x : α) :
    -‖f‖ ≤ f x := (abs_le.mp (norm_coe_le_norm f x)).1
/-
**BoundedContinuousFunction.apply_le_norm** 是 Mathlib 中的一个引理，位于命名空间 `BoundedCont
inuousFunction`。
形式化陈述：apply_le_norm (f : α ->ᵇ Real) (x : α) : f x <= ‖f‖
参数：f : α ->ᵇ Real；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖
-/
lemma apply_le_norm (f : α →ᵇ ℝ) (x : α) :
    f x ≤ ‖f‖ := (abs_le.mp (norm_coe_le_norm f x)).2
/-
**BoundedContinuousFunction.dist_le_two_norm'** 是 Mathlib 中的一个定理，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：dist_le_two_norm' {f : γ -> β} {C : Real} (hC : forall x, ‖f x‖ <= C) (x y
 : γ) : dist (f x) (f y) <= 2 * C
参数：hC : forall x, ‖f x‖ <= C；x y : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `dist_le_norm_add_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a
 b : E), dist a b ≤ ‖a‖ + ‖b‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
theorem dist_le_two_norm' {f : γ → β} {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x y : γ) :
    dist (f x) (f y) ≤ 2 * C :=
  calc
    dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
    _ ≤ C + C := add_le_add (hC x) (hC y)
    _ = 2 * C := (two_mul _).symm

/-- Distance between the images of any two points is at most twice the norm of the function. -/
/-
**BoundedContinuousFunction.dist_le_two_norm** 是 Mathlib 中的一个定理，位于命名空间 `BoundedC
ontinuousFunction`。
形式化陈述：dist_le_two_norm (x y : α) : dist (f x) (f y) <= 2 * ‖f‖
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.dist_le_two_norm'`：dist_le_two_norm' {f : γ ->
 β} {C : Real} (hC : forall x, ‖f x‖ <= C) (x y : γ) : dist (f x) (f y) <= 2 * C
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖

--- 原说明 ---
Distance between the images of any two points is at most twice the norm of the f
unction.
-/
theorem dist_le_two_norm (x y : α) : dist (f x) (f y) ≤ 2 * ‖f‖ :=
  dist_le_two_norm' f.norm_coe_le_norm x y

variable {f}

/-- The norm of a function is controlled by the supremum of the pointwise norms. -/
/-
**BoundedContinuousFunction.norm_le** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：norm_le (C0 : (0 : Real) <= C) : ‖f‖ <= C ↔ forall x : α, ‖f x‖ <= C
参数：C0 : (0 : Real) <= C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `BoundedContinuousFunction.dist_le`：dist_le (C0 : (0 : Real) <= C) : dist
 f g <= C ↔ forall x : α, dist (f x) (g x) <= C

--- 原说明 ---
The norm of a function is controlled by the supremum of the pointwise norms.
-/
theorem norm_le (C0 : (0 : ℝ) ≤ C) : ‖f‖ ≤ C ↔ ∀ x : α, ‖f x‖ ≤ C := by
  simpa using! @dist_le _ _ _ _ f 0 _ C0
/-
**BoundedContinuousFunction.norm_le_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Bound
edContinuousFunction`。
形式化陈述：norm_le_of_nonempty [Nonempty α] {f : α ->ᵇ β} {M : Real} : ‖f‖ <= M ↔ for
all x, ‖f x‖ <= M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoundedContinuousFunction.dist_le_iff_of_nonempty`：dist_le_iff_of_nonemp
ty [Nonempty α] : dist f g <= C ↔ forall x, dist (f x) (g x) <= C
-/
theorem norm_le_of_nonempty [Nonempty α] {f : α →ᵇ β} {M : ℝ} : ‖f‖ ≤ M ↔ ∀ x, ‖f x‖ ≤ M := by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_le_iff_of_nonempty
/-
**BoundedContinuousFunction.norm_lt_iff_of_compact** 是 Mathlib 中的一个定理，位于命名空间 `Bo
undedContinuousFunction`。
形式化陈述：norm_lt_iff_of_compact [CompactSpace α] {f : α ->ᵇ β} {M : Real} (M0 : 0 <
 M) : ‖f‖ < M ↔ forall x, ‖f x‖ < M
参数：M0 : 0 < M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoundedContinuousFunction.dist_lt_iff_of_compact`：dist_lt_iff_of_compact
 [CompactSpace α] (C0 : (0 : Real) < C) : dist f g < C ↔ forall x : α, dist (f x
) (g x) < C
-/
theorem norm_lt_iff_of_compact [CompactSpace α] {f : α →ᵇ β} {M : ℝ} (M0 : 0 < M) :
    ‖f‖ < M ↔ ∀ x, ‖f x‖ < M := by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_lt_iff_of_compact M0
/-
**BoundedContinuousFunction.norm_lt_iff_of_nonempty_compact** 是 Mathlib 中的一个定理，位
于命名空间 `BoundedContinuousFunction`。
形式化陈述：norm_lt_iff_of_nonempty_compact [Nonempty α] [CompactSpace α] {f : α ->ᵇ β
} {M : Real} : ‖f‖ < M ↔ forall x, ‖f x‖ < M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoundedContinuousFunction.dist_lt_iff_of_nonempty_compact`：dist_lt_iff_o
f_nonempty_compact [Nonempty α] [CompactSpace α] : dist f g < C ↔ forall x : α, 
dist (f x) (g x) < C
-/
theorem norm_lt_iff_of_nonempty_compact [Nonempty α] [CompactSpace α] {f : α →ᵇ β} {M : ℝ} :
    ‖f‖ < M ↔ ∀ x, ‖f x‖ < M := by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_lt_iff_of_nonempty_compact

variable (f)

/-- Norm of `const α b` is less than or equal to `‖b‖`. If `α` is nonempty,
then it is equal to `‖b‖`. -/
/-
**BoundedContinuousFunction.norm_const_le** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCont
inuousFunction`。
形式化陈述：norm_const_le (b : β) : ‖const α b‖ <= ‖b‖
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoundedContinuousFunction.norm_le`：norm_le (C0 : (0 : Real) <= C) : ‖f‖ 
<= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
Norm of `const α b` is less than or equal to `‖b‖`. If `α` is nonempty,
then it is equal to `‖b‖`.
-/
theorem norm_const_le (b : β) : ‖const α b‖ ≤ ‖b‖ :=
  (norm_le (norm_nonneg b)).2 fun _ => le_rfl

@[simp]
/-
**BoundedContinuousFunction.norm_const_eq** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCont
inuousFunction`。
形式化陈述：norm_const_eq [h : Nonempty α] (b : β) : ‖const α b‖ = ‖b‖
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `BoundedContinuousFunction.norm_const_le`：norm_const_le (b : β) : ‖const 
α b‖ <= ‖b‖
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖
-/
theorem norm_const_eq [h : Nonempty α] (b : β) : ‖const α b‖ = ‖b‖ :=
  le_antisymm (norm_const_le b) <| h.elim fun x => (const α b).norm_coe_le_norm x

/-- Constructing a bounded continuous function from a uniformly bounded continuous
function taking values in a normed group. -/
/-
**BoundedContinuousFunction.ofNormedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Boun
dedContinuousFunction`。
形式化陈述：ofNormedAddCommGroup {α : Type u} {β : Type v} [TopologicalSpace α] [Semin
ormedAddCommGroup β] (f : α -> β) (Hf : Continuous f) (C : Real) (H : forall x, 
‖f x‖ <= C) : α ->ᵇ β
参数：f : α -> β；Hf : Continuous f；C : Real；H : forall x, ‖f x‖ <= C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructing a bounded continuous function from a uniformly bounded continuous
function taking values in a normed group.
-/
def ofNormedAddCommGroup {α : Type u} {β : Type v} [TopologicalSpace α] [SeminormedAddCommGroup β]
    (f : α → β) (Hf : Continuous f) (C : ℝ) (H : ∀ x, ‖f x‖ ≤ C) : α →ᵇ β :=
  ⟨⟨fun n => f n, Hf⟩, ⟨_, dist_le_two_norm' H⟩⟩

@[simp]
/-
**BoundedContinuousFunction.coe_ofNormedAddCommGroup** 是 Mathlib 中的一个定理，位于命名空间 `
BoundedContinuousFunction`。
形式化陈述：coe_ofNormedAddCommGroup {α : Type u} {β : Type v} [TopologicalSpace α] [S
eminormedAddCommGroup β] (f : α -> β) (Hf : Continuous f) (C : Real) (H : forall
 x, ‖f x‖ <= C) : (ofNormedAddCommGroup f Hf C H : α -> β) = f
参数：f : α -> β；Hf : Continuous f；C : Real；H : forall x, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofNormedAddCommGroup {α : Type u} {β : Type v} [TopologicalSpace α]
    [SeminormedAddCommGroup β] (f : α → β) (Hf : Continuous f) (C : ℝ) (H : ∀ x, ‖f x‖ ≤ C) :
    (ofNormedAddCommGroup f Hf C H : α → β) = f := rfl
/-
**BoundedContinuousFunction.norm_ofNormedAddCommGroup_le** 是 Mathlib 中的一个定理，位于命名
空间 `BoundedContinuousFunction`。
形式化陈述：norm_ofNormedAddCommGroup_le {f : α -> β} (hfc : Continuous f) {C : Real} 
(hC : 0 <= C) (hfC : forall x, ‖f x‖ <= C) : ‖ofNormedAddCommGroup f hfc C hfC‖ 
<= C
参数：hfc : Continuous f；hC : 0 <= C；hfC : forall x, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoundedContinuousFunction.norm_le`：norm_le (C0 : (0 : Real) <= C) : ‖f‖ 
<= C ↔ forall x : α, ‖f x‖ <= C
-/
theorem norm_ofNormedAddCommGroup_le {f : α → β} (hfc : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hfC : ∀ x, ‖f x‖ ≤ C) : ‖ofNormedAddCommGroup f hfc C hfC‖ ≤ C :=
  (norm_le hC).2 hfC

/-- Constructing a bounded continuous function from a uniformly bounded
function on a discrete space, taking values in a normed group. -/
/-
**BoundedContinuousFunction.ofNormedAddCommGroupDiscrete** 是 Mathlib 中的一个定义，位于命名
空间 `BoundedContinuousFunction`。
形式化陈述：ofNormedAddCommGroupDiscrete {α : Type u} {β : Type v} [TopologicalSpace α
] [DiscreteTopology α] [SeminormedAddCommGroup β] (f : α -> β) (C : Real) (H : f
orall x, norm (f x) <= C) : α ->ᵇ β
参数：f : α -> β；C : Real；H : forall x, norm (f x) <= C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructing a bounded continuous function from a uniformly bounded
function on a discrete space, taking values in a normed group.
-/
def ofNormedAddCommGroupDiscrete {α : Type u} {β : Type v} [TopologicalSpace α] [DiscreteTopology α]
    [SeminormedAddCommGroup β] (f : α → β) (C : ℝ) (H : ∀ x, norm (f x) ≤ C) : α →ᵇ β :=
  ofNormedAddCommGroup f continuous_of_discreteTopology C H

@[simp]
/-
**BoundedContinuousFunction.coe_ofNormedAddCommGroupDiscrete** 是 Mathlib 中的一个定理，
位于命名空间 `BoundedContinuousFunction`。
形式化陈述：coe_ofNormedAddCommGroupDiscrete {α : Type u} {β : Type v} [TopologicalSpa
ce α] [DiscreteTopology α] [SeminormedAddCommGroup β] (f : α -> β) (C : Real) (H
 : forall x, ‖f x‖ <= C) : (ofNormedAddCommGroupDiscrete f C H : α -> β) = f
参数：f : α -> β；C : Real；H : forall x, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofNormedAddCommGroupDiscrete {α : Type u} {β : Type v} [TopologicalSpace α]
    [DiscreteTopology α] [SeminormedAddCommGroup β] (f : α → β) (C : ℝ) (H : ∀ x, ‖f x‖ ≤ C) :
    (ofNormedAddCommGroupDiscrete f C H : α → β) = f := rfl

/-- Taking the pointwise norm of a bounded continuous function with values in a
`SeminormedAddCommGroup` yields a bounded continuous function with values in ℝ. -/
/-
**BoundedContinuousFunction.normComp** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinuou
sFunction`。
形式化陈述：normComp : α ->ᵇ Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the pointwise norm of a bounded continuous function with values in a
`SeminormedAddCommGroup` yields a bounded continuous function with values in ℝ.
-/
def normComp : α →ᵇ ℝ :=
  f.comp norm lipschitzWith_one_norm

@[simp]
/-
**BoundedContinuousFunction.coe_normComp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedConti
nuousFunction`。
形式化陈述：coe_normComp : (f.normComp : α -> Real) = norm ∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_normComp : (f.normComp : α → ℝ) = norm ∘ f := rfl

@[simp]
/-
**BoundedContinuousFunction.norm_normComp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCont
inuousFunction`。
形式化陈述：norm_normComp : ‖f.normComp‖ = ‖f‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.norm_eq`：norm_eq (f : α ->ᵇ β) : ‖f‖ = sInf { 
C : Real | 0 <= C ∧ forall x : α, ‖f x‖ <= C }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_normComp : ‖f.normComp‖ = ‖f‖ := by
  simp only [norm_eq, coe_normComp, norm_norm, Function.comp]
/-
**BoundedContinuousFunction.bddAbove_range_norm_comp** 是 Mathlib 中的一个定理，位于命名空间 `
BoundedContinuousFunction`。
形式化陈述：bddAbove_range_norm_comp : BddAbove Set.range norm ∘ f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.bddAbove`：∀ {α : Type u_1} {s : Set α} [inst : Borno
logy α] [inst_1 : Preorder α] [IsOrderBornology α],   Bornology.IsBounded s → Bd
dAbove s
· 使用定理 `BoundedContinuousFunction.isBounded_range`：isBounded_range (f : α ->ᵇ β)
 : IsBounded (range f)
-/
theorem bddAbove_range_norm_comp : BddAbove <| Set.range <| norm ∘ f :=
  (@isBounded_range _ _ _ _ f.normComp).bddAbove
/-
**BoundedContinuousFunction.norm_eq_iSup_norm** 是 Mathlib 中的一个定理，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：norm_eq_iSup_norm : ‖f‖ = ⨆ x : α, ‖f x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.dist_eq_iSup`：dist_eq_iSup : dist f g = ⨆ x : 
α, dist (f x) (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_eq_iSup_norm : ‖f‖ = ⨆ x : α, ‖f x‖ := by
  simp_rw [norm_def, dist_eq_iSup, coe_zero, Pi.zero_apply, dist_zero_right]

/-- If `‖(1 : β)‖ = 1`, then `‖(1 : α →ᵇ β)‖ = 1` if `α` is nonempty. -/
/-
**BoundedContinuousFunction.instNormOneClass** 是 Mathlib 中的一个实例，位于命名空间 `BoundedC
ontinuousFunction`。
形式化陈述：instNormOneClass [Nonempty α] [One β] [NormOneClass β] : NormOneClass (α -
>ᵇ β) where norm_one
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.norm_eq_iSup_norm`：norm_eq_iSup_norm : ‖f‖ = ⨆
 x : α, ‖f x‖
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `‖(1 : β)‖ = 1`, then `‖(1 : α →ᵇ β)‖ = 1` if `α` is nonempty.
-/
instance instNormOneClass [Nonempty α] [One β] [NormOneClass β] : NormOneClass (α →ᵇ β) where
  norm_one := by simp only [norm_eq_iSup_norm, coe_one, Pi.one_apply, norm_one, ciSup_const]

/-- The pointwise opposite of a bounded continuous function is again bounded continuous. -/
/-
**BoundedContinuousFunction.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuousFunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pointwise opposite of a bounded continuous function is again bounded continu
ous.
-/
instance : Neg (α →ᵇ β) :=
  ⟨fun f =>
    ofNormedAddCommGroup (-f) f.continuous.neg ‖f‖ fun x =>
      norm_neg ((⇑f) x) ▸ f.norm_coe_le_norm x⟩

@[simp]
/-
**BoundedContinuousFunction.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：coe_neg : ⇑(-f) = -f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg : ⇑(-f) = -f := rfl
/-
**BoundedContinuousFunction.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuo
usFunction`。
形式化陈述：neg_apply : (-f) x = -f x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply : (-f) x = -f x := rfl

@[simp]
/-
**BoundedContinuousFunction.mkOfCompact_neg** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：mkOfCompact_neg [CompactSpace α] (f : C(α, β)) : mkOfCompact (-f) = -mkOfC
ompact f
参数：f : C(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem mkOfCompact_neg [CompactSpace α] (f : C(α, β)) : mkOfCompact (-f) = -mkOfCompact f := rfl

@[simp]
/-
**BoundedContinuousFunction.mkOfCompact_sub** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：mkOfCompact_sub [CompactSpace α] (f g : C(α, β)) : mkOfCompact (f - g) = m
kOfCompact f - mkOfCompact g
参数：f g : C(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem mkOfCompact_sub [CompactSpace α] (f g : C(α, β)) :
    mkOfCompact (f - g) = mkOfCompact f - mkOfCompact g := rfl

@[simp]
/-
**BoundedContinuousFunction.coe_zsmulRec** 是 Mathlib 中的一个定理，位于命名空间 `BoundedConti
nuousFunction`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : Seminorm
edAddCommGroup β]   (f : BoundedContinuousFunction α β) (z : ℤ), ⇑(zsmulRec (fun
 x1 x2 => x1 • x2) z f) = z • ⇑f
参数：f : BoundedContinuousFunction α β；z : ℤ；zsmulRec (fun x1 x2 => x1 • x2) z f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmulRec.eq_1`：∀ {G : Type u_1} [inst : Zero G] [inst_1 : Add G] [inst_2
 : Neg G] (nsmul : ℕ → G → G) (x : G) (n : ℕ),   zsmulRec nsmul (Int.ofNat n) x 
= n…
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `BoundedContinuousFunction.coe_nsmul`：∀ {α : Type u} {R : Type u_2} [inst
 : TopologicalSpace α] [inst_1 : PseudoMetricSpace R] [inst_2 : AddMonoid R]   [
inst_3 : BoundedAdd R] [i…
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `zsmulRec.eq_2`：∀ {G : Type u_1} [inst : Zero G] [inst_1 : Add G] [inst_2
 : Neg G] (nsmul : ℕ → G → G) (x : G) (n : ℕ),   zsmulRec nsmul (Int.negSucc n) 
x =…
· 使用定理 `negSucc_zsmul`：negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : Nat) : In
t.negSucc n • a = -((n + 1) • a)
· 使用定理 `BoundedContinuousFunction.coe_neg`：coe_neg : ⇑(-f) = -f
-/
theorem coe_zsmulRec : ∀ z, ⇑(zsmulRec (· • ·) z f) = z • ⇑f
  | Int.ofNat n => by rw [zsmulRec, Int.ofNat_eq_natCast, coe_nsmul, natCast_zsmul]
  | Int.negSucc n => by rw [zsmulRec, negSucc_zsmul, coe_neg, coe_nsmul]
/-
**BoundedContinuousFunction.instSMulInt** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：instSMulInt : SMul Int (α ->ᵇ β) where smul n f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
instance instSMulInt : SMul ℤ (α →ᵇ β) where
  smul n f :=
    { toContinuousMap := n • f.toContinuousMap
      map_bounded' := by simpa using (zsmulRec (· • ·) n f).map_bounded' }

@[simp]
/-
**BoundedContinuousFunction.coe_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuo
usFunction`。
形式化陈述：coe_zsmul (r : Int) (f : α ->ᵇ β) : ⇑(r • f) = r • ⇑f
参数：r : Int；f : α ->ᵇ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zsmul (r : ℤ) (f : α →ᵇ β) : ⇑(r • f) = r • ⇑f := rfl

@[simp]
/-
**BoundedContinuousFunction.zsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：zsmul_apply (r : Int) (f : α ->ᵇ β) (v : α) : (r • f) v = r • f v
参数：r : Int；f : α ->ᵇ β；v : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zsmul_apply (r : ℤ) (f : α →ᵇ β) (v : α) : (r • f) v = r • f v := rfl
/-
**BoundedContinuousFunction.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `BoundedC
ontinuousFunction`。
形式化陈述：instAddCommGroup : AddCommGroup (α ->ᵇ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedSub`：∀ {R : Type u_1} [inst : SeminormedAddCommGroup R], Boun
dedSub R
-/
instance instAddCommGroup : AddCommGroup (α →ᵇ β) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    fun _ _ => coe_zsmul _ _
/-
**BoundedContinuousFunction.instSeminormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间
 `BoundedContinuousFunction`。
形式化陈述：instSeminormedAddCommGroup : SeminormedAddCommGroup (α ->ᵇ β) where dist_e
q f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSeminormedAddCommGroup : SeminormedAddCommGroup (α →ᵇ β) where
  dist_eq f g := by simp only [norm_eq, dist_eq, dist_eq_norm_neg_add, add_apply, neg_apply]
/-
**BoundedContinuousFunction.instNormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Bo
undedContinuousFunction`。
形式化陈述：instNormedAddCommGroup {α β} [TopologicalSpace α] [NormedAddCommGroup β] :
 NormedAddCommGroup (α ->ᵇ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNormedAddCommGroup {α β} [TopologicalSpace α] [NormedAddCommGroup β] :
    NormedAddCommGroup (α →ᵇ β) :=
  { instSeminormedAddCommGroup with
    eq_of_dist_eq_zero }
/-
**BoundedContinuousFunction.nnnorm_def** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：nnnorm_def : ‖f‖₊ = nndist f 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nnnorm_def : ‖f‖₊ = nndist f 0 := rfl
/-
**BoundedContinuousFunction.nnnorm_coe_le_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `Boun
dedContinuousFunction`。
形式化陈述：nnnorm_coe_le_nnnorm (x : α) : ‖f x‖₊ <= ‖f‖₊
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖
-/
theorem nnnorm_coe_le_nnnorm (x : α) : ‖f x‖₊ ≤ ‖f‖₊ :=
  norm_coe_le_norm _ _
/-
**BoundedContinuousFunction.nndist_le_two_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `Boun
dedContinuousFunction`。
形式化陈述：nndist_le_two_nnnorm (x y : α) : nndist (f x) (f y) <= 2 * ‖f‖₊
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.dist_le_two_norm`：dist_le_two_norm (x y : α) :
 dist (f x) (f y) <= 2 * ‖f‖
-/
theorem nndist_le_two_nnnorm (x y : α) : nndist (f x) (f y) ≤ 2 * ‖f‖₊ :=
  dist_le_two_norm _ _ _

/-- The `nnnorm` of a function is controlled by the supremum of the pointwise `nnnorm`s. -/
/-
**BoundedContinuousFunction.nnnorm_le** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuo
usFunction`。
形式化陈述：nnnorm_le (C : Real>=0) : ‖f‖₊ <= C ↔ forall x : α, ‖f x‖₊ <= C
参数：C : Real>=0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.norm_le`：norm_le (C0 : (0 : Real) <= C) : ‖f‖ 
<= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
The `nnnorm` of a function is controlled by the supremum of the pointwise `nnnor
m`s.
-/
theorem nnnorm_le (C : ℝ≥0) : ‖f‖₊ ≤ C ↔ ∀ x : α, ‖f x‖₊ ≤ C :=
  norm_le C.prop
/-
**BoundedContinuousFunction.nnnorm_const_le** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：nnnorm_const_le (b : β) : ‖const α b‖₊ <= ‖b‖₊
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.norm_const_le`：norm_const_le (b : β) : ‖const 
α b‖ <= ‖b‖
-/
theorem nnnorm_const_le (b : β) : ‖const α b‖₊ ≤ ‖b‖₊ :=
  norm_const_le _

@[simp]
/-
**BoundedContinuousFunction.nnnorm_const_eq** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：nnnorm_const_eq [Nonempty α] (b : β) : ‖const α b‖₊ = ‖b‖₊
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `BoundedContinuousFunction.norm_const_eq`：norm_const_eq [h : Nonempty α] 
(b : β) : ‖const α b‖ = ‖b‖
-/
theorem nnnorm_const_eq [Nonempty α] (b : β) : ‖const α b‖₊ = ‖b‖₊ :=
  Subtype.ext <| norm_const_eq _
/-
**BoundedContinuousFunction.nnnorm_eq_iSup_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `Bou
ndedContinuousFunction`。
形式化陈述：nnnorm_eq_iSup_nnnorm : ‖f‖₊ = ⨆ x : α, ‖f x‖₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoundedContinuousFunction.norm_eq_iSup_norm`：norm_eq_iSup_norm : ‖f‖ = ⨆
 x : α, ‖f x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_iSup`：coe_iSup {ι : Sort*} (s : ι -> Real>=0) : (↑(⨆ i, s i) 
: Real) = ⨆ i, ↑(s i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnnorm_eq_iSup_nnnorm : ‖f‖₊ = ⨆ x : α, ‖f x‖₊ :=
  Subtype.ext <| (norm_eq_iSup_norm f).trans <| by simp_rw [val_eq_coe, NNReal.coe_iSup, coe_nnnorm]
/-
**BoundedContinuousFunction.enorm_eq_iSup_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Bound
edContinuousFunction`。
形式化陈述：enorm_eq_iSup_enorm : ‖f‖ₑ = ⨆ x, ‖f x‖ₑ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `BoundedContinuousFunction.edist_eq_iSup`：edist_eq_iSup : edist f g = ⨆ x
, edist (f x) (g x)
-/
theorem enorm_eq_iSup_enorm : ‖f‖ₑ = ⨆ x, ‖f x‖ₑ := by
  simpa only [← edist_zero_right] using! edist_eq_iSup
/-
**BoundedContinuousFunction.abs_sub_coe_le_dist** 是 Mathlib 中的一个定理，位于命名空间 `Bound
edContinuousFunction`。
形式化陈述：abs_sub_coe_le_dist : ‖f x - g x‖ <= dist f g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖
· 使用定理 `instBoundedSub`：∀ {R : Type u_1} [inst : SeminormedAddCommGroup R], Boun
dedSub R
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem abs_sub_coe_le_dist : ‖f x - g x‖ ≤ dist f g := by
  rw [dist_eq_norm]
  exact (f - g).norm_coe_le_norm x

@[deprecated (since := "2026-06-03")] alias abs_diff_coe_le_dist := abs_sub_coe_le_dist
/-
**BoundedContinuousFunction.coe_le_coe_add_dist** 是 Mathlib 中的一个定理，位于命名空间 `Bound
edContinuousFunction`。
形式化陈述：coe_le_coe_add_dist {f g : α ->ᵇ Real} : f x <= g x + dist f g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
-/
theorem coe_le_coe_add_dist {f g : α →ᵇ ℝ} : f x ≤ g x + dist f g :=
  sub_le_iff_le_add'.1 <| (abs_le.1 <| @dist_coe_le_dist _ _ _ _ f g x).2
/-
**BoundedContinuousFunction.norm_compContinuous_le** 是 Mathlib 中的一个定理，位于命名空间 `Bo
undedContinuousFunction`。
形式化陈述：norm_compContinuous_le [TopologicalSpace γ] (f : α ->ᵇ β) (g : C(γ, α)) : 
‖f.compContinuous g‖ <= ‖f‖
参数：f : α ->ᵇ β；g : C(γ, α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
· 使用定理 `BoundedContinuousFunction.lipschitz_compContinuous`：lipschitz_compContin
uous {δ : Type*} [TopologicalSpace δ] (g : C(δ, α)) : LipschitzWith 1 fun f : α 
->ᵇ β => f.compContinuous g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_one`：↑1 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem norm_compContinuous_le [TopologicalSpace γ] (f : α →ᵇ β) (g : C(γ, α)) :
    ‖f.compContinuous g‖ ≤ ‖f‖ :=
  ((lipschitz_compContinuous g).dist_le_mul f 0).trans <| by
    rw [NNReal.coe_one, one_mul, dist_zero_right]

end NormedAddCommGroup

section NormedSpace

variable {𝕜 : Type*}
variable [TopologicalSpace α] [SeminormedAddCommGroup β]
variable {f g : α →ᵇ β} {x : α} {C : ℝ}

/-
**BoundedContinuousFunction.instNormedSpace** 是 Mathlib 中的一个实例，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：instNormedSpace [NormedField 𝕜] [NormedSpace 𝕜 β] : NormedSpace 𝕜 (α ->ᵇ β
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNormedSpace [NormedField 𝕜] [NormedSpace 𝕜 β] : NormedSpace 𝕜 (α →ᵇ β) :=
  ⟨fun c f => by
    refine norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
    exact fun x =>
      norm_smul c (f x) ▸ mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)⟩

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 β]

section compLeftContinuousBounded

variable [SeminormedAddCommGroup γ] [NormedSpace 𝕜 γ]

variable (α) in
-- TODO does this work in the `IsBoundedSMul` setting, too?
/-- Postcomposition of bounded continuous functions into a normed module by a continuous linear map
is a continuous linear map.
Upgraded version of `ContinuousLinearMap.compLeftContinuous`, similar to `LinearMap.compLeft`. -/
/-
**BoundedContinuousFunction._root_.ContinuousLinearMap.compLeftContinuousBounded
** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinuousFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Postcomposition of bounded continuous functions into a normed module by a contin
uous linear map
is a continuous linear map.
Upgraded version of `ContinuousLinearMap.compLeftContinuous`, similar to `Linear
Map.compLeft`.
-/
protected def _root_.ContinuousLinearMap.compLeftContinuousBounded (g : β →L[𝕜] γ) :
    (α →ᵇ β) →L[𝕜] α →ᵇ γ :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        ofNormedAddCommGroup (g ∘ f) (g.continuous.comp f.continuous) (‖g‖ * ‖f‖) fun x =>
          g.le_opNorm_of_le (f.norm_coe_le_norm x)
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp } ‖g‖ fun f =>
        norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg g) (norm_nonneg f))
          (fun x => by exact g.le_opNorm_of_le (f.norm_coe_le_norm x))

@[simp]
/-
**BoundedContinuousFunction._root_.ContinuousLinearMap.compLeftContinuousBounded
_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuousFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.compLeftContinuousBounded_apply (g : β →L[𝕜] γ) (f : α →ᵇ β)
    (x : α) : (g.compLeftContinuousBounded α f) x = g (f x) := rfl

end compLeftContinuousBounded

section compContinuousCLM

variable {𝕜 : Type*}

section NormedField

variable [TopologicalSpace γ] [NormedField 𝕜] [NormedSpace 𝕜 β]

variable (β 𝕜) in
/-- Precomposition with a continuous map is a continuous linear map from bounded continuous
functions to bounded continuous functions. -/
/-
**BoundedContinuousFunction.compContinuousCLM** 是 Mathlib 中的一个定义，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：compContinuousCLM (g : C(γ, α)) : (α ->ᵇ β) ->L[𝕜] γ ->ᵇ β
参数：g : C(γ, α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Precomposition with a continuous map is a continuous linear map from bounded con
tinuous
functions to bounded continuous functions.
-/
def compContinuousCLM (g : C(γ, α)) : (α →ᵇ β) →L[𝕜] γ →ᵇ β :=
  LinearMap.mkContinuous
    { toFun f := f.compContinuous g,
      map_add' := by intros; ext; simp,
      map_smul' := by intros; ext; simp }
    1 (by simpa using norm_compContinuous_le · g)

@[simp]
/-
**BoundedContinuousFunction.compContinuousCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `B
oundedContinuousFunction`。
形式化陈述：compContinuousCLM_apply (f : α ->ᵇ β) (g : C(γ, α)) : f.compContinuousCLM 
β 𝕜 g = f.compContinuous g
参数：f : α ->ᵇ β；g : C(γ, α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem compContinuousCLM_apply (f : α →ᵇ β) (g : C(γ, α)) :
  f.compContinuousCLM β 𝕜 g = f.compContinuous g := rfl

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 β] [SeminormedAddCommGroup γ]

/-
**BoundedContinuousFunction.norm_compContinuousCLM_le_one** 是 Mathlib 中的一个定理，位于命
名空间 `BoundedContinuousFunction`。
形式化陈述：norm_compContinuousCLM_le_one (g : C(γ, α)) : ‖compContinuousCLM β 𝕜 g‖ <=
 1
参数：g : C(γ, α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `BoundedContinuousFunction.norm_compContinuous_le`：norm_compContinuous_le
 [TopologicalSpace γ] (f : α ->ᵇ β) (g : C(γ, α)) : ‖f.compContinuous g‖ <= ‖f‖
-/
theorem norm_compContinuousCLM_le_one (g : C(γ, α)) : ‖compContinuousCLM β 𝕜 g‖ ≤ 1 := by
  refine (compContinuousCLM β 𝕜 g).opNorm_le_bound zero_le_one (fun x ↦ ?_)
  simpa using norm_compContinuous_le x g

end NontriviallyNormedField

end compContinuousCLM

end NormedSpace

section NormedRing

variable [TopologicalSpace α] {R : Type*}

section NonUnital

section Seminormed

variable [NonUnitalSeminormedRing R]

/-
**BoundedContinuousFunction.instNonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：instNonUnitalRing : NonUnitalRing (α ->ᵇ R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
-/
instance instNonUnitalRing : NonUnitalRing (α →ᵇ R) := fast_instance%
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) fun _ _ => coe_zsmul _ _
/-
**BoundedContinuousFunction.instNonUnitalSeminormedRing** 是 Mathlib 中的一个实例，位于命名空
间 `BoundedContinuousFunction`。
形式化陈述：instNonUnitalSeminormedRing : NonUnitalSeminormedRing (α ->ᵇ R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalSeminormedRing : NonUnitalSeminormedRing (α →ᵇ R) where
  __ := instSeminormedAddCommGroup
  __ := instNonUnitalRing
  norm_mul_le f g := norm_ofNormedAddCommGroup_le _ (by positivity)
    (fun x ↦ (norm_mul_le _ _).trans <| mul_le_mul
      (norm_coe_le_norm f x) (norm_coe_le_norm g x) (norm_nonneg _) (norm_nonneg _))

/-- If the product of bounded continuous functions is zero, then the norm of their sum is the
maximum of their norms. -/
/-
**BoundedContinuousFunction.norm_add_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：norm_add_eq_max [IsCancelMulZero R] {f g : α ->ᵇ R} (h : f * g = 0) : ‖f +
 g‖ = max ‖f‖ ‖g‖
参数：h : f * g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `BoundedContinuousFunction.norm_le`：norm_le (C0 : (0 : Real) <= C) : ‖f‖ 
<= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the product of bounded continuous functions is zero, then the norm of their s
um is the
maximum of their norms.
-/
lemma norm_add_eq_max [IsCancelMulZero R] {f g : α →ᵇ R} (h : f * g = 0) :
    ‖f + g‖ = max ‖f‖ ‖g‖ := by
  have hfg : ∀ x, f x = 0 ∨ g x = 0 := by simpa [DFunLike.ext_iff, mul_eq_zero] using h
  have hfg' x : ‖(f + g) x‖ = max ‖f x‖ ‖g x‖ := by obtain (h | h) := hfg x <;> simp [h]
  have key (c : ℝ) (hc : 0 ≤ c) : ‖f + g‖ ≤ c ↔ max ‖f‖ ‖g‖ ≤ c := by
    simp_rw [norm_le hc, hfg', max_le_iff, norm_le hc, forall_and]
  exact le_antisymm (by rw [key]; positivity) (by rw [← key]; positivity)

/-- If the product of bounded continuous functions is zero, then the norm of their sum is the
maximum of their norms. -/
/-
**BoundedContinuousFunction.nnnorm_add_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：nnnorm_add_eq_max [IsCancelMulZero R] {f g : α ->ᵇ R} (h : f * g = 0) : ‖f
 + g‖₊ = max ‖f‖₊ ‖g‖₊
参数：h : f * g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用引理 `BoundedContinuousFunction.norm_add_eq_max`：norm_add_eq_max [IsCancelMulZ
ero R] {f g : α ->ᵇ R} (h : f * g = 0) : ‖f + g‖ = max ‖f‖ ‖g‖

--- 原说明 ---
If the product of bounded continuous functions is zero, then the norm of their s
um is the
maximum of their norms.
-/
lemma nnnorm_add_eq_max [IsCancelMulZero R] {f g : α →ᵇ R} (h : f * g = 0) :
    ‖f + g‖₊ = max ‖f‖₊ ‖g‖₊ :=
  NNReal.eq <| norm_add_eq_max h
/-
**BoundedContinuousFunction.norm_sub_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：norm_sub_eq_max [IsCancelMulZero R] {f g : α ->ᵇ R} (h : f * g = 0) : ‖f -
 g‖ = max ‖f‖ ‖g‖
参数：h : f * g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `instBoundedSub`：∀ {R : Type u_1} [inst : SeminormedAddCommGroup R], Boun
dedSub R
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用引理 `BoundedContinuousFunction.norm_add_eq_max`：norm_add_eq_max [IsCancelMulZ
ero R] {f g : α ->ᵇ R} (h : f * g = 0) : ‖f + g‖ = max ‖f‖ ‖g‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
lemma norm_sub_eq_max [IsCancelMulZero R] {f g : α →ᵇ R} (h : f * g = 0) :
    ‖f - g‖ = max ‖f‖ ‖g‖ := by
  simpa [sub_eq_add_neg] using norm_add_eq_max (f := f) (g := -g) (by simpa)
/-
**BoundedContinuousFunction.nnnorm_sub_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：nnnorm_sub_eq_max [IsCancelMulZero R] {f g : α ->ᵇ R} (h : f * g = 0) : ‖f
 - g‖₊ = max ‖f‖₊ ‖g‖₊
参数：h : f * g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `instBoundedSub`：∀ {R : Type u_1} [inst : SeminormedAddCommGroup R], Boun
dedSub R
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `BoundedContinuousFunction.norm_sub_eq_max`：norm_sub_eq_max [IsCancelMulZ
ero R] {f g : α ->ᵇ R} (h : f * g = 0) : ‖f - g‖ = max ‖f‖ ‖g‖
-/
lemma nnnorm_sub_eq_max [IsCancelMulZero R] {f g : α →ᵇ R} (h : f * g = 0) :
    ‖f - g‖₊ = max ‖f‖₊ ‖g‖₊ :=
  NNReal.eq <| norm_sub_eq_max h

open scoped Function in
/-- If the pairwise products of bounded continuous functions are all zero, then the norm of their
sum is the maximum of their norms. -/
/-
**BoundedContinuousFunction.nnnorm_sum_eq_sup** 是 Mathlib 中的一个引理，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：nnnorm_sum_eq_sup [IsCancelMulZero R] {ι : Type*} {f : ι -> (α ->ᵇ R)} (s 
: Finset ι) (h : Pairwise ((· * · = 0) on f)) : ‖∑ i in s, f i‖₊ = s.sup (‖f ·‖₊
)
参数：α ->ᵇ R；s : Finset ι；h : Pairwise ((· * · = 0) on f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `BoundedContinuousFunction.nnnorm_add_eq_max`：nnnorm_add_eq_max [IsCancel
MulZero R] {f g : α ->ᵇ R} (h : f * g = 0) : ‖f + g‖₊ = max ‖f‖₊ ‖g‖₊

--- 原说明 ---
If the pairwise products of bounded continuous functions are all zero, then the 
norm of their
sum is the maximum of their norms.
-/
lemma nnnorm_sum_eq_sup [IsCancelMulZero R] {ι : Type*} {f : ι → (α →ᵇ R)} (s : Finset ι)
    (h : Pairwise ((· * · = 0) on f)) :
    ‖∑ i ∈ s, f i‖₊ = s.sup (‖f ·‖₊) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i ∈ s, f i = 0 by simpa [hj, ← ih] using nnnorm_add_eq_max this
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi ↦ h (by grind)

end Seminormed

/-
**BoundedContinuousFunction.instNonUnitalSeminormedCommRing** 是 Mathlib 中的一个实例，位
于命名空间 `BoundedContinuousFunction`。
形式化陈述：instNonUnitalSeminormedCommRing [NonUnitalSeminormedCommRing R] : NonUnita
lSeminormedCommRing (α ->ᵇ R) where mul_comm _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalSeminormedCommRing [NonUnitalSeminormedCommRing R] :
    NonUnitalSeminormedCommRing (α →ᵇ R) where
  mul_comm _ _ := ext fun _ ↦ mul_comm ..
/-
**BoundedContinuousFunction.instNonUnitalNormedRing** 是 Mathlib 中的一个实例，位于命名空间 `B
oundedContinuousFunction`。
形式化陈述：instNonUnitalNormedRing [NonUnitalNormedRing R] : NonUnitalNormedRing (α -
>ᵇ R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNormedRing [NonUnitalNormedRing R] : NonUnitalNormedRing (α →ᵇ R) where
  __ := instNonUnitalSeminormedRing
  __ := instNormedAddCommGroup
/-
**BoundedContinuousFunction.instNonUnitalNormedCommRing** 是 Mathlib 中的一个实例，位于命名空
间 `BoundedContinuousFunction`。
形式化陈述：instNonUnitalNormedCommRing [NonUnitalNormedCommRing R] : NonUnitalNormedC
ommRing (α ->ᵇ R) where mul_comm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNormedCommRing [NonUnitalNormedCommRing R] :
    NonUnitalNormedCommRing (α →ᵇ R) where
  mul_comm := mul_comm

end NonUnital

section Seminormed

variable [SeminormedRing R]

@[simp]
/-
**BoundedContinuousFunction.coe_npowRec** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] {R : Type u_1} [inst_1 : Semino
rmedRing R]   (f : BoundedContinuousFunction α R) (n : ℕ), ⇑(npowRec n f) = ⇑f ^
 n
参数：f : BoundedContinuousFunction α R；n : ℕ；npowRec n f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
-/
theorem coe_npowRec (f : α →ᵇ R) : ∀ n, ⇑(npowRec n f) = (⇑f) ^ n
  | 0 => by rw [npowRec, pow_zero, coe_one]
  | n + 1 => by rw [npowRec, pow_succ, coe_mul, coe_npowRec f n]
/-
**BoundedContinuousFunction.hasNatPow** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuo
usFunction`。
形式化陈述：hasNatPow : Pow (α ->ᵇ R) Nat where pow f n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasNatPow : Pow (α →ᵇ R) ℕ where
  pow f n :=
    { toContinuousMap := f.toContinuousMap ^ n
      map_bounded' := by simpa [coe_npowRec] using (npowRec n f).map_bounded' }
/-
**BoundedContinuousFunction.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuousFunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (α →ᵇ R) :=
  ⟨fun n => BoundedContinuousFunction.const _ n⟩

@[simp, norm_cast]
/-
**BoundedContinuousFunction.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：coe_natCast (n : Nat) : ((n : α ->ᵇ R) : α -> R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_natCast (n : ℕ) : ((n : α →ᵇ R) : α → R) = n := rfl

@[simp, norm_cast]
/-
**BoundedContinuousFunction.coe_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuo
usFunction`。
形式化陈述：coe_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : α ->ᵇ R) : α -> R) = ofN
at(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : α →ᵇ R) : α → R) = ofNat(n) :=
  rfl
/-
**BoundedContinuousFunction.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuousFunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IntCast (α →ᵇ R) :=
  ⟨fun n => BoundedContinuousFunction.const _ n⟩

@[simp, norm_cast]
/-
**BoundedContinuousFunction.coe_intCast** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：coe_intCast (n : Int) : ((n : α ->ᵇ R) : α -> R) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_intCast (n : ℤ) : ((n : α →ᵇ R) : α → R) = n := rfl
/-
**BoundedContinuousFunction.instRing** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuou
sFunction`。
形式化陈述：instRing : Ring (α ->ᵇ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing : Ring (α →ᵇ R) := fast_instance%
  DFunLike.coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) (fun _ _ => coe_zsmul _ _) (fun _ _ => coe_pow _ _) coe_natCast
    coe_intCast
/-
**BoundedContinuousFunction.instSeminormedRing** 是 Mathlib 中的一个实例，位于命名空间 `Bounde
dContinuousFunction`。
形式化陈述：instSeminormedRing : SeminormedRing (α ->ᵇ R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSeminormedRing : SeminormedRing (α →ᵇ R) where
  __ := instRing
  __ := instNonUnitalSeminormedRing

/-- Composition on the left by a (lipschitz-continuous) homomorphism of topological semirings, as a
`RingHom`. Similar to `RingHom.compLeftContinuous`. -/
@[simps!]
/-
**BoundedContinuousFunction._root_.RingHom.compLeftContinuousBounded** 是 Mathlib
 中的一个定义，位于命名空间 `BoundedContinuousFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition on the left by a (lipschitz-continuous) homomorphism of topological 
semirings, as a
`RingHom`. Similar to `RingHom.compLeftContinuous`.
-/
protected def _root_.RingHom.compLeftContinuousBounded (α : Type*)
    [TopologicalSpace α] [SeminormedRing β] [SeminormedRing γ]
    (g : β →+* γ) {C : NNReal} (hg : LipschitzWith C g) : (α →ᵇ β) →+* (α →ᵇ γ) :=
  { g.toMonoidHom.compLeftContinuousBounded α hg,
    g.toAddMonoidHom.compLeftContinuousBounded α hg with }

end Seminormed

/-
**BoundedContinuousFunction.instNormedRing** 是 Mathlib 中的一个实例，位于命名空间 `BoundedCon
tinuousFunction`。
形式化陈述：instNormedRing [NormedRing R] : NormedRing (α ->ᵇ R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNormedRing [NormedRing R] : NormedRing (α →ᵇ R) where
  __ := instRing
  __ := instNonUnitalNormedRing

end NormedRing

section NormedCommRing

variable [TopologicalSpace α] {R : Type*}

/-
**BoundedContinuousFunction.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `BoundedConti
nuousFunction`。
形式化陈述：instCommRing [SeminormedCommRing R] : CommRing (α ->ᵇ R) where mul_comm _ 
_
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommRing [SeminormedCommRing R] : CommRing (α →ᵇ R) where
  mul_comm _ _ := ext fun _ ↦ mul_comm _ _
/-
**BoundedContinuousFunction.instSeminormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Bo
undedContinuousFunction`。
形式化陈述：instSeminormedCommRing [SeminormedCommRing R] : SeminormedCommRing (α ->ᵇ 
R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSeminormedCommRing [SeminormedCommRing R] : SeminormedCommRing (α →ᵇ R) where
  __ := instCommRing
  __ := instNonUnitalSeminormedRing
/-
**BoundedContinuousFunction.instNormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Bounde
dContinuousFunction`。
形式化陈述：instNormedCommRing [NormedCommRing R] : NormedCommRing (α ->ᵇ R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNormedCommRing [NormedCommRing R] : NormedCommRing (α →ᵇ R) where
  __ := instSeminormedCommRing
  __ := instNormedAddCommGroup

end NormedCommRing

section NonUnitalAlgebra

-- these hypotheses could be generalized if we generalize `IsBoundedSMul` to `Bornology`.
variable {𝕜 : Type*} [PseudoMetricSpace 𝕜] [TopologicalSpace α] [NonUnitalSeminormedRing β]
variable [Zero 𝕜] [SMul 𝕜 β] [IsBoundedSMul 𝕜 β]

/-
**BoundedContinuousFunction.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuousFunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsScalarTower 𝕜 β β] : IsScalarTower 𝕜 (α →ᵇ β) (α →ᵇ β) where
  smul_assoc _ _ _ := ext fun _ ↦ smul_mul_assoc ..
/-
**BoundedContinuousFunction.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuousFunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass 𝕜 β β] : SMulCommClass 𝕜 (α →ᵇ β) (α →ᵇ β) where
  smul_comm _ _ _ := ext fun _ ↦ (mul_smul_comm ..).symm
/-
**BoundedContinuousFunction.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuousFunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass 𝕜 β β] : SMulCommClass (α →ᵇ β) 𝕜 (α →ᵇ β) where
  smul_comm _ _ _ := ext fun _ ↦ mul_smul_comm ..

end NonUnitalAlgebra

section NormedAlgebra

variable {𝕜 : Type*} [NormedField 𝕜] [TopologicalSpace α]
variable [NormedRing γ] [NormedAlgebra 𝕜 γ]

/-- `BoundedContinuousFunction.const` as a `RingHom`. -/
/-
**BoundedContinuousFunction.C** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinuousFuncti
on`。
形式化陈述：C : 𝕜 ->+* α ->ᵇ γ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BoundedContinuousFunction.const` as a `RingHom`.
-/
def C : 𝕜 →+* α →ᵇ γ where
  toFun := fun c : 𝕜 => const α ((algebraMap 𝕜 γ) c)
  map_one' := ext fun _ => (algebraMap 𝕜 γ).map_one
  map_mul' _ _ := ext fun _ => (algebraMap 𝕜 γ).map_mul _ _
  map_zero' := ext fun _ => (algebraMap 𝕜 γ).map_zero
  map_add' _ _ := ext fun _ => (algebraMap 𝕜 γ).map_add _ _
/-
**BoundedContinuousFunction.instAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：instAlgebra : Algebra 𝕜 (α ->ᵇ γ) where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAlgebra : Algebra 𝕜 (α →ᵇ γ) where
  algebraMap := C
  commutes' _ _ := ext fun _ ↦ Algebra.commutes' _ _
  smul_def' _ _ := ext fun _ ↦ Algebra.smul_def' _ _

@[simp]
/-
**BoundedContinuousFunction.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedC
ontinuousFunction`。
形式化陈述：algebraMap_apply (k : 𝕜) (a : α) : algebraMap 𝕜 (α ->ᵇ γ) k a = k • (1 : γ
)
参数：k : 𝕜；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_apply (k : 𝕜) (a : α) : algebraMap 𝕜 (α →ᵇ γ) k a = k • (1 : γ) := by
  simp only [Algebra.algebraMap_eq_smul_one, coe_smul, coe_one, Pi.one_apply]
/-
**BoundedContinuousFunction.instNormedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：instNormedAlgebra : NormedAlgebra 𝕜 (α ->ᵇ γ) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNormedAlgebra : NormedAlgebra 𝕜 (α →ᵇ γ) where
  __ := instAlgebra
  __ := instNormedSpace

variable (𝕜)

/-- Composition on the left by a (lipschitz-continuous) homomorphism of topological `R`-algebras,
as an `AlgHom`. Similar to `AlgHom.compLeftContinuous`. -/
@[simps!]
/-
**BoundedContinuousFunction.AlgHom.compLeftContinuousBounded** 是 Mathlib 中的一个定义，
位于命名空间 `BoundedContinuousFunction.AlgHom`。
形式化陈述：{α : Type u} →   {β : Type v} →     {γ : Type w} →       (𝕜 : Type u_1) → 
        [inst : NormedField 𝕜] →           [inst_1 : TopologicalSpace α] →      
       [inst_2 : NormedRing γ] →               [inst_3 : NormedAlgebra 𝕜 γ] →   
              [inst_4 : NormedRing β] →                   [inst_5 : NormedAlgebr
a 𝕜 β] →                     (g : β →ₐ[𝕜] γ) →                       {C : NNReal
} →                         LipschitzWith C ⇑g → BoundedContinuousFunction α β →
ₐ[𝕜] BoundedContinuousFunction α γ
参数：𝕜 : Type u_1；g : β →ₐ[𝕜] γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition on the left by a (lipschitz-continuous) homomorphism of topological 
`R`-algebras,
as an `AlgHom`. Similar to `AlgHom.compLeftContinuous`.
-/
protected def AlgHom.compLeftContinuousBounded [NormedRing β] [NormedAlgebra 𝕜 β]
    (g : β →ₐ[𝕜] γ) {C : NNReal} (hg : LipschitzWith C g) : (α →ᵇ β) →ₐ[𝕜] (α →ᵇ γ) :=
  { g.toRingHom.compLeftContinuousBounded α hg with
    commutes' := fun _ => DFunLike.ext _ _ fun _ => g.commutes' _ }

/-- The algebra-homomorphism forgetting that a bounded continuous function is bounded. -/
@[simps]
/-
**BoundedContinuousFunction.toContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：{α : Type u} →   {β : Type v} → [inst : TopologicalSpace α] → [inst_1 : Ps
eudoMetricSpace β] → BoundedContinuousFunction α β → C(α, β)
参数：α, β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra-homomorphism forgetting that a bounded continuous function is bounde
d.
-/
def toContinuousMapₐ : (α →ᵇ γ) →ₐ[𝕜] C(α, γ) where
  toFun := (↑)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
/-
**BoundedContinuousFunction.coe_toContinuousMap** 是 Mathlib 中的一个定理，位于命名空间 `Bound
edContinuousFunction`。
形式化陈述：coe_toContinuousMap (f : α ->ᵇ β) : (f.toContinuousMap : α -> β) = f
参数：f : α ->ᵇ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousMapₐ (f : α →ᵇ γ) : (f.toContinuousMapₐ 𝕜 : α → γ) = f := rfl

variable {𝕜} [SeminormedAddCommGroup β] [NormedSpace 𝕜 β]

/-! ### Structure as normed module over scalar functions

If `β` is a normed `𝕜`-space, then we show that the space of bounded continuous
functions from `α` to `β` is naturally a module over the algebra of bounded continuous
functions from `α` to `𝕜`. -/

/-
**BoundedContinuousFunction.instSMul'** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuo
usFunction`。
形式化陈述：instSMul' : SMul (α ->ᵇ 𝕜) (α ->ᵇ β) where smul f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Structure as normed module over scalar functions

If `β` is a normed `𝕜`-space, then we show that the space of bounded continuous
functions from `α` to `β` is naturally a module over the algebra of bounded cont
inuous
functions from `α` to `𝕜`.
-/
instance instSMul' : SMul (α →ᵇ 𝕜) (α →ᵇ β) where
  smul f g :=
    ofNormedAddCommGroup (fun x => f x • g x) (f.continuous.smul g.continuous) (‖f‖ * ‖g‖) fun x =>
      calc
        ‖f x • g x‖ ≤ ‖f x‖ * ‖g x‖ := norm_smul_le _ _
        _ ≤ ‖f‖ * ‖g‖ :=
          mul_le_mul (f.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
/-
**BoundedContinuousFunction.instModule'** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：instModule' : Module (α ->ᵇ 𝕜) (α ->ᵇ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule' : Module (α →ᵇ 𝕜) (α →ᵇ β) :=
  Module.ofMinimalAxioms
      (fun c _ _ => ext fun a => smul_add (c a) _ _)
      (fun _ _ _ => ext fun _ => add_smul _ _ _)
      (fun _ _ _ => ext fun _ => mul_smul _ _ _)
      (fun f => ext fun x => one_smul 𝕜 (f x))

/- TODO: When `NormedModule` has been added to `Analysis.Normed.Module.Basic`, this
shows that the space of bounded continuous functions from `α` to `β` is naturally a normed
module over the algebra of bounded continuous functions from `α` to `𝕜`. -/
/-
**BoundedContinuousFunction.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuousFunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
TODO: When `NormedModule` has been added to `Analysis.Normed.Module.Basic`, this
shows that the space of bounded continuous functions from `α` to `β` is naturall
y a normed
module over the algebra of bounded continuous functions from `α` to `𝕜`.
-/
instance : IsBoundedSMul (α →ᵇ 𝕜) (α →ᵇ β) :=
  IsBoundedSMul.of_norm_smul_le fun _ _ =>
    norm_ofNormedAddCommGroup_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

end NormedAlgebra

section NormedLatticeOrderedGroup

variable [TopologicalSpace α]
  [NormedAddCommGroup β] [Lattice β] [HasSolidNorm β] [IsOrderedAddMonoid β]

/-
**BoundedContinuousFunction.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `BoundedC
ontinuousFunction`。
形式化陈述：instPartialOrder : PartialOrder (α ->ᵇ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrder : PartialOrder (α →ᵇ β) :=
  PartialOrder.lift (fun f => f.toFun) (by simp [Injective])
/-
**BoundedContinuousFunction.instSup** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：instSup : Max (α ->ᵇ β) where max f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSup : Max (α →ᵇ β) where
  max f g :=
    { toFun := f ⊔ g
      continuous_toFun := f.continuous.sup g.continuous
      map_bounded' := by
        obtain ⟨C₁, hf⟩ := f.bounded
        obtain ⟨C₂, hg⟩ := g.bounded
        refine ⟨C₁ + C₂, fun x y ↦ ?_⟩
        simp_rw [dist_eq_norm_sub] at hf hg ⊢
        exact (norm_sup_sub_sup_le_add_norm _ _ _ _).trans (add_le_add (hf _ _) (hg _ _)) }
/-
**BoundedContinuousFunction.instInf** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：instInf : Min (α ->ᵇ β) where min f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInf : Min (α →ᵇ β) where
  min f g :=
    { toFun := f ⊓ g
      continuous_toFun := f.continuous.inf g.continuous
      map_bounded' := by
        obtain ⟨C₁, hf⟩ := f.bounded
        obtain ⟨C₂, hg⟩ := g.bounded
        refine ⟨C₁ + C₂, fun x y ↦ ?_⟩
        simp_rw [dist_eq_norm_sub] at hf hg ⊢
        exact (norm_inf_sub_inf_le_add_norm _ _ _ _).trans (add_le_add (hf _ _) (hg _ _)) }
/-
**BoundedContinuousFunction.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : NormedAd
dCommGroup β] [inst_2 : Lattice β]   [inst_3 : HasSolidNorm β] [inst_4 : IsOrder
edAddMonoid β] (f g : BoundedContinuousFunction α β), ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
参数：f g : BoundedContinuousFunction α β；f ⊔ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_sup (f g : α →ᵇ β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g := rfl
/-
**BoundedContinuousFunction.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : NormedAd
dCommGroup β] [inst_2 : Lattice β]   [inst_3 : HasSolidNorm β] [inst_4 : IsOrder
edAddMonoid β] (f g : BoundedContinuousFunction α β), ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
参数：f g : BoundedContinuousFunction α β；f ⊓ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inf (f g : α →ᵇ β) : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g := rfl
/-
**BoundedContinuousFunction.instSemilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Bounde
dContinuousFunction`。
形式化陈述：instSemilatticeSup : SemilatticeSup (α ->ᵇ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeSup : SemilatticeSup (α →ᵇ β) := fast_instance%
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup
/-
**BoundedContinuousFunction.instSemilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Bounde
dContinuousFunction`。
形式化陈述：instSemilatticeInf : SemilatticeInf (α ->ᵇ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeInf : SemilatticeInf (α →ᵇ β) := fast_instance%
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf
/-
**BoundedContinuousFunction.instLattice** 是 Mathlib 中的一个实例，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：instLattice : Lattice (α ->ᵇ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLattice : Lattice (α →ᵇ β) := fast_instance%
  DFunLike.coe_injective.lattice _ .rfl .rfl coe_sup coe_inf
/-
**BoundedContinuousFunction.coe_abs** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : NormedAd
dCommGroup β] [inst_2 : Lattice β]   [inst_3 : HasSolidNorm β] [inst_4 : IsOrder
edAddMonoid β] (f : BoundedContinuousFunction α β), ⇑|f| = |⇑f|
参数：f : BoundedContinuousFunction α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_abs (f : α →ᵇ β) : ⇑|f| = |⇑f| := rfl
/-
**BoundedContinuousFunction.coe_posPart** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : NormedAd
dCommGroup β] [inst_2 : Lattice β]   [inst_3 : HasSolidNorm β] [inst_4 : IsOrder
edAddMonoid β] (f : BoundedContinuousFunction α β), ⇑f⁺ = (⇑f)⁺
参数：f : BoundedContinuousFunction α β；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_posPart (f : α →ᵇ β) : ⇑f⁺ = (⇑f)⁺ := rfl
/-
**BoundedContinuousFunction.coe_negPart** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContin
uousFunction`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : NormedAd
dCommGroup β] [inst_2 : Lattice β]   [inst_3 : HasSolidNorm β] [inst_4 : IsOrder
edAddMonoid β] (f : BoundedContinuousFunction α β), ⇑f⁻ = (⇑f)⁻
参数：f : BoundedContinuousFunction α β；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_negPart (f : α →ᵇ β) : ⇑f⁻ = (⇑f)⁻ := rfl
/-
**BoundedContinuousFunction.instHasSolidNorm** 是 Mathlib 中的一个实例，位于命名空间 `BoundedC
ontinuousFunction`。
形式化陈述：instHasSolidNorm : HasSolidNorm (α ->ᵇ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSolidNorm.solid`：∀ {α : Type u_1} {inst : NormedAddCommGroup α} {inst
_1 : Lattice α} [self : HasSolidNorm α] ⦃x y : α⦄,   |x| ≤ |y| → ‖x‖ ≤ ‖y‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.norm_le`：norm_le (C0 : (0 : Real) <= C) : ‖f‖ 
<= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖
-/
instance instHasSolidNorm : HasSolidNorm (α →ᵇ β) :=
  { solid := by
      intro f g h
      have i1 : ∀ t, ‖f t‖ ≤ ‖g t‖ := fun t => HasSolidNorm.solid (h t)
      rw [norm_le (norm_nonneg _)]
      exact fun t => (i1 t).trans (norm_coe_le_norm g t) }
/-
**BoundedContinuousFunction.instIsOrderedAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Bo
undedContinuousFunction`。
形式化陈述：instIsOrderedAddMonoid : IsOrderedAddMonoid (α ->ᵇ β) where add_le_add_lef
t f g h₁ h t
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid (α →ᵇ β) where
  add_le_add_left f g h₁ h t := by simpa using h₁ _

end NormedLatticeOrderedGroup

section NonnegativePart

variable [TopologicalSpace α]

/-- The nonnegative part of a bounded continuous `ℝ`-valued function as a bounded
continuous `ℝ≥0`-valued function. -/
/-
**BoundedContinuousFunction.nnrealPart** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：nnrealPart (f : α ->ᵇ Real) : α ->ᵇ Real>=0
参数：f : α ->ᵇ Real。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nonnegative part of a bounded continuous `ℝ`-valued function as a bounded
continuous `ℝ≥0`-valued function.
-/
def nnrealPart (f : α →ᵇ ℝ) : α →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.comp _ (show LipschitzWith 1 Real.toNNReal from lipschitzWith_posPart) f

@[simp]
/-
**BoundedContinuousFunction.nnrealPart_coeFn_eq** 是 Mathlib 中的一个定理，位于命名空间 `Bound
edContinuousFunction`。
形式化陈述：nnrealPart_coeFn_eq (f : α ->ᵇ Real) : ⇑f.nnrealPart = Real.toNNReal ∘ ⇑f
参数：f : α ->ᵇ Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nnrealPart_coeFn_eq (f : α →ᵇ ℝ) : ⇑f.nnrealPart = Real.toNNReal ∘ ⇑f := rfl

/-- The absolute value of a bounded continuous `ℝ`-valued function as a bounded
continuous `ℝ≥0`-valued function. -/
/-
**BoundedContinuousFunction.nnnorm** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinuousF
unction`。
形式化陈述：nnnorm (f : α ->ᵇ Real) : α ->ᵇ Real>=0
参数：f : α ->ᵇ Real。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The absolute value of a bounded continuous `ℝ`-valued function as a bounded
continuous `ℝ≥0`-valued function.
-/
def nnnorm (f : α →ᵇ ℝ) : α →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.comp _
    (show LipschitzWith 1 fun x : ℝ => ‖x‖₊ from lipschitzWith_one_norm) f

@[simp]
/-
**BoundedContinuousFunction.nnnorm_coeFn_eq** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：nnnorm_coeFn_eq (f : α ->ᵇ Real) : ⇑f.nnnorm = NNNorm.nnnorm ∘ ⇑f
参数：f : α ->ᵇ Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nnnorm_coeFn_eq (f : α →ᵇ ℝ) : ⇑f.nnnorm = NNNorm.nnnorm ∘ ⇑f := rfl

-- TODO: Use `posPart` and `negPart` here
/-- Decompose a bounded continuous function to its positive and negative parts. -/
/-
**BoundedContinuousFunction.self_eq_nnrealPart_sub_nnrealPart_neg** 是 Mathlib 中的
一个定理，位于命名空间 `BoundedContinuousFunction`。
形式化陈述：self_eq_nnrealPart_sub_nnrealPart_neg (f : α ->ᵇ Real) : ⇑f = (↑) ∘ f.nnre
alPart - (↑) ∘ (-f).nnrealPart
参数：f : α ->ᵇ Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_zero_sub_max_neg_zero_eq_self`：∀ {α : Type u_1} [inst : AddGroup α] 
[inst_1 : LinearOrder α] [AddLeftMono α] (a : α), max a 0 - max (-a) 0 = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Decompose a bounded continuous function to its positive and negative parts.
-/
theorem self_eq_nnrealPart_sub_nnrealPart_neg (f : α →ᵇ ℝ) :
    ⇑f = (↑) ∘ f.nnrealPart - (↑) ∘ (-f).nnrealPart := by
  funext x
  dsimp
  simp only [max_zero_sub_max_neg_zero_eq_self]

/-- Express the absolute value of a bounded continuous function in terms of its
positive and negative parts. -/
/-
**BoundedContinuousFunction.abs_self_eq_nnrealPart_add_nnrealPart_neg** 是 Mathli
b 中的一个定理，位于命名空间 `BoundedContinuousFunction`。
形式化陈述：abs_self_eq_nnrealPart_add_nnrealPart_neg (f : α ->ᵇ Real) : abs ∘ ⇑f = (↑
) ∘ f.nnrealPart + (↑) ∘ (-f).nnrealPart
参数：f : α ->ᵇ Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_zero_add_max_neg_zero_eq_abs_self`：∀ {G : Type u_1} [inst : AddCommG
roup G] [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] (a : G),   max a 0 + max
 (-a) 0 = |a|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Express the absolute value of a bounded continuous function in terms of its
positive and negative parts.
-/
theorem abs_self_eq_nnrealPart_add_nnrealPart_neg (f : α →ᵇ ℝ) :
    abs ∘ ⇑f = (↑) ∘ f.nnrealPart + (↑) ∘ (-f).nnrealPart := by
  funext x
  dsimp
  simp only [max_zero_add_max_neg_zero_eq_abs_self]

end NonnegativePart

section

variable {α : Type*} [TopologicalSpace α]

-- TODO: `f + const _ ‖f‖` is just `f⁺`
/-
**BoundedContinuousFunction.add_norm_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：add_norm_nonneg (f : α ->ᵇ Real) : 0 <= f + const _ ‖f‖
参数：f : α ->ᵇ Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoundedContinuousFunction.const_apply`：∀ (α : Type u) {β : Type v} [inst
 : TopologicalSpace α] [inst_1 : PseudoMetricSpace β] (b : β),   ⇑(BoundedContin
uousFunction.const α b) = f…
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 43 条，此处仅展示前 30 条）
-/
lemma add_norm_nonneg (f : α →ᵇ ℝ) :
    0 ≤ f + const _ ‖f‖ := by
  intro x
  simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, coe_zero, Pi.zero_apply, coe_add,
    const_apply, Pi.add_apply]
  linarith [(abs_le.mp (norm_coe_le_norm f x)).1]
/-
**BoundedContinuousFunction.norm_sub_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：norm_sub_nonneg (f : α ->ᵇ Real) : 0 <= const _ ‖f‖ - f
参数：f : α ->ᵇ Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedSub`：∀ {R : Type u_1} [inst : SeminormedAddCommGroup R], Boun
dedSub R
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoundedContinuousFunction.const_apply`：∀ (α : Type u) {β : Type v} [inst
 : TopologicalSpace α] [inst_1 : PseudoMetricSpace β] (b : β),   ⇑(BoundedContin
uousFunction.const α b) = f…
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 40 条，此处仅展示前 30 条）
-/
lemma norm_sub_nonneg (f : α →ᵇ ℝ) :
    0 ≤ const _ ‖f‖ - f := by
  intro x
  simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, coe_zero, Pi.zero_apply, coe_sub,
    const_apply, Pi.sub_apply]
  linarith [(abs_le.mp (norm_coe_le_norm f x)).2]

end

end BoundedContinuousFunction

