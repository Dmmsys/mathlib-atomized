/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Patrick Massot, Floris van Doorn, Jireh Loreaux, Eric Wieser,
Yongxi Lin, Louis (Yiyang) Liu
-/
module

public import Mathlib.Topology.Order.OrderClosedExtr
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Ordered

/-!
# The First- and Second-Derivative Tests

We prove the first-derivative test from calculus, in the strong form given on [Wikipedia](https://en.wikipedia.org/wiki/Derivative_test#First-derivative_test).

The test is proved over the real numbers ℝ
using `monotoneOn_of_deriv_nonneg` from `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`.

We prove the second-derivative test using the first-derivative test.
Source: [Wikipedia](https://en.wikipedia.org/wiki/Derivative_test#Proof_of_the_second-derivative_test).

## Main results

* `isLocalMax_of_deriv_Ioo`: Suppose `f` is a real-valued function of a real variable
  defined on some interval containing the point `a`.
  Further suppose that `f` is continuous at `a` and differentiable on some open interval
  containing `a`, except possibly at `a` itself.

  If there exists a positive number `r > 0` such that for every `x` in `Ioo (a − r) a`
  we have `f′(x) ≥ 0`, and for every `x` in `Ioo a (a + r)` we have `f′(x) ≤ 0`,
  then `f` has a local maximum at `a`.

* `isLocalMin_of_deriv_Ioo`: The dual of `first_derivative_max`, for minima.

* `isLocalMax_of_deriv`: 1st derivative test for maxima using filters.

* `isLocalMin_of_deriv`: 1st derivative test for minima using filters.

* `isLocalMin_of_deriv_deriv_pos`: The second-derivative test, minimum version.


## Tags

derivative test, first-derivative test, second-derivative test, calculus
-/

public section


open Set Topology

/-- If `f` is continuous at `b` and differentiable on `Ioo a b`, then `f` is continuous on
`Ioc a b`. -/
/-
**continuousOn_Ioc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is continuous at `b` and differentiable on `Ioo a b`, then `f` is continu
ous on
`Ioc a b`.
-/
private lemma continuousOn_Ioc {f : ℝ → ℝ} {a b : ℝ} (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) : ContinuousOn f (Ioc a b) := by
  by_cases! g₀ : a < b
  · exact Ioo_union_right g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Ioc_eq_empty_of_le g₀]

/-- If `f` is continuous at `a` and differentiable on `Ioo a b`, then `f` is continuous on
`Ico a b`. -/
/-
**continuousOn_Ico** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is continuous at `a` and differentiable on `Ioo a b`, then `f` is continu
ous on
`Ico a b`.
-/
private lemma continuousOn_Ico {f : ℝ → ℝ} {a b : ℝ} (h : ContinuousAt f a)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) : ContinuousOn f (Ico a b) := by
  by_cases! g₀ : a < b
  · exact Ioo_union_left g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Ico_eq_empty_of_le g₀]

/-- If `f` is continuous at `a, b` and differentiable on `Ioo a b`, then `f` is continuous on
`Icc a b`. -/
/-
**continuousOn_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is continuous at `a, b` and differentiable on `Ioo a b`, then `f` is cont
inuous on
`Icc a b`.
-/
private lemma continuousOn_Icc {f : ℝ → ℝ} {a b : ℝ} (ha : ContinuousAt f a)
    (hb : ContinuousAt f b) (hd₀ : DifferentiableOn ℝ f (Ioo a b)) : ContinuousOn f (Icc a b) := by
  by_cases! g₀ : a ≤ b
  · exact Ioo_union_both g₀ ▸ hd₀.continuousOn.union_continuousAt isOpen_Ioo (by simp_all)
  · simp [Icc_eq_empty_of_lt g₀]

/-- If `f` is continuous at `b` and differentiable on `Iio b`, then `f` is continuous on
`Iic b`. -/
/-
**continuousOn_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is continuous at `b` and differentiable on `Iio b`, then `f` is continuou
s on
`Iic b`.
-/
private lemma continuousOn_Iic {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Iio b)) : ContinuousOn f (Iic b) := by
  simp_rw [← Iio_union_right]
  apply hd₀.continuousOn.union_continuousAt isOpen_Iio (by simp [h])

/-- If `f` is continuous at `a` and differentiable on `Ioi a`, then `f` is continuous on
`Ici a`. -/
/-
**continuousOn_Ici** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is continuous at `a` and differentiable on `Ioi a`, then `f` is continuou
s on
`Ici a`.
-/
private lemma continuousOn_Ici {f : ℝ → ℝ} {a : ℝ} (h : ContinuousAt f a)
    (hd₀ : DifferentiableOn ℝ f (Ioi a)) : ContinuousOn f (Ici a) := by
  rw [← Ioi_union_left]
  exact hd₀.continuousOn.union_continuousAt isOpen_Ioi (by simp [h])

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonnegative on `Ioo a b` and
nonpositive on `Ioo b c`. Then `f` attains its maximum on `Ioo a c` at `b`. -/
/-
**isMaxOn_Ioo_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Ioo_of_deriv {f : Real -> Real} {a b c : Real} (h : ContinuousAt f
 b) (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Io
o b c)) (h₀ : forall x in Ioo a b, 0 <= deriv f x) (h₁ : forall x in Ioo b c, de
riv f x <= 0) : IsMaxOn f (Ioo a c) b
参数：h : ContinuousAt f b；hd₀ : DifferentiableOn Real f (Ioo a b)；hd₁ : Differenti
ableOn Real f (Ioo b c)；h₀ : forall x in Ioo a b, 0 <= deriv f x；h₁ : forall x i
n Ioo b c, deriv f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Ioo_of_mono_anti`：isMaxOn_Ioo_of_mono_anti (h₀ : MonotoneOn f (I
oc a b)) (h₁ : AntitoneOn f (Ico b c)) : IsMaxOn f (Ioo a c) b
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ioc`：convex_Ioc (r s : β) : Convex 𝕜 (Ioc r s)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ioc`：∀ 
{f : ℝ → ℝ} {a b : ℝ}, ContinuousAt f b → DifferentiableOn ℝ f (Set.Ioo a b) → C
ontinuousOn f (Set.Ioc a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Ioc`：interior_Ioc [NoMaxOrder α] {a b : α} : interior (Ioc a b)
 = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ico`：convex_Ico (r s : β) : Convex 𝕜 (Ico r s)
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ico`：∀ 
{f : ℝ → ℝ} {a b : ℝ}, ContinuousAt f a → DifferentiableOn ℝ f (Set.Ioo a b) → C
ontinuousOn f (Set.Ico a b)
· 使用定理 `interior_Ico`：interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b)
 = Ioo a b
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonnegative on 
`Ioo a b` and
nonpositive on `Ioo b c`. Then `f` attains its maximum on `Ioo a c` at `b`.
-/
lemma isMaxOn_Ioo_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) :
    IsMaxOn f (Ioo a c) b := by
  refine isMaxOn_Ioo_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc h hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico h hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b` and `c`, the derivative `f'` is nonnegative on
`Ioo a b` and nonpositive on `Ioo b c`. Then `f` attains its maximum on `Ioc a c` at `b`. -/
/-
**isMaxOn_Ioc_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Ioc_of_deriv {f : Real -> Real} {a b c : Real} (hb : ContinuousAt 
f b) (hc : ContinuousAt f c) (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : Di
fferentiableOn Real f (Ioo b c)) (h₀ : forall x in Ioo a b, 0 <= deriv f x) (h₁ 
: forall x in Ioo b c, deriv f x <= 0) : IsMaxOn f (Ioc a c) b
参数：hb : ContinuousAt f b；hc : ContinuousAt f c；hd₀ : DifferentiableOn Real f (Io
o a b)；hd₁ : DifferentiableOn Real f (Ioo b c)；h₀ : forall x in Ioo a b, 0 <= de
riv f x；h₁ : forall x in Ioo b c, deriv f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Ioc_of_mono_anti`：isMaxOn_Ioc_of_mono_anti (h₀ : MonotoneOn f (I
oc a b)) (h₁ : AntitoneOn f (Icc b c)) : IsMaxOn f (Ioc a c) b
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ioc`：convex_Ioc (r s : β) : Convex 𝕜 (Ioc r s)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ioc`：∀ 
{f : ℝ → ℝ} {a b : ℝ}, ContinuousAt f b → DifferentiableOn ℝ f (Set.Ioo a b) → C
ontinuousOn f (Set.Ioc a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Ioc`：interior_Ioc [NoMaxOrder α] {a b : α} : interior (Ioc a b)
 = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Icc`：∀ 
{f : ℝ → ℝ} {a b : ℝ},   ContinuousAt f a → ContinuousAt f b → DifferentiableOn 
ℝ f (Set.Ioo a b) → ContinuousOn f (Set.Icc a b)
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `b` and `c`, the derivative `f'` is nonnega
tive on
`Ioo a b` and nonpositive on `Ioo b c`. Then `f` attains its maximum on `Ioc a c
` at `b`.
-/
lemma isMaxOn_Ioc_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) :
    IsMaxOn f (Ioc a c) b := by
  refine isMaxOn_Ioc_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `a` and `b`, the derivative `f'` is nonnegative on
`Ioo a b` and nonpositive on `Ioo b c`. Then `f` attains its maximum on `Ico a c` at `b`. -/
/-
**isMaxOn_Ico_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Ico_of_deriv {f : Real -> Real} {a b c : Real} (ha : ContinuousAt 
f a) (hb : ContinuousAt f b) (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : Di
fferentiableOn Real f (Ioo b c)) (h₀ : forall x in Ioo a b, 0 <= deriv f x) (h₁ 
: forall x in Ioo b c, deriv f x <= 0) : IsMaxOn f (Ico a c) b
参数：ha : ContinuousAt f a；hb : ContinuousAt f b；hd₀ : DifferentiableOn Real f (Io
o a b)；hd₁ : DifferentiableOn Real f (Ioo b c)；h₀ : forall x in Ioo a b, 0 <= de
riv f x；h₁ : forall x in Ioo b c, deriv f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Ico_of_mono_anti`：isMaxOn_Ico_of_mono_anti (h₀ : MonotoneOn f (I
cc a b)) (h₁ : AntitoneOn f (Ico b c)) : IsMaxOn f (Ico a c) b
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Icc`：∀ 
{f : ℝ → ℝ} {a b : ℝ},   ContinuousAt f a → ContinuousAt f b → DifferentiableOn 
ℝ f (Set.Ioo a b) → ContinuousOn f (Set.Icc a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ico`：convex_Ico (r s : β) : Convex 𝕜 (Ico r s)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ico`：∀ 
{f : ℝ → ℝ} {a b : ℝ}, ContinuousAt f a → DifferentiableOn ℝ f (Set.Ioo a b) → C
ontinuousOn f (Set.Ico a b)
· 使用定理 `interior_Ico`：interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b)
 = Ioo a b

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `a` and `b`, the derivative `f'` is nonnega
tive on
`Ioo a b` and nonpositive on `Ioo b c`. Then `f` attains its maximum on `Ico a c
` at `b`.
-/
lemma isMaxOn_Ico_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) :
    IsMaxOn f (Ico a c) b := by
  refine isMaxOn_Ico_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `a`, `b`, and `c`, the derivative `f'` is nonnegative on
`Ioo a b` and nonpositive on `Ioo b c`. Then `f` attains its maximum on `Icc a c` at `b`. -/
/-
**isMaxOn_Icc_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Icc_of_deriv {f : Real -> Real} {a b c : Real} (ha : ContinuousAt 
f a) (hb : ContinuousAt f b) (hc : ContinuousAt f c) (hd₀ : DifferentiableOn Rea
l f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Ioo b c)) (h₀ : forall x in Ioo a
 b, 0 <= deriv f x) (h₁ : forall x in Ioo b c, deriv f x <= 0) : IsMaxOn f (Icc 
a c) b
参数：ha : ContinuousAt f a；hb : ContinuousAt f b；hc : ContinuousAt f c；hd₀ : Diffe
rentiableOn Real f (Ioo a b)；hd₁ : DifferentiableOn Real f (Ioo b c)；h₀ : forall
 x in Ioo a b, 0 <= deriv f x；h₁ : forall x in Ioo b c, deriv f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Icc_of_mono_anti`：isMaxOn_Icc_of_mono_anti (h₀ : MonotoneOn f (I
cc a b)) (h₁ : AntitoneOn f (Icc b c)) : IsMaxOn f (Icc a c) b
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Icc`：∀ 
{f : ℝ → ℝ} {a b : ℝ},   ContinuousAt f a → ContinuousAt f b → DifferentiableOn 
ℝ f (Set.Ioo a b) → ContinuousOn f (Set.Icc a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `a`, `b`, and `c`, the derivative `f'` is n
onnegative on
`Ioo a b` and nonpositive on `Ioo b c`. Then `f` attains its maximum on `Icc a c
` at `b`.
-/
lemma isMaxOn_Icc_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hc : ContinuousAt f c) (hd₀ : DifferentiableOn ℝ f (Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Ioo b c)) (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x)
    (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) : IsMaxOn f (Icc a c) b := by
  refine isMaxOn_Icc_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonnegative on `Ioo a b` and
nonpositive on `Ioi b`. Then `f` attains its maximum on `Ioi a` at `b`. -/
/-
**isMaxOn_Ioi_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Ioi_of_deriv {f : Real -> Real} {a b : Real} (hb : ContinuousAt f 
b) (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Ioi
 b)) (h₀ : forall x in Ioo a b, 0 <= deriv f x) (h₁ : forall x in Ioi b, deriv f
 x <= 0) : IsMaxOn f (Ioi a) b
参数：hb : ContinuousAt f b；hd₀ : DifferentiableOn Real f (Ioo a b)；hd₁ : Different
iableOn Real f (Ioi b)；h₀ : forall x in Ioo a b, 0 <= deriv f x；h₁ : forall x in
 Ioi b, deriv f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Ioi_of_mono_anti`：isMaxOn_Ioi_of_mono_anti (h₀ : MonotoneOn f (I
oc a b)) (h₁ : AntitoneOn f (Ici b)) : IsMaxOn f (Ioi a) b
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ioc`：convex_Ioc (r s : β) : Convex 𝕜 (Ioc r s)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ioc`：∀ 
{f : ℝ → ℝ} {a b : ℝ}, ContinuousAt f b → DifferentiableOn ℝ f (Set.Ioo a b) → C
ontinuousOn f (Set.Ioc a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Ioc`：interior_Ioc [NoMaxOrder α] {a b : α} : interior (Ioc a b)
 = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ici`：∀ 
{f : ℝ → ℝ} {a : ℝ}, ContinuousAt f a → DifferentiableOn ℝ f (Set.Ioi a) → Conti
nuousOn f (Set.Ici a)
· 使用定理 `interior_Ici'`：interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior 
(Ici a) = Ioi a
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonnegative on 
`Ioo a b` and
nonpositive on `Ioi b`. Then `f` attains its maximum on `Ioi a` at `b`.
-/
lemma isMaxOn_Ioi_of_deriv {f : ℝ → ℝ} {a b : ℝ} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioi b))
    (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioi b, deriv f x ≤ 0) :
    IsMaxOn f (Ioi a) b := by
  refine isMaxOn_Ioi_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `a` and `b`, the derivative `f'` is nonnegative on
`Ioo a b` and nonpositive on `Ioi b`. Then `f` attains its maximum on `Ici a` at `b`. -/
/-
**isMaxOn_Ici_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Ici_of_deriv {f : Real -> Real} {a b : Real} (ha : ContinuousAt f 
a) (hb : ContinuousAt f b) (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : Diff
erentiableOn Real f (Ioi b)) (h₀ : forall x in Ioo a b, 0 <= deriv f x) (h₁ : fo
rall x in Ioi b, deriv f x <= 0) : IsMaxOn f (Ici a) b
参数：ha : ContinuousAt f a；hb : ContinuousAt f b；hd₀ : DifferentiableOn Real f (Io
o a b)；hd₁ : DifferentiableOn Real f (Ioi b)；h₀ : forall x in Ioo a b, 0 <= deri
v f x；h₁ : forall x in Ioi b, deriv f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Ici_of_mono_anti`：isMaxOn_Ici_of_mono_anti (h₀ : MonotoneOn f (I
cc a b)) (h₁ : AntitoneOn f (Ici b)) : IsMaxOn f (Ici a) b
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Icc`：∀ 
{f : ℝ → ℝ} {a b : ℝ},   ContinuousAt f a → ContinuousAt f b → DifferentiableOn 
ℝ f (Set.Ioo a b) → ContinuousOn f (Set.Icc a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ici`：∀ 
{f : ℝ → ℝ} {a : ℝ}, ContinuousAt f a → DifferentiableOn ℝ f (Set.Ioi a) → Conti
nuousOn f (Set.Ici a)
· 使用定理 `interior_Ici'`：interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior 
(Ici a) = Ioi a

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `a` and `b`, the derivative `f'` is nonnega
tive on
`Ioo a b` and nonpositive on `Ioi b`. Then `f` attains its maximum on `Ici a` at
 `b`.
-/
lemma isMaxOn_Ici_of_deriv {f : ℝ → ℝ} {a b : ℝ} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioi b))
    (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioi b, deriv f x ≤ 0) :
    IsMaxOn f (Ici a) b := by
  refine isMaxOn_Ici_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonnegative on `Iio b` and
nonpositive on `Ioo b c`. Then `f` attains its maximum on `Iio c` at `b`. -/
/-
**isMaxOn_Iio_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Iio_of_deriv {f : Real -> Real} {b c : Real} (hb : ContinuousAt f 
b) (hd₀ : DifferentiableOn Real f (Iio b)) (hd₁ : DifferentiableOn Real f (Ioo b
 c)) (h₀ : forall x in Iio b, 0 <= deriv f x) (h₁ : forall x in Ioo b c, deriv f
 x <= 0) : IsMaxOn f (Iio c) b
参数：hb : ContinuousAt f b；hd₀ : DifferentiableOn Real f (Iio b)；hd₁ : Differentia
bleOn Real f (Ioo b c)；h₀ : forall x in Iio b, 0 <= deriv f x；h₁ : forall x in I
oo b c, deriv f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Iio_of_mono_anti`：isMaxOn_Iio_of_mono_anti (h₀ : MonotoneOn f (I
ic b)) (h₁ : AntitoneOn f (Ico b a)) : IsMaxOn f (Iio a) b
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Iic`：convex_Iic (r : β) : Convex 𝕜 (Iic r)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Iic`：∀ 
{f : ℝ → ℝ} {b : ℝ}, ContinuousAt f b → DifferentiableOn ℝ f (Set.Iio b) → Conti
nuousOn f (Set.Iic b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Iic'`：interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior 
(Iic a) = Iio a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ico`：convex_Ico (r s : β) : Convex 𝕜 (Ico r s)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ico`：∀ 
{f : ℝ → ℝ} {a b : ℝ}, ContinuousAt f a → DifferentiableOn ℝ f (Set.Ioo a b) → C
ontinuousOn f (Set.Ico a b)
· 使用定理 `interior_Ico`：interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b)
 = Ioo a b
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonnegative on 
`Iio b` and
nonpositive on `Ioo b c`. Then `f` attains its maximum on `Iio c` at `b`.
-/
lemma isMaxOn_Iio_of_deriv {f : ℝ → ℝ} {b c : ℝ} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Iio b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Iio b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) :
    IsMaxOn f (Iio c) b := by
  refine isMaxOn_Iio_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b` and `c`, the derivative `f'` is nonnegative on
`Iio b` and nonpositive on `Ioo b c`. Then `f` attains its maximum on `Iic c` at `b`. -/
/-
**isMaxOn_Iic_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Iic_of_deriv {f : Real -> Real} {b c : Real} (hb : ContinuousAt f 
b) (hc : ContinuousAt f c) (hd₀ : DifferentiableOn Real f (Iio b)) (hd₁ : Differ
entiableOn Real f (Ioo b c)) (h₀ : forall x in Iio b, 0 <= deriv f x) (h₁ : fora
ll x in Ioo b c, deriv f x <= 0) : IsMaxOn f (Iic c) b
参数：hb : ContinuousAt f b；hc : ContinuousAt f c；hd₀ : DifferentiableOn Real f (Ii
o b)；hd₁ : DifferentiableOn Real f (Ioo b c)；h₀ : forall x in Iio b, 0 <= deriv 
f x；h₁ : forall x in Ioo b c, deriv f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Iic_of_mono_anti`：isMaxOn_Iic_of_mono_anti (h₀ : MonotoneOn f (I
ic b)) (h₁ : AntitoneOn f (Icc b a)) : IsMaxOn f (Iic a) b
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Iic`：convex_Iic (r : β) : Convex 𝕜 (Iic r)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Iic`：∀ 
{f : ℝ → ℝ} {b : ℝ}, ContinuousAt f b → DifferentiableOn ℝ f (Set.Iio b) → Conti
nuousOn f (Set.Iic b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Iic'`：interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior 
(Iic a) = Iio a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Icc`：∀ 
{f : ℝ → ℝ} {a b : ℝ},   ContinuousAt f a → ContinuousAt f b → DifferentiableOn 
ℝ f (Set.Ioo a b) → ContinuousOn f (Set.Icc a b)
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `b` and `c`, the derivative `f'` is nonnega
tive on
`Iio b` and nonpositive on `Ioo b c`. Then `f` attains its maximum on `Iic c` at
 `b`.
-/
lemma isMaxOn_Iic_of_deriv {f : ℝ → ℝ} {b c : ℝ} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
    (hd₀ : DifferentiableOn ℝ f (Iio b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Iio b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) :
    IsMaxOn f (Iic c) b := by
  refine isMaxOn_Iic_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonnegative on `Iio b` and
nonpositive on `Ioi b`. Then `f` attains its maximum on `ℝ` at `b`. -/
/-
**isMaxOn_univ_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_univ_of_deriv {f : Real -> Real} {b : Real} (hb : ContinuousAt f b
) (hd₀ : DifferentiableOn Real f (Iio b)) (hd₁ : DifferentiableOn Real f (Ioi b)
) (h₀ : forall x in Iio b, 0 <= deriv f x) (h₁ : forall x in Ioi b, deriv f x <=
 0) : IsMaxOn f univ b
参数：hb : ContinuousAt f b；hd₀ : DifferentiableOn Real f (Iio b)；hd₁ : Differentia
bleOn Real f (Ioi b)；h₀ : forall x in Iio b, 0 <= deriv f x；h₁ : forall x in Ioi
 b, deriv f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_univ_of_mono_anti`：isMaxOn_univ_of_mono_anti (h₀ : MonotoneOn f 
(Iic b)) (h₁ : AntitoneOn f (Ici b)) : IsMaxOn f univ b
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Iic`：convex_Iic (r : β) : Convex 𝕜 (Iic r)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Iic`：∀ 
{f : ℝ → ℝ} {b : ℝ}, ContinuousAt f b → DifferentiableOn ℝ f (Set.Iio b) → Conti
nuousOn f (Set.Iic b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Iic'`：interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior 
(Iic a) = Iio a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ici`：∀ 
{f : ℝ → ℝ} {a : ℝ}, ContinuousAt f a → DifferentiableOn ℝ f (Set.Ioi a) → Conti
nuousOn f (Set.Ici a)
· 使用定理 `interior_Ici'`：interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior 
(Ici a) = Ioi a
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonnegative on 
`Iio b` and
nonpositive on `Ioi b`. Then `f` attains its maximum on `ℝ` at `b`.
-/
lemma isMaxOn_univ_of_deriv {f : ℝ → ℝ} {b : ℝ} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Iio b)) (hd₁ : DifferentiableOn ℝ f (Ioi b))
    (h₀ : ∀ x ∈ Iio b, 0 ≤ deriv f x) (h₁ : ∀ x ∈ Ioi b, deriv f x ≤ 0) :
    IsMaxOn f univ b := by
  refine isMaxOn_univ_of_mono_anti ?_ ?_
  · apply monotoneOn_of_deriv_nonneg (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply antitoneOn_of_deriv_nonpos (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/-- The First-Derivative Test from calculus, maxima version.
Suppose `a < b < c`, `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonnegative on
`Ioo a b` and nonpositive on `Ioo b c`. Then `f` has a local maximum at `b`. -/
/-
**isLocalMax_of_deriv_Ioo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalMax_of_deriv_Ioo {f : Real -> Real} {a b c : Real} (g₀ : a < b) (g₁
 : b < c) (h : ContinuousAt f b) (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ 
: DifferentiableOn Real f (Ioo b c)) (h₀ : forall x in Ioo a b, 0 <= deriv f x) 
(h₁ : forall x in Ioo b c, deriv f x <= 0) : IsLocalMax f b
参数：g₀ : a < b；g₁ : b < c；h : ContinuousAt f b；hd₀ : DifferentiableOn Real f (Ioo
 a b)；hd₁ : DifferentiableOn Real f (Ioo b c)；h₀ : forall x in Ioo a b, 0 <= der
iv f x；h₁ : forall x in Ioo b c, deriv f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxOn.isLocalMax`：IsMaxOn.isLocalMax (hf : IsMaxOn f s a) (hs : s in 𝓝
 a) : IsLocalMax f a
· 使用引理 `isMaxOn_Ioo_of_deriv`：isMaxOn_Ioo_of_deriv {f : Real -> Real} {a b c : R
eal} (h : ContinuousAt f b) (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : Dif
ferentiabl…
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ

--- 原说明 ---
The First-Derivative Test from calculus, maxima version.
Suppose `a < b < c`, `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is no
nnegative on
`Ioo a b` and nonpositive on `Ioo b c`. Then `f` has a local maximum at `b`.
-/
lemma isLocalMax_of_deriv_Ioo {f : ℝ → ℝ} {a b c : ℝ} (g₀ : a < b) (g₁ : b < c)
    (h : ContinuousAt f b) (hd₀ : DifferentiableOn ℝ f (Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Ioo b c)) (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x)
    (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) : IsLocalMax f b :=
  (isMaxOn_Ioo_of_deriv h hd₀ hd₁ h₀ h₁).isLocalMax (Ioo_mem_nhds g₀ g₁)

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonpositive on `Ioo a b` and
nonnegative on `Ioo b c`. Then `f` attains its minimum on `Ioo a c` at `b`. -/
/-
**isMinOn_Ioo_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Ioo_of_deriv {f : Real -> Real} {a b c : Real} (h : ContinuousAt f
 b) (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Io
o b c)) (h₀ : forall x in Ioo a b, deriv f x <= 0) (h₁ : forall x in Ioo b c, 0 
<= deriv f x) : IsMinOn f (Ioo a c) b
参数：h : ContinuousAt f b；hd₀ : DifferentiableOn Real f (Ioo a b)；hd₁ : Differenti
ableOn Real f (Ioo b c)；h₀ : forall x in Ioo a b, deriv f x <= 0；h₁ : forall x i
n Ioo b c, 0 <= deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMinOn_Ioo_of_anti_mono`：isMinOn_Ioo_of_anti_mono (h₀ : AntitoneOn f (I
oc a b)) (h₁ : MonotoneOn f (Ico b c)) : IsMinOn f (Ioo a c) b
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ioc`：convex_Ioc (r s : β) : Convex 𝕜 (Ioc r s)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ioc`：∀ 
{f : ℝ → ℝ} {a b : ℝ}, ContinuousAt f b → DifferentiableOn ℝ f (Set.Ioo a b) → C
ontinuousOn f (Set.Ioc a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Ioc`：interior_Ioc [NoMaxOrder α] {a b : α} : interior (Ioc a b)
 = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ico`：convex_Ico (r s : β) : Convex 𝕜 (Ico r s)
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ico`：∀ 
{f : ℝ → ℝ} {a b : ℝ}, ContinuousAt f a → DifferentiableOn ℝ f (Set.Ioo a b) → C
ontinuousOn f (Set.Ico a b)
· 使用定理 `interior_Ico`：interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b)
 = Ioo a b
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonpositive on 
`Ioo a b` and
nonnegative on `Ioo b c`. Then `f` attains its minimum on `Ioo a c` at `b`.
-/
lemma isMinOn_Ioo_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) :
    IsMinOn f (Ioo a c) b := by
  refine isMinOn_Ioo_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc h hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico h hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b` and `c`, the derivative `f'` is nonpositive on
`Ioo a b` and nonnegative on `Ioo b c`. Then `f` attains its minimum on `Ioc a c` at `b`. -/
/-
**isMinOn_Ioc_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Ioc_of_deriv {f : Real -> Real} {a b c : Real} (hb : ContinuousAt 
f b) (hc : ContinuousAt f c) (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : Di
fferentiableOn Real f (Ioo b c)) (h₀ : forall x in Ioo a b, deriv f x <= 0) (h₁ 
: forall x in Ioo b c, 0 <= deriv f x) : IsMinOn f (Ioc a c) b
参数：hb : ContinuousAt f b；hc : ContinuousAt f c；hd₀ : DifferentiableOn Real f (Io
o a b)；hd₁ : DifferentiableOn Real f (Ioo b c)；h₀ : forall x in Ioo a b, deriv f
 x <= 0；h₁ : forall x in Ioo b c, 0 <= deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMinOn_Ioc_of_anti_mono`：isMinOn_Ioc_of_anti_mono (h₀ : AntitoneOn f (I
oc a b)) (h₁ : MonotoneOn f (Icc b c)) : IsMinOn f (Ioc a c) b
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ioc`：convex_Ioc (r s : β) : Convex 𝕜 (Ioc r s)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ioc`：∀ 
{f : ℝ → ℝ} {a b : ℝ}, ContinuousAt f b → DifferentiableOn ℝ f (Set.Ioo a b) → C
ontinuousOn f (Set.Ioc a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Ioc`：interior_Ioc [NoMaxOrder α] {a b : α} : interior (Ioc a b)
 = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Icc`：∀ 
{f : ℝ → ℝ} {a b : ℝ},   ContinuousAt f a → ContinuousAt f b → DifferentiableOn 
ℝ f (Set.Ioo a b) → ContinuousOn f (Set.Icc a b)
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `b` and `c`, the derivative `f'` is nonposi
tive on
`Ioo a b` and nonnegative on `Ioo b c`. Then `f` attains its minimum on `Ioc a c
` at `b`.
-/
lemma isMinOn_Ioc_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) :
    IsMinOn f (Ioc a c) b := by
  refine isMinOn_Ioc_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `a` and `b`, the derivative `f'` is nonpositive on
`Ioo a b` and nonnegative on `Ioo b c`. Then `f` attains its minimum on `Ico a c` at `b`. -/
/-
**isMinOn_Ico_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Ico_of_deriv {f : Real -> Real} {a b c : Real} (ha : ContinuousAt 
f a) (hb : ContinuousAt f b) (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : Di
fferentiableOn Real f (Ioo b c)) (h₀ : forall x in Ioo a b, deriv f x <= 0) (h₁ 
: forall x in Ioo b c, 0 <= deriv f x) : IsMinOn f (Ico a c) b
参数：ha : ContinuousAt f a；hb : ContinuousAt f b；hd₀ : DifferentiableOn Real f (Io
o a b)；hd₁ : DifferentiableOn Real f (Ioo b c)；h₀ : forall x in Ioo a b, deriv f
 x <= 0；h₁ : forall x in Ioo b c, 0 <= deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMinOn_Ico_of_anti_mono`：isMinOn_Ico_of_anti_mono (h₀ : AntitoneOn f (I
cc a b)) (h₁ : MonotoneOn f (Ico b c)) : IsMinOn f (Ico a c) b
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Icc`：∀ 
{f : ℝ → ℝ} {a b : ℝ},   ContinuousAt f a → ContinuousAt f b → DifferentiableOn 
ℝ f (Set.Ioo a b) → ContinuousOn f (Set.Icc a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ico`：convex_Ico (r s : β) : Convex 𝕜 (Ico r s)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ico`：∀ 
{f : ℝ → ℝ} {a b : ℝ}, ContinuousAt f a → DifferentiableOn ℝ f (Set.Ioo a b) → C
ontinuousOn f (Set.Ico a b)
· 使用定理 `interior_Ico`：interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b)
 = Ioo a b

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `a` and `b`, the derivative `f'` is nonposi
tive on
`Ioo a b` and nonnegative on `Ioo b c`. Then `f` attains its minimum on `Ico a c
` at `b`.
-/
lemma isMinOn_Ico_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) :
    IsMinOn f (Ico a c) b := by
  refine isMinOn_Ico_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `a`, `b`, and `c`, the derivative `f'` is nonpositive on
`Ioo a b` and nonnegative on `Ioo b c`. Then `f` attains its minimum on `Icc a c` at `b`. -/
/-
**isMinOn_Icc_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Icc_of_deriv {f : Real -> Real} {a b c : Real} (ha : ContinuousAt 
f a) (hb : ContinuousAt f b) (hc : ContinuousAt f c) (hd₀ : DifferentiableOn Rea
l f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Ioo b c)) (h₀ : forall x in Ioo a
 b, deriv f x <= 0) (h₁ : forall x in Ioo b c, 0 <= deriv f x) : IsMinOn f (Icc 
a c) b
参数：ha : ContinuousAt f a；hb : ContinuousAt f b；hc : ContinuousAt f c；hd₀ : Diffe
rentiableOn Real f (Ioo a b)；hd₁ : DifferentiableOn Real f (Ioo b c)；h₀ : forall
 x in Ioo a b, deriv f x <= 0；h₁ : forall x in Ioo b c, 0 <= deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMinOn_Icc_of_anti_mono`：isMinOn_Icc_of_anti_mono (h₀ : AntitoneOn f (I
cc a b)) (h₁ : MonotoneOn f (Icc b c)) : IsMinOn f (Icc a c) b
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Icc`：∀ 
{f : ℝ → ℝ} {a b : ℝ},   ContinuousAt f a → ContinuousAt f b → DifferentiableOn 
ℝ f (Set.Ioo a b) → ContinuousOn f (Set.Icc a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `a`, `b`, and `c`, the derivative `f'` is n
onpositive on
`Ioo a b` and nonnegative on `Ioo b c`. Then `f` attains its minimum on `Icc a c
` at `b`.
-/
lemma isMinOn_Icc_of_deriv {f : ℝ → ℝ} {a b c : ℝ} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hc : ContinuousAt f c) (hd₀ : DifferentiableOn ℝ f (Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Ioo b c)) (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0)
    (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) : IsMinOn f (Icc a c) b := by
  refine isMinOn_Icc_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonpositive on `Ioo a b` and
nonnegative on `Ioi b`. Then `f` attains its minimum on `Ioi a` at `b`. -/
/-
**isMinOn_Ioi_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Ioi_of_deriv {f : Real -> Real} {a b : Real} (hb : ContinuousAt f 
b) (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : DifferentiableOn Real f (Ioi
 b)) (h₀ : forall x in Ioo a b, deriv f x <= 0) (h₁ : forall x in Ioi b, 0 <= de
riv f x) : IsMinOn f (Ioi a) b
参数：hb : ContinuousAt f b；hd₀ : DifferentiableOn Real f (Ioo a b)；hd₁ : Different
iableOn Real f (Ioi b)；h₀ : forall x in Ioo a b, deriv f x <= 0；h₁ : forall x in
 Ioi b, 0 <= deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMinOn_Ioi_of_anti_mono`：isMinOn_Ioi_of_anti_mono (h₀ : AntitoneOn f (I
oc a b)) (h₁ : MonotoneOn f (Ici b)) : IsMinOn f (Ioi a) b
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ioc`：convex_Ioc (r s : β) : Convex 𝕜 (Ioc r s)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ioc`：∀ 
{f : ℝ → ℝ} {a b : ℝ}, ContinuousAt f b → DifferentiableOn ℝ f (Set.Ioo a b) → C
ontinuousOn f (Set.Ioc a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Ioc`：interior_Ioc [NoMaxOrder α] {a b : α} : interior (Ioc a b)
 = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ici`：∀ 
{f : ℝ → ℝ} {a : ℝ}, ContinuousAt f a → DifferentiableOn ℝ f (Set.Ioi a) → Conti
nuousOn f (Set.Ici a)
· 使用定理 `interior_Ici'`：interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior 
(Ici a) = Ioi a
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonpositive on 
`Ioo a b` and
nonnegative on `Ioi b`. Then `f` attains its minimum on `Ioi a` at `b`.
-/
lemma isMinOn_Ioi_of_deriv {f : ℝ → ℝ} {a b : ℝ} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioi b))
    (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioi b, 0 ≤ deriv f x) :
    IsMinOn f (Ioi a) b := by
  refine isMinOn_Ioi_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Ioc a b) (continuousOn_Ioc hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `a` and `b`, the derivative `f'` is nonpositive on
`Ioo a b` and nonnegative on `Ioi b`. Then `f` attains its minimum on `Ici a` at `b`. -/
/-
**isMinOn_Ici_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Ici_of_deriv {f : Real -> Real} {a b : Real} (ha : ContinuousAt f 
a) (hb : ContinuousAt f b) (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : Diff
erentiableOn Real f (Ioi b)) (h₀ : forall x in Ioo a b, deriv f x <= 0) (h₁ : fo
rall x in Ioi b, 0 <= deriv f x) : IsMinOn f (Ici a) b
参数：ha : ContinuousAt f a；hb : ContinuousAt f b；hd₀ : DifferentiableOn Real f (Io
o a b)；hd₁ : DifferentiableOn Real f (Ioi b)；h₀ : forall x in Ioo a b, deriv f x
 <= 0；h₁ : forall x in Ioi b, 0 <= deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMinOn_Ici_of_anti_mono`：isMinOn_Ici_of_anti_mono (h₀ : AntitoneOn f (I
cc a b)) (h₁ : MonotoneOn f (Ici b)) : IsMinOn f (Ici a) b
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Icc`：∀ 
{f : ℝ → ℝ} {a b : ℝ},   ContinuousAt f a → ContinuousAt f b → DifferentiableOn 
ℝ f (Set.Ioo a b) → ContinuousOn f (Set.Icc a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ici`：∀ 
{f : ℝ → ℝ} {a : ℝ}, ContinuousAt f a → DifferentiableOn ℝ f (Set.Ioi a) → Conti
nuousOn f (Set.Ici a)
· 使用定理 `interior_Ici'`：interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior 
(Ici a) = Ioi a

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `a` and `b`, the derivative `f'` is nonposi
tive on
`Ioo a b` and nonnegative on `Ioi b`. Then `f` attains its minimum on `Ici a` at
 `b`.
-/
lemma isMinOn_Ici_of_deriv {f : ℝ → ℝ} {a b : ℝ} (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioi b))
    (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioi b, 0 ≤ deriv f x) :
    IsMinOn f (Ici a) b := by
  refine isMinOn_Ici_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_Icc ha hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonpositive on `Iio b` and
nonnegative on `Ioo b c`. Then `f` attains its minimum on `Iio c` at `b`. -/
/-
**isMinOn_Iio_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Iio_of_deriv {f : Real -> Real} {b c : Real} (hb : ContinuousAt f 
b) (hd₀ : DifferentiableOn Real f (Iio b)) (hd₁ : DifferentiableOn Real f (Ioo b
 c)) (h₀ : forall x in Iio b, deriv f x <= 0) (h₁ : forall x in Ioo b c, 0 <= de
riv f x) : IsMinOn f (Iio c) b
参数：hb : ContinuousAt f b；hd₀ : DifferentiableOn Real f (Iio b)；hd₁ : Differentia
bleOn Real f (Ioo b c)；h₀ : forall x in Iio b, deriv f x <= 0；h₁ : forall x in I
oo b c, 0 <= deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMinOn_Iio_of_anti_mono`：isMinOn_Iio_of_anti_mono (h₀ : AntitoneOn f (I
ic b)) (h₁ : MonotoneOn f (Ico b a)) : IsMinOn f (Iio a) b
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Iic`：convex_Iic (r : β) : Convex 𝕜 (Iic r)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Iic`：∀ 
{f : ℝ → ℝ} {b : ℝ}, ContinuousAt f b → DifferentiableOn ℝ f (Set.Iio b) → Conti
nuousOn f (Set.Iic b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Iic'`：interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior 
(Iic a) = Iio a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ico`：convex_Ico (r s : β) : Convex 𝕜 (Ico r s)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ico`：∀ 
{f : ℝ → ℝ} {a b : ℝ}, ContinuousAt f a → DifferentiableOn ℝ f (Set.Ioo a b) → C
ontinuousOn f (Set.Ico a b)
· 使用定理 `interior_Ico`：interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b)
 = Ioo a b
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonpositive on 
`Iio b` and
nonnegative on `Ioo b c`. Then `f` attains its minimum on `Iio c` at `b`.
-/
lemma isMinOn_Iio_of_deriv {f : ℝ → ℝ} {b c : ℝ} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Iio b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Iio b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) :
    IsMinOn f (Iio c) b := by
  refine isMinOn_Iio_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ico b c) (continuousOn_Ico hb hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b` and `c`, the derivative `f'` is nonpositive on
`Iio b` and nonnegative on `Ioo b c`. Then `f` attains its minimum on `Iic c` at `b`. -/
/-
**isMinOn_Iic_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Iic_of_deriv {f : Real -> Real} {b c : Real} (hb : ContinuousAt f 
b) (hc : ContinuousAt f c) (hd₀ : DifferentiableOn Real f (Iio b)) (hd₁ : Differ
entiableOn Real f (Ioo b c)) (h₀ : forall x in Iio b, deriv f x <= 0) (h₁ : fora
ll x in Ioo b c, 0 <= deriv f x) : IsMinOn f (Iic c) b
参数：hb : ContinuousAt f b；hc : ContinuousAt f c；hd₀ : DifferentiableOn Real f (Ii
o b)；hd₁ : DifferentiableOn Real f (Ioo b c)；h₀ : forall x in Iio b, deriv f x <
= 0；h₁ : forall x in Ioo b c, 0 <= deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMinOn_Iic_of_anti_mono`：isMinOn_Iic_of_anti_mono (h₀ : AntitoneOn f (I
ic b)) (h₁ : MonotoneOn f (Icc b a)) : IsMinOn f (Iic a) b
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Iic`：convex_Iic (r : β) : Convex 𝕜 (Iic r)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Iic`：∀ 
{f : ℝ → ℝ} {b : ℝ}, ContinuousAt f b → DifferentiableOn ℝ f (Set.Iio b) → Conti
nuousOn f (Set.Iic b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Iic'`：interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior 
(Iic a) = Iio a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Icc`：∀ 
{f : ℝ → ℝ} {a b : ℝ},   ContinuousAt f a → ContinuousAt f b → DifferentiableOn 
ℝ f (Set.Ioo a b) → ContinuousOn f (Set.Icc a b)
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `b` and `c`, the derivative `f'` is nonposi
tive on
`Iio b` and nonnegative on `Ioo b c`. Then `f` attains its minimum on `Iic c` at
 `b`.
-/
lemma isMinOn_Iic_of_deriv {f : ℝ → ℝ} {b c : ℝ} (hb : ContinuousAt f b) (hc : ContinuousAt f c)
    (hd₀ : DifferentiableOn ℝ f (Iio b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Iio b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) :
    IsMinOn f (Iic c) b := by
  refine isMinOn_Iic_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Icc b c) (continuousOn_Icc hb hc hd₁) <;> simp_all

/-- Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonpositive on `Iio b` and
nonnegative on `Ioi b`. Then `f` attains its minimum on `ℝ` at `b`. -/
/-
**isMinOn_univ_of_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_univ_of_deriv {f : Real -> Real} {b : Real} (hb : ContinuousAt f b
) (hd₀ : DifferentiableOn Real f (Iio b)) (hd₁ : DifferentiableOn Real f (Ioi b)
) (h₀ : forall x in Iio b, deriv f x <= 0) (h₁ : forall x in Ioi b, 0 <= deriv f
 x) : IsMinOn f univ b
参数：hb : ContinuousAt f b；hd₀ : DifferentiableOn Real f (Iio b)；hd₁ : Differentia
bleOn Real f (Ioi b)；h₀ : forall x in Iio b, deriv f x <= 0；h₁ : forall x in Ioi
 b, 0 <= deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMinOn_univ_of_anti_mono`：isMinOn_univ_of_anti_mono (h₀ : AntitoneOn f 
(Iic b)) (h₁ : MonotoneOn f (Ici b)) : IsMinOn f univ b
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Iic`：convex_Iic (r : β) : Convex 𝕜 (Iic r)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Iic`：∀ 
{f : ℝ → ℝ} {b : ℝ}, ContinuousAt f b → DifferentiableOn ℝ f (Set.Iio b) → Conti
nuousOn f (Set.Iic b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Iic'`：interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior 
(Iic a) = Iio a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `_private.Mathlib.Analysis.Calculus.DerivativeTest.0.continuousOn_Ici`：∀ 
{f : ℝ → ℝ} {a : ℝ}, ContinuousAt f a → DifferentiableOn ℝ f (Set.Ioi a) → Conti
nuousOn f (Set.Ici a)
· 使用定理 `interior_Ici'`：interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior 
(Ici a) = Ioi a
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R

--- 原说明 ---
Suppose `f : ℝ → ℝ` is continuous at `b`, the derivative `f'` is nonpositive on 
`Iio b` and
nonnegative on `Ioi b`. Then `f` attains its minimum on `ℝ` at `b`.
-/
lemma isMinOn_univ_of_deriv {f : ℝ → ℝ} {b : ℝ} (hb : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Iio b)) (hd₁ : DifferentiableOn ℝ f (Ioi b))
    (h₀ : ∀ x ∈ Iio b, deriv f x ≤ 0) (h₁ : ∀ x ∈ Ioi b, 0 ≤ deriv f x) :
    IsMinOn f univ b := by
  refine isMinOn_univ_of_anti_mono ?_ ?_
  · apply antitoneOn_of_deriv_nonpos (convex_Iic b) (continuousOn_Iic hb hd₀) <;> simp_all
  · apply monotoneOn_of_deriv_nonneg (convex_Ici b) (continuousOn_Ici hb hd₁) <;> simp_all

/-- The First-Derivative Test from calculus, minima version. -/
/-
**isLocalMin_of_deriv_Ioo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalMin_of_deriv_Ioo {f : Real -> Real} {a b c : Real} (g₀ : a < b) (g₁
 : b < c) (h : ContinuousAt f b) (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ 
: DifferentiableOn Real f (Ioo b c)) (h₀ : forall x in Ioo a b, deriv f x <= 0) 
(h₁ : forall x in Ioo b c, 0 <= deriv f x) : IsLocalMin f b
参数：g₀ : a < b；g₁ : b < c；h : ContinuousAt f b；hd₀ : DifferentiableOn Real f (Ioo
 a b)；hd₁ : DifferentiableOn Real f (Ioo b c)；h₀ : forall x in Ioo a b, deriv f 
x <= 0；h₁ : forall x in Ioo b c, 0 <= deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinOn.isLocalMin`：IsMinOn.isLocalMin (hf : IsMinOn f s a) (hs : s in 𝓝
 a) : IsLocalMin f a
· 使用引理 `isMinOn_Ioo_of_deriv`：isMinOn_Ioo_of_deriv {f : Real -> Real} {a b c : R
eal} (h : ContinuousAt f b) (hd₀ : DifferentiableOn Real f (Ioo a b)) (hd₁ : Dif
ferentiabl…
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ

--- 原说明 ---
The First-Derivative Test from calculus, minima version.
-/
lemma isLocalMin_of_deriv_Ioo {f : ℝ → ℝ} {a b c : ℝ} (g₀ : a < b) (g₁ : b < c)
    (h : ContinuousAt f b) (hd₀ : DifferentiableOn ℝ f (Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Ioo b c)) (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0)
    (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) : IsLocalMin f b :=
  (isMinOn_Ioo_of_deriv h hd₀ hd₁ h₀ h₁).isLocalMin (Ioo_mem_nhds g₀ g₁)

/-- The First-Derivative Test from calculus, maxima version,
expressed in terms of left and right filters. -/
/-
**isLocalMax_of_deriv'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalMax_of_deriv' {f : Real -> Real} {b : Real} (h : ContinuousAt f b) 
(hd₀ : forallᶠ x in 𝓝[<] b, DifferentiableAt Real f x) (hd₁ : forallᶠ x in 𝓝[>] 
b, DifferentiableAt Real f x) (h₀ : forallᶠ x in 𝓝[<] b, 0 <= deriv f x) (h₁ : f
orallᶠ x in 𝓝[>] b, deriv f x <= 0) : IsLocalMax f b
参数：h : ContinuousAt f b；hd₀ : forallᶠ x in 𝓝[<] b, DifferentiableAt Real f x；hd₁
 : forallᶠ x in 𝓝[>] b, DifferentiableAt Real f x；h₀ : forallᶠ x in 𝓝[<] b, 0 <=
 deriv f x；h₁ : forallᶠ x in 𝓝[>] b, deriv f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `nhdsLT_basis`：nhdsLT_basis [NoMinOrder α] (a : α) : (𝓝[<] a).HasBasis (·
 < a) (Ioo · a)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用引理 `nhdsGT_basis`：nhdsGT_basis [NoMaxOrder α] (a : α) : (𝓝[>] a).HasBasis (a
 < ·) (Ioo a)
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用引理 `isLocalMax_of_deriv_Ioo`：isLocalMax_of_deriv_Ioo {f : Real -> Real} {a b
 c : Real} (g₀ : a < b) (g₁ : b < c) (h : ContinuousAt f b) (hd₀ : Differentiabl
eOn Real f (I…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The First-Derivative Test from calculus, maxima version,
expressed in terms of left and right filters.
-/
lemma isLocalMax_of_deriv' {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd₀ : ∀ᶠ x in 𝓝[<] b, DifferentiableAt ℝ f x) (hd₁ : ∀ᶠ x in 𝓝[>] b, DifferentiableAt ℝ f x)
    (h₀ : ∀ᶠ x in 𝓝[<] b, 0 ≤ deriv f x) (h₁ : ∀ᶠ x in 𝓝[>] b, deriv f x ≤ 0) :
    IsLocalMax f b := by
  obtain ⟨a, ha⟩ := (nhdsLT_basis b).eventually_iff.mp <| hd₀.and h₀
  obtain ⟨c, hc⟩ := (nhdsGT_basis b).eventually_iff.mp <| hd₁.and h₁
  exact isLocalMax_of_deriv_Ioo ha.1 hc.1 h
    (fun _ hx => (ha.2 hx).1.differentiableWithinAt)
    (fun _ hx => (hc.2 hx).1.differentiableWithinAt)
    (fun _ hx => (ha.2 hx).2) (fun x hx => (hc.2 hx).2)

/-- The First-Derivative Test from calculus, minima version,
expressed in terms of left and right filters. -/
/-
**isLocalMin_of_deriv'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalMin_of_deriv' {f : Real -> Real} {b : Real} (h : ContinuousAt f b) 
(hd₀ : forallᶠ x in 𝓝[<] b, DifferentiableAt Real f x) (hd₁ : forallᶠ x in 𝓝[>] 
b, DifferentiableAt Real f x) (h₀ : forallᶠ x in 𝓝[<] b, deriv f x <= 0) (h₁ : f
orallᶠ x in 𝓝[>] b, deriv f x >= 0) : IsLocalMin f b
参数：h : ContinuousAt f b；hd₀ : forallᶠ x in 𝓝[<] b, DifferentiableAt Real f x；hd₁
 : forallᶠ x in 𝓝[>] b, DifferentiableAt Real f x；h₀ : forallᶠ x in 𝓝[<] b, deri
v f x <= 0；h₁ : forallᶠ x in 𝓝[>] b, deriv f x >= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `nhdsLT_basis`：nhdsLT_basis [NoMinOrder α] (a : α) : (𝓝[<] a).HasBasis (·
 < a) (Ioo · a)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用引理 `nhdsGT_basis`：nhdsGT_basis [NoMaxOrder α] (a : α) : (𝓝[>] a).HasBasis (a
 < ·) (Ioo a)
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用引理 `isLocalMin_of_deriv_Ioo`：isLocalMin_of_deriv_Ioo {f : Real -> Real} {a b
 c : Real} (g₀ : a < b) (g₁ : b < c) (h : ContinuousAt f b) (hd₀ : Differentiabl
eOn Real f (I…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The First-Derivative Test from calculus, minima version,
expressed in terms of left and right filters.
-/
lemma isLocalMin_of_deriv' {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd₀ : ∀ᶠ x in 𝓝[<] b, DifferentiableAt ℝ f x) (hd₁ : ∀ᶠ x in 𝓝[>] b, DifferentiableAt ℝ f x)
    (h₀ : ∀ᶠ x in 𝓝[<] b, deriv f x ≤ 0) (h₁ : ∀ᶠ x in 𝓝[>] b, deriv f x ≥ 0) :
    IsLocalMin f b := by
  obtain ⟨a, ha⟩ := (nhdsLT_basis b).eventually_iff.mp <| hd₀.and h₀
  obtain ⟨c, hc⟩ := (nhdsGT_basis b).eventually_iff.mp <| hd₁.and h₁
  exact isLocalMin_of_deriv_Ioo ha.1 hc.1 h
    (fun _ hx => (ha.2 hx).1.differentiableWithinAt)
    (fun _ hx => (hc.2 hx).1.differentiableWithinAt)
    (fun _ hx => (ha.2 hx).2) (fun x hx => (hc.2 hx).2)

/-- The First Derivative test, maximum version. -/
/-
**isLocalMax_of_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalMax_of_deriv {f : Real -> Real} {b : Real} (h : ContinuousAt f b) (
hd : forallᶠ x in 𝓝[!=] b, DifferentiableAt Real f x) (h₀ : forallᶠ x in 𝓝[<] b,
 0 <= deriv f x) (h₁ : forallᶠ x in 𝓝[>] b, deriv f x <= 0) : IsLocalMax f b
参数：h : ContinuousAt f b；hd : forallᶠ x in 𝓝[!=] b, DifferentiableAt Real f x；h₀ 
: forallᶠ x in 𝓝[<] b, 0 <= deriv f x；h₁ : forallᶠ x in 𝓝[>] b, deriv f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isLocalMax_of_deriv'`：isLocalMax_of_deriv' {f : Real -> Real} {b : Real}
 (h : ContinuousAt f b) (hd₀ : forallᶠ x in 𝓝[<] b, DifferentiableAt Real f x) (
hd₁ : fora…
· 使用定理 `nhdsLT_le_nhdsNE`：nhdsLT_le_nhdsNE (a : α) : 𝓝[<] a <= 𝓝[!=] a
· 使用定理 `nhdsGT_le_nhdsNE`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 :
 Preorder α] (a : α), nhdsWithin a (Set.Ioi a) ≤ nhdsWithin a {a}ᶜ

--- 原说明 ---
The First Derivative test, maximum version.
-/
theorem isLocalMax_of_deriv {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℝ f x)
    (h₀ : ∀ᶠ x in 𝓝[<] b, 0 ≤ deriv f x) (h₁ : ∀ᶠ x in 𝓝[>] b, deriv f x ≤ 0) :
    IsLocalMax f b :=
  isLocalMax_of_deriv' h (nhdsLT_le_nhdsNE _ (by tauto)) (nhdsGT_le_nhdsNE _ (by tauto)) h₀ h₁

/-- The First Derivative test, minimum version. -/
/-
**isLocalMin_of_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalMin_of_deriv {f : Real -> Real} {b : Real} (h : ContinuousAt f b) (
hd : forallᶠ x in 𝓝[!=] b, DifferentiableAt Real f x) (h₀ : forallᶠ x in 𝓝[<] b,
 deriv f x <= 0) (h₁ : forallᶠ x in 𝓝[>] b, 0 <= deriv f x) : IsLocalMin f b
参数：h : ContinuousAt f b；hd : forallᶠ x in 𝓝[!=] b, DifferentiableAt Real f x；h₀ 
: forallᶠ x in 𝓝[<] b, deriv f x <= 0；h₁ : forallᶠ x in 𝓝[>] b, 0 <= deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isLocalMin_of_deriv'`：isLocalMin_of_deriv' {f : Real -> Real} {b : Real}
 (h : ContinuousAt f b) (hd₀ : forallᶠ x in 𝓝[<] b, DifferentiableAt Real f x) (
hd₁ : fora…
· 使用定理 `nhdsLT_le_nhdsNE`：nhdsLT_le_nhdsNE (a : α) : 𝓝[<] a <= 𝓝[!=] a
· 使用定理 `nhdsGT_le_nhdsNE`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 :
 Preorder α] (a : α), nhdsWithin a (Set.Ioi a) ≤ nhdsWithin a {a}ᶜ

--- 原说明 ---
The First Derivative test, minimum version.
-/
theorem isLocalMin_of_deriv {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℝ f x)
    (h₀ : ∀ᶠ x in 𝓝[<] b, deriv f x ≤ 0) (h₁ : ∀ᶠ x in 𝓝[>] b, 0 ≤ deriv f x) :
    IsLocalMin f b :=
  isLocalMin_of_deriv' h (nhdsLT_le_nhdsNE _ (by tauto)) (nhdsGT_le_nhdsNE _ (by tauto)) h₀ h₁

open Filter SignType

section SecondDeriv

variable {f : ℝ → ℝ} {x₀ : ℝ}

/-- If the derivative of `f` is positive at a root `x₀` of `f`, then locally the sign of `f x`
matches `x - x₀`. -/
/-
**eventually_nhdsWithin_sign_eq_of_deriv_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventually_nhdsWithin_sign_eq_of_deriv_pos (hf : deriv f x₀ > 0) (hx : f x
₀ = 0) : forallᶠ x in 𝓝 x₀, sign (f x) = sign (x - x₀)
参数：hf : deriv f x₀ > 0；hx : f x₀ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsNE_sup_pure`：nhdsNE_sup_pure (a : α) : 𝓝[!=] a ⊔ pure a = 𝓝 a
· 使用定理 `Filter.eventually_sup`：eventually_sup {p : α -> Prop} {f g : Filter α} :
 (forallᶠ x in f ⊔ g, p x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in g, p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivAt_iff_tendsto_slope`：hasDerivAt_iff_tendsto_slope : HasDerivAt 
f f' x ↔ Tendsto (slope f x) (𝓝[!=] x) (𝓝 f')
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `differentiableAt_of_deriv_ne_zero`：differentiableAt_of_deriv_ne_zero (h 
: deriv f x != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `eventually_gt_nhds`：eventually_gt_nhds (hab : b < a) : forallᶠ x in 𝓝 a,
 b < x
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Ne.eq_def`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用引理 `neg_of_slope_pos`：neg_of_slope_pos {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStri
ctOrderedRing 𝕜] {f : 𝕜 -> 𝕜} {x₀ b : 𝕜} (hb : b < x₀) (hbf : 0 < slope f x₀ b) 
(hf : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, a - b < 0 ↔ a < b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If the derivative of `f` is positive at a root `x₀` of `f`, then locally the sig
n of `f x`
matches `x - x₀`.
-/
lemma eventually_nhdsWithin_sign_eq_of_deriv_pos (hf : deriv f x₀ > 0) (hx : f x₀ = 0) :
    ∀ᶠ x in 𝓝 x₀, sign (f x) = sign (x - x₀) := by
  rw [← nhdsNE_sup_pure x₀, eventually_sup]
  refine ⟨?_, by simpa⟩
  have h_tendsto := hasDerivAt_iff_tendsto_slope.mp
    (differentiableAt_of_deriv_ne_zero <| ne_of_gt hf).hasDerivAt
  filter_upwards [(h_tendsto.eventually <| eventually_gt_nhds hf),
    self_mem_nhdsWithin] with x hx₀ hx₁
  rw [mem_compl_iff, mem_singleton_iff, ← Ne.eq_def] at hx₁
  obtain (hx' | hx') := hx₁.lt_or_gt
  · rw [sign_neg (neg_of_slope_pos hx' hx₀ hx), sign_neg (sub_neg.mpr hx')]
  · rw [sign_pos (pos_of_slope_pos hx' hx₀ hx), sign_pos (sub_pos.mpr hx')]

/-- If the derivative of `f` is negative at a root `x₀` of `f`, then locally the sign of `f x`
matches `x₀ - x`. -/
/-
**eventually_nhdsWithin_sign_eq_of_deriv_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventually_nhdsWithin_sign_eq_of_deriv_neg (hf : deriv f x₀ < 0) (hx : f x
₀ = 0) : forallᶠ x in 𝓝 x₀, sign (f x) = sign (x₀ - x)
参数：hf : deriv f x₀ < 0；hx : f x₀ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Left.sign_neg`：Left.sign_neg [AddLeftStrictMono α] (a : α) : sign (-a) =
 -sign a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用引理 `eventually_nhdsWithin_sign_eq_of_deriv_pos`：eventually_nhdsWithin_sign_e
q_of_deriv_pos (hf : deriv f x₀ > 0) (hx : f x₀ = 0) : forallᶠ x in 𝓝 x₀, sign (
f x) = sign (x - x₀)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv.fun_neg'`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : T
ype v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 → F},
 (de…

--- 原说明 ---
If the derivative of `f` is negative at a root `x₀` of `f`, then locally the sig
n of `f x`
matches `x₀ - x`.
-/
lemma eventually_nhdsWithin_sign_eq_of_deriv_neg (hf : deriv f x₀ < 0) (hx : f x₀ = 0) :
    ∀ᶠ x in 𝓝 x₀, sign (f x) = sign (x₀ - x) := by
  simpa [Left.sign_neg, -neg_sub, ← neg_sub x₀] using
    eventually_nhdsWithin_sign_eq_of_deriv_pos
      (f := (-f ·)) (x₀ := x₀) (by simpa [deriv.neg]) (by simpa)
/-
**deriv_neg_left_of_sign_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_neg_left_of_sign_deriv {f : Real -> Real} {x₀ : Real} (h₀ : forallᶠ 
(x : Real) in 𝓝[!=] x₀, sign (deriv f x) = sign (x - x₀)) : forallᶠ (b : Real) i
n 𝓝[<] x₀, deriv f b < 0
参数：h₀ : forallᶠ (x : Real) in 𝓝[!=] x₀, sign (deriv f x) = sign (x - x₀)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `nhdsLT_le_nhdsNE`：nhdsLT_le_nhdsNE (a : α) : 𝓝[<] a <= 𝓝[!=] a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_eq_neg_one_iff`：sign_eq_neg_one_iff : sign a = -1 ↔ a < 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, a - b < 0 ↔ a < b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma deriv_neg_left_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, sign (deriv f x) = sign (x - x₀)) :
    ∀ᶠ (b : ℝ) in 𝓝[<] x₀, deriv f b < 0 := by
  filter_upwards [nhdsLT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x < x₀)
  rwa [← sub_neg, ← sign_eq_neg_one_iff, ← hx', sign_eq_neg_one_iff] at hx
/-
**deriv_neg_right_of_sign_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_neg_right_of_sign_deriv {f : Real -> Real} {x₀ : Real} (h₀ : forallᶠ
 (x : Real) in 𝓝[!=] x₀, sign (deriv f x) = sign (x₀ - x)) : forallᶠ (b : Real) 
in 𝓝[>] x₀, deriv f b < 0
参数：h₀ : forallᶠ (x : Real) in 𝓝[!=] x₀, sign (deriv f x) = sign (x₀ - x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `nhdsGT_le_nhdsNE`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 :
 Preorder α] (a : α), nhdsWithin a (Set.Ioi a) ≤ nhdsWithin a {a}ᶜ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_eq_neg_one_iff`：sign_eq_neg_one_iff : sign a = -1 ↔ a < 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, a - b < 0 ↔ a < b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma deriv_neg_right_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, sign (deriv f x) = sign (x₀ - x)) :
     ∀ᶠ (b : ℝ) in 𝓝[>] x₀, deriv f b < 0 := by
  filter_upwards [nhdsGT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x₀ < x)
  rwa [← sub_neg, ← sign_eq_neg_one_iff, ← hx', sign_eq_neg_one_iff] at hx
/-
**deriv_pos_right_of_sign_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_pos_right_of_sign_deriv {f : Real -> Real} {x₀ : Real} (h₀ : forallᶠ
 (x : Real) in 𝓝[!=] x₀, sign (deriv f x) = sign (x - x₀)) : forallᶠ (b : Real) 
in 𝓝[>] x₀, deriv f b > 0
参数：h₀ : forallᶠ (x : Real) in 𝓝[!=] x₀, sign (deriv f x) = sign (x - x₀)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `nhdsGT_le_nhdsNE`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 :
 Preorder α] (a : α), nhdsWithin a (Set.Ioi a) ≤ nhdsWithin a {a}ᶜ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_eq_one_iff`：sign_eq_one_iff : sign a = 1 ↔ 0 < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma deriv_pos_right_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, sign (deriv f x) = sign (x - x₀)) :
     ∀ᶠ (b : ℝ) in 𝓝[>] x₀, deriv f b > 0 := by
  filter_upwards [nhdsGT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x₀ < x)
  rwa [← sub_pos, ← sign_eq_one_iff, ← hx', sign_eq_one_iff] at hx
/-
**deriv_pos_left_of_sign_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_pos_left_of_sign_deriv {f : Real -> Real} {x₀ : Real} (h₀ : forallᶠ 
(x : Real) in 𝓝[!=] x₀, sign (deriv f x) = sign (x₀ - x)) : forallᶠ (b : Real) i
n 𝓝[<] x₀, deriv f b > 0
参数：h₀ : forallᶠ (x : Real) in 𝓝[!=] x₀, sign (deriv f x) = sign (x₀ - x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `nhdsLT_le_nhdsNE`：nhdsLT_le_nhdsNE (a : α) : 𝓝[<] a <= 𝓝[!=] a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_eq_one_iff`：sign_eq_one_iff : sign a = 1 ↔ 0 < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma deriv_pos_left_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, sign (deriv f x) = sign (x₀ - x)) :
    ∀ᶠ (b : ℝ) in 𝓝[<] x₀, deriv f b > 0 := by
  filter_upwards [nhdsLT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x < x₀)
  rwa [← sub_pos, ← sign_eq_one_iff, ← hx', sign_eq_one_iff] at hx

/-- The First Derivative test with a hypothesis on the sign of the derivative, maximum version. -/
/-
**isLocalMax_of_sign_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalMax_of_sign_deriv {f : Real -> Real} {x₀ : Real} (h : ContinuousAt 
f x₀) (hf : forallᶠ x in 𝓝[!=] x₀, sign (deriv f x) = sign (x₀ - x)) : IsLocalMa
x f x₀
参数：h : ContinuousAt f x₀；hf : forallᶠ x in 𝓝[!=] x₀, sign (deriv f x) = sign (x₀
 - x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `deriv_pos_left_of_sign_deriv`：deriv_pos_left_of_sign_deriv {f : Real -> 
Real} {x₀ : Real} (h₀ : forallᶠ (x : Real) in 𝓝[!=] x₀, sign (deriv f x) = sign 
(x₀ - x)) : forall…
· 使用引理 `deriv_neg_right_of_sign_deriv`：deriv_neg_right_of_sign_deriv {f : Real -
> Real} {x₀ : Real} (h₀ : forallᶠ (x : Real) in 𝓝[!=] x₀, sign (deriv f x) = sig
n (x₀ - x)) : foral…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_sup`：eventually_sup {p : α -> Prop} {f g : Filter α} :
 (forallᶠ x in f ⊔ g, p x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in g, p x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `nhdsLT_sup_nhdsGT`：nhdsLT_sup_nhdsGT (a : α) : 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[!=] a
· 使用定理 `isLocalMax_of_deriv`：isLocalMax_of_deriv {f : Real -> Real} {b : Real} (
h : ContinuousAt f b) (hd : forallᶠ x in 𝓝[!=] b, DifferentiableAt Real f x) (h₀
 : forall…
· 使用定理 `differentiableAt_of_deriv_ne_zero`：differentiableAt_of_deriv_ne_zero (h 
: deriv f x != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
The First Derivative test with a hypothesis on the sign of the derivative, maxim
um version.
-/
theorem isLocalMax_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ} (h : ContinuousAt f x₀)
    (hf : ∀ᶠ x in 𝓝[≠] x₀, sign (deriv f x) = sign (x₀ - x)) :
    IsLocalMax f x₀ := by
  have hl := deriv_pos_left_of_sign_deriv hf
  have hg := deriv_neg_right_of_sign_deriv hf
  replace hf := (nhdsLT_sup_nhdsGT x₀) ▸
    eventually_sup.mpr ⟨hl.mono fun x hx => hx.ne', hg.mono fun x hx => hx.ne⟩
  exact isLocalMax_of_deriv h (hf.mono fun x hx ↦ differentiableAt_of_deriv_ne_zero hx)
    (hl.mono fun _ => le_of_lt) (hg.mono fun _ => le_of_lt)

/-- The First Derivative test with a hypothesis on the sign of the derivative, minimum version. -/
/-
**isLocalMin_of_sign_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalMin_of_sign_deriv {f : Real -> Real} {x₀ : Real} (h : ContinuousAt 
f x₀) (hf : forallᶠ x in 𝓝[!=] x₀, sign (deriv f x) = sign (x - x₀)) : IsLocalMi
n f x₀
参数：h : ContinuousAt f x₀；hf : forallᶠ x in 𝓝[!=] x₀, sign (deriv f x) = sign (x 
- x₀)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMax.neg`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : AddCommGroup β] [inst_2 : PartialOrder β]   [IsOrderedAddMonoid β] {f 
: α …
· 使用定理 `isLocalMax_of_sign_deriv`：isLocalMax_of_sign_deriv {f : Real -> Real} {x
₀ : Real} (h : ContinuousAt f x₀) (hf : forallᶠ x in 𝓝[!=] x₀, sign (deriv f x) 
= sign (x₀ - x…
· 使用定理 `ContinuousAt.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X 
→ G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv.fun_neg'`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : T
ype v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 → F},
 (de…
· 使用定理 `Left.sign_neg`：Left.sign_neg [AddLeftStrictMono α] (a : α) : sign (-a) =
 -sign a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
The First Derivative test with a hypothesis on the sign of the derivative, minim
um version.
-/
theorem isLocalMin_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ} (h : ContinuousAt f x₀)
    (hf : ∀ᶠ x in 𝓝[≠] x₀, sign (deriv f x) = sign (x - x₀)) :
    IsLocalMin f x₀ := by
  refine neg_neg f ▸ (isLocalMax_of_sign_deriv (f := (-f ·)) h.neg ?foo |>.neg)
  simpa [Left.sign_neg, -neg_sub, ← neg_sub _ x₀, deriv.neg]

/-- The Second-Derivative Test from calculus, minimum version.
Applies to functions like `x^2 + 1[x ≥ 0]` as well as twice differentiable
functions. -/
/-
**isLocalMin_of_deriv_deriv_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalMin_of_deriv_deriv_pos (hf : deriv (deriv f) x₀ > 0) (hd : deriv f 
x₀ = 0) (hc : ContinuousAt f x₀) : IsLocalMin f x₀
参数：hf : deriv (deriv f) x₀ > 0；hd : deriv f x₀ = 0；hc : ContinuousAt f x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLocalMin_of_sign_deriv`：isLocalMin_of_sign_deriv {f : Real -> Real} {x
₀ : Real} (h : ContinuousAt f x₀) (hf : forallᶠ x in 𝓝[!=] x₀, sign (deriv f x) 
= sign (x - x₀…
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用引理 `eventually_nhdsWithin_sign_eq_of_deriv_pos`：eventually_nhdsWithin_sign_e
q_of_deriv_pos (hf : deriv f x₀ > 0) (hx : f x₀ = 0) : forallᶠ x in 𝓝 x₀, sign (
f x) = sign (x - x₀)

--- 原说明 ---
The Second-Derivative Test from calculus, minimum version.
Applies to functions like `x^2 + 1[x ≥ 0]` as well as twice differentiable
functions.
-/
theorem isLocalMin_of_deriv_deriv_pos (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMin f x₀ :=
  isLocalMin_of_sign_deriv hc <| nhdsWithin_le_nhds <|
    eventually_nhdsWithin_sign_eq_of_deriv_pos hf hd

/-- The Second-Derivative Test from calculus, maximum version. -/
/-
**isLocalMax_of_deriv_deriv_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalMax_of_deriv_deriv_neg (hf : deriv (deriv f) x₀ < 0) (hd : deriv f 
x₀ = 0) (hc : ContinuousAt f x₀) : IsLocalMax f x₀
参数：hf : deriv (deriv f) x₀ < 0；hd : deriv f x₀ = 0；hc : ContinuousAt f x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `IsLocalMin.neg`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : AddCommGroup β] [inst_2 : PartialOrder β]   [IsOrderedAddMonoid β] {f 
: α …
· 使用定理 `isLocalMin_of_deriv_deriv_pos`：isLocalMin_of_deriv_deriv_pos (hf : deriv
 (deriv f) x₀ > 0) (hd : deriv f x₀ = 0) (hc : ContinuousAt f x₀) : IsLocalMin f
 x₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `deriv.neg'`：deriv.neg' : (deriv (-f)) = fun x => -deriv f x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv.fun_neg'`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : T
ype v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 → F},
 (de…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ContinuousAt.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X 
→ G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ

--- 原说明 ---
The Second-Derivative Test from calculus, maximum version.
-/
theorem isLocalMax_of_deriv_deriv_neg (hf : deriv (deriv f) x₀ < 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMax f x₀ := by
  simpa using isLocalMin_of_deriv_deriv_pos (by simpa) (by simpa) hc.neg |>.neg

end SecondDeriv

