/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Affine combinations of points

This file defines affine combinations of points.

## Main definitions

* `weightedVSubOfPoint` is a general weighted combination of
  subtractions with an explicit base point, yielding a vector.

* `weightedVSub` uses an arbitrary choice of base point and is intended
  to be used when the sum of weights is 0, in which case the result is
  independent of the choice of base point.

* `affineCombination` adds the weighted combination to the arbitrary
  base point, yielding a point rather than a vector, and is intended
  to be used when the sum of weights is 1, in which case the result is
  independent of the choice of base point.

These definitions are for sums over a `Finset`; versions for a
`Fintype` may be obtained using `Finset.univ`, while versions for a
`Finsupp` may be obtained using `Finsupp.support`.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/

@[expose] public section


noncomputable section

open Affine

namespace Finset

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
variable [S : AffineSpace V P]
variable {ι : Type*} (s : Finset ι)
variable {ι₂ : Type*} (s₂ : Finset ι₂)

/-- A weighted sum of the results of subtracting a base point from the
given points, as a linear map on the weights.  The main cases of
interest are where the sum of the weights is 0, in which case the sum
is independent of the choice of base point, and where the sum of the
weights is 1, in which case the sum added to the base point is
independent of the choice of base point. -/
/-
**Finset.weightedVSubOfPoint** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：weightedVSubOfPoint (p : ι -> P) (b : P) : (ι -> k) ->ₗ[k] V
参数：p : ι -> P；b : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weighted sum of the results of subtracting a base point from the
given points, as a linear map on the weights.  The main cases of
interest are where the sum of the weights is 0, in which case the sum
is independent of the choice of base point, and where the sum of the
weights is 1, in which case the sum added to the base point is
independent of the choice of base point.
-/
def weightedVSubOfPoint (p : ι → P) (b : P) : (ι → k) →ₗ[k] V :=
  ∑ i ∈ s, (LinearMap.proj i : (ι → k) →ₗ[k] k).smulRight (p i -ᵥ b)

@[simp]
/-
**Finset.weightedVSubOfPoint_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSubOfPoint_apply (w : ι -> k) (p : ι -> P) (b : P) : s.weightedVS
ubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
参数：w : ι -> k；p : ι -> P；b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.sum_apply`：sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) 
(b : M) : (∑ d in t, f d) b = ∑ d in t, f d b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem weightedVSubOfPoint_apply (w : ι → k) (p : ι → P) (b : P) :
    s.weightedVSubOfPoint p b w = ∑ i ∈ s, w i • (p i -ᵥ b) := by
  simp [weightedVSubOfPoint, LinearMap.sum_apply]

/-- The value of `weightedVSubOfPoint`, where the given points are equal. -/
@[simp (high)]
/-
**Finset.weightedVSubOfPoint_apply_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSubOfPoint_apply_const (w : ι -> k) (p : P) (b : P) : s.weightedV
SubOfPoint (fun _ => p) b w = (∑ i in s, w i) • (p -ᵥ b)
参数：w : ι -> k；p : P；b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x

--- 原说明 ---
The value of `weightedVSubOfPoint`, where the given points are equal.
-/
theorem weightedVSubOfPoint_apply_const (w : ι → k) (p : P) (b : P) :
    s.weightedVSubOfPoint (fun _ => p) b w = (∑ i ∈ s, w i) • (p -ᵥ b) := by
  rw [weightedVSubOfPoint_apply, sum_smul]
/-
**Finset.weightedVSubOfPoint_vadd** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：weightedVSubOfPoint_vadd (s : Finset ι) (w : ι -> k) (p : ι -> P) (b : P) 
(v : V) : s.weightedVSubOfPoint (v +ᵥ p) b w = s.weightedVSubOfPoint p (-v +ᵥ b)
 w
参数：s : Finset ι；w : ι -> k；p : ι -> P；b : P；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weightedVSubOfPoint_vadd (s : Finset ι) (w : ι → k) (p : ι → P) (b : P) (v : V) :
    s.weightedVSubOfPoint (v +ᵥ p) b w = s.weightedVSubOfPoint p (-v +ᵥ b) w := by
  simp [vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, add_comm]
/-
**Finset.weightedVSubOfPoint_smul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：weightedVSubOfPoint_smul {G : Type*} [Group G] [DistribMulAction G V] [SMu
lCommClass G k V] (s : Finset ι) (w : ι -> k) (p : ι -> V) (b : V) (a : G) : s.w
eightedVSubOfPoint (a • p) b w = a • s.weightedVSubOfPoint p (a⁻¹ • b) w
参数：s : Finset ι；w : ι -> k；p : ι -> V；b : V；a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weightedVSubOfPoint_smul {G : Type*} [Group G] [DistribMulAction G V] [SMulCommClass G k V]
    (s : Finset ι) (w : ι → k) (p : ι → V) (b : V) (a : G) :
    s.weightedVSubOfPoint (a • p) b w = a • s.weightedVSubOfPoint p (a⁻¹ • b) w := by
  simp [smul_sum, smul_sub, smul_comm a (w _)]

/-- `weightedVSubOfPoint` gives equal results for two families of weights and two families of
points that are equal on `s`. -/
/-
**Finset.weightedVSubOfPoint_congr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSubOfPoint_congr {w₁ w₂ : ι -> k} (hw : forall i in s, w₁ i = w₂ 
i) {p₁ p₂ : ι -> P} (hp : forall i in s, p₁ i = p₂ i) (b : P) : s.weightedVSubOf
Point p₁ b w₁ = s.weightedVSubOfPoint p₂ b w₂
参数：hw : forall i in s, w₁ i = w₂ i；hp : forall i in s, p₁ i = p₂ i；b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…

--- 原说明 ---
`weightedVSubOfPoint` gives equal results for two families of weights and two fa
milies of
points that are equal on `s`.
-/
theorem weightedVSubOfPoint_congr {w₁ w₂ : ι → k} (hw : ∀ i ∈ s, w₁ i = w₂ i) {p₁ p₂ : ι → P}
    (hp : ∀ i ∈ s, p₁ i = p₂ i) (b : P) :
    s.weightedVSubOfPoint p₁ b w₁ = s.weightedVSubOfPoint p₂ b w₂ := by
  simp_rw [weightedVSubOfPoint_apply]
  refine sum_congr rfl fun i hi => ?_
  rw [hw i hi, hp i hi]

/-- Given a family of points, if we use a member of the family as a base point, the
`weightedVSubOfPoint` does not depend on the value of the weights at this point. -/
/-
**Finset.weightedVSubOfPoint_eq_of_weights_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：weightedVSubOfPoint_eq_of_weights_eq (p : ι -> P) (j : ι) (w₁ w₂ : ι -> k)
 (hw : forall i, i != j -> w₁ i = w₂ i) : s.weightedVSubOfPoint p (p j) w₁ = s.w
eightedVSubOfPoint p (p j) w₂
参数：p : ι -> P；j : ι；w₁ w₂ : ι -> k；hw : forall i, i != j -> w₁ i = w₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given a family of points, if we use a member of the family as a base point, the
`weightedVSubOfPoint` does not depend on the value of the weights at this point.
-/
theorem weightedVSubOfPoint_eq_of_weights_eq (p : ι → P) (j : ι) (w₁ w₂ : ι → k)
    (hw : ∀ i, i ≠ j → w₁ i = w₂ i) :
    s.weightedVSubOfPoint p (p j) w₁ = s.weightedVSubOfPoint p (p j) w₂ := by
  simp only [Finset.weightedVSubOfPoint_apply]
  congr
  ext i
  rcases eq_or_ne i j with h | h
  · simp [h]
  · simp [hw i h]

/-- The weighted sum is independent of the base point when the sum of
the weights is 0. -/
/-
**Finset.weightedVSubOfPoint_eq_of_sum_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：weightedVSubOfPoint_eq_of_sum_eq_zero (w : ι -> k) (p : ι -> P) (h : ∑ i i
n s, w i = 0) (b₁ b₂ : P) : s.weightedVSubOfPoint p b₁ w = s.weightedVSubOfPoint
 p b₂ w
参数：w : ι -> k；p : ι -> P；h : ∑ i in s, w i = 0；b₁ b₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0

--- 原说明 ---
The weighted sum is independent of the base point when the sum of
the weights is 0.
-/
theorem weightedVSubOfPoint_eq_of_sum_eq_zero (w : ι → k) (p : ι → P) (h : ∑ i ∈ s, w i = 0)
    (b₁ b₂ : P) : s.weightedVSubOfPoint p b₁ w = s.weightedVSubOfPoint p b₂ w := by
  apply eq_of_sub_eq_zero
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply, ← sum_sub_distrib]
  conv_lhs =>
    congr
    · skip
    · ext
      rw [← smul_sub, vsub_sub_vsub_cancel_left]
  rw [← sum_smul, h, zero_smul]

/-- The weighted sum, added to the base point, is independent of the
base point when the sum of the weights is 1. -/
/-
**Finset.weightedVSubOfPoint_vadd_eq_of_sum_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Fi
nset`。
形式化陈述：weightedVSubOfPoint_vadd_eq_of_sum_eq_one (w : ι -> k) (p : ι -> P) (h : ∑
 i in s, w i = 1) (b₁ b₂ : P) : s.weightedVSubOfPoint p b₁ w +ᵥ b₁ = s.weightedV
SubOfPoint p b₂ w +ᵥ b₂
参数：w : ι -> k；p : ι -> P；h : ∑ i in s, w i = 1；b₁ b₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0

--- 原说明 ---
The weighted sum, added to the base point, is independent of the
base point when the sum of the weights is 1.
-/
theorem weightedVSubOfPoint_vadd_eq_of_sum_eq_one (w : ι → k) (p : ι → P) (h : ∑ i ∈ s, w i = 1)
    (b₁ b₂ : P) : s.weightedVSubOfPoint p b₁ w +ᵥ b₁ = s.weightedVSubOfPoint p b₂ w +ᵥ b₂ := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply, ← @vsub_eq_zero_iff_eq V,
    vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, ← add_sub_assoc, add_comm, add_sub_assoc, ←
    sum_sub_distrib]
  conv_lhs =>
    congr
    · skip
    · congr
      · skip
      · ext
        rw [← smul_sub, vsub_sub_vsub_cancel_left]
  rw [← sum_smul, h, one_smul, vsub_add_vsub_cancel, vsub_self]

/-- The weighted sum is unaffected by removing the base point, if
present, from the set of points. -/
@[simp (high)]
/-
**Finset.weightedVSubOfPoint_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSubOfPoint_erase [DecidableEq ι] (w : ι -> k) (p : ι -> P) (i : ι
) : (s.erase i).weightedVSubOfPoint p (p i) w = s.weightedVSubOfPoint p (p i) w
参数：w : ι -> k；p : ι -> P；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid 
M] [inst_1 : DecidableEq ι] (s : Finset ι) {f : ι → M} {a : ι},   f a = 0 → ∑ x 
∈ s.er…
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0

--- 原说明 ---
The weighted sum is unaffected by removing the base point, if
present, from the set of points.
-/
theorem weightedVSubOfPoint_erase [DecidableEq ι] (w : ι → k) (p : ι → P) (i : ι) :
    (s.erase i).weightedVSubOfPoint p (p i) w = s.weightedVSubOfPoint p (p i) w := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply]
  apply sum_erase
  rw [vsub_self, smul_zero]

/-- The weighted sum is unaffected by adding the base point, whether
or not present, to the set of points. -/
@[simp (high)]
/-
**Finset.weightedVSubOfPoint_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSubOfPoint_insert [DecidableEq ι] (w : ι -> k) (p : ι -> P) (i : 
ι) : (insert i s).weightedVSubOfPoint p (p i) w = s.weightedVSubOfPoint p (p i) 
w
参数：w : ι -> k；p : ι -> P；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_insert_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {
a : ι} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   f a = 0 
→ ∑ x ∈ inse…
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0

--- 原说明 ---
The weighted sum is unaffected by adding the base point, whether
or not present, to the set of points.
-/
theorem weightedVSubOfPoint_insert [DecidableEq ι] (w : ι → k) (p : ι → P) (i : ι) :
    (insert i s).weightedVSubOfPoint p (p i) w = s.weightedVSubOfPoint p (p i) w := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply]
  apply sum_insert_zero
  rw [vsub_self, smul_zero]

/-- The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
/-
**Finset.weightedVSubOfPoint_indicator_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：weightedVSubOfPoint_indicator_subset (w : ι -> k) (p : ι -> P) (b : P) {s₁
 s₂ : Finset ι} (h : s₁ subseteq s₂) : s₁.weightedVSubOfPoint p b w = s₂.weighte
dVSubOfPoint p b (Set.indicator (↑s₁) w)
参数：w : ι -> k；p : ι -> P；b : P；h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_indicator_subset_of_eq_zero`：∀ {ι : Type u_1} {α : Type u_3} 
{β : Type u_4} [inst : AddCommMonoid β] [inst_1 : Zero α] (f : ι → α) (g : ι → α
 → β)   {s t : Finset ι}, s …
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0

--- 原说明 ---
The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set.
-/
theorem weightedVSubOfPoint_indicator_subset (w : ι → k) (p : ι → P) (b : P) {s₁ s₂ : Finset ι}
    (h : s₁ ⊆ s₂) :
    s₁.weightedVSubOfPoint p b w = s₂.weightedVSubOfPoint p b (Set.indicator (↑s₁) w) := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply]
  exact Eq.symm <|
    sum_indicator_subset_of_eq_zero w (fun i wi => wi • (p i -ᵥ b : V)) h fun i => zero_smul k _

/-- A weighted sum, over the image of an embedding, equals a weighted
sum with the same points and weights over the original
`Finset`. -/
/-
**Finset.weightedVSubOfPoint_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSubOfPoint_map (e : ι₂ ↪ ι) (w : ι -> k) (p : ι -> P) (b : P) : (
s₂.map e).weightedVSubOfPoint p b w = s₂.weightedVSubOfPoint (p ∘ e) b (w ∘ e)
参数：e : ι₂ ↪ ι；w : ι -> k；p : ι -> P；b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …

--- 原说明 ---
A weighted sum, over the image of an embedding, equals a weighted
sum with the same points and weights over the original
`Finset`.
-/
theorem weightedVSubOfPoint_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) (b : P) :
    (s₂.map e).weightedVSubOfPoint p b w = s₂.weightedVSubOfPoint (p ∘ e) b (w ∘ e) := by
  simp_rw [weightedVSubOfPoint_apply]
  exact Finset.sum_map _ _ _

/-- A weighted sum of pairwise subtractions, expressed as a subtraction of two
`weightedVSubOfPoint` expressions. -/
/-
**Finset.sum_smul_vsub_eq_weightedVSubOfPoint_sub** 是 Mathlib 中的一个定理，位于命名空间 `Fin
set`。
形式化陈述：sum_smul_vsub_eq_weightedVSubOfPoint_sub (w : ι -> k) (p₁ p₂ : ι -> P) (b 
: P) : (∑ i in s, w i • (p₁ i -ᵥ p₂ i)) = s.weightedVSubOfPoint p₁ b w - s.weigh
tedVSubOfPoint p₂ b w
参数：w : ι -> k；p₁ p₂ : ι -> P；b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A weighted sum of pairwise subtractions, expressed as a subtraction of two
`weightedVSubOfPoint` expressions.
-/
theorem sum_smul_vsub_eq_weightedVSubOfPoint_sub (w : ι → k) (p₁ p₂ : ι → P) (b : P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂ i)) =
      s.weightedVSubOfPoint p₁ b w - s.weightedVSubOfPoint p₂ b w := by
  simp_rw [weightedVSubOfPoint_apply, ← sum_sub_distrib, ← smul_sub, vsub_sub_vsub_cancel_right]

/-- A weighted sum of pairwise subtractions, where the point on the right is constant,
expressed as a subtraction involving a `weightedVSubOfPoint` expression. -/
/-
**Finset.sum_smul_vsub_const_eq_weightedVSubOfPoint_sub** 是 Mathlib 中的一个定理，位于命名空
间 `Finset`。
形式化陈述：sum_smul_vsub_const_eq_weightedVSubOfPoint_sub (w : ι -> k) (p₁ : ι -> P) 
(p₂ b : P) : (∑ i in s, w i • (p₁ i -ᵥ p₂)) = s.weightedVSubOfPoint p₁ b w - (∑ 
i in s, w i) • (p₂ -ᵥ b)
参数：w : ι -> k；p₁ : ι -> P；p₂ b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_smul_vsub_eq_weightedVSubOfPoint_sub`：sum_smul_vsub_eq_weight
edVSubOfPoint_sub (w : ι -> k) (p₁ p₂ : ι -> P) (b : P) : (∑ i in s, w i • (p₁ i
 -ᵥ p₂ i)) = s.weightedVSubOfPoint p₁…
· 使用定理 `Finset.weightedVSubOfPoint_apply_const`：weightedVSubOfPoint_apply_const 
(w : ι -> k) (p : P) (b : P) : s.weightedVSubOfPoint (fun _ => p) b w = (∑ i in 
s, w i) • (p -ᵥ b)

--- 原说明 ---
A weighted sum of pairwise subtractions, where the point on the right is constan
t,
expressed as a subtraction involving a `weightedVSubOfPoint` expression.
-/
theorem sum_smul_vsub_const_eq_weightedVSubOfPoint_sub (w : ι → k) (p₁ : ι → P) (p₂ b : P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂)) = s.weightedVSubOfPoint p₁ b w - (∑ i ∈ s, w i) • (p₂ -ᵥ b) := by
  rw [sum_smul_vsub_eq_weightedVSubOfPoint_sub, weightedVSubOfPoint_apply_const]

/-- A weighted sum of pairwise subtractions, where the point on the left is constant,
expressed as a subtraction involving a `weightedVSubOfPoint` expression. -/
/-
**Finset.sum_smul_const_vsub_eq_sub_weightedVSubOfPoint** 是 Mathlib 中的一个定理，位于命名空
间 `Finset`。
形式化陈述：sum_smul_const_vsub_eq_sub_weightedVSubOfPoint (w : ι -> k) (p₂ : ι -> P) 
(p₁ b : P) : (∑ i in s, w i • (p₁ -ᵥ p₂ i)) = (∑ i in s, w i) • (p₁ -ᵥ b) - s.we
ightedVSubOfPoint p₂ b w
参数：w : ι -> k；p₂ : ι -> P；p₁ b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_smul_vsub_eq_weightedVSubOfPoint_sub`：sum_smul_vsub_eq_weight
edVSubOfPoint_sub (w : ι -> k) (p₁ p₂ : ι -> P) (b : P) : (∑ i in s, w i • (p₁ i
 -ᵥ p₂ i)) = s.weightedVSubOfPoint p₁…
· 使用定理 `Finset.weightedVSubOfPoint_apply_const`：weightedVSubOfPoint_apply_const 
(w : ι -> k) (p : P) (b : P) : s.weightedVSubOfPoint (fun _ => p) b w = (∑ i in 
s, w i) • (p -ᵥ b)

--- 原说明 ---
A weighted sum of pairwise subtractions, where the point on the left is constant
,
expressed as a subtraction involving a `weightedVSubOfPoint` expression.
-/
theorem sum_smul_const_vsub_eq_sub_weightedVSubOfPoint (w : ι → k) (p₂ : ι → P) (p₁ b : P) :
    (∑ i ∈ s, w i • (p₁ -ᵥ p₂ i)) = (∑ i ∈ s, w i) • (p₁ -ᵥ b) - s.weightedVSubOfPoint p₂ b w := by
  rw [sum_smul_vsub_eq_weightedVSubOfPoint_sub, weightedVSubOfPoint_apply_const]

/-- A weighted sum may be split into such sums over two subsets. -/
/-
**Finset.weightedVSubOfPoint_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSubOfPoint_sdiff [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subseteq
 s) (w : ι -> k) (p : ι -> P) (b : P) : (s \ s₂).weightedVSubOfPoint p b w + s₂.
weightedVSubOfPoint p b w = s.weightedVSubOfPoint p b w
参数：h : s₂ subseteq s；w : ι -> k；p : ι -> P；b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_sdiff`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   s₁ ⊆ s₂ → ∑ x ∈ s₂
 \ s₁,…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A weighted sum may be split into such sums over two subsets.
-/
theorem weightedVSubOfPoint_sdiff [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) (b : P) :
    (s \ s₂).weightedVSubOfPoint p b w + s₂.weightedVSubOfPoint p b w =
      s.weightedVSubOfPoint p b w := by
  simp_rw [weightedVSubOfPoint_apply, sum_sdiff h]

/-- A weighted sum may be split into a subtraction of such sums over two subsets. -/
/-
**Finset.weightedVSubOfPoint_sdiff_sub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSubOfPoint_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subs
eteq s) (w : ι -> k) (p : ι -> P) (b : P) : (s \ s₂).weightedVSubOfPoint p b w -
 s₂.weightedVSubOfPoint p b (-w) = s.weightedVSubOfPoint p b w
参数：h : s₂ subseteq s；w : ι -> k；p : ι -> P；b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Finset.weightedVSubOfPoint_sdiff`：weightedVSubOfPoint_sdiff [DecidableEq
 ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k) (p : ι -> P) (b : P) : (s \
 s₂).weightedVSubOfPoi…

--- 原说明 ---
A weighted sum may be split into a subtraction of such sums over two subsets.
-/
theorem weightedVSubOfPoint_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) (b : P) :
    (s \ s₂).weightedVSubOfPoint p b w - s₂.weightedVSubOfPoint p b (-w) =
      s.weightedVSubOfPoint p b w := by
  rw [map_neg, sub_neg_eq_add, s.weightedVSubOfPoint_sdiff h]

/-- A weighted sum over `s.subtype pred` equals one over `{x ∈ s | pred x}`. -/
/-
**Finset.weightedVSubOfPoint_subtype_eq_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：weightedVSubOfPoint_subtype_eq_filter (w : ι -> k) (p : ι -> P) (b : P) (p
red : ι -> Prop) [DecidablePred pred] : ((s.subtype pred).weightedVSubOfPoint (f
un i => p i) b fun i => w i) = {x in s | pred x}.weightedVSubOfPoint p b w
参数：w : ι -> k；p : ι -> P；b : P；pred : ι -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subtype_eq_sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : F
inset ι} [inst : AddCommMonoid M] (f : ι → M) {p : ι → Prop}   [inst_1 : Decidab
lePred p], ∑ x ∈ Finse…

--- 原说明 ---
A weighted sum over `s.subtype pred` equals one over `{x ∈ s | pred x}`.
-/
theorem weightedVSubOfPoint_subtype_eq_filter (w : ι → k) (p : ι → P) (b : P) (pred : ι → Prop)
    [DecidablePred pred] :
    ((s.subtype pred).weightedVSubOfPoint (fun i => p i) b fun i => w i) =
      {x ∈ s | pred x}.weightedVSubOfPoint p b w := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply, ← sum_subtype_eq_sum_filter]

/-- A weighted sum over `{x ∈ s | pred x}` equals one over `s` if all the weights at indices in `s`
not satisfying `pred` are zero. -/
/-
**Finset.weightedVSubOfPoint_filter_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSubOfPoint_filter_of_ne (w : ι -> k) (p : ι -> P) (b : P) {pred :
 ι -> Prop} [DecidablePred pred] (h : forall i in s, w i != 0 -> pred i) : {x in
 s | pred x}.weightedVSubOfPoint p b w = s.weightedVSubOfPoint p b w
参数：w : ι -> k；p : ι -> P；b : P；h : forall i in s, w i != 0 -> pred i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_filter_of_ne`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} 
[inst : AddCommMonoid M] {f : ι → M} {p : ι → Prop}   [inst_1 : DecidablePred p]
, (∀ x ∈ s, f…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False

--- 原说明 ---
A weighted sum over `{x ∈ s | pred x}` equals one over `s` if all the weights at
 indices in `s`
not satisfying `pred` are zero.
-/
theorem weightedVSubOfPoint_filter_of_ne (w : ι → k) (p : ι → P) (b : P) {pred : ι → Prop}
    [DecidablePred pred] (h : ∀ i ∈ s, w i ≠ 0 → pred i) :
    {x ∈ s | pred x}.weightedVSubOfPoint p b w = s.weightedVSubOfPoint p b w := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply, sum_filter_of_ne]
  intro i hi hne
  refine h i hi ?_
  intro hw
  simp [hw] at hne

/-- A constant multiplier of the weights in `weightedVSubOfPoint` may be moved outside the
sum. -/
/-
**Finset.weightedVSubOfPoint_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSubOfPoint_const_smul (w : ι -> k) (p : ι -> P) (b : P) (c : k) :
 s.weightedVSubOfPoint p b (c • w) = c • s.weightedVSubOfPoint p b w
参数：w : ι -> k；p : ι -> P；b : P；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A constant multiplier of the weights in `weightedVSubOfPoint` may be moved outsi
de the
sum.
-/
theorem weightedVSubOfPoint_const_smul (w : ι → k) (p : ι → P) (b : P) (c : k) :
    s.weightedVSubOfPoint p b (c • w) = c • s.weightedVSubOfPoint p b w := by
  simp_rw [weightedVSubOfPoint_apply, smul_sum, Pi.smul_apply, smul_smul, smul_eq_mul]

/-- A weighted sum of the results of subtracting a default base point
from the given points, as a linear map on the weights.  This is
intended to be used when the sum of the weights is 0; that condition
is specified as a hypothesis on those lemmas that require it. -/
/-
**Finset.weightedVSub** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：weightedVSub (p : ι -> P) : (ι -> k) ->ₗ[k] V
参数：p : ι -> P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weighted sum of the results of subtracting a default base point
from the given points, as a linear map on the weights.  This is
intended to be used when the sum of the weights is 0; that condition
is specified as a hypothesis on those lemmas that require it.
-/
def weightedVSub (p : ι → P) : (ι → k) →ₗ[k] V :=
  s.weightedVSubOfPoint p (Classical.choice S.nonempty)

/-- Applying `weightedVSub` with given weights.  This is for the case
where a result involving a default base point is OK (for example, when
that base point will cancel out later); a more typical use case for
`weightedVSub` would involve selecting a preferred base point with
`weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero` and then
using `weightedVSubOfPoint_apply`. -/
/-
**Finset.weightedVSub_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_apply (w : ι -> k) (p : ι -> P) : s.weightedVSub p w = ∑ i in
 s, w i • (p i -ᵥ Classical.choice S.nonempty)
参数：w : ι -> k；p : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Applying `weightedVSub` with given weights.  This is for the case
where a result involving a default base point is OK (for example, when
that base point will cancel out later); a more typical use case for
`weightedVSub` would involve selecting a preferred base point with
`weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero` and then
using `weightedVSubOfPoint_apply`.
-/
theorem weightedVSub_apply (w : ι → k) (p : ι → P) :
    s.weightedVSub p w = ∑ i ∈ s, w i • (p i -ᵥ Classical.choice S.nonempty) := by
  simp [weightedVSub]

/-- `weightedVSub` gives the sum of the results of subtracting any
base point, when the sum of the weights is 0. -/
/-
**Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 `Finset`。
形式化陈述：weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero (w : ι -> k) (p : ι -> 
P) (h : ∑ i in s, w i = 0) (b : P) : s.weightedVSub p w = s.weightedVSubOfPoint 
p b w
参数：w : ι -> k；p : ι -> P；h : ∑ i in s, w i = 0；b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.weightedVSubOfPoint_eq_of_sum_eq_zero`：weightedVSubOfPoint_eq_of_
sum_eq_zero (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w i = 0) (b₁ b₂ : P) : s.we
ightedVSubOfPoint p b₁ w = s.weigh…

--- 原说明 ---
`weightedVSub` gives the sum of the results of subtracting any
base point, when the sum of the weights is 0.
-/
theorem weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero (w : ι → k) (p : ι → P)
    (h : ∑ i ∈ s, w i = 0) (b : P) : s.weightedVSub p w = s.weightedVSubOfPoint p b w :=
  s.weightedVSubOfPoint_eq_of_sum_eq_zero w p h _ _

/-- The value of `weightedVSub`, where the given points are equal and the sum of the weights
is 0. -/
@[simp]
/-
**Finset.weightedVSub_apply_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_apply_const (w : ι -> k) (p : P) (h : ∑ i in s, w i = 0) : s.
weightedVSub (fun _ => p) w = 0
参数：w : ι -> k；p : P；h : ∑ i in s, w i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSub.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3}
 [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [S : A
ddTorsor V P] …
· 使用定理 `Finset.weightedVSubOfPoint_apply_const`：weightedVSubOfPoint_apply_const 
(w : ι -> k) (p : P) (b : P) : s.weightedVSubOfPoint (fun _ => p) b w = (∑ i in 
s, w i) • (p -ᵥ b)
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0

--- 原说明 ---
The value of `weightedVSub`, where the given points are equal and the sum of the
 weights
is 0.
-/
theorem weightedVSub_apply_const (w : ι → k) (p : P) (h : ∑ i ∈ s, w i = 0) :
    s.weightedVSub (fun _ => p) w = 0 := by
  rw [weightedVSub, weightedVSubOfPoint_apply_const, h, zero_smul]

/-- The `weightedVSub` for an empty set is 0. -/
@[simp]
/-
**Finset.weightedVSub_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_empty (w : ι -> k) (p : ι -> P) : (∅ : Finset ι).weightedVSub
 p w = (0 : V)
参数：w : ι -> k；p : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSub_apply`：weightedVSub_apply (w : ι -> k) (p : ι -> P) 
: s.weightedVSub p w = ∑ i in s, w i • (p i -ᵥ Classical.choice S.nonempty)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `weightedVSub` for an empty set is 0.
-/
theorem weightedVSub_empty (w : ι → k) (p : ι → P) : (∅ : Finset ι).weightedVSub p w = (0 : V) := by
  simp [weightedVSub_apply]
/-
**Finset.weightedVSub_vadd** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_vadd {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 0) (p :
 ι -> P) (v : V) : s.weightedVSub (v +ᵥ p) w = s.weightedVSub p w
参数：h : ∑ i in s, w i = 0；p : ι -> P；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSub.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3}
 [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [S : A
ddTorsor V P] …
· 使用引理 `Finset.weightedVSubOfPoint_vadd`：weightedVSubOfPoint_vadd (s : Finset ι)
 (w : ι -> k) (p : ι -> P) (b : P) (v : V) : s.weightedVSubOfPoint (v +ᵥ p) b w 
= s.weightedVSubOfPoi…
· 使用定理 `Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero`：weightedVSub_
eq_weightedVSubOfPoint_of_sum_eq_zero (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w
 i = 0) (b : P) : s.weightedVSub p w = s.weight…
-/
lemma weightedVSub_vadd {s : Finset ι} {w : ι → k} (h : ∑ i ∈ s, w i = 0) (p : ι → P) (v : V) :
    s.weightedVSub (v +ᵥ p) w = s.weightedVSub p w := by
  rw [weightedVSub, weightedVSubOfPoint_vadd,
    weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ h]
/-
**Finset.weightedVSub_smul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_smul {G : Type*} [Group G] [DistribMulAction G V] [SMulCommCl
ass G k V] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 0) (p : ι -> V) (a :
 G) : s.weightedVSub (a • p) w = a • s.weightedVSub p w
参数：h : ∑ i in s, w i = 0；p : ι -> V；a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSub.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3}
 [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [S : A
ddTorsor V P] …
· 使用引理 `Finset.weightedVSubOfPoint_smul`：weightedVSubOfPoint_smul {G : Type*} [G
roup G] [DistribMulAction G V] [SMulCommClass G k V] (s : Finset ι) (w : ι -> k)
 (p : ι -> V) (b : V)…
· 使用定理 `Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero`：weightedVSub_
eq_weightedVSubOfPoint_of_sum_eq_zero (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w
 i = 0) (b : P) : s.weightedVSub p w = s.weight…
-/
lemma weightedVSub_smul {G : Type*} [Group G] [DistribMulAction G V] [SMulCommClass G k V]
    {s : Finset ι} {w : ι → k} (h : ∑ i ∈ s, w i = 0) (p : ι → V) (a : G) :
    s.weightedVSub (a • p) w = a • s.weightedVSub p w := by
  rw [weightedVSub, weightedVSubOfPoint_smul,
    weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ h]

/-- `weightedVSub` gives equal results for two families of weights and two families of points
that are equal on `s`. -/
/-
**Finset.weightedVSub_congr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_congr {w₁ w₂ : ι -> k} (hw : forall i in s, w₁ i = w₂ i) {p₁ 
p₂ : ι -> P} (hp : forall i in s, p₁ i = p₂ i) : s.weightedVSub p₁ w₁ = s.weight
edVSub p₂ w₂
参数：hw : forall i in s, w₁ i = w₂ i；hp : forall i in s, p₁ i = p₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.weightedVSubOfPoint_congr`：weightedVSubOfPoint_congr {w₁ w₂ : ι -
> k} (hw : forall i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P} (hp : forall i in s, p₁ 
i = p₂ i) (b : P) : s.…

--- 原说明 ---
`weightedVSub` gives equal results for two families of weights and two families 
of points
that are equal on `s`.
-/
theorem weightedVSub_congr {w₁ w₂ : ι → k} (hw : ∀ i ∈ s, w₁ i = w₂ i) {p₁ p₂ : ι → P}
    (hp : ∀ i ∈ s, p₁ i = p₂ i) : s.weightedVSub p₁ w₁ = s.weightedVSub p₂ w₂ :=
  s.weightedVSubOfPoint_congr hw hp _

/-- The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
/-
**Finset.weightedVSub_indicator_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_indicator_subset (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι}
 (h : s₁ subseteq s₂) : s₁.weightedVSub p w = s₂.weightedVSub p (Set.indicator (
↑s₁) w)
参数：w : ι -> k；p : ι -> P；h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.weightedVSubOfPoint_indicator_subset`：weightedVSubOfPoint_indicat
or_subset (w : ι -> k) (p : ι -> P) (b : P) {s₁ s₂ : Finset ι} (h : s₁ subseteq 
s₂) : s₁.weightedVSubOfPoint p b …

--- 原说明 ---
The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set.
-/
theorem weightedVSub_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : Finset ι} (h : s₁ ⊆ s₂) :
    s₁.weightedVSub p w = s₂.weightedVSub p (Set.indicator (↑s₁) w) :=
  weightedVSubOfPoint_indicator_subset _ _ _ h

/-- A weighted subtraction, over the image of an embedding, equals a
weighted subtraction with the same points and weights over the
original `Finset`. -/
/-
**Finset.weightedVSub_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_map (e : ι₂ ↪ ι) (w : ι -> k) (p : ι -> P) : (s₂.map e).weigh
tedVSub p w = s₂.weightedVSub (p ∘ e) (w ∘ e)
参数：e : ι₂ ↪ ι；w : ι -> k；p : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.weightedVSubOfPoint_map`：weightedVSubOfPoint_map (e : ι₂ ↪ ι) (w 
: ι -> k) (p : ι -> P) (b : P) : (s₂.map e).weightedVSubOfPoint p b w = s₂.weigh
tedVSubOfPoint (p ∘ …

--- 原说明 ---
A weighted subtraction, over the image of an embedding, equals a
weighted subtraction with the same points and weights over the
original `Finset`.
-/
theorem weightedVSub_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
    (s₂.map e).weightedVSub p w = s₂.weightedVSub (p ∘ e) (w ∘ e) :=
  s₂.weightedVSubOfPoint_map _ _ _ _

/-- A weighted sum of pairwise subtractions, expressed as a subtraction of two `weightedVSub`
expressions. -/
/-
**Finset.sum_smul_vsub_eq_weightedVSub_sub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_smul_vsub_eq_weightedVSub_sub (w : ι -> k) (p₁ p₂ : ι -> P) : (∑ i in 
s, w i • (p₁ i -ᵥ p₂ i)) = s.weightedVSub p₁ w - s.weightedVSub p₂ w
参数：w : ι -> k；p₁ p₂ : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_smul_vsub_eq_weightedVSubOfPoint_sub`：sum_smul_vsub_eq_weight
edVSubOfPoint_sub (w : ι -> k) (p₁ p₂ : ι -> P) (b : P) : (∑ i in s, w i • (p₁ i
 -ᵥ p₂ i)) = s.weightedVSubOfPoint p₁…

--- 原说明 ---
A weighted sum of pairwise subtractions, expressed as a subtraction of two `weig
htedVSub`
expressions.
-/
theorem sum_smul_vsub_eq_weightedVSub_sub (w : ι → k) (p₁ p₂ : ι → P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂ i)) = s.weightedVSub p₁ w - s.weightedVSub p₂ w :=
  s.sum_smul_vsub_eq_weightedVSubOfPoint_sub _ _ _ _

/-- A weighted sum of pairwise subtractions, where the point on the right is constant and the
sum of the weights is 0. -/
/-
**Finset.sum_smul_vsub_const_eq_weightedVSub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_smul_vsub_const_eq_weightedVSub (w : ι -> k) (p₁ : ι -> P) (p₂ : P) (h
 : ∑ i in s, w i = 0) : (∑ i in s, w i • (p₁ i -ᵥ p₂)) = s.weightedVSub p₁ w
参数：w : ι -> k；p₁ : ι -> P；p₂ : P；h : ∑ i in s, w i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_smul_vsub_eq_weightedVSub_sub`：sum_smul_vsub_eq_weightedVSub_
sub (w : ι -> k) (p₁ p₂ : ι -> P) : (∑ i in s, w i • (p₁ i -ᵥ p₂ i)) = s.weighte
dVSub p₁ w - s.weightedVSub p₂…
· 使用定理 `Finset.weightedVSub_apply_const`：weightedVSub_apply_const (w : ι -> k) (
p : P) (h : ∑ i in s, w i = 0) : s.weightedVSub (fun _ => p) w = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a

--- 原说明 ---
A weighted sum of pairwise subtractions, where the point on the right is constan
t and the
sum of the weights is 0.
-/
theorem sum_smul_vsub_const_eq_weightedVSub (w : ι → k) (p₁ : ι → P) (p₂ : P)
    (h : ∑ i ∈ s, w i = 0) : (∑ i ∈ s, w i • (p₁ i -ᵥ p₂)) = s.weightedVSub p₁ w := by
  rw [sum_smul_vsub_eq_weightedVSub_sub, s.weightedVSub_apply_const _ _ h, sub_zero]

/-- A weighted sum of pairwise subtractions, where the point on the left is constant and the
sum of the weights is 0. -/
/-
**Finset.sum_smul_const_vsub_eq_neg_weightedVSub** 是 Mathlib 中的一个定理，位于命名空间 `Fins
et`。
形式化陈述：sum_smul_const_vsub_eq_neg_weightedVSub (w : ι -> k) (p₂ : ι -> P) (p₁ : P
) (h : ∑ i in s, w i = 0) : (∑ i in s, w i • (p₁ -ᵥ p₂ i)) = -s.weightedVSub p₂ 
w
参数：w : ι -> k；p₂ : ι -> P；p₁ : P；h : ∑ i in s, w i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_smul_vsub_eq_weightedVSub_sub`：sum_smul_vsub_eq_weightedVSub_
sub (w : ι -> k) (p₁ p₂ : ι -> P) : (∑ i in s, w i • (p₁ i -ᵥ p₂ i)) = s.weighte
dVSub p₁ w - s.weightedVSub p₂…
· 使用定理 `Finset.weightedVSub_apply_const`：weightedVSub_apply_const (w : ι -> k) (
p : P) (h : ∑ i in s, w i = 0) : s.weightedVSub (fun _ => p) w = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a

--- 原说明 ---
A weighted sum of pairwise subtractions, where the point on the left is constant
 and the
sum of the weights is 0.
-/
theorem sum_smul_const_vsub_eq_neg_weightedVSub (w : ι → k) (p₂ : ι → P) (p₁ : P)
    (h : ∑ i ∈ s, w i = 0) : (∑ i ∈ s, w i • (p₁ -ᵥ p₂ i)) = -s.weightedVSub p₂ w := by
  rw [sum_smul_vsub_eq_weightedVSub_sub, s.weightedVSub_apply_const _ _ h, zero_sub]

/-- A weighted sum may be split into such sums over two subsets. -/
/-
**Finset.weightedVSub_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_sdiff [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w 
: ι -> k) (p : ι -> P) : (s \ s₂).weightedVSub p w + s₂.weightedVSub p w = s.wei
ghtedVSub p w
参数：h : s₂ subseteq s；w : ι -> k；p : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.weightedVSubOfPoint_sdiff`：weightedVSubOfPoint_sdiff [DecidableEq
 ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k) (p : ι -> P) (b : P) : (s \
 s₂).weightedVSubOfPoi…

--- 原说明 ---
A weighted sum may be split into such sums over two subsets.
-/
theorem weightedVSub_sdiff [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k) (p : ι → P) :
    (s \ s₂).weightedVSub p w + s₂.weightedVSub p w = s.weightedVSub p w :=
  s.weightedVSubOfPoint_sdiff h _ _ _

/-- A weighted sum may be split into a subtraction of such sums over two subsets. -/
/-
**Finset.weightedVSub_sdiff_sub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subseteq s)
 (w : ι -> k) (p : ι -> P) : (s \ s₂).weightedVSub p w - s₂.weightedVSub p (-w) 
= s.weightedVSub p w
参数：h : s₂ subseteq s；w : ι -> k；p : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.weightedVSubOfPoint_sdiff_sub`：weightedVSubOfPoint_sdiff_sub [Dec
idableEq ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k) (p : ι -> P) (b : P
) : (s \ s₂).weightedVSubO…

--- 原说明 ---
A weighted sum may be split into a subtraction of such sums over two subsets.
-/
theorem weightedVSub_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) : (s \ s₂).weightedVSub p w - s₂.weightedVSub p (-w) = s.weightedVSub p w :=
  s.weightedVSubOfPoint_sdiff_sub h _ _ _

/-- A weighted sum over `s.subtype pred` equals one over `{x ∈ s | pred x}`. -/
/-
**Finset.weightedVSub_subtype_eq_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_subtype_eq_filter (w : ι -> k) (p : ι -> P) (pred : ι -> Prop
) [DecidablePred pred] : ((s.subtype pred).weightedVSub (fun i => p i) fun i => 
w i) = {x in s | pred x}.weightedVSub p w
参数：w : ι -> k；p : ι -> P；pred : ι -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.weightedVSubOfPoint_subtype_eq_filter`：weightedVSubOfPoint_subtyp
e_eq_filter (w : ι -> k) (p : ι -> P) (b : P) (pred : ι -> Prop) [DecidablePred 
pred] : ((s.subtype pred).weighted…

--- 原说明 ---
A weighted sum over `s.subtype pred` equals one over `{x ∈ s | pred x}`.
-/
theorem weightedVSub_subtype_eq_filter (w : ι → k) (p : ι → P) (pred : ι → Prop)
    [DecidablePred pred] :
    ((s.subtype pred).weightedVSub (fun i => p i) fun i => w i) =
      {x ∈ s | pred x}.weightedVSub p w :=
  s.weightedVSubOfPoint_subtype_eq_filter _ _ _ _

/-- A weighted sum over `{x ∈ s | pred x}` equals one over `s` if all the weights at indices in `s`
not satisfying `pred` are zero. -/
/-
**Finset.weightedVSub_filter_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_filter_of_ne (w : ι -> k) (p : ι -> P) {pred : ι -> Prop} [De
cidablePred pred] (h : forall i in s, w i != 0 -> pred i) : {x in s | pred x}.we
ightedVSub p w = s.weightedVSub p w
参数：w : ι -> k；p : ι -> P；h : forall i in s, w i != 0 -> pred i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.weightedVSubOfPoint_filter_of_ne`：weightedVSubOfPoint_filter_of_n
e (w : ι -> k) (p : ι -> P) (b : P) {pred : ι -> Prop} [DecidablePred pred] (h :
 forall i in s, w i != 0 -> p…

--- 原说明 ---
A weighted sum over `{x ∈ s | pred x}` equals one over `s` if all the weights at
 indices in `s`
not satisfying `pred` are zero.
-/
theorem weightedVSub_filter_of_ne (w : ι → k) (p : ι → P) {pred : ι → Prop} [DecidablePred pred]
    (h : ∀ i ∈ s, w i ≠ 0 → pred i) : {x ∈ s | pred x}.weightedVSub p w = s.weightedVSub p w :=
  s.weightedVSubOfPoint_filter_of_ne _ _ _ h

/-- A constant multiplier of the weights in `weightedVSub_of` may be moved outside the sum. -/
/-
**Finset.weightedVSub_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_const_smul (w : ι -> k) (p : ι -> P) (c : k) : s.weightedVSub
 p (c • w) = c • s.weightedVSub p w
参数：w : ι -> k；p : ι -> P；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.weightedVSubOfPoint_const_smul`：weightedVSubOfPoint_const_smul (w
 : ι -> k) (p : ι -> P) (b : P) (c : k) : s.weightedVSubOfPoint p b (c • w) = c 
• s.weightedVSubOfPoint p b…

--- 原说明 ---
A constant multiplier of the weights in `weightedVSub_of` may be moved outside t
he sum.
-/
theorem weightedVSub_const_smul (w : ι → k) (p : ι → P) (c : k) :
    s.weightedVSub p (c • w) = c • s.weightedVSub p w :=
  s.weightedVSubOfPoint_const_smul _ _ _ _
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AffineSpace (ι → k) (ι → k) := Pi.instAddTorsor

variable (k)

/-- A weighted sum of the results of subtracting a default base point
from the given points, added to that base point, as an affine map on
the weights.  This is intended to be used when the sum of the weights
is 1, in which case it is an affine combination (barycenter) of the
points with the given weights; that condition is specified as a
hypothesis on those lemmas that require it. -/
/-
**Finset.affineCombination** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：affineCombination (p : ι -> P) : (ι -> k) ->ᵃ[k] P where toFun w
参数：p : ι -> P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weighted sum of the results of subtracting a default base point
from the given points, added to that base point, as an affine map on
the weights.  This is intended to be used when the sum of the weights
is 1, in which case it is an affine combination (barycenter) of the
points with the given weights; that condition is specified as a
hypothesis on those lemmas that require it.
-/
def affineCombination (p : ι → P) : (ι → k) →ᵃ[k] P where
  toFun w := s.weightedVSubOfPoint p (Classical.choice S.nonempty) w +ᵥ Classical.choice S.nonempty
  linear := s.weightedVSub p
  map_vadd' w₁ w₂ := by simp_rw [vadd_vadd, weightedVSub, vadd_eq_add, map_add]

/-- The linear map corresponding to `affineCombination` is
`weightedVSub`. -/
@[simp]
/-
**Finset.affineCombination_linear** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：affineCombination_linear (p : ι -> P) : (s.affineCombination k p).linear =
 s.weightedVSub p
参数：p : ι -> P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map corresponding to `affineCombination` is
`weightedVSub`.
-/
theorem affineCombination_linear (p : ι → P) :
    (s.affineCombination k p).linear = s.weightedVSub p :=
  rfl

variable {k}

/-- Applying `affineCombination` with given weights.  This is for the
case where a result involving a default base point is OK (for example,
when that base point will cancel out later); a more typical use case
for `affineCombination` would involve selecting a preferred base
point with
`affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one` and
then using `weightedVSubOfPoint_apply`. -/
/-
**Finset.affineCombination_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：affineCombination_apply (w : ι -> k) (p : ι -> P) : (s.affineCombination k
 p) w = s.weightedVSubOfPoint p (Classical.choice S.nonempty) w +ᵥ Classical.cho
ice S.nonempty
参数：w : ι -> k；p : ι -> P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying `affineCombination` with given weights.  This is for the
case where a result involving a default base point is OK (for example,
when that base point will cancel out later); a more typical use case
for `affineCombination` would involve selecting a preferred base
point with
`affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one` and
then using `weightedVSubOfPoint_apply`.
-/
theorem affineCombination_apply (w : ι → k) (p : ι → P) :
    (s.affineCombination k p) w =
      s.weightedVSubOfPoint p (Classical.choice S.nonempty) w +ᵥ Classical.choice S.nonempty :=
  rfl

/-- The value of `affineCombination`, where the given points are equal. -/
@[simp]
/-
**Finset.affineCombination_apply_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：affineCombination_apply_const (w : ι -> k) (p : P) (h : ∑ i in s, w i = 1)
 : s.affineCombination k (fun _ => p) w = p
参数：w : ι -> k；p : P；h : ∑ i in s, w i = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombination_apply`：affineCombination_apply (w : ι -> k) (p 
: ι -> P) : (s.affineCombination k p) w = s.weightedVSubOfPoint p (Classical.cho
ice S.nonempty) w +ᵥ…
· 使用定理 `Finset.weightedVSubOfPoint_apply_const`：weightedVSubOfPoint_apply_const 
(w : ι -> k) (p : P) (b : P) : s.weightedVSubOfPoint (fun _ => p) b w = (∑ i in 
s, w i) • (p -ᵥ b)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁

--- 原说明 ---
The value of `affineCombination`, where the given points are equal.
-/
theorem affineCombination_apply_const (w : ι → k) (p : P) (h : ∑ i ∈ s, w i = 1) :
    s.affineCombination k (fun _ => p) w = p := by
  rw [affineCombination_apply, s.weightedVSubOfPoint_apply_const, h, one_smul, vsub_vadd]

/-- `affineCombination` gives equal results for two families of weights and two families of
points that are equal on `s`. -/
/-
**Finset.affineCombination_congr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：affineCombination_congr {w₁ w₂ : ι -> k} (hw : forall i in s, w₁ i = w₂ i)
 {p₁ p₂ : ι -> P} (hp : forall i in s, p₁ i = p₂ i) : s.affineCombination k p₁ w
₁ = s.affineCombination k p₂ w₂
参数：hw : forall i in s, w₁ i = w₂ i；hp : forall i in s, p₁ i = p₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_congr`：weightedVSubOfPoint_congr {w₁ w₂ : ι -
> k} (hw : forall i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P} (hp : forall i in s, p₁ 
i = p₂ i) (b : P) : s.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`affineCombination` gives equal results for two families of weights and two fami
lies of
points that are equal on `s`.
-/
theorem affineCombination_congr {w₁ w₂ : ι → k} (hw : ∀ i ∈ s, w₁ i = w₂ i) {p₁ p₂ : ι → P}
    (hp : ∀ i ∈ s, p₁ i = p₂ i) : s.affineCombination k p₁ w₁ = s.affineCombination k p₂ w₂ := by
  simp_rw [affineCombination_apply, s.weightedVSubOfPoint_congr hw hp]

/-- `affineCombination` gives the sum with any base point, when the
sum of the weights is 1. -/
/-
**Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one** 是 Mathlib
 中的一个定理，位于命名空间 `Finset`。
形式化陈述：affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι -> k) (
p : ι -> P) (h : ∑ i in s, w i = 1) (b : P) : s.affineCombination k p w = s.weig
htedVSubOfPoint p b w +ᵥ b
参数：w : ι -> k；p : ι -> P；h : ∑ i in s, w i = 1；b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.weightedVSubOfPoint_vadd_eq_of_sum_eq_one`：weightedVSubOfPoint_va
dd_eq_of_sum_eq_one (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w i = 1) (b₁ b₂ : P
) : s.weightedVSubOfPoint p b₁ w +ᵥ b₁…

--- 原说明 ---
`affineCombination` gives the sum with any base point, when the
sum of the weights is 1.
-/
theorem affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι → k) (p : ι → P)
    (h : ∑ i ∈ s, w i = 1) (b : P) :
    s.affineCombination k p w = s.weightedVSubOfPoint p b w +ᵥ b :=
  s.weightedVSubOfPoint_vadd_eq_of_sum_eq_one w p h _ _

/-- Adding a `weightedVSub` to an `affineCombination`. -/
/-
**Finset.weightedVSub_vadd_affineCombination** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_vadd_affineCombination (w₁ w₂ : ι -> k) (p : ι -> P) : s.weig
htedVSub p w₁ +ᵥ s.affineCombination k p w₂ = s.affineCombination k p (w₁ + w₂)
参数：w₁ w₂ : ι -> k；p : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `Finset.affineCombination_linear`：affineCombination_linear (p : ι -> P) :
 (s.affineCombination k p).linear = s.weightedVSub p

--- 原说明 ---
Adding a `weightedVSub` to an `affineCombination`.
-/
theorem weightedVSub_vadd_affineCombination (w₁ w₂ : ι → k) (p : ι → P) :
    s.weightedVSub p w₁ +ᵥ s.affineCombination k p w₂ = s.affineCombination k p (w₁ + w₂) := by
  rw [← vadd_eq_add, AffineMap.map_vadd, affineCombination_linear]

/-- Subtracting two `affineCombination`s. -/
/-
**Finset.affineCombination_vsub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：affineCombination_vsub (w₁ w₂ : ι -> k) (p : ι -> P) : s.affineCombination
 k p w₁ -ᵥ s.affineCombination k p w₂ = s.weightedVSub p (w₁ - w₂)
参数：w₁ w₂ : ι -> k；p : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
· 使用定理 `Finset.affineCombination_linear`：affineCombination_linear (p : ι -> P) :
 (s.affineCombination k p).linear = s.weightedVSub p
· 使用定理 `vsub_eq_sub`：∀ {G : Type u_1} [inst : AddGroup G] (g₁ g₂ : G), g₁ -ᵥ g₂ 
= g₁ - g₂

--- 原说明 ---
Subtracting two `affineCombination`s.
-/
theorem affineCombination_vsub (w₁ w₂ : ι → k) (p : ι → P) :
    s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weightedVSub p (w₁ - w₂) := by
  rw [← AffineMap.linearMap_vsub, affineCombination_linear, vsub_eq_sub]
/-
**Finset.attach_affineCombination_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：attach_affineCombination_of_injective [DecidableEq P] (s : Finset P) (w : 
P -> k) (f : s -> P) (hf : Function.Injective f) : s.attach.affineCombination k 
f (w ∘ f) = (image f univ).affineCombination k id w
参数：s : Finset P；w : P -> k；f : s -> P；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `AffineMap.mk.congr_simp`：∀ {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3
} {V2 : Type u_4} {P2 : Type u_5} [inst : Ring k]   [inst_1 : AddCommGroup V1] [
inst_2 : _roo…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用定理 `Finset.coe_attach`：coe_attach (s : Finset α) : (s.attach : Set s) = Set.
univ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem attach_affineCombination_of_injective [DecidableEq P] (s : Finset P) (w : P → k) (f : s → P)
    (hf : Function.Injective f) :
    s.attach.affineCombination k f (w ∘ f) = (image f univ).affineCombination k id w := by
  simp [affineCombination, hf]
/-
**Finset.attach_affineCombination_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：attach_affineCombination_coe (s : Finset P) (w : P -> k) : s.attach.affine
Combination k ((↑) : s -> P) (w ∘ (↑)) = s.affineCombination k id w
参数：s : Finset P；w : P -> k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.attach_affineCombination_of_injective`：attach_affineCombination_o
f_injective [DecidableEq P] (s : Finset P) (w : P -> k) (f : s -> P) (hf : Funct
ion.Injective f) : s.attach.affine…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Finset.univ_eq_attach`：Finset.univ_eq_attach {α : Type u} (s : Finset α)
 : (univ : Finset s) = s.attach
· 使用定理 `Finset.attach_image_val`：attach_image_val [DecidableEq α] {s : Finset α}
 : s.attach.image Subtype.val = s
-/
theorem attach_affineCombination_coe (s : Finset P) (w : P → k) :
    s.attach.affineCombination k ((↑) : s → P) (w ∘ (↑)) = s.affineCombination k id w := by
  classical rw [attach_affineCombination_of_injective s w ((↑) : s → P) Subtype.coe_injective,
      univ_eq_attach, attach_image_val]

/-- Viewing a module as an affine space modelled on itself, a `weightedVSub` is just a linear
combination. -/
@[simp]
/-
**Finset.weightedVSub_eq_linear_combination** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSub_eq_linear_combination {ι} (s : Finset ι) {w : ι -> k} {p : ι 
-> V} (hw : s.sum w = 0) : s.weightedVSub p w = ∑ i in s, w i • p i
参数：s : Finset ι；hw : s.sum w = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Finset.weightedVSub_apply`：weightedVSub_apply (w : ι -> k) (p : ι -> P) 
: s.weightedVSub p w = ∑ i in s, w i • (p i -ᵥ Classical.choice S.nonempty)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Viewing a module as an affine space modelled on itself, a `weightedVSub` is just
 a linear
combination.
-/
theorem weightedVSub_eq_linear_combination {ι} (s : Finset ι) {w : ι → k} {p : ι → V}
    (hw : s.sum w = 0) : s.weightedVSub p w = ∑ i ∈ s, w i • p i := by
  simp [s.weightedVSub_apply, vsub_eq_sub, smul_sub, ← Finset.sum_smul, hw]

/-- Viewing a module as an affine space modelled on itself, affine combinations are just linear
combinations. -/
@[simp]
/-
**Finset.affineCombination_eq_linear_combination** 是 Mathlib 中的一个定理，位于命名空间 `Fins
et`。
形式化陈述：affineCombination_eq_linear_combination (s : Finset ι) (p : ι -> V) (w : ι
 -> k) (hw : ∑ i in s, w i = 1) : s.affineCombination k p w = ∑ i in s, w i • p 
i
参数：s : Finset ι；p : ι -> V；w : ι -> k；hw : ∑ i in s, w i = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one`：affi
neCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι -> k) (p : ι -> P
) (h : ∑ i in s, w i = 1) (b : P) : s.affineCombination …
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Viewing a module as an affine space modelled on itself, affine combinations are 
just linear
combinations.
-/
theorem affineCombination_eq_linear_combination (s : Finset ι) (p : ι → V) (w : ι → k)
    (hw : ∑ i ∈ s, w i = 1) : s.affineCombination k p w = ∑ i ∈ s, w i • p i := by
  simp [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw 0]

/-- An `affineCombination` equals a point if that point is in the set
and has weight 1 and the other points in the set have weight 0. -/
-- Cannot be @[simp] because `i` cannot be inferred by `simp`.
/-
**Finset.affineCombination_of_eq_one_of_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finse
t`。
形式化陈述：affineCombination_of_eq_one_of_eq_zero (w : ι -> k) (p : ι -> P) {i : ι} (
his : i in s) (hwi : w i = 1) (hw0 : forall i2 in s, i2 != i -> w i2 = 0) : s.af
fineCombination k p w = p i
参数：w : ι -> k；p : ι -> P；his : i in s；hwi : w i = 1；hw0 : forall i2 in s, i2 != 
i -> w i2 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one`：affi
neCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι -> k) (p : ι -> P
) (h : ∑ i in s, w i = 1) (b : P) : s.affineCombination …
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
-/
theorem affineCombination_of_eq_one_of_eq_zero (w : ι → k) (p : ι → P) {i : ι} (his : i ∈ s)
    (hwi : w i = 1) (hw0 : ∀ i2 ∈ s, i2 ≠ i → w i2 = 0) : s.affineCombination k p w = p i := by
  have h1 : ∑ i ∈ s, w i = 1 := hwi ▸ sum_eq_single i hw0 fun h => False.elim (h his)
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p h1 (p i),
    weightedVSubOfPoint_apply]
  convert! zero_vadd V (p i)
  refine sum_eq_zero ?_
  intro i2 hi2
  by_cases h : i2 = i
  · simp [h]
  · simp [hw0 i2 hi2 h]

/-- An affine combination is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
/-
**Finset.affineCombination_indicator_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：affineCombination_indicator_subset (w : ι -> k) (p : ι -> P) {s₁ s₂ : Fins
et ι} (h : s₁ subseteq s₂) : s₁.affineCombination k p w = s₂.affineCombination k
 p (Set.indicator (↑s₁) w)
参数：w : ι -> k；p : ι -> P；h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombination_apply`：affineCombination_apply (w : ι -> k) (p 
: ι -> P) : (s.affineCombination k p) w = s.weightedVSubOfPoint p (Classical.cho
ice S.nonempty) w +ᵥ…
· 使用定理 `Finset.weightedVSubOfPoint_indicator_subset`：weightedVSubOfPoint_indicat
or_subset (w : ι -> k) (p : ι -> P) (b : P) {s₁ s₂ : Finset ι} (h : s₁ subseteq 
s₂) : s₁.weightedVSubOfPoint p b …

--- 原说明 ---
An affine combination is unaffected by changing the weights to the
corresponding indicator function and adding points to the set.
-/
theorem affineCombination_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : Finset ι}
    (h : s₁ ⊆ s₂) :
    s₁.affineCombination k p w = s₂.affineCombination k p (Set.indicator (↑s₁) w) := by
  rw [affineCombination_apply, affineCombination_apply,
    weightedVSubOfPoint_indicator_subset _ _ _ h]

/-- An affine combination, over the image of an embedding, equals an
affine combination with the same points and weights over the original
`Finset`. -/
/-
**Finset.affineCombination_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：affineCombination_map (e : ι₂ ↪ ι) (w : ι -> k) (p : ι -> P) : (s₂.map e).
affineCombination k p w = s₂.affineCombination k (p ∘ e) (w ∘ e)
参数：e : ι₂ ↪ ι；w : ι -> k；p : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubOfPoint_map`：weightedVSubOfPoint_map (e : ι₂ ↪ ι) (w 
: ι -> k) (p : ι -> P) (b : P) : (s₂.map e).weightedVSubOfPoint p b w = s₂.weigh
tedVSubOfPoint (p ∘ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An affine combination, over the image of an embedding, equals an
affine combination with the same points and weights over the original
`Finset`.
-/
theorem affineCombination_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
    (s₂.map e).affineCombination k p w = s₂.affineCombination k (p ∘ e) (w ∘ e) := by
  simp_rw [affineCombination_apply, weightedVSubOfPoint_map]

/-- A weighted sum of pairwise subtractions, expressed as a subtraction of two `affineCombination`
expressions. -/
/-
**Finset.sum_smul_vsub_eq_affineCombination_vsub** 是 Mathlib 中的一个定理，位于命名空间 `Fins
et`。
形式化陈述：sum_smul_vsub_eq_affineCombination_vsub (w : ι -> k) (p₁ p₂ : ι -> P) : (∑
 i in s, w i • (p₁ i -ᵥ p₂ i)) = s.affineCombination k p₁ w -ᵥ s.affineCombinati
on k p₂ w
参数：w : ι -> k；p₁ p₂ : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_vsub_vadd_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : Add
Group G] [T : AddTorsor G P] (v₁ v₂ : G) (p : P),   (v₁ +ᵥ p) -ᵥ (v₂ +ᵥ p) = v₁ 
- v₂
· 使用定理 `Finset.sum_smul_vsub_eq_weightedVSubOfPoint_sub`：sum_smul_vsub_eq_weight
edVSubOfPoint_sub (w : ι -> k) (p₁ p₂ : ι -> P) (b : P) : (∑ i in s, w i • (p₁ i
 -ᵥ p₂ i)) = s.weightedVSubOfPoint p₁…

--- 原说明 ---
A weighted sum of pairwise subtractions, expressed as a subtraction of two `affi
neCombination`
expressions.
-/
theorem sum_smul_vsub_eq_affineCombination_vsub (w : ι → k) (p₁ p₂ : ι → P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂ i)) =
      s.affineCombination k p₁ w -ᵥ s.affineCombination k p₂ w := by
  simp_rw [affineCombination_apply, vadd_vsub_vadd_cancel_right]
  exact s.sum_smul_vsub_eq_weightedVSubOfPoint_sub _ _ _ _

/-- A weighted sum of pairwise subtractions, where the point on the right is constant and the
sum of the weights is 1. -/
/-
**Finset.sum_smul_vsub_const_eq_affineCombination_vsub** 是 Mathlib 中的一个定理，位于命名空间
 `Finset`。
形式化陈述：sum_smul_vsub_const_eq_affineCombination_vsub (w : ι -> k) (p₁ : ι -> P) (
p₂ : P) (h : ∑ i in s, w i = 1) : (∑ i in s, w i • (p₁ i -ᵥ p₂)) = s.affineCombi
nation k p₁ w -ᵥ p₂
参数：w : ι -> k；p₁ : ι -> P；p₂ : P；h : ∑ i in s, w i = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_smul_vsub_eq_affineCombination_vsub`：sum_smul_vsub_eq_affineC
ombination_vsub (w : ι -> k) (p₁ p₂ : ι -> P) : (∑ i in s, w i • (p₁ i -ᵥ p₂ i))
 = s.affineCombination k p₁ w -ᵥ s.a…
· 使用定理 `Finset.affineCombination_apply_const`：affineCombination_apply_const (w :
 ι -> k) (p : P) (h : ∑ i in s, w i = 1) : s.affineCombination k (fun _ => p) w 
= p

--- 原说明 ---
A weighted sum of pairwise subtractions, where the point on the right is constan
t and the
sum of the weights is 1.
-/
theorem sum_smul_vsub_const_eq_affineCombination_vsub (w : ι → k) (p₁ : ι → P) (p₂ : P)
    (h : ∑ i ∈ s, w i = 1) : (∑ i ∈ s, w i • (p₁ i -ᵥ p₂)) = s.affineCombination k p₁ w -ᵥ p₂ := by
  rw [sum_smul_vsub_eq_affineCombination_vsub, affineCombination_apply_const _ _ _ h]

/-- A weighted sum of pairwise subtractions, where the point on the left is constant and the
sum of the weights is 1. -/
/-
**Finset.sum_smul_const_vsub_eq_vsub_affineCombination** 是 Mathlib 中的一个定理，位于命名空间
 `Finset`。
形式化陈述：sum_smul_const_vsub_eq_vsub_affineCombination (w : ι -> k) (p₂ : ι -> P) (
p₁ : P) (h : ∑ i in s, w i = 1) : (∑ i in s, w i • (p₁ -ᵥ p₂ i)) = p₁ -ᵥ s.affin
eCombination k p₂ w
参数：w : ι -> k；p₂ : ι -> P；p₁ : P；h : ∑ i in s, w i = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_smul_vsub_eq_affineCombination_vsub`：sum_smul_vsub_eq_affineC
ombination_vsub (w : ι -> k) (p₁ p₂ : ι -> P) : (∑ i in s, w i • (p₁ i -ᵥ p₂ i))
 = s.affineCombination k p₁ w -ᵥ s.a…
· 使用定理 `Finset.affineCombination_apply_const`：affineCombination_apply_const (w :
 ι -> k) (p : P) (h : ∑ i in s, w i = 1) : s.affineCombination k (fun _ => p) w 
= p

--- 原说明 ---
A weighted sum of pairwise subtractions, where the point on the left is constant
 and the
sum of the weights is 1.
-/
theorem sum_smul_const_vsub_eq_vsub_affineCombination (w : ι → k) (p₂ : ι → P) (p₁ : P)
    (h : ∑ i ∈ s, w i = 1) : (∑ i ∈ s, w i • (p₁ -ᵥ p₂ i)) = p₁ -ᵥ s.affineCombination k p₂ w := by
  rw [sum_smul_vsub_eq_affineCombination_vsub, affineCombination_apply_const _ _ _ h]

/-- A weighted sum may be split into a subtraction of affine combinations over two subsets. -/
/-
**Finset.affineCombination_sdiff_sub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：affineCombination_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ subset
eq s) (w : ι -> k) (p : ι -> P) : (s \ s₂).affineCombination k p w -ᵥ s₂.affineC
ombination k p (-w) = s.weightedVSub p w
参数：h : s₂ subseteq s；w : ι -> k；p : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_vsub_vadd_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : Add
Group G] [T : AddTorsor G P] (v₁ v₂ : G) (p : P),   (v₁ +ᵥ p) -ᵥ (v₂ +ᵥ p) = v₁ 
- v₂
· 使用定理 `Finset.weightedVSub_sdiff_sub`：weightedVSub_sdiff_sub [DecidableEq ι] {s
₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k) (p : ι -> P) : (s \ s₂).weightedV
Sub p w - s₂.weight…

--- 原说明 ---
A weighted sum may be split into a subtraction of affine combinations over two s
ubsets.
-/
theorem affineCombination_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) :
    (s \ s₂).affineCombination k p w -ᵥ s₂.affineCombination k p (-w) = s.weightedVSub p w := by
  simp_rw [affineCombination_apply, vadd_vsub_vadd_cancel_right]
  exact s.weightedVSub_sdiff_sub h _ _

/-- If a weighted sum is zero and one of the weights is `-1`, the corresponding point is
the affine combination of the other points with the given weights. -/
/-
**Finset.affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one** 是 Mathlib 
中的一个定理，位于命名空间 `Finset`。
形式化陈述：affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one {w : ι -> k} {p
 : ι -> P} (hw : s.weightedVSub p w = (0 : V)) {i : ι} [DecidablePred (· != i)] 
(his : i in s) (hwi : w i = -1) : {x in s | x != i}.affineCombination k p w = p 
i
参数：hw : s.weightedVSub p w = (0 : V)；· != i；his : i in s；hwi : w i = -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `Finset.affineCombination_sdiff_sub`：affineCombination_sdiff_sub [Decidab
leEq ι] {s₂ : Finset ι} (h : s₂ subseteq s) (w : ι -> k) (p : ι -> P) : (s \ s₂)
.affineCombination k p w…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Finset.sdiff_singleton_eq_erase`：sdiff_singleton_eq_erase (a : α) (s : F
inset α) : s \ {a} = s.erase a
· 使用定理 `Finset.filter_ne'`：filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a != b) = s.erase b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Finset.affineCombination_of_eq_one_of_eq_zero`：affineCombination_of_eq_o
ne_of_eq_zero (w : ι -> k) (p : ι -> P) {i : ι} (his : i in s) (hwi : w i = 1) (
hw0 : forall i2 in s, i2 != i -> w …
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
If a weighted sum is zero and one of the weights is `-1`, the corresponding poin
t is
the affine combination of the other points with the given weights.
-/
theorem affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one {w : ι → k} {p : ι → P}
    (hw : s.weightedVSub p w = (0 : V)) {i : ι} [DecidablePred (· ≠ i)] (his : i ∈ s)
    (hwi : w i = -1) : {x ∈ s | x ≠ i}.affineCombination k p w = p i := by
  classical
    rw [← @vsub_eq_zero_iff_eq V, ← hw,
      ← s.affineCombination_sdiff_sub (singleton_subset_iff.2 his), sdiff_singleton_eq_erase,
      ← filter_ne']
    congr
    refine (affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_singleton_self _) ?_ ?_).symm
    · simp [hwi]
    · simp

/-- An affine combination over `s.subtype pred` equals one over `{x ∈ s | pred x}`. -/
/-
**Finset.affineCombination_subtype_eq_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：affineCombination_subtype_eq_filter (w : ι -> k) (p : ι -> P) (pred : ι ->
 Prop) [DecidablePred pred] : ((s.subtype pred).affineCombination k (fun i => p 
i) fun i => w i) = {x in s | pred x}.affineCombination k p w
参数：w : ι -> k；p : ι -> P；pred : ι -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombination_apply`：affineCombination_apply (w : ι -> k) (p 
: ι -> P) : (s.affineCombination k p) w = s.weightedVSubOfPoint p (Classical.cho
ice S.nonempty) w +ᵥ…
· 使用定理 `Finset.weightedVSubOfPoint_subtype_eq_filter`：weightedVSubOfPoint_subtyp
e_eq_filter (w : ι -> k) (p : ι -> P) (b : P) (pred : ι -> Prop) [DecidablePred 
pred] : ((s.subtype pred).weighted…

--- 原说明 ---
An affine combination over `s.subtype pred` equals one over `{x ∈ s | pred x}`.
-/
theorem affineCombination_subtype_eq_filter (w : ι → k) (p : ι → P) (pred : ι → Prop)
    [DecidablePred pred] :
    ((s.subtype pred).affineCombination k (fun i => p i) fun i => w i) =
      {x ∈ s | pred x}.affineCombination k p w := by
  rw [affineCombination_apply, affineCombination_apply, weightedVSubOfPoint_subtype_eq_filter]

/-- An affine combination over `{x ∈ s | pred x}` equals one over `s` if all the weights at indices
in `s` not satisfying `pred` are zero. -/
/-
**Finset.affineCombination_filter_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：affineCombination_filter_of_ne (w : ι -> k) (p : ι -> P) {pred : ι -> Prop
} [DecidablePred pred] (h : forall i in s, w i != 0 -> pred i) : {x in s | pred 
x}.affineCombination k p w = s.affineCombination k p w
参数：w : ι -> k；p : ι -> P；h : forall i in s, w i != 0 -> pred i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombination_apply`：affineCombination_apply (w : ι -> k) (p 
: ι -> P) : (s.affineCombination k p) w = s.weightedVSubOfPoint p (Classical.cho
ice S.nonempty) w +ᵥ…
· 使用定理 `Finset.weightedVSubOfPoint_filter_of_ne`：weightedVSubOfPoint_filter_of_n
e (w : ι -> k) (p : ι -> P) (b : P) {pred : ι -> Prop} [DecidablePred pred] (h :
 forall i in s, w i != 0 -> p…

--- 原说明 ---
An affine combination over `{x ∈ s | pred x}` equals one over `s` if all the wei
ghts at indices
in `s` not satisfying `pred` are zero.
-/
theorem affineCombination_filter_of_ne (w : ι → k) (p : ι → P) {pred : ι → Prop}
    [DecidablePred pred] (h : ∀ i ∈ s, w i ≠ 0 → pred i) :
    {x ∈ s | pred x}.affineCombination k p w = s.affineCombination k p w := by
  rw [affineCombination_apply, affineCombination_apply,
    s.weightedVSubOfPoint_filter_of_ne _ _ _ h]

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as
`weightedVSubOfPoint` using a `Finset` lying within that subset and
with a given sum of weights if and only if it can be expressed as
`weightedVSubOfPoint` with that sum of weights for the
corresponding indexed family whose index type is the subtype
corresponding to that subset. -/
/-
**Finset.eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype** 是 Ma
thlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype {v : V} {
x : k} {s : Set ι} {p : ι -> P} {b : P} : (exists fs : Finset ι, ↑fs subseteq s 
∧ exists w : ι -> k, ∑ i in fs, w i = x ∧ v = fs.weightedVSubOfPoint p b w) ↔ ex
ists (fs : Finset s) (w : s -> k), ∑ i in fs, w i = x ∧ v = fs.weightedVSubOfPoi
nt (fun i : s => p i) b w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_subtype_of_mem`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι
} [inst : AddCommMonoid M] (f : ι → M) {p : ι → Prop}   [inst_1 : DecidablePred 
p], (∀ x ∈ s, p…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_subtype_subset`：map_subtype_subset {t : Set α} (s : Finset t)
 : ↑(s.map (Embedding.subtype _)) subseteq t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `dite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) 
[inst_1 : Decidable p] (a : α) (b : p → β) (c : ¬p → β),   (if h : p then b h e…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0

--- 原说明 ---
Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as
`weightedVSubOfPoint` using a `Finset` lying within that subset and
with a given sum of weights if and only if it can be expressed as
`weightedVSubOfPoint` with that sum of weights for the
corresponding indexed family whose index type is the subtype
corresponding to that subset.
-/
theorem eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype {v : V} {x : k} {s : Set ι}
    {p : ι → P} {b : P} :
    (∃ fs : Finset ι, ↑fs ⊆ s ∧ ∃ w : ι → k, ∑ i ∈ fs, w i = x ∧
        v = fs.weightedVSubOfPoint p b w) ↔
      ∃ (fs : Finset s) (w : s → k), ∑ i ∈ fs, w i = x ∧
        v = fs.weightedVSubOfPoint (fun i : s => p i) b w := by
  classical
    simp_rw [weightedVSubOfPoint_apply]
    constructor
    · rintro ⟨fs, hfs, w, rfl, rfl⟩
      exact ⟨fs.subtype (· ∈ s), fun i => w i, sum_subtype_of_mem _ hfs,
        (sum_subtype_of_mem _ hfs).symm⟩
    · rintro ⟨fs, w, rfl, rfl⟩
      refine ⟨fs.map (Function.Embedding.subtype _), map_subtype_subset _, fun i =>
        if h : i ∈ s then w ⟨i, h⟩ else 0, ?_, ?_⟩ <;> simp

variable (k)

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as `weightedVSub` using
a `Finset` lying within that subset and with sum of weights 0 if and
only if it can be expressed as `weightedVSub` with sum of weights 0
for the corresponding indexed family whose index type is the subtype
corresponding to that subset. -/
/-
**Finset.eq_weightedVSub_subset_iff_eq_weightedVSub_subtype** 是 Mathlib 中的一个定理，位
于命名空间 `Finset`。
形式化陈述：eq_weightedVSub_subset_iff_eq_weightedVSub_subtype {v : V} {s : Set ι} {p 
: ι -> P} : (exists fs : Finset ι, ↑fs subseteq s ∧ exists w : ι -> k, ∑ i in fs
, w i = 0 ∧ v = fs.weightedVSub p w) ↔ exists (fs : Finset s) (w : s -> k), ∑ i 
in fs, w i = 0 ∧ v = fs.weightedVSub (fun i : s => p i) w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype`
：eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype {v : V} {x : k
} {s : Set ι} {p : ι -> P} {b : P} : (exists fs : Finset ι, ↑…

--- 原说明 ---
Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as `weightedVSub` using
a `Finset` lying within that subset and with sum of weights 0 if and
only if it can be expressed as `weightedVSub` with sum of weights 0
for the corresponding indexed family whose index type is the subtype
corresponding to that subset.
-/
theorem eq_weightedVSub_subset_iff_eq_weightedVSub_subtype {v : V} {s : Set ι} {p : ι → P} :
    (∃ fs : Finset ι, ↑fs ⊆ s ∧ ∃ w : ι → k, ∑ i ∈ fs, w i = 0 ∧
        v = fs.weightedVSub p w) ↔
      ∃ (fs : Finset s) (w : s → k), ∑ i ∈ fs, w i = 0 ∧
        v = fs.weightedVSub (fun i : s => p i) w :=
  eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype

variable (V)

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A point can be expressed as an
`affineCombination` using a `Finset` lying within that subset and
with sum of weights 1 if and only if it can be expressed an
`affineCombination` with sum of weights 1 for the corresponding
indexed family whose index type is the subtype corresponding to that
subset. -/
/-
**Finset.eq_affineCombination_subset_iff_eq_affineCombination_subtype** 是 Mathli
b 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_affineCombination_subset_iff_eq_affineCombination_subtype {p0 : P} {s :
 Set ι} {p : ι -> P} : (exists fs : Finset ι, ↑fs subseteq s ∧ exists w : ι -> k
, ∑ i in fs, w i = 1 ∧ p0 = fs.affineCombination k p w) ↔ exists (fs : Finset s)
 (w : s -> k), ∑ i in fs, w i = 1 ∧ p0 = fs.affineCombination k (fun i : s => p 
i) w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype`
：eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype {v : V} {x : k
} {s : Set ι} {p : ι -> P} {b : P} : (exists fs : Finset ι, ↑…

--- 原说明 ---
Suppose an indexed family of points is given, along with a subset
of the index type.  A point can be expressed as an
`affineCombination` using a `Finset` lying within that subset and
with sum of weights 1 if and only if it can be expressed an
`affineCombination` with sum of weights 1 for the corresponding
indexed family whose index type is the subtype corresponding to that
subset.
-/
theorem eq_affineCombination_subset_iff_eq_affineCombination_subtype {p0 : P} {s : Set ι}
    {p : ι → P} :
    (∃ fs : Finset ι, ↑fs ⊆ s ∧ ∃ w : ι → k, ∑ i ∈ fs, w i = 1 ∧
        p0 = fs.affineCombination k p w) ↔
      ∃ (fs : Finset s) (w : s → k), ∑ i ∈ fs, w i = 1 ∧
        p0 = fs.affineCombination k (fun i : s => p i) w := by
  simp_rw [affineCombination_apply, eq_vadd_iff_vsub_eq]
  exact eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype

variable {k V}

/-- Affine maps commute with affine combinations. -/
/-
**Finset.map_affineCombination** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_affineCombination {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [Aff
ineSpace V₂ P₂] (p : ι -> P) (w : ι -> k) (hw : s.sum w = 1) (f : P ->ᵃ[k] P₂) :
 f (s.affineCombination k p w) = s.affineCombination k (f ∘ p) w
参数：p : ι -> P；w : ι -> k；hw : s.sum w = 1；f : P ->ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one`：affi
neCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι -> k) (p : ι -> P
) (h : ∑ i in s, w i = 1) (b : P) : s.affineCombination …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.weightedVSubOfPoint_vadd_eq_of_sum_eq_one`：weightedVSubOfPoint_va
dd_eq_of_sum_eq_one (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w i = 1) (b₁ b₂ : P
) : s.weightedVSubOfPoint p b₁ w +ᵥ b₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Affine maps commute with affine combinations.
-/
theorem map_affineCombination {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]
    (p : ι → P) (w : ι → k) (hw : s.sum w = 1) (f : P →ᵃ[k] P₂) :
    f (s.affineCombination k p w) = s.affineCombination k (f ∘ p) w := by
  have b := Classical.choice (inferInstance : AffineSpace V P).nonempty
  have b₂ := Classical.choice (inferInstance : AffineSpace V₂ P₂).nonempty
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw b,
    s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w (f ∘ p) hw b₂, ←
    s.weightedVSubOfPoint_vadd_eq_of_sum_eq_one w (f ∘ p) hw (f b) b₂]
  simp only [weightedVSubOfPoint_apply, RingHom.id_apply, AffineMap.map_vadd, map_smulₛₗ,
    AffineMap.linearMap_vsub, map_sum, Function.comp_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The value of `affineCombination`, where the given points take only two values. -/
/-
**Finset.affineCombination_apply_eq_lineMap_sum** 是 Mathlib 中的一个引理，位于命名空间 `Finse
t`。
形式化陈述：affineCombination_apply_eq_lineMap_sum [DecidableEq ι] (w : ι -> k) (p : ι
 -> P) (p₁ p₂ : P) (s' : Finset ι) (h : ∑ i in s, w i = 1) (hp₂ : forall i in s 
inter s', p i = p₂) (hp₁ : forall i in s \ s', p i = p₁) : s.affineCombination k
 p w = AffineMap.lineMap p₁ p₂ (∑ i in s inter s', w i)
参数：w : ι -> k；p : ι -> P；p₁ p₂ : P；s' : Finset ι；h : ∑ i in s, w i = 1；hp₂ : for
all i in s inter s', p i = p₂；hp₁ : forall i in s \ s', p i = p₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one`：affi
neCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι -> k) (p : ι -> P
) (h : ∑ i in s, w i = 1) (b : P) : s.affineCombination …
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_inter_add_sum_sdiff`：∀ {ι : Type u_1} {M : Type u_3} [inst : 
AddCommMonoid M] [inst_1 : DecidableEq ι] (s t : Finset ι) (f : ι → M),   ∑ x ∈ 
s ∩ t, f x + ∑ x ∈ s…
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `vadd_right_cancel_iff`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] {g₁ g₂ : G} (p : P), g₁ +ᵥ p = g₂ +ᵥ p ↔ g₁ = g₂
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
The value of `affineCombination`, where the given points take only two values.
-/
lemma affineCombination_apply_eq_lineMap_sum [DecidableEq ι] (w : ι → k) (p : ι → P)
    (p₁ p₂ : P) (s' : Finset ι) (h : ∑ i ∈ s, w i = 1) (hp₂ : ∀ i ∈ s ∩ s', p i = p₂)
    (hp₁ : ∀ i ∈ s \ s', p i = p₁) :
    s.affineCombination k p w = AffineMap.lineMap p₁ p₂ (∑ i ∈ s ∩ s', w i) := by
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p h p₁,
    weightedVSubOfPoint_apply, ← s.sum_inter_add_sum_sdiff s', AffineMap.lineMap_apply,
    vadd_right_cancel_iff, sum_smul]
  convert! add_zero _ with i hi
  · convert! Finset.sum_const_zero with i hi
    simp [hp₁ i hi]
  · exact (hp₂ i hi).symm

set_option backward.isDefEq.respectTransparency false in
/-- Applying `AffineMap.lineMap` on two `Finset.affineCombination` over the same set of points
is equivalent to applying `AffineMap.lineMap` to the weights. -/
/-
**Finset.lineMap_affineCombination** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lineMap_affineCombination (w₁ : ι -> k) (w₂ : ι -> k) (r : k) (p : ι -> P)
 : AffineMap.lineMap (s.affineCombination k p w₁) (s.affineCombination k p w₂) r
 = s.affineCombination k p (AffineMap.lineMap w₁ w₂ r)
参数：w₁ : ι -> k；w₂ : ι -> k；r : k；p : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AffineMap.lineMap_apply_module`：lineMap_apply_module (p₀ p₁ : V1) (c : k
) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Applying `AffineMap.lineMap` on two `Finset.affineCombination` over the same set
 of points
is equivalent to applying `AffineMap.lineMap` to the weights.
-/
theorem lineMap_affineCombination (w₁ : ι → k) (w₂ : ι → k) (r : k) (p : ι → P) :
    AffineMap.lineMap (s.affineCombination k p w₁) (s.affineCombination k p w₂) r =
    s.affineCombination k p (AffineMap.lineMap w₁ w₂ r) := by
  simp_rw [Finset.affineCombination_apply, ← AffineMap.lineMap_vadd, AffineMap.lineMap_apply_module,
    map_add, map_smul]

variable (k)

/-- Weights for expressing a single point as an affine combination. -/
@[deprecated Pi.single (since := "2026-04-16")]
/-
**Finset.affineCombinationSingleWeights** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：affineCombinationSingleWeights [DecidableEq ι] (i : ι) : ι -> k
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Weights for expressing a single point as an affine combination.
-/
def affineCombinationSingleWeights [DecidableEq ι] (i : ι) : ι → k :=
  Pi.single i 1

@[deprecated Pi.single_eq_same (since := "2026-04-16")]
/-
**Finset.affineCombinationSingleWeights_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Fi
nset`。
形式化陈述：affineCombinationSingleWeights_apply_self [DecidableEq ι] (i : ι) : affine
CombinationSingleWeights k i i = 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
theorem affineCombinationSingleWeights_apply_self [DecidableEq ι] (i : ι) :
    affineCombinationSingleWeights k i i = 1 := Pi.single_eq_same _ _

@[deprecated Pi.single_eq_of_ne (since := "2026-04-16")]
/-
**Finset.affineCombinationSingleWeights_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `F
inset`。
形式化陈述：affineCombinationSingleWeights_apply_of_ne [DecidableEq ι] {i j : ι} (h : 
j != i) : affineCombinationSingleWeights k i j = 0
参数：h : j != i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
-/
theorem affineCombinationSingleWeights_apply_of_ne [DecidableEq ι] {i j : ι} (h : j ≠ i) :
    affineCombinationSingleWeights k i j = 0 := Pi.single_eq_of_ne h _

@[deprecated Finset.sum_pi_single' (since := "2026-04-16")]
/-
**Finset.sum_affineCombinationSingleWeights** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_affineCombinationSingleWeights [DecidableEq ι] {i : ι} (h : i in s) : 
∑ j in s, affineCombinationSingleWeights k i j = 1
参数：h : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombinationSingleWeights.eq_1`：∀ (k : Type u_1) [inst : Rin
g k] {ι : Type u_4} [inst_1 : DecidableEq ι] (i : ι),   Finset.affineCombination
SingleWeights k i = Pi.single i …
· 使用定理 `Finset.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] [inst_1 : DecidableEq ι] (a : ι) (x : M) (s : Finset ι),   ∑ a' ∈ s, Pi.
single a x …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem sum_affineCombinationSingleWeights [DecidableEq ι] {i : ι} (h : i ∈ s) :
    ∑ j ∈ s, affineCombinationSingleWeights k i j = 1 := by
  rw [affineCombinationSingleWeights, s.sum_pi_single', if_pos h]

/-- Weights for expressing the subtraction of two points as a `weightedVSub`. -/
/-
**Finset.weightedVSubVSubWeights** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：weightedVSubVSubWeights [DecidableEq ι] (i j : ι) : ι -> k
参数：i j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Weights for expressing the subtraction of two points as a `weightedVSub`.
-/
def weightedVSubVSubWeights [DecidableEq ι] (i j : ι) : ι → k :=
  Pi.single i 1 - Pi.single j 1

@[simp]
/-
**Finset.weightedVSubVSubWeights_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSubVSubWeights_self [DecidableEq ι] (i : ι) : weightedVSubVSubWei
ghts k i i = 0
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem weightedVSubVSubWeights_self [DecidableEq ι] (i : ι) :
    weightedVSubVSubWeights k i i = 0 := by simp [weightedVSubVSubWeights]

@[simp]
/-
**Finset.weightedVSubVSubWeights_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSubVSubWeights_apply_left [DecidableEq ι] {i j : ι} (h : i != j) 
: weightedVSubVSubWeights k i j i = 1
参数：h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem weightedVSubVSubWeights_apply_left [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    weightedVSubVSubWeights k i j i = 1 := by simp [weightedVSubVSubWeights, h]

@[simp]
/-
**Finset.weightedVSubVSubWeights_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSubVSubWeights_apply_right [DecidableEq ι] {i j : ι} (h : i != j)
 : weightedVSubVSubWeights k i j j = -1
参数：h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem weightedVSubVSubWeights_apply_right [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    weightedVSubVSubWeights k i j j = -1 := by simp [weightedVSubVSubWeights, h.symm]

@[simp]
/-
**Finset.weightedVSubVSubWeights_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：weightedVSubVSubWeights_apply_of_ne [DecidableEq ι] {i j t : ι} (hi : t !=
 i) (hj : t != j) : weightedVSubVSubWeights k i j t = 0
参数：hi : t != i；hj : t != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem weightedVSubVSubWeights_apply_of_ne [DecidableEq ι] {i j t : ι} (hi : t ≠ i) (hj : t ≠ j) :
    weightedVSubVSubWeights k i j t = 0 := by simp [weightedVSubVSubWeights, hi, hj]

@[simp]
/-
**Finset.sum_weightedVSubVSubWeights** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_weightedVSubVSubWeights [DecidableEq ι] {i j : ι} (hi : i in s) (hj : 
j in s) : ∑ t in s, weightedVSubVSubWeights k i j t = 0
参数：hi : i in s；hj : j in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] [inst_1 : DecidableEq ι] (a : ι) (x : M) (s : Finset ι),   ∑ a' ∈ s, Pi.
single a x …
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_weightedVSubVSubWeights [DecidableEq ι] {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    ∑ t ∈ s, weightedVSubVSubWeights k i j t = 0 := by
  simp_rw [weightedVSubVSubWeights, Pi.sub_apply, sum_sub_distrib]
  simp [hi, hj]

variable {k}

/-- Weights for expressing `lineMap` as an affine combination. -/
/-
**Finset.affineCombinationLineMapWeights** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：affineCombinationLineMapWeights [DecidableEq ι] (i j : ι) (c : k) : ι -> k
参数：i j : ι；c : k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Weights for expressing `lineMap` as an affine combination.
-/
def affineCombinationLineMapWeights [DecidableEq ι] (i j : ι) (c : k) : ι → k :=
  c • weightedVSubVSubWeights k j i + Pi.single i 1

@[simp]
/-
**Finset.affineCombinationLineMapWeights_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：affineCombinationLineMapWeights_self [DecidableEq ι] (i : ι) (c : k) : aff
ineCombinationLineMapWeights i i c = Pi.single i 1
参数：i : ι；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubVSubWeights_self`：weightedVSubVSubWeights_self [Decid
ableEq ι] (i : ι) : weightedVSubVSubWeights k i i = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem affineCombinationLineMapWeights_self [DecidableEq ι] (i : ι) (c : k) :
    affineCombinationLineMapWeights i i c = Pi.single i 1 := by
  simp [affineCombinationLineMapWeights]

@[simp]
/-
**Finset.affineCombinationLineMapWeights_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `F
inset`。
形式化陈述：affineCombinationLineMapWeights_apply_left [DecidableEq ι] {i j : ι} (h : 
i != j) (c : k) : affineCombinationLineMapWeights i j c i = 1 - c
参数：h : i != j；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubVSubWeights_apply_right`：weightedVSubVSubWeights_appl
y_right [DecidableEq ι] {i j : ι} (h : i != j) : weightedVSubVSubWeights k i j j
 = -1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem affineCombinationLineMapWeights_apply_left [DecidableEq ι] {i j : ι} (h : i ≠ j) (c : k) :
    affineCombinationLineMapWeights i j c i = 1 - c := by
  simp [affineCombinationLineMapWeights, h.symm, sub_eq_neg_add]

@[simp]
/-
**Finset.affineCombinationLineMapWeights_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `
Finset`。
形式化陈述：affineCombinationLineMapWeights_apply_right [DecidableEq ι] {i j : ι} (h :
 i != j) (c : k) : affineCombinationLineMapWeights i j c j = c
参数：h : i != j；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.weightedVSubVSubWeights_apply_left`：weightedVSubVSubWeights_apply
_left [DecidableEq ι] {i j : ι} (h : i != j) : weightedVSubVSubWeights k i j i =
 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem affineCombinationLineMapWeights_apply_right [DecidableEq ι] {i j : ι} (h : i ≠ j) (c : k) :
    affineCombinationLineMapWeights i j c j = c := by
  simp [affineCombinationLineMapWeights, h.symm]

@[simp]
/-
**Finset.affineCombinationLineMapWeights_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `
Finset`。
形式化陈述：affineCombinationLineMapWeights_apply_of_ne [DecidableEq ι] {i j t : ι} (h
i : t != i) (hj : t != j) (c : k) : affineCombinationLineMapWeights i j c t = 0
参数：hi : t != i；hj : t != j；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.weightedVSubVSubWeights_apply_of_ne`：weightedVSubVSubWeights_appl
y_of_ne [DecidableEq ι] {i j t : ι} (hi : t != i) (hj : t != j) : weightedVSubVS
ubWeights k i j t = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem affineCombinationLineMapWeights_apply_of_ne [DecidableEq ι] {i j t : ι} (hi : t ≠ i)
    (hj : t ≠ j) (c : k) : affineCombinationLineMapWeights i j c t = 0 := by
  simp [affineCombinationLineMapWeights, hi, hj]

@[simp]
/-
**Finset.sum_affineCombinationLineMapWeights** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_affineCombinationLineMapWeights [DecidableEq ι] {i j : ι} (hi : i in s
) (hj : j in s) (c : k) : ∑ t in s, affineCombinationLineMapWeights i j c t = 1
参数：hi : i in s；hj : j in s；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_weightedVSubVSubWeights`：sum_weightedVSubVSubWeights [Decidab
leEq ι] {i j : ι} (hi : i in s) (hj : j in s) : ∑ t in s, weightedVSubVSubWeight
s k i j t = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] [inst_1 : DecidableEq ι] (a : ι) (x : M) (s : Finset ι),   ∑ a' ∈ s, Pi.
single a x …
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_affineCombinationLineMapWeights [DecidableEq ι] {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (c : k) : ∑ t ∈ s, affineCombinationLineMapWeights i j c t = 1 := by
  simp_rw [affineCombinationLineMapWeights, Pi.add_apply, sum_add_distrib]
  simp [hi, hj, ← mul_sum]

variable (k)

/-- An affine combination with `affineCombinationSingleWeights` gives the specified point. -/
@[simp]
/-
**Finset.affineCombination_piSingle** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：affineCombination_piSingle [DecidableEq ι] (p : ι -> P) {i : ι} (hi : i in
 s) : s.affineCombination k p (Pi.single i 1) = p i
参数：p : ι -> P；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.affineCombination_of_eq_one_of_eq_zero`：affineCombination_of_eq_o
ne_of_eq_zero (w : ι -> k) (p : ι -> P) {i : ι} (his : i in s) (hwi : w i = 1) (
hw0 : forall i2 in s, i2 != i -> w …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
An affine combination with `affineCombinationSingleWeights` gives the specified 
point.
-/
theorem affineCombination_piSingle [DecidableEq ι] (p : ι → P) {i : ι}
    (hi : i ∈ s) : s.affineCombination k p (Pi.single i 1) = p i := by
  refine s.affineCombination_of_eq_one_of_eq_zero _ _ hi (by simp) ?_
  rintro j - hj
  simp [hj]

/-- An affine combination with `affineCombinationSingleWeights` gives the specified point. -/
@[deprecated affineCombination_piSingle (since := "2026-04-16")]
/-
**Finset.affineCombination_affineCombinationSingleWeights** 是 Mathlib 中的一个定理，位于命
名空间 `Finset`。
形式化陈述：affineCombination_affineCombinationSingleWeights [DecidableEq ι] (p : ι ->
 P) {i : ι} (hi : i in s) : s.affineCombination k p (affineCombinationSingleWeig
hts k i) = p i
参数：p : ι -> P；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i

--- 原说明 ---
An affine combination with `affineCombinationSingleWeights` gives the specified 
point.
-/
theorem affineCombination_affineCombinationSingleWeights [DecidableEq ι] (p : ι → P) {i : ι}
    (hi : i ∈ s) : s.affineCombination k p (affineCombinationSingleWeights k i) = p i :=
  affineCombination_piSingle _ _ _ hi

/-- A weighted subtraction with `weightedVSubVSubWeights` gives the result of subtracting the
specified points. -/
@[simp]
/-
**Finset.weightedVSub_weightedVSubVSubWeights** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：weightedVSub_weightedVSubVSubWeights [DecidableEq ι] (p : ι -> P) {i j : ι
} (hi : i in s) (hj : j in s) : s.weightedVSub p (weightedVSubVSubWeights k i j)
 = p i -ᵥ p j
参数：p : ι -> P；hi : i in s；hj : j in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.weightedVSubVSubWeights.eq_1`：∀ (k : Type u_1) [inst : Ring k] {ι
 : Type u_4} [inst_1 : DecidableEq ι] (i j : ι),   Finset.weightedVSubVSubWeight
s k i j = Pi.single i 1 -…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_vsub`：affineCombination_vsub (w₁ w₂ : ι -> k) (
p : ι -> P) : s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weigh
tedVSub p (w₁ - w₂)
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i

--- 原说明 ---
A weighted subtraction with `weightedVSubVSubWeights` gives the result of subtra
cting the
specified points.
-/
theorem weightedVSub_weightedVSubVSubWeights [DecidableEq ι] (p : ι → P) {i j : ι} (hi : i ∈ s)
    (hj : j ∈ s) : s.weightedVSub p (weightedVSubVSubWeights k i j) = p i -ᵥ p j := by
  rw [weightedVSubVSubWeights, ← affineCombination_vsub,
    s.affineCombination_piSingle k p hi, s.affineCombination_piSingle k p hj]

variable {k}

set_option backward.isDefEq.respectTransparency false in
/-- An affine combination with `affineCombinationLineMapWeights` gives the result of
`line_map`. -/
@[simp]
/-
**Finset.affineCombination_affineCombinationLineMapWeights** 是 Mathlib 中的一个定理，位于
命名空间 `Finset`。
形式化陈述：affineCombination_affineCombinationLineMapWeights [DecidableEq ι] (p : ι -
> P) {i j : ι} (hi : i in s) (hj : j in s) (c : k) : s.affineCombination k p (af
fineCombinationLineMapWeights i j c) = AffineMap.lineMap (p i) (p j) c
参数：p : ι -> P；hi : i in s；hj : j in s；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombinationLineMapWeights.eq_1`：∀ {k : Type u_1} [inst : Ri
ng k] {ι : Type u_4} [inst_1 : DecidableEq ι] (i j : ι) (c : k),   Finset.affine
CombinationLineMapWeights i j c =…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.weightedVSub_vadd_affineCombination`：weightedVSub_vadd_affineComb
ination (w₁ w₂ : ι -> k) (p : ι -> P) : s.weightedVSub p w₁ +ᵥ s.affineCombinati
on k p w₂ = s.affineCombination …
· 使用定理 `Finset.weightedVSub_const_smul`：weightedVSub_const_smul (w : ι -> k) (p 
: ι -> P) (c : k) : s.weightedVSub p (c • w) = c • s.weightedVSub p w
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
· 使用定理 `Finset.weightedVSub_weightedVSubVSubWeights`：weightedVSub_weightedVSubVS
ubWeights [DecidableEq ι] (p : ι -> P) {i j : ι} (hi : i in s) (hj : j in s) : s
.weightedVSub p (weightedVSubVSub…
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀

--- 原说明 ---
An affine combination with `affineCombinationLineMapWeights` gives the result of
`line_map`.
-/
theorem affineCombination_affineCombinationLineMapWeights [DecidableEq ι] (p : ι → P) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (c : k) :
    s.affineCombination k p (affineCombinationLineMapWeights i j c) =
      AffineMap.lineMap (p i) (p j) c := by
  rw [affineCombinationLineMapWeights, ← weightedVSub_vadd_affineCombination,
    weightedVSub_const_smul, s.affineCombination_piSingle k p hi,
    s.weightedVSub_weightedVSubVSubWeights k p hj hi, AffineMap.lineMap_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Applying `AffineMap.homothety` on `Finset.affineCombination` towards one of the weighted points
  is equivalent to moving the weights towards `Finset.affineCombinationSingleWeights`. -/
-- Redeclaring all variables because `AffineMap.homothety` requires `[CommRing k]`
/-
**Finset.homothety_affineCombination** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：homothety_affineCombination {k V P : Type*} [CommRing k] [AddCommGroup V] 
[Module k V] [AffineSpace V P] {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι
 -> P) (w : ι -> k) {i : ι} (hi : i in s) (r : k) : AffineMap.homothety (p i) r 
(s.affineCombination k p w) = s.affineCombination k p (AffineMap.lineMap (Pi.sin
gle i 1) w r)
参数：s : Finset ι；p : ι -> P；w : ι -> k；hi : i in s；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.homothety_eq_lineMap`：homothety_eq_lineMap (c : P1) (r : k) (p
 : P1) : homothety c r p = lineMap c p r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.lineMap_affineCombination`：lineMap_affineCombination (w₁ : ι -> k
) (w₂ : ι -> k) (r : k) (p : ι -> P) : AffineMap.lineMap (s.affineCombination k 
p w₁) (s.affineCombina…
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
-/
theorem homothety_affineCombination {k V P : Type*} [CommRing k] [AddCommGroup V] [Module k V]
    [AffineSpace V P] {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → P) (w : ι → k) {i : ι}
    (hi : i ∈ s) (r : k) :
    AffineMap.homothety (p i) r (s.affineCombination k p w) = s.affineCombination k p
      (AffineMap.lineMap (Pi.single i 1) w r) := by
  rw [AffineMap.homothety_eq_lineMap, ← Finset.lineMap_affineCombination,
    Finset.affineCombination_piSingle _ _ _ hi]

end Finset

section AffineSpace'

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- A `weightedVSub` with sum of weights 0 is in the `vectorSpan` of
an indexed family. -/
/-
**weightedVSub_mem_vectorSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：weightedVSub_mem_vectorSpan {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i
 = 0) (p : ι -> P) : s.weightedVSub p w in vectorSpan k (Set.range p)
参数：h : ∑ i in s, w i = 0；p : ι -> P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.eq_empty_of_isEmpty`：eq_empty_of_isEmpty [IsEmpty α] (s : Finset 
α) : s = ∅
· 使用定理 `Finset.weightedVSub_empty`：weightedVSub_empty (w : ι -> k) (p : ι -> P) 
: (∅ : Finset ι).weightedVSub p w = (0 : V)
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `vectorSpan_range_eq_span_range_vsub_right`：vectorSpan_range_eq_span_rang
e_vsub_right (p : ι -> P) (i0 : ι) : vectorSpan k (Set.range p) = Submodule.span
 k (Set.range fun i : ι => p i …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Finsupp.mem_span_image_iff_linearCombination`：mem_span_image_iff_linearC
ombination {s : Set α} {x : M} : x in span R (v '' s) ↔ exists l in supported R 
R s, linearCombination R v l = x
· 使用定理 `Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero`：weightedVSub_
eq_weightedVSubOfPoint_of_sum_eq_zero (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w
 i = 0) (b : P) : s.weightedVSub p w = s.weight…
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Set.mem_of_indicator_ne_zero`：∀ {α : Type u_1} {M : Type u_3} [inst : Ze
ro M] {s : Set α} {f : α → M} {a : α}, s.indicator f a ≠ 0 → a ∈ s
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.onFinset_sum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] {s : Finset α} {f : α → M}   {g : α → M
 → N} (hf …
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A `weightedVSub` with sum of weights 0 is in the `vectorSpan` of
an indexed family.
-/
theorem weightedVSub_mem_vectorSpan {s : Finset ι} {w : ι → k} (h : ∑ i ∈ s, w i = 0)
    (p : ι → P) : s.weightedVSub p w ∈ vectorSpan k (Set.range p) := by
  classical
    rcases isEmpty_or_nonempty ι with (hι | ⟨⟨i0⟩⟩)
    · simp [Finset.eq_empty_of_isEmpty s]
    · rw [vectorSpan_range_eq_span_range_vsub_right k p i0, ← Set.image_univ,
        Finsupp.mem_span_image_iff_linearCombination,
        Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w p h (p i0),
        Finset.weightedVSubOfPoint_apply]
      let w' := Set.indicator (↑s) w
      have hwx : ∀ i, w' i ≠ 0 → i ∈ s := fun i => Set.mem_of_indicator_ne_zero
      use Finsupp.onFinset s w' hwx, Set.subset_univ _
      rw [Finsupp.linearCombination_apply, Finsupp.onFinset_sum hwx]
      · apply Finset.sum_congr rfl
        intro i hi
        simp [w', Set.indicator_apply, if_pos hi]
      · exact fun _ => zero_smul k _

/-- An `affineCombination` with sum of weights 1 is in the
`affineSpan` of an indexed family, if the underlying ring is
nontrivial. -/
/-
**affineCombination_mem_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineCombination_mem_affineSpan [Nontrivial k] {s : Finset ι} {w : ι -> k
} (h : ∑ i in s, w i = 1) (p : ι -> P) : s.affineCombination k p w in affineSpan
 k (Set.range p)
参数：h : ∑ i in s, w i = 1；p : ι -> P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.nonempty_of_sum_ne_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Fin
set ι} {f : ι → M} [inst : AddCommMonoid M], ∑ x ∈ s, f x ≠ 0 → s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_update_of_mem`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCom
mMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι},   i ∈ s → ∀ (f : ι →
 M) (b : M), ∑…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.affineCombination_of_eq_one_of_eq_zero`：affineCombination_of_eq_o
ne_of_eq_zero (w : ι -> k) (p : ι -> P) {i : ι} (his : i in s) (hwi : w i = 1) (
hw0 : forall i2 in s, i2 != i -> w …
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `Finset.affineCombination_vsub`：affineCombination_vsub (w₁ w₂ : ι -> k) (
p : ι -> P) : s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weigh
tedVSub p (w₁ - w₂)
· 使用定理 `weightedVSub_mem_vectorSpan`：weightedVSub_mem_vectorSpan {s : Finset ι} 
{w : ι -> k} (h : ∑ i in s, w i = 0) (p : ι -> P) : s.weightedVSub p w in vector
Span k (Set.range…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
An `affineCombination` with sum of weights 1 is in the
`affineSpan` of an indexed family, if the underlying ring is
nontrivial.
-/
theorem affineCombination_mem_affineSpan [Nontrivial k] {s : Finset ι} {w : ι → k}
    (h : ∑ i ∈ s, w i = 1) (p : ι → P) :
    s.affineCombination k p w ∈ affineSpan k (Set.range p) := by
  classical
    have hnz : ∑ i ∈ s, w i ≠ 0 := h.symm ▸ one_ne_zero
    have hn : s.Nonempty := Finset.nonempty_of_sum_ne_zero hnz
    obtain ⟨i1, hi1⟩ := hn
    let w1 : ι → k := Function.update (Function.const ι 0) i1 1
    have hw1 : ∑ i ∈ s, w1 i = 1 := by
      simp only [w1, Function.const_zero, Finset.sum_update_of_mem hi1, Pi.zero_apply,
          Finset.sum_const_zero, add_zero]
    have hw1s : s.affineCombination k p w1 = p i1 :=
      s.affineCombination_of_eq_one_of_eq_zero w1 p hi1 (Function.update_self ..) fun _ _ hne =>
        Function.update_of_ne hne ..
    have hv : s.affineCombination k p w -ᵥ p i1 ∈ (affineSpan k (Set.range p)).direction := by
      rw [direction_affineSpan, ← hw1s, Finset.affineCombination_vsub]
      apply weightedVSub_mem_vectorSpan
      simp [Pi.sub_apply, h, hw1]
    rw [← vsub_vadd (s.affineCombination k p w) (p i1)]
    exact AffineSubspace.vadd_mem_of_mem_direction hv (mem_affineSpan k (Set.mem_range_self _))

/-- An `affineCombination` with sum of weights 1 is in the
`affineSpan` of an indexed family, if the family is nonempty. -/
/-
**affineCombination_mem_affineSpan_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineCombination_mem_affineSpan_of_nonempty [Nonempty ι] {s : Finset ι} {
w : ι -> k} (h : ∑ i in s, w i = 1) (p : ι -> P) : s.affineCombination k p w in 
affineSpan k (Set.range p)
参数：h : ∑ i in s, w i = 1；p : ι -> P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `affineSpan_eq_top_iff_nonempty_of_subsingleton`：affineSpan_eq_top_iff_no
nempty_of_subsingleton [Subsingleton P] : affineSpan k s = ⊤ ↔ s.Nonempty
· 使用定理 `AddTorsor.subsingleton_iff`：∀ (G : Type u_1) (P : Type u_2) [inst : AddG
roup G] [AddTorsor G P], Subsingleton G ↔ Subsingleton P
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `affineCombination_mem_affineSpan`：affineCombination_mem_affineSpan [Nont
rivial k] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 1) (p : ι -> P) : s.a
ffineCombination k p w…

--- 原说明 ---
An `affineCombination` with sum of weights 1 is in the
`affineSpan` of an indexed family, if the family is nonempty.
-/
theorem affineCombination_mem_affineSpan_of_nonempty [Nonempty ι] {s : Finset ι} {w : ι → k}
    (h : ∑ i ∈ s, w i = 1) (p : ι → P) :
    s.affineCombination k p w ∈ affineSpan k (Set.range p) := by
  rcases subsingleton_or_nontrivial k with hs | hn
  · have hnv := Module.subsingleton k V
    rw [AddTorsor.subsingleton_iff V P] at hnv
    rw [(affineSpan_eq_top_iff_nonempty_of_subsingleton k).2 (Set.range_nonempty p)]
    simp
  · exact affineCombination_mem_affineSpan h p

variable (k) in
/-- A vector is in the `vectorSpan` of an indexed family if and only
if it is a `weightedVSub` with sum of weights 0. -/
/-
**mem_vectorSpan_iff_eq_weightedVSub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_vectorSpan_iff_eq_weightedVSub {v : V} {p : ι -> P} : v in vectorSpan 
k (Set.range p) ↔ exists (s : Finset ι) (w : ι -> k), ∑ i in s, w i = 0 ∧ v = s.
weightedVSub p w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_eq_empty`：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = 
∅
· 使用定理 `vectorSpan_empty`：vectorSpan_empty : vectorSpan k (∅ : Set P) = (⊥ : Sub
module k V)
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.weightedVSub_empty`：weightedVSub_empty (w : ι -> k) (p : ι -> P) 
: (∅ : Finset ι).weightedVSub p w = (0 : V)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vectorSpan_range_eq_span_range_vsub_right`：vectorSpan_range_eq_span_rang
e_vsub_right (p : ι -> P) (i0 : ι) : vectorSpan k (Set.range p) = Submodule.span
 k (Set.range fun i : ι => p i …
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Finsupp.mem_span_image_iff_linearCombination`：mem_span_image_iff_linearC
ombination {s : Set α} {x : M} : x in span R (v '' s) ↔ exists l in supported R 
R s, linearCombination R v l = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Finset.sum_update_of_mem`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCom
mMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι},   i ∈ s → ∀ (f : ι →
 M) (b : M), ∑…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.sum_insert_of_eq_zero_if_notMem`：∀ {ι : Type u_1} {M : Type u_4} 
{s : Finset ι} {a : ι} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableE
q ι],   (a ∉ s → f a = 0) → …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
A vector is in the `vectorSpan` of an indexed family if and only
if it is a `weightedVSub` with sum of weights 0.
-/
theorem mem_vectorSpan_iff_eq_weightedVSub {v : V} {p : ι → P} :
    v ∈ vectorSpan k (Set.range p) ↔
      ∃ (s : Finset ι) (w : ι → k), ∑ i ∈ s, w i = 0 ∧ v = s.weightedVSub p w := by
  classical
    constructor
    · rcases isEmpty_or_nonempty ι with (hι | ⟨⟨i0⟩⟩)
      swap
      · rw [vectorSpan_range_eq_span_range_vsub_right k p i0, ← Set.image_univ,
          Finsupp.mem_span_image_iff_linearCombination]
        rintro ⟨l, _, hv⟩
        use insert i0 l.support
        set w :=
          (l : ι → k) - Function.update (Function.const ι 0 : ι → k) i0 (∑ i ∈ l.support, l i) with
          hwdef
        use w
        have hw : ∑ i ∈ insert i0 l.support, w i = 0 := by
          rw [hwdef]
          simp_rw [Pi.sub_apply, Finset.sum_sub_distrib,
            Finset.sum_update_of_mem (Finset.mem_insert_self _ _),
            Finset.sum_insert_of_eq_zero_if_notMem Finsupp.notMem_support_iff.1]
          simp only [Function.const_apply, Finset.sum_const_zero, add_zero, sub_self]
        use hw
        have hz : w i0 • (p i0 -ᵥ p i0 : V) = 0 := (vsub_self (p i0)).symm ▸ smul_zero _
        change (fun i => w i • (p i -ᵥ p i0 : V)) i0 = 0 at hz
        rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w p hw (p i0),
          Finset.weightedVSubOfPoint_apply, ← hv, Finsupp.linearCombination_apply,
          @Finset.sum_insert_zero _ _ l.support i0 _ _ _ hz]
        change (∑ i ∈ l.support, l i • _) = _
        congr with i
        by_cases h : i = i0
        · simp [h]
        · simp [hwdef, h]
      · rw [Set.range_eq_empty, vectorSpan_empty, Submodule.mem_bot]
        rintro rfl
        use ∅
        simp
    · rintro ⟨s, w, hw, rfl⟩
      exact weightedVSub_mem_vectorSpan hw p

/-- A point in the `affineSpan` of an indexed family is an
`affineCombination` with sum of weights 1. See also
`eq_affineCombination_of_mem_affineSpan_of_fintype`. -/
/-
**eq_affineCombination_of_mem_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_affineCombination_of_mem_affineSpan {p1 : P} {p : ι -> P} (h : p1 in af
fineSpan k (Set.range p)) : exists (s : Finset ι) (w : ι -> k), ∑ i in s, w i = 
1 ∧ p1 = s.affineCombination k p w
参数：h : p1 in affineSpan k (Set.range p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_nonempty_iff_nonempty`：range_nonempty_iff_nonempty : (range f)
.Nonempty ↔ Nonempty ι
· 使用定理 `affineSpan_nonempty`：affineSpan_nonempty : (affineSpan k s : Set P).None
mpty ↔ s.Nonempty
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `mem_vectorSpan_iff_eq_weightedVSub`：mem_vectorSpan_iff_eq_weightedVSub {
v : V} {p : ι -> P} : v in vectorSpan k (Set.range p) ↔ exists (s : Finset ι) (w
 : ι -> k), ∑ i in s, w …
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_indicator_subset`：∀ {ι : Type u_1} {β : Type u_4} [inst : Add
CommMonoid β] (f : ι → β) {s t : Finset ι},   s ⊆ t → ∑ i ∈ t, (↑s).indicator f 
i = ∑ i ∈ s, f i
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `Finset.weightedVSub_indicator_subset`：weightedVSub_indicator_subset (w :
 ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι} (h : s₁ subseteq s₂) : s₁.weightedVSub 
p w = s₂.weightedVSub p (S…
· 使用定理 `Finset.sum_update_of_mem`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCom
mMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι},   i ∈ s → ∀ (f : ι →
 M) (b : M), ∑…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.affineCombination_of_eq_one_of_eq_zero`：affineCombination_of_eq_o
ne_of_eq_zero (w : ι -> k) (p : ι -> P) {i : ι} (his : i in s) (hwi : w i = 1) (
hw0 : forall i2 in s, i2 != i -> w …
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finset.weightedVSub_vadd_affineCombination`：weightedVSub_vadd_affineComb
ination (w₁ w₂ : ι -> k) (p : ι -> P) : s.weightedVSub p w₁ +ᵥ s.affineCombinati
on k p w₂ = s.affineCombination …
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁

--- 原说明 ---
A point in the `affineSpan` of an indexed family is an
`affineCombination` with sum of weights 1. See also
`eq_affineCombination_of_mem_affineSpan_of_fintype`.
-/
theorem eq_affineCombination_of_mem_affineSpan {p1 : P} {p : ι → P}
    (h : p1 ∈ affineSpan k (Set.range p)) :
    ∃ (s : Finset ι) (w : ι → k), ∑ i ∈ s, w i = 1 ∧ p1 = s.affineCombination k p w := by
  classical
    have hn : (affineSpan k (Set.range p) : Set P).Nonempty := ⟨p1, h⟩
    rw [affineSpan_nonempty, Set.range_nonempty_iff_nonempty] at hn
    obtain ⟨i0⟩ := hn
    have h0 : p i0 ∈ affineSpan k (Set.range p) := mem_affineSpan k (Set.mem_range_self i0)
    have hd : p1 -ᵥ p i0 ∈ (affineSpan k (Set.range p)).direction :=
      AffineSubspace.vsub_mem_direction h h0
    rw [direction_affineSpan, mem_vectorSpan_iff_eq_weightedVSub] at hd
    rcases hd with ⟨s, w, h, hs⟩
    let s' := insert i0 s
    let w' := Set.indicator (↑s) w
    have h' : ∑ i ∈ s', w' i = 0 := by
      rw [← h, Finset.sum_indicator_subset _ (Finset.subset_insert i0 s)]
    have hs' : s'.weightedVSub p w' = p1 -ᵥ p i0 := by
      rw [hs]
      exact (Finset.weightedVSub_indicator_subset _ _ (Finset.subset_insert i0 s)).symm
    let w0 : ι → k := Function.update (Function.const ι 0) i0 1
    have hw0 : ∑ i ∈ s', w0 i = 1 := by
      rw [Finset.sum_update_of_mem (Finset.mem_insert_self _ _)]
      simp only [Function.const_apply, Finset.sum_const_zero,
        add_zero]
    have hw0s : s'.affineCombination k p w0 = p i0 :=
      s'.affineCombination_of_eq_one_of_eq_zero w0 p (Finset.mem_insert_self _ _)
        (Function.update_self ..) fun _ _ hne => Function.update_of_ne hne _ _
    refine ⟨s', w0 + w', ?_, ?_⟩
    · simp [Pi.add_apply, Finset.sum_add_distrib, hw0, h']
    · rw [add_comm, ← Finset.weightedVSub_vadd_affineCombination, hw0s, hs', vsub_vadd]
/-
**eq_affineCombination_of_mem_affineSpan_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：eq_affineCombination_of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p 
: ι -> P} (h : p1 in affineSpan k (Set.range p)) : exists w : ι -> k, ∑ i, w i =
 1 ∧ p1 = Finset.univ.affineCombination k p w
参数：h : p1 in affineSpan k (Set.range p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_affineCombination_of_mem_affineSpan`：eq_affineCombination_of_mem_affi
neSpan {p1 : P} {p : ι -> P} (h : p1 in affineSpan k (Set.range p)) : exists (s 
: Finset ι) (w : ι -> k), ∑ …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.sum_extend_by_zero`：∀ {α : Type u_1} {ι : Type u_4} [inst : Deci
dableEq ι] [inst_1 : Fintype ι] [inst_2 : AddCommMonoid α] (s : Finset ι)   (f :
 ι → α), (∑ i, i…
· 使用定理 `Finset.affineCombination_indicator_subset`：affineCombination_indicator_s
ubset (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι} (h : s₁ subseteq s₂) : s₁.aff
ineCombination k p w = s₂.affin…
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
-/
theorem eq_affineCombination_of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι → P}
    (h : p1 ∈ affineSpan k (Set.range p)) :
    ∃ w : ι → k, ∑ i, w i = 1 ∧ p1 = Finset.univ.affineCombination k p w := by
  classical
    obtain ⟨s, w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan h
    refine
      ⟨(s : Set ι).indicator w, ?_, Finset.affineCombination_indicator_subset w p s.subset_univ⟩
    simp only [Finset.mem_coe, Set.indicator_apply, ← hw]
    rw [Fintype.sum_extend_by_zero s w]

/-- A point in the `affineSpan` of a subset of an indexed family is an
`affineCombination` with sum of weights 1, using only points in the given subset. -/
/-
**eq_affineCombination_of_mem_affineSpan_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_affineCombination_of_mem_affineSpan_image {p₁ : P} {p : ι -> P} {s : Se
t ι} (h : p₁ in affineSpan k (p '' s)) : exists (fs : Finset ι) (w : ι -> k), ↑f
s subseteq s ∧ ∑ i in fs, w i = 1 ∧ p₁ = fs.affineCombination k p w
参数：h : p₁ in affineSpan k (p '' s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_affineCombination_of_mem_affineSpan`：eq_affineCombination_of_mem_affi
neSpan {p1 : P} {p : ι -> P} (h : p1 in affineSpan k (Set.range p)) : exists (s 
: Finset ι) (w : ι -> k), ∑ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.affineCombination_map`：affineCombination_map (e : ι₂ ↪ ι) (w : ι 
-> k) (p : ι -> P) : (s₂.map e).affineCombination k p w = s₂.affineCombination k
 (p ∘ e) (w ∘ e)
· 使用定理 `Finset.affineCombination_congr`：affineCombination_congr {w₁ w₂ : ι -> k}
 (hw : forall i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P} (hp : forall i in s, p₁ i = 
p₂ i) : s.affineComb…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A point in the `affineSpan` of a subset of an indexed family is an
`affineCombination` with sum of weights 1, using only points in the given subset
.
-/
lemma eq_affineCombination_of_mem_affineSpan_image {p₁ : P} {p : ι → P} {s : Set ι}
    (h : p₁ ∈ affineSpan k (p '' s)) :
    ∃ (fs : Finset ι) (w : ι → k), ↑fs ⊆ s ∧ ∑ i ∈ fs, w i = 1 ∧
      p₁ = fs.affineCombination k p w := by
  classical
  rw [Set.image_eq_range] at h
  obtain ⟨fs', w', hw', rfl⟩ := eq_affineCombination_of_mem_affineSpan h
  refine ⟨fs'.map (Function.Embedding.subtype _), fun i ↦ if hi : i ∈ s then w' ⟨i, hi⟩ else 0,
    (by simp), (by simp [hw']), ?_⟩
  simp only [Finset.affineCombination_map, Function.Embedding.coe_subtype]
  exact fs'.affineCombination_congr (by simp) (by simp)
/-
**affineCombination_mem_affineSpan_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：affineCombination_mem_affineSpan_image [Nontrivial k] {s : Finset ι} {w : 
ι -> k} (h : ∑ i in s, w i = 1) {s' : Set ι} (hs' : forall i in s, i ∉ s' -> w i
 = 0) (p : ι -> P) : s.affineCombination k p w in affineSpan k (p '' s')
参数：h : ∑ i in s, w i = 1；hs' : forall i in s, i ∉ s' -> w i = 0；p : ι -> P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_sdiff`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   s₁ ⊆ s₂ → ∑ x ∈ s₂
 \ s₁,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `right_eq_add`：∀ {M : Type u_4} [inst : AddMonoid M] [IsRightCancelAdd M]
 {a b : M}, b = a + b ↔ a = 0
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.affineCombination_subtype_eq_filter`：affineCombination_subtype_eq
_filter (w : ι -> k) (p : ι -> P) (pred : ι -> Prop) [DecidablePred pred] : ((s.
subtype pred).affineCombination …
· 使用定理 `Finset.affineCombination_indicator_subset`：affineCombination_indicator_s
ubset (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι} (h : s₁ subseteq s₂) : s₁.aff
ineCombination k p w = s₂.affin…
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `Finset.affineCombination_congr`：affineCombination_congr {w₁ w₂ : ι -> k}
 (hw : forall i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P} (hp : forall i in s, p₁ i = 
p₂ i) : s.affineComb…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `affineCombination_mem_affineSpan`：affineCombination_mem_affineSpan [Nont
rivial k] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 1) (p : ι -> P) : s.a
ffineCombination k p w…
· 使用定理 `Finset.sum_subtype_eq_sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : F
inset ι} [inst : AddCommMonoid M] (f : ι → M) {p : ι → Prop}   [inst_1 : Decidab
lePred p], ∑ x ∈ Finse…
-/
lemma affineCombination_mem_affineSpan_image [Nontrivial k] {s : Finset ι} {w : ι → k}
    (h : ∑ i ∈ s, w i = 1) {s' : Set ι} (hs' : ∀ i ∈ s, i ∉ s' → w i = 0) (p : ι → P) :
    s.affineCombination k p w ∈ affineSpan k (p '' s') := by
  classical
  rw [Set.image_eq_range]
  let w' : s' → k := fun i ↦ w i
  have h' : ∑ i ∈ s with i ∈ s', w i = 1 := by
    rw [← h, ← Finset.sum_sdiff (s₁ := {x ∈ s | x ∈ s'}) (s₂ := s) (by simp), right_eq_add]
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_filter, not_and] at hi
    exact hs' i hi.1 (hi.2 hi.1)
  rw [← Finset.sum_subtype_eq_sum_filter] at h'
  convert! affineCombination_mem_affineSpan h' (fun x ↦ p x)
  rw [Finset.affineCombination_subtype_eq_filter, Finset.affineCombination_indicator_subset w p
    (Finset.filter_subset _ _)]
  refine Finset.affineCombination_congr _ (fun i hi ↦ ?_) (fun _ _ ↦ rfl)
  simp_all [Set.indicator_apply]

variable (k V)

/-- A point is in the `affineSpan` of an indexed family if and only
if it is an `affineCombination` with sum of weights 1, provided the
underlying ring is nontrivial. -/
/-
**mem_affineSpan_iff_eq_affineCombination** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_affineSpan_iff_eq_affineCombination [Nontrivial k] {p1 : P} {p : ι -> 
P} : p1 in affineSpan k (Set.range p) ↔ exists (s : Finset ι) (w : ι -> k), ∑ i 
in s, w i = 1 ∧ p1 = s.affineCombination k p w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_affineCombination_of_mem_affineSpan`：eq_affineCombination_of_mem_affi
neSpan {p1 : P} {p : ι -> P} (h : p1 in affineSpan k (Set.range p)) : exists (s 
: Finset ι) (w : ι -> k), ∑ …
· 使用定理 `affineCombination_mem_affineSpan`：affineCombination_mem_affineSpan [Nont
rivial k] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 1) (p : ι -> P) : s.a
ffineCombination k p w…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A point is in the `affineSpan` of an indexed family if and only
if it is an `affineCombination` with sum of weights 1, provided the
underlying ring is nontrivial.
-/
theorem mem_affineSpan_iff_eq_affineCombination [Nontrivial k] {p1 : P} {p : ι → P} :
    p1 ∈ affineSpan k (Set.range p) ↔
      ∃ (s : Finset ι) (w : ι → k), ∑ i ∈ s, w i = 1 ∧ p1 = s.affineCombination k p w := by
  constructor
  · exact eq_affineCombination_of_mem_affineSpan
  · rintro ⟨s, w, hw, rfl⟩
    exact affineCombination_mem_affineSpan hw p

/-- Given a family of points together with a chosen base point in that family, membership of the
affine span of this family corresponds to an identity in terms of `weightedVSubOfPoint`, with
weights that are not required to sum to 1. -/
/-
**mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd [Nontrivial k] (p : ι -> P)
 (j : ι) (q : P) : q in affineSpan k (Set.range p) ↔ exists (s : Finset ι) (w : 
ι -> k), q = s.weightedVSubOfPoint p (p j) w +ᵥ p j
参数：p : ι -> P；j : ι；q : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_affineCombination_of_mem_affineSpan`：eq_affineCombination_of_mem_affi
neSpan {p1 : P} {p : ι -> P} (h : p1 in affineSpan k (Set.range p)) : exists (s 
: Finset ι) (w : ι -> k), ∑ …
· 使用定理 `Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one`：affi
neCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι -> k) (p : ι -> P
) (h : ∑ i in s, w i = 1) (b : P) : s.affineCombination …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `Finset.sum_update_of_mem`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCom
mMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι},   i ∈ s → ∀ (f : ι →
 M) (b : M), ∑…
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.sum_update_of_notMem`：∀ {ι : Type u_1} {M : Type u_3} [inst : Add
CommMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι},   i ∉ s → ∀ (f : 
ι → M) (b : M), ∑…
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.weightedVSubOfPoint_eq_of_weights_eq`：weightedVSubOfPoint_eq_of_w
eights_eq (p : ι -> P) (j : ι) (w₁ w₂ : ι -> k) (hw : forall i, i != j -> w₁ i =
 w₂ i) : s.weightedVSubOfPoint p …
· 使用定理 `Finset.weightedVSubOfPoint_insert`：weightedVSubOfPoint_insert [Decidable
Eq ι] (w : ι -> k) (p : ι -> P) (i : ι) : (insert i s).weightedVSubOfPoint p (p 
i) w = s.weightedVSubOf…
· 使用定理 `affineCombination_mem_affineSpan`：affineCombination_mem_affineSpan [Nont
rivial k] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 1) (p : ι -> P) : s.a
ffineCombination k p w…

--- 原说明 ---
Given a family of points together with a chosen base point in that family, membe
rship of the
affine span of this family corresponds to an identity in terms of `weightedVSubO
fPoint`, with
weights that are not required to sum to 1.
-/
theorem mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd [Nontrivial k] (p : ι → P) (j : ι) (q : P) :
    q ∈ affineSpan k (Set.range p) ↔
      ∃ (s : Finset ι) (w : ι → k), q = s.weightedVSubOfPoint p (p j) w +ᵥ p j := by
  constructor
  · intro hq
    obtain ⟨s, w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan hq
    exact ⟨s, w, s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw (p j)⟩
  · rintro ⟨s, w, rfl⟩
    classical
      let w' : ι → k := Function.update w j (1 - (s \ {j}).sum w)
      have h₁ : (insert j s).sum w' = 1 := by
        by_cases hj : j ∈ s
        · simp [w', Finset.sum_update_of_mem hj, Finset.insert_eq_of_mem hj]
        · simp_rw [w', Finset.sum_insert hj, Finset.sum_update_of_notMem hj, Function.update_self,
            ← Finset.erase_eq, Finset.erase_eq_of_notMem hj, sub_add_cancel]
      have hww : ∀ i, i ≠ j → w i = w' i := by
        intro i hij
        simp [w', hij]
      rw [s.weightedVSubOfPoint_eq_of_weights_eq p j w w' hww, ←
        s.weightedVSubOfPoint_insert w' p j, ←
        (insert j s).affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w' p h₁ (p j)]
      exact affineCombination_mem_affineSpan h₁ p

variable {k V}

set_option backward.isDefEq.respectTransparency false in
/-- Given a set of points, together with a chosen base point in this set, if we affinely transport
all other members of the set along the line joining them to this base point, the affine span is
unchanged. -/
/-
**affineSpan_eq_affineSpan_lineMap_units** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_eq_affineSpan_lineMap_units [Nontrivial k] {s : Set P} {p : P} 
(hp : p in s) (w : s -> Units k) : affineSpan k (Set.range fun q : s => AffineMa
p.lineMap p ↑q (w q : k)) = affineSpan k s
参数：hp : p in s；w : s -> Units k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd`：mem_affineSpan_iff_eq_we
ightedVSubOfPoint_vadd [Nontrivial k] (p : ι -> P) (j : ι) (q : P) : q in affine
Span k (Set.range p) ↔ exists (s : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineMap.lineMap_same`：lineMap_same (p : P1) : lineMap p p = const k k 
p
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AffineMap.lineMap_vsub_left`：lineMap_vsub_left (p₀ p₁ : P1) (c : k) : li
neMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.inv_mul_cancel_right`：inv_mul_cancel_right (a : α) (b : αˣ) : a * 
↑b⁻¹ * b = a

--- 原说明 ---
Given a set of points, together with a chosen base point in this set, if we affi
nely transport
all other members of the set along the line joining them to this base point, the
 affine span is
unchanged.
-/
theorem affineSpan_eq_affineSpan_lineMap_units [Nontrivial k] {s : Set P} {p : P} (hp : p ∈ s)
    (w : s → Units k) :
    affineSpan k (Set.range fun q : s => AffineMap.lineMap p ↑q (w q : k)) = affineSpan k s := by
  have : s = Set.range ((↑) : s → P) := by simp
  conv_rhs =>
    rw [this]
  apply le_antisymm
    <;> intro q hq
    <;> rw [mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd k V _ (⟨p, hp⟩ : s) q] at hq ⊢
    <;> obtain ⟨t, μ, rfl⟩ := hq
    <;> use t
    <;> [use fun x => μ x * ↑(w x); use fun x => μ x * ↑(w x)⁻¹]
    <;> simp [smul_smul]

end AffineSpace'

namespace AffineMap

variable {k : Type*} {V : Type*} (P : Type*) [CommRing k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*} (s : Finset ι)

-- TODO: define `affineMap.proj`, `affineMap.fst`, `affineMap.snd`
/-- A weighted sum, as an affine map on the points involved. -/
/-
**AffineMap.weightedVSubOfPoint** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：weightedVSubOfPoint (w : ι -> k) : (ι -> P) × P ->ᵃ[k] V where toFun p
参数：w : ι -> k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weighted sum, as an affine map on the points involved.
-/
def weightedVSubOfPoint (w : ι → k) : (ι → P) × P →ᵃ[k] V where
  toFun p := s.weightedVSubOfPoint p.fst p.snd w
  linear := ∑ i ∈ s, w i • ((LinearMap.proj i).comp (LinearMap.fst _ _ _) - LinearMap.snd _ _ _)
  map_vadd' := by
    rintro ⟨p, b⟩ ⟨v, b'⟩
    simp [LinearMap.sum_apply, Finset.weightedVSubOfPoint, vsub_vadd_eq_vsub_sub,
     vadd_vsub_assoc, ← sub_add_eq_add_sub, smul_add, Finset.sum_add_distrib]

end AffineMap

