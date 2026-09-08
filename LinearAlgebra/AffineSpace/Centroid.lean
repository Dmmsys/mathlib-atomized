/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Combination

/-!
# Centroid of a Finite Set of Points in Affine Space

This file defines the centroid of a finite set of points in an affine space over a division
ring.

## Main definitions

* `centroidWeights`: A constant weight function assigning to each index in a `Finset` the same
  weight, equal to the reciprocal of the number of elements.

* `centroid`: the centroid of a `Finset` of points, defined as the affine combination using
  `centroidWeights`.

-/

@[expose] public section

assert_not_exists Affine.Simplex

noncomputable section

open Affine

namespace Finset

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

/-- The weights for the centroid of some points. -/
/-
**Finset.centroidWeights** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：centroidWeights : ι -> k
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weights for the centroid of some points.
-/
def centroidWeights : ι → k :=
  Function.const ι (#s : k)⁻¹

/-- `centroidWeights` at any point. -/
@[simp]
/-
**Finset.centroidWeights_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：centroidWeights_apply (i : ι) : s.centroidWeights k i = (#s : k)⁻¹
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`centroidWeights` at any point.
-/
theorem centroidWeights_apply (i : ι) : s.centroidWeights k i = (#s : k)⁻¹ :=
  rfl

/-- `centroidWeights` equals a constant function. -/
/-
**Finset.centroidWeights_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：centroidWeights_eq_const : s.centroidWeights k = Function.const ι (#s : k)
⁻¹
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`centroidWeights` equals a constant function.
-/
theorem centroidWeights_eq_const : s.centroidWeights k = Function.const ι (#s : k)⁻¹ :=
  rfl

variable {k} in
/-- The weights in the centroid sum to 1, if the number of points,
converted to `k`, is not zero. -/
/-
**Finset.sum_centroidWeights_eq_one_of_cast_card_ne_zero** 是 Mathlib 中的一个定理，位于命名
空间 `Finset`。
形式化陈述：sum_centroidWeights_eq_one_of_cast_card_ne_zero (h : (#s : k) != 0) : ∑ i 
in s, s.centroidWeights k i = 1
参数：h : (#s : k) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The weights in the centroid sum to 1, if the number of points,
converted to `k`, is not zero.
-/
theorem sum_centroidWeights_eq_one_of_cast_card_ne_zero (h : (#s : k) ≠ 0) :
    ∑ i ∈ s, s.centroidWeights k i = 1 := by simp [h]

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the number of points is not zero. -/
/-
**Finset.sum_centroidWeights_eq_one_of_card_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `F
inset`。
形式化陈述：sum_centroidWeights_eq_one_of_card_ne_zero [CharZero k] (h : #s != 0) : ∑ 
i in s, s.centroidWeights k i = 1
参数：h : #s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the characteristic zero case, the weights in the centroid sum
to 1 if the number of points is not zero.
-/
theorem sum_centroidWeights_eq_one_of_card_ne_zero [CharZero k] (h : #s ≠ 0) :
    ∑ i ∈ s, s.centroidWeights k i = 1 := by
  simp_all

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the set is nonempty. -/
/-
**Finset.sum_centroidWeights_eq_one_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finse
t`。
形式化陈述：sum_centroidWeights_eq_one_of_nonempty [CharZero k] (h : s.Nonempty) : ∑ i
 in s, s.centroidWeights k i = 1
参数：h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_card_ne_zero`：sum_centroidWeights_e
q_one_of_card_ne_zero [CharZero k] (h : #s != 0) : ∑ i in s, s.centroidWeights k
 i = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y

--- 原说明 ---
In the characteristic zero case, the weights in the centroid sum
to 1 if the set is nonempty.
-/
theorem sum_centroidWeights_eq_one_of_nonempty [CharZero k] (h : s.Nonempty) :
    ∑ i ∈ s, s.centroidWeights k i = 1 :=
  s.sum_centroidWeights_eq_one_of_card_ne_zero k (ne_of_gt (card_pos.2 h))

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the number of points is `n + 1`. -/
/-
**Finset.sum_centroidWeights_eq_one_of_card_eq_add_one** 是 Mathlib 中的一个定理，位于命名空间
 `Finset`。
形式化陈述：sum_centroidWeights_eq_one_of_card_eq_add_one [CharZero k] {n : Nat} (h : 
#s = n + 1) : ∑ i in s, s.centroidWeights k i = 1
参数：h : #s = n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_card_ne_zero`：sum_centroidWeights_e
q_one_of_card_ne_zero [CharZero k] (h : #s != 0) : ∑ i in s, s.centroidWeights k
 i = 1
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
In the characteristic zero case, the weights in the centroid sum
to 1 if the number of points is `n + 1`.
-/
theorem sum_centroidWeights_eq_one_of_card_eq_add_one [CharZero k] {n : ℕ} (h : #s = n + 1) :
    ∑ i ∈ s, s.centroidWeights k i = 1 :=
  s.sum_centroidWeights_eq_one_of_card_ne_zero k (h.symm ▸ Nat.succ_ne_zero n)

/-- The centroid of some points.  Although defined for any `s`, this
is intended to be used in the case where the number of points,
converted to `k`, is not zero. -/
/-
**Finset.centroid** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：centroid (p : ι -> P) : P
参数：p : ι -> P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The centroid of some points.  Although defined for any `s`, this
is intended to be used in the case where the number of points,
converted to `k`, is not zero.
-/
def centroid (p : ι → P) : P :=
  s.affineCombination k p (s.centroidWeights k)

/-- The definition of the centroid. -/
/-
**Finset.centroid_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：centroid_def (p : ι -> P) : s.centroid k p = s.affineCombination k p (s.ce
ntroidWeights k)
参数：p : ι -> P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definition of the centroid.
-/
theorem centroid_def (p : ι → P) : s.centroid k p = s.affineCombination k p (s.centroidWeights k) :=
  rfl
/-
**Finset.centroid_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：centroid_univ (s : Finset P) : univ.centroid k ((↑) : s -> P) = s.centroid
 k id
参数：s : Finset P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.centroid.eq_1`：∀ (k : Type u_1) {V : Type u_2} {P : Type u_3} [in
st : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module k V] [i
nst_3 : Ad…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.attach_affineCombination_coe`：attach_affineCombination_coe (s : F
inset P) (w : P -> k) : s.attach.affineCombination k ((↑) : s -> P) (w ∘ (↑)) = 
s.affineCombination k id …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem centroid_univ (s : Finset P) : univ.centroid k ((↑) : s → P) = s.centroid k id := by
  rw [centroid, centroid, ← s.attach_affineCombination_coe]
  congr
  ext
  simp

/-- The centroid of a single point. -/
@[simp]
/-
**Finset.centroid_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：centroid_singleton (p : ι -> P) (i : ι) : ({i} : Finset ι).centroid k p = 
p i
参数：p : ι -> P；i : ι。
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
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The centroid of a single point.
-/
theorem centroid_singleton (p : ι → P) (i : ι) : ({i} : Finset ι).centroid k p = p i := by
  simp [centroid_def, affineCombination_apply]

/-- The centroid of two points, expressed directly as adding a vector
to a point. -/
/-
**Finset.centroid_pair** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：centroid_pair [DecidableEq ι] [Invertible (2 : k)] (p : ι -> P) (i₁ i₂ : ι
) : ({i₁, i₂} : Finset ι).centroid k p = (2⁻¹ : k) • (p i₂ -ᵥ p i₁) +ᵥ p i₁
参数：2 : k；p : ι -> P；i₁ i₂ : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.centroid_singleton`：centroid_singleton (p : ι -> P) (i : ι) : ({i
} : Finset ι).centroid k p = p i
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.notMem_singleton`：notMem_singleton {a b : α} : a ∉ ({b} : Finset 
α) ↔ a != b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Finset.centroid_def`：centroid_def (p : ι -> P) : s.centroid k p = s.affi
neCombination k p (s.centroidWeights k)
· 使用定理 `Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one`：affi
neCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι -> k) (p : ι -> P
) (h : ∑ i in s, w i = 1) (b : P) : s.affineCombination …
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_cast_card_ne_zero`：sum_centroidWeig
hts_eq_one_of_cast_card_ne_zero (h : (#s : k) != 0) : ∑ i in s, s.centroidWeight
s k i = 1
· 使用定理 `Finset.weightedVSubOfPoint_insert`：weightedVSubOfPoint_insert [Decidable
Eq ι] (w : ι -> k) (p : ι -> P) (i : ι) : (insert i s).weightedVSubOfPoint p (p 
i) w = s.weightedVSubOf…
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a

--- 原说明 ---
The centroid of two points, expressed directly as adding a vector
to a point.
-/
theorem centroid_pair [DecidableEq ι] [Invertible (2 : k)] (p : ι → P) (i₁ i₂ : ι) :
    ({i₁, i₂} : Finset ι).centroid k p = (2⁻¹ : k) • (p i₂ -ᵥ p i₁) +ᵥ p i₁ := by
  by_cases h : i₁ = i₂
  · simp [h]
  · have hc : (#{i₁, i₂} : k) ≠ 0 := by
      rw [card_insert_of_notMem (notMem_singleton.2 h), card_singleton]
      simpa using Invertible.ne_zero _
    rw [centroid_def,
      affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _
        (sum_centroidWeights_eq_one_of_cast_card_ne_zero _ hc) (p i₁)]
    simp [h, one_add_one_eq_two]

/-- The centroid of two points indexed by `Fin 2`, expressed directly
as adding a vector to the first point. -/
/-
**Finset.centroid_pair_fin** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：centroid_pair_fin [Invertible (2 : k)] (p : Fin 2 -> P) : univ.centroid k 
p = (2⁻¹ : k) • (p 1 -ᵥ p 0) +ᵥ p 0
参数：2 : k；p : Fin 2 -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.univ_fin2`：Finset.univ_fin2 : (univ : Finset (Fin 2)) = {0, 1}
· 使用定理 `Finset.centroid_pair`：centroid_pair [DecidableEq ι] [Invertible (2 : k)]
 (p : ι -> P) (i₁ i₂ : ι) : ({i₁, i₂} : Finset ι).centroid k p = (2⁻¹ : k) • (p 
i₂ -ᵥ p i₁…

--- 原说明 ---
The centroid of two points indexed by `Fin 2`, expressed directly
as adding a vector to the first point.
-/
theorem centroid_pair_fin [Invertible (2 : k)] (p : Fin 2 → P) :
    univ.centroid k p = (2⁻¹ : k) • (p 1 -ᵥ p 0) +ᵥ p 0 := by
  rw [univ_fin2]
  convert! centroid_pair k p 0 1

/-- A centroid, over the image of an embedding, equals a centroid with
the same points and weights over the original `Finset`. -/
/-
**Finset.centroid_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：centroid_map (e : ι₂ ↪ ι) (p : ι -> P) : (s₂.map e).centroid k p = s₂.cent
roid k (p ∘ e)
参数：e : ι₂ ↪ ι；p : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.affineCombination_map`：affineCombination_map (e : ι₂ ↪ ι) (w : ι 
-> k) (p : ι -> P) : (s₂.map e).affineCombination k p w = s₂.affineCombination k
 (p ∘ e) (w ∘ e)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A centroid, over the image of an embedding, equals a centroid with
the same points and weights over the original `Finset`.
-/
theorem centroid_map (e : ι₂ ↪ ι) (p : ι → P) :
    (s₂.map e).centroid k p = s₂.centroid k (p ∘ e) := by
  simp [centroid_def, affineCombination_map, centroidWeights]

/-- `centroidWeights` gives the weights for the centroid as a
constant function, which is suitable when summing over the points
whose centroid is being taken.  This function gives the weights in a
form suitable for summing over a larger set of points, as an indicator
function that is zero outside the set whose centroid is being taken.
In the case of a `Fintype`, the sum may be over `univ`. -/
/-
**Finset.centroidWeightsIndicator** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：centroidWeightsIndicator : ι -> k
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`centroidWeights` gives the weights for the centroid as a
constant function, which is suitable when summing over the points
whose centroid is being taken.  This function gives the weights in a
form suitable for summing over a larger set of points, as an indicator
function that is zero outside the set whose centroid is being taken.
In the case of a `Fintype`, the sum may be over `univ`.
-/
def centroidWeightsIndicator : ι → k :=
  Set.indicator (↑s) (s.centroidWeights k)

/-- The definition of `centroidWeightsIndicator`. -/
/-
**Finset.centroidWeightsIndicator_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：centroidWeightsIndicator_def : s.centroidWeightsIndicator k = Set.indicato
r (↑s) (s.centroidWeights k)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definition of `centroidWeightsIndicator`.
-/
theorem centroidWeightsIndicator_def :
    s.centroidWeightsIndicator k = Set.indicator (↑s) (s.centroidWeights k) :=
  rfl

/-- The sum of the weights for the centroid indexed by a `Fintype`. -/
/-
**Finset.sum_centroidWeightsIndicator** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_centroidWeightsIndicator [Fintype ι] : ∑ i, s.centroidWeightsIndicator
 k i = ∑ i in s, s.centroidWeights k i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_indicator_subset`：∀ {ι : Type u_1} {β : Type u_4} [inst : Add
CommMonoid β] (f : ι → β) {s t : Finset ι},   s ⊆ t → ∑ i ∈ t, (↑s).indicator f 
i = ∑ i ∈ s, f i
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ

--- 原说明 ---
The sum of the weights for the centroid indexed by a `Fintype`.
-/
theorem sum_centroidWeightsIndicator [Fintype ι] :
    ∑ i, s.centroidWeightsIndicator k i = ∑ i ∈ s, s.centroidWeights k i :=
  sum_indicator_subset _ (subset_univ _)

/-- In the characteristic zero case, the weights in the centroid
indexed by a `Fintype` sum to 1 if the number of points is not
zero. -/
/-
**Finset.sum_centroidWeightsIndicator_eq_one_of_card_ne_zero** 是 Mathlib 中的一个定理，
位于命名空间 `Finset`。
形式化陈述：sum_centroidWeightsIndicator_eq_one_of_card_ne_zero [CharZero k] [Fintype 
ι] (h : #s != 0) : ∑ i, s.centroidWeightsIndicator k i = 1
参数：h : #s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_centroidWeightsIndicator`：sum_centroidWeightsIndicator [Finty
pe ι] : ∑ i, s.centroidWeightsIndicator k i = ∑ i in s, s.centroidWeights k i
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_card_ne_zero`：sum_centroidWeights_e
q_one_of_card_ne_zero [CharZero k] (h : #s != 0) : ∑ i in s, s.centroidWeights k
 i = 1

--- 原说明 ---
In the characteristic zero case, the weights in the centroid
indexed by a `Fintype` sum to 1 if the number of points is not
zero.
-/
theorem sum_centroidWeightsIndicator_eq_one_of_card_ne_zero [CharZero k] [Fintype ι]
    (h : #s ≠ 0) : ∑ i, s.centroidWeightsIndicator k i = 1 := by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_card_ne_zero k h

/-- In the characteristic zero case, the weights in the centroid
indexed by a `Fintype` sum to 1 if the set is nonempty. -/
/-
**Finset.sum_centroidWeightsIndicator_eq_one_of_nonempty** 是 Mathlib 中的一个定理，位于命名
空间 `Finset`。
形式化陈述：sum_centroidWeightsIndicator_eq_one_of_nonempty [CharZero k] [Fintype ι] (
h : s.Nonempty) : ∑ i, s.centroidWeightsIndicator k i = 1
参数：h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_centroidWeightsIndicator`：sum_centroidWeightsIndicator [Finty
pe ι] : ∑ i, s.centroidWeightsIndicator k i = ∑ i in s, s.centroidWeights k i
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_nonempty`：sum_centroidWeights_eq_on
e_of_nonempty [CharZero k] (h : s.Nonempty) : ∑ i in s, s.centroidWeights k i = 
1

--- 原说明 ---
In the characteristic zero case, the weights in the centroid
indexed by a `Fintype` sum to 1 if the set is nonempty.
-/
theorem sum_centroidWeightsIndicator_eq_one_of_nonempty [CharZero k] [Fintype ι] (h : s.Nonempty) :
    ∑ i, s.centroidWeightsIndicator k i = 1 := by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_nonempty k h

/-- In the characteristic zero case, the weights in the centroid
indexed by a `Fintype` sum to 1 if the number of points is `n + 1`. -/
/-
**Finset.sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one** 是 Mathlib 中的一个
定理，位于命名空间 `Finset`。
形式化陈述：sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one [CharZero k] [Finty
pe ι] {n : Nat} (h : #s = n + 1) : ∑ i, s.centroidWeightsIndicator k i = 1
参数：h : #s = n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_centroidWeightsIndicator`：sum_centroidWeightsIndicator [Finty
pe ι] : ∑ i, s.centroidWeightsIndicator k i = ∑ i in s, s.centroidWeights k i
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_card_eq_add_one`：sum_centroidWeight
s_eq_one_of_card_eq_add_one [CharZero k] {n : Nat} (h : #s = n + 1) : ∑ i in s, 
s.centroidWeights k i = 1

--- 原说明 ---
In the characteristic zero case, the weights in the centroid
indexed by a `Fintype` sum to 1 if the number of points is `n + 1`.
-/
theorem sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one [CharZero k] [Fintype ι] {n : ℕ}
    (h : #s = n + 1) : ∑ i, s.centroidWeightsIndicator k i = 1 := by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_card_eq_add_one k h

/-- The centroid as an affine combination over a `Fintype`. -/
/-
**Finset.centroid_eq_affineCombination_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：centroid_eq_affineCombination_fintype [Fintype ι] (p : ι -> P) : s.centroi
d k p = univ.affineCombination k p (s.centroidWeightsIndicator k)
参数：p : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.affineCombination_indicator_subset`：affineCombination_indicator_s
ubset (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι} (h : s₁ subseteq s₂) : s₁.aff
ineCombination k p w = s₂.affin…
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ

--- 原说明 ---
The centroid as an affine combination over a `Fintype`.
-/
theorem centroid_eq_affineCombination_fintype [Fintype ι] (p : ι → P) :
    s.centroid k p = univ.affineCombination k p (s.centroidWeightsIndicator k) :=
  affineCombination_indicator_subset _ _ (subset_univ _)

/-- An indexed family of points that is injective on the given
`Finset` has the same centroid as the image of that `Finset`.  This is
stated in terms of a set equal to the image to provide control of
definitional equality for the index type used for the centroid of the
image. -/
/-
**Finset.centroid_eq_centroid_image_of_inj_on** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：centroid_eq_centroid_image_of_inj_on {p : ι -> P} (hi : forall i in s, for
all j in s, p i = p j -> i = j) {ps : Set P} [Fintype ps] (hps : ps = p '' ↑s) :
 s.centroid k p = (univ : Finset ps).centroid k fun x => (x : P)
参数：hi : forall i in s, forall j in s, p i = p j -> i = j；hps : ps = p '' ↑s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.centroid_map`：centroid_map (e : ι₂ ↪ ι) (p : ι -> P) : (s₂.map e)
.centroid k p = s₂.centroid k (p ∘ e)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
An indexed family of points that is injective on the given
`Finset` has the same centroid as the image of that `Finset`.  This is
stated in terms of a set equal to the image to provide control of
definitional equality for the index type used for the centroid of the
image.
-/
theorem centroid_eq_centroid_image_of_inj_on {p : ι → P}
    (hi : ∀ i ∈ s, ∀ j ∈ s, p i = p j → i = j) {ps : Set P} [Fintype ps]
    (hps : ps = p '' ↑s) : s.centroid k p = (univ : Finset ps).centroid k fun x => (x : P) := by
  let f : p '' ↑s → ι := fun x => x.property.choose
  have hf : ∀ x, f x ∈ s ∧ p (f x) = x := fun x => x.property.choose_spec
  let f' : ps → ι := fun x => f ⟨x, hps ▸ x.property⟩
  have hf' : ∀ x, f' x ∈ s ∧ p (f' x) = x := fun x => hf ⟨x, hps ▸ x.property⟩
  have hf'i : Function.Injective f' := by
    intro x y h
    rw [Subtype.ext_iff, ← (hf' x).2, ← (hf' y).2, h]
  let f'e : ps ↪ ι := ⟨f', hf'i⟩
  have hu : Finset.univ.map f'e = s := by
    ext x
    rw [mem_map]
    constructor
    · rintro ⟨i, _, rfl⟩
      exact (hf' i).1
    · intro hx
      use ⟨p x, hps.symm ▸ Set.mem_image_of_mem _ hx⟩, mem_univ _
      refine hi _ (hf' _).1 _ hx ?_
      rw [(hf' _).2]
  rw [← hu, centroid_map]
  congr with x
  change p (f' x) = ↑x
  rw [(hf' x).2]

/-- Two indexed families of points that are injective on the given
`Finset`s and with the same points in the image of those `Finset`s
have the same centroid. -/
/-
**Finset.centroid_eq_of_inj_on_of_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：centroid_eq_of_inj_on_of_image_eq {p : ι -> P} (hi : forall i in s, forall
 j in s, p i = p j -> i = j) {p₂ : ι₂ -> P} (hi₂ : forall i in s₂, forall j in s
₂, p₂ i = p₂ j -> i = j) (he : p '' ↑s = p₂ '' ↑s₂) : s.centroid k p = s₂.centro
id k p₂
参数：hi : forall i in s, forall j in s, p i = p j -> i = j；hi₂ : forall i in s₂, f
orall j in s₂, p₂ i = p₂ j -> i = j；he : p '' ↑s = p₂ '' ↑s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.centroid_eq_centroid_image_of_inj_on`：centroid_eq_centroid_image_
of_inj_on {p : ι -> P} (hi : forall i in s, forall j in s, p i = p j -> i = j) {
ps : Set P} [Fintype ps] (hps : p…

--- 原说明 ---
Two indexed families of points that are injective on the given
`Finset`s and with the same points in the image of those `Finset`s
have the same centroid.
-/
theorem centroid_eq_of_inj_on_of_image_eq {p : ι → P}
    (hi : ∀ i ∈ s, ∀ j ∈ s, p i = p j → i = j) {p₂ : ι₂ → P}
    (hi₂ : ∀ i ∈ s₂, ∀ j ∈ s₂, p₂ i = p₂ j → i = j) (he : p '' ↑s = p₂ '' ↑s₂) :
    s.centroid k p = s₂.centroid k p₂ := by
  classical rw [s.centroid_eq_centroid_image_of_inj_on k hi rfl,
      s₂.centroid_eq_centroid_image_of_inj_on k hi₂ he]

/-- The centroid commutes with translation by a constant point.
Subtracting a fixed point `p₀` from the centroid is the same as taking the centroid of
the family translated by `-ᵥ p₀` -/
/-
**Finset.centroid_vsub_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：centroid_vsub_const [CharZero k] {p : ι -> P} {p₀ : P} (hs : s.Nonempty) :
 Finset.centroid k s p -ᵥ p₀ = Finset.centroid k s (fun i => p i -ᵥ p₀)
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_nonempty`：sum_centroidWeights_eq_on
e_of_nonempty [CharZero k] (h : s.Nonempty) : ∑ i in s, s.centroidWeights k i = 
1

--- 原说明 ---
The centroid commutes with translation by a constant point.
Subtracting a fixed point `p₀` from the centroid is the same as taking the centr
oid of
the family translated by `-ᵥ p₀`
-/
theorem centroid_vsub_const [CharZero k] {p : ι → P} {p₀ : P} (hs : s.Nonempty) :
    Finset.centroid k s p -ᵥ p₀ = Finset.centroid k s (fun i => p i -ᵥ p₀) := by
  have h := s.sum_centroidWeights_eq_one_of_nonempty k hs
  simp only [centroid_def]
  grind [sum_smul_vsub_const_eq_affineCombination_vsub, affineCombination_eq_linear_combination]

end Finset

section DivisionRing

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*}

open Set Finset

/-- The centroid lies in the affine span if the number of points,
converted to `k`, is not zero. -/
/-
**centroid_mem_affineSpan_of_cast_card_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：centroid_mem_affineSpan_of_cast_card_ne_zero {s : Finset ι} (p : ι -> P) (
h : (#s : k) != 0) : s.centroid k p in affineSpan k (range p)
参数：p : ι -> P；h : (#s : k) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineCombination_mem_affineSpan`：affineCombination_mem_affineSpan [Nont
rivial k] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 1) (p : ι -> P) : s.a
ffineCombination k p w…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_cast_card_ne_zero`：sum_centroidWeig
hts_eq_one_of_cast_card_ne_zero (h : (#s : k) != 0) : ∑ i in s, s.centroidWeight
s k i = 1

--- 原说明 ---
The centroid lies in the affine span if the number of points,
converted to `k`, is not zero.
-/
theorem centroid_mem_affineSpan_of_cast_card_ne_zero {s : Finset ι} (p : ι → P)
    (h : (#s : k) ≠ 0) : s.centroid k p ∈ affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_cast_card_ne_zero h) p

variable (k)

/-- In the characteristic zero case, the centroid lies in the affine
span if the number of points is not zero. -/
/-
**centroid_mem_affineSpan_of_card_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：centroid_mem_affineSpan_of_card_ne_zero [CharZero k] {s : Finset ι} (p : ι
 -> P) (h : #s != 0) : s.centroid k p in affineSpan k (range p)
参数：p : ι -> P；h : #s != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineCombination_mem_affineSpan`：affineCombination_mem_affineSpan [Nont
rivial k] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 1) (p : ι -> P) : s.a
ffineCombination k p w…
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_card_ne_zero`：sum_centroidWeights_e
q_one_of_card_ne_zero [CharZero k] (h : #s != 0) : ∑ i in s, s.centroidWeights k
 i = 1

--- 原说明 ---
In the characteristic zero case, the centroid lies in the affine
span if the number of points is not zero.
-/
theorem centroid_mem_affineSpan_of_card_ne_zero [CharZero k] {s : Finset ι} (p : ι → P)
    (h : #s ≠ 0) : s.centroid k p ∈ affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_card_ne_zero k h) p

/-- In the characteristic zero case, the centroid lies in the affine
span if the set is nonempty. -/
/-
**centroid_mem_affineSpan_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：centroid_mem_affineSpan_of_nonempty [CharZero k] {s : Finset ι} (p : ι -> 
P) (h : s.Nonempty) : s.centroid k p in affineSpan k (range p)
参数：p : ι -> P；h : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineCombination_mem_affineSpan`：affineCombination_mem_affineSpan [Nont
rivial k] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 1) (p : ι -> P) : s.a
ffineCombination k p w…
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_nonempty`：sum_centroidWeights_eq_on
e_of_nonempty [CharZero k] (h : s.Nonempty) : ∑ i in s, s.centroidWeights k i = 
1

--- 原说明 ---
In the characteristic zero case, the centroid lies in the affine
span if the set is nonempty.
-/
theorem centroid_mem_affineSpan_of_nonempty [CharZero k] {s : Finset ι} (p : ι → P)
    (h : s.Nonempty) : s.centroid k p ∈ affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_nonempty k h) p

/-- In the characteristic zero case, the centroid lies in the affine
span if the number of points is `n + 1`. -/
/-
**centroid_mem_affineSpan_of_card_eq_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：centroid_mem_affineSpan_of_card_eq_add_one [CharZero k] {s : Finset ι} (p 
: ι -> P) {n : Nat} (h : #s = n + 1) : s.centroid k p in affineSpan k (range p)
参数：p : ι -> P；h : #s = n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineCombination_mem_affineSpan`：affineCombination_mem_affineSpan [Nont
rivial k] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 1) (p : ι -> P) : s.a
ffineCombination k p w…
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_card_eq_add_one`：sum_centroidWeight
s_eq_one_of_card_eq_add_one [CharZero k] {n : Nat} (h : #s = n + 1) : ∑ i in s, 
s.centroidWeights k i = 1

--- 原说明 ---
In the characteristic zero case, the centroid lies in the affine
span if the number of points is `n + 1`.
-/
theorem centroid_mem_affineSpan_of_card_eq_add_one [CharZero k] {s : Finset ι} (p : ι → P) {n : ℕ}
    (h : #s = n + 1) : s.centroid k p ∈ affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_card_eq_add_one k h) p

end DivisionRing

