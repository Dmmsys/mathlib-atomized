/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Nonneg.Module
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Nonnegative real numbers

In this file we define `NNReal` (notation: `ℝ≥0`) to be the type of non-negative real numbers,
a.k.a. the interval `[0, ∞)`. We also define the following operations and structures on `ℝ≥0`:

* the order on `ℝ≥0` is the restriction of the order on `ℝ`; these relations define a conditionally
  complete linear order with a bottom element, `ConditionallyCompleteLinearOrderBot`;

* `a + b` and `a * b` are the restrictions of addition and multiplication of real numbers to `ℝ≥0`;
  these operations together with `0 = ⟨0, _⟩` and `1 = ⟨1, _⟩` turn `ℝ≥0` into a conditionally
  complete linear ordered archimedean commutative semifield; we have no typeclass for this in
  `mathlib` yet, so we define the following instances instead:

  - `IsOrderedRing ℝ≥0`;
  - `OrderedCommSemiring ℝ≥0`;
  - `CanonicallyOrderedAdd ℝ≥0`;
  - `LinearOrderedCommGroupWithZero ℝ≥0`;
  - `CanonicallyLinearOrderedAddCommMonoid ℝ≥0`;
  - `Archimedean ℝ≥0`;
  - `ConditionallyCompleteLinearOrderBot ℝ≥0`.

  These instances are derived from corresponding instances about the type `{x : α // 0 ≤ x}` in an
  appropriate ordered field/ring/group/monoid `α`, see `Mathlib/Algebra/Order/Nonneg/Ring.lean`.

* `Real.toNNReal x` is defined as `⟨max x 0, _⟩`, i.e. `↑(Real.toNNReal x) = x` when `0 ≤ x` and
  `↑(Real.toNNReal x) = 0` otherwise.

We also define an instance `CanLift ℝ ℝ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℝ` and `hx : 0 ≤ x` in the proof context with `x : ℝ≥0` while replacing all occurrences
of `x` with `↑x`. This tactic also works for a function `f : α → ℝ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

This file defines `ℝ≥0` as a localized notation for `NNReal`.
-/

@[expose] public section

assert_not_exists TrivialStar

open Function

/-- Nonnegative real numbers, denoted as `ℝ≥0` within the NNReal namespace -/
/-
**NNReal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Nonnegative real numbers, denoted as `ℝ≥0` within the NNReal namespace
-/
def NNReal := { r : ℝ // 0 ≤ r }

namespace NNReal

@[inherit_doc] scoped notation "ℝ≥0" => NNReal

/-- Coercion `ℝ≥0 → ℝ`. -/
/-
**NNReal.toReal** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
形式化陈述：NNReal → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion `ℝ≥0 → ℝ`.
-/
@[coe] def toReal : ℝ≥0 → ℝ := Subtype.val
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion `ℝ≥0 → ℝ`.
-/
instance : Coe ℝ≥0 ℝ := ⟨toReal⟩

/-- Constructor of ℝ≥0 from a nonnegative real number.

Important: You should use `NNReal.mk` instead of the anonymous constructor `⟨_, _⟩` to avoid abuse
of the definitional equality between `ℝ≥0` and `{ r : ℝ // 0 ≤ r }`. -/
/-
**NNReal.mk** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
形式化陈述：(x : ℝ) → 0 ≤ x → NNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor of ℝ≥0 from a nonnegative real number.

Important: You should use `NNReal.mk` instead of the anonymous constructor `⟨_, 
_⟩` to avoid abuse
of the definitional equality between `ℝ≥0` and `{ r : ℝ // 0 ≤ r }`.
-/
protected def mk (x : ℝ) (hx : 0 ≤ x) : ℝ≥0 := ⟨x, hx⟩
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero ℝ≥0 := ⟨.mk 0 le_rfl⟩
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One ℝ≥0 := ⟨.mk 1 zero_le_one⟩
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot ℝ≥0 := ⟨0⟩

deriving instance
  Nontrivial, Inhabited,
  PartialOrder, SemilatticeSup, SemilatticeInf, DistribLattice,
  Semiring, CommMonoidWithZero, CommSemiring, AddCancelCommMonoid,
  Sub, OrderedSub, OrderBot,
  CanonicallyOrderedAdd, NoZeroDivisors, DenselyOrdered,
  Archimedean, MulArchimedean, IsOrderedRing, IsStrictOrderedRing
  for NNReal

noncomputable section
deriving instance LinearOrder for NNReal
end

/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (0 : ℝ≥0) = ⊥ := by with_reducible_and_instances rfl

-- a computable copy of `Nonneg.instNNRatCast`
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NNRatCast ℝ≥0 where nnratCast r := ⟨r, r.cast_nonneg⟩
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Inv ℝ≥0 where
  inv x := .mk (x : ℝ)⁻¹ (inv_nonneg.mpr x.2)
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Div ℝ≥0 where
  div x y := .mk ((x : ℝ) / (y : ℝ)) (div_nonneg x.2 y.2)
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : SMul ℚ≥0 ℝ≥0 where
  smul x y := .mk (x • (y : ℝ)) (by rw [NNRat.smul_def]; exact mul_nonneg x.cast_nonneg y.2)
/-
**NNReal.zpow** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
形式化陈述：zpow : Pow Real>=0 Int where pow x n
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance zpow : Pow ℝ≥0 ℤ where
  pow x n := .mk ((x : ℝ) ^ n) (zpow_nonneg x.2 _)

/-- Redo the `Nonneg.semifield` instance, because this will get unfolded a lot,
and ends up inserting the non-reducible defeq `ℝ≥0 = { x // x ≥ 0 }` in places where
it needs to be reducible(-with-instances).
-/
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Redo the `Nonneg.semifield` instance, because this will get unfolded a lot,
and ends up inserting the non-reducible defeq `ℝ≥0 = { x // x ≥ 0 }` in places w
here
it needs to be reducible(-with-instances).
-/
noncomputable instance : Semifield ℝ≥0 := fast_instance%
  Function.Injective.semifield toReal Subtype.val_injective
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedRing ℝ≥0 :=
  Nonneg.isOrderedRing
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStrictOrderedRing ℝ≥0 :=
  Nonneg.isStrictOrderedRing
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : LinearOrderedCommGroupWithZero ℝ≥0 where
  bot_le h := h.2
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {p q : ℝ≥0} (h1p : 0 < p) (h2p : p ≤ q) : q⁻¹ ≤ p⁻¹ := by
  with_reducible_and_instances exact inv_anti₀ h1p h2p
/-
**NNReal.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (a : NNReal) (ha : 0 ≤ ↑a), NNReal.mk (↑a) ha = a
参数：a : NNReal；ha : 0 ≤ ↑a；↑a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_coe (a : ℝ≥0) (ha : 0 ≤ (a : ℝ)) : NNReal.mk (a : ℝ) ha = a := rfl

-- Simp lemma to put back `n.val` into the normal form given by the coercion.
@[simp]
/-
**NNReal.val_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：val_eq_coe (n : Real>=0) : n.val = n
参数：n : Real>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_eq_coe (n : ℝ≥0) : n.val = n :=
  rfl
/-
**NNReal.canLift** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
形式化陈述：canLift : CanLift Real Real>=0 toReal fun r => 0 <= r
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance canLift : CanLift ℝ ℝ≥0 toReal fun r => 0 ≤ r :=
  Subtype.canLift _
/-
**NNReal.eq** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {n m : NNReal}, ↑n = ↑m → n = m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
@[ext] protected theorem eq {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) → n = m :=
  Subtype.ext
/-
**NNReal.ne_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：ne_iff {x y : Real>=0} : (x : Real) != (y : Real) ↔ x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `NNReal.eq_iff`：∀ {n m : NNReal}, n = m ↔ ↑n = ↑m
-/
theorem ne_iff {x y : ℝ≥0} : (x : ℝ) ≠ (y : ℝ) ↔ x ≠ y :=
  not_congr <| NNReal.eq_iff.symm
/-
**NNReal.** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «forall» {p : ℝ≥0 → Prop} :
    (∀ x : ℝ≥0, p x) ↔ ∀ (x : ℝ) (hx : 0 ≤ x), p (.mk x hx) :=
  Subtype.forall
/-
**NNReal.** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «exists» {p : ℝ≥0 → Prop} :
    (∃ x : ℝ≥0, p x) ↔ ∃ (x : ℝ) (hx : 0 ≤ x), p (.mk x hx) :=
  Subtype.exists

/-- Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r < 0`. -/
/-
**NNReal._root_.Real.toNNReal** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r <
 0`.
-/
def _root_.Real.toNNReal (r : ℝ) : ℝ≥0 :=
  .mk (max r 0) (le_max_right _ _)
/-
**NNReal._root_.Real.coe_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.coe_toNNReal (r : ℝ) (hr : 0 ≤ r) : (Real.toNNReal r : ℝ) = r :=
  max_eq_left hr
/-
**NNReal._root_.Real.toNNReal_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.toNNReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : r.toNNReal = .mk r hr := by
  simp_rw [Real.toNNReal, max_eq_left hr]
/-
**NNReal._root_.Real.le_coe_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.le_coe_toNNReal (r : ℝ) : r ≤ Real.toNNReal r :=
  le_max_left r 0
/-
**NNReal.coe_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (r : NNReal), 0 ≤ ↑r
参数：r : NNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
@[bound] theorem coe_nonneg (r : ℝ≥0) : (0 : ℝ) ≤ r := r.2
/-
**NNReal.not_toReal_neg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r : NNReal}, ¬↑r < 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
@[simp] lemma not_toReal_neg {r : ℝ≥0} : ¬ r.toReal < 0 := r.coe_nonneg.not_gt
/-
**NNReal.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (a : ℝ) (ha : 0 ≤ a), ↑(NNReal.mk a ha) = a
参数：a : ℝ；ha : 0 ≤ a；NNReal.mk a ha。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] theorem coe_mk (a : ℝ) (ha) : toReal (.mk a ha) = a := rfl
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Zero ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : One ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Add ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Sub ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Mul ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example : Inv ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example : Div ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : LE ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Bot ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Inhabited ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Nontrivial ℝ≥0 := by infer_instance
/-
**NNReal.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：Function.Injective NNReal.toReal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
protected theorem coe_injective : Injective ((↑) : ℝ≥0 → ℝ) := Subtype.coe_injective
/-
**NNReal.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `NNReal.coe_injective`：Function.Injective NNReal.toReal
-/
@[simp, norm_cast] lemma coe_inj {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) = r₂ ↔ r₁ = r₂ :=
  NNReal.coe_injective.eq_iff
/-
**NNReal.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：↑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_zero : ((0 : ℝ≥0) : ℝ) = 0 := rfl
/-
**NNReal.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_one : ((1 : ℝ≥0) : ℝ) = 1 := rfl
/-
**NNReal.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：NNReal.mk 0 ⋯ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
@[simp] lemma mk_zero : NNReal.mk 0 le_rfl = 0 := rfl
/-
**NNReal.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：NNReal.mk 1 ⋯ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
@[simp] lemma mk_one : NNReal.mk 1 zero_le_one = 1 := rfl

@[simp, norm_cast]
/-
**NNReal.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (r₁ r₂ : NNReal), ↑(r₁ + r₂) = ↑r₁ + ↑r₂
参数：r₁ r₂ : NNReal；r₁ + r₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_add (r₁ r₂ : ℝ≥0) : ((r₁ + r₂ : ℝ≥0) : ℝ) = r₁ + r₂ :=
  rfl

@[simp, norm_cast]
/-
**NNReal.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (r₁ r₂ : NNReal), ↑(r₁ * r₂) = ↑r₁ * ↑r₂
参数：r₁ r₂ : NNReal；r₁ * r₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_mul (r₁ r₂ : ℝ≥0) : ((r₁ * r₂ : ℝ≥0) : ℝ) = r₁ * r₂ :=
  rfl

@[simp, norm_cast]
/-
**NNReal.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (r : NNReal), ↑r⁻¹ = (↑r)⁻¹
参数：r : NNReal；↑r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_inv (r : ℝ≥0) : ((r⁻¹ : ℝ≥0) : ℝ) = (r : ℝ)⁻¹ :=
  rfl

@[simp, norm_cast]
/-
**NNReal.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (r₁ r₂ : NNReal), ↑(r₁ / r₂) = ↑r₁ / ↑r₂
参数：r₁ r₂ : NNReal；r₁ / r₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_div (r₁ r₂ : ℝ≥0) : ((r₁ / r₂ : ℝ≥0) : ℝ) = (r₁ : ℝ) / r₂ :=
  rfl
/-
**NNReal.coe_two** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：↑2 = 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
protected theorem coe_two : ((2 : ℝ≥0) : ℝ) = 2 := rfl

@[simp, norm_cast]
/-
**NNReal.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r₁ r₂ : NNReal}, r₂ ≤ r₁ → ↑(r₁ - r₂) = ↑r₁ - ↑r₂
参数：r₁ - r₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_sub_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE α] [Add
LeftMono α] {a b c : α}, a ≤ b - c ↔ c ≤ b - a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
protected theorem coe_sub {r₁ r₂ : ℝ≥0} (h : r₂ ≤ r₁) : ((r₁ - r₂ : ℝ≥0) : ℝ) = ↑r₁ - ↑r₂ :=
  max_eq_left <| le_sub_comm.2 <| by simp [show (r₂ : ℝ) ≤ r₁ from h]

variable {r r₁ r₂ : ℝ≥0} {x y : ℝ}
/-
**NNReal.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_zero`：↑0 = 0
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_eq_zero : (r : ℝ) = 0 ↔ r = 0 := by rw [← coe_zero, coe_inj]
/-
**NNReal.coe_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r : NNReal}, ↑r = 1 ↔ r = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_one`：↑1 = 1
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_eq_one : (r : ℝ) = 1 ↔ r = 1 := by rw [← coe_one, coe_inj]
/-
**NNReal.coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r : NNReal}, ↑r ≠ 0 ↔ r ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `NNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
-/
@[norm_cast] lemma coe_ne_zero : (r : ℝ) ≠ 0 ↔ r ≠ 0 := coe_eq_zero.not
/-
**NNReal.coe_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r : NNReal}, ↑r ≠ 1 ↔ r ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `NNReal.coe_eq_one`：∀ {r : NNReal}, ↑r = 1 ↔ r = 1
-/
@[norm_cast] lemma coe_ne_one : (r : ℝ) ≠ 1 ↔ r ≠ 1 := coe_eq_one.not
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : CommSemiring ℝ≥0 := by infer_instance

/-- Coercion `ℝ≥0 → ℝ` as a `RingHom`.

TODO: what if we define `Coe ℝ≥0 ℝ` using this function? -/
/-
**NNReal.toRealHom** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
形式化陈述：toRealHom : Real>=0 ->+* Real where toFun
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.coe_one`：↑1 = 1
· 使用定理 `NNReal.coe_mul`：∀ (r₁ r₂ : NNReal), ↑(r₁ * r₂) = ↑r₁ * ↑r₂
· 使用定理 `NNReal.coe_zero`：↑0 = 0
· 使用定理 `NNReal.coe_add`：∀ (r₁ r₂ : NNReal), ↑(r₁ + r₂) = ↑r₁ + ↑r₂

--- 原说明 ---
Coercion `ℝ≥0 → ℝ` as a `RingHom`.

TODO: what if we define `Coe ℝ≥0 ℝ` using this function?
-/
def toRealHom : ℝ≥0 →+* ℝ where
  toFun := (↑)
  map_one' := NNReal.coe_one
  map_mul' := NNReal.coe_mul
  map_zero' := NNReal.coe_zero
  map_add' := NNReal.coe_add
/-
**NNReal.coe_toRealHom** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：⇑NNReal.toRealHom = NNReal.toReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_toRealHom : ⇑toRealHom = toReal := rfl

section Actions

/-- A scalar multiplication over `ℝ` restricts to a scalar multiplication over `ℝ≥0`. -/
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scalar multiplication over `ℝ` restricts to a scalar multiplication over `ℝ≥0`
.
-/
instance {M : Type*} [SMul ℝ M] : SMul ℝ≥0 M :=
  ⟨fun c m ↦ (c : ℝ) • m⟩

/-- A `MulAction` over `ℝ` restricts to a `MulAction` over `ℝ≥0`. -/
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `MulAction` over `ℝ` restricts to a `MulAction` over `ℝ≥0`.
-/
instance {M : Type*} [MulAction ℝ M] : MulAction ℝ≥0 M :=
  fast_instance% MulAction.compHom M toRealHom.toMonoidHom
/-
**NNReal.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：smul_def {M : Type*} [SMul Real M] (c : Real>=0) (x : M) : c • x = (c : Re
al) • x
参数：c : Real>=0；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def {M : Type*} [SMul ℝ M] (c : ℝ≥0) (x : M) : c • x = (c : ℝ) • x :=
  rfl
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Type*} [MulAction ℝ M] [MulAction ℝ N] [SMul M N] [IsScalarTower ℝ M N] :
    IsScalarTower ℝ≥0 M N where smul_assoc r := smul_assoc (r : ℝ)
/-
**NNReal.smulCommClass_left** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
形式化陈述：smulCommClass_left {M N : Type*} [MulAction Real N] [SMul M N] [SMulCommCl
ass Real M N] : SMulCommClass Real>=0 M N where smul_comm r
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass_left {M N : Type*} [MulAction ℝ N] [SMul M N] [SMulCommClass ℝ M N] :
    SMulCommClass ℝ≥0 M N where smul_comm r := smul_comm (r : ℝ)
/-
**NNReal.smulCommClass_right** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
形式化陈述：smulCommClass_right {M N : Type*} [MulAction Real N] [SMul M N] [SMulCommC
lass M Real N] : SMulCommClass M Real>=0 N where smul_comm m r
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass_right {M N : Type*} [MulAction ℝ N] [SMul M N] [SMulCommClass M ℝ N] :
    SMulCommClass M ℝ≥0 N where smul_comm m r := smul_comm m (r : ℝ)

/-- A `DistribMulAction` over `ℝ` restricts to a `DistribMulAction` over `ℝ≥0`. -/
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `DistribMulAction` over `ℝ` restricts to a `DistribMulAction` over `ℝ≥0`.
-/
instance {M : Type*} [AddMonoid M] [DistribMulAction ℝ M] : DistribMulAction ℝ≥0 M :=
  fast_instance% DistribMulAction.compHom M toRealHom.toMonoidHom

/-- A `Module` over `ℝ` restricts to a `Module` over `ℝ≥0`. -/
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Module` over `ℝ` restricts to a `Module` over `ℝ≥0`.
-/
instance {M : Type*} [AddCommMonoid M] [Module ℝ M] : Module ℝ≥0 M :=
  fast_instance% Module.compHom M toRealHom

/-- An `Algebra` over `ℝ` restricts to an `Algebra` over `ℝ≥0`. -/
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `Algebra` over `ℝ` restricts to an `Algebra` over `ℝ≥0`.
-/
instance {A : Type*} [Semiring A] [Algebra ℝ A] : Algebra ℝ≥0 A where
  commutes' r x := by simp [Algebra.commutes]
  smul_def' r x := by simp [← Algebra.smul_def (r : ℝ) x, smul_def]
  algebraMap := (algebraMap ℝ A).comp (toRealHom : ℝ≥0 →+* ℝ)

-- verify that the above produces instances we might care about
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Algebra ℝ≥0 ℝ := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : DistribMulAction ℝ≥0ˣ ℝ := by infer_instance

end Actions

/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : MonoidWithZero ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : CommMonoidWithZero ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example : CommGroupWithZero ℝ≥0 := by infer_instance

@[simp, norm_cast]
/-
**NNReal.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_pow (r : Real>=0) (n : Nat) : ((r ^ n : Real>=0) : Real) = (r : Real) 
^ n
参数：r : Real>=0；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow (r : ℝ≥0) (n : ℕ) : ((r ^ n : ℝ≥0) : ℝ) = (r : ℝ) ^ n := rfl

@[simp, norm_cast]
/-
**NNReal.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_zpow (r : Real>=0) (n : Int) : ((r ^ n : Real>=0) : Real) = (r : Real)
 ^ n
参数：r : Real>=0；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zpow (r : ℝ≥0) (n : ℤ) : ((r ^ n : ℝ≥0) : ℝ) = (r : ℝ) ^ n := rfl

variable {ι : Type*} {f : ι → ℝ}
/-
**NNReal.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (r : NNReal) (n : ℕ), ↑(n • r) = n • ↑r
参数：r : NNReal；n : ℕ；n • r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_nsmul (r : ℝ≥0) (n : ℕ) : ↑(n • r) = n • (r : ℝ) := rfl
/-
**NNReal.coe_nnqsmul** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (q : ℚ≥0) (x : NNReal), ↑(q • x) = q • ↑x
参数：q : ℚ≥0；x : NNReal；q • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_nnqsmul (q : ℚ≥0) (x : ℝ≥0) : ↑(q • x) = (q • x : ℝ) := rfl

@[simp, norm_cast]
/-
**NNReal.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (n : ℕ), ↑↑n = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
-/
protected theorem coe_natCast (n : ℕ) : (↑(↑n : ℝ≥0) : ℝ) = n :=
  map_natCast toRealHom n

@[simp, norm_cast]
/-
**NNReal.coe_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
参数：n : ℕ；OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] : ((ofNat(n) : ℝ≥0) : ℝ) = ofNat(n) :=
  rfl

@[simp, norm_cast]
/-
**NNReal.coe_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (m : ℕ) (s : Bool) (e : ℕ), ↑(OfScientific.ofScientific m s e) = OfScien
tific.ofScientific m s e
参数：m : ℕ；s : Bool；e : ℕ；OfScientific.ofScientific m s e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    ↑(OfScientific.ofScientific m s e : ℝ≥0) = (OfScientific.ofScientific m s e : ℝ) :=
  rfl

@[simp, norm_cast]
/-
**NNReal.algebraMap_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：algebraMap_eq_coe : (algebraMap Real>=0 Real : Real>=0 -> Real) = (↑)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma algebraMap_eq_coe : (algebraMap ℝ≥0 ℝ : ℝ≥0 → ℝ) = (↑) := rfl
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example : LinearOrder ℝ≥0 := by infer_instance
/-
**NNReal.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast, gcongr] lemma coe_le_coe : (r₁ : ℝ) ≤ r₂ ↔ r₁ ≤ r₂ := Iff.rfl
/-
**NNReal.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast, gcongr] lemma coe_lt_coe : (r₁ : ℝ) < r₂ ↔ r₁ < r₂ := Iff.rfl

@[bound] private alias ⟨_, Bound.coe_lt_coe_of_lt⟩ := coe_lt_coe
/-
**NNReal.coe_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_pos : (0 : ℝ) < r ↔ 0 < r := Iff.rfl

@[bound] private alias ⟨_, Bound.coe_pos_of_pos⟩ := coe_pos
/-
**NNReal.one_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r : NNReal}, 1 ≤ ↑r ↔ 1 ≤ r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `NNReal.coe_one`：↑1 = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma one_le_coe : 1 ≤ (r : ℝ) ↔ 1 ≤ r := by rw [← coe_le_coe, coe_one]
/-
**NNReal.one_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r : NNReal}, 1 < ↑r ↔ 1 < r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
· 使用定理 `NNReal.coe_one`：↑1 = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma one_lt_coe : 1 < (r : ℝ) ↔ 1 < r := by rw [← coe_lt_coe, coe_one]
/-
**NNReal.coe_le_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r : NNReal}, ↑r ≤ 1 ↔ r ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `NNReal.coe_one`：↑1 = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_le_one : (r : ℝ) ≤ 1 ↔ r ≤ 1 := by rw [← coe_le_coe, coe_one]
/-
**NNReal.coe_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r : NNReal}, ↑r < 1 ↔ r < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
· 使用定理 `NNReal.coe_one`：↑1 = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_lt_one : (r : ℝ) < 1 ↔ r < 1 := by rw [← coe_lt_coe, coe_one]
/-
**NNReal.coe_mono** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：Monotone NNReal.toReal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
-/
@[gcongr, mono] lemma coe_mono : Monotone ((↑) : ℝ≥0 → ℝ) := fun _ _ => NNReal.coe_le_coe.2
/-
**NNReal._root_.Real.toNNReal_monotone** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Real.toNNReal_monotone : Monotone Real.toNNReal := fun _ _ h =>
  max_le_max_right _ h

@[gcongr]
/-
**NNReal._root_.Real.toNNReal_mono** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Real.toNNReal_mono {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : r₁.toNNReal ≤ r₂.toNNReal :=
  Real.toNNReal_monotone h

@[simp]
/-
**NNReal._root_.Real.toNNReal_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.toNNReal_coe {r : ℝ≥0} : Real.toNNReal r = r :=
  NNReal.eq <| max_eq_left r.2

@[simp]
/-
**NNReal.mk_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：mk_natCast (n : Nat) : NNReal.mk (n : Real) (n.cast_nonneg) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
-/
theorem mk_natCast (n : ℕ) : NNReal.mk (n : ℝ) (n.cast_nonneg) = n :=
  NNReal.eq (NNReal.coe_natCast n).symm

@[simp]
/-
**NNReal._root_.Real.toNNReal_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.toNNReal_natCast (n : ℕ) : Real.toNNReal n = n :=
  NNReal.eq <| by simp [Real.coe_toNNReal]

@[deprecated (since := "2026-05-19")] alias _root_.Real.toNNReal_coe_nat := Real.toNNReal_natCast

@[simp]
/-
**NNReal._root_.Real.toNNReal_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.toNNReal_ofNat (n : ℕ) [n.AtLeastTwo] :
    Real.toNNReal ofNat(n) = OfNat.ofNat n :=
  Real.toNNReal_natCast n

/-- `Real.toNNReal` and `NNReal.toReal : ℝ≥0 → ℝ` form a Galois insertion. -/
/-
**NNReal.gi** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
形式化陈述：gi : GaloisInsertion Real.toNNReal (↑)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.coe_mono`：Monotone NNReal.toReal
· 使用定理 `Real.toNNReal_monotone`：Monotone Real.toNNReal
· 使用定理 `Real.le_coe_toNNReal`：∀ (r : ℝ), r ≤ ↑r.toNNReal
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r

--- 原说明 ---
`Real.toNNReal` and `NNReal.toReal : ℝ≥0 → ℝ` form a Galois insertion.
-/
def gi : GaloisInsertion Real.toNNReal (↑) :=
  GaloisInsertion.monotoneIntro NNReal.coe_mono Real.toNNReal_monotone Real.le_coe_toNNReal
    fun _ => Real.toNNReal_coe

-- note that anything involving the (decidability of the) linear order,
-- will be noncomputable, everything else should not be.
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : OrderBot ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : PartialOrder ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : AddCommMonoid ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : IsOrderedAddMonoid ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : DistribLattice ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : SemilatticeInf ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : SemilatticeSup ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Semiring ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : CommMonoid ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : IsOrderedMonoid ℝ≥0 := instLinearOrderedCommGroupWithZero.toIsOrderedMonoid
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example : LinearOrderedCommMonoidWithZero ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : DenselyOrdered ℝ≥0 := by infer_instance
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : NoMaxOrder ℝ≥0 := by infer_instance
/-
**NNReal.instPosSMulStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
形式化陈述：instPosSMulStrictMono {α} [Preorder α] [MulAction Real α] [PosSMulStrictMo
no Real α] : PosSMulStrictMono Real>=0 α where smul_lt_smul_of_pos_left _r hr _a
₁ _a₂ ha
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
-/
instance instPosSMulStrictMono {α} [Preorder α] [MulAction ℝ α] [PosSMulStrictMono ℝ α] :
    PosSMulStrictMono ℝ≥0 α where
  smul_lt_smul_of_pos_left _r hr _a₁ _a₂ ha := (smul_lt_smul_of_pos_left ha (coe_pos.2 hr) :)
/-
**NNReal.instSMulPosStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
形式化陈述：instSMulPosStrictMono {α} [Zero α] [Preorder α] [MulAction Real α] [SMulPo
sStrictMono Real α] : SMulPosStrictMono Real>=0 α where smul_lt_smul_of_pos_righ
t _a ha _r₁ _r₂ hr
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
-/
instance instSMulPosStrictMono {α} [Zero α] [Preorder α] [MulAction ℝ α] [SMulPosStrictMono ℝ α] :
    SMulPosStrictMono ℝ≥0 α where
  smul_lt_smul_of_pos_right _a ha _r₁ _r₂ hr := (smul_lt_smul_of_pos_right (coe_lt_coe.2 hr) ha :)

/-- If `a` is a nonnegative real number, then the closed interval `[0, a]` in `ℝ` is order
isomorphic to the interval `Set.Iic a`. -/
-- TODO: if we use `@[simps!]` it will look through the `NNReal = Subtype _` definition,
-- but if we use `@[simps]` it will not look through the `Equiv.Set.sep` definition.
-- Turning `NNReal` into a structure may be the best way to go here.
-- @[simps!? apply_coe_coe]
/-
**NNReal.orderIsoIccZeroCoe** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
形式化陈述：orderIsoIccZeroCoe (a : Real>=0) : Set.Icc (0 : Real) a ≃o Set.Iic a where
 toEquiv
参数：a : Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def orderIsoIccZeroCoe (a : ℝ≥0) : Set.Icc (0 : ℝ) a ≃o Set.Iic a where
  toEquiv := Equiv.Set.sep (Set.Ici 0) fun x : ℝ => x ≤ a
  map_rel_iff' := Iff.rfl

@[simp]
/-
**NNReal.orderIsoIccZeroCoe_apply_coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：orderIsoIccZeroCoe_apply_coe_coe (a : Real>=0) (b : Set.Icc (0 : Real) a) 
: (orderIsoIccZeroCoe a b : Real) = b
参数：a : Real>=0；b : Set.Icc (0 : Real) a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoIccZeroCoe_apply_coe_coe (a : ℝ≥0) (b : Set.Icc (0 : ℝ) a) :
    (orderIsoIccZeroCoe a b : ℝ) = b :=
  rfl

@[simp]
/-
**NNReal.orderIsoIccZeroCoe_symm_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：orderIsoIccZeroCoe_symm_apply_coe (a : Real>=0) (b : Set.Iic a) : ((orderI
soIccZeroCoe a).symm b : Real) = b
参数：a : Real>=0；b : Set.Iic a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoIccZeroCoe_symm_apply_coe (a : ℝ≥0) (b : Set.Iic a) :
    ((orderIsoIccZeroCoe a).symm b : ℝ) = b :=
  rfl
/-
**NNReal.coe_image** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_image {s : Set Real>=0} : (↑) '' s = { x : Real | exists h : 0 <= x, .
mk x h in s }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_image`：coe_image {p : α -> Prop} {s : Set (Subtype p)} : (↑)
 '' s = { x | exists h : p x, (⟨x, h⟩ : Subtype p) in s }
-/
theorem coe_image {s : Set ℝ≥0} :
    (↑) '' s = { x : ℝ | ∃ h : 0 ≤ x, .mk x h ∈ s } :=
  Subtype.coe_image
/-
**NNReal.bddAbove_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：bddAbove_coe {s : Set Real>=0} : BddAbove (((↑) : Real>=0 -> Real) '' s) ↔
 BddAbove s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem bddAbove_coe {s : Set ℝ≥0} : BddAbove (((↑) : ℝ≥0 → ℝ) '' s) ↔ BddAbove s :=
  Iff.intro
    (fun ⟨b, hb⟩ =>
      ⟨Real.toNNReal b, fun ⟨y, _⟩ hys =>
        show y ≤ max b 0 from le_max_of_le_left <| hb <| Set.mem_image_of_mem _ hys⟩)
    fun ⟨b, hb⟩ => ⟨b, fun _ ⟨_, hx, eq⟩ => eq ▸ hb hx⟩
/-
**NNReal.bddBelow_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：bddBelow_coe (s : Set Real>=0) : BddBelow (((↑) : Real>=0 -> Real) '' s)
参数：s : Set Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem bddBelow_coe (s : Set ℝ≥0) : BddBelow (((↑) : ℝ≥0 → ℝ) '' s) :=
  ⟨0, fun _ ⟨q, _, eq⟩ => eq ▸ q.2⟩
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : ConditionallyCompleteLinearOrderBot ℝ≥0 :=
  fast_instance% Nonneg.conditionallyCompleteLinearOrderBot 0

@[norm_cast]
/-
**NNReal.coe_sSup** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_sSup (s : Set Real>=0) : (↑(sSup s) : Real) = sSup (((↑) : Real>=0 -> 
Real) '' s)
参数：s : Set Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.sSup_nonneg`：sSup_nonneg (hs : forall x in s, 0 <= x) : 0 <= sSup s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `subset_sSup_of_within`：subset_sSup_of_within [Inhabited s] {t : Set s} (
h' : t.Nonempty) (h'' : BddAbove t) (h : sSup ((↑) '' t : Set α) in s) : sSup ((
↑) '' t : S…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `csSup_of_not_bddAbove`：csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s
 = sSup ∅
· 使用引理 `Real.sSup_of_not_bddAbove`：sSup_of_not_bddAbove (hs : ¬BddAbove s) : sSu
p s = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.bddAbove_coe`：bddAbove_coe {s : Set Real>=0} : BddAbove (((↑) : R
eal>=0 -> Real) '' s) ↔ BddAbove s
-/
theorem coe_sSup (s : Set ℝ≥0) : (↑(sSup s) : ℝ) = sSup (((↑) : ℝ≥0 → ℝ) '' s) := by
  rcases Set.eq_empty_or_nonempty s with rfl | hs
  · simp
  by_cases H : BddAbove s
  · have A : sSup (Subtype.val '' s) ∈ Set.Ici 0 := by
      apply Real.sSup_nonneg
      rintro - ⟨y, -, rfl⟩
      exact y.2
    exact (@subset_sSup_of_within ℝ (Set.Ici (0 : ℝ)) _ _ (_) s hs H A).symm
  · simp only [csSup_of_not_bddAbove H, csSup_empty, bot_eq_zero', NNReal.coe_zero]
    apply (Real.sSup_of_not_bddAbove ?_).symm
    contrapose H
    exact bddAbove_coe.1 H

@[simp, norm_cast]
/-
**NNReal.coe_iSup** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_iSup {ι : Sort*} (s : ι -> Real>=0) : (↑(⨆ i, s i) : Real) = ⨆ i, ↑(s 
i)
参数：s : ι -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `NNReal.coe_sSup`：coe_sSup (s : Set Real>=0) : (↑(sSup s) : Real) = sSup 
(((↑) : Real>=0 -> Real) '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem coe_iSup {ι : Sort*} (s : ι → ℝ≥0) : (↑(⨆ i, s i) : ℝ) = ⨆ i, ↑(s i) := by
  rw [iSup, iSup, coe_sSup, ← Set.range_comp]; rfl

@[norm_cast]
/-
**NNReal.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_sInf (s : Set Real>=0) : (↑(sInf s) : Real) = sInf (((↑) : Real>=0 -> 
Real) '' s)
参数：s : Set Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
· 使用定理 `subset_sInf_emptyset`：subset_sInf_emptyset [Inhabited s] : sInf (∅ : Set
 s) = default
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.sInf_nonneg`：sInf_nonneg (hs : forall x in s, 0 <= x) : 0 <= sInf s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `subset_sInf_of_within`：subset_sInf_of_within [Inhabited s] {t : Set s} (
h' : t.Nonempty) (h'' : BddBelow t) (h : sInf ((↑) '' t : Set α) in s) : sInf ((
↑) '' t : S…
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
theorem coe_sInf (s : Set ℝ≥0) : (↑(sInf s) : ℝ) = sInf (((↑) : ℝ≥0 → ℝ) '' s) := by
  rcases Set.eq_empty_or_nonempty s with rfl | hs
  · simp only [Set.image_empty, Real.sInf_empty, coe_eq_zero]
    exact @subset_sInf_emptyset ℝ (Set.Ici (0 : ℝ)) _ _ (_)
  have A : sInf (Subtype.val '' s) ∈ Set.Ici 0 := by
    apply Real.sInf_nonneg
    rintro - ⟨y, -, rfl⟩
    exact y.2
  exact (@subset_sInf_of_within ℝ (Set.Ici (0 : ℝ)) _ _ (_) s hs (OrderBot.bddBelow s) A).symm

@[simp]
/-
**NNReal.sInf_empty** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：sInf_empty : sInf (∅ : Set Real>=0) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用定理 `NNReal.coe_sInf`：coe_sInf (s : Set Real>=0) : (↑(sInf s) : Real) = sInf 
(((↑) : Real>=0 -> Real) '' s)
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
-/
theorem sInf_empty : sInf (∅ : Set ℝ≥0) = 0 := by
  rw [← coe_eq_zero, coe_sInf, Set.image_empty, Real.sInf_empty]

@[norm_cast]
/-
**NNReal.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_iInf {ι : Sort*} (s : ι -> Real>=0) : (↑(⨅ i, s i) : Real) = ⨅ i, ↑(s 
i)
参数：s : ι -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `NNReal.coe_sInf`：coe_sInf (s : Set Real>=0) : (↑(sInf s) : Real) = sInf 
(((↑) : Real>=0 -> Real) '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem coe_iInf {ι : Sort*} (s : ι → ℝ≥0) : (↑(⨅ i, s i) : ℝ) = ⨅ i, ↑(s i) := by
  rw [iInf, iInf, coe_sInf, ← Set.range_comp]; rfl

-- Short-circuit instance search
/-
**NNReal.addLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
形式化陈述：addLeftMono : AddLeftMono Real>=0
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
-/
instance addLeftMono : AddLeftMono ℝ≥0 := inferInstance
/-
**NNReal.addLeftReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
形式化陈述：addLeftReflectLT : AddLeftReflectLT Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addLeftReflectLT : AddLeftReflectLT ℝ≥0 := inferInstance
/-
**NNReal.mulLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
形式化陈述：mulLeftMono : MulLeftMono Real>=0
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
-/
instance mulLeftMono : MulLeftMono ℝ≥0 := inferInstance
/-
**NNReal.lt_iff_exists_rat_btwn** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：lt_iff_exists_rat_btwn (a b : Real>=0) : a < b ↔ exists q : Rat, 0 <= q ∧ 
a < Real.toNNReal q ∧ Real.toNNReal q < b
参数：a b : Real>=0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Rat.cast_nonneg`：∀ {q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Lin
earOrder K] [IsStrictOrderedRing K], 0 ≤ ↑q ↔ 0 ≤ q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
-/
theorem lt_iff_exists_rat_btwn (a b : ℝ≥0) :
    a < b ↔ ∃ q : ℚ, 0 ≤ q ∧ a < Real.toNNReal q ∧ Real.toNNReal q < b :=
  Iff.intro
    (fun h : (↑a : ℝ) < (↑b : ℝ) =>
      let ⟨q, haq, hqb⟩ := exists_rat_btwn h
      have : 0 ≤ (q : ℝ) := le_trans a.2 <| le_of_lt haq
      ⟨q, Rat.cast_nonneg.1 this, by
        simp [Real.coe_toNNReal _ this, NNReal.coe_lt_coe.symm, haq, hqb]⟩)
    fun ⟨_, _, haq, hqb⟩ => lt_trans haq hqb
/-
**NNReal.bot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：bot_eq_zero : (⊥ : Real>=0) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_eq_zero : (⊥ : ℝ≥0) = 0 := rfl
/-
**NNReal.mul_sup** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：mul_sup (a b c : Real>=0) : a * (b ⊔ c) = a * b ⊔ a * c
参数：a b c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_max_of_nonneg`：mul_max_of_nonneg [PosMulMono R] (b c : R) (ha : 0 <=
 a) : a * max b c = max (a * b) (a * c)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem mul_sup (a b c : ℝ≥0) : a * (b ⊔ c) = a * b ⊔ a * c :=
  mul_max_of_nonneg _ _ zero_le
/-
**NNReal.sup_mul** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：sup_mul (a b c : Real>=0) : (a ⊔ b) * c = a * c ⊔ b * c
参数：a b c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_mul_of_nonneg`：max_mul_of_nonneg [MulPosMono R] (a b : R) (hc : 0 <=
 c) : max a b * c = max (a * c) (b * c)
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem sup_mul (a b c : ℝ≥0) : (a ⊔ b) * c = a * c ⊔ b * c :=
  max_mul_of_nonneg _ _ zero_le

@[simp, norm_cast]
/-
**NNReal.coe_max** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_max (x y : Real>=0) : ((max x y : Real>=0) : Real) = max (x : Real) (y
 : Real)
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `NNReal.coe_mono`：Monotone NNReal.toReal
-/
theorem coe_max (x y : ℝ≥0) : ((max x y : ℝ≥0) : ℝ) = max (x : ℝ) (y : ℝ) :=
  NNReal.coe_mono.map_max

@[simp, norm_cast]
/-
**NNReal.coe_min** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_min (x y : Real>=0) : ((min x y : Real>=0) : Real) = min (x : Real) (y
 : Real)
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `NNReal.coe_mono`：Monotone NNReal.toReal
-/
theorem coe_min (x y : ℝ≥0) : ((min x y : ℝ≥0) : ℝ) = min (x : ℝ) (y : ℝ) :=
  NNReal.coe_mono.map_min

@[simp]
/-
**NNReal.zero_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：zero_le_coe {q : Real>=0} : 0 <= (q : Real)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem zero_le_coe {q : ℝ≥0} : 0 ≤ (q : ℝ) :=
  q.2
/-
**NNReal.instIsStrictOrderedModule** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
形式化陈述：instIsStrictOrderedModule {M : Type*} [AddCommMonoid M] [PartialOrder M] [
Module Real M] [IsStrictOrderedModule Real M] : IsStrictOrderedModule Real>=0 M
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsStrictOrderedModule {M : Type*} [AddCommMonoid M] [PartialOrder M]
    [Module ℝ M] [IsStrictOrderedModule ℝ M] :
    IsStrictOrderedModule ℝ≥0 M := inferInstanceAs <| IsStrictOrderedModule (Subtype _) M

end NNReal

open NNReal

namespace Real

section ToNNReal

@[simp]
/-
**Real.coe_toNNReal'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：coe_toNNReal' (r : Real) : (Real.toNNReal r : Real) = max r 0
参数：r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNNReal' (r : ℝ) : (Real.toNNReal r : ℝ) = max r 0 :=
  rfl

@[simp]
/-
**Real.toNNReal_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_zero : Real.toNNReal 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem toNNReal_zero : Real.toNNReal 0 = 0 := NNReal.eq <| coe_toNNReal _ le_rfl

@[simp]
/-
**Real.toNNReal_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_one : Real.toNNReal 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem toNNReal_one : Real.toNNReal 1 = 1 := NNReal.eq <| coe_toNNReal _ zero_le_one

@[simp]
/-
**Real.toNNReal_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_pos {r : Real} : 0 < Real.toNNReal r ↔ 0 < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toNNReal_pos {r : ℝ} : 0 < Real.toNNReal r ↔ 0 < r := by
  simp [← NNReal.coe_lt_coe]

@[simp]
/-
**Real.toNNReal_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_eq_zero {r : Real} : Real.toNNReal r = 0 ↔ r <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Real.toNNReal_pos`：toNNReal_pos {r : Real} : 0 < Real.toNNReal r ↔ 0 < r
-/
theorem toNNReal_eq_zero {r : ℝ} : Real.toNNReal r = 0 ↔ r ≤ 0 := by
  simpa [-toNNReal_pos] using not_iff_not.2 (@toNNReal_pos r)
/-
**Real.toNNReal_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_of_nonpos {r : Real} : r <= 0 -> Real.toNNReal r = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.toNNReal_eq_zero`：toNNReal_eq_zero {r : Real} : Real.toNNReal r = 0
 ↔ r <= 0
-/
theorem toNNReal_of_nonpos {r : ℝ} : r ≤ 0 → Real.toNNReal r = 0 :=
  toNNReal_eq_zero.2
/-
**Real.toNNReal_eq_iff_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：toNNReal_eq_iff_eq_coe {r : Real} {p : Real>=0} (hp : p != 0) : r.toNNReal
 = p ↔ r = p
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Real.toNNReal_of_nonpos`：toNNReal_of_nonpos {r : Real} : r <= 0 -> Real.
toNNReal r = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
-/
lemma toNNReal_eq_iff_eq_coe {r : ℝ} {p : ℝ≥0} (hp : p ≠ 0) : r.toNNReal = p ↔ r = p :=
  ⟨fun h ↦ h ▸ (coe_toNNReal _ <| not_lt.1 fun hlt ↦ hp <| h ▸ toNNReal_of_nonpos hlt.le).symm,
    fun h ↦ h.symm ▸ toNNReal_coe⟩

@[simp]
/-
**Real.toNNReal_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：toNNReal_eq_one {r : Real} : r.toNNReal = 1 ↔ r = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.toNNReal_eq_iff_eq_coe`：toNNReal_eq_iff_eq_coe {r : Real} {p : Real
>=0} (hp : p != 0) : r.toNNReal = p ↔ r = p
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
-/
lemma toNNReal_eq_one {r : ℝ} : r.toNNReal = 1 ↔ r = 1 := toNNReal_eq_iff_eq_coe one_ne_zero

@[simp]
/-
**Real.toNNReal_eq_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：toNNReal_eq_natCast {r : Real} {n : Nat} (hn : n != 0) : r.toNNReal = n ↔ 
r = n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用引理 `Real.toNNReal_eq_iff_eq_coe`：toNNReal_eq_iff_eq_coe {r : Real} {p : Real
>=0} (hp : p != 0) : r.toNNReal = p ↔ r = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
-/
lemma toNNReal_eq_natCast {r : ℝ} {n : ℕ} (hn : n ≠ 0) : r.toNNReal = n ↔ r = n :=
  mod_cast toNNReal_eq_iff_eq_coe <| Nat.cast_ne_zero.2 hn

@[simp]
/-
**Real.toNNReal_eq_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：toNNReal_eq_ofNat {r : Real} {n : Nat} [n.AtLeastTwo] : r.toNNReal = ofNat
(n) ↔ r = OfNat.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.toNNReal_eq_natCast`：toNNReal_eq_natCast {r : Real} {n : Nat} (hn :
 n != 0) : r.toNNReal = n ↔ r = n
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
lemma toNNReal_eq_ofNat {r : ℝ} {n : ℕ} [n.AtLeastTwo] :
    r.toNNReal = ofNat(n) ↔ r = OfNat.ofNat n :=
  toNNReal_eq_natCast (NeZero.ne n)

@[simp]
/-
**Real.toNNReal_le_toNNReal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_le_toNNReal_iff {r p : Real} (hp : 0 <= p) : toNNReal r <= toNNRe
al p ↔ r <= p
参数：hp : 0 <= p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toNNReal_le_toNNReal_iff {r p : ℝ} (hp : 0 ≤ p) :
    toNNReal r ≤ toNNReal p ↔ r ≤ p := by simp [← NNReal.coe_le_coe, hp]

@[simp]
/-
**Real.toNNReal_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：toNNReal_le_one {r : Real} : r.toNNReal <= 1 ↔ r <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_one`：toNNReal_one : Real.toNNReal 1 = 1
· 使用定理 `Real.toNNReal_le_toNNReal_iff`：toNNReal_le_toNNReal_iff {r p : Real} (hp
 : 0 <= p) : toNNReal r <= toNNReal p ↔ r <= p
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma toNNReal_le_one {r : ℝ} : r.toNNReal ≤ 1 ↔ r ≤ 1 := by
  simpa using toNNReal_le_toNNReal_iff zero_le_one

@[simp]
/-
**Real.one_lt_toNNReal** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：one_lt_toNNReal {r : Real} : 1 < r.toNNReal ↔ 1 < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Real.toNNReal_le_one`：toNNReal_le_one {r : Real} : r.toNNReal <= 1 ↔ r <
= 1
-/
lemma one_lt_toNNReal {r : ℝ} : 1 < r.toNNReal ↔ 1 < r := by
  simpa only [not_le] using toNNReal_le_one.not

@[simp]
/-
**Real.toNNReal_le_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：toNNReal_le_natCast {r : Real} {n : Nat} : r.toNNReal <= n ↔ r <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_natCast`：∀ (n : ℕ), (↑n).toNNReal = ↑n
· 使用定理 `Real.toNNReal_le_toNNReal_iff`：toNNReal_le_toNNReal_iff {r p : Real} (hp
 : 0 <= p) : toNNReal r <= toNNReal p ↔ r <= p
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
lemma toNNReal_le_natCast {r : ℝ} {n : ℕ} : r.toNNReal ≤ n ↔ r ≤ n := by
  simpa using toNNReal_le_toNNReal_iff n.cast_nonneg

@[simp]
/-
**Real.natCast_lt_toNNReal** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：natCast_lt_toNNReal {r : Real} {n : Nat} : n < r.toNNReal ↔ n < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Real.toNNReal_le_natCast`：toNNReal_le_natCast {r : Real} {n : Nat} : r.t
oNNReal <= n ↔ r <= n
-/
lemma natCast_lt_toNNReal {r : ℝ} {n : ℕ} : n < r.toNNReal ↔ n < r := by
  simpa only [not_le] using toNNReal_le_natCast.not

@[simp]
/-
**Real.toNNReal_le_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：toNNReal_le_ofNat {r : Real} {n : Nat} [n.AtLeastTwo] : r.toNNReal <= ofNa
t(n) ↔ r <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.toNNReal_le_natCast`：toNNReal_le_natCast {r : Real} {n : Nat} : r.t
oNNReal <= n ↔ r <= n
-/
lemma toNNReal_le_ofNat {r : ℝ} {n : ℕ} [n.AtLeastTwo] :
    r.toNNReal ≤ ofNat(n) ↔ r ≤ n :=
  toNNReal_le_natCast

@[simp]
/-
**Real.ofNat_lt_toNNReal** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：ofNat_lt_toNNReal {r : Real} {n : Nat} [n.AtLeastTwo] : ofNat(n) < r.toNNR
eal ↔ n < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.natCast_lt_toNNReal`：natCast_lt_toNNReal {r : Real} {n : Nat} : n <
 r.toNNReal ↔ n < r
-/
lemma ofNat_lt_toNNReal {r : ℝ} {n : ℕ} [n.AtLeastTwo] :
    ofNat(n) < r.toNNReal ↔ n < r :=
  natCast_lt_toNNReal

@[simp]
/-
**Real.toNNReal_eq_toNNReal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_eq_toNNReal_iff {r p : Real} (hr : 0 <= r) (hp : 0 <= p) : toNNRe
al r = toNNReal p ↔ r = p
参数：hr : 0 <= r；hp : 0 <= p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toNNReal_eq_toNNReal_iff {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    toNNReal r = toNNReal p ↔ r = p := by simp [← coe_inj, hr, hp]

@[simp]
/-
**Real.toNNReal_lt_toNNReal_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_lt_toNNReal_iff' {r p : Real} : Real.toNNReal r < Real.toNNReal p
 ↔ r < p ∧ 0 < p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
· 使用定理 `max_lt_max_left_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, 
max b c < max a c ↔ b < a ∧ c < a
-/
theorem toNNReal_lt_toNNReal_iff' {r p : ℝ} : Real.toNNReal r < Real.toNNReal p ↔ r < p ∧ 0 < p :=
  NNReal.coe_lt_coe.symm.trans max_lt_max_left_iff
/-
**Real.toNNReal_lt_toNNReal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_lt_toNNReal_iff {r p : Real} (h : 0 < p) : Real.toNNReal r < Real
.toNNReal p ↔ r < p
参数：h : 0 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Real.toNNReal_lt_toNNReal_iff'`：toNNReal_lt_toNNReal_iff' {r p : Real} :
 Real.toNNReal r < Real.toNNReal p ↔ r < p ∧ 0 < p
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
-/
theorem toNNReal_lt_toNNReal_iff {r p : ℝ} (h : 0 < p) :
    Real.toNNReal r < Real.toNNReal p ↔ r < p :=
  toNNReal_lt_toNNReal_iff'.trans (and_iff_left h)
/-
**Real.lt_of_toNNReal_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lt_of_toNNReal_lt {r p : Real} (h : r.toNNReal < p.toNNReal) : r < p
参数：h : r.toNNReal < p.toNNReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.toNNReal_lt_toNNReal_iff`：toNNReal_lt_toNNReal_iff {r p : Real} (h 
: 0 < p) : Real.toNNReal r < Real.toNNReal p ↔ r < p
· 使用定理 `Real.toNNReal_pos`：toNNReal_pos {r : Real} : 0 < Real.toNNReal r ↔ 0 < r
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
-/
theorem lt_of_toNNReal_lt {r p : ℝ} (h : r.toNNReal < p.toNNReal) : r < p :=
  (Real.toNNReal_lt_toNNReal_iff <| Real.toNNReal_pos.1 (ne_bot_of_gt h).bot_lt).1 h
/-
**Real.toNNReal_lt_toNNReal_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_lt_toNNReal_iff_of_nonneg {r p : Real} (hr : 0 <= r) : Real.toNNR
eal r < Real.toNNReal p ↔ r < p
参数：hr : 0 <= r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Real.toNNReal_lt_toNNReal_iff'`：toNNReal_lt_toNNReal_iff' {r p : Real} :
 Real.toNNReal r < Real.toNNReal p ↔ r < p ∧ 0 < p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
-/
theorem toNNReal_lt_toNNReal_iff_of_nonneg {r p : ℝ} (hr : 0 ≤ r) :
    Real.toNNReal r < Real.toNNReal p ↔ r < p :=
  toNNReal_lt_toNNReal_iff'.trans ⟨And.left, fun h => ⟨h, lt_of_le_of_lt hr h⟩⟩
/-
**Real.toNNReal_le_toNNReal_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：toNNReal_le_toNNReal_iff' {r p : Real} : r.toNNReal <= p.toNNReal ↔ r <= p
 ∨ r <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toNNReal_le_toNNReal_iff' {r p : ℝ} : r.toNNReal ≤ p.toNNReal ↔ r ≤ p ∨ r ≤ 0 := by
  simp_rw [← not_lt, toNNReal_lt_toNNReal_iff', not_and_or]
/-
**Real.toNNReal_le_toNNReal_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：toNNReal_le_toNNReal_iff_of_pos {r p : Real} (hr : 0 < r) : r.toNNReal <= 
p.toNNReal ↔ r <= p
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toNNReal_le_toNNReal_iff_of_pos {r p : ℝ} (hr : 0 < r) : r.toNNReal ≤ p.toNNReal ↔ r ≤ p := by
  simp [toNNReal_le_toNNReal_iff', hr.not_ge]

@[simp]
/-
**Real.one_le_toNNReal** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：one_le_toNNReal {r : Real} : 1 <= r.toNNReal ↔ 1 <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_one`：toNNReal_one : Real.toNNReal 1 = 1
· 使用引理 `Real.toNNReal_le_toNNReal_iff_of_pos`：toNNReal_le_toNNReal_iff_of_pos {r
 p : Real} (hr : 0 < r) : r.toNNReal <= p.toNNReal ↔ r <= p
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma one_le_toNNReal {r : ℝ} : 1 ≤ r.toNNReal ↔ 1 ≤ r := by
  simpa using toNNReal_le_toNNReal_iff_of_pos one_pos

@[simp]
/-
**Real.toNNReal_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：toNNReal_lt_one {r : Real} : r.toNNReal < 1 ↔ r < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toNNReal_lt_one {r : ℝ} : r.toNNReal < 1 ↔ r < 1 := by simp only [← not_le, one_le_toNNReal]

@[simp]
/-
**Real.natCastle_toNNReal'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：natCastle_toNNReal' {n : Nat} {r : Real} : ↑n <= r.toNNReal ↔ n <= r ∨ n =
 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.toNNReal_natCast`：∀ (n : ℕ), (↑n).toNNReal = ↑n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Real.toNNReal_le_toNNReal_iff'`：toNNReal_le_toNNReal_iff' {r p : Real} :
 r.toNNReal <= p.toNNReal ↔ r <= p ∨ r <= 0
-/
lemma natCastle_toNNReal' {n : ℕ} {r : ℝ} : ↑n ≤ r.toNNReal ↔ n ≤ r ∨ n = 0 := by
  simpa [n.cast_nonneg.ge_iff_eq'] using toNNReal_le_toNNReal_iff' (r := n)

@[simp]
/-
**Real.toNNReal_lt_natCast'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：toNNReal_lt_natCast' {n : Nat} {r : Real} : r.toNNReal < n ↔ r < n ∧ n != 
0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_natCast`：∀ (n : ℕ), (↑n).toNNReal = ↑n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Real.toNNReal_lt_toNNReal_iff'`：toNNReal_lt_toNNReal_iff' {r p : Real} :
 Real.toNNReal r < Real.toNNReal p ↔ r < p ∧ 0 < p
-/
lemma toNNReal_lt_natCast' {n : ℕ} {r : ℝ} : r.toNNReal < n ↔ r < n ∧ n ≠ 0 := by
  simpa [pos_iff_ne_zero] using toNNReal_lt_toNNReal_iff' (r := r) (p := n)
/-
**Real.natCast_le_toNNReal** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：natCast_le_toNNReal {n : Nat} {r : Real} (hn : n != 0) : ↑n <= r.toNNReal 
↔ n <= r
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma natCast_le_toNNReal {n : ℕ} {r : ℝ} (hn : n ≠ 0) : ↑n ≤ r.toNNReal ↔ n ≤ r := by simp [hn]
/-
**Real.toNNReal_lt_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：toNNReal_lt_natCast {r : Real} {n : Nat} (hn : n != 0) : r.toNNReal < n ↔ 
r < n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toNNReal_lt_natCast {r : ℝ} {n : ℕ} (hn : n ≠ 0) : r.toNNReal < n ↔ r < n := by simp [hn]

@[simp]
/-
**Real.toNNReal_lt_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：toNNReal_lt_ofNat {r : Real} {n : Nat} [n.AtLeastTwo] : r.toNNReal < ofNat
(n) ↔ r < OfNat.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.toNNReal_lt_natCast`：toNNReal_lt_natCast {r : Real} {n : Nat} (hn :
 n != 0) : r.toNNReal < n ↔ r < n
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
lemma toNNReal_lt_ofNat {r : ℝ} {n : ℕ} [n.AtLeastTwo] :
    r.toNNReal < ofNat(n) ↔ r < OfNat.ofNat n :=
  toNNReal_lt_natCast (NeZero.ne n)

@[simp]
/-
**Real.ofNat_le_toNNReal** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：ofNat_le_toNNReal {n : Nat} {r : Real} [n.AtLeastTwo] : ofNat(n) <= r.toNN
Real ↔ OfNat.ofNat n <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.natCast_le_toNNReal`：natCast_le_toNNReal {n : Nat} {r : Real} (hn :
 n != 0) : ↑n <= r.toNNReal ↔ n <= r
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
lemma ofNat_le_toNNReal {n : ℕ} {r : ℝ} [n.AtLeastTwo] :
    ofNat(n) ≤ r.toNNReal ↔ OfNat.ofNat n ≤ r :=
  natCast_le_toNNReal (NeZero.ne n)

@[simp]
/-
**Real.toNNReal_add** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_add {r p : Real} (hr : 0 <= r) (hp : 0 <= p) : Real.toNNReal (r +
 p) = Real.toNNReal r + Real.toNNReal p
参数：hr : 0 <= r；hp : 0 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toNNReal_add {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    Real.toNNReal (r + p) = Real.toNNReal r + Real.toNNReal p :=
  NNReal.eq <| by simp [hr, hp, add_nonneg]
/-
**Real.toNNReal_add_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_add_toNNReal {r p : Real} (hr : 0 <= r) (hp : 0 <= p) : Real.toNN
Real r + Real.toNNReal p = Real.toNNReal (r + p)
参数：hr : 0 <= r；hp : 0 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.toNNReal_add`：toNNReal_add {r p : Real} (hr : 0 <= r) (hp : 0 <= p)
 : Real.toNNReal (r + p) = Real.toNNReal r + Real.toNNReal p
-/
theorem toNNReal_add_toNNReal {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    Real.toNNReal r + Real.toNNReal p = Real.toNNReal (r + p) :=
  (Real.toNNReal_add hr hp).symm
/-
**Real.toNNReal_le_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_le_toNNReal {r p : Real} (h : r <= p) : Real.toNNReal r <= Real.t
oNNReal p
参数：h : r <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.toNNReal_mono`：∀ {r₁ r₂ : ℝ}, r₁ ≤ r₂ → r₁.toNNReal ≤ r₂.toNNReal
-/
theorem toNNReal_le_toNNReal {r p : ℝ} (h : r ≤ p) : Real.toNNReal r ≤ Real.toNNReal p :=
  Real.toNNReal_mono h
/-
**Real.toNNReal_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_add_le {r p : Real} : Real.toNNReal (r + p) <= Real.toNNReal r + 
Real.toNNReal p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `NNReal.zero_le_coe`：zero_le_coe {q : Real>=0} : 0 <= (q : Real)
-/
theorem toNNReal_add_le {r p : ℝ} : Real.toNNReal (r + p) ≤ Real.toNNReal r + Real.toNNReal p :=
  NNReal.coe_le_coe.1 <| max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) NNReal.zero_le_coe
/-
**Real.toNNReal_le_iff_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_le_iff_le_coe {r : Real} {p : Real>=0} : toNNReal r <= p ↔ r <= ↑
p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem toNNReal_le_iff_le_coe {r : ℝ} {p : ℝ≥0} : toNNReal r ≤ p ↔ r ≤ ↑p :=
  NNReal.gi.gc r p
/-
**Real.le_toNNReal_iff_coe_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_toNNReal_iff_coe_le {r : Real>=0} {p : Real} (hp : 0 <= p) : r <= Real.
toNNReal p ↔ ↑r <= p
参数：hp : 0 <= p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_toNNReal_iff_coe_le {r : ℝ≥0} {p : ℝ} (hp : 0 ≤ p) : r ≤ Real.toNNReal p ↔ ↑r ≤ p := by
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal p hp]
/-
**Real.le_toNNReal_iff_coe_le'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_toNNReal_iff_coe_le' {r : Real>=0} {p : Real} (hr : 0 < r) : r <= Real.
toNNReal p ↔ ↑r <= p
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Real.le_toNNReal_iff_coe_le`：le_toNNReal_iff_coe_le {r : Real>=0} {p : R
eal} (hp : 0 <= p) : r <= Real.toNNReal p ↔ ↑r <= p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.toNNReal_eq_zero`：toNNReal_eq_zero {r : Real} : Real.toNNReal r = 0
 ↔ r <= 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_toNNReal_iff_coe_le' {r : ℝ≥0} {p : ℝ} (hr : 0 < r) : r ≤ Real.toNNReal p ↔ ↑r ≤ p :=
  (le_or_gt 0 p).elim le_toNNReal_iff_coe_le fun hp => by
    simp only [(hp.trans_le r.coe_nonneg).not_ge, toNNReal_eq_zero.2 hp.le, hr.not_ge]
/-
**Real.toNNReal_lt_iff_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_lt_iff_lt_coe {r : Real} {p : Real>=0} (ha : 0 <= r) : Real.toNNR
eal r < p ↔ r < ↑p
参数：ha : 0 <= r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toNNReal_lt_iff_lt_coe {r : ℝ} {p : ℝ≥0} (ha : 0 ≤ r) : Real.toNNReal r < p ↔ r < ↑p := by
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal r ha]
/-
**Real.lt_toNNReal_iff_coe_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lt_toNNReal_iff_coe_lt {r : Real>=0} {p : Real} : r < Real.toNNReal p ↔ ↑r
 < p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Real.toNNReal_le_iff_le_coe`：toNNReal_le_iff_le_coe {r : Real} {p : Real
>=0} : toNNReal r <= p ↔ r <= ↑p
-/
theorem lt_toNNReal_iff_coe_lt {r : ℝ≥0} {p : ℝ} : r < Real.toNNReal p ↔ ↑r < p :=
  lt_iff_lt_of_le_iff_le toNNReal_le_iff_le_coe
/-
**Real.toNNReal_pow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_pow {x : Real} (hx : 0 <= x) (n : Nat) : (x ^ n).toNNReal = x.toN
NReal ^ n
参数：hx : 0 <= x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `NNReal.coe_pow`：coe_pow (r : Real>=0) (n : Nat) : ((r ^ n : Real>=0) : R
eal) = (r : Real) ^ n
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem toNNReal_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : (x ^ n).toNNReal = x.toNNReal ^ n := by
  rw [← coe_inj, NNReal.coe_pow, Real.coe_toNNReal _ (pow_nonneg hx _),
    Real.coe_toNNReal x hx]
/-
**Real.toNNReal_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_zpow {x : Real} (hx : 0 <= x) (n : Int) : (x ^ n).toNNReal = x.to
NNReal ^ n
参数：hx : 0 <= x；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `NNReal.coe_zpow`：coe_zpow (r : Real>=0) (n : Int) : ((r ^ n : Real>=0) :
 Real) = (r : Real) ^ n
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用定理 `zpow_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Parti
alOrder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 ≤ a → ∀ (n : 
ℤ…
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem toNNReal_zpow {x : ℝ} (hx : 0 ≤ x) (n : ℤ) : (x ^ n).toNNReal = x.toNNReal ^ n := by
  rw [← coe_inj, NNReal.coe_zpow, Real.coe_toNNReal _ (zpow_nonneg hx _), Real.coe_toNNReal x hx]
/-
**Real.toNNReal_mul** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_mul {p q : Real} (hp : 0 <= p) : Real.toNNReal (p * q) = Real.toN
NReal p * Real.toNNReal q
参数：hp : 0 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `mul_max_of_nonneg`：mul_max_of_nonneg [PosMulMono R] (b c : R) (ha : 0 <=
 a) : a * max b c = max (a * b) (a * c)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toNNReal_mul {p q : ℝ} (hp : 0 ≤ p) :
    Real.toNNReal (p * q) = Real.toNNReal p * Real.toNNReal q :=
  NNReal.eq <| by simp [mul_max_of_nonneg, hp]

end ToNNReal

end Real

open Real

namespace NNReal

section Mul

/-
**NNReal.mul_eq_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：mul_eq_mul_left {a b c : Real>=0} (h : a != 0) : a * b = a * c ↔ b = c
参数：h : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_mul_left_iff`：∀ {M₀ : Type u_1} [inst : MulZeroClass M₀] [IsLeftC
ancelMulZero M₀] {a b c : M₀}, a * b = a * c ↔ b = c ∨ a = 0
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_eq_mul_left {a b c : ℝ≥0} (h : a ≠ 0) : a * b = a * c ↔ b = c := by
  rw [mul_eq_mul_left_iff, or_iff_left h]

end Mul

section Pow

/-
**NNReal.pow_antitone_exp** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：pow_antitone_exp {a : Real>=0} (m n : Nat) (mn : m <= n) (a1 : a <= 1) : a
 ^ n <= a ^ m
参数：m n : Nat；mn : m <= n；a1 : a <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_le_pow_of_le_one`：pow_le_pow_of_le_one [PosMulMono M₀] (ha₀ : 0 <= a
) (ha₁ : a <= 1) {m n : Nat} (hmn : m <= n) : a ^ n <= a ^ m
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem pow_antitone_exp {a : ℝ≥0} (m n : ℕ) (mn : m ≤ n) (a1 : a ≤ 1) : a ^ n ≤ a ^ m :=
  pow_le_pow_of_le_one zero_le a1 mn

nonrec theorem exists_pow_lt_of_lt_one {a b : ℝ≥0} (ha : 0 < a) (hb : b < 1) :
    ∃ n : ℕ, b ^ n < a := by
  simpa only [← coe_pow, NNReal.coe_lt_coe] using
    exists_pow_lt_of_lt_one (NNReal.coe_pos.2 ha) (NNReal.coe_lt_coe.2 hb)

nonrec theorem exists_mem_Ico_zpow {x : ℝ≥0} {y : ℝ≥0} (hx : x ≠ 0) (hy : 1 < y) :
    ∃ n : ℤ, x ∈ Set.Ico (y ^ n) (y ^ (n + 1)) :=
  exists_mem_Ico_zpow hx.bot_lt hy

nonrec theorem exists_mem_Ioc_zpow {x : ℝ≥0} {y : ℝ≥0} (hx : x ≠ 0) (hy : 1 < y) :
    ∃ n : ℤ, x ∈ Set.Ioc (y ^ n) (y ^ (n + 1)) :=
  exists_mem_Ioc_zpow hx.bot_lt hy

end Pow

section Sub

/-!
### Lemmas about subtraction

In this section we provide a few lemmas about subtraction that do not fit well into any other
typeclass. For lemmas about subtraction and addition see lemmas about `OrderedSub` in the file
`Mathlib/Algebra/Order/Sub/Basic.lean`. See also `mul_tsub` and `tsub_mul`.
-/

/-
**NNReal.sub_def** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：sub_def {r p : Real>=0} : r - p = Real.toNNReal (r - p)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Lemmas about subtraction

In this section we provide a few lemmas about subtraction that do not fit well i
nto any other
typeclass. For lemmas about subtraction and addition see lemmas about `OrderedSu
b` in the file
`Mathlib/Algebra/Order/Sub/Basic.lean`. See also `mul_tsub` and `tsub_mul`.
-/
theorem sub_def {r p : ℝ≥0} : r - p = Real.toNNReal (r - p) :=
  rfl
/-
**NNReal.coe_sub_def** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_sub_def {r p : Real>=0} : ↑(r - p) = max (r - p : Real) 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub_def {r p : ℝ≥0} : ↑(r - p) = max (r - p : ℝ) 0 :=
  rfl
/-
**NNReal.** 是 Mathlib 中的一个示例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : OrderedSub ℝ≥0 := by infer_instance

end Sub

section Inv

@[simp]
/-
**NNReal.inv_mk** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：inv_mk {r : Real} (hr : 0 <= r) : (NNReal.mk r hr)⁻¹ = .mk (r⁻¹) (inv_nonn
eg.2 hr)
参数：hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_mk {r : ℝ} (hr : 0 ≤ r) : (NNReal.mk r hr)⁻¹ = .mk (r⁻¹) (inv_nonneg.2 hr) := rfl

@[simp]
/-
**NNReal.inv_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：inv_le {r p : Real>=0} (h : r != 0) : r⁻¹ <= p ↔ 1 <= r * p
参数：h : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_le {r p : ℝ≥0} (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r * p := by
  rw [← mul_le_mul_iff_right₀ (pos_iff_ne_zero.2 h), mul_inv_cancel₀ h]
/-
**NNReal.inv_le_of_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：inv_le_of_le_mul {r p : Real>=0} (h : 1 <= r * p) : r⁻¹ <= p
参数：h : 1 <= r * p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem inv_le_of_le_mul {r p : ℝ≥0} (h : 1 ≤ r * p) : r⁻¹ ≤ p := by
  by_cases r = 0 <;> simp [*, inv_le]

@[simp]
/-
**NNReal.le_inv_iff_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：le_inv_iff_mul_le {r p : Real>=0} (h : p != 0) : r <= p⁻¹ ↔ r * p <= 1
参数：h : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_inv_iff_mul_le {r p : ℝ≥0} (h : p ≠ 0) : r ≤ p⁻¹ ↔ r * p ≤ 1 := by
  rw [← mul_le_mul_iff_right₀ (pos_iff_ne_zero.2 h), mul_inv_cancel₀ h, mul_comm]

@[simp]
/-
**NNReal.lt_inv_iff_mul_lt** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：lt_inv_iff_mul_lt {r p : Real>=0} (h : p != 0) : r < p⁻¹ ↔ r * p < 1
参数：h : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_right₀`：mul_lt_mul_iff_right₀ [PosMulStrictMono α] [PosMu
lReflectLT α] (a0 : 0 < a) : a * b < a * c ↔ b < c where mp h
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_inv_iff_mul_lt {r p : ℝ≥0} (h : p ≠ 0) : r < p⁻¹ ↔ r * p < 1 := by
  rw [← mul_lt_mul_iff_right₀ (pos_iff_ne_zero.2 h), mul_inv_cancel₀ h, mul_comm]
/-
**NNReal.div_le_of_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：div_le_of_le_mul {a b c : Real>=0} (h : a <= b * c) : a / c <= b
参数：h : a <= b * c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
-/
theorem div_le_of_le_mul {a b c : ℝ≥0} (h : a ≤ b * c) : a / c ≤ b :=
  if h0 : c = 0 then by simp [h0] else (div_le_iff₀ (pos_iff_ne_zero.2 h0)).2 h
/-
**NNReal.div_le_of_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：div_le_of_le_mul' {a b c : Real>=0} (h : a <= b * c) : a / b <= c
参数：h : a <= b * c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.div_le_of_le_mul`：div_le_of_le_mul {a b c : Real>=0} (h : a <= b 
* c) : a / c <= b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem div_le_of_le_mul' {a b c : ℝ≥0} (h : a ≤ b * c) : a / b ≤ c :=
  div_le_of_le_mul <| mul_comm b c ▸ h
/-
**NNReal.mul_lt_of_lt_div** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：mul_lt_of_lt_div {a b r : Real>=0} (h : a < b / r) : a * r < b
参数：h : a < b / r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
-/
theorem mul_lt_of_lt_div {a b r : ℝ≥0} (h : a < b / r) : a * r < b :=
  (lt_div_iff₀ <| pos_iff_ne_zero.2 fun hr => False.elim <| by simp [hr] at h).1 h
/-
**NNReal.le_of_forall_lt_one_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：le_of_forall_lt_one_mul_le {x y : Real>=0} (h : forall a < 1, a * x <= y) 
: x <= y
参数：h : forall a < 1, a * x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_lt_imp_le_of_dense`：∀ {α : Type u_2} [inst : LinearOrder α]
 [DenselyOrdered α] {a₁ a₂ : α}, (∀ a < a₂, a ≤ a₁) → a₂ ≤ a₁
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `inv_eq_zero`：inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.lt_inv_iff_mul_lt`：lt_inv_iff_mul_lt {r p : Real>=0} (h : p != 0)
 : r < p⁻¹ ↔ r * p < 1
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem le_of_forall_lt_one_mul_le {x y : ℝ≥0} (h : ∀ a < 1, a * x ≤ y) : x ≤ y :=
  le_of_forall_lt_imp_le_of_dense fun a ha => by
    have hx : x ≠ 0 := ha.ne_zero
    have hx' : x⁻¹ ≠ 0 := by rwa [Ne, inv_eq_zero]
    have : a * x⁻¹ < 1 := by rwa [← lt_inv_iff_mul_lt hx', inv_inv]
    have : a * x⁻¹ * x ≤ y := h _ this
    rwa [mul_assoc, inv_mul_cancel₀ hx, mul_one] at this

nonrec theorem half_le_self (a : ℝ≥0) : a / 2 ≤ a :=
  half_le_self bot_le

nonrec theorem half_lt_self {a : ℝ≥0} (h : a ≠ 0) : a / 2 < a :=
  half_lt_self h.bot_lt
/-
**NNReal.div_lt_one_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：div_lt_one_of_lt {a b : Real>=0} (h : a < b) : a / b < 1
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `LT.lt.bot_lt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → ⊥ < a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem div_lt_one_of_lt {a b : ℝ≥0} (h : a < b) : a / b < 1 := by
  rwa [div_lt_iff₀ h.bot_lt, one_mul]
/-
**NNReal._root_.Real.toNNReal_inv** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.toNNReal_inv {x : ℝ} : Real.toNNReal x⁻¹ = (Real.toNNReal x)⁻¹ := by
  rcases le_total 0 x with hx | hx
  · nth_rw 1 [← Real.coe_toNNReal x hx]
    rw [← NNReal.coe_inv, Real.toNNReal_coe]
  · rw [toNNReal_eq_zero.mpr hx, inv_zero, toNNReal_eq_zero.mpr (inv_nonpos.mpr hx)]
/-
**NNReal._root_.Real.toNNReal_div** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.toNNReal_div {x y : ℝ} (hx : 0 ≤ x) :
    Real.toNNReal (x / y) = Real.toNNReal x / Real.toNNReal y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.toNNReal_inv, ← Real.toNNReal_mul hx]
/-
**NNReal._root_.Real.toNNReal_div'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.toNNReal_div' {x y : ℝ} (hy : 0 ≤ y) :
    Real.toNNReal (x / y) = Real.toNNReal x / Real.toNNReal y := by
  rw [div_eq_inv_mul, div_eq_inv_mul, Real.toNNReal_mul (inv_nonneg.2 hy), Real.toNNReal_inv]
/-
**NNReal.inv_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：inv_lt_one_iff {x : Real>=0} (hx : x != 0) : x⁻¹ < 1 ↔ 1 < x
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_lt_one_iff {x : ℝ≥0} (hx : x ≠ 0) : x⁻¹ < 1 ↔ 1 < x := by
  rw [← one_div, div_lt_iff₀ hx.bot_lt, one_mul]
/-
**NNReal.inv_lt_inv** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：inv_lt_inv {x y : Real>=0} (hx : x != 0) (h : x < y) : y⁻¹ < x⁻¹
参数：hx : x != 0；h : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `inv_strictAnti₀`：inv_strictAnti₀ (hb : 0 < b) (hba : b < a) : a⁻¹ < b⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
theorem inv_lt_inv {x y : ℝ≥0} (hx : x ≠ 0) (h : x < y) : y⁻¹ < x⁻¹ :=
  inv_strictAnti₀ hx.bot_lt h
/-
**NNReal.exists_nat_pos_inv_lt** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：exists_nat_pos_inv_lt {b : Real>=0} (hb : 0 < b) : exists (n : Nat), 0 < n
 ∧ (n : Real>=0)⁻¹ < b
参数：hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.exists_nat_pos_inv_lt`：exists_nat_pos_inv_lt {b : Real} (hb : 0 < b
) : exists (n : Nat), 0 < n ∧ (n : Real)⁻¹ < b
-/
lemma exists_nat_pos_inv_lt {b : ℝ≥0} (hb : 0 < b) :
    ∃ (n : ℕ), 0 < n ∧ (n : ℝ≥0)⁻¹ < b :=
  b.toReal.exists_nat_pos_inv_lt hb

end Inv

@[simp]
/-
**NNReal.abs_eq** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：abs_eq (x : Real>=0) : |(x : Real)| = x
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem abs_eq (x : ℝ≥0) : |(x : ℝ)| = x :=
  abs_of_nonneg x.property

section Csupr

open Set

variable {ι : Sort*} {f : ι → ℝ≥0}

/-
**NNReal.le_toNNReal_of_coe_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：le_toNNReal_of_coe_le {x : Real>=0} {y : Real} (h : ↑x <= y) : x <= y.toNN
Real
参数：h : ↑x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.le_toNNReal_iff_coe_le`：le_toNNReal_iff_coe_le {r : Real>=0} {p : R
eal} (hp : 0 <= p) : r <= Real.toNNReal p ↔ ↑r <= p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem le_toNNReal_of_coe_le {x : ℝ≥0} {y : ℝ} (h : ↑x ≤ y) : x ≤ y.toNNReal :=
  (le_toNNReal_iff_coe_le <| x.2.trans h).2 h

nonrec theorem sSup_of_not_bddAbove {s : Set ℝ≥0} (hs : ¬BddAbove s) : SupSet.sSup s = 0 := by
  grind [csSup_of_not_bddAbove, csSup_empty, bot_eq_zero']
/-
**NNReal.iSup_of_not_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：iSup_of_not_bddAbove (hf : ¬BddAbove (range f)) : ⨆ i, f i = 0
参数：hf : ¬BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.sSup_of_not_bddAbove`：∀ {s : Set NNReal}, ¬BddAbove s → sSup s = 
0
-/
theorem iSup_of_not_bddAbove (hf : ¬BddAbove (range f)) : ⨆ i, f i = 0 :=
  sSup_of_not_bddAbove hf
/-
**NNReal.iSup_empty** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：iSup_empty [IsEmpty ι] (f : ι -> Real>=0) : ⨆ i, f i = 0
参数：f : ι -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
-/
theorem iSup_empty [IsEmpty ι] (f : ι → ℝ≥0) : ⨆ i, f i = 0 := ciSup_of_empty f
/-
**NNReal.iInf_empty** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：iInf_empty [IsEmpty ι] (f : ι -> Real>=0) : ⨅ i, f i = 0
参数：f : ι -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_of_isEmpty`：∀ {α : Type u_8} {ι : Sort u_9} [inst : InfSet α] [IsEm
pty ι] (f : ι → α), iInf f = sInf ∅
· 使用定理 `NNReal.sInf_empty`：sInf_empty : sInf (∅ : Set Real>=0) = 0
-/
theorem iInf_empty [IsEmpty ι] (f : ι → ℝ≥0) : ⨅ i, f i = 0 := by
  rw [_root_.iInf_of_isEmpty, sInf_empty]
/-
**NNReal.iSup_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {ι : Sort u_1} {f : ι → NNReal}, BddAbove (Set.range f) → (⨆ i, f i = 0 
↔ ∀ (i : ι), f i = 0)
参数：Set.range f；⨆ i, f i = 0 ↔ ∀ (i : ι), f i = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ciSup_le_iff`：ciSup_le_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddAb
ove (range f)) : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
@[simp] lemma iSup_eq_zero (hf : BddAbove (range f)) : ⨆ i, f i = 0 ↔ ∀ i, f i = 0 := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp [← bot_eq_zero', ← le_bot_iff, ciSup_le_iff hf]

@[simp]
/-
**NNReal.iInf_const_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：iInf_const_zero {α : Sort*} : ⨅ _ : α, (0 : Real>=0) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `NNReal.coe_iInf`：coe_iInf {ι : Sort*} (s : ι -> Real>=0) : (↑(⨅ i, s i) 
: Real) = ⨅ i, ↑(s i)
· 使用定理 `Real.iInf_const_zero`：iInf_const_zero : ⨅ _ : ι, (0 : Real) = 0
-/
theorem iInf_const_zero {α : Sort*} : ⨅ _ : α, (0 : ℝ≥0) = 0 := by
  rw [← coe_inj, coe_iInf]
  exact Real.iInf_const_zero

end Csupr

end NNReal

namespace Set

namespace OrdConnected

variable {s : Set ℝ} {t : Set ℝ≥0}

/-
**Set.OrdConnected.preimage_coe_nnreal_real** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdCo
nnected`。
形式化陈述：preimage_coe_nnreal_real (h : s.OrdConnected) : ((↑) ⁻¹' s : Set Real>=0).
OrdConnected
参数：h : s.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.preimage_mono`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Preorder α] [inst_1 : Preorder β] {s : Set α} {f : β → α},   s.OrdConnected → Mo
notone f → (f ⁻¹' s)…
· 使用定理 `NNReal.coe_mono`：Monotone NNReal.toReal
-/
theorem preimage_coe_nnreal_real (h : s.OrdConnected) : ((↑) ⁻¹' s : Set ℝ≥0).OrdConnected :=
  h.preimage_mono NNReal.coe_mono
/-
**Set.OrdConnected.image_coe_nnreal_real** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConne
cted`。
形式化陈述：image_coe_nnreal_real (h : t.OrdConnected) : ((↑) '' t : Set Real).OrdConn
ected
参数：h : t.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
-/
theorem image_coe_nnreal_real (h : t.OrdConnected) : ((↑) '' t : Set ℝ).OrdConnected :=
  ⟨forall_mem_image.2 fun x hx =>
      forall_mem_image.2 fun _y hy z hz => ⟨⟨z, x.2.trans hz.1⟩, h.out hx hy hz, rfl⟩⟩

-- TODO: does it generalize to a `GaloisInsertion`?
/-
**Set.OrdConnected.image_real_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnect
ed`。
形式化陈述：image_real_toNNReal (h : s.OrdConnected) : (Real.toNNReal '' s).OrdConnect
ed
参数：h : s.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.toNNReal_of_nonpos`：toNNReal_of_nonpos {r : Real} : r <= 0 -> Real.
toNNReal r = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.toNNReal_le_iff_le_coe`：toNNReal_le_iff_le_coe {r : Real} {p : Real
>=0} : toNNReal r <= p ↔ r <= ↑p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
-/
theorem image_real_toNNReal (h : s.OrdConnected) : (Real.toNNReal '' s).OrdConnected := by
  refine ⟨forall_mem_image.2 fun x hx => forall_mem_image.2 fun y hy z hz => ?_⟩
  rcases le_total y 0 with hy₀ | hy₀
  · rw [mem_Icc, Real.toNNReal_of_nonpos hy₀, nonpos_iff_eq_zero] at hz
    exact ⟨y, hy, (toNNReal_of_nonpos hy₀).trans hz.2.symm⟩
  · lift y to ℝ≥0 using hy₀
    rw [toNNReal_coe] at hz
    exact ⟨z, h.out hx hy ⟨toNNReal_le_iff_le_coe.1 hz.1, hz.2⟩, toNNReal_coe⟩
/-
**Set.OrdConnected.preimage_real_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConn
ected`。
形式化陈述：preimage_real_toNNReal (h : t.OrdConnected) : (Real.toNNReal ⁻¹' t).OrdCon
nected
参数：h : t.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.preimage_mono`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Preorder α] [inst_1 : Preorder β] {s : Set α} {f : β → α},   s.OrdConnected → Mo
notone f → (f ⁻¹' s)…
· 使用定理 `Real.toNNReal_monotone`：Monotone Real.toNNReal
-/
theorem preimage_real_toNNReal (h : t.OrdConnected) : (Real.toNNReal ⁻¹' t).OrdConnected :=
  h.preimage_mono Real.toNNReal_monotone

end OrdConnected

end Set

namespace Real

/-- The absolute value on `ℝ` as a map to `ℝ≥0`. -/
@[pp_nodot]
/-
**Real.nnabs** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：nnabs : Real ->*₀ Real>=0 where toFun x
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The absolute value on `ℝ` as a map to `ℝ≥0`.
-/
def nnabs : ℝ →*₀ ℝ≥0 where
  toFun x := ⟨|x|, abs_nonneg x⟩
  map_zero' := by simp; rfl
  map_one' := by simp; rfl
  map_mul' x y := by simp [abs_mul]; rfl

@[norm_cast, simp]
/-
**Real.coe_nnabs** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：coe_nnabs (x : Real) : (nnabs x : Real) = |x|
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nnabs (x : ℝ) : (nnabs x : ℝ) = |x| :=
  rfl

@[simp]
/-
**Real.nnabs_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：nnabs_of_nonneg {x : Real} (h : 0 <= x) : nnabs x = toNNReal x
参数：h : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用定理 `Real.coe_nnabs`：coe_nnabs (x : Real) : (nnabs x : Real) = |x|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem nnabs_of_nonneg {x : ℝ} (h : 0 ≤ x) : nnabs x = toNNReal x := by
  ext
  rw [coe_toNNReal x h, coe_nnabs, abs_of_nonneg h]
/-
**Real.nnabs_coe** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：nnabs_coe (x : Real>=0) : nnabs x = x
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.nnabs_of_nonneg`：nnabs_of_nonneg {x : Real} (h : 0 <= x) : nnabs x 
= toNNReal x
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnabs_coe (x : ℝ≥0) : nnabs x = x := by simp
/-
**Real.coe_toNNReal_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：coe_toNNReal_le (x : Real) : (toNNReal x : Real) <= |x|
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem coe_toNNReal_le (x : ℝ) : (toNNReal x : ℝ) ≤ |x| :=
  max_le (le_abs_self _) (abs_nonneg _)
/-
**Real.toNNReal_abs** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (x : ℝ), |x|.toNNReal = Real.nnabs x
参数：x : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.coe_injective`：Function.Injective NNReal.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toNNReal_abs (x : ℝ) : |x|.toNNReal = nnabs x := NNReal.coe_injective <| by simp
/-
**Real.nnabs_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (n : ℕ), Real.nnabs ↑n = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.nnabs_of_nonneg`：nnabs_of_nonneg {x : Real} (h : 0 <= x) : nnabs x 
= toNNReal x
· 使用定理 `Real.toNNReal_natCast`：∀ (n : ℕ), (↑n).toNNReal = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp high] lemma nnabs_natCast (n : ℕ) : nnabs n = n := by simp
/-
**Real.nnabs_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], Real.nnabs (OfNat.ofNat n) = OfNat.ofNat 
n
参数：n : ℕ；OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.nnabs_of_nonneg`：nnabs_of_nonneg {x : Real} (h : 0 <= x) : nnabs x 
= toNNReal x
· 使用定理 `Real.toNNReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).to
NNReal = OfNat.ofNat n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp high] lemma nnabs_ofNat (n : ℕ) [n.AtLeastTwo] : nnabs ofNat(n) = ofNat(n) := by simp
/-
**Real.cast_natAbs_eq_nnabs_cast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cast_natAbs_eq_nnabs_cast (n : Int) : (n.natAbs : Real>=0) = nnabs n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用定理 `Real.coe_nnabs`：coe_nnabs (x : Real) : (nnabs x : Real) = |x|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
-/
theorem cast_natAbs_eq_nnabs_cast (n : ℤ) : (n.natAbs : ℝ≥0) = nnabs n := by
  ext
  rw [NNReal.coe_natCast, Nat.cast_natAbs, Real.coe_nnabs, Int.cast_abs]

@[simp]
/-
**Real.nnabs_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：nnabs_pos {x : Real} : 0 < x.nnabs ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nnabs_pos {x : ℝ} : 0 < x.nnabs ↔ x ≠ 0 := by simp [← NNReal.coe_pos]

/-- Every real number nonnegative or nonpositive, phrased using `ℝ≥0`. -/
/-
**Real.nnreal_dichotomy** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：nnreal_dichotomy (r : Real) : exists x : Real>=0, r = x ∨ r = -x
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
Every real number nonnegative or nonpositive, phrased using `ℝ≥0`.
-/
lemma nnreal_dichotomy (r : ℝ) : ∃ x : ℝ≥0, r = x ∨ r = -x := by
  obtain (hr | hr) : 0 ≤ r ∨ 0 ≤ -r := by simpa using le_total ..
  all_goals
    rw [← neg_neg r]
    lift (_ : ℝ) to ℝ≥0 using hr with r
    aesop

/-- Every real number is either zero, positive or negative, phrased using `ℝ≥0`. -/
/-
**Real.nnreal_trichotomy** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：nnreal_trichotomy (r : Real) : r = 0 ∨ exists x : Real>=0, 0 < x ∧ (r = x 
∨ r = -x)
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.nnreal_dichotomy`：nnreal_dichotomy (r : Real) : exists x : Real>=0,
 r = x ∨ r = -x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Every real number is either zero, positive or negative, phrased using `ℝ≥0`.
-/
lemma nnreal_trichotomy (r : ℝ) : r = 0 ∨ ∃ x : ℝ≥0, 0 < x ∧ (r = x ∨ r = -x) := by
  obtain ⟨x, hx⟩ := nnreal_dichotomy r
  rw [or_iff_not_imp_left]
  aesop (add simp pos_iff_ne_zero)

/-- To prove a property holds for real numbers it suffices to show that it holds for `x : ℝ≥0`,
and if it holds for `x : ℝ≥0`, then it does also for `(-↑x : ℝ)`. -/
@[elab_as_elim]
/-
**Real.nnreal_induction_on** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：nnreal_induction_on {motive : Real -> Prop} (nonneg : forall x : Real>=0, 
motive x) (nonpos : forall x : Real>=0, motive x -> motive (-x)) (r : Real) : mo
tive r
参数：nonneg : forall x : Real>=0, motive x；nonpos : forall x : Real>=0, motive x -
> motive (-x)；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.nnreal_dichotomy`：nnreal_dichotomy (r : Real) : exists x : Real>=0,
 r = x ∨ r = -x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
To prove a property holds for real numbers it suffices to show that it holds for
 `x : ℝ≥0`,
and if it holds for `x : ℝ≥0`, then it does also for `(-↑x : ℝ)`.
-/
lemma nnreal_induction_on {motive : ℝ → Prop} (nonneg : ∀ x : ℝ≥0, motive x)
    (nonpos : ∀ x : ℝ≥0, motive x → motive (-x)) (r : ℝ) : motive r := by
  obtain ⟨r, (rfl | rfl)⟩ := r.nnreal_dichotomy
  all_goals simp_all

/-- A version of `nnreal_induction_on` which splits into three cases (zero, positive and negative)
instead of two. -/
@[elab_as_elim]
/-
**Real.nnreal_induction_on'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：nnreal_induction_on' {motive : Real -> Prop} (zero : motive 0) (pos : fora
ll x : Real>=0, 0 < x -> motive x) (neg : forall x : Real>=0, 0 < x -> motive x 
-> motive (-x)) (r : Real) : motive r
参数：zero : motive 0；pos : forall x : Real>=0, 0 < x -> motive x；neg : forall x : 
Real>=0, 0 < x -> motive x -> motive (-x)；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.nnreal_trichotomy`：nnreal_trichotomy (r : Real) : r = 0 ∨ exists x 
: Real>=0, 0 < x ∧ (r = x ∨ r = -x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
A version of `nnreal_induction_on` which splits into three cases (zero, positive
 and negative)
instead of two.
-/
lemma nnreal_induction_on' {motive : ℝ → Prop} (zero : motive 0) (pos : ∀ x : ℝ≥0, 0 < x → motive x)
    (neg : ∀ x : ℝ≥0, 0 < x → motive x → motive (-x)) (r : ℝ) : motive r := by
  obtain rfl | ⟨r, hr, (rfl | rfl)⟩ := r.nnreal_trichotomy
  all_goals simp_all

end Real

section StrictMono

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- If `Γ₀ˣ` is nontrivial and `f : Γ₀ →*₀ ℝ≥0` is strictly monotone, then for any positive
  `r : ℝ≥0`, there exists `d : Γ₀ˣ` with `f d < r`. -/
/-
**NNReal.exists_lt_of_strictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NNReal.exists_lt_of_strictMono [h : Nontrivial Γ₀ˣ] {f : Γ₀ ->*₀ Real>=0} 
(hf : StrictMono f) {r : Real>=0} (hr : 0 < r) : exists d : Γ₀ˣ, f d < r
参数：hf : StrictMono f；hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nontrivial_iff_exists_ne`：nontrivial_iff_exists_ne (x : α) : Nontrivial 
α ↔ exists y, y != x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `map_eq_zero`：map_eq_zero : f a = 0 ↔ a = 0
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `NNReal.inv_lt_one_iff`：inv_lt_one_iff {x : Real>=0} (hx : x != 0) : x⁻¹ 
< 1 ↔ 1 < x
· 使用定理 `NNReal.exists_pow_lt_of_lt_one`：∀ {a b : NNReal}, 0 < a → b < 1 → ∃ n, b
 ^ n < a
· 使用引理 `Units.val_pow_eq_pow_val`：val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^
 n : α)
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …

--- 原说明 ---
If `Γ₀ˣ` is nontrivial and `f : Γ₀ →*₀ ℝ≥0` is strictly monotone, then for any p
ositive
  `r : ℝ≥0`, there exists `d : Γ₀ˣ` with `f d < r`.
-/
theorem NNReal.exists_lt_of_strictMono [h : Nontrivial Γ₀ˣ] {f : Γ₀ →*₀ ℝ≥0} (hf : StrictMono f)
    {r : ℝ≥0} (hr : 0 < r) : ∃ d : Γ₀ˣ, f d < r := by
  obtain ⟨g, hg1⟩ := (nontrivial_iff_exists_ne (1 : Γ₀ˣ)).mp h
  set u : Γ₀ˣ := if g < 1 then g else g⁻¹ with hu
  have hfu : f u < 1 := by
    rw [hu]
    split_ifs with hu1
    · rw [← map_one f]; exact hf hu1
    · have hfg0 : f g ≠ 0 :=
        fun h0 ↦ (Units.ne_zero g) ((map_eq_zero f).mp h0)
      have hg1' : 1 < g := lt_of_le_of_ne (not_lt.mp hu1) hg1.symm
      rw [Units.val_inv_eq_inv_val, map_inv₀, inv_lt_one_iff hfg0, ← map_one f]
      exact hf hg1'
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hfu
  use u ^ n
  rwa [Units.val_pow_eq_pow_val, map_pow]

/-- If `Γ₀ˣ` is nontrivial and `f : Γ₀ →*₀ ℝ≥0` is strictly monotone, then for any positive
  real `r`, there exists `d : Γ₀ˣ` with `f d < r`. -/
/-
**Real.exists_lt_of_strictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.exists_lt_of_strictMono [h : Nontrivial Γ₀ˣ] {f : Γ₀ ->*₀ Real>=0} (h
f : StrictMono f) {r : Real} (hr : 0 < r) : exists d : Γ₀ˣ, (f d : Real) < r
参数：hf : StrictMono f；hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NNReal.exists_lt_of_strictMono`：NNReal.exists_lt_of_strictMono [h : Nont
rivial Γ₀ˣ] {f : Γ₀ ->*₀ Real>=0} (hf : StrictMono f) {r : Real>=0} (hr : 0 < r)
 : exists d : Γ₀ˣ, f…

--- 原说明 ---
If `Γ₀ˣ` is nontrivial and `f : Γ₀ →*₀ ℝ≥0` is strictly monotone, then for any p
ositive
  real `r`, there exists `d : Γ₀ˣ` with `f d < r`.
-/
theorem Real.exists_lt_of_strictMono [h : Nontrivial Γ₀ˣ] {f : Γ₀ →*₀ ℝ≥0} (hf : StrictMono f)
    {r : ℝ} (hr : 0 < r) : ∃ d : Γ₀ˣ, (f d : ℝ) < r := by
  set s : NNReal := ⟨r, le_of_lt hr⟩
  have hs : 0 < s := hr
  exact NNReal.exists_lt_of_strictMono hf hs

end StrictMono

/-- While not very useful, this instance uses the same representation as `Real.instRepr`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
While not very useful, this instance uses the same representation as `Real.instR
epr`.
-/
unsafe instance : Repr ℝ≥0 where
  reprPrec r _ := f!"({repr r.val}).toNNReal"

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

alias ⟨_, nnreal_coe_pos⟩ := coe_pos

/-- Extension for the `positivity` tactic: cast from `ℝ≥0` to `ℝ`. -/
@[positivity NNReal.toReal _]
meta def evalNNRealtoReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(NNReal.toReal $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(nnreal_coe_pos $pa))
    | _ => pure (.nonnegative q(NNReal.coe_nonneg $a))
  | _, _, _ => throwError "not NNReal.toReal"

/-- Extension for the `positivity` tactic: `Real.toNNReal` -/
@[positivity Real.toNNReal _]
meta def evalRealToNNReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ≥0), ~q(Real.toNNReal $a) =>
    assertInstancesCommute
    match (← core q(inferInstance) (some q(inferInstance)) a) with
    | .positive pa => pure (.positive q(toNNReal_pos.mpr $pa))
    | _ => failure
  | _, _, _ => throwError "not Real.toNNReal"

alias ⟨_, nnabs_pos_of_pos⟩ := Real.nnabs_pos

/-- Extension for the `positivity` tactic: `Real.nnabs` -/
@[positivity Real.nnabs _]
meta def evalRealNNAbs : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ≥0), ~q(Real.nnabs $a) =>
    assertInstancesCommute
    match (← core q(inferInstance) (some q(inferInstance)) a).toNonzero with
    | some pa => pure (.positive q(nnabs_pos_of_pos $pa))
    | _ => failure
  | _, _, _ => throwError "not Real.nnabs"

end Mathlib.Meta.Positivity

