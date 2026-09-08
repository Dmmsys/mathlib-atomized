/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Adam Topaz
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Order.Filter.Bases.Basic

/-!

# Valuative Relations

In this file we introduce a class called `ValuativeRel R` for a ring `R`.
This bundles a relation `vle : R → R → Prop` on `R` which mimics a
preorder on `R` arising from a valuation.
We introduce the notation `x ≤ᵥ y` for this relation.

Recall that the equivalence class of a valuation is *completely* characterized by
such a preorder. Thus, we can think of `ValuativeRel R` as a way of
saying that `R` is endowed with an equivalence class of valuations.

## Main Definitions

- `ValuativeRel R` endows a semiring `R` with a relation "arising from a valuation". When `R` is a
  ring, this is equivalent to fixing an equivalence class of valuations on `R`.
  Use the notation `x ≤ᵥ y` for this relation.
- `ValuativeRel.valuation R` is the "canonical" valuation associated to `ValuativeRel R`,
  taking values in `ValuativeRel.ValueGroupWithZero R`.
- Given a valuation `v` on `R` and an instance `[ValuativeRel R]`, writing `[v.Compatible]`
  ensures that the relation `x ≤ᵥ y` is equivalent to `v x ≤ v y`. Note that
  it is possible to have `[v.Compatible]` and `[w.Compatible]` for two different valuations on `R`.
- Given `[ValuativeRel A]`, `[ValuativeRel B]` and `[Algebra A B]`, the class
  `[ValuativeExtension A B]` ensures that the algebra map `A → B` is compatible with the valuations
  on `A` and `B`. For example, this can be used to talk about extensions of valued fields.


## Remark

The last two axioms in `ValuativeRel`, namely `vle_mul_cancel` and `not_vle_one_zero`, are
used to ensure that we have a well-behaved valuation taking values in a *value group* (with zero).
In principle, it should be possible to drop these two axioms and obtain a value monoid,
however, such a value monoid would not necessarily embed into an ordered abelian group with zero.
Similarly, without these axioms, the support of the valuation need not be a prime ideal.
We have thus opted to include these two axioms and obtain a `ValueGroupWithZero` associated to
a `ValuativeRel` in order to best align with the literature about valuations on commutative rings.

Future work could refactor `ValuativeRel` by dropping the `vle_mul_cancel` and `not_vle_one_zero`
axioms, opting to make these mixins instead.

## Projects

The `ValuativeRel` class should eventually replace the existing `Valued` typeclass.
Once such a refactor happens, `ValuativeRel` could be renamed to `Valued`.

## TODO
Split this file. For instance, the universal properties of `ValueGroupWithZero` and definition of
`IsRankLeOne` could be separated out.
-/

@[expose] public section

noncomputable section

/-- The class `[ValuativeRel R]` class introduces an operator `x ≤ᵥ y : Prop` for `x y : R`
which is the natural relation arising from (the equivalence class of) a valuation on `R` when `R`
is a ring. More precisely, if `v` is a valuation on `R` then the associated relation is
`x ≤ᵥ y ↔ v x ≤ v y`. Use this class to talk about the case where `R` is equipped
with an equivalence class of valuations. -/
@[ext]
/-
**ValuativeRel** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [Semiring R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class `[ValuativeRel R]` class introduces an operator `x ≤ᵥ y : Prop` for `x
 y : R`
which is the natural relation arising from (the equivalence class of) a valuatio
n on `R` when `R`
is a ring. More precisely, if `v` is a valuation on `R` then the associated rela
tion is
`x ≤ᵥ y ↔ v x ≤ v y`. Use this class to talk about the case where `R` is equippe
d
with an equivalence class of valuations.
-/
class ValuativeRel (R : Type*) [Semiring R] where
  /-- The valuation less-equal operator arising from `ValuativeRel`. -/
  vle : R → R → Prop
  vle_total (x y) : vle x y ∨ vle y x
  vle_trans {z y x} : vle x y → vle y z → vle x z
  vle_add {x y z} : vle x z → vle y z → vle (x + y) z
  mul_vle_mul_left {x y} (h : vle x y) (z) : vle (x * z) (y * z)
  vle_mul_cancel {x y z} : ¬ vle z 0 → vle (x * z) (y * z) → vle x y
  not_vle_one_zero : ¬ vle 1 0
  vle_mul_comm {x y} : vle (x * y) (y * x)

@[inherit_doc] infix:50 " ≤ᵥ " => ValuativeRel.vle

macro_rules | `($a ≤ᵥ $b) => `(binrel% ValuativeRel.vle $a $b)

namespace Valuation

variable {R Γ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ]
  (v : Valuation R Γ)

/-- We say that a valuation `v` is `Compatible` if the relation `x ≤ᵥ y`
is equivalent to `v x ≤ v y`. -/
/-
**Valuation.Compatible** 是 Mathlib 中的一个归纳类型，位于命名空间 `Valuation`。
形式化陈述：{R : Type u_1} →   {Γ : Type u_2} →     [inst : Ring R] → [inst_1 : Linear
OrderedCommMonoidWithZero Γ] → Valuation R Γ → [ValuativeRel R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a valuation `v` is `Compatible` if the relation `x ≤ᵥ y`
is equivalent to `v x ≤ v y`.
-/
class Compatible [ValuativeRel R] where
  vle_iff_le (x y : R) : x ≤ᵥ y ↔ v x ≤ v y

end Valuation

/-- A preorder on a ring is said to be "valuative" if it agrees with the
valuative relation. -/
/-
**ValuativePreorder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [inst : Semiring R] → [ValuativeRel R] → [Preorder R] → P
rop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preorder on a ring is said to be "valuative" if it agrees with the
valuative relation.
-/
class ValuativePreorder (R : Type*) [Semiring R] [ValuativeRel R] [Preorder R] where
  vle_iff_le (x y : R) : x ≤ᵥ y ↔ x ≤ y

namespace ValuativeRel

variable {R : Type*} [Semiring R] [ValuativeRel R] {x x' y y' z : R}

/-- The valuation less-than relation, defined as `x <ᵥ y ↔ ¬ y ≤ᵥ x`. -/
/-
**ValuativeRel.vlt** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel`。
形式化陈述：vlt (x y : R) : Prop
参数：x y : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation less-than relation, defined as `x <ᵥ y ↔ ¬ y ≤ᵥ x`.
-/
def vlt (x y : R) : Prop := ¬ y ≤ᵥ x

@[inherit_doc] infix:50 " <ᵥ " => ValuativeRel.vlt

macro_rules | `($a <ᵥ $b) => `(binrel% ValuativeRel.vlt $a $b)

/-- The valuation equals relation, defined as `x =ᵥ y ↔ x ≤ᵥ y ∧ y ≤ᵥ x`. -/
/-
**ValuativeRel.veq** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel`。
形式化陈述：veq : R -> R -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation equals relation, defined as `x =ᵥ y ↔ x ≤ᵥ y ∧ y ≤ᵥ x`.
-/
def veq : R → R → Prop := AntisymmRel (· ≤ᵥ ·)

@[inherit_doc] infix:50 " =ᵥ " => ValuativeRel.veq
/-
**ValuativeRel.veq_mul_comm** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：veq_mul_comm (x y : R) : x * y =ᵥ y * x
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle_mul_comm`：∀ {R : Type u_1} {inst : Semiring R} [self : 
ValuativeRel R] {x y : R}, x * y ≤ᵥ y * x
-/
lemma veq_mul_comm (x y : R) : x * y =ᵥ y * x := ⟨vle_mul_comm, vle_mul_comm⟩

macro_rules | `($a =ᵥ $b) => `(binrel% ValuativeRel.veq $a $b)
/-
**ValuativeRel.not_vle** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {x y : R}, 
¬x ≤ᵥ y ↔ y <ᵥ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, grind =] lemma not_vle : ¬ x ≤ᵥ y ↔ y <ᵥ x := .rfl
/-
**ValuativeRel.not_vlt** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {x y : R}, 
¬x <ᵥ y ↔ y ≤ᵥ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `ValuativeRel.not_vle`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x y : R}, ¬x ≤ᵥ y ↔ y <ᵥ x
-/
@[simp, grind =] lemma not_vlt : ¬ x <ᵥ y ↔ y ≤ᵥ x := not_vle.not_left
/-
**ValuativeRel.veq_def** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：veq_def : x =ᵥ y ↔ x <=ᵥ y ∧ y <=ᵥ x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma veq_def : x =ᵥ y ↔ x ≤ᵥ y ∧ y ≤ᵥ x := .rfl

protected alias ⟨_, vle.not_vlt⟩ := not_vlt
protected alias ⟨_, vlt.not_vle⟩ := not_vle
/-
**ValuativeRel.veq_comm** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：veq_comm : x =ᵥ y ↔ y =ᵥ x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antisymmRel_comm`：antisymmRel_comm : AntisymmRel r a b ↔ AntisymmRel r b
 a
-/
lemma veq_comm : x =ᵥ y ↔ y =ᵥ x := antisymmRel_comm
@[symm] protected alias ⟨veq.symm, _⟩ := veq_comm
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Symm R (· =ᵥ ·) where
  symm _ _ := veq.symm
/-
**ValuativeRel.vle_of_veq** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：vle_of_veq (h : x =ᵥ y) : x <=ᵥ y
参数：h : x =ᵥ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma vle_of_veq (h : x =ᵥ y) : x ≤ᵥ y := h.1
/-
**ValuativeRel.vge_of_veq** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：vge_of_veq (h : x =ᵥ y) : y <=ᵥ x
参数：h : x =ᵥ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma vge_of_veq (h : x =ᵥ y) : y ≤ᵥ x := h.2

protected alias veq.vle := vle_of_veq
protected alias veq.vge := vge_of_veq
/-
**ValuativeRel.not_vlt_of_veq** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：not_vlt_of_veq (h : x =ᵥ y) : ¬ x <ᵥ y
参数：h : x =ᵥ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle.not_vlt`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 :
 ValuativeRel R] {x y : R}, y ≤ᵥ x → ¬x <ᵥ y
· 使用定理 `ValuativeRel.veq.vge`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x y : R}, x =ᵥ y → y ≤ᵥ x
-/
lemma not_vlt_of_veq (h : x =ᵥ y) : ¬ x <ᵥ y := h.vge.not_vlt
/-
**ValuativeRel.not_vgt_of_veq** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：not_vgt_of_veq (h : x =ᵥ y) : ¬ y <ᵥ x
参数：h : x =ᵥ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle.not_vlt`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 :
 ValuativeRel R] {x y : R}, y ≤ᵥ x → ¬x <ᵥ y
· 使用定理 `ValuativeRel.veq.vle`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x y : R}, x =ᵥ y → x ≤ᵥ y
-/
lemma not_vgt_of_veq (h : x =ᵥ y) : ¬ y <ᵥ x := h.vle.not_vlt

protected alias veq.not_vlt := not_vlt_of_veq
protected alias veq.not_vgt := not_vgt_of_veq
/-
**ValuativeRel.vle_refl** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] (x : R), x 
≤ᵥ x
参数：x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_self_iff`：∀ {a : Prop}, a ∨ a ↔ a
· 使用定理 `ValuativeRel.vle_total`：∀ {R : Type u_1} {inst : Semiring R} [self : Val
uativeRel R] (x y : R), x ≤ᵥ y ∨ y ≤ᵥ x
-/
@[simp, refl] lemma vle_refl (x : R) : x ≤ᵥ x := or_self_iff.1 <| vle_total x x
/-
**ValuativeRel.vle_rfl** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：vle_rfl : x <=ᵥ x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle_refl`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Va
luativeRel R] (x : R), x ≤ᵥ x
-/
lemma vle_rfl : x ≤ᵥ x := vle_refl x

protected alias vle.refl := vle_refl
protected alias vle.rfl := vle_rfl
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Refl R (· ≤ᵥ ·) where
  refl _ := vle_rfl
/-
**ValuativeRel.veq_refl** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] (x : R), x 
=ᵥ x
参数：x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AntisymmRel.rfl`：AntisymmRel.rfl [Std.Refl r] {a : α} : AntisymmRel r a 
a
· 使用定理 `ValuativeRel.instReflVle`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 :
 ValuativeRel R], Std.Refl fun x1 x2 => x1 ≤ᵥ x2
-/
@[simp, refl] lemma veq_refl (x : R) : x =ᵥ x := AntisymmRel.rfl
/-
**ValuativeRel.veq_rfl** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：veq_rfl : x =ᵥ x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.veq_refl`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Va
luativeRel R] (x : R), x =ᵥ x
-/
lemma veq_rfl : x =ᵥ x := veq_refl x

protected alias veq.refl := veq_refl
protected alias veq.rfl := veq_rfl
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Refl R (· =ᵥ ·) where
  refl _ := veq_rfl

@[simp]
/-
**ValuativeRel.zero_vle** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel`。
形式化陈述：zero_vle (x : R) : 0 <=ᵥ x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ValuativeRel.mul_vle_mul_left`：∀ {R : Type u_1} {inst : Semiring R} [sel
f : ValuativeRel R] {x y : R}, x ≤ᵥ y → ∀ (z : R), x * z ≤ᵥ y * z
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `ValuativeRel.vle_total`：∀ {R : Type u_1} {inst : Semiring R} [self : Val
uativeRel R] (x y : R), x ≤ᵥ y ∨ y ≤ᵥ x
· 使用定理 `ValuativeRel.not_vle_one_zero`：∀ {R : Type u_1} {inst : Semiring R} [sel
f : ValuativeRel R], ¬1 ≤ᵥ 0
-/
theorem zero_vle (x : R) : 0 ≤ᵥ x := by
  simpa using mul_vle_mul_left ((vle_total 0 1).resolve_right not_vle_one_zero) x

@[simp]
/-
**ValuativeRel.not_vlt_zero** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel`。
形式化陈述：not_vlt_zero (x : R) : ¬ x <ᵥ 0
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem not_vlt_zero (x : R) : ¬ x <ᵥ 0 := by
  simp
/-
**ValuativeRel.vlt.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel.vlt`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {x y : R}, 
x <ᵥ y → y ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.not_vlt_zero`：not_vlt_zero (x : R) : ¬ x <ᵥ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem vlt.ne_zero (h : x <ᵥ y) : y ≠ 0 := by
  rintro rfl; exact not_vlt_zero _ h

@[simp]
/-
**ValuativeRel.zero_vlt_one** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：zero_vlt_one : (0 : R) <ᵥ 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.not_vle_one_zero`：∀ {R : Type u_1} {inst : Semiring R} [sel
f : ValuativeRel R], ¬1 ≤ᵥ 0
-/
lemma zero_vlt_one : (0 : R) <ᵥ 1 :=
  not_vle_one_zero

@[deprecated mul_vle_mul_left (since := "2026-01-06")]
/-
**ValuativeRel.vle_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：vle_mul_right (z) (h : x <=ᵥ y) : x * z <=ᵥ y * z
参数：z；h : x <=ᵥ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.mul_vle_mul_left`：∀ {R : Type u_1} {inst : Semiring R} [sel
f : ValuativeRel R] {x y : R}, x ≤ᵥ y → ∀ (z : R), x * z ≤ᵥ y * z
-/
lemma vle_mul_right (z) (h : x ≤ᵥ y) : x * z ≤ᵥ y * z :=
  mul_vle_mul_left h z
/-
**ValuativeRel.mul_vle_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：mul_vle_mul_right (h : x <=ᵥ y) (z) : z * x <=ᵥ z * y
参数：h : x <=ᵥ y；z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle_trans`：∀ {R : Type u_1} {inst : Semiring R} [self : Val
uativeRel R] {z y x : R}, x ≤ᵥ y → y ≤ᵥ z → x ≤ᵥ z
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `ValuativeRel.veq_mul_comm`：veq_mul_comm (x y : R) : x * y =ᵥ y * x
· 使用定理 `ValuativeRel.mul_vle_mul_left`：∀ {R : Type u_1} {inst : Semiring R} [sel
f : ValuativeRel R] {x y : R}, x ≤ᵥ y → ∀ (z : R), x * z ≤ᵥ y * z
-/
lemma mul_vle_mul_right (h : x ≤ᵥ y) (z) : z * x ≤ᵥ z * y :=
  vle_trans (veq_mul_comm _ _).1 (vle_trans (mul_vle_mul_left h z) ((veq_mul_comm _ _).1))
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans R R R vle vle vle where
  trans := vle_trans

protected alias vle.trans := vle_trans
/-
**ValuativeRel.vle_trans'** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：vle_trans' (h1 : y <=ᵥ z) (h2 : x <=ᵥ y) : x <=ᵥ z
参数：h1 : y <=ᵥ z；h2 : x <=ᵥ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle.trans`：∀ {R : Type u_1} {inst : Semiring R} [self : Val
uativeRel R] {z y x : R}, x ≤ᵥ y → y ≤ᵥ z → x ≤ᵥ z
-/
lemma vle_trans' (h1 : y ≤ᵥ z) (h2 : x ≤ᵥ y) : x ≤ᵥ z :=
  h2.trans h1

protected alias vle.trans' := vle_trans'
/-
**ValuativeRel.veq_trans** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：veq_trans (h1 : x =ᵥ y) (h2 : y =ᵥ z) : x =ᵥ z
参数：h1 : x =ᵥ y；h2 : y =ᵥ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.trans`：AntisymmRel.trans [IsTrans α r] (hab : AntisymmRel r 
a b) (hbc : AntisymmRel r b c) : AntisymmRel r a c
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
-/
lemma veq_trans (h1 : x =ᵥ y) (h2 : y =ᵥ z) : x =ᵥ z :=
  AntisymmRel.trans h1 h2
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans R R R veq veq veq where
  trans := veq_trans
/-
**ValuativeRel.vle_of_veq_of_vle** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：vle_of_veq_of_vle (h1 : x =ᵥ y) (h2 : y <=ᵥ z) : x <=ᵥ z
参数：h1 : x =ᵥ y；h2 : y <=ᵥ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle.trans`：∀ {R : Type u_1} {inst : Semiring R} [self : Val
uativeRel R] {z y x : R}, x ≤ᵥ y → y ≤ᵥ z → x ≤ᵥ z
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma vle_of_veq_of_vle (h1 : x =ᵥ y) (h2 : y ≤ᵥ z) : x ≤ᵥ z :=
  h1.1.trans h2
/-
**ValuativeRel.vle_of_vle_of_veq** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：vle_of_vle_of_veq (h1 : x <=ᵥ y) (h2 : y =ᵥ z) : x <=ᵥ z
参数：h1 : x <=ᵥ y；h2 : y =ᵥ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle.trans`：∀ {R : Type u_1} {inst : Semiring R} [self : Val
uativeRel R] {z y x : R}, x ≤ᵥ y → y ≤ᵥ z → x ≤ᵥ z
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma vle_of_vle_of_veq (h1 : x ≤ᵥ y) (h2 : y =ᵥ z) : x ≤ᵥ z :=
  h1.trans h2.1
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans R R R veq vle vle where
  trans := vle_of_veq_of_vle
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans R R R vle veq vle where
  trans := vle_of_vle_of_veq
/-
**ValuativeRel.vlt_of_vlt_of_vle** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：vlt_of_vlt_of_vle (h1 : x <ᵥ y) (h2 : y <=ᵥ z) : x <ᵥ z
参数：h1 : x <ᵥ y；h2 : y <=ᵥ z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle_trans`：∀ {R : Type u_1} {inst : Semiring R} [self : Val
uativeRel R] {z y x : R}, x ≤ᵥ y → y ≤ᵥ z → x ≤ᵥ z
-/
lemma vlt_of_vlt_of_vle (h1 : x <ᵥ y) (h2 : y ≤ᵥ z) : x <ᵥ z :=
  fun h ↦ (h1 (vle_trans h2 h)).elim

alias vlt.trans_vle := vlt_of_vlt_of_vle
/-
**ValuativeRel.vlt_of_vle_of_vlt** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：vlt_of_vle_of_vlt (h1 : x <=ᵥ y) (h2 : y <ᵥ z) : x <ᵥ z
参数：h1 : x <=ᵥ y；h2 : y <ᵥ z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle_trans`：∀ {R : Type u_1} {inst : Semiring R} [self : Val
uativeRel R] {z y x : R}, x ≤ᵥ y → y ≤ᵥ z → x ≤ᵥ z
-/
lemma vlt_of_vle_of_vlt (h1 : x ≤ᵥ y) (h2 : y <ᵥ z) : x <ᵥ z :=
  fun h ↦ (h2 (vle_trans h h1)).elim

alias vle.trans_vlt := vlt_of_vle_of_vlt
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans R R R vlt vle vlt where
  trans := vlt_of_vlt_of_vle
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans R R R vle vlt vlt where
  trans := vlt_of_vle_of_vlt
/-
**ValuativeRel.vlt.vle** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel.vlt`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {x y : R}, 
x <ᵥ y → x ≤ᵥ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `ValuativeRel.vle_total`：∀ {R : Type u_1} {inst : Semiring R} [self : Val
uativeRel R] (x y : R), x ≤ᵥ y ∨ y ≤ᵥ x
-/
lemma vlt.vle (h : x <ᵥ y) : x ≤ᵥ y :=
  (vle_total _ _).resolve_right h
/-
**ValuativeRel.vlt.trans** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel.vlt`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {x y z : R}
, x <ᵥ y → y <ᵥ z → x <ᵥ z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vlt.trans_vle`：∀ {R : Type u_1} [inst : Semiring R] [inst_1
 : ValuativeRel R] {x y z : R}, x <ᵥ y → y ≤ᵥ z → x <ᵥ z
· 使用定理 `ValuativeRel.vlt.vle`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x y : R}, x <ᵥ y → x ≤ᵥ y
-/
lemma vlt.trans (h1 : x <ᵥ y) (h2 : y <ᵥ z) : x <ᵥ z :=
  h1.trans_vle h2.vle
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans R R R vlt vlt vlt where
  trans := vlt.trans
/-
**ValuativeRel.vlt_of_veq_of_vlt** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：vlt_of_veq_of_vlt (h1 : x =ᵥ y) (h2 : y <ᵥ z) : x <ᵥ z
参数：h1 : x =ᵥ y；h2 : y <ᵥ z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle.trans_vlt`：∀ {R : Type u_1} [inst : Semiring R] [inst_1
 : ValuativeRel R] {x y z : R}, x ≤ᵥ y → y <ᵥ z → x <ᵥ z
· 使用定理 `ValuativeRel.veq.vle`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x y : R}, x =ᵥ y → x ≤ᵥ y
-/
lemma vlt_of_veq_of_vlt (h1 : x =ᵥ y) (h2 : y <ᵥ z) : x <ᵥ z :=
  h1.vle.trans_vlt h2
/-
**ValuativeRel.vlt_of_vlt_of_veq** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：vlt_of_vlt_of_veq (h1 : x <ᵥ y) (h2 : y =ᵥ z) : x <ᵥ z
参数：h1 : x <ᵥ y；h2 : y =ᵥ z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vlt.trans_vle`：∀ {R : Type u_1} [inst : Semiring R] [inst_1
 : ValuativeRel R] {x y z : R}, x <ᵥ y → y ≤ᵥ z → x <ᵥ z
· 使用定理 `ValuativeRel.veq.vle`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x y : R}, x =ᵥ y → x ≤ᵥ y
-/
lemma vlt_of_vlt_of_veq (h1 : x <ᵥ y) (h2 : y =ᵥ z) : x <ᵥ z :=
  h1.trans_vle h2.vle
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans R R R veq vlt vlt where
  trans := vlt_of_veq_of_vlt
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans R R R vlt veq vlt where
  trans := vlt_of_vlt_of_veq

@[gcongr]
/-
**ValuativeRel.vlt_imp_vlt_of_vle_of_vle** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel
`。
形式化陈述：vlt_imp_vlt_of_vle_of_vle (h1 : x <=ᵥ x') (h2 : y' <=ᵥ y) : x' <ᵥ y' -> x 
<ᵥ y
参数：h1 : x <=ᵥ x'；h2 : y' <=ᵥ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle.trans_vlt`：∀ {R : Type u_1} [inst : Semiring R] [inst_1
 : ValuativeRel R] {x y z : R}, x ≤ᵥ y → y <ᵥ z → x <ᵥ z
· 使用定理 `ValuativeRel.vlt.trans_vle`：∀ {R : Type u_1} [inst : Semiring R] [inst_1
 : ValuativeRel R] {x y z : R}, x <ᵥ y → y ≤ᵥ z → x <ᵥ z
-/
theorem vlt_imp_vlt_of_vle_of_vle (h1 : x ≤ᵥ x') (h2 : y' ≤ᵥ y) : x' <ᵥ y' → x <ᵥ y :=
  (h1.trans_vlt <| ·.trans_vle h2)

@[gcongr]
/-
**ValuativeRel.mul_vle_mul** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：mul_vle_mul {x x' y y' : R} (h1 : x <=ᵥ y) (h2 : x' <=ᵥ y') : x * x' <=ᵥ y
 * y'
参数：h1 : x <=ᵥ y；h2 : x' <=ᵥ y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle.trans`：∀ {R : Type u_1} {inst : Semiring R} [self : Val
uativeRel R] {z y x : R}, x ≤ᵥ y → y ≤ᵥ z → x ≤ᵥ z
· 使用定理 `ValuativeRel.mul_vle_mul_left`：∀ {R : Type u_1} {inst : Semiring R} [sel
f : ValuativeRel R] {x y : R}, x ≤ᵥ y → ∀ (z : R), x * z ≤ᵥ y * z
· 使用引理 `ValuativeRel.mul_vle_mul_right`：mul_vle_mul_right (h : x <=ᵥ y) (z) : z 
* x <=ᵥ z * y
-/
lemma mul_vle_mul {x x' y y' : R} (h1 : x ≤ᵥ y) (h2 : x' ≤ᵥ y') : x * x' ≤ᵥ y * y' :=
  (mul_vle_mul_left h1 _).trans (mul_vle_mul_right h2 _)
/-
**ValuativeRel.mul_vle_mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {x y z : R}
, 0 <ᵥ z → (x * z ≤ᵥ y * z ↔ x ≤ᵥ y)
参数：x * z ≤ᵥ y * z ↔ x ≤ᵥ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle_mul_cancel`：∀ {R : Type u_1} {inst : Semiring R} [self 
: ValuativeRel R] {x y z : R}, ¬z ≤ᵥ 0 → x * z ≤ᵥ y * z → x ≤ᵥ y
· 使用定理 `ValuativeRel.mul_vle_mul_left`：∀ {R : Type u_1} {inst : Semiring R} [sel
f : ValuativeRel R] {x y : R}, x ≤ᵥ y → ∀ (z : R), x * z ≤ᵥ y * z
-/
@[simp] lemma mul_vle_mul_iff_left (hz : 0 <ᵥ z) : x * z ≤ᵥ y * z ↔ x ≤ᵥ y :=
  ⟨vle_mul_cancel hz, (mul_vle_mul_left · _)⟩
/-
**ValuativeRel.mul_vle_mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {x y z : R}
, 0 <ᵥ x → (x * y ≤ᵥ x * z ↔ y ≤ᵥ z)
参数：x * y ≤ᵥ x * z ↔ y ≤ᵥ z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuativeRel.mul_vle_mul_iff_left`：∀ {R : Type u_1} [inst : Semiring R] 
[inst_1 : ValuativeRel R] {x y z : R}, 0 <ᵥ z → (x * z ≤ᵥ y * z ↔ x ≤ᵥ y)
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `ValuativeRel.vle_refl`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Va
luativeRel R] (x : R), x ≤ᵥ x
· 使用定理 `Mathlib.Tactic.GCongr.AntisymmRel.left`：∀ {α : Type u_3} {a b : α} {r : 
α → α → Prop}, AntisymmRel r a b → r a b
· 使用引理 `ValuativeRel.veq_mul_comm`：veq_mul_comm (x y : R) : x * y =ᵥ y * x
· 使用定理 `ValuativeRel.veq.symm`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Va
luativeRel R] {x y : R}, x =ᵥ y → y =ᵥ x
-/
@[simp] lemma mul_vle_mul_iff_right (hx : 0 <ᵥ x) : x * y ≤ᵥ x * z ↔ y ≤ᵥ z := by
  refine ⟨fun h ↦ ?_ , fun h ↦ ?_⟩
  · grw [veq_mul_comm, veq_mul_comm (x := x)] at h
    rwa [mul_vle_mul_iff_left hx] at h
  · grw [veq_mul_comm, veq_mul_comm (x := x)]
    rwa [mul_vle_mul_iff_left hx]
/-
**ValuativeRel.mul_vlt_mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {x y z : R}
, 0 <ᵥ z → (x * z <ᵥ y * z ↔ x <ᵥ y)
参数：x * z <ᵥ y * z ↔ x <ᵥ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ValuativeRel.mul_vle_mul_iff_left`：∀ {R : Type u_1} [inst : Semiring R] 
[inst_1 : ValuativeRel R] {x y z : R}, 0 <ᵥ z → (x * z ≤ᵥ y * z ↔ x ≤ᵥ y)
-/
@[simp] lemma mul_vlt_mul_iff_left (hz : 0 <ᵥ z) : x * z <ᵥ y * z ↔ x <ᵥ y :=
  (mul_vle_mul_iff_left hz).not

@[gcongr] alias ⟨_, mul_vlt_mul_left⟩ := mul_vlt_mul_iff_left
@[deprecated (since := "2026-01-06")] alias vlt_mul_right := mul_vlt_mul_left
/-
**ValuativeRel.mul_vlt_mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {x y z : R}
, 0 <ᵥ x → (x * y <ᵥ x * z ↔ y <ᵥ z)
参数：x * y <ᵥ x * z ↔ y <ᵥ z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ValuativeRel.mul_vle_mul_iff_right`：∀ {R : Type u_1} [inst : Semiring R]
 [inst_1 : ValuativeRel R] {x y z : R}, 0 <ᵥ x → (x * y ≤ᵥ x * z ↔ y ≤ᵥ z)
-/
@[simp] lemma mul_vlt_mul_iff_right (hx : 0 <ᵥ x) : x * y <ᵥ x * z ↔ y <ᵥ z :=
  (mul_vle_mul_iff_right hx).not

@[gcongr] alias ⟨_, mul_vlt_mul_right⟩ := mul_vlt_mul_iff_right
@[deprecated (since := "2026-01-06")] alias vlt_mul_left := mul_vlt_mul_right

@[gcongr]
/-
**ValuativeRel.mul_veq_mul** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：mul_veq_mul (h1 : x =ᵥ y) (h2 : x' =ᵥ y') : x * x' =ᵥ y * y'
参数：h1 : x =ᵥ y；h2 : x' =ᵥ y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ValuativeRel.mul_vle_mul`：mul_vle_mul {x x' y y' : R} (h1 : x <=ᵥ y) (h2
 : x' <=ᵥ y') : x * x' <=ᵥ y * y'
· 使用定理 `ValuativeRel.veq.vle`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x y : R}, x =ᵥ y → x ≤ᵥ y
· 使用定理 `ValuativeRel.veq.vge`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x y : R}, x =ᵥ y → y ≤ᵥ x
-/
lemma mul_veq_mul (h1 : x =ᵥ y) (h2 : x' =ᵥ y') : x * x' =ᵥ y * y' :=
  ⟨mul_vle_mul h1.vle h2.vle, mul_vle_mul h1.vge h2.vge⟩
/-
**ValuativeRel.veq_mul_right_comm** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：veq_mul_right_comm (x y z : R) : x * y * z =ᵥ x * z * y
参数：x y z : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用引理 `ValuativeRel.mul_veq_mul`：mul_veq_mul (h1 : x =ᵥ y) (h2 : x' =ᵥ y') : x 
* x' =ᵥ y * y'
· 使用定理 `ValuativeRel.veq_refl`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Va
luativeRel R] (x : R), x =ᵥ x
· 使用引理 `ValuativeRel.veq_mul_comm`：veq_mul_comm (x y : R) : x * y =ᵥ y * x
-/
lemma veq_mul_right_comm (x y z : R) : x * y * z =ᵥ x * z * y := by
  grw [mul_assoc, veq_mul_comm y, mul_assoc]
/-
**ValuativeRel.veq_mul_mul_mul_comm** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：veq_mul_mul_mul_comm (x y z w : R) : x * y * (z * w) =ᵥ x * z * (y * w)
参数：x y z w : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用引理 `ValuativeRel.mul_veq_mul`：mul_veq_mul (h1 : x =ᵥ y) (h2 : x' =ᵥ y') : x 
* x' =ᵥ y * y'
· 使用引理 `ValuativeRel.veq_mul_right_comm`：veq_mul_right_comm (x y z : R) : x * y 
* z =ᵥ x * z * y
· 使用定理 `ValuativeRel.veq_refl`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Va
luativeRel R] (x : R), x =ᵥ x
-/
lemma veq_mul_mul_mul_comm (x y z w : R) : x * y * (z * w) =ᵥ x * z * (y * w) := by
  grw [← mul_assoc, veq_mul_right_comm x, mul_assoc]
/-
**ValuativeRel.vle_add_cases** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel`。
形式化陈述：vle_add_cases (x y : R) : x + y <=ᵥ x ∨ x + y <=ᵥ y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `ValuativeRel.vle_add`：∀ {R : Type u_1} {inst : Semiring R} [self : Valua
tiveRel R] {x y z : R}, x ≤ᵥ z → y ≤ᵥ z → x + y ≤ᵥ z
· 使用定理 `ValuativeRel.vle.rfl`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x : R}, x ≤ᵥ x
· 使用定理 `ValuativeRel.vle_total`：∀ {R : Type u_1} {inst : Semiring R} [self : Val
uativeRel R] (x y : R), x ≤ᵥ y ∨ y ≤ᵥ x
-/
theorem vle_add_cases (x y : R) : x + y ≤ᵥ x ∨ x + y ≤ᵥ y :=
  (vle_total y x).imp (fun h => vle_add .rfl h) (fun h => vle_add h .rfl)
/-
**ValuativeRel.zero_vlt_mul** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {x y : R}, 
0 <ᵥ x → 0 <ᵥ y → 0 <ᵥ x * y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuativeRel.not_vlt`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x y : R}, ¬x <ᵥ y ↔ y ≤ᵥ x
· 使用定理 `ValuativeRel.vle_mul_cancel`：∀ {R : Type u_1} {inst : Semiring R} [self 
: ValuativeRel R] {x y z : R}, ¬z ≤ᵥ 0 → x * z ≤ᵥ y * z → x ≤ᵥ y
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `ValuativeRel.vle_refl`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Va
luativeRel R] (x : R), x ≤ᵥ x
· 使用定理 `Mathlib.Tactic.GCongr.AntisymmRel.left`：∀ {α : Type u_3} {a b : α} {r : 
α → α → Prop}, AntisymmRel r a b → r a b
· 使用引理 `ValuativeRel.veq_mul_comm`：veq_mul_comm (x y : R) : x * y =ᵥ y * x
· 使用定理 `ValuativeRel.veq.symm`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Va
luativeRel R] {x y : R}, x =ᵥ y → y =ᵥ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma zero_vlt_mul (hx : 0 <ᵥ x) (hy : 0 <ᵥ y) : 0 <ᵥ x * y := by
  contrapose hy
  rw [not_vlt] at hy ⊢
  grw [show (0 : R) = x * 0 by simp, veq_mul_comm, veq_mul_comm x] at hy
  exact vle_mul_cancel hx hy

variable (R) in
/-- The submonoid of elements `x : R` whose valuation is positive. -/
/-
**ValuativeRel.posSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel`。
形式化陈述：posSubmonoid : Submonoid R where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.zero_vlt_mul`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 
: ValuativeRel R] {x y : R}, 0 <ᵥ x → 0 <ᵥ y → 0 <ᵥ x * y
· 使用引理 `ValuativeRel.zero_vlt_one`：zero_vlt_one : (0 : R) <ᵥ 1

--- 原说明 ---
The submonoid of elements `x : R` whose valuation is positive.
-/
def posSubmonoid : Submonoid R where
  carrier := { x | 0 <ᵥ x }
  mul_mem' := zero_vlt_mul
  one_mem' := zero_vlt_one
/-
**ValuativeRel.zero_vlt_coe_posSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel
`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] (x : ↥(Valu
ativeRel.posSubmonoid R)), 0 <ᵥ ↑x
参数：x : ↥(ValuativeRel.posSubmonoid R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
@[simp] lemma zero_vlt_coe_posSubmonoid (x : posSubmonoid R) : 0 <ᵥ x.val := x.prop

@[simp]
/-
**ValuativeRel.posSubmonoid_def** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：posSubmonoid_def (x : R) : x in posSubmonoid R ↔ 0 <ᵥ x
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma posSubmonoid_def (x : R) : x ∈ posSubmonoid R ↔ 0 <ᵥ x := Iff.rfl
/-
**ValuativeRel.right_cancel_posSubmonoid** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel
`。
形式化陈述：right_cancel_posSubmonoid (x y : R) (u : posSubmonoid R) : x * u <=ᵥ y * u
 ↔ x <=ᵥ y
参数：x y : R；u : posSubmonoid R。
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
lemma right_cancel_posSubmonoid (x y : R) (u : posSubmonoid R) :
    x * u ≤ᵥ y * u ↔ x ≤ᵥ y := by simp
/-
**ValuativeRel.left_cancel_posSubmonoid** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`
。
形式化陈述：left_cancel_posSubmonoid (x y : R) (u : posSubmonoid R) : u * x <=ᵥ u * y 
↔ x <=ᵥ y
参数：x y : R；u : posSubmonoid R。
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
lemma left_cancel_posSubmonoid (x y : R) (u : posSubmonoid R) :
    u * x ≤ᵥ u * y ↔ x ≤ᵥ y := by simp

@[simp]
/-
**ValuativeRel.val_posSubmonoid_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`
。
形式化陈述：val_posSubmonoid_ne_zero (x : posSubmonoid R) : (x : R) != 0
参数：x : posSubmonoid R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `ValuativeRel.posSubmonoid_def`：posSubmonoid_def (x : R) : x in posSubmon
oid R ↔ 0 <ᵥ x
-/
lemma val_posSubmonoid_ne_zero (x : posSubmonoid R) : (x : R) ≠ 0 := by
  have := x.prop
  rw [posSubmonoid_def] at this
  contrapose this
  simp [this]

variable (R) in
/-- The setoid used to construct `ValueGroupWithZero R`. -/
@[instance_reducible]
/-
**ValuativeRel.valueSetoid** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel`。
形式化陈述：valueSetoid : Setoid (R × posSubmonoid R) where r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The setoid used to construct `ValueGroupWithZero R`.
-/
def valueSetoid : Setoid (R × posSubmonoid R) where
  r := fun (x, s) (y, t) => x * t ≤ᵥ y * s ∧ y * s ≤ᵥ x * t
  iseqv := {
    refl ru := ⟨vle_refl _, vle_refl _⟩
    symm h := ⟨h.2, h.1⟩
    trans := by
      rintro ⟨r, u⟩ ⟨s, v⟩ ⟨t, w⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
      constructor
      · have := mul_vle_mul h1 (vle_refl ↑w)
        grw [veq_mul_right_comm (x := s)] at this
        have := vle_trans this (mul_vle_mul h3 (vle_refl _))
        grw [veq_mul_right_comm r, veq_mul_right_comm t] at this
        simpa using this
      · have := mul_vle_mul h4 (vle_refl ↑u)
        grw [veq_mul_right_comm s] at this
        have := vle_trans this (mul_vle_mul h2 (vle_refl _))
        grw [veq_mul_right_comm t, veq_mul_right_comm r] at this
        simpa using this
  }

variable (R) in
/-- The "canonical" value group-with-zero of a ring with a valuative relation. -/
/-
**ValuativeRel.ValueGroupWithZero** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel`。
形式化陈述：ValueGroupWithZero
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "canonical" value group-with-zero of a ring with a valuative relation.
-/
def ValueGroupWithZero := Quotient (valueSetoid R)

/-- Construct an element of the value group-with-zero from an element `r : R` and
  `y : posSubmonoid R`. This should be thought of as `v r / v y`. -/
protected
/-
**ValuativeRel.ValueGroupWithZero.mk** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel.Val
ueGroupWithZero`。
形式化陈述：{R : Type u_1} →   [inst : Semiring R] →     [inst_1 : ValuativeRel R] → R
 → ↥(ValuativeRel.posSubmonoid R) → ValuativeRel.ValueGroupWithZero R
参数：ValuativeRel.posSubmonoid R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ValueGroupWithZero.mk (x : R) (y : posSubmonoid R) : ValueGroupWithZero R :=
  Quotient.mk _ (x, y)

protected
/-
**ValuativeRel.ValueGroupWithZero.sound** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel.
ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {x y : R} {
t s : ↥(ValuativeRel.posSubmonoid R)},   x * ↑s ≤ᵥ y * ↑t → y * ↑t ≤ᵥ x * ↑s → V
aluativeRel.ValueGroupWithZero.mk x t = ValuativeRel.ValueGroupWithZero.mk y s
参数：ValuativeRel.posSubmonoid R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem ValueGroupWithZero.sound {t s : posSubmonoid R}
    (h₁ : x * s ≤ᵥ y * t) (h₂ : y * t ≤ᵥ x * s) :
    ValueGroupWithZero.mk x t = ValueGroupWithZero.mk y s :=
  Quotient.sound ⟨h₁, h₂⟩

protected
/-
**ValuativeRel.ValueGroupWithZero.exact** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel.
ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {x y : R} {
t s : ↥(ValuativeRel.posSubmonoid R)},   ValuativeRel.ValueGroupWithZero.mk x t 
= ValuativeRel.ValueGroupWithZero.mk y s → x * ↑s ≤ᵥ y * ↑t ∧ y * ↑t ≤ᵥ x * ↑s
参数：ValuativeRel.posSubmonoid R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
-/
theorem ValueGroupWithZero.exact {t s : posSubmonoid R}
    (h : ValueGroupWithZero.mk x t = ValueGroupWithZero.mk y s) :
    x * s ≤ᵥ y * t ∧ y * t ≤ᵥ x * s :=
  Quotient.exact h

protected
/-
**ValuativeRel.ValueGroupWithZero.ind** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel.Va
lueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {motive : V
aluativeRel.ValueGroupWithZero R → Prop},   (∀ (x : R) (y : ↥(ValuativeRel.posSu
bmonoid R)), motive (ValuativeRel.ValueGroupWithZero.mk x y)) →     ∀ (t : Valua
tiveRel.ValueGroupWithZero R), motive t
参数：∀ (x : R) (y : ↥(ValuativeRel.posSubmonoid R)), motive (ValuativeRel.ValueGro
upWithZero.mk x y)；t : ValuativeRel.ValueGroupWithZero R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
-/
theorem ValueGroupWithZero.ind {motive : ValueGroupWithZero R → Prop} (mk : ∀ x y, motive (.mk x y))
    (t : ValueGroupWithZero R) : motive t :=
  Quotient.ind (fun (x, y) => mk x y) t

/-- Lifts a function `R → posSubmonoid R → α` to the value group-with-zero of `R`. -/
protected
/-
**ValuativeRel.ValueGroupWithZero.lift** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel.V
alueGroupWithZero`。
形式化陈述：{R : Type u_1} →   [inst : Semiring R] →     [inst_1 : ValuativeRel R] →  
     {α : Sort u_2} →         (f : R → ↥(ValuativeRel.posSubmonoid R) → α) →    
       (∀ (x y : R) (t s : ↥(ValuativeRel.posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y
 * ↑s ≤ᵥ x * ↑t → f x s = f y t) →             ValuativeRel.ValueGroupWithZero R
 → α
参数：f : R → ↥(ValuativeRel.posSubmonoid R) → α；∀ (x y : R) (t s : ↥(ValuativeRel.
posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y * ↑s ≤ᵥ x * ↑t → f x s = f y t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ValueGroupWithZero.lift {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t)
    (t : ValueGroupWithZero R) : α :=
  Quotient.lift (fun (x, y) => f x y) (fun (x, t) (y, s) ⟨h₁, h₂⟩ => hf x y s t h₁ h₂) t

@[simp] protected
/-
**ValuativeRel.ValueGroupWithZero.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRe
l.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {α : Sort u
_2}   (f : R → ↥(ValuativeRel.posSubmonoid R) → α)   (hf : ∀ (x y : R) (t s : ↥(
ValuativeRel.posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y * ↑s ≤ᵥ x * ↑t → f x s = f y
 t) (x : R)   (y : ↥(ValuativeRel.posSubmonoid R)),   ValuativeRel.ValueGroupWit
hZero.lift f hf (ValuativeRel.ValueGroupWithZero.mk x y) = f x y
参数：f : R → ↥(ValuativeRel.posSubmonoid R) → α；hf : ∀ (x y : R) (t s : ↥(Valuativ
eRel.posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y * ↑s ≤ᵥ x * ↑t → f x s = f y t；x : R
；y : ↥(ValuativeRel.posSubmonoid R)；ValuativeRel.ValueGroupWithZero.mk x y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ValueGroupWithZero.lift_mk {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t)
    (x : R) (y : posSubmonoid R) : ValueGroupWithZero.lift f hf (.mk x y) = f x y := rfl

/-- Lifts a function `R → posSubmonoid R → R → posSubmonoid R → α` to
  the value group-with-zero of `R`. -/
protected
/-
**ValuativeRel.ValueGroupWithZero.lift** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel.V
alueGroupWithZero`。
形式化陈述：{R : Type u_1} →   [inst : Semiring R] →     [inst_1 : ValuativeRel R] →  
     {α : Sort u_2} →         (f : R → ↥(ValuativeRel.posSubmonoid R) → α) →    
       (∀ (x y : R) (t s : ↥(ValuativeRel.posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y
 * ↑s ≤ᵥ x * ↑t → f x s = f y t) →             ValuativeRel.ValueGroupWithZero R
 → α
参数：f : R → ↥(ValuativeRel.posSubmonoid R) → α；∀ (x y : R) (t s : ↥(ValuativeRel.
posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y * ↑s ≤ᵥ x * ↑t → f x s = f y t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ValueGroupWithZero.lift₂ {α : Sort*} (f : R → posSubmonoid R → R → posSubmonoid R → α)
    (hf : ∀ (x y z w : R) (t s u v : posSubmonoid R),
      x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → z * u ≤ᵥ w * v → w * v ≤ᵥ z * u →
      f x s z v = f y t w u)
    (t₁ : ValueGroupWithZero R) (t₂ : ValueGroupWithZero R) : α :=
  Quotient.lift₂ (fun (x, t) (y, s) => f x t y s)
    (fun (x, t) (z, v) (y, s) (w, u) ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ => hf x y z w s t u v h₁ h₂ h₃ h₄) t₁ t₂

@[simp] protected
/-
**ValuativeRel.ValueGroupWithZero.lift** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel.V
alueGroupWithZero`。
形式化陈述：{R : Type u_1} →   [inst : Semiring R] →     [inst_1 : ValuativeRel R] →  
     {α : Sort u_2} →         (f : R → ↥(ValuativeRel.posSubmonoid R) → α) →    
       (∀ (x y : R) (t s : ↥(ValuativeRel.posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y
 * ↑s ≤ᵥ x * ↑t → f x s = f y t) →             ValuativeRel.ValueGroupWithZero R
 → α
参数：f : R → ↥(ValuativeRel.posSubmonoid R) → α；∀ (x y : R) (t s : ↥(ValuativeRel.
posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y * ↑s ≤ᵥ x * ↑t → f x s = f y t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ValueGroupWithZero.lift₂_mk {α : Sort*} (f : R → posSubmonoid R → R → posSubmonoid R → α)
    (hf : ∀ (x y z w : R) (t s u v : posSubmonoid R),
      x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → z * u ≤ᵥ w * v → w * v ≤ᵥ z * u →
      f x s z v = f y t w u)
    (x y : R) (z w : posSubmonoid R) :
    ValueGroupWithZero.lift₂ f hf (.mk x z) (.mk y w) = f x z y w := rfl
/-
**ValuativeRel.ValueGroupWithZero.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeR
el.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {x y : R} {
t s : ↥(ValuativeRel.posSubmonoid R)},   ValuativeRel.ValueGroupWithZero.mk x t 
= ValuativeRel.ValueGroupWithZero.mk y s ↔ x * ↑s ≤ᵥ y * ↑t ∧ y * ↑t ≤ᵥ x * ↑s
参数：ValuativeRel.posSubmonoid R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
theorem ValueGroupWithZero.mk_eq_mk {t s : posSubmonoid R} :
    ValueGroupWithZero.mk x t = ValueGroupWithZero.mk y s ↔ x * s ≤ᵥ y * t ∧ y * t ≤ᵥ x * s :=
  Quotient.eq
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (ValueGroupWithZero R) where
  zero := .mk 0 1

@[simp]
/-
**ValuativeRel.ValueGroupWithZero.mk_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Valuativ
eRel.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] (x : R) (y 
: ↥(ValuativeRel.posSubmonoid R)),   ValuativeRel.ValueGroupWithZero.mk x y = 0 
↔ x ≤ᵥ 0
参数：x : R；y : ↥(ValuativeRel.posSubmonoid R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ValuativeRel.ValueGroupWithZero.mk_eq_mk`：∀ {R : Type u_1} [inst : Semir
ing R] [inst_1 : ValuativeRel R] {x y : R} {t s : ↥(ValuativeRel.posSubmonoid R)
},   ValuativeRel.ValueGroupWi…
· 使用定理 `ValuativeRel.ValueGroupWithZero.sound`：∀ {R : Type u_1} [inst : Semiring
 R] [inst_1 : ValuativeRel R] {x y : R} {t s : ↥(ValuativeRel.posSubmonoid R)}, 
  x * ↑s ≤ᵥ y * ↑t → y * ↑t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem ValueGroupWithZero.mk_eq_zero (x : R) (y : posSubmonoid R) :
    ValueGroupWithZero.mk x y = 0 ↔ x ≤ᵥ 0 :=
  ⟨fun h => by simpa using ValueGroupWithZero.mk_eq_mk.mp h,
    fun h => ValueGroupWithZero.sound (by simpa using h) (by simp)⟩

@[simp]
/-
**ValuativeRel.ValueGroupWithZero.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRe
l.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] (x : ↥(Valu
ativeRel.posSubmonoid R)),   ValuativeRel.ValueGroupWithZero.mk 0 x = 0
参数：x : ↥(ValuativeRel.posSubmonoid R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ValuativeRel.ValueGroupWithZero.mk_eq_zero`：∀ {R : Type u_1} [inst : Sem
iring R] [inst_1 : ValuativeRel R] (x : R) (y : ↥(ValuativeRel.posSubmonoid R)),
   ValuativeRel.ValueGroupWithZe…
· 使用定理 `ValuativeRel.vle.rfl`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x : R}, x ≤ᵥ x
-/
theorem ValueGroupWithZero.mk_zero (x : posSubmonoid R) : ValueGroupWithZero.mk 0 x = 0 :=
  (ValueGroupWithZero.mk_eq_zero 0 x).mpr .rfl
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (ValueGroupWithZero R) where
  one := .mk 1 1

@[simp]
/-
**ValuativeRel.ValueGroupWithZero.mk_self** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRe
l.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] (x : ↥(Valu
ativeRel.posSubmonoid R)),   ValuativeRel.ValueGroupWithZero.mk (↑x) x = 1
参数：x : ↥(ValuativeRel.posSubmonoid R)；↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.ValueGroupWithZero.sound`：∀ {R : Type u_1} [inst : Semiring
 R] [inst_1 : ValuativeRel R] {x y : R} {t s : ↥(ValuativeRel.posSubmonoid R)}, 
  x * ↑s ≤ᵥ y * ↑t → y * ↑t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem ValueGroupWithZero.mk_self (x : posSubmonoid R) : ValueGroupWithZero.mk (x : R) x = 1 :=
  ValueGroupWithZero.sound (by simp) (by simp)

@[simp]
/-
**ValuativeRel.ValueGroupWithZero.mk_one_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuativ
eRel.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R], ValuativeR
el.ValueGroupWithZero.mk 1 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.ValueGroupWithZero.sound`：∀ {R : Type u_1} [inst : Semiring
 R] [inst_1 : ValuativeRel R] {x y : R} {t s : ↥(ValuativeRel.posSubmonoid R)}, 
  x * ↑s ≤ᵥ y * ↑t → y * ↑t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem ValueGroupWithZero.mk_one_one : ValueGroupWithZero.mk (1 : R) 1 = 1 :=
  ValueGroupWithZero.sound (by simp) (by simp)

@[simp]
/-
**ValuativeRel.ValueGroupWithZero.mk_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuative
Rel.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] (x : R) (y 
: ↥(ValuativeRel.posSubmonoid R)),   ValuativeRel.ValueGroupWithZero.mk x y = 1 
↔ x ≤ᵥ ↑y ∧ ↑y ≤ᵥ x
参数：x : R；y : ↥(ValuativeRel.posSubmonoid R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ValueGroupWithZero.mk_eq_one (x : R) (y : posSubmonoid R) :
    ValueGroupWithZero.mk x y = 1 ↔ x ≤ᵥ y ∧ y ≤ᵥ x := by
  simp [← mk_one_one, mk_eq_mk]
/-
**ValuativeRel.ValueGroupWithZero.lift_zero** 是 Mathlib 中的一个定理，位于命名空间 `Valuative
Rel.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {α : Sort u
_2}   (f : R → ↥(ValuativeRel.posSubmonoid R) → α)   (hf : ∀ (x y : R) (t s : ↥(
ValuativeRel.posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y * ↑s ≤ᵥ x * ↑t → f x s = f y
 t),   ValuativeRel.ValueGroupWithZero.lift f hf 0 = f 0 1
参数：f : R → ↥(ValuativeRel.posSubmonoid R) → α；hf : ∀ (x y : R) (t s : ↥(Valuativ
eRel.posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y * ↑s ≤ᵥ x * ↑t → f x s = f y t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ValueGroupWithZero.lift_zero {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t) :
    ValueGroupWithZero.lift f hf 0 = f 0 1 :=
  rfl

@[simp]
/-
**ValuativeRel.ValueGroupWithZero.lift_one** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeR
el.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {α : Sort u
_2}   (f : R → ↥(ValuativeRel.posSubmonoid R) → α)   (hf : ∀ (x y : R) (t s : ↥(
ValuativeRel.posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y * ↑s ≤ᵥ x * ↑t → f x s = f y
 t),   ValuativeRel.ValueGroupWithZero.lift f hf 1 = f 1 1
参数：f : R → ↥(ValuativeRel.posSubmonoid R) → α；hf : ∀ (x y : R) (t s : ↥(Valuativ
eRel.posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y * ↑s ≤ᵥ x * ↑t → f x s = f y t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ValueGroupWithZero.lift_one {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t) :
    ValueGroupWithZero.lift f hf 1 = f 1 1 :=
  rfl
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (ValueGroupWithZero R) where
  mul := ValueGroupWithZero.lift₂ (fun a b c d => .mk (a * c) (b * d)) <| by
    intro x y z w t s u v h₁ h₂ h₃ h₄
    apply ValueGroupWithZero.sound
    · grw [Submonoid.coe_mul, Submonoid.coe_mul,
        veq_mul_mul_mul_comm x, veq_mul_mul_mul_comm y]
      exact mul_vle_mul h₁ h₃
    · grw [Submonoid.coe_mul, Submonoid.coe_mul,
        veq_mul_mul_mul_comm x, veq_mul_mul_mul_comm y]
      exact mul_vle_mul h₂ h₄

@[simp]
/-
**ValuativeRel.ValueGroupWithZero.mk_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `Valuative
Rel.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] (a b : R) (
c d : ↥(ValuativeRel.posSubmonoid R)),   ValuativeRel.ValueGroupWithZero.mk a c 
* ValuativeRel.ValueGroupWithZero.mk b d =     ValuativeRel.ValueGroupWithZero.m
k (a * b) (c * d)
参数：a b : R；c d : ↥(ValuativeRel.posSubmonoid R)；a * b；c * d。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ValueGroupWithZero.mk_mul_mk (a b : R) (c d : posSubmonoid R) :
    ValueGroupWithZero.mk a c * ValueGroupWithZero.mk b d = ValueGroupWithZero.mk (a * b) (c * d) :=
  rfl
/-
**ValuativeRel.ValueGroupWithZero.lift_mul** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeR
el.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {α : Type u
_2} [inst_2 : Mul α]   (f : R → ↥(ValuativeRel.posSubmonoid R) → α)   (hf : ∀ (x
 y : R) (t s : ↥(ValuativeRel.posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y * ↑s ≤ᵥ x *
 ↑t → f x s = f y t),   (∀ (a b : R) (r s : ↥(ValuativeRel.posSubmonoid R)), f (
a * b) (r * s) = f a r * f b s) →     ∀ (a b : ValuativeRel.ValueGroupWithZero R
),       ValuativeRel.ValueGroupWithZero.lift f hf (a * b) =         ValuativeRe
l.ValueGroupWithZero.lift f hf a * ValuativeRel.ValueGroupWithZero.lift f hf b
参数：f : R → ↥(ValuativeRel.posSubmonoid R) → α；hf : ∀ (x y : R) (t s : ↥(Valuativ
eRel.posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y * ↑s ≤ᵥ x * ↑t → f x s = f y t；∀ (a 
b : R) (r s : ↥(ValuativeRel.posSubmonoid R)), f (a * b) (r * s) = f a r * f b s
；a b : ValuativeRel.ValueGroupWithZero R；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.ValueGroupWithZero.ind`：∀ {R : Type u_1} [inst : Semiring R
] [inst_1 : ValuativeRel R] {motive : ValuativeRel.ValueGroupWithZero R → Prop},
   (∀ (x : R) (y : ↥(Valu…
-/
theorem ValueGroupWithZero.lift_mul {α : Type*} [Mul α] (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t)
    (hdist : ∀ (a b r s), f (a * b) (r * s) = f a r * f b s)
    (a b : ValueGroupWithZero R) :
    ValueGroupWithZero.lift f hf (a * b) =
      ValueGroupWithZero.lift f hf a * ValueGroupWithZero.lift f hf b := by
  induction a using ValueGroupWithZero.ind
  induction b using ValueGroupWithZero.ind
  simpa using hdist _ _ _ _
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoidWithZero (ValueGroupWithZero R) where
  mul_assoc a b c := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    induction c using ValueGroupWithZero.ind
    simp [mul_assoc]
  one_mul := ValueGroupWithZero.ind <| by simp [← ValueGroupWithZero.mk_one_one]
  mul_one := ValueGroupWithZero.ind <| by simp [← ValueGroupWithZero.mk_one_one]
  zero_mul := ValueGroupWithZero.ind <| fun _ _ => by
    rw [← ValueGroupWithZero.mk_zero 1, ValueGroupWithZero.mk_mul_mk]
    simp
  mul_zero := ValueGroupWithZero.ind <| fun _ _ => by
    rw [← ValueGroupWithZero.mk_zero 1, ValueGroupWithZero.mk_mul_mk]
    simp
  mul_comm a b := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    apply ValuativeRel.ValueGroupWithZero.sound <;>
    · simp only [Submonoid.coe_mul]
      nth_grw 2 [veq_mul_comm]
      nth_grw 6 [veq_mul_comm]
  npow n := ValueGroupWithZero.lift (fun a b => ValueGroupWithZero.mk (a ^ n) (b ^ n)) <| by
    intro x y t s h₁ h₂
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ, ← ValueGroupWithZero.mk_mul_mk, ih]
      apply congrArg (_ * ·)
      exact ValueGroupWithZero.sound h₁ h₂
  npow_zero := ValueGroupWithZero.ind (by simp_rw [HPow.hPow, Pow.pow]; simp)
  npow_succ n := ValueGroupWithZero.ind (by simp_rw [HPow.hPow, Pow.pow]; simp [pow_succ])
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (ValueGroupWithZero R) where
  le := ValueGroupWithZero.lift₂ (fun a s b t => a * t ≤ᵥ b * s) <| by
    intro x y z w t s u v h₁ h₂ h₃ h₄
    by_cases hw : w ≤ᵥ 0 <;> by_cases hz : z ≤ᵥ 0
    · refine propext ⟨fun h => vle_trans ?_ (zero_vle _), fun h => vle_trans ?_ (zero_vle _)⟩
      · apply vle_mul_cancel (s * v).prop
        grw [veq_mul_right_comm, Submonoid.coe_mul, ← mul_assoc]
        apply (mul_vle_mul_left (mul_vle_mul_left h₂ v) u).trans
        grw [veq_mul_right_comm x]
        apply (mul_vle_mul_left (mul_vle_mul_left h t) u).trans
        apply vle_trans (mul_vle_mul_left (mul_vle_mul_left (mul_vle_mul_left hz s) t) u)
        simp
      · apply vle_mul_cancel (t * u).prop
        grw [veq_mul_right_comm, Submonoid.coe_mul, ← mul_assoc]
        apply (mul_vle_mul_left (mul_vle_mul_left h₁ u) v).trans
        grw [veq_mul_right_comm y]
        apply (mul_vle_mul_left (mul_vle_mul_left h s) v).trans
        apply vle_trans (mul_vle_mul_left (mul_vle_mul_left (mul_vle_mul_left hw t) s) v)
        simp
    · absurd hz
      apply vle_mul_cancel u.prop
      simpa using h₃.trans (mul_vle_mul_left hw v)
    · absurd hw
      apply vle_mul_cancel v.prop
      simpa using h₄.trans (mul_vle_mul_left hz u)
    · refine propext ⟨fun h => ?_, fun h => ?_⟩
      · apply vle_mul_cancel s.prop
        apply vle_mul_cancel hz
        calc y * u * s * z
          _ =ᵥ y * s * (z * u) := by grw [veq_mul_comm z, veq_mul_mul_mul_comm, mul_assoc]
          _ ≤ᵥ x * t * (w * v) := by gcongr
          _ =ᵥ x * v * (t * w) := by grw [veq_mul_comm w, veq_mul_mul_mul_comm, mul_assoc]
          _ ≤ᵥ z * s * (t * w) := by gcongr
          _ =ᵥ w * t * s * z := by grw [veq_mul_comm, veq_mul_comm _ w, veq_mul_comm z, ← mul_assoc]
      · apply vle_mul_cancel t.prop
        apply vle_mul_cancel hw
        calc x * v * t * w
          _ =ᵥ x * t * (w * v) := by grw [veq_mul_comm w, veq_mul_mul_mul_comm, mul_assoc]
          _ ≤ᵥ y * s * (z * u) := by gcongr
          _ =ᵥ y * u * (s * z) := by grw [veq_mul_comm z, veq_mul_mul_mul_comm, mul_assoc]
          _ ≤ᵥ w * t * (s * z) := by gcongr
          _ =ᵥ z * s * t * w := by grw [veq_mul_comm, veq_mul_comm _ z, veq_mul_comm w, ← mul_assoc]

@[simp]
/-
**ValuativeRel.ValueGroupWithZero.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeR
el.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] (x y : R) (
t s : ↥(ValuativeRel.posSubmonoid R)),   ValuativeRel.ValueGroupWithZero.mk x t 
≤ ValuativeRel.ValueGroupWithZero.mk y s ↔ x * ↑s ≤ᵥ y * ↑t
参数：x y : R；t s : ↥(ValuativeRel.posSubmonoid R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ValueGroupWithZero.mk_le_mk (x y : R) (t s : posSubmonoid R) :
    ValueGroupWithZero.mk x t ≤ ValueGroupWithZero.mk y s ↔ x * s ≤ᵥ y * t := Iff.rfl
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrder (ValueGroupWithZero R) where
  le_refl := ValueGroupWithZero.ind fun _ _ => .rfl
  le_trans a b c hab hbc := by
    induction a using ValueGroupWithZero.ind with | mk a₁ a₂
    induction b using ValueGroupWithZero.ind with | mk b₁ b₂
    induction c using ValueGroupWithZero.ind with | mk c₁ c₂
    rw [ValueGroupWithZero.mk_le_mk] at hab hbc ⊢
    apply vle_mul_cancel b₂.prop
    calc a₁ * c₂ * b₂
      _ =ᵥ a₁ * b₂ * c₂ := by grw [veq_mul_right_comm]
      _ ≤ᵥ b₁ * a₂ * c₂ := mul_vle_mul_left hab _
      _ =ᵥ b₁ * c₂ * a₂ := by grw [veq_mul_right_comm]
      _ ≤ᵥ c₁ * b₂ * a₂ := mul_vle_mul_left hbc _
      _ =ᵥ c₁ * a₂ * b₂ := by grw [veq_mul_right_comm]
  le_antisymm a b hab hba := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    exact ValueGroupWithZero.sound hab hba
  le_total a b := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    rw [ValueGroupWithZero.mk_le_mk, ValueGroupWithZero.mk_le_mk]
    apply vle_total
  toDecidableLE := Classical.decRel LE.le

@[simp]
/-
**ValuativeRel.ValueGroupWithZero.mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeR
el.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] (x y : R) (
t s : ↥(ValuativeRel.posSubmonoid R)),   ValuativeRel.ValueGroupWithZero.mk x t 
< ValuativeRel.ValueGroupWithZero.mk y s ↔ x * ↑s <ᵥ y * ↑t
参数：x y : R；t s : ↥(ValuativeRel.posSubmonoid R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuativeRel.not_vle`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x y : R}, ¬x ≤ᵥ y ↔ y <ᵥ x
· 使用定理 `ValuativeRel.ValueGroupWithZero.mk_le_mk`：∀ {R : Type u_1} [inst : Semir
ing R] [inst_1 : ValuativeRel R] (x y : R) (t s : ↥(ValuativeRel.posSubmonoid R)
),   ValuativeRel.ValueGroupWi…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ValueGroupWithZero.mk_lt_mk (x y : R) (t s : posSubmonoid R) :
    ValueGroupWithZero.mk x t < ValueGroupWithZero.mk y s ↔ x * s <ᵥ y * t := by
  rw [lt_iff_not_ge, ← not_vle, mk_le_mk]

@[simp]
/-
**ValuativeRel.ValueGroupWithZero.mk_pos** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel
.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] {x : R} {s 
: ↥(ValuativeRel.posSubmonoid R)},   0 < ValuativeRel.ValueGroupWithZero.mk x s 
↔ 0 <ᵥ x
参数：ValuativeRel.posSubmonoid R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuativeRel.ValueGroupWithZero.mk_zero`：∀ {R : Type u_1} [inst : Semiri
ng R] [inst_1 : ValuativeRel R] (x : ↥(ValuativeRel.posSubmonoid R)),   Valuativ
eRel.ValueGroupWithZero.mk 0 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ValueGroupWithZero.mk_pos {s : posSubmonoid R} :
    0 < ValueGroupWithZero.mk x s ↔ 0 <ᵥ x := by rw [← mk_zero 1]; simp [-mk_zero]
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (ValueGroupWithZero R) where
  bot := 0
/-
**ValuativeRel.ValueGroupWithZero.bot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Valuati
veRel.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R], ⊥ = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ValueGroupWithZero.bot_eq_zero : (⊥ : ValueGroupWithZero R) = 0 := rfl
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (ValueGroupWithZero R) where
  bot_le := ValueGroupWithZero.ind fun x y => by
    rw [ValueGroupWithZero.bot_eq_zero, ← ValueGroupWithZero.mk_zero 1, ValueGroupWithZero.mk_le_mk]
    simp
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedMonoid (ValueGroupWithZero R) where
  mul_le_mul_left a b hab c := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    induction c using ValueGroupWithZero.ind
    simp only [ValueGroupWithZero.mk_mul_mk, ValueGroupWithZero.mk_le_mk, Submonoid.coe_mul]
    nth_grw 1 [veq_mul_mul_mul_comm]
    nth_grw 2 [veq_mul_mul_mul_comm]
    exact mul_vle_mul_left hab _
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (ValueGroupWithZero R) where
  inv := ValueGroupWithZero.lift (fun x s => by
    classical exact if h : x ≤ᵥ 0 then 0 else .mk s ⟨x, h⟩) <| by
    intro x y t s h₁ h₂
    by_cases hx : x ≤ᵥ 0 <;> by_cases hy : y ≤ᵥ 0
    · simp [hx, hy]
    · absurd hy
      apply vle_mul_cancel s.prop
      simpa using vle_trans h₂ (mul_vle_mul_left hx t)
    · absurd hx
      apply vle_mul_cancel t.prop
      simpa using vle_trans h₁ (mul_vle_mul_left hy s)
    · simp only [dif_neg hx, dif_neg hy]
      apply ValueGroupWithZero.sound
      · grw [veq_mul_comm, veq_mul_comm _ x]
        simpa using h₂
      · grw [veq_mul_comm, veq_mul_comm _ y]
        simpa [mul_comm] using h₁

@[simp]
/-
**ValuativeRel.ValueGroupWithZero.inv_mk** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel
.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] (x : R) (y 
: ↥(ValuativeRel.posSubmonoid R))   (hx : ¬x ≤ᵥ 0), (ValuativeRel.ValueGroupWith
Zero.mk x y)⁻¹ = ValuativeRel.ValueGroupWithZero.mk ↑y ⟨x, hx⟩
参数：x : R；y : ↥(ValuativeRel.posSubmonoid R)；hx : ¬x ≤ᵥ 0；ValuativeRel.ValueGroup
WithZero.mk x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem ValueGroupWithZero.inv_mk (x : R) (y : posSubmonoid R) (hx : ¬x ≤ᵥ 0) :
    (ValueGroupWithZero.mk x y)⁻¹ = ValueGroupWithZero.mk (y : R) ⟨x, hx⟩ := dif_neg hx

/-- The value group-with-zero is a linearly ordered commutative group with zero. -/
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The value group-with-zero is a linearly ordered commutative group with zero.
-/
instance : LinearOrderedCommGroupWithZero (ValueGroupWithZero R) where
  isBot_zero _ := bot_le
  exists_pair_ne := by
    refine ⟨0, 1, fun h => ?_⟩
    apply ge_of_eq at h
    rw [← ValueGroupWithZero.mk_zero 1, ← ValueGroupWithZero.mk_one_one,
      ValueGroupWithZero.mk_le_mk] at h
    simp [not_vle_one_zero] at h
  inv_zero := dif_pos .rfl
  mul_inv_cancel := ValueGroupWithZero.ind fun x y h => by
    rw [ne_eq, ← ValueGroupWithZero.mk_zero 1, ValueGroupWithZero.mk_eq_mk] at h
    simp only [Submonoid.coe_one, mul_one, zero_mul, zero_vle, and_true] at h
    grw [ValueGroupWithZero.inv_mk x y h, ← ValueGroupWithZero.mk_one_one,
      ValueGroupWithZero.mk_mul_mk, ValueGroupWithZero.mk_eq_mk, veq_mul_comm x]
    simp
  mul_lt_mul_of_pos_left := ValueGroupWithZero.ind fun a x ha ↦ ValueGroupWithZero.ind fun b y ↦
    ValueGroupWithZero.ind fun c z hbc ↦ by
      simp only [ValueGroupWithZero.mk_lt_mk,
        ValueGroupWithZero.mk_mul_mk, Submonoid.coe_mul]
      grw [veq_mul_mul_mul_comm, veq_mul_mul_mul_comm _ c]
      simp_all

section Valuation

variable {R : Type*} [Ring R] [ValuativeRel R] {x : R}

variable (R) in
/-- The "canonical" valuation associated to a valuative relation. -/
/-
**ValuativeRel.valuation** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel`。
形式化陈述：valuation : Valuation R (ValueGroupWithZero R) where toFun r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "canonical" valuation associated to a valuative relation.
-/
def valuation : Valuation R (ValueGroupWithZero R) where
  toFun r := ValueGroupWithZero.mk r 1
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := by simp
  map_add_le_max' := by simp [vle_add_cases]
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (valuation R).Compatible where
  vle_iff_le _ _ := by simp [valuation]

@[simp]
/-
**ValuativeRel.ValueGroupWithZero.lift_valuation** 是 Mathlib 中的一个定理，位于命名空间 `Valu
ativeRel.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_2} [inst : Ring R] [inst_1 : ValuativeRel R] {α : Sort u_3} 
(f : R → ↥(ValuativeRel.posSubmonoid R) → α)   (hf : ∀ (x y : R) (t s : ↥(Valuat
iveRel.posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y * ↑s ≤ᵥ x * ↑t → f x s = f y t)   
(x : R), ValuativeRel.ValueGroupWithZero.lift f hf ((ValuativeRel.valuation R) x
) = f x 1
参数：f : R → ↥(ValuativeRel.posSubmonoid R) → α；hf : ∀ (x y : R) (t s : ↥(Valuativ
eRel.posSubmonoid R)), x * ↑t ≤ᵥ y * ↑s → y * ↑s ≤ᵥ x * ↑t → f x s = f y t；x : R
；(ValuativeRel.valuation R) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ValueGroupWithZero.lift_valuation {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t)
    (x : R) :
    ValueGroupWithZero.lift f hf (valuation R x) = f x 1 :=
  rfl
/-
**ValuativeRel.valuation_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：valuation_eq_zero_iff : valuation R x = 0 ↔ x <=ᵥ 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.ValueGroupWithZero.mk_eq_zero`：∀ {R : Type u_1} [inst : Sem
iring R] [inst_1 : ValuativeRel R] (x : R) (y : ↥(ValuativeRel.posSubmonoid R)),
   ValuativeRel.ValueGroupWithZe…
-/
lemma valuation_eq_zero_iff : valuation R x = 0 ↔ x ≤ᵥ 0 :=
  ValueGroupWithZero.mk_eq_zero _ _
/-
**ValuativeRel.valuation_posSubmonoid_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valuati
veRel`。
形式化陈述：valuation_posSubmonoid_ne_zero (x : posSubmonoid R) : valuation R (x : R) 
!= 0
参数：x : posSubmonoid R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `ValuativeRel.valuation_eq_zero_iff`：valuation_eq_zero_iff : valuation R 
x = 0 ↔ x <=ᵥ 0
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma valuation_posSubmonoid_ne_zero (x : posSubmonoid R) :
    valuation R (x : R) ≠ 0 := by
  rw [ne_eq, valuation_eq_zero_iff]
  exact x.prop
/-
**ValuativeRel.ValueGroupWithZero.mk_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `Valuative
Rel.ValueGroupWithZero`。
形式化陈述：∀ {R : Type u_2} [inst : Ring R] [inst_1 : ValuativeRel R] (r : R) (s : ↥(
ValuativeRel.posSubmonoid R)),   ValuativeRel.ValueGroupWithZero.mk r s = (Valua
tiveRel.valuation R) r / (ValuativeRel.valuation R) ↑s
参数：r : R；s : ↥(ValuativeRel.posSubmonoid R)；ValuativeRel.valuation R；ValuativeRe
l.valuation R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用引理 `ValuativeRel.valuation_posSubmonoid_ne_zero`：valuation_posSubmonoid_ne_z
ero (x : posSubmonoid R) : valuation R (x : R) != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma ValueGroupWithZero.mk_eq_div (r : R) (s : posSubmonoid R) :
    ValueGroupWithZero.mk r s = valuation R r / valuation R (s : R) := by
  rw [eq_div_iff (valuation_posSubmonoid_ne_zero _)]
  simp [valuation, mk_eq_mk]

/-- Construct a valuative relation on a ring using a valuation. -/
@[instance_reducible]
/-
**ValuativeRel.ofValuation** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel`。
形式化陈述：ofValuation {S Γ : Type*} [Ring S] [LinearOrderedCommGroupWithZero Γ] (v :
 Valuation S Γ) : ValuativeRel S where vle x y
参数：v : Valuation S Γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a valuative relation on a ring using a valuation.
-/
def ofValuation
    {S Γ : Type*} [Ring S]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation S Γ) : ValuativeRel S where
  vle x y := v x ≤ v y
  vle_total x y := le_total (v x) (v y)
  vle_trans := le_trans
  vle_add hab hbc := (map_add_le_max v _ _).trans (sup_le hab hbc)
  mul_vle_mul_left _ h := by simp only [map_mul]; gcongr
  vle_mul_cancel h0 h := by
    simp only [map_mul] at h
    apply le_of_mul_le_mul_right h
    simpa [pos_iff_ne_zero] using h0
  not_vle_one_zero := by simp
  vle_mul_comm := by simp [map_mul, mul_comm]
/-
**ValuativeRel._root_.Valuation.Compatible.ofValuation** 是 Mathlib 中的一个引理，位于命名空间
 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Valuation.Compatible.ofValuation
    {S Γ : Type*} [Ring S]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation S Γ) :
    letI := ValuativeRel.ofValuation v  -- letI so that instance is inlined directly in declaration
    Valuation.Compatible v :=
  letI := ValuativeRel.ofValuation v
  ⟨fun _ _ ↦ Iff.rfl⟩
/-
**ValuativeRel.isEquiv** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：isEquiv {Γ₁ Γ₂ : Type*} [LinearOrderedCommMonoidWithZero Γ₁] [LinearOrdere
dCommMonoidWithZero Γ₂] (v₁ : Valuation R Γ₁) (v₂ : Valuation R Γ₂) [v₁.Compatib
le] [v₂.Compatible] : v₁.IsEquiv v₂
参数：v₁ : Valuation R Γ₁；v₂ : Valuation R Γ₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isEquiv {Γ₁ Γ₂ : Type*}
    [LinearOrderedCommMonoidWithZero Γ₁]
    [LinearOrderedCommMonoidWithZero Γ₂]
    (v₁ : Valuation R Γ₁)
    (v₂ : Valuation R Γ₂)
    [v₁.Compatible] [v₂.Compatible] :
    v₁.IsEquiv v₂ := by
  intro x y
  simp_rw [← Valuation.Compatible.vle_iff_le]

end Valuation

end ValuativeRel

namespace Valuation

open ValuativeRel

variable {R : Type*} [Ring R] [ValuativeRel R]
variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) [v.Compatible]
variable {x y : R}

/-
**Valuation.vle_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：vle_iff_le : x <=ᵥ y ↔ v x <= v y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.Compatible.vle_iff_le`：∀ {R : Type u_1} {Γ : Type u_2} {inst :
 Ring R} {inst_1 : LinearOrderedCommMonoidWithZero Γ} {v : Valuation R Γ}   {ins
t_2 : ValuativeRel R}…
-/
lemma vle_iff_le : x ≤ᵥ y ↔ v x ≤ v y :=
  Compatible.vle_iff_le _ _
/-
**Valuation.vlt_iff_lt** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：vlt_iff_lt : x <ᵥ y ↔ v x < v y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma vlt_iff_lt : x <ᵥ y ↔ v x < v y := by
  simp [lt_iff_not_ge, ← Compatible.vle_iff_le]
/-
**Valuation.veq_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：veq_iff_eq : x =ᵥ y ↔ v x = v y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Valuation.vle_iff_le`：vle_iff_le : x <=ᵥ y ↔ v x <= v y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma veq_iff_eq : x =ᵥ y ↔ v x = v y := by
  simp_rw [veq_def, vle_iff_le v, antisymm_iff]
/-
**Valuation.vle_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：vle_one_iff : x <=ᵥ 1 ↔ v x <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.vle_iff_le`：vle_iff_le : x <=ᵥ y ↔ v x <= v y
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma vle_one_iff : x ≤ᵥ 1 ↔ v x ≤ 1 := by simp [v.vle_iff_le]
/-
**Valuation.vlt_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：vlt_one_iff : x <ᵥ 1 ↔ v x < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.vlt_iff_lt`：vlt_iff_lt : x <ᵥ y ↔ v x < v y
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma vlt_one_iff : x <ᵥ 1 ↔ v x < 1 := by simp [v.vlt_iff_lt]
/-
**Valuation.one_vle_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：one_vle_iff : 1 <=ᵥ x ↔ 1 <= v x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.vle_iff_le`：vle_iff_le : x <=ᵥ y ↔ v x <= v y
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma one_vle_iff : 1 ≤ᵥ x ↔ 1 ≤ v x := by simp [v.vle_iff_le]
/-
**Valuation.one_vlt_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：one_vlt_iff : 1 <ᵥ x ↔ 1 < v x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.vlt_iff_lt`：vlt_iff_lt : x <ᵥ y ↔ v x < v y
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma one_vlt_iff : 1 <ᵥ x ↔ 1 < v x := by simp [v.vlt_iff_lt]

@[simp]
/-
**Valuation.apply_posSubmonoid_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：apply_posSubmonoid_ne_zero (x : posSubmonoid R) : v (x : R) != 0
参数：x : posSubmonoid R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.IsEquiv.eq_zero`：eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 
0 ↔ v₂ r = 0
· 使用引理 `ValuativeRel.isEquiv`：isEquiv {Γ₁ Γ₂ : Type*} [LinearOrderedCommMonoidWi
thZero Γ₁] [LinearOrderedCommMonoidWithZero Γ₂] (v₁ : Valuation R Γ₁) (v₂ : Valu
ation R Γ₂…
· 使用定理 `ValuativeRel.instCompatibleValueGroupWithZeroValuation`：∀ {R : Type u_2}
 [inst : Ring R] [inst_1 : ValuativeRel R], (ValuativeRel.valuation R).Compatibl
e
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma apply_posSubmonoid_ne_zero (x : posSubmonoid R) : v (x : R) ≠ 0 := by
  simp [(isEquiv v (valuation R)).eq_zero, valuation_posSubmonoid_ne_zero]

@[simp]
/-
**Valuation.apply_posSubmonoid_pos** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：apply_posSubmonoid_pos (x : posSubmonoid R) : 0 < v x
参数：x : posSubmonoid R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `Valuation.apply_posSubmonoid_ne_zero`：apply_posSubmonoid_ne_zero (x : po
sSubmonoid R) : v (x : R) != 0
-/
lemma apply_posSubmonoid_pos (x : posSubmonoid R) : 0 < v x :=
  zero_lt_iff.mpr <| v.apply_posSubmonoid_ne_zero x

end Valuation

namespace ValuativeRel

variable {R : Type*} [Semiring R] [ValuativeRel R]

variable (R) in
/-- An alias for endowing a ring with a preorder defined as the valuative relation. -/
/-
**ValuativeRel.WithPreorder** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel`。
形式化陈述：WithPreorder
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alias for endowing a ring with a preorder defined as the valuative relation.
-/
def WithPreorder := R

/-- The ring instance on `WithPreorder R` arising from the ring structure on `R`. -/
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring instance on `WithPreorder R` arising from the ring structure on `R`.
-/
instance : Semiring (WithPreorder R) := inferInstanceAs (Semiring R)

/-- The preorder on `WithPreorder R` arising from the valuative relation on `R`. -/
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preorder on `WithPreorder R` arising from the valuative relation on `R`.
-/
instance : Preorder (WithPreorder R) where
  le (x y : R) := x ≤ᵥ y
  le_refl _ := vle_refl _
  le_trans _ _ _ := vle_trans
  lt (x y : R) := x <ᵥ y
  lt_iff_le_not_ge (x y : R) := by have := vle_total x y; grind

/-- The valuative relation on `WithPreorder R` arising from the valuative relation on `R`.
This is defined as the preorder itself. -/
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuative relation on `WithPreorder R` arising from the valuative relation o
n `R`.
This is defined as the preorder itself.
-/
instance : ValuativeRel (WithPreorder R) where
  vle := (· ≤ ·)
  vle_total := vle_total (R := R)
  vle_trans := vle_trans (R := R)
  vle_add := vle_add (R := R)
  mul_vle_mul_left := mul_vle_mul_left (R := R)
  vle_mul_cancel := vle_mul_cancel (R := R)
  not_vle_one_zero := not_vle_one_zero (R := R)
  vle_mul_comm := vle_mul_comm (R := R)
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ValuativePreorder (WithPreorder R) where
  vle_iff_le _ _ := Iff.rfl

variable (R) in
/-- The support of the valuation on `R`. -/
/-
**ValuativeRel.supp** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel`。
形式化陈述：supp : Ideal R where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of the valuation on `R`.
-/
def supp : Ideal R where
  carrier := { x | x ≤ᵥ 0 }
  add_mem' ha hb := vle_add ha hb
  zero_mem' := vle_refl _
  smul_mem' x _ h := by simpa using mul_vle_mul_right h _
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (supp R).IsTwoSided where
  mul_mem_of_left _ h := by simpa [supp] using mul_vle_mul_left h _

@[simp]
/-
**ValuativeRel.supp_def** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：supp_def (x : R) : x in supp R ↔ x <=ᵥ 0
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.refl`：∀ (a : Prop), a ↔ a
-/
lemma supp_def (x : R) : x ∈ supp R ↔ x ≤ᵥ 0 := Iff.refl _
/-
**ValuativeRel.supp_eq_valuation_supp** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：supp_eq_valuation_supp {R : Type*} [CommRing R] [ValuativeRel R] : supp R 
= (valuation R).supp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `ValuativeRel.valuation_eq_zero_iff`：valuation_eq_zero_iff : valuation R 
x = 0 ↔ x <=ᵥ 0
-/
lemma supp_eq_valuation_supp {R : Type*} [CommRing R] [ValuativeRel R] :
    supp R = (valuation R).supp := by
  ext
  simpa using valuation_eq_zero_iff.symm
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (supp R).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one]
    exact not_vle_one_zero
  mem_or_mem' h := by
    by_contra! h'
    simp only [supp_def, not_vle] at h h'
    exact vlt.not_vle (zero_vlt_mul h'.1 h'.2) h

section Ring

variable {R : Type*} [Ring R] [ValuativeRel R] {a b c d : R}

@[deprecated (since := "2026-01-06")] alias vle_mul_right_iff := mul_vle_mul_iff_left

@[deprecated (since := "2026-01-06")] alias vle_mul_left_iff := mul_vle_mul_iff_right

@[deprecated (since := "2026-01-06")] alias vlt_mul_right_iff := mul_vlt_mul_iff_left

@[deprecated (since := "2026-01-06")] alias vlt_mul_left_iff := mul_vlt_mul_iff_right

/-
**ValuativeRel.mul_vlt_mul_of_vlt_of_vle** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel
`。
形式化陈述：mul_vlt_mul_of_vlt_of_vle (hab : a <ᵥ b) (hcd : c <=ᵥ d) (hd : 0 <ᵥ d) : a
 * c <ᵥ b * d
参数：hab : a <ᵥ b；hcd : c <=ᵥ d；hd : 0 <ᵥ d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle.trans_vlt`：∀ {R : Type u_1} [inst : Semiring R] [inst_1
 : ValuativeRel R] {x y z : R}, x ≤ᵥ y → y <ᵥ z → x <ᵥ z
· 使用引理 `ValuativeRel.mul_vle_mul_right`：mul_vle_mul_right (h : x <=ᵥ y) (z) : z 
* x <=ᵥ z * y
· 使用定理 `ValuativeRel.mul_vlt_mul_left`：∀ {R : Type u_1} [inst : Semiring R] [ins
t_1 : ValuativeRel R] {x y z : R}, 0 <ᵥ z → x <ᵥ y → x * z <ᵥ y * z
-/
lemma mul_vlt_mul_of_vlt_of_vle (hab : a <ᵥ b) (hcd : c ≤ᵥ d) (hd : 0 <ᵥ d) :
    a * c <ᵥ b * d :=
  (mul_vle_mul_right hcd _).trans_vlt (mul_vlt_mul_left hd hab)
/-
**ValuativeRel.mul_vlt_mul_of_vle_of_vlt** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel
`。
形式化陈述：mul_vlt_mul_of_vle_of_vlt (hab : a <=ᵥ b) (hcd : c <ᵥ d) (ha : 0 <ᵥ a) : a
 * c <ᵥ b * d
参数：hab : a <=ᵥ b；hcd : c <ᵥ d；ha : 0 <ᵥ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vlt.trans_vle`：∀ {R : Type u_1} [inst : Semiring R] [inst_1
 : ValuativeRel R] {x y z : R}, x <ᵥ y → y ≤ᵥ z → x <ᵥ z
· 使用定理 `ValuativeRel.mul_vlt_mul_right`：∀ {R : Type u_1} [inst : Semiring R] [in
st_1 : ValuativeRel R] {x y z : R}, 0 <ᵥ x → y <ᵥ z → x * y <ᵥ x * z
· 使用定理 `ValuativeRel.mul_vle_mul_left`：∀ {R : Type u_1} {inst : Semiring R} [sel
f : ValuativeRel R] {x y : R}, x ≤ᵥ y → ∀ (z : R), x * z ≤ᵥ y * z
-/
lemma mul_vlt_mul_of_vle_of_vlt (hab : a ≤ᵥ b) (hcd : c <ᵥ d) (ha : 0 <ᵥ a) :
    a * c <ᵥ b * d :=
  (mul_vlt_mul_right ha hcd).trans_vle (mul_vle_mul_left hab _)

@[gcongr]
/-
**ValuativeRel.mul_vlt_mul** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：mul_vlt_mul (hab : a <ᵥ b) (hcd : c <ᵥ d) : a * c <ᵥ b * d
参数：hab : a <ᵥ b；hcd : c <ᵥ d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.vle.trans_vlt`：∀ {R : Type u_1} [inst : Semiring R] [inst_1
 : ValuativeRel R] {x y z : R}, x ≤ᵥ y → y <ᵥ z → x <ᵥ z
· 使用引理 `ValuativeRel.mul_vle_mul_right`：mul_vle_mul_right (h : x <=ᵥ y) (z) : z 
* x <=ᵥ z * y
· 使用定理 `ValuativeRel.vlt.vle`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x y : R}, x <ᵥ y → x ≤ᵥ y
· 使用定理 `ValuativeRel.mul_vlt_mul_left`：∀ {R : Type u_1} [inst : Semiring R] [ins
t_1 : ValuativeRel R] {x y z : R}, 0 <ᵥ z → x <ᵥ y → x * z <ᵥ y * z
· 使用定理 `ValuativeRel.zero_vle`：zero_vle (x : R) : 0 <=ᵥ x
-/
lemma mul_vlt_mul (hab : a <ᵥ b) (hcd : c <ᵥ d) : a * c <ᵥ b * d :=
  (mul_vle_mul_right hcd.vle _).trans_vlt (mul_vlt_mul_left ((zero_vle c).trans_vlt hcd) hab)
/-
**ValuativeRel.pow_vle_pow** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：pow_vle_pow (hab : a <=ᵥ b) (n : Nat) : a ^ n <=ᵥ b ^ n
参数：hab : a <=ᵥ b；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `ValuativeRel.mul_vle_mul`：mul_vle_mul {x x' y y' : R} (h1 : x <=ᵥ y) (h2
 : x' <=ᵥ y') : x * x' <=ᵥ y * y'
-/
lemma pow_vle_pow (hab : a ≤ᵥ b) (n : ℕ) : a ^ n ≤ᵥ b ^ n := by
  induction n with
  | zero => simp
  | succ _ hn => simp [pow_succ, mul_vle_mul hn hab]
/-
**ValuativeRel.pow_vlt_pow** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：pow_vlt_pow (hab : a <ᵥ b) {n : Nat} (hn : n != 0) : a ^ n <ᵥ b ^ n
参数：hab : a <ᵥ b；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma pow_vlt_pow (hab : a <ᵥ b) {n : ℕ} (hn : n ≠ 0) : a ^ n <ᵥ b ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => contradiction
  | one => simpa
  | more _ _ => simp_all [pow_succ, mul_vlt_mul]
/-
**ValuativeRel.pow_vle_pow_of_vle_one** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：pow_vle_pow_of_vle_one (ha : a <=ᵥ 1) {n m : Nat} (hnm : n <= m) : a ^ m <
=ᵥ a ^ n
参数：ha : a <=ᵥ 1；hnm : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `ValuativeRel.mul_vle_mul_right`：mul_vle_mul_right (h : x <=ᵥ y) (z) : z 
* x <=ᵥ z * y
· 使用引理 `ValuativeRel.pow_vle_pow`：pow_vle_pow (hab : a <=ᵥ b) (n : Nat) : a ^ n 
<=ᵥ b ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma pow_vle_pow_of_vle_one (ha : a ≤ᵥ 1) {n m : ℕ} (hnm : n ≤ m) : a ^ m ≤ᵥ a ^ n := by
  obtain ⟨m, rfl⟩ := exists_add_of_le hnm
  simpa [pow_add] using mul_vle_mul_right (pow_vle_pow ha m) _
/-
**ValuativeRel.pow_vle_pow_of_one_vle** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：pow_vle_pow_of_one_vle (ha : 1 <=ᵥ a) {n m : Nat} (hnm : n <= m) : a ^ n <
=ᵥ a ^ m
参数：ha : 1 <=ᵥ a；hnm : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `ValuativeRel.mul_vle_mul_right`：mul_vle_mul_right (h : x <=ᵥ y) (z) : z 
* x <=ᵥ z * y
· 使用引理 `ValuativeRel.pow_vle_pow`：pow_vle_pow (hab : a <=ᵥ b) (n : Nat) : a ^ n 
<=ᵥ b ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma pow_vle_pow_of_one_vle (ha : 1 ≤ᵥ a) {n m : ℕ} (hnm : n ≤ m) : a ^ n ≤ᵥ a ^ m := by
  obtain ⟨m, rfl⟩ := exists_add_of_le hnm
  simpa [pow_add] using mul_vle_mul_right (pow_vle_pow ha m) _

end Ring

section DivisionRing

variable {K : Type*} [DivisionRing K] [ValuativeRel K] {a b c x : K}

@[simp]
/-
**ValuativeRel.vle_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：vle_zero_iff : a <=ᵥ 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ValuativeRel.supp_def`：supp_def (x : R) : x in supp R ↔ x <=ᵥ 0
· 使用定理 `Ideal.eq_bot_of_prime`：eq_bot_of_prime [h : I.IsPrime] : I = ⊥
· 使用定理 `ValuativeRel.instIsPrimeSupp`：∀ {R : Type u_1} [inst : Semiring R] [inst
_1 : ValuativeRel R], (ValuativeRel.supp R).IsPrime
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma vle_zero_iff : a ≤ᵥ 0 ↔ a = 0 := by
  rw [← supp_def, Ideal.eq_bot_of_prime (supp K), Ideal.mem_bot]

@[simp]
/-
**ValuativeRel.zero_vlt_iff** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：zero_vlt_iff : 0 <ᵥ a ↔ a != 0
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
lemma zero_vlt_iff : 0 <ᵥ a ↔ a ≠ 0 := by
  simp [vlt]

@[simp]
/-
**ValuativeRel.zero_veq_iff** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：zero_veq_iff : a =ᵥ 0 ↔ a = 0 where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ValuativeRel.vle_zero_iff`：vle_zero_iff : a <=ᵥ 0 ↔ a = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma zero_veq_iff : a =ᵥ 0 ↔ a = 0 where
  mp h := vle_zero_iff.1 h.1
  mpr := by simp +contextual

@[simp]
/-
**ValuativeRel.veq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：veq_zero_iff : 0 =ᵥ a ↔ 0 = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ValuativeRel.veq_comm`：veq_comm : x =ᵥ y ↔ y =ᵥ x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `ValuativeRel.zero_veq_iff`：zero_veq_iff : a =ᵥ 0 ↔ a = 0 where mp h
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma veq_zero_iff : 0 =ᵥ a ↔ 0 = a := by
  rw [veq_comm, eq_comm, zero_veq_iff]
/-
**ValuativeRel.vle_div_iff** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：vle_div_iff (hc : c != 0) : a <=ᵥ b / c ↔ a * c <=ᵥ b
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuativeRel.mul_vle_mul_iff_left`：∀ {R : Type u_1} [inst : Semiring R] 
[inst_1 : ValuativeRel R] {x y z : R}, 0 <ᵥ z → (x * z ≤ᵥ y * z ↔ x ≤ᵥ y)
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma vle_div_iff (hc : c ≠ 0) : a ≤ᵥ b / c ↔ a * c ≤ᵥ b := by
  rw [← mul_vle_mul_iff_left (by simpa), div_mul_cancel₀ _ (by lia)]
/-
**ValuativeRel.div_vle_iff** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：div_vle_iff (hc : c != 0) : a / c <=ᵥ b ↔ a <=ᵥ b * c
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuativeRel.mul_vle_mul_iff_left`：∀ {R : Type u_1} [inst : Semiring R] 
[inst_1 : ValuativeRel R] {x y z : R}, 0 <ᵥ z → (x * z ≤ᵥ y * z ↔ x ≤ᵥ y)
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma div_vle_iff (hc : c ≠ 0) : a / c ≤ᵥ b ↔ a ≤ᵥ b * c := by
  rw [← mul_vle_mul_iff_left (by simpa), div_mul_cancel₀ _ (by lia)]
/-
**ValuativeRel.one_vle_div_iff** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：one_vle_div_iff (hb : b != 0) : 1 <=ᵥ a / b ↔ b <=ᵥ a
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ValuativeRel.vle_div_iff`：vle_div_iff (hc : c != 0) : a <=ᵥ b / c ↔ a * 
c <=ᵥ b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma one_vle_div_iff (hb : b ≠ 0) : 1 ≤ᵥ a / b ↔ b ≤ᵥ a := by
  simp [vle_div_iff hb]
/-
**ValuativeRel.div_vle_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：div_vle_one_iff (hb : b != 0) : a / b <=ᵥ 1 ↔ a <=ᵥ b
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ValuativeRel.div_vle_iff`：div_vle_iff (hc : c != 0) : a / c <=ᵥ b ↔ a <=
ᵥ b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma div_vle_one_iff (hb : b ≠ 0) : a / b ≤ᵥ 1 ↔ a ≤ᵥ b := by
  simp [div_vle_iff hb]
/-
**ValuativeRel.one_vle_inv** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：one_vle_inv (hx : x != 0) : 1 <=ᵥ x⁻¹ ↔ x <=ᵥ 1
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `ValuativeRel.one_vle_div_iff`：one_vle_div_iff (hb : b != 0) : 1 <=ᵥ a / 
b ↔ b <=ᵥ a
-/
lemma one_vle_inv (hx : x ≠ 0) : 1 ≤ᵥ x⁻¹ ↔ x ≤ᵥ 1 := by
  simpa using one_vle_div_iff (a := 1) hx
/-
**ValuativeRel.inv_vle_one** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：inv_vle_one (hx : x != 0) : x⁻¹ <=ᵥ 1 ↔ 1 <=ᵥ x
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `ValuativeRel.div_vle_one_iff`：div_vle_one_iff (hb : b != 0) : a / b <=ᵥ 
1 ↔ a <=ᵥ b
-/
lemma inv_vle_one (hx : x ≠ 0) : x⁻¹ ≤ᵥ 1 ↔ 1 ≤ᵥ x := by
  simpa using div_vle_one_iff (a := 1) hx
/-
**ValuativeRel.inv_vlt_one** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：inv_vlt_one (hx : x != 0) : x⁻¹ <ᵥ 1 ↔ 1 <ᵥ x
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `ValuativeRel.one_vle_inv`：one_vle_inv (hx : x != 0) : 1 <=ᵥ x⁻¹ ↔ x <=ᵥ 
1
-/
lemma inv_vlt_one (hx : x ≠ 0) : x⁻¹ <ᵥ 1 ↔ 1 <ᵥ x :=
  (one_vle_inv hx).not
/-
**ValuativeRel.one_vlt_inv** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：one_vlt_inv (hx : x != 0) : 1 <ᵥ x⁻¹ ↔ x <ᵥ 1
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `ValuativeRel.inv_vle_one`：inv_vle_one (hx : x != 0) : x⁻¹ <=ᵥ 1 ↔ 1 <=ᵥ 
x
-/
lemma one_vlt_inv (hx : x ≠ 0) : 1 <ᵥ x⁻¹ ↔ x <ᵥ 1 :=
  (inv_vle_one hx).not

end DivisionRing

open NNReal in variable (R) in
/-- An auxiliary structure used to define `IsRankLeOne`. -/
/-
**ValuativeRel.RankLeOneStruct** 是 Mathlib 中的一个归纳类型，位于命名空间 `ValuativeRel`。
形式化陈述：(R : Type u_1) → [inst : Semiring R] → [ValuativeRel R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary structure used to define `IsRankLeOne`.
-/
structure RankLeOneStruct where
  /-- The embedding of the value group-with-zero into the nonnegative reals. -/
  emb : ValueGroupWithZero R →*₀ ℝ≥0
  strictMono : StrictMono emb

variable (R) in
/-- We say that a ring with a valuative relation is of rank one if
there exists a strictly monotone embedding of the "canonical" value group-with-zero into
the nonnegative reals, and the image of this embedding contains some element different
from `0` and `1`. -/
/-
**ValuativeRel.IsRankLeOne** 是 Mathlib 中的一个归纳类型，位于命名空间 `ValuativeRel`。
形式化陈述：(R : Type u_1) → [inst : Semiring R] → [ValuativeRel R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a ring with a valuative relation is of rank one if
there exists a strictly monotone embedding of the "canonical" value group-with-z
ero into
the nonnegative reals, and the image of this embedding contains some element dif
ferent
from `0` and `1`.
-/
class IsRankLeOne where
  nonempty : Nonempty (RankLeOneStruct R)

variable (R) in
/-- We say that a valuative relation on a ring is *nontrivial* if the
  value group-with-zero is nontrivial, meaning that it has an element
  which is different from 0 and 1. -/
/-
**ValuativeRel.IsNontrivial** 是 Mathlib 中的一个归纳类型，位于命名空间 `ValuativeRel`。
形式化陈述：(R : Type u_1) → [inst : Semiring R] → [ValuativeRel R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a valuative relation on a ring is *nontrivial* if the
  value group-with-zero is nontrivial, meaning that it has an element
  which is different from 0 and 1.
-/
class IsNontrivial where
  condition : ∃ γ : ValueGroupWithZero R, γ ≠ 0 ∧ γ ≠ 1
/-
**ValuativeRel.IsNontrivial.exists_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRe
l.IsNontrivial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] [ValuativeR
el.IsNontrivial R], ∃ γ, 0 < γ ∧ γ < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.IsNontrivial.condition`：∀ {R : Type u_1} {inst : Semiring R
} {inst_1 : ValuativeRel R} [self : ValuativeRel.IsNontrivial R], ∃ γ, γ ≠ 0 ∧ γ
 ≠ 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_or_lt_iff_ne`：lt_or_lt_iff_ne : a < b ∨ b < a ↔ a != b
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma IsNontrivial.exists_lt_one [IsNontrivial R] :
    ∃ γ : ValueGroupWithZero R, 0 < γ ∧ γ < 1 := by
  obtain ⟨γ, h0, h1⟩ := IsNontrivial.condition (R := R)
  obtain h1 | h1 := lt_or_lt_iff_ne.mpr h1
  · exact ⟨γ, zero_lt_iff.mpr h0, h1⟩
  · exact ⟨γ⁻¹, by simpa [zero_lt_iff], by simp [inv_lt_one_iff₀, h0, h1]⟩
/-
**ValuativeRel.isNontrivial_iff_nontrivial_units** 是 Mathlib 中的一个引理，位于命名空间 `Valu
ativeRel`。
形式化陈述：isNontrivial_iff_nontrivial_units : IsNontrivial R ↔ Nontrivial (ValueGrou
pWithZero R)ˣ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isNontrivial_iff_nontrivial_units :
    IsNontrivial R ↔ Nontrivial (ValueGroupWithZero R)ˣ := by
  constructor
  · rintro ⟨γ, hγ, hγ'⟩
    refine ⟨Units.mk0 _ hγ, 1, ?_⟩
    simp [← Units.val_eq_one, hγ']
  · rintro ⟨r, s, h⟩
    rcases eq_or_ne r 1 with rfl | hr
    · exact ⟨s.val, by simp, by simpa using h.symm⟩
    · exact ⟨r.val, by simp, by simpa using hr⟩

section Valuation

variable {R : Type*} [Ring R] [ValuativeRel R]

/-
**ValuativeRel.isNontrivial_iff_isNontrivial** 是 Mathlib 中的一个引理，位于命名空间 `Valuativ
eRel`。
形式化陈述：isNontrivial_iff_isNontrivial {Γ₀ : Type*} [LinearOrderedCommMonoidWithZer
o Γ₀] (v : Valuation R Γ₀) [v.Compatible] : IsNontrivial R ↔ v.IsNontrivial
参数：v : Valuation R Γ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.ValueGroupWithZero.ind`：∀ {R : Type u_1} [inst : Semiring R
] [inst_1 : ValuativeRel R] {motive : ValuativeRel.ValueGroupWithZero R → Prop},
   (∀ (x : R) (y : ↥(Valu…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Valuation.Compatible.vle_iff_le`：∀ {R : Type u_1} {Γ : Type u_2} {inst :
 Ring R} {inst_1 : LinearOrderedCommMonoidWithZero Γ} {v : Valuation R Γ}   {ins
t_2 : ValuativeRel R}…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Valuation.IsEquiv.eq_zero`：eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 
0 ↔ v₂ r = 0
· 使用引理 `ValuativeRel.isEquiv`：isEquiv {Γ₁ Γ₂ : Type*} [LinearOrderedCommMonoidWi
thZero Γ₁] [LinearOrderedCommMonoidWithZero Γ₂] (v₁ : Valuation R Γ₁) (v₂ : Valu
ation R Γ₂…
· 使用定理 `ValuativeRel.instCompatibleValueGroupWithZeroValuation`：∀ {R : Type u_2}
 [inst : Ring R] [inst_1 : ValuativeRel R], (ValuativeRel.valuation R).Compatibl
e
· 使用引理 `Valuation.IsEquiv.eq_one_iff_eq_one`：eq_one_iff_eq_one (h : v₁.IsEquiv v
₂) {x : R} : v₁ x = 1 ↔ v₂ x = 1
-/
lemma isNontrivial_iff_isNontrivial
    {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) [v.Compatible] :
    IsNontrivial R ↔ v.IsNontrivial := by
  constructor
  · rintro ⟨r, hr, hr'⟩
    induction r using ValueGroupWithZero.ind with | mk r s
    have hγ : v r ≠ 0 := by simpa [Valuation.Compatible.vle_iff_le (v := v)] using hr
    have hγ' : v r ≤ v s → v r < v s := by
      simpa [Valuation.Compatible.vle_iff_le (v := v)] using hr'
    by_cases hr : v r = 1
    · exact ⟨s, by simp, fun h ↦ by simp [h, hr] at hγ'⟩
    · exact ⟨r, by simpa using hγ, hr⟩
  · rintro ⟨r, hr, hr'⟩
    exact ⟨valuation R r, (isEquiv v (valuation R)).eq_zero.ne.mp hr,
      by simpa [(isEquiv v (valuation R)).eq_one_iff_eq_one] using hr'⟩
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    [IsNontrivial R] (v : Valuation R Γ₀) [v.Compatible] :
    v.IsNontrivial := by rwa [← isNontrivial_iff_isNontrivial]
/-
**ValuativeRel.ValueGroupWithZero.mk_eq_valuation** 是 Mathlib 中的一个定理，位于命名空间 `Val
uativeRel.ValueGroupWithZero`。
形式化陈述：∀ {K : Type u_3} [inst : DivisionRing K] [inst_1 : ValuativeRel K] (x : K)
 (y : ↥(ValuativeRel.posSubmonoid K)),   ValuativeRel.ValueGroupWithZero.mk x y 
= (ValuativeRel.valuation K) (x / ↑y)
参数：x : K；y : ↥(ValuativeRel.posSubmonoid K)；ValuativeRel.valuation K；x / ↑y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.map_div`：map_div {R : Type*} [DivisionRing R] (v : Valuation R
 Γ₀) : forall x y, v (x / y) = v x / v y
· 使用定理 `ValuativeRel.ValueGroupWithZero.mk_eq_div`：∀ {R : Type u_2} [inst : Ring
 R] [inst_1 : ValuativeRel R] (r : R) (s : ↥(ValuativeRel.posSubmonoid R)),   Va
luativeRel.ValueGroupWithZero.m…
-/
lemma ValueGroupWithZero.mk_eq_valuation {K : Type*} [DivisionRing K] [ValuativeRel K]
    (x : K) (y : posSubmonoid K) :
    ValueGroupWithZero.mk x y = valuation K (x / y) := by
  rw [Valuation.map_div, ValueGroupWithZero.mk_eq_div]
/-
**ValuativeRel.exists_valuation_div_valuation_eq** 是 Mathlib 中的一个引理，位于命名空间 `Valu
ativeRel`。
形式化陈述：exists_valuation_div_valuation_eq (γ : ValueGroupWithZero R) : exists (a :
 R) (b : posSubmonoid R), valuation _ a / valuation _ (b : R) = γ
参数：γ : ValueGroupWithZero R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.ValueGroupWithZero.ind`：∀ {R : Type u_1} [inst : Semiring R
] [inst_1 : ValuativeRel R] {motive : ValuativeRel.ValueGroupWithZero R → Prop},
   (∀ (x : R) (y : ↥(Valu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `ValuativeRel.ValueGroupWithZero.inv_mk`：∀ {R : Type u_1} [inst : Semirin
g R] [inst_1 : ValuativeRel R] (x : R) (y : ↥(ValuativeRel.posSubmonoid R))   (h
x : ¬x ≤ᵥ 0), (ValuativeRel.…
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_valuation_div_valuation_eq (γ : ValueGroupWithZero R) :
    ∃ (a : R) (b : posSubmonoid R), valuation _ a / valuation _ (b : R) = γ := by
  induction γ using ValueGroupWithZero.ind with | mk a b
  use a, b
  simp [valuation, div_eq_mul_inv, ValueGroupWithZero.inv_mk (b : R) 1 b.prop]
/-
**ValuativeRel.exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq** 是 M
athlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq (γ : (ValueGro
upWithZero R)ˣ) : exists (a b : posSubmonoid R), valuation R a / valuation _ (b 
: R) = γ
参数：γ : (ValueGroupWithZero R)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ValuativeRel.exists_valuation_div_valuation_eq`：exists_valuation_div_val
uation_eq (γ : ValueGroupWithZero R) : exists (a : R) (b : posSubmonoid R), valu
ation _ a / valuation _ (b : R) = γ
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ValuativeRel.valuation_eq_zero_iff`：valuation_eq_zero_iff : valuation R 
x = 0 ↔ x <=ᵥ 0
· 使用定理 `ValuativeRel.not_vlt`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x y : R}, ¬x <ᵥ y ↔ y ≤ᵥ x
· 使用引理 `ValuativeRel.posSubmonoid_def`：posSubmonoid_def (x : R) : x in posSubmon
oid R ↔ 0 <ᵥ x
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq (γ : (ValueGroupWithZero R)ˣ) :
    ∃ (a b : posSubmonoid R), valuation R a / valuation _ (b : R) = γ := by
  obtain ⟨a, b, hab⟩ := exists_valuation_div_valuation_eq γ.val
  lift a to posSubmonoid R using by
    contrapose! hab
    rw [posSubmonoid_def, not_vlt, ← valuation_eq_zero_iff] at hab
    simp [hab, eq_comm]
  use a, b

-- See `exists_valuation_div_valuation_eq` for the version that works for all rings.
/-
**ValuativeRel.valuation_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ValuativeRel`。
形式化陈述：valuation_surjective {K : Type*} [DivisionRing K] [ValuativeRel K] : Funct
ion.Surjective (valuation K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.ValueGroupWithZero.ind`：∀ {R : Type u_1} [inst : Semiring R
] [inst_1 : ValuativeRel R] {motive : ValuativeRel.ValueGroupWithZero R → Prop},
   (∀ (x : R) (y : ↥(Valu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuativeRel.ValueGroupWithZero.mk_eq_valuation`：∀ {K : Type u_3} [inst 
: DivisionRing K] [inst_1 : ValuativeRel K] (x : K) (y : ↥(ValuativeRel.posSubmo
noid K)),   ValuativeRel.ValueGroupWi…
-/
theorem valuation_surjective {K : Type*} [DivisionRing K] [ValuativeRel K] :
    Function.Surjective (valuation K) :=
  ValueGroupWithZero.ind (ValueGroupWithZero.mk_eq_valuation · · ▸ ⟨_, rfl⟩)

end Valuation

variable (R) in
/-- A ring with a valuative relation is discrete if its value group-with-zero
has a maximal element `< 1`. -/
/-
**ValuativeRel.IsDiscrete** 是 Mathlib 中的一个归纳类型，位于命名空间 `ValuativeRel`。
形式化陈述：(R : Type u_1) → [inst : Semiring R] → [ValuativeRel R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring with a valuative relation is discrete if its value group-with-zero
has a maximal element `< 1`.
-/
class IsDiscrete where
  has_maximal_element :
    ∃ γ : ValueGroupWithZero R, γ < 1 ∧ (∀ δ : ValueGroupWithZero R, δ < 1 → δ ≤ γ)

variable (R) in
/-- The maximal element that is `< 1` in the value group of a discrete valuation. -/
-- TODO: Link to `Valuation.IsUniformizer` once we connect `Valuation.IsRankOneDiscrete` with
-- `ValuativeRel`.
noncomputable
/-
**ValuativeRel.uniformizer** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel`。
形式化陈述：uniformizer [IsDiscrete R] : ValueGroupWithZero R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.IsDiscrete.has_maximal_element`：∀ {R : Type u_1} {inst : Se
miring R} {inst_1 : ValuativeRel R} [self : ValuativeRel.IsDiscrete R],   ∃ γ < 
1, ∀ δ < 1, δ ≤ γ
-/
def uniformizer [IsDiscrete R] : ValueGroupWithZero R :=
  IsDiscrete.has_maximal_element.choose
/-
**ValuativeRel.uniformizer_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：uniformizer_lt_one [IsDiscrete R] : uniformizer R < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ValuativeRel.IsDiscrete.has_maximal_element`：∀ {R : Type u_1} {inst : Se
miring R} {inst_1 : ValuativeRel R} [self : ValuativeRel.IsDiscrete R],   ∃ γ < 
1, ∀ δ < 1, δ ≤ γ
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma uniformizer_lt_one [IsDiscrete R] :
    uniformizer R < 1 := IsDiscrete.has_maximal_element.choose_spec.1
/-
**ValuativeRel.le_uniformizer_iff** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：le_uniformizer_iff [IsDiscrete R] {a : ValueGroupWithZero R} : a <= unifor
mizer R ↔ a < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `ValuativeRel.uniformizer_lt_one`：uniformizer_lt_one [IsDiscrete R] : uni
formizer R < 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ValuativeRel.IsDiscrete.has_maximal_element`：∀ {R : Type u_1} {inst : Se
miring R} {inst_1 : ValuativeRel R} [self : ValuativeRel.IsDiscrete R],   ∃ γ < 
1, ∀ δ < 1, δ ≤ γ
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma le_uniformizer_iff [IsDiscrete R] {a : ValueGroupWithZero R} :
    a ≤ uniformizer R ↔ a < 1 :=
  ⟨fun h ↦ h.trans_lt uniformizer_lt_one,
    IsDiscrete.has_maximal_element.choose_spec.2 a⟩
/-
**ValuativeRel.uniformizer_pos** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：uniformizer_pos [IsDiscrete R] [IsNontrivial R] : 0 < uniformizer R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.IsNontrivial.exists_lt_one`：∀ {R : Type u_1} [inst : Semiri
ng R] [inst_1 : ValuativeRel R] [ValuativeRel.IsNontrivial R], ∃ γ, 0 < γ ∧ γ < 
1
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ValuativeRel.le_uniformizer_iff`：le_uniformizer_iff [IsDiscrete R] {a : 
ValueGroupWithZero R} : a <= uniformizer R ↔ a < 1
-/
lemma uniformizer_pos [IsDiscrete R] [IsNontrivial R] :
    0 < uniformizer R := by
  obtain ⟨γ, hγ, hγ'⟩ := IsNontrivial.exists_lt_one (R := R)
  exact hγ.trans_le (le_uniformizer_iff.mpr hγ')

@[simp]
/-
**ValuativeRel.uniformizer_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：uniformizer_ne_zero [IsDiscrete R] [IsNontrivial R] : uniformizer R != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `ValuativeRel.uniformizer_pos`：uniformizer_pos [IsDiscrete R] [IsNontrivi
al R] : 0 < uniformizer R
-/
lemma uniformizer_ne_zero [IsDiscrete R] [IsNontrivial R] :
    uniformizer R ≠ 0 :=
  uniformizer_pos.ne'
/-
**ValuativeRel.uniformizer_inv_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：uniformizer_inv_le_iff [IsDiscrete R] [IsNontrivial R] {a : ValueGroupWith
Zero R} : (uniformizer R)⁻¹ <= a ↔ 1 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用引理 `inv_le_comm₀`：inv_le_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ <= b ↔ b⁻¹ <=
 a
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
· 使用定理 `LinearOrderedCommMonoidWithZero.toMulPosStrictMono`：∀ {α : Type u_1} [in
st : LinearOrderedCommMonoidWithZero α], MulPosStrictMono α
· 使用引理 `ValuativeRel.uniformizer_pos`：uniformizer_pos [IsDiscrete R] [IsNontrivi
al R] : 0 < uniformizer R
· 使用引理 `ValuativeRel.le_uniformizer_iff`：le_uniformizer_iff [IsDiscrete R] {a : 
ValueGroupWithZero R} : a <= uniformizer R ↔ a < 1
· 使用引理 `inv_lt_one₀`：inv_lt_one₀ (ha : 0 < a) : a⁻¹ < 1 ↔ 1 < a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma uniformizer_inv_le_iff [IsDiscrete R] [IsNontrivial R] {a : ValueGroupWithZero R} :
    (uniformizer R)⁻¹ ≤ a ↔ 1 < a := by
  by_cases ha : a = 0
  · simp [ha]
  replace ha : 0 < a := bot_lt_iff_ne_bot.mpr ha
  rw [inv_le_comm₀ uniformizer_pos ha, le_uniformizer_iff, inv_lt_one₀ ha]

variable {R Γ : Type*} [Ring R] [ValuativeRel R] [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation R Γ)

open MonoidWithZeroHom ValueGroup₀

namespace ValueGroupWithZero

/-- The `ValueGroupWithZero R` is the "minimal" value group (with zero) among all value groups
of valuations that are compatible with the valuative relation, in the sense that it is canonically
isomorphic to the subgroup (with zero) generated by `v '' R` for any compatible `v`.
`ValueGroupWithZero.embed v` is exactly this isomorphism map; it will later be upgraded to
`ValueGroupWithZero.orderMonoidIso v`. -/
noncomputable
/-
**ValuativeRel.ValueGroupWithZero.embed** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeRel.
ValueGroupWithZero`。
形式化陈述：embed [v.Compatible] : ValueGroupWithZero R ->*₀ ValueGroup₀ (.ofClass v) 
where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def embed [v.Compatible] : ValueGroupWithZero R →*₀ ValueGroup₀ (.ofClass v) where
  toFun := ValueGroupWithZero.lift
    (fun r s ↦ (restrict₀ (.ofClass v) r / (restrict₀ (.ofClass v) s))) <| by
    intro x y r s
    simp only [Valuation.Compatible.vle_iff_le (v := v), map_mul, ← and_imp, ← le_antisymm_iff]
    rw [div_eq_div_iff]
    · simp only [ValueGroup₀.restrict₀_apply, dite_mul, zero_mul]
      split_ifs with h1 h2 h3 <;>
      simp_all [← WithZero.coe_mul, ← Units.val_inj] <;> simpa
    all_goals simp [ValueGroup₀.restrict₀]
  map_zero' := by simp [lift_zero, ValueGroup₀.restrict₀]
  map_one' := by simp [ValueGroup₀.restrict₀]
  map_mul' _ _ := by
    apply lift_mul
    simp only [map_mul, ValueGroup₀.restrict₀_apply, mul_dite, mul_zero, dite_mul, zero_mul,
      Submonoid.coe_mul, Subtype.forall, posSubmonoid_def]
    intro x y z hz w hw
    split_ifs
    all_goals simp_all
    simp [field, ← WithZero.coe_mul, ← Units.val_inj]

/-- The element `.mk x s` in `ValueGroupWithZero R` is sent to `v x / v s` in the
image group of `v`. -/
@[simp]
/-
**ValuativeRel.ValueGroupWithZero.embed_mk** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeR
el.ValueGroupWithZero`。
形式化陈述：embed_mk [v.Compatible] (x : R) (s : posSubmonoid R) : embed v (.mk x s) =
 (restrict₀ (.ofClass v) x / (restrict₀ (.ofClass v) s))
参数：x : R；s : posSubmonoid R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀

--- 原说明 ---
The element `.mk x s` in `ValueGroupWithZero R` is sent to `v x / v s` in the
image group of `v`.
-/
lemma embed_mk [v.Compatible] (x : R) (s : posSubmonoid R) :
    embed v (.mk x s) = (restrict₀ (.ofClass v) x / (restrict₀ (.ofClass v) s)) :=
  rfl

/--
The triangle in the following diagram is commutative:
```
      restrict₀ v                embedding
    R –––––––––––> ValueGroup₀ v –––––––––> Γ
    │                ∧
    │               /
    │              / embed v
    ∨             /
ValueGroupWithZero R
```
where the first row is the map `v` factored through its image group (with zero) in `Γ`.
-/
@[simp]
/-
**ValuativeRel.ValueGroupWithZero.embed_valuation_eq_restrict** 是 Mathlib 中的一个引理
，位于命名空间 `ValuativeRel.ValueGroupWithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The triangle in the following diagram is commutative:
```
      restrict₀ v                embedding
    R –––––––––––> ValueGroup₀ v –––––––––> Γ
    │                ∧
    │               /
    │              / embed v
    ∨             /
ValueGroupWithZero R
```
where the first row is the map `v` factored through its image group (with zero) 
in `Γ`.
-/
lemma embed_valuation_eq_restrict₀ [v.Compatible] (x : R) :
    embed v (valuation R x) = ValueGroup₀.restrict₀ (.ofClass v) x := by
  convert! embed_mk v x 1
  simp

/--
When `v` is `valuation R`, in the following commutative diagram where the first row is the map `v`
factored through its image group (with zero),
```
                                 embedding
    R –––––––––––> ValueGroup₀ v –––––-–––> ValueGroupWithZero R
    │                ∧
    │               /
    │              / embed v
    ∨             /
ValueGroupWithZero R
```
the map from `ValueGroupWithZero R` to itself is identity.
-/
@[simp]
/-
**ValuativeRel.ValueGroupWithZero.embedding_embed_valuation_eq** 是 Mathlib 中的一个引
理，位于命名空间 `ValuativeRel.ValueGroupWithZero`。
形式化陈述：embedding_embed_valuation_eq (γ : ValueGroupWithZero R) : embedding (embed
 (valuation R) γ) = γ
参数：γ : ValueGroupWithZero R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.ValueGroupWithZero.ind`：∀ {R : Type u_1} [inst : Semiring R
] [inst_1 : ValuativeRel R] {motive : ValuativeRel.ValueGroupWithZero R → Prop},
   (∀ (x : R) (y : ↥(Valu…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `ValuativeRel.instCompatibleValueGroupWithZeroValuation`：∀ {R : Type u_2}
 [inst : Ring R] [inst_1 : ValuativeRel R], (ValuativeRel.valuation R).Compatibl
e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuativeRel.ValueGroupWithZero.mk_eq_div`：∀ {R : Type u_2} [inst : Ring
 R] [inst_1 : ValuativeRel R] (r : R) (s : ↥(ValuativeRel.posSubmonoid R)),   Va
luativeRel.ValueGroupWithZero.m…
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用引理 `ValuativeRel.ValueGroupWithZero.embed_valuation_eq_restrict₀`：embed_valu
ation_eq_restrict₀ [v.Compatible] (x : R) : embed v (valuation R x) = ValueGroup
₀.restrict₀ (.ofClass v) x
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀`：embedding_restrict₀ (
a : A) : ValueGroup₀.embedding (restrict₀ f a) = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
When `v` is `valuation R`, in the following commutative diagram where the first 
row is the map `v`
factored through its image group (with zero),
```
                                 embedding
    R –––––––––––> ValueGroup₀ v –––––-–––> ValueGroupWithZero R
    │                ∧
    │               /
    │              / embed v
    ∨             /
ValueGroupWithZero R
```
the map from `ValueGroupWithZero R` to itself is identity.
-/
lemma embedding_embed_valuation_eq (γ : ValueGroupWithZero R) :
    embedding (embed (valuation R) γ) = γ := by
  induction γ using ValueGroupWithZero.ind
  simp [mk_eq_div]

/-- The map `embed v` is strictly monotone. -/
/-
**ValuativeRel.ValueGroupWithZero.embed_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Va
luativeRel.ValueGroupWithZero`。
形式化陈述：embed_strictMono [v.Compatible] : StrictMono (embed v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `ValuativeRel.exists_valuation_div_valuation_eq`：exists_valuation_div_val
uation_eq (γ : ValueGroupWithZero R) : exists (a : R) (b : posSubmonoid R), valu
ation _ a / valuation _ (b : R) = γ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono`：embedding_strictMono
 : StrictMono (embedding (f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用引理 `div_lt_div_iff₀`：div_lt_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b < c /
 d ↔ a * d < c * b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Units.mk0.congr_simp`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] (a a_1
 : G₀) (e_a : a = a_1) (ha : a ≠ 0), Units.mk0 a ha = Units.mk0 a_1 ⋯
· 使用定理 `Units.mk0_one`：mk0_one (h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidWithZeroHom.ValueGroup₀.restrict₀_apply`：∀ {A : Type u_1} {B : Typ
e u_2} [inst : MonoidWithZero A] [inst_1 : GroupWithZero B] (f : A →*₀ B) (a : A
),   (MonoidWithZeroHom.ValueGroup₀…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `ValuativeRel.ValueGroupWithZero.lift.congr_simp`：∀ {R : Type u_1} [inst 
: Semiring R] [inst_1 : ValuativeRel R] {α : Sort u_2}   (f f_1 : R → ↥(Valuativ
eRel.posSubmonoid R) → α) (e_f : f = …
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The map `embed v` is strictly monotone.
-/
lemma embed_strictMono [v.Compatible] : StrictMono (embed v) := by
  intro a b h
  obtain ⟨a, r, rfl⟩ := exists_valuation_div_valuation_eq a
  obtain ⟨b, s, rfl⟩ := exists_valuation_div_valuation_eq b
  rw [← embedding_strictMono.lt_iff_lt]
  simp only [map_div₀]
  rw [div_lt_div_iff₀] at h ⊢
  any_goals simp only [zero_lt_iff, ne_eq, Valuation.apply_posSubmonoid_ne_zero, not_false_eq_true]
  · rw [← map_mul, ← map_mul, (isEquiv (valuation R) v).lt_iff_lt] at h
    simp only [embed, coe_mk, ZeroHom.coe_mk, lift_valuation,
      OneMemClass.coe_one, map_one, div_one]
    rw [embedding_restrict₀ a, embedding_restrict₀ b, embedding_restrict₀ r.1,
      embedding_restrict₀ s.1]
    simpa using h
  · simp [restrict₀_apply, embed]
  · simp [restrict₀_apply, embed]

/--
When we have `h : w.IsEquiv v`, the image group (with zero) of `v` is
isomorphic to that of `w` via `h.orderMonoidIso`. Then the following diagram is commutative:
```
              ValueGroup₀ w
                ∧      |
       embed w /       |
              /        |
ValueGroupWithZero R   | h.orderMonoidIso
              \        |
       embed v \       |
                ∨      ∨
              ValueGroup₀ v
```
-/
@[simp]
/-
**ValuativeRel.ValueGroupWithZero.orderMonoidIso_embed** 是 Mathlib 中的一个定理，位于命名空间
 `ValuativeRel.ValueGroupWithZero`。
形式化陈述：orderMonoidIso_embed [v.Compatible] {Γ' : Type*} [LinearOrderedCommGroupWi
thZero Γ'] (w : Valuation R Γ') [w.Compatible] (x : ValueGroupWithZero R) (h : w
.IsEquiv v) : h.orderMonoidIso (embed w x) = embed v x
参数：w : Valuation R Γ'；x : ValueGroupWithZero R；h : w.IsEquiv v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `ValuativeRel.ValueGroupWithZero.ind`：∀ {R : Type u_1} [inst : Semiring R
] [inst_1 : ValuativeRel R] {motive : ValuativeRel.ValueGroupWithZero R → Prop},
   (∀ (x : R) (y : ↥(Valu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Valuation.IsEquiv.orderMonoidIso_spec₀`：orderMonoidIso_spec₀ (h : v.IsEq
uiv w) (a : R) : h.orderMonoidIso (restrict₀ (.ofClass v) a) = restrict₀ (.ofCla
ss w) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
When we have `h : w.IsEquiv v`, the image group (with zero) of `v` is
isomorphic to that of `w` via `h.orderMonoidIso`. Then the following diagram is 
commutative:
```
              ValueGroup₀ w
                ∧      |
       embed w /       |
              /        |
ValueGroupWithZero R   | h.orderMonoidIso
              \        |
       embed v \       |
                ∨      ∨
              ValueGroup₀ v
```
-/
theorem orderMonoidIso_embed [v.Compatible] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
    (w : Valuation R Γ') [w.Compatible] (x : ValueGroupWithZero R) (h : w.IsEquiv v) :
    h.orderMonoidIso
    (embed w x) = embed v x := by
  simp only [embed, coe_mk, ZeroHom.coe_mk]
  induction x using ValueGroupWithZero.ind with
  | mk r s => simp [Valuation.IsEquiv.orderMonoidIso_spec₀]

/-- If a valuation `v` is compatible with the valuative relation, then `ValueGroupWithZero R`
is isomorphic to the image group (with zero) of `v` as an ordered group with zero. -/
noncomputable
/-
**ValuativeRel.ValueGroupWithZero.orderMonoidIso** 是 Mathlib 中的一个定义，位于命名空间 `Valu
ativeRel.ValueGroupWithZero`。
形式化陈述：orderMonoidIso [v.Compatible] : ValueGroupWithZero R ≃*o ValueGroup₀ (.ofC
lass v) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def orderMonoidIso [v.Compatible] : ValueGroupWithZero R ≃*o ValueGroup₀ (.ofClass v) where
  __ := embed v
  invFun x := embedding ((isEquiv v (valuation R)).orderMonoidIso x)
  left_inv x := by simp
  right_inv := Function.rightInverse_of_injective_of_leftInverse
      (by rw [← Function.comp_def, EquivLike.injective_comp]
          exact embedding_strictMono.injective) (fun x ↦ by simp)
  map_le_map_iff' := (embed_strictMono v).le_iff_le

/-- This is the same as `ValuativeRel.ValueGroupWithZero.embed_mk`, where `embed` is upgraded to
`orderMonoidIso`. -/
@[simp]
/-
**ValuativeRel.ValueGroupWithZero.orderMonoidIso_mk** 是 Mathlib 中的一个引理，位于命名空间 `V
aluativeRel.ValueGroupWithZero`。
形式化陈述：orderMonoidIso_mk [v.Compatible] (x : R) (s : posSubmonoid R) : orderMonoi
dIso v (.mk x s) = restrict₀ (.ofClass v) x / (restrict₀ (.ofClass v) s)
参数：x : R；s : posSubmonoid R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀

--- 原说明 ---
This is the same as `ValuativeRel.ValueGroupWithZero.embed_mk`, where `embed` is
 upgraded to
`orderMonoidIso`.
-/
lemma orderMonoidIso_mk [v.Compatible] (x : R) (s : posSubmonoid R) :
    orderMonoidIso v (.mk x s) = restrict₀ (.ofClass v) x / (restrict₀ (.ofClass v) s) :=
  rfl

/-- This is the same as `ValuativeRel.ValueGroupWithZero.embed_valuation_eq_restrict₀`,
where `embed` is upgraded to `orderMonoidIso`. -/
@[simp]
/-
**ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict** 是 Mathl
ib 中的一个引理，位于命名空间 `ValuativeRel.ValueGroupWithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the same as `ValuativeRel.ValueGroupWithZero.embed_valuation_eq_restrict
₀`,
where `embed` is upgraded to `orderMonoidIso`.
-/
lemma orderMonoidIso_valuation_eq_restrict₀ [v.Compatible] (x : R) :
    orderMonoidIso v (valuation R x) = restrict₀ (.ofClass v) x :=
  embed_valuation_eq_restrict₀ v x

/-- This is the same as `ValuativeRel.ValueGroupWithZero.embedding_embed_valuation_eq`, where
`embed` is upgraded to `orderMonoidIso`. -/
@[simp]
/-
**ValuativeRel.ValueGroupWithZero.embedding_orderMonoidIso_valuation_eq** 是 Math
lib 中的一个引理，位于命名空间 `ValuativeRel.ValueGroupWithZero`。
形式化陈述：embedding_orderMonoidIso_valuation_eq (γ : ValueGroupWithZero R) : embeddi
ng (orderMonoidIso (valuation R) γ) = γ
参数：γ : ValueGroupWithZero R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ValuativeRel.ValueGroupWithZero.embedding_embed_valuation_eq`：embedding_
embed_valuation_eq (γ : ValueGroupWithZero R) : embedding (embed (valuation R) γ
) = γ

--- 原说明 ---
This is the same as `ValuativeRel.ValueGroupWithZero.embedding_embed_valuation_e
q`, where
`embed` is upgraded to `orderMonoidIso`.
-/
lemma embedding_orderMonoidIso_valuation_eq (γ : ValueGroupWithZero R) :
    embedding (orderMonoidIso (valuation R) γ) = γ :=
  embedding_embed_valuation_eq γ

/-- The map `orderMonoidIso v` is strictly monotone. -/
/-
**ValuativeRel.ValueGroupWithZero.orderMonoidIso_strictMono** 是 Mathlib 中的一个引理，位
于命名空间 `ValuativeRel.ValueGroupWithZero`。
形式化陈述：orderMonoidIso_strictMono [v.Compatible] : StrictMono (orderMonoidIso v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ValuativeRel.ValueGroupWithZero.embed_strictMono`：embed_strictMono [v.Co
mpatible] : StrictMono (embed v)

--- 原说明 ---
The map `orderMonoidIso v` is strictly monotone.
-/
lemma orderMonoidIso_strictMono [v.Compatible] : StrictMono (orderMonoidIso v) :=
  embed_strictMono v

/-- The map `embedding ∘ orderMonoidIso (valuation R))` is identity. -/
/-
**ValuativeRel.ValueGroupWithZero.leftInverse_embedding_orderMonoidIso** 是 Mathl
ib 中的一个引理，位于命名空间 `ValuativeRel.ValueGroupWithZero`。
形式化陈述：leftInverse_embedding_orderMonoidIso : Function.LeftInverse embedding (ord
erMonoidIso (valuation R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ValuativeRel.ValueGroupWithZero.embedding_orderMonoidIso_valuation_eq`：e
mbedding_orderMonoidIso_valuation_eq (γ : ValueGroupWithZero R) : embedding (ord
erMonoidIso (valuation R) γ) = γ

--- 原说明 ---
The map `embedding ∘ orderMonoidIso (valuation R))` is identity.
-/
lemma leftInverse_embedding_orderMonoidIso : Function.LeftInverse embedding
    (orderMonoidIso (valuation R)) :=
  embedding_orderMonoidIso_valuation_eq

/-- The isomorphism between `ValueGroupWithZero R` and `ValueGroup₀ (valuation R)`. -/
@[deprecated "use ValueGroupWithZero.orderMonoidIso instead" (since := "2026-03-17")]
/-
**ValuativeRel.ValueGroupWithZero.valueGroupWithZero_equiv_valueGroup** 是 Mathli
b 中的一个定义，位于命名空间 `ValuativeRel.ValueGroupWithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `ValueGroupWithZero R` and `ValueGroup₀ (valuation R)`.
-/
def valueGroupWithZero_equiv_valueGroup₀ := orderMonoidIso (valuation R)

end ValueGroupWithZero

open ValueGroupWithZero

@[simp]
/-
**ValuativeRel.valuation_lt_symm_orderMonoidIso** 是 Mathlib 中的一个引理，位于命名空间 `Valua
tiveRel`。
形式化陈述：valuation_lt_symm_orderMonoidIso [v.Compatible] (γ : ValueGroup₀ (.ofClass
 v)) (x : R) : valuation R x < (orderMonoidIso v).symm γ ↔ v.restrict x < γ
参数：γ : ValueGroup₀ (.ofClass v)；x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `map_lt_map_iff`：map_lt_map_iff (f : F) {a b : α} : f a < f b ↔ a < b
· 使用定理 `OrderMonoidIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   OrderIs
oClass (α ≃*o β) α β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀`：o
rderMonoidIso_valuation_eq_restrict₀ [v.Compatible] (x : R) : orderMonoidIso v (
valuation R x) = restrict₀ (.ofClass v) x
· 使用定理 `OrderMonoidIso.apply_symm_apply`：apply_symm_apply (e : α ≃*o β) (y : β) 
: e (e.symm y) = y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma valuation_lt_symm_orderMonoidIso [v.Compatible] (γ : ValueGroup₀ (.ofClass v)) (x : R) :
    valuation R x < (orderMonoidIso v).symm γ ↔ v.restrict x < γ :=
  calc
    _ ↔ orderMonoidIso v _ < orderMonoidIso v _ := (map_lt_map_iff (orderMonoidIso v)).symm
    _ ↔ _ := by simp [v.restrict_def x]

@[simp]
/-
**ValuativeRel.restrict_lt_orderMonoidIso** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRe
l`。
形式化陈述：restrict_lt_orderMonoidIso [v.Compatible] (γ : ValueGroupWithZero R) (x : 
R) : v.restrict x < (orderMonoidIso v) γ ↔ (valuation R) x < γ
参数：γ : ValueGroupWithZero R；x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderMonoidIso.symm_apply_apply`：symm_apply_apply (e : α ≃*o β) (x : α) 
: e.symm (e x) = x
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `ValuativeRel.valuation_lt_symm_orderMonoidIso`：valuation_lt_symm_orderMo
noidIso [v.Compatible] (γ : ValueGroup₀ (.ofClass v)) (x : R) : valuation R x < 
(orderMonoidIso v).symm γ ↔ v.restr…
-/
lemma restrict_lt_orderMonoidIso [v.Compatible] (γ : ValueGroupWithZero R) (x : R) :
    v.restrict x < (orderMonoidIso v) γ ↔ (valuation R) x < γ := by
  simpa using (valuation_lt_symm_orderMonoidIso v (orderMonoidIso v γ) x).symm

/-- For any `x ∈ posSubmonoid R`, the trivial valuation `1 : Valuation R Γ` sends `x` to `1`.
In fact, this is true for any `x ≠ 0`. This lemma is a special case useful for shorthand of
`x ∈ posSubmonoid R → x ≠ 0`. -/
/-
**ValuativeRel.one_apply_posSubmonoid** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeRel`。
形式化陈述：one_apply_posSubmonoid [Nontrivial R] [NoZeroDivisors R] [DecidablePred fu
n x : R => x = 0] (x : posSubmonoid R) : (1 : Valuation R Γ) x = 1
参数：x : posSubmonoid R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valuation.one_apply_of_ne_zero`：one_apply_of_ne_zero {x : R} (hx : x != 
0) : (1 : Valuation R Γ₀) x = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
For any `x ∈ posSubmonoid R`, the trivial valuation `1 : Valuation R Γ` sends `x
` to `1`.
In fact, this is true for any `x ≠ 0`. This lemma is a special case useful for s
horthand of
`x ∈ posSubmonoid R → x ≠ 0`.
-/
lemma one_apply_posSubmonoid [Nontrivial R] [NoZeroDivisors R] [DecidablePred fun x : R ↦ x = 0]
    (x : posSubmonoid R) : (1 : Valuation R Γ) x = 1 :=
  Valuation.one_apply_of_ne_zero (by simp)

end ValuativeRel

/-- If `B` is an `A` algebra and both `A` and `B` have valuative relations,
we say that `B|A` is a valuative extension if the valuative relation on `A` is
induced by the one on `B`. -/
/-
**ValuativeExtension** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_1) →   (B : Type u_2) →     [inst : CommSemiring A] → [inst_1 
: Semiring B] → [ValuativeRel A] → [ValuativeRel B] → [Algebra A B] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `B` is an `A` algebra and both `A` and `B` have valuative relations,
we say that `B|A` is a valuative extension if the valuative relation on `A` is
induced by the one on `B`.
-/
class ValuativeExtension (A B : Type*) [CommSemiring A] [Semiring B] [ValuativeRel A]
    [ValuativeRel B] [Algebra A B] where
  vle_iff_vle (a b : A) : algebraMap A B a ≤ᵥ algebraMap A B b ↔ a ≤ᵥ b

namespace ValuativeExtension

open ValuativeRel ValueGroupWithZero MonoidWithZeroHom ValueGroup₀

variable {A B : Type*}

section Semiring

variable [CommSemiring A] [Semiring B] [ValuativeRel A] [ValuativeRel B]
  [Algebra A B] [ValuativeExtension A B]

/-
**ValuativeExtension.vlt_iff_vlt** 是 Mathlib 中的一个引理，位于命名空间 `ValuativeExtension`。
形式化陈述：vlt_iff_vlt {a b : A} : algebraMap A B a <ᵥ algebraMap A B b ↔ a <ᵥ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuativeRel.not_vle`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Val
uativeRel R] {x y : R}, ¬x ≤ᵥ y ↔ y <ᵥ x
· 使用定理 `ValuativeExtension.vle_iff_vle`：∀ {A : Type u_1} {B : Type u_2} {inst : 
CommSemiring A} {inst_1 : Semiring B} {inst_2 : ValuativeRel A}   {inst_3 : Valu
ativeRel B} {inst_4 …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma vlt_iff_vlt {a b : A} : algebraMap A B a <ᵥ algebraMap A B b ↔ a <ᵥ b := by
  rw [← not_vle, vle_iff_vle, not_vle]

variable (A B) in
/-- The morphism of `posSubmonoid`s associated to an algebra map.
  This is used in constructing `ValuativeExtension.mapValueGroupWithZero`. -/
@[simps]
/-
**ValuativeExtension.mapPosSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeExtensi
on`。
形式化陈述：mapPosSubmonoid : posSubmonoid A ->* posSubmonoid B where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism of `posSubmonoid`s associated to an algebra map.
  This is used in constructing `ValuativeExtension.mapValueGroupWithZero`.
-/
def mapPosSubmonoid : posSubmonoid A →* posSubmonoid B where
  toFun := fun ⟨a,ha⟩ => ⟨algebraMap _ _ a,
    by simpa only [posSubmonoid_def, ← (algebraMap A B).map_zero, vlt_iff_vlt] using ha⟩
  map_one' := by simp
  map_mul' := by simp

end Semiring

section Ring

variable [CommRing A] [Ring B] [ValuativeRel A] [ValuativeRel B]
  [Algebra A B] [ValuativeExtension A B]

variable (A) in
/-
**ValuativeExtension.compatible_comap** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeExtens
ion`。
形式化陈述：compatible_comap {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ] (w : Valu
ation B Γ) [w.Compatible] : (w.comap (algebraMap A B)).Compatible
参数：w : Valuation B Γ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuativeExtension.vle_iff_vle`：∀ {A : Type u_1} {B : Type u_2} {inst : 
CommSemiring A} {inst_1 : Semiring B} {inst_2 : ValuativeRel A}   {inst_3 : Valu
ativeRel B} {inst_4 …
· 使用定理 `Valuation.Compatible.vle_iff_le`：∀ {R : Type u_1} {Γ : Type u_2} {inst :
 Ring R} {inst_1 : LinearOrderedCommMonoidWithZero Γ} {v : Valuation R Γ}   {ins
t_2 : ValuativeRel R}…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance compatible_comap {Γ : Type*}
    [LinearOrderedCommMonoidWithZero Γ] (w : Valuation B Γ) [w.Compatible] :
    (w.comap (algebraMap A B)).Compatible := by
  constructor
  simp [← vle_iff_vle (A := A) (B := B), Valuation.Compatible.vle_iff_le (v := w)]

variable (A B) in
/-- The map on value groups-with-zero associated to the structure morphism of an algebra. -/
/-
**ValuativeExtension.mapValueGroupWithZero** 是 Mathlib 中的一个定义，位于命名空间 `ValuativeE
xtension`。
形式化陈述：mapValueGroupWithZero : ValueGroupWithZero A ->*₀ ValueGroupWithZero B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map on value groups-with-zero associated to the structure morphism of an alg
ebra.
-/
def mapValueGroupWithZero : ValueGroupWithZero A →*₀ ValueGroupWithZero B :=
  have := compatible_comap A (valuation B)
  embedding.comp (orderMonoidIso ((valuation B).comap (algebraMap A B))).toMonoidWithZeroHom

@[simp]
/-
**ValuativeExtension.mapValueGroupWithZero_mk** 是 Mathlib 中的一个引理，位于命名空间 `Valuati
veExtension`。
形式化陈述：mapValueGroupWithZero_mk (r : A) (s : posSubmonoid A) : mapValueGroupWithZ
ero A B (.mk r s) = .mk (algebraMap A B r) (mapPosSubmonoid A B s)
参数：r : A；s : posSubmonoid A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀`：embedding_restrict₀ (
a : A) : ValueGroup₀.embedding (restrict₀ f a) = f a
· 使用定理 `ValuativeRel.ValueGroupWithZero.mk_eq_div`：∀ {R : Type u_2} [inst : Ring
 R] [inst_1 : ValuativeRel R] (r : R) (s : ↥(ValuativeRel.posSubmonoid R)),   Va
luativeRel.ValueGroupWithZero.m…
· 使用定理 `ValuativeExtension.mapPosSubmonoid_apply_coe`：∀ (A : Type u_1) (B : Type
 u_2) [inst : CommSemiring A] [inst_1 : Semiring B] [inst_2 : ValuativeRel A]   
[inst_3 : ValuativeRel B] [inst_4 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapValueGroupWithZero_mk (r : A) (s : posSubmonoid A) :
    mapValueGroupWithZero A B (.mk r s) = .mk (algebraMap A B r) (mapPosSubmonoid A B s) := by
  simp [mapValueGroupWithZero, mk_eq_div (R := B)]

@[simp]
/-
**ValuativeExtension.mapValueGroupWithZero_valuation** 是 Mathlib 中的一个引理，位于命名空间 `
ValuativeExtension`。
形式化陈述：mapValueGroupWithZero_valuation (a : A) : mapValueGroupWithZero A B (valua
tion _ a) = valuation _ (algebraMap _ _ a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ValuativeExtension.mapValueGroupWithZero_mk`：mapValueGroupWithZero_mk (r
 : A) (s : posSubmonoid A) : mapValueGroupWithZero A B (.mk r s) = .mk (algebraM
ap A B r) (mapPosSubmonoid A B s)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapValueGroupWithZero_valuation (a : A) :
    mapValueGroupWithZero A B (valuation _ a) = valuation _ (algebraMap _ _ a) := by
  simp [valuation]
/-
**ValuativeExtension.mapValueGroupWithZero_strictMono** 是 Mathlib 中的一个引理，位于命名空间 
`ValuativeExtension`。
形式化陈述：mapValueGroupWithZero_strictMono : StrictMono (mapValueGroupWithZero A B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono`：embedding_strictMono
 : StrictMono (embedding (f
· 使用引理 `ValuativeRel.ValueGroupWithZero.embed_strictMono`：embed_strictMono [v.Co
mpatible] : StrictMono (embed v)
· 使用定理 `ValuativeRel.instCompatibleValueGroupWithZeroValuation`：∀ {R : Type u_2}
 [inst : Ring R] [inst_1 : ValuativeRel R], (ValuativeRel.valuation R).Compatibl
e
-/
lemma mapValueGroupWithZero_strictMono : StrictMono (mapValueGroupWithZero A B) :=
  embedding_strictMono.comp (embed_strictMono _)

variable (B) in
/-
**ValuativeExtension._root_.ValuativeRel.IsRankLeOne.of_valuativeExtension** 是 M
athlib 中的一个引理，位于命名空间 `ValuativeExtension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ValuativeRel.IsRankLeOne.of_valuativeExtension [IsRankLeOne B] : IsRankLeOne A := by
  obtain ⟨⟨f, hf⟩⟩ := IsRankLeOne.nonempty (R := B)
  exact ⟨⟨f.comp (mapValueGroupWithZero _ _), hf.comp mapValueGroupWithZero_strictMono⟩⟩

end Ring

end ValuativeExtension

namespace ValuativeRel

variable {R : Type*} [Semiring R] [ValuativeRel R]

/-- Any rank-at-most-one valuation has a mul-archimedean value group.
The converse (for any compatible valuation) is `ValuativeRel.isRankLeOne_iff_mulArchimedean`
which is in a later file since it requires a larger theory of reals. -/
/-
**ValuativeRel.** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any rank-at-most-one valuation has a mul-archimedean value group.
The converse (for any compatible valuation) is `ValuativeRel.isRankLeOne_iff_mul
Archimedean`
which is in a later file since it requires a larger theory of reals.
-/
instance [IsRankLeOne R] : MulArchimedean (ValueGroupWithZero R) := by
  obtain ⟨⟨f, hf⟩⟩ := IsRankLeOne.nonempty (R := R)
  exact .comap f.toMonoidHom hf

end ValuativeRel

