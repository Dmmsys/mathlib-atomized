/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yaël Dillies
-/
module

public import Mathlib.Data.Nat.Notation
public import Batteries.Classes.RatCast

/-!
# Basic definitions around the rational numbers

This file declares `ℚ` notation for the rationals and defines the nonnegative rationals `ℚ≥0`.

This file is eligible to upstreaming to Batteries.
-/

@[expose] public section

@[inherit_doc] notation "ℚ" => Rat

/-- Nonnegative rational numbers. -/
/-
**NNRat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NNRat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Nonnegative rational numbers.
-/
def NNRat := {q : ℚ // 0 ≤ q}

@[inherit_doc] notation "ℚ≥0" => NNRat

/-!
### Cast from `NNRat`

This section sets up the typeclasses necessary to declare the canonical embedding `ℚ≥0` to any
semifield.
-/

/-- Typeclass for the canonical homomorphism `ℚ≥0 → K`.

This should be considered as a notation typeclass. The sole purpose of this typeclass is to be
extended by `DivisionSemiring`. -/
/-
**NNRatCast** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for the canonical homomorphism `ℚ≥0 → K`.

This should be considered as a notation typeclass. The sole purpose of this type
class is to be
extended by `DivisionSemiring`.
-/
class NNRatCast (K : Type*) where
  /-- The canonical homomorphism `ℚ≥0 → K`.

  Do not use directly. Use the coercion instead. -/
  protected nnratCast : ℚ≥0 → K
/-
**NNRat.instNNRatCast** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NNRat.instNNRatCast : NNRatCast Rat>=0 where nnratCast q
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance NNRat.instNNRatCast : NNRatCast ℚ≥0 where nnratCast q := q

variable {K : Type*} [NNRatCast K]

/-- Canonical homomorphism from `ℚ≥0` to a division semiring `K`.

This is just the bare function in order to aid in creating instances of `DivisionSemiring`. -/
/-
**NNRat.cast** 是 Mathlib 中的一个定义，位于命名空间 `NNRat`。
形式化陈述：{K : Type u_1} → [NNRatCast K] → ℚ≥0 → K
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Canonical homomorphism from `ℚ≥0` to a division semiring `K`.

This is just the bare function in order to aid in creating instances of `Divisio
nSemiring`.
-/
@[coe, reducible, match_pattern] protected def NNRat.cast : ℚ≥0 → K := NNRatCast.nnratCast

-- See note [coercion into rings]
/-
**NNRatCast.toCoeTail** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NNRatCast.toCoeTail : CoeTail Rat>=0 K where coe
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance NNRatCast.toCoeTail : CoeTail ℚ≥0 K where coe := NNRat.cast

-- See note [coercion into rings]
/-
**NNRatCast.toCoeHTCT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NNRatCast.toCoeHTCT : CoeHTCT Rat>=0 K where coe
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance NNRatCast.toCoeHTCT : CoeHTCT ℚ≥0 K where coe := NNRat.cast
/-
**Rat.instNNRatCast** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Rat.instNNRatCast : NNRatCast Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Rat.instNNRatCast : NNRatCast ℚ := ⟨Subtype.val⟩

/-! ### Numerator and denominator of a nonnegative rational -/

namespace NNRat

/-- The numerator of a nonnegative rational. -/
/-
**NNRat.num** 是 Mathlib 中的一个定义，位于命名空间 `NNRat`。
形式化陈述：num (q : Rat>=0) : Nat
参数：q : Rat>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The numerator of a nonnegative rational.
-/
def num (q : ℚ≥0) : ℕ := (q : ℚ).num.natAbs

/-- The denominator of a nonnegative rational. -/
/-
**NNRat.den** 是 Mathlib 中的一个定义，位于命名空间 `NNRat`。
形式化陈述：den (q : Rat>=0) : Nat
参数：q : Rat>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The denominator of a nonnegative rational.
-/
def den (q : ℚ≥0) : ℕ := (q : ℚ).den
/-
**NNRat.num_mk** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ) (hq : 0 ≤ q), NNRat.num ⟨q, hq⟩ = q.num.natAbs
参数：q : ℚ；hq : 0 ≤ q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma num_mk (q : ℚ) (hq : 0 ≤ q) : num ⟨q, hq⟩ = q.num.natAbs := rfl
/-
**NNRat.den_mk** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ) (hq : 0 ≤ q), NNRat.den ⟨q, hq⟩ = q.den
参数：q : ℚ；hq : 0 ≤ q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma den_mk (q : ℚ) (hq : 0 ≤ q) : den ⟨q, hq⟩ = q.den := rfl
/-
**NNRat.cast_id** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (n : ℚ≥0), ↑n = n
参数：n : ℚ≥0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma cast_id (n : ℚ≥0) : NNRat.cast n = n := rfl
/-
**NNRat.cast_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：NNRat.cast = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma cast_eq_id : NNRat.cast = id := rfl

end NNRat

namespace Rat

/-
**Rat.cast_id** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (n : ℚ), ↑n = n
参数：n : ℚ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma cast_id (n : ℚ) : Rat.cast n = n := rfl
/-
**Rat.cast_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：Rat.cast = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma cast_eq_id : Rat.cast = id := rfl

end Rat

