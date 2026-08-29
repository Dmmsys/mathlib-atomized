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

@[inherit_doc] notation "Rat" => Rat

/--
Definition of `NNRat` / `NNRat` 的定义

English:
definition NNRat
  body: {q : Rat // 0 <= q}

@[inherit_doc] notation "Rat>=0" => NNRat

中文:
定义 NNRat
  定义体: {q : Rat // 0 <= q}

@[inherit_doc] notation "Rat>=0" => NNRat
-/
def NNRat := {q : Rat // 0 <= q}

@[inherit_doc] notation "Rat>=0" => NNRat

/-!
### Cast from `NNRat`

This section sets up the typeclasses necessary to declare the canonical embedding `ℚ≥0` to any
semifield.
-/

/--
Definition of `NNRatCast` / `NNRatCast` 的定义

English:
class NNRatCast
  parameters: (K : Type*)
  axioms and operations (1):
    - nnratCast : Rat>=0 -> K

中文:
类 非负有理数嵌入
  参数: (K : 类型)
  公理与运算 (1 个):
    - nnratCast : 有理数>=0 -> K
-/
class NNRatCast (K : Type*) where
  /-- The canonical homomorphism `ℚ≥0 → K`.

  Do not use directly. Use the coercion instead. -/
  protected nnratCast : Rat>=0 -> K

/--
Instance `NNRat.instNNRatCast` / 实例 `NNRat.instNNRatCast`

English:
instance NNRat.instNNRatCast
  signature: : NNRatCast Rat>=0 where nnratCast q
  body: q

中文:
实例 NNRat.instNNRatCast
  签名: : 非负有理数嵌入 有理数>=0 where nnratCast q
  定义体: q
-/
instance NNRat.instNNRatCast : NNRatCast Rat>=0 where nnratCast q := q

variable {K : Type*} [NNRatCast K]

/--
Definition of `NNRat.cast` / `NNRat.cast` 的定义

English:
definition NNRat.cast
  signature: : Rat>=0 -> K
  body: NNRatCast.nnratCast

中文:
定义 NNRat.cast
  签名: : 有理数>=0 -> K
  定义体: NNRatCast.nnratCast
-/
@[coe, reducible, match_pattern] protected def NNRat.cast : Rat>=0 -> K := NNRatCast.nnratCast

-- See note [coercion into rings]
/--
Instance `NNRatCast.toCoeTail` / 实例 `NNRatCast.toCoeTail`

English:
instance NNRatCast.toCoeTail
  signature: : CoeTail Rat>=0 K where coe
  body: NNRat.cast

中文:
实例 非负有理数嵌入.toCoeTail
  签名: : CoeTail 有理数>=0 K where coe
  定义体: NNRat.cast

Depends on / 依赖: NNRat.cast
-/
instance NNRatCast.toCoeTail : CoeTail Rat>=0 K where coe := NNRat.cast

-- See note [coercion into rings]
/--
Instance `NNRatCast.toCoeHTCT` / 实例 `NNRatCast.toCoeHTCT`

English:
instance NNRatCast.toCoeHTCT
  signature: : CoeHTCT Rat>=0 K where coe
  body: NNRat.cast

中文:
实例 非负有理数嵌入.toCoeHTCT
  签名: : CoeHTCT 有理数>=0 K where coe
  定义体: NNRat.cast

Depends on / 依赖: NNRat.cast
-/
instance NNRatCast.toCoeHTCT : CoeHTCT Rat>=0 K where coe := NNRat.cast

/--
Instance `Rat.instNNRatCast` / 实例 `Rat.instNNRatCast`

English:
instance Rat.instNNRatCast
  signature: : NNRatCast Rat
  body: ⟨Subtype.val⟩

中文:
实例 有理数.instNNRatCast
  签名: : 非负有理数嵌入 有理数
  定义体: ⟨Subtype.val⟩

Depends on / 依赖: Subtype, Subtype.val
-/
instance Rat.instNNRatCast : NNRatCast Rat := ⟨Subtype.val⟩

/-! ### Numerator and denominator of a nonnegative rational -/

namespace NNRat

/--
Definition of `num` / `num` 的定义

English:
definition num
  signature: (q : Rat>=0)
  body: (q : Rat).num.natAbs

中文:
定义 num
  签名: (q : 有理数>=0)
  定义体: (q : Rat).num.natAbs

Depends on / 依赖: natAbs, num.natAbs
-/
def num (q : Rat>=0) : Nat := (q : Rat).num.natAbs

/--
Definition of `den` / `den` 的定义

English:
definition den
  signature: (q : Rat>=0)
  body: (q : Rat).den

中文:
定义 den
  签名: (q : 有理数>=0)
  定义体: (q : Rat).den
-/
def den (q : Rat>=0) : Nat := (q : Rat).den

/--
lemma `num_mk` / 引理 `num_mk`

English:
lemma num_mk
  given: (q : Rat) (hq : 0 <= q)
  statement: num ⟨q, hq⟩ = q.num.natAbs
  proof: rfl

中文:
引理 num_mk
  条件: (q : 有理数) (hq : 0 <= q)
  结论: num ⟨q, hq⟩ = q.num.natAbs
  证明: rfl
-/
@[simp] lemma num_mk (q : Rat) (hq : 0 <= q) : num ⟨q, hq⟩ = q.num.natAbs := rfl
/--
lemma `den_mk` / 引理 `den_mk`

English:
lemma den_mk
  given: (q : Rat) (hq : 0 <= q)
  statement: den ⟨q, hq⟩ = q.den
  proof: rfl

中文:
引理 den_mk
  条件: (q : 有理数) (hq : 0 <= q)
  结论: den ⟨q, hq⟩ = q.den
  证明: rfl
-/
@[simp] lemma den_mk (q : Rat) (hq : 0 <= q) : den ⟨q, hq⟩ = q.den := rfl

/--
lemma `cast_id` / 引理 `cast_id`

English:
lemma cast_id
  given: (n : Rat>=0)
  statement: NNRat.cast n = n
  proof: rfl

中文:
引理 cast_id
  条件: (n : 有理数>=0)
  结论: NNRat.cast n = n
  证明: rfl
-/
@[norm_cast] lemma cast_id (n : Rat>=0) : NNRat.cast n = n := rfl
/--
lemma `cast_eq_id` / 引理 `cast_eq_id`

English:
lemma cast_eq_id
  statement: NNRat.cast = id
  proof: rfl

中文:
引理 cast_eq_id
  结论: NNRat.cast = id
  证明: rfl
-/
@[simp] lemma cast_eq_id : NNRat.cast = id := rfl

end NNRat

namespace Rat

/--
lemma `cast_id` / 引理 `cast_id`

English:
lemma cast_id
  given: (n : Rat)
  statement: Rat.cast n = n
  proof: rfl

中文:
引理 cast_id
  条件: (n : 有理数)
  结论: 有理数.cast n = n
  证明: rfl
-/
@[norm_cast] lemma cast_id (n : Rat) : Rat.cast n = n := rfl
/--
lemma `cast_eq_id` / 引理 `cast_eq_id`

English:
lemma cast_eq_id
  statement: Rat.cast = id
  proof: rfl

中文:
引理 cast_eq_id
  结论: 有理数.cast = id
  证明: rfl
-/
@[simp] lemma cast_eq_id : Rat.cast = id := rfl

end Rat
