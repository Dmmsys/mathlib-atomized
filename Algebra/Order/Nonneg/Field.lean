/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Field.Canonical
public import Mathlib.Algebra.Order.Nonneg.Ring
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Semifield structure on the type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

This is used to derive algebraic structures on `ℝ≥0` and `ℚ≥0` automatically.
-/

@[expose] public section

assert_not_exists abs_inv

open Set

variable {α : Type*}

section NNRat
variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

/--
lemma `NNRat.cast_nonneg` / 引理 `NNRat.cast_nonneg`

English:
lemma NNRat.cast_nonneg
  given: (q : Rat>=0)
  statement: 0 <= (q : α)
  proof: by
  rw [cast_def]; exact div_nonneg q.num.cast_nonneg q.den.cast_nonneg

中文:
引理 NNRat.cast_nonneg
  条件: (q : Rat>=0)
  结论: 0 <= (q : α)
  证明: by
  rw [cast_def]; exact div_nonneg q.num.cast_nonneg q.den.cast_nonneg

Depends on / 依赖: cast_def, cast_nonneg, div_nonneg, q.den.cast_nonneg, q.num.cast_nonneg
-/
lemma NNRat.cast_nonneg (q : Rat>=0) : 0 <= (q : α) := by
  rw [cast_def]; exact div_nonneg q.num.cast_nonneg q.den.cast_nonneg

/--
lemma `nnqsmul_nonneg` / 引理 `nnqsmul_nonneg`

English:
lemma nnqsmul_nonneg
  given: (q : Rat>=0) (ha : 0 <= a)
  statement: 0 <= q • a
  proof: by
  rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg ha

中文:
引理 nnqsmul_nonneg
  条件: (q : Rat>=0) (ha : 0 <= a)
  结论: 0 <= q • a
  证明: by
  rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg ha

Depends on / 依赖: NNRat.smul_def, cast_nonneg, mul_nonneg, q.cast_nonneg, smul_def
-/
lemma nnqsmul_nonneg (q : Rat>=0) (ha : 0 <= a) : 0 <= q • a := by
  rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg ha

end NNRat

namespace Nonneg

/-- In an ordered field, the units of the nonnegative elements are the positive elements. -/
@[simps]
/--
Definition of `unitsEquivPos` / `unitsEquivPos` 的定义

English:
definition unitsEquivPos
  signature: (R : Type*) [DivisionSemiring R] [PartialOrder R]
  body: ⟨r, lt_of_le_of_ne r.1.2 (Subtype.val_injective.ne r.ne_zero.symm)⟩
  invFun r := ⟨⟨r.1, r.2.le⟩, ⟨r.1⁻¹, inv_nonneg.mpr r.2.le⟩,
    by ext; simp [r.2.ne'], by ext; simp [r.2.ne']⟩
  left_inv r := by ext; rfl
  right_inv r := by ext; rfl
  map_mul' _ _ := rfl

中文:
定义 unitsEquivPos
  签名: (R : 类型) [DivisionSemiring R] [PartialOrder R]
  定义体: ⟨r, lt_of_le_of_ne r.1.2 (Subtype.val_injective.ne r.ne_zero.symm)⟩
  invFun r := ⟨⟨r.1, r.2.le⟩, ⟨r.1⁻¹, inv_nonneg.mpr r.2.le⟩,
    by ext; simp [r.2.ne'], by ext; simp [r.2.ne']⟩
  left_inv r := by ext; rfl
  right_inv r := by ext; rfl
  map_mul' _ _ := rfl

Depends on / 依赖: Subtype, Subtype.val_injective.ne, lt_of_le_of_ne, ne_zero, r.ne_zero.symm, val_injective
-/
def unitsEquivPos (R : Type*) [DivisionSemiring R] [PartialOrder R]
    [IsStrictOrderedRing R] [PosMulReflectLT R] :
    { r : R // 0 <= r }ˣ ≃* { r : R // 0 < r } where
  toFun r := ⟨r, lt_of_le_of_ne r.1.2 (Subtype.val_injective.ne r.ne_zero.symm)⟩
  invFun r := ⟨⟨r.1, r.2.le⟩, ⟨r.1⁻¹, inv_nonneg.mpr r.2.le⟩,
    by ext; simp [r.2.ne'], by ext; simp [r.2.ne']⟩
  left_inv r := by ext; rfl
  right_inv r := by ext; rfl
  map_mul' _ _ := rfl

section LinearOrderedSemifield

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {x y : α}

/--
Instance `inv` / 实例 `inv`

English:
instance inv
  signature: : Inv { x : α // 0 <= x }
  body: ⟨fun x => ⟨x⁻¹, inv_nonneg.2 x.2⟩⟩

@[simp, norm_cast]

中文:
实例 inv
  签名: : Inv { x : α // 0 <= x }
  定义体: ⟨fun x => ⟨x⁻¹, inv_nonneg.2 x.2⟩⟩

@[simp, norm_cast]

Depends on / 依赖: inv_nonneg
-/
instance inv : Inv { x : α // 0 <= x } :=
  ⟨fun x => ⟨x⁻¹, inv_nonneg.2 x.2⟩⟩

@[simp, norm_cast]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (a : { x : α // 0 <= x })
  statement: ((a⁻¹ : { x : α // 0 <= x }) : α) = (a : α)⁻¹
  proof: rfl

@[simp]

中文:
定理 coe_inv
  条件: (a : { x : α // 0 <= x })
  结论: ((a⁻¹ : { x : α // 0 <= x }) : α) = (a : α)⁻¹
  证明: rfl

@[simp]
-/
protected theorem coe_inv (a : { x : α // 0 <= x }) : ((a⁻¹ : { x : α // 0 <= x }) : α) = (a : α)⁻¹ :=
  rfl

@[simp]
/--
theorem `inv_mk` / 定理 `inv_mk`

English:
theorem inv_mk
  given: (hx : 0 <= x)
  proof: rfl

中文:
定理 inv_mk
  条件: (hx : 0 <= x)
  证明: rfl
-/
theorem inv_mk (hx : 0 <= x) :
    (⟨x, hx⟩ : { x : α // 0 <= x })⁻¹ = ⟨x⁻¹, inv_nonneg.2 hx⟩ :=
  rfl

/--
Instance `div` / 实例 `div`

English:
instance div
  signature: : Div { x : α // 0 <= x }
  body: ⟨fun x y => ⟨x / y, div_nonneg x.2 y.2⟩⟩

@[simp, norm_cast]

中文:
实例 div
  签名: : Div { x : α // 0 <= x }
  定义体: ⟨fun x y => ⟨x / y, div_nonneg x.2 y.2⟩⟩

@[simp, norm_cast]

Depends on / 依赖: div_nonneg
-/
instance div : Div { x : α // 0 <= x } :=
  ⟨fun x y => ⟨x / y, div_nonneg x.2 y.2⟩⟩

@[simp, norm_cast]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: (a b : { x : α // 0 <= x })
  statement: ((a / b : { x : α // 0 <= x }) : α) = a / b
  proof: rfl

@[simp]

中文:
定理 coe_div
  条件: (a b : { x : α // 0 <= x })
  结论: ((a / b : { x : α // 0 <= x }) : α) = a / b
  证明: rfl

@[simp]
-/
protected theorem coe_div (a b : { x : α // 0 <= x }) : ((a / b : { x : α // 0 <= x }) : α) = a / b :=
  rfl

@[simp]
/--
theorem `mk_div_mk` / 定理 `mk_div_mk`

English:
theorem mk_div_mk
  given: (hx : 0 <= x) (hy : 0 <= y)
  proof: rfl

中文:
定理 mk_div_mk
  条件: (hx : 0 <= x) (hy : 0 <= y)
  证明: rfl
-/
theorem mk_div_mk (hx : 0 <= x) (hy : 0 <= y) :
    (⟨x, hx⟩ : { x : α // 0 <= x }) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ :=
  rfl

/--
Instance `zpow` / 实例 `zpow`

English:
instance zpow
  signature: : Pow { x : α // 0 <= x } Int
  body: ⟨fun a n => ⟨(a : α) ^ n, zpow_nonneg a.2 _⟩⟩

@[simp, norm_cast]

中文:
实例 zpow
  签名: : Pow { x : α // 0 <= x } 整数
  定义体: ⟨fun a n => ⟨(a : α) ^ n, zpow_nonneg a.2 _⟩⟩

@[simp, norm_cast]

Depends on / 依赖: zpow_nonneg
-/
instance zpow : Pow { x : α // 0 <= x } Int :=
  ⟨fun a n => ⟨(a : α) ^ n, zpow_nonneg a.2 _⟩⟩

@[simp, norm_cast]
/--
theorem `coe_zpow` / 定理 `coe_zpow`

English:
theorem coe_zpow
  given: (a : { x : α // 0 <= x }) (n : Int)
  proof: rfl

@[simp]

中文:
定理 coe_zpow
  条件: (a : { x : α // 0 <= x }) (n : 整数)
  证明: rfl

@[simp]
-/
protected theorem coe_zpow (a : { x : α // 0 <= x }) (n : Int) :
    ((a ^ n : { x : α // 0 <= x }) : α) = (a : α) ^ n :=
  rfl

@[simp]
/--
theorem `mk_zpow` / 定理 `mk_zpow`

English:
theorem mk_zpow
  given: (hx : 0 <= x) (n : Int)
  proof: rfl

中文:
定理 mk_zpow
  条件: (hx : 0 <= x) (n : 整数)
  证明: rfl
-/
theorem mk_zpow (hx : 0 <= x) (n : Int) :
    (⟨x, hx⟩ : { x : α // 0 <= x }) ^ n = ⟨x ^ n, zpow_nonneg hx n⟩ :=
  rfl

/--
Instance `instNNRatCast` / 实例 `instNNRatCast`

English:
instance instNNRatCast
  signature: : NNRatCast {x : α // 0 <= x}
  body: ⟨fun q => ⟨q, q.cast_nonneg⟩⟩

中文:
实例 instNNRatCast
  签名: : NNRatCast {x : α // 0 <= x}
  定义体: ⟨fun q => ⟨q, q.cast_nonneg⟩⟩

Depends on / 依赖: cast_nonneg, q.cast_nonneg
-/
instance instNNRatCast : NNRatCast {x : α // 0 <= x} := ⟨fun q => ⟨q, q.cast_nonneg⟩⟩
/--
Instance `instNNRatSMul` / 实例 `instNNRatSMul`

English:
instance instNNRatSMul
  signature: : SMul Rat>=0 {x : α // 0 <= x} where
  body: ⟨q • a, by rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg a.2⟩

中文:
实例 instNNRatSMul
  签名: : SMul Rat>=0 {x : α // 0 <= x} where
  定义体: ⟨q • a, by rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg a.2⟩

Depends on / 依赖: NNRat.smul_def, cast_nonneg, mul_nonneg, q.cast_nonneg, smul_def
-/
instance instNNRatSMul : SMul Rat>=0 {x : α // 0 <= x} where
  smul q a := ⟨q • a, by rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg a.2⟩

/--
lemma `coe_nnratCast` / 引理 `coe_nnratCast`

English:
lemma coe_nnratCast
  given: (q : Rat>=0)
  statement: (q : {x : α // 0 <= x}) = (q : α)
  proof: rfl

中文:
引理 coe_nnratCast
  条件: (q : Rat>=0)
  结论: (q : {x : α // 0 <= x}) = (q : α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_nnratCast (q : Rat>=0) : (q : {x : α // 0 <= x}) = (q : α) := rfl
/--
lemma `mk_nnratCast` / 引理 `mk_nnratCast`

English:
lemma mk_nnratCast
  given: (q : Rat>=0)
  statement: (⟨q, q.cast_nonneg⟩ : {x : α // 0 <= x}) = q
  proof: rfl

中文:
引理 mk_nnratCast
  条件: (q : Rat>=0)
  结论: (⟨q, q.cast_nonneg⟩ : {x : α // 0 <= x}) = q
  证明: rfl
-/
@[simp] lemma mk_nnratCast (q : Rat>=0) : (⟨q, q.cast_nonneg⟩ : {x : α // 0 <= x}) = q := rfl

/--
lemma `coe_nnqsmul` / 引理 `coe_nnqsmul`

English:
lemma coe_nnqsmul
  given: (q : Rat>=0) (a : {x : α // 0 <= x})
  proof: rfl

中文:
引理 coe_nnqsmul
  条件: (q : Rat>=0) (a : {x : α // 0 <= x})
  证明: rfl
-/
@[simp, norm_cast] lemma coe_nnqsmul (q : Rat>=0) (a : {x : α // 0 <= x}) :
    ↑(q • a) = (q • a : α) := rfl
/--
lemma `mk_nnqsmul` / 引理 `mk_nnqsmul`

English:
lemma mk_nnqsmul
  given: (q : Rat>=0) (a : α) (ha : 0 <= a)
  proof: rfl

中文:
引理 mk_nnqsmul
  条件: (q : Rat>=0) (a : α) (ha : 0 <= a)
  证明: rfl
-/
@[simp] lemma mk_nnqsmul (q : Rat>=0) (a : α) (ha : 0 <= a) :
    (⟨q • a, by rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg ha⟩ : {x : α // 0 <= x}) =
      q • a := rfl

/--
Instance `semifield` / 实例 `semifield`

English:
instance semifield
  signature: : Semifield { x : α // 0 <= x }
  body: fast_instance%
  Subtype.coe_injective.semifield _ Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul Nonneg.coe_inv Nonneg.coe_div (fun _ _ => rfl) coe_nnqsmul Nonneg.coe_pow
    Nonneg.coe_zpow Nonneg.coe_natCast coe_nnratCast

中文:
实例 semifield
  签名: : Semifield { x : α // 0 <= x }
  定义体: fast_instance%
  Subtype.coe_injective.semifield _ Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul Nonneg.coe_inv Nonneg.coe_div (fun _ _ => rfl) coe_nnqsmul Nonneg.coe_pow
    Nonneg.coe_zpow Nonneg.coe_natCast coe_nnratCast

Depends on / 依赖: fast_instance
-/
instance semifield : Semifield { x : α // 0 <= x } := fast_instance%
  Subtype.coe_injective.semifield _ Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul Nonneg.coe_inv Nonneg.coe_div (fun _ _ => rfl) coe_nnqsmul Nonneg.coe_pow
    Nonneg.coe_zpow Nonneg.coe_natCast coe_nnratCast

end LinearOrderedSemifield

/--
Instance `linearOrderedCommGroupWithZero` / 实例 `linearOrderedCommGroupWithZero`

English:
instance linearOrderedCommGroupWithZero
  signature: [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  body: fast_instance% CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero

中文:
实例 linearOrderedCommGroupWithZero
  签名: [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  定义体: fast_instance% CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero

Depends on / 依赖: CanonicallyOrderedAdd, CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero, fast_instance, toLinearOrderedCommGroupWithZero
-/
instance linearOrderedCommGroupWithZero [Field α] [LinearOrder α] [IsStrictOrderedRing α] :
    LinearOrderedCommGroupWithZero { x : α // 0 <= x } :=
  fast_instance% CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero

end Nonneg
