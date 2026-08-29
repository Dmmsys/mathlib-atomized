/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Cofinality.Basic
public import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Cofinality of an ordinal

This file contains the definition of the cofinality `Ordinal.cof o` of an ordinal. This is the
cofinality of the ordinal `o` when viewed as a linear order.

## Main statements

* `Cardinal.lt_power_cof_ord`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ ℵ₀`.

## Implementation notes

* We do not separately define the cofinality of a cardinal. If `c` is a cardinal number, you can
  write its cofinality as `c.ord.cof`.
-/

public noncomputable section

open Function Cardinal Set Order
open scoped Ordinal

universe u v w

variable {α γ : Type u} {β : Type v}

/--
theorem `Order.cof_int` / 定理 `Order.cof_int`

English:
theorem Order.cof_int
  statement: cof Int = ℵ₀
  proof: by simp

中文:
定理 Order.cof_int
  结论: cof 整数 = ℵ₀
  证明: by simp
-/
theorem Order.cof_int : cof Int = ℵ₀ := by simp

/-! ### Cofinality of ordinals -/

-- TODO: generalize to `OrderType`
namespace Ordinal

/--
Definition of `cof` / `cof` 的定义

English:
definition cof
  signature: (o : Ordinal.{u})
  body: o.liftOnWellOrder (fun α _ _ => Order.cof α) fun _ _ _ _ _ _ h =>
    let ⟨f⟩ := type_eq.1 h
    (OrderIso.ofRelIsoLT f).cof_congr

@[simp]

中文:
定义 cof
  签名: (o : 序数.{u})
  定义体: o.liftOnWellOrder (fun α _ _ => Order.cof α) fun _ _ _ _ _ _ h =>
    let ⟨f⟩ := type_eq.1 h
    (OrderIso.ofRelIsoLT f).cof_congr

@[simp]

Depends on / 依赖: Order.cof, OrderIso, OrderIso.ofRelIsoLT, cof_congr, liftOnWellOrder, o.liftOnWellOrder, ofRelIsoLT, type_eq
-/
def cof (o : Ordinal.{u}) : Cardinal.{u} :=
  o.liftOnWellOrder (fun α _ _ => Order.cof α) fun _ _ _ _ _ _ h =>
    let ⟨f⟩ := type_eq.1 h
    (OrderIso.ofRelIsoLT f).cof_congr

@[simp]
/--
theorem `cof_type` / 定理 `cof_type`

English:
theorem cof_type
  given: (α : Type*) [LinearOrder α] [WellFoundedLT α]
  proof: liftOnWellOrder_type ..

@[deprecated (since := "2026-02-18")] alias cof_type_lt := cof_type

@[simp]

中文:
定理 cof_type
  条件: (α : 类型) [线性序 α] [WellFoundedLT α]
  证明: liftOnWellOrder_type ..

@[deprecated (since := "2026-02-18")] alias cof_type_lt := cof_type

@[simp]

Depends on / 依赖: liftOnWellOrder_type
-/
theorem cof_type (α : Type*) [LinearOrder α] [WellFoundedLT α] :
    (typeLT α).cof = Order.cof α :=
  liftOnWellOrder_type ..

@[deprecated (since := "2026-02-18")] alias cof_type_lt := cof_type

@[simp]
/--
theorem `cof_toType` / 定理 `cof_toType`

English:
theorem cof_toType
  given: (o : Ordinal)
  statement: Order.cof o.ToType = o.cof
  proof: by
  conv_rhs => rw [← type_toType o, cof_type]

@[deprecated (since := "2026-02-18")] alias cof_eq_cof_toType := cof_toType
@[deprecated (since := "2026-02-18")] alias le_cof_type := le_cof_iff
@[deprecated (since := "2026-02-18")] alias cof_type_le := cof_le
@[deprecated (since := "2026-02-18")] a

中文:
定理 cof_toType
  条件: (o : 序数)
  结论: Order.cof o.ToType = o.cof
  证明: by
  conv_rhs => rw [← type_toType o, cof_type]

@[deprecated (since := "2026-02-18")] alias cof_eq_cof_toType := cof_toType
@[deprecated (since := "2026-02-18")] alias le_cof_type := le_cof_iff
@[deprecated (since := "2026-02-18")] alias cof_type_le := cof_le
@[deprecated (since := "2026-02-18")] a

Depends on / 依赖: cof_type, conv_rhs, type_toType
-/
theorem cof_toType (o : Ordinal) : Order.cof o.ToType = o.cof := by
  conv_rhs => rw [← type_toType o, cof_type]

@[deprecated (since := "2026-02-18")] alias cof_eq_cof_toType := cof_toType
@[deprecated (since := "2026-02-18")] alias le_cof_type := le_cof_iff
@[deprecated (since := "2026-02-18")] alias cof_type_le := cof_le
@[deprecated (since := "2026-02-18")] alias lt_cof_type := cof_le
@[deprecated (since := "2026-02-18")] alias cof_eq := Order.cof_eq

@[simp]
/--
theorem `lift_cof` / 定理 `lift_cof`

English:
theorem lift_cof
  given: (o : Ordinal.{u})
  statement: Cardinal.lift.{v} (cof o) = cof (Ordinal.lift.{v} o)
  proof: by
  cases o using inductionOnWellOrder with | type α
  rw [cof_type]; rw [← type_lt_ulift]; rw [cof_type]; rw [← Cardinal.lift_id'.{u]; rw [v} (Order.cof (ULift _))]; rw [← Cardinal.lift_umax]; rw [← ULift.orderIso.lift_cof_congr]

中文:
定理 lift_cof
  条件: (o : 序数.{u})
  结论: 基数.lift.{v} (cof o) = cof (序数.lift.{v} o)
  证明: by
  cases o using inductionOnWellOrder with | type α
  rw [cof_type]; rw [← type_lt_ulift]; rw [cof_type]; rw [← Cardinal.lift_id'.{u]; rw [v} (Order.cof (ULift _))]; rw [← Cardinal.lift_umax]; rw [← ULift.orderIso.lift_cof_congr]

Depends on / 依赖: Cardinal, Cardinal.lift_id, Cardinal.lift_umax, Order.cof, ULift.orderIso.lift_cof_congr, cof_type, inductionOnWellOrder, lift_cof_congr, lift_id, lift_umax, orderIso, type_lt_ulift
-/
theorem lift_cof (o : Ordinal.{u}) : Cardinal.lift.{v} (cof o) = cof (Ordinal.lift.{v} o) := by
  cases o using inductionOnWellOrder with | type α
  rw [cof_type]; rw [← type_lt_ulift]; rw [cof_type]; rw [← Cardinal.lift_id'.{u]; rw [v} (Order.cof (ULift _))]; rw [← Cardinal.lift_umax]; rw [← ULift.orderIso.lift_cof_congr]

/--
theorem `_root_.Order.cof_Iio` / 定理 `_root_.Order.cof_Iio`

English:
theorem _root_.Order.cof_Iio
  given: [LinearOrder α] [WellFoundedLT α] (x : α)
  proof: (cof_type _).symm

@[simp]

中文:
定理 _root_.Order.cof_Iio
  条件: [线性序 α] [WellFoundedLT α] (x : α)
  证明: (cof_type _).symm

@[simp]
-/
theorem _root_.Order.cof_Iio [LinearOrder α] [WellFoundedLT α] (x : α) :
    Order.cof (Iio x) = cof (typein (α := α) (· < ·) x) :=
  (cof_type _).symm

@[simp]
/--
theorem `cof_Iio` / 定理 `cof_Iio`

English:
theorem cof_Iio
  given: (o : Ordinal.{u})
  statement: Order.cof (Iio o) = cof (lift.{u + 1} o)
  proof: by
  rw [Order.cof_Iio]; rw [typein_ordinal]

中文:
定理 cof_Iio
  条件: (o : 序数.{u})
  结论: Order.cof (左无界右开区间 o) = cof (lift.{u + 1} o)
  证明: by
  rw [Order.cof_Iio]; rw [typein_ordinal]

Depends on / 依赖: Order.cof_Iio, cof_Iio, typein_ordinal
-/
theorem cof_Iio (o : Ordinal.{u}) : Order.cof (Iio o) = cof (lift.{u + 1} o) := by
  rw [Order.cof_Iio]; rw [typein_ordinal]

/--
theorem `cof_le_card` / 定理 `cof_le_card`

English:
theorem cof_le_card
  given: (o : Ordinal)
  statement: cof o <= card o
  proof: by
  simpa using cof_le_cardinalMk o.ToType

中文:
定理 cof_le_card
  条件: (o : 序数)
  结论: cof o <= card o
  证明: by
  simpa using cof_le_cardinalMk o.ToType

Depends on / 依赖: ToType, cof_le_cardinalMk, o.ToType
-/
theorem cof_le_card (o : Ordinal) : cof o <= card o := by
  simpa using cof_le_cardinalMk o.ToType

/--
theorem `cof_ord_le` / 定理 `cof_ord_le`

English:
theorem cof_ord_le
  given: (c : Cardinal)
  statement: c.ord.cof <= c
  proof: by
  simpa using cof_le_card c.ord

中文:
定理 cof_ord_le
  条件: (c : 基数)
  结论: c.ord.cof <= c
  证明: by
  simpa using cof_le_card c.ord

Depends on / 依赖: c.ord, cof_le_card
-/
theorem cof_ord_le (c : Cardinal) : c.ord.cof <= c := by
  simpa using cof_le_card c.ord

/--
theorem `ord_cof_le` / 定理 `ord_cof_le`

English:
theorem ord_cof_le
  given: (o : Ordinal)
  statement: o.cof.ord <= o
  proof: (ord_le_ord.2 (cof_le_card o)).trans (ord_card_le o)

@[simp]

中文:
定理 ord_cof_le
  条件: (o : 序数)
  结论: o.cof.ord <= o
  证明: (ord_le_ord.2 (cof_le_card o)).trans (ord_card_le o)

@[simp]

Depends on / 依赖: cof_le_card, ord_card_le, ord_le_ord
-/
theorem ord_cof_le (o : Ordinal) : o.cof.ord <= o :=
  (ord_le_ord.2 (cof_le_card o)).trans (ord_card_le o)

@[simp]
/--
theorem `cof_eq_zero` / 定理 `cof_eq_zero`

English:
theorem cof_eq_zero
  given: {o}
  statement: cof o = 0 ↔ o = 0
  proof: by
  rw [← cof_toType]; rw [cof_eq_zero_iff]; rw [isEmpty_toType_iff]

@[deprecated cof_eq_zero (since := "2026-02-18")]

中文:
定理 cof_eq_zero
  条件: {o}
  结论: cof o = 0 ↔ o = 0
  证明: by
  rw [← cof_toType]; rw [cof_eq_zero_iff]; rw [isEmpty_toType_iff]

@[deprecated cof_eq_zero (since := "2026-02-18")]

Depends on / 依赖: cof_eq_zero_iff, cof_toType, isEmpty_toType_iff
-/
theorem cof_eq_zero {o} : cof o = 0 ↔ o = 0 := by
  rw [← cof_toType]; rw [cof_eq_zero_iff]; rw [isEmpty_toType_iff]

@[deprecated cof_eq_zero (since := "2026-02-18")]
/--
theorem `cof_ne_zero` / 定理 `cof_ne_zero`

English:
theorem cof_ne_zero
  given: {o}
  statement: cof o != 0 ↔ o != 0
  proof: cof_eq_zero.not

@[simp]

中文:
定理 cof_ne_zero
  条件: {o}
  结论: cof o != 0 ↔ o != 0
  证明: cof_eq_zero.not

@[simp]

Depends on / 依赖: cof_eq_zero, cof_eq_zero.not
-/
theorem cof_ne_zero {o} : cof o != 0 ↔ o != 0 :=
  cof_eq_zero.not

@[simp]
/--
theorem `cof_pos` / 定理 `cof_pos`

English:
theorem cof_pos
  given: {o}
  statement: 0 < cof o ↔ 0 < o
  proof: by
  simp [pos_iff_ne_zero]

@[simp]

中文:
定理 cof_pos
  条件: {o}
  结论: 0 < cof o ↔ 0 < o
  证明: by
  simp [pos_iff_ne_zero]

@[simp]

Depends on / 依赖: pos_iff_ne_zero
-/
theorem cof_pos {o} : 0 < cof o ↔ 0 < o := by
  simp [pos_iff_ne_zero]

@[simp]
/--
theorem `cof_zero` / 定理 `cof_zero`

English:
theorem cof_zero
  statement: cof 0 = 0
  proof: cof_eq_zero.2 rfl

中文:
定理 cof_zero
  结论: cof 0 = 0
  证明: cof_eq_zero.2 rfl

Depends on / 依赖: cof_eq_zero
-/
theorem cof_zero : cof 0 = 0 :=
  cof_eq_zero.2 rfl

/--
theorem `cof_eq_one_iff` / 定理 `cof_eq_one_iff`

English:
theorem cof_eq_one_iff
  given: {o}
  statement: cof o = 1 ↔ o in range succ
  proof: by
  cases o using inductionOnWellOrder with | type α
  rw [cof_type]; rw [Order.cof_eq_one_iff]; rw [type_lt_mem_range_succ_iff]
  simp_rw [isTop_iff_isMax]

中文:
定理 cof_eq_one_iff
  条件: {o}
  结论: cof o = 1 ↔ o in range succ
  证明: by
  cases o using inductionOnWellOrder with | type α
  rw [cof_type]; rw [Order.cof_eq_one_iff]; rw [type_lt_mem_range_succ_iff]
  simp_rw [isTop_iff_isMax]

Depends on / 依赖: Order.cof_eq_one_iff, cof_eq_one_iff, cof_type, inductionOnWellOrder, isTop_iff_isMax, simp_rw, type_lt_mem_range_succ_iff
-/
theorem cof_eq_one_iff {o} : cof o = 1 ↔ o in range succ := by
  cases o using inductionOnWellOrder with | type α
  rw [cof_type]; rw [Order.cof_eq_one_iff]; rw [type_lt_mem_range_succ_iff]
  simp_rw [isTop_iff_isMax]

/--
theorem `cof_add_one` / 定理 `cof_add_one`

English:
theorem cof_add_one
  given: (o)
  statement: cof (o + 1) = 1
  proof: cof_eq_one_iff.2 (mem_range_self o)

@[simp]

中文:
定理 cof_add_one
  条件: (o)
  结论: cof (o + 1) = 1
  证明: cof_eq_one_iff.2 (mem_range_self o)

@[simp]

Depends on / 依赖: cof_eq_one_iff, mem_range_self
-/
theorem cof_add_one (o) : cof (o + 1) = 1 :=
  cof_eq_one_iff.2 (mem_range_self o)

@[simp]
/--
theorem `cof_one` / 定理 `cof_one`

English:
theorem cof_one
  statement: cof 1 = 1
  proof: by
  simpa using cof_add_one 0

@[deprecated cof_add_one (since := "2026-05-25")]

中文:
定理 cof_one
  结论: cof 1 = 1
  证明: by
  simpa using cof_add_one 0

@[deprecated cof_add_one (since := "2026-05-25")]

Depends on / 依赖: cof_add_one
-/
theorem cof_one : cof 1 = 1 := by
  simpa using cof_add_one 0

@[deprecated cof_add_one (since := "2026-05-25")]
/--
theorem `cof_succ` / 定理 `cof_succ`

English:
theorem cof_succ
  given: (o)
  statement: cof (succ o) = 1
  proof: cof_add_one o

中文:
定理 cof_succ
  条件: (o)
  结论: cof (succ o) = 1
  证明: cof_add_one o

Depends on / 依赖: cof_add_one
-/
theorem cof_succ (o) : cof (succ o) = 1 :=
  cof_add_one o

/--
theorem `one_lt_cof_iff` / 定理 `one_lt_cof_iff`

English:
theorem one_lt_cof_iff
  given: {o : Ordinal}
  statement: 1 < cof o ↔ IsSuccLimit o
  proof: by
  rw [← not_iff_not]; rw [not_lt]; rw [Cardinal.le_one_iff]; rw [isSuccLimit_iff]; rw [not_and_or]; rw [not_ne_iff]; rw [not_isSuccPrelimit_iff_mem_range_succ]; rw [cof_eq_zero]; rw [cof_eq_one_iff]

@[simp]

中文:
定理 one_lt_cof_iff
  条件: {o : 序数}
  结论: 1 < cof o ↔ 是SuccLimit o
  证明: by
  rw [← not_iff_not]; rw [not_lt]; rw [Cardinal.le_one_iff]; rw [isSuccLimit_iff]; rw [not_and_or]; rw [not_ne_iff]; rw [not_isSuccPrelimit_iff_mem_range_succ]; rw [cof_eq_zero]; rw [cof_eq_one_iff]

@[simp]

Depends on / 依赖: Cardinal, Cardinal.le_one_iff, cof_eq_one_iff, cof_eq_zero, isSuccLimit_iff, le_one_iff, not_and_or, not_iff_not, not_isSuccPrelimit_iff_mem_range_succ, not_lt, not_ne_iff
-/
theorem one_lt_cof_iff {o : Ordinal} : 1 < cof o ↔ IsSuccLimit o := by
  rw [← not_iff_not]; rw [not_lt]; rw [Cardinal.le_one_iff]; rw [isSuccLimit_iff]; rw [not_and_or]; rw [not_ne_iff]; rw [not_isSuccPrelimit_iff_mem_range_succ]; rw [cof_eq_zero]; rw [cof_eq_one_iff]

@[simp]
/--
theorem `cof_lt_aleph0_iff` / 定理 `cof_lt_aleph0_iff`

English:
theorem cof_lt_aleph0_iff
  given: {o : Ordinal}
  statement: cof o < ℵ₀ ↔ cof o <= 1
  proof: by
  simpa using Order.cof_lt_aleph0_iff (α := o.ToType)

@[simp]

中文:
定理 cof_lt_aleph0_iff
  条件: {o : 序数}
  结论: cof o < ℵ₀ ↔ cof o <= 1
  证明: by
  simpa using Order.cof_lt_aleph0_iff (α := o.ToType)

@[simp]

Depends on / 依赖: Order.cof_lt_aleph0_iff, ToType, cof_lt_aleph0_iff, o.ToType
-/
theorem cof_lt_aleph0_iff {o : Ordinal} : cof o < ℵ₀ ↔ cof o <= 1 := by
  simpa using Order.cof_lt_aleph0_iff (α := o.ToType)

@[simp]
/--
theorem `aleph0_le_cof_iff` / 定理 `aleph0_le_cof_iff`

English:
theorem aleph0_le_cof_iff
  given: {o : Ordinal}
  statement: ℵ₀ <= cof o ↔ 1 < cof o
  proof: by
  simp [← not_lt]

@[deprecated one_lt_cof_iff (since := "2026-03-22")]

中文:
定理 aleph0_le_cof_iff
  条件: {o : 序数}
  结论: ℵ₀ <= cof o ↔ 1 < cof o
  证明: by
  simp [← not_lt]

@[deprecated one_lt_cof_iff (since := "2026-03-22")]

Depends on / 依赖: not_lt
-/
theorem aleph0_le_cof_iff {o : Ordinal} : ℵ₀ <= cof o ↔ 1 < cof o := by
  simp [← not_lt]

@[deprecated one_lt_cof_iff (since := "2026-03-22")]
/--
theorem `aleph0_le_cof` / 定理 `aleph0_le_cof`

English:
theorem aleph0_le_cof
  given: {o}
  statement: ℵ₀ <= cof o ↔ IsSuccLimit o
  proof: by
  rw [aleph0_le_cof_iff]; rw [one_lt_cof_iff]

中文:
定理 aleph0_le_cof
  条件: {o}
  结论: ℵ₀ <= cof o ↔ 是SuccLimit o
  证明: by
  rw [aleph0_le_cof_iff]; rw [one_lt_cof_iff]

Depends on / 依赖: aleph0_le_cof_iff, one_lt_cof_iff
-/
theorem aleph0_le_cof {o} : ℵ₀ <= cof o ↔ IsSuccLimit o := by
  rw [aleph0_le_cof_iff]; rw [one_lt_cof_iff]

/--
theorem `cof_eq_aleph0_of_isSuccLimit` / 定理 `cof_eq_aleph0_of_isSuccLimit`

English:
theorem cof_eq_aleph0_of_isSuccLimit
  given: {o : Ordinal} (ho : IsSuccLimit o) (ho' : o < ω₁)
  proof: by
  apply ((cof_le_card _).trans _).antisymm
  · rwa [aleph0_le_cof_iff, one_lt_cof_iff]
  · rwa [card_le_iff, succ_aleph0, ord_aleph]

@[simp]

中文:
定理 cof_eq_aleph0_of_isSuccLimit
  条件: {o : 序数} (ho : 是SuccLimit o) (ho' : o < ω₁)
  证明: by
  apply ((cof_le_card _).trans _).antisymm
  · rwa [aleph0_le_cof_iff, one_lt_cof_iff]
  · rwa [card_le_iff, succ_aleph0, ord_aleph]

@[simp]

Depends on / 依赖: aleph0_le_cof_iff, antisymm, card_le_iff, cof_le_card, one_lt_cof_iff, ord_aleph, succ_aleph0
-/
theorem cof_eq_aleph0_of_isSuccLimit {o : Ordinal} (ho : IsSuccLimit o) (ho' : o < ω₁) :
    cof o = ℵ₀ := by
  apply ((cof_le_card _).trans _).antisymm
  · rwa [aleph0_le_cof_iff, one_lt_cof_iff]
  · rwa [card_le_iff, succ_aleph0, ord_aleph]

@[simp]
/--
theorem `cof_omega0` / 定理 `cof_omega0`

English:
theorem cof_omega0
  statement: cof ω = ℵ₀
  proof: cof_eq_aleph0_of_isSuccLimit isSuccLimit_omega0 omega0_lt_omega_one

@[deprecated (since := "2026-02-18")] alias cof_eq_one_iff_is_succ := cof_eq_one_iff

中文:
定理 cof_omega0
  结论: cof ω = ℵ₀
  证明: cof_eq_aleph0_of_isSuccLimit isSuccLimit_omega0 omega0_lt_omega_one

@[deprecated (since := "2026-02-18")] alias cof_eq_one_iff_is_succ := cof_eq_one_iff

Depends on / 依赖: cof_eq_aleph0_of_isSuccLimit, isSuccLimit_omega0, omega0_lt_omega_one
-/
theorem cof_omega0 : cof ω = ℵ₀ :=
  cof_eq_aleph0_of_isSuccLimit isSuccLimit_omega0 omega0_lt_omega_one

@[deprecated (since := "2026-02-18")] alias cof_eq_one_iff_is_succ := cof_eq_one_iff

variable (α) in
/--
theorem `exists_ord_cof_eq` / 定理 `exists_ord_cof_eq`

English:
theorem exists_ord_cof_eq
  given: [LinearOrder α] [WellFoundedLT α]
  proof: by
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  obtain ⟨r, hr, hr'⟩ := exists_ord_eq s
  have ht := hs.trans (isCofinal_setOfPred_imp_lt r)
  refine ⟨_, ht, (ord_le.2 (cof_le ht)).antisymm' ?_⟩
  rw [← hs']; rw [hr']; rw [type_le_iff']
  refine ⟨.ofMonotone (fun x => ⟨x.1, ?_⟩) fun x y hxy => ?_⟩
  · 

中文:
定理 存在_ord_cof_eq
  条件: [线性序 α] [WellFoundedLT α]
  证明: by
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  obtain ⟨r, hr, hr'⟩ := exists_ord_eq s
  have ht := hs.trans (isCofinal_setOfPred_imp_lt r)
  refine ⟨_, ht, (ord_le.2 (cof_le ht)).antisymm' ?_⟩
  rw [← hs']; rw [hr']; rw [type_le_iff']
  refine ⟨.ofMonotone (fun x => ⟨x.1, ?_⟩) fun x y hxy => ?_⟩
  · 

Depends on / 依赖: Subtype, Subtype.coe_inj, antisymm, coe_inj, cof_le, exists_cof_eq, exists_ord_eq, hs.trans, isCofinal_setOfPred_imp_lt, ofMonotone, ord_le, resolve_right, trichotomous_of, type_le_iff
-/
theorem exists_ord_cof_eq [LinearOrder α] [WellFoundedLT α] :
    exists s : Set α, IsCofinal s ∧ typeLT s = (Order.cof α).ord := by
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  obtain ⟨r, hr, hr'⟩ := exists_ord_eq s
  have ht := hs.trans (isCofinal_setOfPred_imp_lt r)
  refine ⟨_, ht, (ord_le.2 (cof_le ht)).antisymm' ?_⟩
  rw [← hs']; rw [hr']; rw [type_le_iff']
  refine ⟨.ofMonotone (fun x => ⟨x.1, ?_⟩) fun x y hxy => ?_⟩
  · grind
  · apply (trichotomous_of r _ _).resolve_right
    rintro (_ | hxy')
    · simp_all [Subtype.coe_inj]
    · obtain ⟨x, z, hz, rfl⟩ := x
      exact (hz _ hxy').asymm hxy

@[deprecated (since := "2026-05-25")] alias ord_cof_eq := exists_ord_cof_eq

/--
theorem `exists_ord_cof_eq_of_isCofinal` / 定理 `exists_ord_cof_eq_of_isCofinal`

English:
theorem exists_ord_cof_eq_of_isCofinal
  statement: [LinearOrder α] [WellFoundedLT α]
  proof: by
  obtain ⟨t, ht, ht'⟩ := exists_ord_cof_eq s
  rw [cof_eq_of_isCofinal hs] at ht'
  refine ⟨t, ?_, hs.trans ht, ?_⟩
  · simp
  · rw [← ht']
    exact ((Subtype.strictMono_coe _).strictMonoOn _).orderIso.ordinalType_congr.symm

@[simp]

中文:
定理 存在_ord_cof_eq_of_isCofinal
  结论: [线性序 α] [WellFoundedLT α]
  证明: by
  obtain ⟨t, ht, ht'⟩ := exists_ord_cof_eq s
  rw [cof_eq_of_isCofinal hs] at ht'
  refine ⟨t, ?_, hs.trans ht, ?_⟩
  · simp
  · rw [← ht']
    exact ((Subtype.strictMono_coe _).strictMonoOn _).orderIso.ordinalType_congr.symm

@[simp]

Depends on / 依赖: Subtype, Subtype.strictMono_coe, cof_eq_of_isCofinal, exists_ord_cof_eq, hs.trans, orderIso, orderIso.ordinalType_congr.symm, ordinalType_congr, strictMonoOn, strictMono_coe
-/
theorem exists_ord_cof_eq_of_isCofinal [LinearOrder α] [WellFoundedLT α]
    {s : Set α} (hs : IsCofinal s) : exists t subseteq s, IsCofinal t ∧ typeLT t = (Order.cof α).ord := by
  obtain ⟨t, ht, ht'⟩ := exists_ord_cof_eq s
  rw [cof_eq_of_isCofinal hs] at ht'
  refine ⟨t, ?_, hs.trans ht, ?_⟩
  · simp
  · rw [← ht']
    exact ((Subtype.strictMono_coe _).strictMonoOn _).orderIso.ordinalType_congr.symm

@[simp]
/--
theorem `_root_.Order.cof_ord_cof` / 定理 `_root_.Order.cof_ord_cof`

English:
theorem _root_.Order.cof_ord_cof
  given: (α : Type*) [LinearOrder α] [WellFoundedLT α]
  proof: by
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq α
  rw [← hs']; rw [cof_type]; rw [cof_eq_of_isCofinal hs]

@[simp]

中文:
定理 _root_.Order.cof_ord_cof
  条件: (α : 类型) [线性序 α] [WellFoundedLT α]
  证明: by
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq α
  rw [← hs']; rw [cof_type]; rw [cof_eq_of_isCofinal hs]

@[simp]

Depends on / 依赖: cof_eq_of_isCofinal, cof_type, exists_ord_cof_eq
-/
theorem _root_.Order.cof_ord_cof (α : Type*) [LinearOrder α] [WellFoundedLT α] :
    (Order.cof α).ord.cof = Order.cof α := by
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq α
  rw [← hs']; rw [cof_type]; rw [cof_eq_of_isCofinal hs]

@[simp]
/--
theorem `cof_ord_cof` / 定理 `cof_ord_cof`

English:
theorem cof_ord_cof
  given: (o : Ordinal)
  statement: o.cof.ord.cof = o.cof
  proof: by
  simpa using Order.cof_ord_cof o.ToType

@[deprecated (since := "2026-03-21")] alias cof_cof := cof_ord_cof

中文:
定理 cof_ord_cof
  条件: (o : 序数)
  结论: o.cof.ord.cof = o.cof
  证明: by
  simpa using Order.cof_ord_cof o.ToType

@[deprecated (since := "2026-03-21")] alias cof_cof := cof_ord_cof

Depends on / 依赖: Order.cof_ord_cof, ToType, cof_ord_cof, o.ToType
-/
theorem cof_ord_cof (o : Ordinal) : o.cof.ord.cof = o.cof := by
  simpa using Order.cof_ord_cof o.ToType

@[deprecated (since := "2026-03-21")] alias cof_cof := cof_ord_cof

/-! ### Cofinalities and suprema -/

section LinearOrder
variable [LinearOrder β] [LinearOrder γ]

/--
theorem `lift_cof_iSup_add_one` / 定理 `lift_cof_iSup_add_one`

English:
theorem lift_cof_iSup_add_one
  given: [Small.{u} β] {f : β -> Ordinal} (hf : StrictMono f)
  proof: by
  have : StrictMono (β := Iio (⨆ i, f i + 1)) (fun i => ⟨f i, ?_⟩) := fun x y h => hf h
  · have := lift_cof_congr_of_strictMono this ?_
    · rw [← Cardinal.lift_inj.{_, max (u + 1) v}, Cardinal.lift_lift.{_, _, v},
        Cardinal.lift_umax.{_, u + 1}, Cardinal.lift_umax.{_, u + 1}, this]
    

中文:
定理 lift_cof_iSup_add_one
  条件: [Small.{u} β] {f : β -> 序数} (hf : 严格递增 f)
  证明: by
  have : StrictMono (β := Iio (⨆ i, f i + 1)) (fun i => ⟨f i, ?_⟩) := fun x y h => hf h
  · have := lift_cof_congr_of_strictMono this ?_
    · rw [← Cardinal.lift_inj.{_, max (u + 1) v}, Cardinal.lift_lift.{_, _, v},
        Cardinal.lift_umax.{_, u + 1}, Cardinal.lift_umax.{_, u + 1}, this]
    

Depends on / 依赖: Cardinal, Cardinal.lift_inj, Cardinal.lift_lift, Cardinal.lift_umax, Ordinal, Ordinal.lt_iSup_add_one_iff, Set.mem_range_self, StrictMono, bddAbove_of_small, le_ciSup, lift_cof_congr_of_strictMono, lift_inj, lift_lift, lift_umax, lt_add_one, lt_iSup_add_one_iff, mem_Iio, mem_range_self, trans_le
-/
theorem lift_cof_iSup_add_one [Small.{u} β] {f : β -> Ordinal} (hf : StrictMono f) :
    Cardinal.lift.{v} (cof (⨆ i, f i + 1)) = Cardinal.lift.{u} (Order.cof β) := by
  have : StrictMono (β := Iio (⨆ i, f i + 1)) (fun i => ⟨f i, ?_⟩) := fun x y h => hf h
  · have := lift_cof_congr_of_strictMono this ?_
    · rw [← Cardinal.lift_inj.{_, max (u + 1) v}, Cardinal.lift_lift.{_, _, v},
        Cardinal.lift_umax.{_, u + 1}, Cardinal.lift_umax.{_, u + 1}, this]
      simp
    · intro ⟨b, hb⟩
      rw [mem_Iio]; rw [Ordinal.lt_iSup_add_one_iff] at hb
      obtain ⟨i, hi⟩ := hb
      exact ⟨_, Set.mem_range_self i, hi⟩
  · rw [mem_Iio]
exact (lt_add_one _).trans_le le_ciSup bddAbove_of_small _

/--
theorem `cof_iSup_add_one` / 定理 `cof_iSup_add_one`

English:
theorem cof_iSup_add_one
  given: {f : γ -> Ordinal} (hf : StrictMono f)
  proof: by
  simpa using lift_cof_iSup_add_one hf

中文:
定理 cof_iSup_add_one
  条件: {f : γ -> 序数} (hf : 严格递增 f)
  证明: by
  simpa using lift_cof_iSup_add_one hf

Depends on / 依赖: lift_cof_iSup_add_one
-/
theorem cof_iSup_add_one {f : γ -> Ordinal} (hf : StrictMono f) :
    cof (⨆ i, f i + 1) = Order.cof γ := by
  simpa using lift_cof_iSup_add_one hf

/--
theorem `lift_cof_iSup` / 定理 `lift_cof_iSup`

English:
theorem lift_cof_iSup
  given: [Small.{u} β] [NoMaxOrder β] {f : β -> Ordinal} (hf : StrictMono f)
  proof: by
  rw [← iSup_add_one hf]; rw [lift_cof_iSup_add_one hf]

中文:
定理 lift_cof_iSup
  条件: [Small.{u} β] [NoMax序 β] {f : β -> 序数} (hf : 严格递增 f)
  证明: by
  rw [← iSup_add_one hf]; rw [lift_cof_iSup_add_one hf]

Depends on / 依赖: iSup_add_one, lift_cof_iSup_add_one
-/
theorem lift_cof_iSup [Small.{u} β] [NoMaxOrder β] {f : β -> Ordinal} (hf : StrictMono f) :
    Cardinal.lift.{v} (cof (⨆ i, f i)) = Cardinal.lift.{u} (Order.cof β) := by
  rw [← iSup_add_one hf]; rw [lift_cof_iSup_add_one hf]

/--
theorem `cof_iSup` / 定理 `cof_iSup`

English:
theorem cof_iSup
  given: [NoMaxOrder γ] {f : γ -> Ordinal} (hf : StrictMono f)
  proof: by
  simpa using lift_cof_iSup hf

中文:
定理 cof_iSup
  条件: [NoMax序 γ] {f : γ -> 序数} (hf : 严格递增 f)
  证明: by
  simpa using lift_cof_iSup hf

Depends on / 依赖: lift_cof_iSup
-/
theorem cof_iSup [NoMaxOrder γ] {f : γ -> Ordinal} (hf : StrictMono f) :
    cof (⨆ i, f i) = Order.cof γ := by
  simpa using lift_cof_iSup hf

end LinearOrder

/--
theorem `cof_iSup_Iio_add_one` / 定理 `cof_iSup_Iio_add_one`

English:
theorem cof_iSup_Iio_add_one
  given: {a} {f : Iio a -> Ordinal} (hf : StrictMono f)
  proof: by
  simpa [← lift_cof] using lift_cof_iSup_add_one hf

中文:
定理 cof_iSup_Iio_add_one
  条件: {a} {f : 左无界右开区间 a -> 序数} (hf : 严格递增 f)
  证明: by
  simpa [← lift_cof] using lift_cof_iSup_add_one hf

Depends on / 依赖: lift_cof, lift_cof_iSup_add_one
-/
theorem cof_iSup_Iio_add_one {a} {f : Iio a -> Ordinal} (hf : StrictMono f) :
    cof (⨆ i, f i + 1) = cof a := by
  simpa [← lift_cof] using lift_cof_iSup_add_one hf

/--
theorem `cof_iSup_Iio` / 定理 `cof_iSup_Iio`

English:
theorem cof_iSup_Iio
  given: {a} {f : Iio a -> Ordinal} (hf : StrictMono f) (ha : IsSuccPrelimit a)
  proof: by
  rw [← iSup_Iio_add_one hf ha]; rw [cof_iSup_Iio_add_one hf]

中文:
定理 cof_iSup_Iio
  条件: {a} {f : 左无界右开区间 a -> 序数} (hf : 严格递增 f) (ha : IsSuccPrelimit a)
  证明: by
  rw [← iSup_Iio_add_one hf ha]; rw [cof_iSup_Iio_add_one hf]

Depends on / 依赖: cof_iSup_Iio_add_one, iSup_Iio_add_one
-/
theorem cof_iSup_Iio {a} {f : Iio a -> Ordinal} (hf : StrictMono f) (ha : IsSuccPrelimit a) :
    cof (⨆ i, f i) = cof a := by
  rw [← iSup_Iio_add_one hf ha]; rw [cof_iSup_Iio_add_one hf]

/--
theorem `cof_map_of_isNormal` / 定理 `cof_map_of_isNormal`

English:
theorem cof_map_of_isNormal
  given: {f} (hf : IsNormal f) {a} (ha : IsSuccLimit a)
  statement: cof (f a) = cof a
  proof: by
  rw [hf.apply_of_isSuccLimit ha]; rw [cof_iSup_Iio _ ha.isSuccPrelimit]
exact hf.strictMono.comp Subtype.strictMono_coe _

@[deprecated (since := "2026-03-19")]
alias cof_eq_of_isNormal := cof_map_of_isNormal

中文:
定理 cof_map_of_isNormal
  条件: {f} (hf : 是正规 f) {a} (ha : 是SuccLimit a)
  结论: cof (f a) = cof a
  证明: by
  rw [hf.apply_of_isSuccLimit ha]; rw [cof_iSup_Iio _ ha.isSuccPrelimit]
exact hf.strictMono.comp Subtype.strictMono_coe _

@[deprecated (since := "2026-03-19")]
alias cof_eq_of_isNormal := cof_map_of_isNormal

Depends on / 依赖: Subtype, Subtype.strictMono_coe, apply_of_isSuccLimit, cof_iSup_Iio, ha.isSuccPrelimit, hf.apply_of_isSuccLimit, hf.strictMono.comp, isSuccPrelimit, strictMono, strictMono_coe
-/
theorem cof_map_of_isNormal {f} (hf : IsNormal f) {a} (ha : IsSuccLimit a) : cof (f a) = cof a := by
  rw [hf.apply_of_isSuccLimit ha]; rw [cof_iSup_Iio _ ha.isSuccPrelimit]
exact hf.strictMono.comp Subtype.strictMono_coe _

@[deprecated (since := "2026-03-19")]
alias cof_eq_of_isNormal := cof_map_of_isNormal

/--
theorem `le_cof_map_of_isNormal` / 定理 `le_cof_map_of_isNormal`

English:
theorem le_cof_map_of_isNormal
  given: {f} (hf : IsNormal f) (a)
  statement: cof a <= cof (f a)
  proof: by
  cases a using limitRecOn with
  | zero => simp
  | add_one a =>
    rw [cof_add_one]; rw [Cardinal.one_le_iff_ne_zero]; rw [cof_eq_zero.ne]
    exact (hf.strictMono (lt_succ a)).ne_zero
  | limit a ha => rw [cof_map_of_isNormal hf ha]

@[deprecated (since := "2026-03-19")]
alias cof_le_of_isNor

中文:
定理 le_cof_map_of_isNormal
  条件: {f} (hf : 是正规 f) (a)
  结论: cof a <= cof (f a)
  证明: by
  cases a using limitRecOn with
  | zero => simp
  | add_one a =>
    rw [cof_add_one]; rw [Cardinal.one_le_iff_ne_zero]; rw [cof_eq_zero.ne]
    exact (hf.strictMono (lt_succ a)).ne_zero
  | limit a ha => rw [cof_map_of_isNormal hf ha]

@[deprecated (since := "2026-03-19")]
alias cof_le_of_isNor

Depends on / 依赖: Cardinal, Cardinal.one_le_iff_ne_zero, add_one, cof_add_one, cof_eq_zero, cof_eq_zero.ne, cof_map_of_isNormal, hf.strictMono, limitRecOn, lt_succ, ne_zero, one_le_iff_ne_zero, strictMono
-/
theorem le_cof_map_of_isNormal {f} (hf : IsNormal f) (a) : cof a <= cof (f a) := by
  cases a using limitRecOn with
  | zero => simp
  | add_one a =>
    rw [cof_add_one]; rw [Cardinal.one_le_iff_ne_zero]; rw [cof_eq_zero.ne]
    exact (hf.strictMono (lt_succ a)).ne_zero
  | limit a ha => rw [cof_map_of_isNormal hf ha]

@[deprecated (since := "2026-03-19")]
alias cof_le_of_isNormal := le_cof_map_of_isNormal

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sSup_add_one_lt_of_lt_cof` / 定理 `sSup_add_one_lt_of_lt_cof`

English:
theorem sSup_add_one_lt_of_lt_cof
  statement: {s : Set Ordinal.{u}} {a : Ordinal.{u}}
  proof: by
  let f := OrderIso.ofRelIsoLT (enum (α := s) (· < ·))
  have : Small.{u} (Iio (typeLT s)) := by
    refine small_of_injective (β := Iio a) (f := fun x => ⟨f x, hs _ (f x).2⟩) fun _ => ?_
    simp [Subtype.val_inj]
  have : range (fun i => (f i).1 + 1) = (· + 1) '' s := by
    convert! range_comp

中文:
定理 sSup_add_one_lt_of_lt_cof
  结论: {s : 集合 序数.{u}} {a : 序数.{u}}
  证明: by
  let f := OrderIso.ofRelIsoLT (enum (α := s) (· < ·))
  have : Small.{u} (Iio (typeLT s)) := by
    refine small_of_injective (β := Iio a) (f := fun x => ⟨f x, hs _ (f x).2⟩) fun _ => ?_
    simp [Subtype.val_inj]
  have : range (fun i => (f i).1 + 1) = (· + 1) '' s := by
    convert! range_comp

Depends on / 依赖: Cardinal, Cardinal.lift_, Cardinal.lift_lt, OrderIso, OrderIso.ofRelIsoLT, Subtype, Subtype.val_inj, convert, f.range_eq, lift_, lift_cof, lift_lt, lt_of_le_of_ne, ofRelIsoLT, range_comp, range_eq, sSup_range, small_of_injective, typeLT, val_inj
-/
theorem sSup_add_one_lt_of_lt_cof {s : Set Ordinal.{u}} {a : Ordinal.{u}}
    (ha : #s < (lift.{u + 1} a).cof) (hs : forall i in s, i < a) : sSup ((· + 1) '' s) < a := by
  let f := OrderIso.ofRelIsoLT (enum (α := s) (· < ·))
  have : Small.{u} (Iio (typeLT s)) := by
    refine small_of_injective (β := Iio a) (f := fun x => ⟨f x, hs _ (f x).2⟩) fun _ => ?_
    simp [Subtype.val_inj]
  have : range (fun i => (f i).1 + 1) = (· + 1) '' s := by
    convert! range_comp (· + 1) (fun i => (f i).1)
    rw [range_comp']; rw [f.range_eq]
    simp
  rw [← this]; rw [sSup_range]
  apply lt_of_le_of_ne
  · simp [hs]
  · rintro rfl
    rw [← lift_cof]; rw [← Cardinal.lift_lt.{_]; rw [u + 2}]; rw [Cardinal.lift_lift]; rw [lift_cof_iSup_add_one fun _ => by simp]; rw [cof_Iio]; rw [← lift_cof]; rw [cof_type]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lt] at ha
    exact ha.not_ge (cof_le_cardinalMk _)

/--
theorem `sSup_lt_of_lt_cof` / 定理 `sSup_lt_of_lt_cof`

English:
theorem sSup_lt_of_lt_cof
  statement: {s : Set Ordinal.{u}} {a : Ordinal.{u}}
  proof: (sSup_le_sSup_add_one s).trans_lt (sSup_add_one_lt_of_lt_cof ha hs)

中文:
定理 sSup_lt_of_lt_cof
  结论: {s : 集合 序数.{u}} {a : 序数.{u}}
  证明: (sSup_le_sSup_add_one s).trans_lt (sSup_add_one_lt_of_lt_cof ha hs)

Depends on / 依赖: sSup_add_one_lt_of_lt_cof, sSup_le_sSup_add_one, trans_lt
-/
theorem sSup_lt_of_lt_cof {s : Set Ordinal.{u}} {a : Ordinal.{u}}
    (ha : #s < (lift.{u + 1} a).cof) (hs : forall i in s, i < a) : sSup s < a :=
  (sSup_le_sSup_add_one s).trans_lt (sSup_add_one_lt_of_lt_cof ha hs)

/--
theorem `lift_iSup_add_one_lt_of_lt_cof` / 定理 `lift_iSup_add_one_lt_of_lt_cof`

English:
theorem lift_iSup_add_one_lt_of_lt_cof
  statement: {f : β -> Ordinal.{u}} {a : Ordinal.{u}}
  proof: by
  rw [iSup]; rw [range_comp' (· + 1)]
  apply sSup_add_one_lt_of_lt_cof _ (by simpa)
  rw [← Cardinal.lift_lt.{_]; rw [v}]
  apply mk_range_le_lift.trans_lt
  rw [← Cardinal.lift_lt.{_]; rw [u + 1}] at ha
  simpa [← lift_cof] using ha

中文:
定理 lift_iSup_add_one_lt_of_lt_cof
  结论: {f : β -> 序数.{u}} {a : 序数.{u}}
  证明: by
  rw [iSup]; rw [range_comp' (· + 1)]
  apply sSup_add_one_lt_of_lt_cof _ (by simpa)
  rw [← Cardinal.lift_lt.{_]; rw [v}]
  apply mk_range_le_lift.trans_lt
  rw [← Cardinal.lift_lt.{_]; rw [u + 1}] at ha
  simpa [← lift_cof] using ha

Depends on / 依赖: Cardinal, Cardinal.lift_lt, lift_cof, lift_lt, mk_range_le_lift, mk_range_le_lift.trans_lt, range_comp, sSup_add_one_lt_of_lt_cof, trans_lt
-/
theorem lift_iSup_add_one_lt_of_lt_cof {f : β -> Ordinal.{u}} {a : Ordinal.{u}}
    (ha : Cardinal.lift.{u} #β < (lift.{v} a).cof) (hf : forall i, f i < a) : ⨆ i, f i + 1 < a := by
  rw [iSup]; rw [range_comp' (· + 1)]
  apply sSup_add_one_lt_of_lt_cof _ (by simpa)
  rw [← Cardinal.lift_lt.{_]; rw [v}]
  apply mk_range_le_lift.trans_lt
  rw [← Cardinal.lift_lt.{_]; rw [u + 1}] at ha
  simpa [← lift_cof] using ha

/--
theorem `iSup_add_one_lt_of_lt_cof` / 定理 `iSup_add_one_lt_of_lt_cof`

English:
theorem iSup_add_one_lt_of_lt_cof
  statement: {f : α -> Ordinal.{u}} {a : Ordinal.{u}}
  proof: by
  rw [← Cardinal.lift_lt.{_]; rw [u}]; rw [lift_cof] at ha
  simpa using lift_iSup_add_one_lt_of_lt_cof ha hf

中文:
定理 iSup_add_one_lt_of_lt_cof
  结论: {f : α -> 序数.{u}} {a : 序数.{u}}
  证明: by
  rw [← Cardinal.lift_lt.{_]; rw [u}]; rw [lift_cof] at ha
  simpa using lift_iSup_add_one_lt_of_lt_cof ha hf

Depends on / 依赖: Cardinal, Cardinal.lift_lt, lift_cof, lift_iSup_add_one_lt_of_lt_cof, lift_lt
-/
theorem iSup_add_one_lt_of_lt_cof {f : α -> Ordinal.{u}} {a : Ordinal.{u}}
    (ha : #α < a.cof) (hf : forall i, f i < a) : ⨆ i, f i + 1 < a := by
  rw [← Cardinal.lift_lt.{_]; rw [u}]; rw [lift_cof] at ha
  simpa using lift_iSup_add_one_lt_of_lt_cof ha hf

/--
theorem `lift_iSup_lt_of_lt_cof` / 定理 `lift_iSup_lt_of_lt_cof`

English:
theorem lift_iSup_lt_of_lt_cof
  statement: {f : β -> Ordinal.{u}} {a : Ordinal.{u}}
  proof: (iSup_le_iSup_add_one f).trans_lt (lift_iSup_add_one_lt_of_lt_cof ha hf)

中文:
定理 lift_iSup_lt_of_lt_cof
  结论: {f : β -> 序数.{u}} {a : 序数.{u}}
  证明: (iSup_le_iSup_add_one f).trans_lt (lift_iSup_add_one_lt_of_lt_cof ha hf)

Depends on / 依赖: iSup_le_iSup_add_one, lift_iSup_add_one_lt_of_lt_cof, trans_lt
-/
theorem lift_iSup_lt_of_lt_cof {f : β -> Ordinal.{u}} {a : Ordinal.{u}}
    (ha : Cardinal.lift.{u} #β < (lift.{v} a).cof) (hf : forall i, f i < a) : ⨆ i, f i < a :=
  (iSup_le_iSup_add_one f).trans_lt (lift_iSup_add_one_lt_of_lt_cof ha hf)

/--
theorem `iSup_lt_of_lt_cof` / 定理 `iSup_lt_of_lt_cof`

English:
theorem iSup_lt_of_lt_cof
  statement: {f : α -> Ordinal.{u}} {a : Ordinal.{u}}
  proof: by
  rw [← Cardinal.lift_lt.{_]; rw [u}]; rw [lift_cof] at ha
  simpa using lift_iSup_lt_of_lt_cof ha hf

中文:
定理 iSup_lt_of_lt_cof
  结论: {f : α -> 序数.{u}} {a : 序数.{u}}
  证明: by
  rw [← Cardinal.lift_lt.{_]; rw [u}]; rw [lift_cof] at ha
  simpa using lift_iSup_lt_of_lt_cof ha hf

Depends on / 依赖: Cardinal, Cardinal.lift_lt, lift_cof, lift_iSup_lt_of_lt_cof, lift_lt
-/
theorem iSup_lt_of_lt_cof {f : α -> Ordinal.{u}} {a : Ordinal.{u}}
    (ha : #α < a.cof) (hf : forall i, f i < a) : ⨆ i, f i < a := by
  rw [← Cardinal.lift_lt.{_]; rw [u}]; rw [lift_cof] at ha
  simpa using lift_iSup_lt_of_lt_cof ha hf

/--
theorem `cof_lift_iSup_add_one_le` / 定理 `cof_lift_iSup_add_one_le`

English:
theorem cof_lift_iSup_add_one_le
  given: [Small.{u} β] (f : β -> Ordinal.{u})
  proof: by
  by_contra! hf
  exact (lift_iSup_add_one_lt_of_lt_cof hf <| Ordinal.lt_iSup_add_one _).false

中文:
定理 cof_lift_iSup_add_one_le
  条件: [Small.{u} β] (f : β -> 序数.{u})
  证明: by
  by_contra! hf
  exact (lift_iSup_add_one_lt_of_lt_cof hf <| Ordinal.lt_iSup_add_one _).false

Depends on / 依赖: Ordinal, Ordinal.lt_iSup_add_one, lift_iSup_add_one_lt_of_lt_cof, lt_iSup_add_one
-/
theorem cof_lift_iSup_add_one_le [Small.{u} β] (f : β -> Ordinal.{u}) :
    cof (lift.{v} (⨆ i, f i + 1)) <= Cardinal.lift.{u} (#β) := by
  by_contra! hf
  exact (lift_iSup_add_one_lt_of_lt_cof hf <| Ordinal.lt_iSup_add_one _).false

/--
theorem `cof_iSup_add_one_le` / 定理 `cof_iSup_add_one_le`

English:
theorem cof_iSup_add_one_le
  given: (f : α -> Ordinal.{u})
  statement: cof (⨆ i, f i + 1) <= #α
  proof: by
  simpa using cof_lift_iSup_add_one_le f

中文:
定理 cof_iSup_add_one_le
  条件: (f : α -> 序数.{u})
  结论: cof (⨆ i, f i + 1) <= #α
  证明: by
  simpa using cof_lift_iSup_add_one_le f

Depends on / 依赖: cof_lift_iSup_add_one_le
-/
theorem cof_iSup_add_one_le (f : α -> Ordinal.{u}) : cof (⨆ i, f i + 1) <= #α := by
  simpa using cof_lift_iSup_add_one_le f

/--
theorem `_root_.Cardinal.sSup_lt_of_lt_cof_ord` / 定理 `_root_.Cardinal.sSup_lt_of_lt_cof_ord`

English:
theorem _root_.Cardinal.sSup_lt_of_lt_cof_ord
  statement: {s : Set Cardinal.{u}} {a : Cardinal.{u}}
  proof: by
  rw [← ord_lt_ord]; rw [sSup_ord]
  apply Ordinal.sSup_lt_of_lt_cof
  · simpa [mk_image_eq ord_injective]
  · simpa

中文:
定理 _root_.基数.sSup_lt_of_lt_cof_ord
  结论: {s : 集合 基数.{u}} {a : 基数.{u}}
  证明: by
  rw [← ord_lt_ord]; rw [sSup_ord]
  apply Ordinal.sSup_lt_of_lt_cof
  · simpa [mk_image_eq ord_injective]
  · simpa

Depends on / 依赖: Ordinal, Ordinal.sSup_lt_of_lt_cof, mk_image_eq, ord_injective, ord_lt_ord, sSup_lt_of_lt_cof, sSup_ord
-/
theorem _root_.Cardinal.sSup_lt_of_lt_cof_ord {s : Set Cardinal.{u}} {a : Cardinal.{u}}
    (ha : #s < (Cardinal.lift.{u + 1} a).ord.cof) (hs : forall i in s, i < a) : sSup s < a := by
  rw [← ord_lt_ord]; rw [sSup_ord]
  apply Ordinal.sSup_lt_of_lt_cof
  · simpa [mk_image_eq ord_injective]
  · simpa

/--
theorem `_root_.Cardinal.lift_iSup_lt_of_lt_cof_ord` / 定理 `_root_.Cardinal.lift_iSup_lt_of_lt_cof_ord`

English:
theorem _root_.Cardinal.lift_iSup_lt_of_lt_cof_ord
  statement: {f : β -> Cardinal.{u}} {a : Cardinal.{u}}
  proof: by
  rw [← ord_lt_ord]; rw [iSup_ord]
  apply Ordinal.lift_iSup_lt_of_lt_cof <;> simpa

中文:
定理 _root_.基数.lift_iSup_lt_of_lt_cof_ord
  结论: {f : β -> 基数.{u}} {a : 基数.{u}}
  证明: by
  rw [← ord_lt_ord]; rw [iSup_ord]
  apply Ordinal.lift_iSup_lt_of_lt_cof <;> simpa

Depends on / 依赖: Ordinal, Ordinal.lift_iSup_lt_of_lt_cof, iSup_ord, lift_iSup_lt_of_lt_cof, ord_lt_ord
-/
theorem _root_.Cardinal.lift_iSup_lt_of_lt_cof_ord {f : β -> Cardinal.{u}} {a : Cardinal.{u}}
    (ha : Cardinal.lift.{u} #β < a.lift.ord.cof) (hf : forall i, f i < a) : ⨆ i, f i < a := by
  rw [← ord_lt_ord]; rw [iSup_ord]
  apply Ordinal.lift_iSup_lt_of_lt_cof <;> simpa

/--
theorem `_root_.Cardinal.iSup_lt_of_lt_cof_ord` / 定理 `_root_.Cardinal.iSup_lt_of_lt_cof_ord`

English:
theorem _root_.Cardinal.iSup_lt_of_lt_cof_ord
  statement: {f : α -> Cardinal.{u}} {a : Cardinal.{u}}
  proof: by
  rw [← ord_lt_ord]; rw [iSup_ord]
  apply Ordinal.iSup_lt_of_lt_cof <;> simpa

中文:
定理 _root_.基数.iSup_lt_of_lt_cof_ord
  结论: {f : α -> 基数.{u}} {a : 基数.{u}}
  证明: by
  rw [← ord_lt_ord]; rw [iSup_ord]
  apply Ordinal.iSup_lt_of_lt_cof <;> simpa

Depends on / 依赖: Ordinal, Ordinal.iSup_lt_of_lt_cof, iSup_lt_of_lt_cof, iSup_ord, ord_lt_ord
-/
theorem _root_.Cardinal.iSup_lt_of_lt_cof_ord {f : α -> Cardinal.{u}} {a : Cardinal.{u}}
    (ha : #α < a.ord.cof) (hf : forall i, f i < a) : ⨆ i, f i < a := by
  rw [← ord_lt_ord]; rw [iSup_ord]
  apply Ordinal.iSup_lt_of_lt_cof <;> simpa

/-- The set in the `lsub` characterization of `cof` is nonempty. -/
@[deprecated "to build an increasing function with limit o, use the fundamental sequence API."
(since := "2026-03-27")]
/--
theorem `cof_lsub_def_nonempty` / 定理 `cof_lsub_def_nonempty`

English:
theorem cof_lsub_def_nonempty
  given: (o)
  proof: ⟨_, ⟨_, _, lsub_typein o, mk_toType o⟩⟩

@[deprecated "to build an increasing function with limit o, use the fundamental sequence API."
(since := "2026-03-27")]

中文:
定理 cof_lsub_def_nonempty
  条件: (o)
  证明: ⟨_, ⟨_, _, lsub_typein o, mk_toType o⟩⟩

@[deprecated "to build an increasing function with limit o, use the fundamental sequence API."
(since := "2026-03-27")]

Depends on / 依赖: lsub_typein, mk_toType
-/
theorem cof_lsub_def_nonempty (o) :
    { a : Cardinal | exists (ι : _) (f : ι -> Ordinal), lsub.{u, u} f = o ∧ #ι = a }.Nonempty :=
  ⟨_, ⟨_, _, lsub_typein o, mk_toType o⟩⟩

@[deprecated "to build an increasing function with limit o, use the fundamental sequence API."
(since := "2026-03-27")]
/--
theorem `cof_eq_sInf_lsub` / 定理 `cof_eq_sInf_lsub`

English:
theorem cof_eq_sInf_lsub
  given: (o : Ordinal.{u})
  statement: cof o =
  proof: by
  refine le_antisymm (le_csInf (cof_lsub_def_nonempty o) ?_) (csInf_le' ?_)
  · rintro a ⟨ι, f, hf, rfl⟩
    rw [← hf]
    exact cof_iSup_add_one_le f
  · rcases Order.cof_eq (α := o.ToType) with ⟨S, hS, hS'⟩
    let f : S -> Ordinal := fun s => typein LT.lt s.val
    refine ⟨S, f, le_antisymm (l

中文:
定理 cof_eq_sInf_lsub
  条件: (o : 序数.{u})
  结论: cof o =
  证明: by
  refine le_antisymm (le_csInf (cof_lsub_def_nonempty o) ?_) (csInf_le' ?_)
  · rintro a ⟨ι, f, hf, rfl⟩
    rw [← hf]
    exact cof_iSup_add_one_le f
  · rcases Order.cof_eq (α := o.ToType) with ⟨S, hS, hS'⟩
    let f : S -> Ordinal := fun s => typein LT.lt s.val
    refine ⟨S, f, le_antisymm (l

Depends on / 依赖: LT.lt, Order.cof_eq, Ordinal, ToType, cof_eq, cof_iSup_add_one_le, cof_lsub_def_nonempty, cof_toType, csInf_le, le_antisymm, le_csInf, le_of_forall_lt, lsub_le, not_lt, o.ToType, s.val, type_toType, typein, typein_le_typein, typein_lt_self
-/
theorem cof_eq_sInf_lsub (o : Ordinal.{u}) : cof o =
    sInf { a : Cardinal | exists (ι : Type u) (f : ι -> Ordinal), lsub.{u, u} f = o ∧ #ι = a } := by
  refine le_antisymm (le_csInf (cof_lsub_def_nonempty o) ?_) (csInf_le' ?_)
  · rintro a ⟨ι, f, hf, rfl⟩
    rw [← hf]
    exact cof_iSup_add_one_le f
  · rcases Order.cof_eq (α := o.ToType) with ⟨S, hS, hS'⟩
    let f : S -> Ordinal := fun s => typein LT.lt s.val
    refine ⟨S, f, le_antisymm (lsub_le fun i => typein_lt_self (o := o) i)
      (le_of_forall_lt fun a ha => ?_), by rwa [cof_toType] at hS'⟩
    rw [← type_toType o] at ha
    rcases hS (enum (· < ·) ⟨a, ha⟩) with ⟨b, hb, hb'⟩
    rw [← not_lt]; rw [← typein_le_typein]; rw [typein_enum] at hb'
    exact hb'.trans_lt (lt_lsub.{u, u} f ⟨b, hb⟩)

@[deprecated "to build an increasing function with limit o, use the fundamental sequence API."
(since := "2026-03-27")]
/--
theorem `exists_lsub_cof` / 定理 `exists_lsub_cof`

English:
theorem exists_lsub_cof
  given: (o : Ordinal)
  proof: by
  rw [cof_eq_sInf_lsub]
  exact csInf_mem (cof_lsub_def_nonempty o)

@[deprecated cof_iSup_add_one_le (since := "2026-03-22")]

中文:
定理 存在_lsub_cof
  条件: (o : 序数)
  证明: by
  rw [cof_eq_sInf_lsub]
  exact csInf_mem (cof_lsub_def_nonempty o)

@[deprecated cof_iSup_add_one_le (since := "2026-03-22")]

Depends on / 依赖: cof_eq_sInf_lsub, cof_lsub_def_nonempty, csInf_mem
-/
theorem exists_lsub_cof (o : Ordinal) :
    exists (ι : _) (f : ι -> Ordinal), lsub.{u, u} f = o ∧ #ι = cof o := by
  rw [cof_eq_sInf_lsub]
  exact csInf_mem (cof_lsub_def_nonempty o)

@[deprecated cof_iSup_add_one_le (since := "2026-03-22")]
/--
theorem `cof_lsub_le` / 定理 `cof_lsub_le`

English:
theorem cof_lsub_le
  given: {ι} (f : ι -> Ordinal)
  statement: cof (lsub.{u, u} f) <= #ι
  proof: cof_iSup_add_one_le f

@[deprecated cof_lift_iSup_add_one_le (since := "2026-03-22")]

中文:
定理 cof_lsub_le
  条件: {ι} (f : ι -> 序数)
  结论: cof (lsub.{u, u} f) <= #ι
  证明: cof_iSup_add_one_le f

@[deprecated cof_lift_iSup_add_one_le (since := "2026-03-22")]

Depends on / 依赖: cof_iSup_add_one_le
-/
theorem cof_lsub_le {ι} (f : ι -> Ordinal) : cof (lsub.{u, u} f) <= #ι :=
  cof_iSup_add_one_le f

@[deprecated cof_lift_iSup_add_one_le (since := "2026-03-22")]
/--
theorem `cof_lsub_le_lift` / 定理 `cof_lsub_le_lift`

English:
theorem cof_lsub_le_lift
  given: {ι} (f : ι -> Ordinal)
  proof: by
  rw [← lift_id'.{u} (lsub f)]; rw [← Cardinal.lift_umax.{u]; rw [v}]
  exact cof_lift_iSup_add_one_le _

@[deprecated le_cof_iff (since := "2026-03-21")]

中文:
定理 cof_lsub_le_lift
  条件: {ι} (f : ι -> 序数)
  证明: by
  rw [← lift_id'.{u} (lsub f)]; rw [← Cardinal.lift_umax.{u]; rw [v}]
  exact cof_lift_iSup_add_one_le _

@[deprecated le_cof_iff (since := "2026-03-21")]

Depends on / 依赖: Cardinal, Cardinal.lift_umax, cof_lift_iSup_add_one_le, lift_id, lift_umax
-/
theorem cof_lsub_le_lift {ι} (f : ι -> Ordinal) :
    cof (lsub.{u, v} f) <= Cardinal.lift.{v, u} #ι := by
  rw [← lift_id'.{u} (lsub f)]; rw [← Cardinal.lift_umax.{u]; rw [v}]
  exact cof_lift_iSup_add_one_le _

@[deprecated le_cof_iff (since := "2026-03-21")]
/--
theorem `le_cof_iff_lsub` / 定理 `le_cof_iff_lsub`

English:
theorem le_cof_iff_lsub
  given: {o : Ordinal} {a : Cardinal}
  proof: by
  rw [cof_eq_sInf_lsub]
  exact
    (le_csInf_iff'' (cof_lsub_def_nonempty o)).trans
      ⟨fun H ι f hf => H _ ⟨ι, f, hf, rfl⟩, fun H b ⟨ι, f, hf, hb⟩ => by
        rw [← hb]
        exact H _ hf⟩

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 le_cof_iff_lsub
  条件: {o : 序数} {a : 基数}
  证明: by
  rw [cof_eq_sInf_lsub]
  exact
    (le_csInf_iff'' (cof_lsub_def_nonempty o)).trans
      ⟨fun H ι f hf => H _ ⟨ι, f, hf, rfl⟩, fun H b ⟨ι, f, hf, hb⟩ => by
        rw [← hb]
        exact H _ hf⟩

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: cof_eq_sInf_lsub, cof_lsub_def_nonempty, le_csInf_iff
-/
theorem le_cof_iff_lsub {o : Ordinal} {a : Cardinal} :
    a <= cof o ↔ forall {ι} (f : ι -> Ordinal), lsub.{u, u} f = o -> a <= #ι := by
  rw [cof_eq_sInf_lsub]
  exact
    (le_csInf_iff'' (cof_lsub_def_nonempty o)).trans
      ⟨fun H ι f hf => H _ ⟨ι, f, hf, rfl⟩, fun H b ⟨ι, f, hf, hb⟩ => by
        rw [← hb]
        exact H _ hf⟩

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `lsub_lt_ord_lift` / 定理 `lsub_lt_ord_lift`

English:
theorem lsub_lt_ord_lift
  statement: {ι} {f : ι -> Ordinal} {c : Ordinal}
  proof: by
  apply lift_iSup_add_one_lt_of_lt_cof _ hf
  rwa [Cardinal.lift_umax, c.lift_id']

@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 lsub_lt_ord_lift
  结论: {ι} {f : ι -> 序数} {c : 序数}
  证明: by
  apply lift_iSup_add_one_lt_of_lt_cof _ hf
  rwa [Cardinal.lift_umax, c.lift_id']

@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: Cardinal, Cardinal.lift_umax, c.lift_id, lift_iSup_add_one_lt_of_lt_cof, lift_id, lift_umax
-/
theorem lsub_lt_ord_lift {ι} {f : ι -> Ordinal} {c : Ordinal}
    (hι : Cardinal.lift.{v, u} #ι < c.cof)
    (hf : forall i, f i < c) : lsub.{u, v} f < c := by
  apply lift_iSup_add_one_lt_of_lt_cof _ hf
  rwa [Cardinal.lift_umax, c.lift_id']

@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `lsub_lt_ord` / 定理 `lsub_lt_ord`

English:
theorem lsub_lt_ord
  given: {ι} {f : ι -> Ordinal} {c : Ordinal} (hι : #ι < c.cof)
  proof: iSup_add_one_lt_of_lt_cof hι

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 lsub_lt_ord
  条件: {ι} {f : ι -> 序数} {c : 序数} (hι : #ι < c.cof)
  证明: iSup_add_one_lt_of_lt_cof hι

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: iSup_add_one_lt_of_lt_cof
-/
theorem lsub_lt_ord {ι} {f : ι -> Ordinal} {c : Ordinal} (hι : #ι < c.cof) :
    (forall i, f i < c) -> lsub.{u, u} f < c :=
  iSup_add_one_lt_of_lt_cof hι

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `cof_iSup_le_lift` / 定理 `cof_iSup_le_lift`

English:
theorem cof_iSup_le_lift
  given: {ι} {f : ι -> Ordinal} (H : forall i, f i < iSup f)
  proof: by
  by_contra! hf
  apply (lift_iSup_lt_of_lt_cof _ H).false
  rwa [Cardinal.lift_umax, lift_id']

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 cof_iSup_le_lift
  条件: {ι} {f : ι -> 序数} (H : 对任意 i, f i < iSup f)
  证明: by
  by_contra! hf
  apply (lift_iSup_lt_of_lt_cof _ H).false
  rwa [Cardinal.lift_umax, lift_id']

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: Cardinal, Cardinal.lift_umax, lift_iSup_lt_of_lt_cof, lift_id, lift_umax
-/
theorem cof_iSup_le_lift {ι} {f : ι -> Ordinal} (H : forall i, f i < iSup f) :
    cof (iSup f) <= Cardinal.lift.{v, u} #ι := by
  by_contra! hf
  apply (lift_iSup_lt_of_lt_cof _ H).false
  rwa [Cardinal.lift_umax, lift_id']

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `cof_iSup_le` / 定理 `cof_iSup_le`

English:
theorem cof_iSup_le
  given: {ι} {f : ι -> Ordinal} (H : forall i, f i < iSup f)
  proof: by
  by_contra! hf
  exact (iSup_lt_of_lt_cof hf H).false

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 cof_iSup_le
  条件: {ι} {f : ι -> 序数} (H : 对任意 i, f i < iSup f)
  证明: by
  by_contra! hf
  exact (iSup_lt_of_lt_cof hf H).false

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: iSup_lt_of_lt_cof
-/
theorem cof_iSup_le {ι} {f : ι -> Ordinal} (H : forall i, f i < iSup f) :
    cof (iSup f) <= #ι := by
  by_contra! hf
  exact (iSup_lt_of_lt_cof hf H).false

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `iSup_lt_ord_lift` / 定理 `iSup_lt_ord_lift`

English:
theorem iSup_lt_ord_lift
  statement: {ι} {f : ι -> Ordinal} {c : Ordinal} (hι : Cardinal.lift.{v, u} #ι < c.cof)
  proof: by
  apply lift_iSup_lt_of_lt_cof _ hf
  rwa [Cardinal.lift_umax, lift_id']

@[deprecated (since := "2026-03-22")]
alias iSup_lt_ord := iSup_lt_of_lt_cof

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 iSup_lt_ord_lift
  结论: {ι} {f : ι -> 序数} {c : 序数} (hι : 基数.lift.{v, u} #ι < c.cof)
  证明: by
  apply lift_iSup_lt_of_lt_cof _ hf
  rwa [Cardinal.lift_umax, lift_id']

@[deprecated (since := "2026-03-22")]
alias iSup_lt_ord := iSup_lt_of_lt_cof

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: Cardinal, Cardinal.lift_umax, lift_iSup_lt_of_lt_cof, lift_id, lift_umax
-/
theorem iSup_lt_ord_lift {ι} {f : ι -> Ordinal} {c : Ordinal} (hι : Cardinal.lift.{v, u} #ι < c.cof)
    (hf : forall i, f i < c) : iSup f < c := by
  apply lift_iSup_lt_of_lt_cof _ hf
  rwa [Cardinal.lift_umax, lift_id']

@[deprecated (since := "2026-03-22")]
alias iSup_lt_ord := iSup_lt_of_lt_cof

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `iSup_lt_lift` / 定理 `iSup_lt_lift`

English:
theorem iSup_lt_lift
  statement: {ι} {f : ι -> Cardinal} {c : Cardinal}
  proof: by
  apply lift_iSup_lt_of_lt_cof_ord _ hf
  rwa [Cardinal.lift_umax, c.lift_id']

@[deprecated (since := "2026-03-22")]
alias iSup_lt := Cardinal.iSup_lt_of_lt_cof_ord

中文:
定理 iSup_lt_lift
  结论: {ι} {f : ι -> 基数} {c : 基数}
  证明: by
  apply lift_iSup_lt_of_lt_cof_ord _ hf
  rwa [Cardinal.lift_umax, c.lift_id']

@[deprecated (since := "2026-03-22")]
alias iSup_lt := Cardinal.iSup_lt_of_lt_cof_ord

Depends on / 依赖: Cardinal, Cardinal.lift_umax, c.lift_id, lift_iSup_lt_of_lt_cof_ord, lift_id, lift_umax
-/
theorem iSup_lt_lift {ι} {f : ι -> Cardinal} {c : Cardinal}
    (hι : Cardinal.lift.{v, u} #ι < c.ord.cof)
    (hf : forall i, f i < c) : iSup f < c := by
  apply lift_iSup_lt_of_lt_cof_ord _ hf
  rwa [Cardinal.lift_umax, c.lift_id']

@[deprecated (since := "2026-03-22")]
alias iSup_lt := Cardinal.iSup_lt_of_lt_cof_ord

/--
theorem `nfpFamily_lt_ord_lift` / 定理 `nfpFamily_lt_ord_lift`

English:
theorem nfpFamily_lt_ord_lift
  statement: {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : ℵ₀ < cof c)
  proof: by
  refine lift_iSup_lt_of_lt_cof ?_ (fun l => ?_)
  · rw [Cardinal.lift_umax, c.lift_id']
    apply (Cardinal.lift_le.2 (mk_list_le_max _)).trans_lt
    rw [Cardinal.lift_max]
    apply max_lt <;> simpa
  · induction l with
    | nil => exact ha
    | cons i l H => exact hf _ _ H

中文:
定理 nfpFamily_lt_ord_lift
  结论: {ι} {f : ι -> 序数 -> 序数} {c} (hc : ℵ₀ < cof c)
  证明: by
  refine lift_iSup_lt_of_lt_cof ?_ (fun l => ?_)
  · rw [Cardinal.lift_umax, c.lift_id']
    apply (Cardinal.lift_le.2 (mk_list_le_max _)).trans_lt
    rw [Cardinal.lift_max]
    apply max_lt <;> simpa
  · induction l with
    | nil => exact ha
    | cons i l H => exact hf _ _ H

Depends on / 依赖: Cardinal, Cardinal.lift_le, Cardinal.lift_max, Cardinal.lift_umax, c.lift_id, lift_iSup_lt_of_lt_cof, lift_id, lift_le, lift_max, lift_umax, max_lt, mk_list_le_max, trans_lt
-/
theorem nfpFamily_lt_ord_lift {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : ℵ₀ < cof c)
    (hc' : Cardinal.lift.{v, u} #ι < cof c) (hf : forall (i), forall b < c, f i b < c) {a} (ha : a < c) :
    nfpFamily f a < c := by
  refine lift_iSup_lt_of_lt_cof ?_ (fun l => ?_)
  · rw [Cardinal.lift_umax, c.lift_id']
    apply (Cardinal.lift_le.2 (mk_list_le_max _)).trans_lt
    rw [Cardinal.lift_max]
    apply max_lt <;> simpa
  · induction l with
    | nil => exact ha
    | cons i l H => exact hf _ _ H

/--
theorem `nfpFamily_lt_ord` / 定理 `nfpFamily_lt_ord`

English:
theorem nfpFamily_lt_ord
  statement: {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : ℵ₀ < cof c) (hc' : #ι < cof c)
  proof: nfpFamily_lt_ord_lift hc (by rwa [(#ι).lift_id]) hf

中文:
定理 nfpFamily_lt_ord
  结论: {ι} {f : ι -> 序数 -> 序数} {c} (hc : ℵ₀ < cof c) (hc' : #ι < cof c)
  证明: nfpFamily_lt_ord_lift hc (by rwa [(#ι).lift_id]) hf

Depends on / 依赖: lift_id, nfpFamily_lt_ord_lift
-/
theorem nfpFamily_lt_ord {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : ℵ₀ < cof c) (hc' : #ι < cof c)
    (hf : forall (i), forall b < c, f i b < c) {a} : a < c -> nfpFamily.{u, u} f a < c :=
  nfpFamily_lt_ord_lift hc (by rwa [(#ι).lift_id]) hf

/--
theorem `nfp_lt_ord` / 定理 `nfp_lt_ord`

English:
theorem nfp_lt_ord
  given: {f : Ordinal -> Ordinal} {c} (hc : ℵ₀ < cof c) (hf : forall i < c, f i < c) {a}
  proof: nfpFamily_lt_ord_lift hc (by simpa using Cardinal.one_lt_aleph0.trans hc) fun _ => hf

@[deprecated exists_lsub_cof (since := "2026-03-21")]

中文:
定理 nfp_lt_ord
  条件: {f : 序数 -> 序数} {c} (hc : ℵ₀ < cof c) (hf : 对任意 i < c, f i < c) {a}
  证明: nfpFamily_lt_ord_lift hc (by simpa using Cardinal.one_lt_aleph0.trans hc) fun _ => hf

@[deprecated exists_lsub_cof (since := "2026-03-21")]

Depends on / 依赖: Cardinal, Cardinal.one_lt_aleph0.trans, nfpFamily_lt_ord_lift, one_lt_aleph0
-/
theorem nfp_lt_ord {f : Ordinal -> Ordinal} {c} (hc : ℵ₀ < cof c) (hf : forall i < c, f i < c) {a} :
    a < c -> nfp f a < c :=
  nfpFamily_lt_ord_lift hc (by simpa using Cardinal.one_lt_aleph0.trans hc) fun _ => hf

@[deprecated exists_lsub_cof (since := "2026-03-21")]
/--
theorem `exists_blsub_cof` / 定理 `exists_blsub_cof`

English:
theorem exists_blsub_cof
  given: (o : Ordinal)
  proof: by
  rcases exists_lsub_cof o with ⟨ι, f, hf, hι⟩
  rcases Cardinal.exists_ord_eq ι with ⟨r, hr, hι'⟩
  rw [← @blsub_eq_lsub' ι r hr] at hf
  rw [← hι]; rw [hι']
  exact ⟨_, hf⟩

@[deprecated le_cof_iff (since := "2026-03-21")]

中文:
定理 存在_blsub_cof
  条件: (o : 序数)
  证明: by
  rcases exists_lsub_cof o with ⟨ι, f, hf, hι⟩
  rcases Cardinal.exists_ord_eq ι with ⟨r, hr, hι'⟩
  rw [← @blsub_eq_lsub' ι r hr] at hf
  rw [← hι]; rw [hι']
  exact ⟨_, hf⟩

@[deprecated le_cof_iff (since := "2026-03-21")]

Depends on / 依赖: Cardinal, Cardinal.exists_ord_eq, blsub_eq_lsub, exists_lsub_cof, exists_ord_eq
-/
theorem exists_blsub_cof (o : Ordinal) :
    exists f : forall a < (cof o).ord, Ordinal, blsub.{u, u} _ f = o := by
  rcases exists_lsub_cof o with ⟨ι, f, hf, hι⟩
  rcases Cardinal.exists_ord_eq ι with ⟨r, hr, hι'⟩
  rw [← @blsub_eq_lsub' ι r hr] at hf
  rw [← hι]; rw [hι']
  exact ⟨_, hf⟩

@[deprecated le_cof_iff (since := "2026-03-21")]
/--
theorem `le_cof_iff_blsub` / 定理 `le_cof_iff_blsub`

English:
theorem le_cof_iff_blsub
  given: {b : Ordinal} {a : Cardinal}
  proof: le_cof_iff_lsub.trans
    ⟨fun H o f hf => by simpa using H _ hf, fun H ι f hf => by
      rcases Cardinal.exists_ord_eq ι with ⟨r, hr, hι'⟩
      rw [← @blsub_eq_lsub' ι r hr] at hf
      simpa using H _ hf⟩

@[deprecated cof_lift_iSup_add_one_le (since := "2026-03-22")]

中文:
定理 le_cof_iff_blsub
  条件: {b : 序数} {a : 基数}
  证明: le_cof_iff_lsub.trans
    ⟨fun H o f hf => by simpa using H _ hf, fun H ι f hf => by
      rcases Cardinal.exists_ord_eq ι with ⟨r, hr, hι'⟩
      rw [← @blsub_eq_lsub' ι r hr] at hf
      simpa using H _ hf⟩

@[deprecated cof_lift_iSup_add_one_le (since := "2026-03-22")]

Depends on / 依赖: Cardinal, Cardinal.exists_ord_eq, blsub_eq_lsub, exists_ord_eq, le_cof_iff_lsub, le_cof_iff_lsub.trans
-/
theorem le_cof_iff_blsub {b : Ordinal} {a : Cardinal} :
    a <= cof b ↔ forall {o} (f : forall a < o, Ordinal), blsub.{u, u} o f = b -> a <= o.card :=
  le_cof_iff_lsub.trans
    ⟨fun H o f hf => by simpa using H _ hf, fun H ι f hf => by
      rcases Cardinal.exists_ord_eq ι with ⟨r, hr, hι'⟩
      rw [← @blsub_eq_lsub' ι r hr] at hf
      simpa using H _ hf⟩

@[deprecated cof_lift_iSup_add_one_le (since := "2026-03-22")]
/--
theorem `cof_blsub_le_lift` / 定理 `cof_blsub_le_lift`

English:
theorem cof_blsub_le_lift
  given: {o} (f : forall a < o, Ordinal)
  proof: by
  rw [← mk_toType o]
  exact cof_lsub_le_lift _

@[deprecated cof_iSup_add_one_le (since := "2026-03-22")]

中文:
定理 cof_blsub_le_lift
  条件: {o} (f : 对任意 a < o, 序数)
  证明: by
  rw [← mk_toType o]
  exact cof_lsub_le_lift _

@[deprecated cof_iSup_add_one_le (since := "2026-03-22")]

Depends on / 依赖: cof_lsub_le_lift, mk_toType
-/
theorem cof_blsub_le_lift {o} (f : forall a < o, Ordinal) :
    cof (blsub.{u, v} o f) <= Cardinal.lift.{v, u} o.card := by
  rw [← mk_toType o]
  exact cof_lsub_le_lift _

@[deprecated cof_iSup_add_one_le (since := "2026-03-22")]
/--
theorem `cof_blsub_le` / 定理 `cof_blsub_le`

English:
theorem cof_blsub_le
  given: {o} (f : forall a < o, Ordinal)
  statement: cof (blsub.{u, u} o f) <= o.card
  proof: by
  rw [← o.card.lift_id]
  exact cof_blsub_le_lift f

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 cof_blsub_le
  条件: {o} (f : 对任意 a < o, 序数)
  结论: cof (blsub.{u, u} o f) <= o.card
  证明: by
  rw [← o.card.lift_id]
  exact cof_blsub_le_lift f

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: cof_blsub_le_lift, lift_id, o.card.lift_id
-/
theorem cof_blsub_le {o} (f : forall a < o, Ordinal) : cof (blsub.{u, u} o f) <= o.card := by
  rw [← o.card.lift_id]
  exact cof_blsub_le_lift f

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `blsub_lt_ord_lift` / 定理 `blsub_lt_ord_lift`

English:
theorem blsub_lt_ord_lift
  statement: {o : Ordinal.{u}} {f : forall a < o, Ordinal} {c : Ordinal}
  proof: lt_of_le_of_ne (blsub_le hf) fun h =>
    ho.not_ge (by simpa [← iSup_ord, hf, h] using cof_blsub_le_lift.{u, v} f)

@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 blsub_lt_ord_lift
  结论: {o : 序数.{u}} {f : 对任意 a < o, 序数} {c : 序数}
  证明: lt_of_le_of_ne (blsub_le hf) fun h =>
    ho.not_ge (by simpa [← iSup_ord, hf, h] using cof_blsub_le_lift.{u, v} f)

@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: blsub_le, cof_blsub_le_lift, ho.not_ge, iSup_ord, lt_of_le_of_ne, not_ge
-/
theorem blsub_lt_ord_lift {o : Ordinal.{u}} {f : forall a < o, Ordinal} {c : Ordinal}
    (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf : forall i hi, f i hi < c) : blsub.{u, v} o f < c :=
  lt_of_le_of_ne (blsub_le hf) fun h =>
    ho.not_ge (by simpa [← iSup_ord, hf, h] using cof_blsub_le_lift.{u, v} f)

@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `blsub_lt_ord` / 定理 `blsub_lt_ord`

English:
theorem blsub_lt_ord
  statement: {o : Ordinal} {f : forall a < o, Ordinal} {c : Ordinal} (ho : o.card < c.cof)
  proof: blsub_lt_ord_lift (by rwa [o.card.lift_id]) hf

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 blsub_lt_ord
  结论: {o : 序数} {f : 对任意 a < o, 序数} {c : 序数} (ho : o.card < c.cof)
  证明: blsub_lt_ord_lift (by rwa [o.card.lift_id]) hf

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: blsub_lt_ord_lift, lift_id, o.card.lift_id
-/
theorem blsub_lt_ord {o : Ordinal} {f : forall a < o, Ordinal} {c : Ordinal} (ho : o.card < c.cof)
    (hf : forall i hi, f i hi < c) : blsub.{u, u} o f < c :=
  blsub_lt_ord_lift (by rwa [o.card.lift_id]) hf

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `cof_bsup_le_lift` / 定理 `cof_bsup_le_lift`

English:
theorem cof_bsup_le_lift
  given: {o : Ordinal} {f : forall a < o, Ordinal} (H : forall i h, f i h < bsup.{u, v} o f)
  proof: by
  rw [← bsup_eq_blsub_iff_lt_bsup.{u]; rw [v}] at H
  rw [H]
  exact cof_blsub_le_lift.{u, v} f

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 cof_bsup_le_lift
  条件: {o : 序数} {f : 对任意 a < o, 序数} (H : 对任意 i h, f i h < bsup.{u, v} o f)
  证明: by
  rw [← bsup_eq_blsub_iff_lt_bsup.{u]; rw [v}] at H
  rw [H]
  exact cof_blsub_le_lift.{u, v} f

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: bsup_eq_blsub_iff_lt_bsup, cof_blsub_le_lift
-/
theorem cof_bsup_le_lift {o : Ordinal} {f : forall a < o, Ordinal} (H : forall i h, f i h < bsup.{u, v} o f) :
    cof (bsup.{u, v} o f) <= Cardinal.lift.{v, u} o.card := by
  rw [← bsup_eq_blsub_iff_lt_bsup.{u]; rw [v}] at H
  rw [H]
  exact cof_blsub_le_lift.{u, v} f

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `cof_bsup_le` / 定理 `cof_bsup_le`

English:
theorem cof_bsup_le
  given: {o : Ordinal} {f : forall a < o, Ordinal}
  proof: by
  rw [← o.card.lift_id]
  exact cof_bsup_le_lift

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 cof_bsup_le
  条件: {o : 序数} {f : 对任意 a < o, 序数}
  证明: by
  rw [← o.card.lift_id]
  exact cof_bsup_le_lift

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: cof_bsup_le_lift, lift_id, o.card.lift_id
-/
theorem cof_bsup_le {o : Ordinal} {f : forall a < o, Ordinal} :
    (forall i h, f i h < bsup.{u, u} o f) -> cof (bsup.{u, u} o f) <= o.card := by
  rw [← o.card.lift_id]
  exact cof_bsup_le_lift

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `bsup_lt_ord_lift` / 定理 `bsup_lt_ord_lift`

English:
theorem bsup_lt_ord_lift
  statement: {o : Ordinal} {f : forall a < o, Ordinal} {c : Ordinal}
  proof: (bsup_le_blsub f).trans_lt (blsub_lt_ord_lift ho hf)

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 bsup_lt_ord_lift
  结论: {o : 序数} {f : 对任意 a < o, 序数} {c : 序数}
  证明: (bsup_le_blsub f).trans_lt (blsub_lt_ord_lift ho hf)

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: blsub_lt_ord_lift, bsup_le_blsub, trans_lt
-/
theorem bsup_lt_ord_lift {o : Ordinal} {f : forall a < o, Ordinal} {c : Ordinal}
    (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf : forall i hi, f i hi < c) : bsup.{u, v} o f < c :=
  (bsup_le_blsub f).trans_lt (blsub_lt_ord_lift ho hf)

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `bsup_lt_ord` / 定理 `bsup_lt_ord`

English:
theorem bsup_lt_ord
  given: {o : Ordinal} {f : forall a < o, Ordinal} {c : Ordinal} (ho : o.card < c.cof)
  proof: bsup_lt_ord_lift (by rwa [o.card.lift_id])

中文:
定理 bsup_lt_ord
  条件: {o : 序数} {f : 对任意 a < o, 序数} {c : 序数} (ho : o.card < c.cof)
  证明: bsup_lt_ord_lift (by rwa [o.card.lift_id])

Depends on / 依赖: bsup_lt_ord_lift, lift_id, o.card.lift_id
-/
theorem bsup_lt_ord {o : Ordinal} {f : forall a < o, Ordinal} {c : Ordinal} (ho : o.card < c.cof) :
    (forall i hi, f i hi < c) -> bsup.{u, u} o f < c :=
  bsup_lt_ord_lift (by rwa [o.card.lift_id])

/-! ### Cofinality arithmetic -/

@[simp]
/--
theorem `cof_add` / 定理 `cof_add`

English:
theorem cof_add
  given: (a : Ordinal) {b : Ordinal} (hb : b != 0)
  statement: cof (a + b) = cof b
  proof: by
  rcases zero_or_succ_or_isSuccLimit b with (rfl | ⟨c, rfl⟩ | hb)
  · contradiction
  · rw [succ_eq_add_one, ← add_assoc, cof_add_one, cof_add_one]
  · exact cof_map_of_isNormal (isNormal_add_right a) hb

@[simp]

中文:
定理 cof_add
  条件: (a : 序数) {b : 序数} (hb : b != 0)
  结论: cof (a + b) = cof b
  证明: by
  rcases zero_or_succ_or_isSuccLimit b with (rfl | ⟨c, rfl⟩ | hb)
  · contradiction
  · rw [succ_eq_add_one, ← add_assoc, cof_add_one, cof_add_one]
  · exact cof_map_of_isNormal (isNormal_add_right a) hb

@[simp]

Depends on / 依赖: add_assoc, cof_add_one, cof_map_of_isNormal, isNormal_add_right, succ_eq_add_one, zero_or_succ_or_isSuccLimit
-/
theorem cof_add (a : Ordinal) {b : Ordinal} (hb : b != 0) : cof (a + b) = cof b := by
  rcases zero_or_succ_or_isSuccLimit b with (rfl | ⟨c, rfl⟩ | hb)
  · contradiction
  · rw [succ_eq_add_one, ← add_assoc, cof_add_one, cof_add_one]
  · exact cof_map_of_isNormal (isNormal_add_right a) hb

@[simp]
/--
theorem `cof_mul` / 定理 `cof_mul`

English:
theorem cof_mul
  given: {a b : Ordinal} (ha : a != 0) (hb : IsSuccPrelimit b)
  statement: cof (a * b) = cof b
  proof: by
  by_cases hb' : IsMin b
  · simp [hb'.eq_bot]
  · exact cof_map_of_isNormal (isNormal_mul_right ha.pos) ⟨hb', hb⟩

@[simp]

中文:
定理 cof_mul
  条件: {a b : 序数} (ha : a != 0) (hb : IsSuccPrelimit b)
  结论: cof (a * b) = cof b
  证明: by
  by_cases hb' : IsMin b
  · simp [hb'.eq_bot]
  · exact cof_map_of_isNormal (isNormal_mul_right ha.pos) ⟨hb', hb⟩

@[simp]

Depends on / 依赖: cof_map_of_isNormal, eq_bot, ha.pos, isNormal_mul_right
-/
theorem cof_mul {a b : Ordinal} (ha : a != 0) (hb : IsSuccPrelimit b) : cof (a * b) = cof b := by
  by_cases hb' : IsMin b
  · simp [hb'.eq_bot]
  · exact cof_map_of_isNormal (isNormal_mul_right ha.pos) ⟨hb', hb⟩

@[simp]
/--
theorem `cof_preOmega` / 定理 `cof_preOmega`

English:
theorem cof_preOmega
  given: {o : Ordinal} (ho : IsSuccPrelimit o)
  statement: (preOmega o).cof = o.cof
  proof: by
  by_cases h : IsMin o
  · simp [h.eq_bot]
  · exact cof_map_of_isNormal isNormal_preOmega ⟨h, ho⟩

@[simp]

中文:
定理 cof_preOmega
  条件: {o : 序数} (ho : IsSuccPrelimit o)
  结论: (preOmega o).cof = o.cof
  证明: by
  by_cases h : IsMin o
  · simp [h.eq_bot]
  · exact cof_map_of_isNormal isNormal_preOmega ⟨h, ho⟩

@[simp]

Depends on / 依赖: cof_map_of_isNormal, eq_bot, h.eq_bot, isNormal_preOmega
-/
theorem cof_preOmega {o : Ordinal} (ho : IsSuccPrelimit o) : (preOmega o).cof = o.cof := by
  by_cases h : IsMin o
  · simp [h.eq_bot]
  · exact cof_map_of_isNormal isNormal_preOmega ⟨h, ho⟩

@[simp]
/--
theorem `cof_omega` / 定理 `cof_omega`

English:
theorem cof_omega
  given: {o : Ordinal} (ho : IsSuccLimit o)
  statement: (ω_ o).cof = o.cof
  proof: cof_map_of_isNormal isNormal_omega ho

@[deprecated Order.cof_eq (since := "2026-03-20")]

中文:
定理 cof_omega
  条件: {o : 序数} (ho : 是SuccLimit o)
  结论: (ω_ o).cof = o.cof
  证明: cof_map_of_isNormal isNormal_omega ho

@[deprecated Order.cof_eq (since := "2026-03-20")]

Depends on / 依赖: cof_map_of_isNormal, isNormal_omega
-/
theorem cof_omega {o : Ordinal} (ho : IsSuccLimit o) : (ω_ o).cof = o.cof :=
  cof_map_of_isNormal isNormal_omega ho

@[deprecated Order.cof_eq (since := "2026-03-20")]
/--
theorem `cof_eq'` / 定理 `cof_eq'`

English:
theorem cof_eq'
  given: (r : α -> α -> Prop) [H : IsWellOrder α r] (h : IsSuccLimit (type r))
  proof: by
  classical
  let := linearOrderOfSTO r
  have : WellFoundedLT α := H.toIsWellFounded
  have : NoMaxOrder α := isSuccPrelimit_type_lt_iff.1 h.isSuccPrelimit
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  refine ⟨s, ?_, hs'⟩
  rwa [← not_bddAbove_iff_isCofinal, not_bddAbove_iff] at hs

@[simp]

中文:
定理 cof_eq'
  条件: (r : α -> α -> 命题) [H : 是良序 α r] (h : 是SuccLimit (type r))
  证明: by
  classical
  let := linearOrderOfSTO r
  have : WellFoundedLT α := H.toIsWellFounded
  have : NoMaxOrder α := isSuccPrelimit_type_lt_iff.1 h.isSuccPrelimit
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  refine ⟨s, ?_, hs'⟩
  rwa [← not_bddAbove_iff_isCofinal, not_bddAbove_iff] at hs

@[simp]

Depends on / 依赖: H.toIsWellFounded, NoMaxOrder, WellFoundedLT, classical, exists_cof_eq, h.isSuccPrelimit, isSuccPrelimit, isSuccPrelimit_type_lt_iff, linearOrderOfSTO, not_bddAbove_iff, not_bddAbove_iff_isCofinal, toIsWellFounded
-/
theorem cof_eq' (r : α -> α -> Prop) [H : IsWellOrder α r] (h : IsSuccLimit (type r)) :
    exists S : Set α, (forall a, exists b in S, r a b) ∧ #S = cof (type r) := by
  classical
  let := linearOrderOfSTO r
  have : WellFoundedLT α := H.toIsWellFounded
  have : NoMaxOrder α := isSuccPrelimit_type_lt_iff.1 h.isSuccPrelimit
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  refine ⟨s, ?_, hs'⟩
  rwa [← not_bddAbove_iff_isCofinal, not_bddAbove_iff] at hs

@[simp]
/--
theorem `cof_univ` / 定理 `cof_univ`

English:
theorem cof_univ
  statement: cof univ.{u, v} = Cardinal.univ.{u, v}
  proof: by
  rw [univ]; rw [← lift_cof]; rw [cof_type]; rw [cof_ordinal]; rw [Cardinal.lift_univ]; rw [Cardinal.univ_umax.{u]; rw [v}]

中文:
定理 cof_univ
  结论: cof univ.{u, v} = 基数.univ.{u, v}
  证明: by
  rw [univ]; rw [← lift_cof]; rw [cof_type]; rw [cof_ordinal]; rw [Cardinal.lift_univ]; rw [Cardinal.univ_umax.{u]; rw [v}]

Depends on / 依赖: Cardinal, Cardinal.lift_univ, Cardinal.univ_umax, cof_ordinal, cof_type, lift_cof, lift_univ, univ_umax
-/
theorem cof_univ : cof univ.{u, v} = Cardinal.univ.{u, v} := by
  rw [univ]; rw [← lift_cof]; rw [cof_type]; rw [cof_ordinal]; rw [Cardinal.lift_univ]; rw [Cardinal.univ_umax.{u]; rw [v}]

end Ordinal

namespace Cardinal
open Ordinal


-- TODO: re-state this for a bundled well-order
/--
theorem `mk_bounded_subset` / 定理 `mk_bounded_subset`

English:
theorem mk_bounded_subset
  statement: {α : Type*} (h : IsStrongPrelimit #α) {r : α -> α -> Prop}
  proof: by
  rcases eq_or_ne #α 0 with (ha | ha)
  · rw [ha]
    have := mk_eq_zero_iff.1 ha
    rw [mk_eq_zero_iff]
    constructor
    rintro ⟨s, hs⟩
    exact (not_unbounded_iff s).2 hs (unbounded_of_isEmpty s)
  have h' : IsStrongLimit #α := ⟨ha, @h⟩
  have ha := h'.aleph0_le
  apply le_antisymm
  · hav

中文:
定理 mk_bounded_subset
  结论: {α : 类型} (h : IsStrongPrelimit #α) {r : α -> α -> 命题}
  证明: by
  rcases eq_or_ne #α 0 with (ha | ha)
  · rw [ha]
    have := mk_eq_zero_iff.1 ha
    rw [mk_eq_zero_iff]
    constructor
    rintro ⟨s, hs⟩
    exact (not_unbounded_iff s).2 hs (unbounded_of_isEmpty s)
  have h' : IsStrongLimit #α := ⟨ha, @h⟩
  have ha := h'.aleph0_le
  apply le_antisymm
  · hav

Depends on / 依赖: Bounded, IsStrongLimit, aleph0_le, coe_ofPred, eq_or_ne, le_antisymm, mk_eq_zero_iff, mk_iUnion_le_sum_mk, mk_iUnion_le_sum_mk.trans, mul_le_max_of_aleph0_le_left, not_unbounded_iff, ofPred_exists, sum_le_mk_mul_iSup, unbounded_of_isEmpty
-/
theorem mk_bounded_subset {α : Type*} (h : IsStrongPrelimit #α) {r : α -> α -> Prop}
    [IsWellOrder α r] (hr : (#α).ord = type r) : #{ s : Set α // Bounded r s } = #α := by
  rcases eq_or_ne #α 0 with (ha | ha)
  · rw [ha]
    have := mk_eq_zero_iff.1 ha
    rw [mk_eq_zero_iff]
    constructor
    rintro ⟨s, hs⟩
    exact (not_unbounded_iff s).2 hs (unbounded_of_isEmpty s)
  have h' : IsStrongLimit #α := ⟨ha, @h⟩
  have ha := h'.aleph0_le
  apply le_antisymm
  · have : { s : Set α | Bounded r s } = ⋃ i, 𝒫 { j | r j i } := ofPred_exists _
    rw [← coe_ofPred]; rw [this]
    refine mk_iUnion_le_sum_mk.trans ((sum_le_mk_mul_iSup (fun i => #(𝒫 { j | r j i }))).trans
      ((mul_le_max_of_aleph0_le_left ha).trans ?_))
    rw [max_eq_left]
    apply ciSup_le' _
    intro i
    rw [mk_powerset]
    exact (h (card_typein_lt _ hr)).le
  · refine @mk_le_of_injective α _ (fun x => Subtype.mk {x} ?_) ?_
    · apply bounded_singleton
      rw [← hr]
      apply isSuccLimit_ord ha
    · intro a b hab
      simpa [singleton_eq_singleton_iff] using hab

/--
theorem `mk_subset_mk_lt_cof` / 定理 `mk_subset_mk_lt_cof`

English:
theorem mk_subset_mk_lt_cof
  given: {α : Type*} (h : IsStrongPrelimit #α)
  proof: by
  rcases eq_or_ne #α 0 with (ha | ha)
  · simp [ha]
  have h' : IsStrongLimit #α := ⟨ha, @h⟩
  rcases exists_ord_eq α with ⟨r, wo, hr⟩
  classical
  let := linearOrderOfSTO r
  apply le_antisymm
  · conv_rhs => rw [← mk_bounded_subset h hr]
    apply mk_subtype_le_of_subset
    intro s hs
    rw 

中文:
定理 mk_subset_mk_lt_cof
  条件: {α : 类型} (h : IsStrongPrelimit #α)
  证明: by
  rcases eq_or_ne #α 0 with (ha | ha)
  · simp [ha]
  have h' : IsStrongLimit #α := ⟨ha, @h⟩
  rcases exists_ord_eq α with ⟨r, wo, hr⟩
  classical
  let := linearOrderOfSTO r
  apply le_antisymm
  · conv_rhs => rw [← mk_bounded_subset h hr]
    apply mk_subtype_le_of_subset
    intro s hs
    rw 

Depends on / 依赖: IsCofinal, IsStrongLimit, Subtype, Subtype.mk, classical, cof_le, contrapose, conv_rhs, eq_or_ne, exists_ord_eq, isSuccLimit_ord, le_antisymm, linearOrderOfSTO, mk_bounded_subset, mk_le_of_injective, mk_singleton, mk_subtype_le_of_subset, not_bounded_iff, not_lt, one_lt_cof_iff
-/
theorem mk_subset_mk_lt_cof {α : Type*} (h : IsStrongPrelimit #α) :
    #{ s : Set α // #s < cof (#α).ord } = #α := by
  rcases eq_or_ne #α 0 with (ha | ha)
  · simp [ha]
  have h' : IsStrongLimit #α := ⟨ha, @h⟩
  rcases exists_ord_eq α with ⟨r, wo, hr⟩
  classical
  let := linearOrderOfSTO r
  apply le_antisymm
  · conv_rhs => rw [← mk_bounded_subset h hr]
    apply mk_subtype_le_of_subset
    intro s hs
    rw [hr] at hs
    contrapose! hs
    rw [not_bounded_iff] at hs
    apply cof_le
    simp_rw [IsCofinal, ← not_lt]
    exact hs
  · refine @mk_le_of_injective α _ (fun x => Subtype.mk {x} ?_) ?_
    · rw [mk_singleton, one_lt_cof_iff]
      exact isSuccLimit_ord h'.aleph0_le
    · intro a b hab
      simpa [singleton_eq_singleton_iff] using hab

@[deprecated (since := "2026-02-25")]
alias unbounded_of_unbounded_sUnion := isCofinal_of_isCofinal_sUnion
@[deprecated (since := "2026-02-25")]
alias unbounded_of_unbounded_iUnion := isCofinal_of_isCofinal_iUnion


/--
theorem `lt_power_cof_ord` / 定理 `lt_power_cof_ord`

English:
theorem lt_power_cof_ord
  given: {c : Cardinal} (hc : ℵ₀ <= c)
  statement: c < c ^ c.ord.cof
  proof: by
  induction c using Cardinal.inductionOn with | mk α
  obtain ⟨_, _, hα⟩ := exists_ord_eq_type_lt α
  have : NoMaxOrder α := by
    rw [← isSuccPrelimit_type_lt_iff]; rw [← hα]
    exact (isSuccLimit_ord hc).isSuccPrelimit
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq α
  rw [hα]; rw [cof_type]; rw 

中文:
定理 lt_power_cof_ord
  条件: {c : 基数} (hc : ℵ₀ <= c)
  结论: c < c ^ c.ord.cof
  证明: by
  induction c using Cardinal.inductionOn with | mk α
  obtain ⟨_, _, hα⟩ := exists_ord_eq_type_lt α
  have : NoMaxOrder α := by
    rw [← isSuccPrelimit_type_lt_iff]; rw [← hα]
    exact (isSuccLimit_ord hc).isSuccPrelimit
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq α
  rw [hα]; rw [cof_type]; rw 

Depends on / 依赖: Cardinal, Cardinal.inductionOn, NoMaxOrder, Order.cof, card_ord, card_type, cof_type, exists_ord_cof_eq, exists_ord_eq_type_lt, inductionOn, isCofinal_iff_iUnion_Iio_eq_u, isSuccLimit_ord, isSuccPrelimit, isSuccPrelimit_type_lt_iff, mk_Iio_lt, mk_iUnion_le_sum_mk, mk_iUnion_le_sum_mk.trans, mk_univ, prod_const, sum_lt_prod
-/
theorem lt_power_cof_ord {c : Cardinal} (hc : ℵ₀ <= c) : c < c ^ c.ord.cof := by
  induction c using Cardinal.inductionOn with | mk α
  obtain ⟨_, _, hα⟩ := exists_ord_eq_type_lt α
  have : NoMaxOrder α := by
    rw [← isSuccPrelimit_type_lt_iff]; rw [← hα]
    exact (isSuccLimit_ord hc).isSuccPrelimit
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq α
  rw [hα]; rw [cof_type]; rw [← card_ord (Order.cof _)]; rw [← hs']; rw [card_type]; rw [← prod_const']
  refine (mk_iUnion_le_sum_mk.trans' ?_).trans_lt (sum_lt_prod _ _ fun i => mk_Iio_lt i.1 hα)
  rw [← mk_univ]; rw [← isCofinal_iff_iUnion_Iio_eq_univ.1 hs]; rw [iUnion_coe_set]

@[deprecated (since := "2026-03-30")]
alias lt_power_cof := lt_power_cof_ord

/--
theorem `lt_cof_ord_power` / 定理 `lt_cof_ord_power`

English:
theorem lt_cof_ord_power
  given: {a b : Cardinal} (ha : ℵ₀ <= a) (hb : 1 < b)
  statement: a < (b ^ a).ord.cof
  proof: by
  apply lt_imp_lt_of_le_imp_le (power_le_power_left <| power_ne_zero a hb.ne_bot)
  rw [← power_mul]; rw [mul_eq_self ha]
  exact lt_power_cof_ord (ha.trans <| (cantor' _ hb).le)

@[deprecated (since := "2026-03-30")]
alias lt_cof_power := lt_cof_ord_power

中文:
定理 lt_cof_ord_power
  条件: {a b : 基数} (ha : ℵ₀ <= a) (hb : 1 < b)
  结论: a < (b ^ a).ord.cof
  证明: by
  apply lt_imp_lt_of_le_imp_le (power_le_power_left <| power_ne_zero a hb.ne_bot)
  rw [← power_mul]; rw [mul_eq_self ha]
  exact lt_power_cof_ord (ha.trans <| (cantor' _ hb).le)

@[deprecated (since := "2026-03-30")]
alias lt_cof_power := lt_cof_ord_power

Depends on / 依赖: cantor, ha.trans, hb.ne_bot, lt_imp_lt_of_le_imp_le, lt_power_cof_ord, mul_eq_self, ne_bot, power_le_power_left, power_mul, power_ne_zero
-/
theorem lt_cof_ord_power {a b : Cardinal} (ha : ℵ₀ <= a) (hb : 1 < b) : a < (b ^ a).ord.cof := by
  apply lt_imp_lt_of_le_imp_le (power_le_power_left <| power_ne_zero a hb.ne_bot)
  rw [← power_mul]; rw [mul_eq_self ha]
  exact lt_power_cof_ord (ha.trans <| (cantor' _ hb).le)

@[deprecated (since := "2026-03-30")]
alias lt_cof_power := lt_cof_ord_power

end Cardinal
