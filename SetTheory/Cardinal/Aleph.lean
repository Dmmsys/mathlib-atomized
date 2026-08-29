/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.Monoid.Basic
public import Mathlib.SetTheory.Cardinal.Cofinality.Enum
public import Mathlib.SetTheory.Cardinal.ToNat
public import Mathlib.SetTheory.Cardinal.ENat
public import Mathlib.SetTheory.Ordinal.Enum
public import Mathlib.SetTheory.Ordinal.Univ

import Mathlib.SetTheory.Ordinal.Principal

/-!
# Omega, aleph, and beth functions

This file defines the `ω`, `ℵ`, and `ℶ` functions which enumerate certain kinds of ordinals and
cardinals. Each is provided in two variants: the standard versions which only take infinite values,
and "preliminary" versions which include finite values and are sometimes more convenient.

* The function `Ordinal.preOmega` enumerates the initial ordinals, i.e. the smallest ordinals with
  any given cardinality. Thus `preOmega n = n`, `preOmega ω = ω`, `preOmega (ω + 1) = ω₁`, etc.
  `Ordinal.omega` is the more standard function which skips over finite ordinals.
* The function `Cardinal.preAleph` is an order isomorphism between ordinals and cardinals. Thus
  `preAleph n = n`, `preAleph ω = ℵ₀`, `preAleph (ω + 1) = ℵ₁`, etc. `Cardinal.aleph` is the more
  standard function which skips over finite cardinals.
* The function `Cardinal.preBeth` is the unique normal function with `beth 0 = 0` and
  `beth (succ o) = 2 ^ beth o`. `Cardinal.beth` is the more standard function which skips over
  finite cardinals.

## Notation

The following notations are scoped to the `Ordinal` namespace.

- `ω_ o` is notation for `Ordinal.omega o`. `ω₁` is notation for `ω_ 1`.

The following notations are scoped to the `Cardinal` namespace.

- `ℵ_ o` is notation for `aleph o`. `ℵ₁` is notation for `ℵ_ 1`.
- `ℶ_ o` is notation for `beth o`. The value `ℶ_ 1` equals the continuum `𝔠`, which is defined in
  `Mathlib/SetTheory/Cardinal/Continuum.lean`.
-/

@[expose] public section

assert_not_exists Field Finsupp Module Cardinal.mul_eq_self

noncomputable section

open Function Set Cardinal Equiv Order Ordinal

universe u v w

/-! ### Omega ordinals -/

namespace Ordinal

/--
Definition of `IsInitial` / `IsInitial` 的定义

English:
definition IsInitial
  signature: (o : Ordinal)
  body: o.card.ord = o

中文:
定义 IsInitial
  签名: (o : 序数)
  定义体: o.card.ord = o

Depends on / 依赖: o.card.ord
-/
def IsInitial (o : Ordinal) : Prop :=
  o.card.ord = o

/--
theorem `IsInitial.ord_card` / 定理 `IsInitial.ord_card`

English:
theorem IsInitial.ord_card
  given: {o : Ordinal} (h : IsInitial o)
  statement: o.card.ord = o
  proof: h

中文:
定理 IsInitial.ord_card
  条件: {o : 序数} (h : IsInitial o)
  结论: o.card.ord = o
  证明: h
-/
theorem IsInitial.ord_card {o : Ordinal} (h : IsInitial o) : o.card.ord = o := h

/--
theorem `IsInitial.le_ord_iff_card_le` / 定理 `IsInitial.le_ord_iff_card_le`

English:
theorem IsInitial.le_ord_iff_card_le
  given: {o : Ordinal} (ho : o.IsInitial) (c : Cardinal)
  proof: by
  grw [← ord_le_ord, ho.ord_card]

中文:
定理 IsInitial.le_ord_iff_card_le
  条件: {o : 序数} (ho : o.IsInitial) (c : 基数)
  证明: by
  grw [← ord_le_ord, ho.ord_card]

Depends on / 依赖: ho.ord_card, ord_card, ord_le_ord
-/
theorem IsInitial.le_ord_iff_card_le {o : Ordinal} (ho : o.IsInitial) (c : Cardinal) :
    o <= c.ord ↔ o.card <= c := by
  grw [← ord_le_ord, ho.ord_card]

/--
theorem `IsInitial.card_le_card` / 定理 `IsInitial.card_le_card`

English:
theorem IsInitial.card_le_card
  given: {a b : Ordinal} (ha : IsInitial a)
  statement: a.card <= b.card ↔ a <= b
  proof: by
  refine ⟨fun h => ?_, Ordinal.card_le_card⟩
  rw [← ha.le_ord_iff_card_le] at h
  grw [h, ord_card_le]

中文:
定理 IsInitial.card_le_card
  条件: {a b : 序数} (ha : IsInitial a)
  结论: a.card <= b.card ↔ a <= b
  证明: by
  refine ⟨fun h => ?_, Ordinal.card_le_card⟩
  rw [← ha.le_ord_iff_card_le] at h
  grw [h, ord_card_le]

Depends on / 依赖: Ordinal, Ordinal.card_le_card, card_le_card, ha.le_ord_iff_card_le, le_ord_iff_card_le, ord_card_le
-/
theorem IsInitial.card_le_card {a b : Ordinal} (ha : IsInitial a) : a.card <= b.card ↔ a <= b := by
  refine ⟨fun h => ?_, Ordinal.card_le_card⟩
  rw [← ha.le_ord_iff_card_le] at h
  grw [h, ord_card_le]

/--
theorem `IsInitial.card_lt_card` / 定理 `IsInitial.card_lt_card`

English:
theorem IsInitial.card_lt_card
  given: {a b : Ordinal} (hb : IsInitial b)
  statement: a.card < b.card ↔ a < b
  proof: lt_iff_lt_of_le_iff_le hb.card_le_card

中文:
定理 IsInitial.card_lt_card
  条件: {a b : 序数} (hb : IsInitial b)
  结论: a.card < b.card ↔ a < b
  证明: lt_iff_lt_of_le_iff_le hb.card_le_card

Depends on / 依赖: card_le_card, hb.card_le_card, lt_iff_lt_of_le_iff_le
-/
theorem IsInitial.card_lt_card {a b : Ordinal} (hb : IsInitial b) : a.card < b.card ↔ a < b :=
  lt_iff_lt_of_le_iff_le hb.card_le_card

/--
theorem `isInitial_ord` / 定理 `isInitial_ord`

English:
theorem isInitial_ord
  given: (c : Cardinal)
  statement: IsInitial c.ord
  proof: by
  rw [IsInitial]; rw [card_ord]

@[simp]

中文:
定理 isInitial_ord
  条件: (c : 基数)
  结论: IsInitial c.ord
  证明: by
  rw [IsInitial]; rw [card_ord]

@[simp]

Depends on / 依赖: IsInitial, card_ord
-/
theorem isInitial_ord (c : Cardinal) : IsInitial c.ord := by
  rw [IsInitial]; rw [card_ord]

@[simp]
/--
theorem `isInitial_natCast` / 定理 `isInitial_natCast`

English:
theorem isInitial_natCast
  given: (n : Nat)
  statement: IsInitial n
  proof: by
  rw [IsInitial]; rw [card_nat]; rw [ord_natCast]

中文:
定理 isInitial_natCast
  条件: (n : 自然数)
  结论: IsInitial n
  证明: by
  rw [IsInitial]; rw [card_nat]; rw [ord_natCast]

Depends on / 依赖: IsInitial, card_nat, ord_natCast
-/
theorem isInitial_natCast (n : Nat) : IsInitial n := by
  rw [IsInitial]; rw [card_nat]; rw [ord_natCast]

/--
theorem `isInitial_zero` / 定理 `isInitial_zero`

English:
theorem isInitial_zero
  statement: IsInitial 0
  proof: by
  exact_mod_cast isInitial_natCast 0

中文:
定理 isInitial_zero
  结论: IsInitial 0
  证明: by
  exact_mod_cast isInitial_natCast 0

Depends on / 依赖: isInitial_natCast
-/
theorem isInitial_zero : IsInitial 0 := by
  exact_mod_cast isInitial_natCast 0

/--
theorem `isInitial_one` / 定理 `isInitial_one`

English:
theorem isInitial_one
  statement: IsInitial 1
  proof: by
  exact_mod_cast isInitial_natCast 1

中文:
定理 isInitial_one
  结论: IsInitial 1
  证明: by
  exact_mod_cast isInitial_natCast 1

Depends on / 依赖: isInitial_natCast
-/
theorem isInitial_one : IsInitial 1 := by
  exact_mod_cast isInitial_natCast 1

/--
theorem `isInitial_omega0` / 定理 `isInitial_omega0`

English:
theorem isInitial_omega0
  statement: IsInitial ω
  proof: by
  rw [IsInitial]; rw [card_omega0]; rw [ord_aleph0]

中文:
定理 isInitial_omega0
  结论: IsInitial ω
  证明: by
  rw [IsInitial]; rw [card_omega0]; rw [ord_aleph0]

Depends on / 依赖: IsInitial, card_omega0, ord_aleph0
-/
theorem isInitial_omega0 : IsInitial ω := by
  rw [IsInitial]; rw [card_omega0]; rw [ord_aleph0]

/--
theorem `isInitial_succ` / 定理 `isInitial_succ`

English:
theorem isInitial_succ
  given: {o : Ordinal}
  statement: IsInitial (succ o) ↔ o < ω
  proof: ⟨Function.mtr fun hwo => ne_of_lt by simp_all [ord_card_le],
  fun how => (Ordinal.lt_omega0.1 how).rec fun n h => h ▸ isInitial_natCast (n + 1)⟩

中文:
定理 isInitial_succ
  条件: {o : 序数}
  结论: IsInitial (succ o) ↔ o < ω
  证明: ⟨Function.mtr fun hwo => ne_of_lt by simp_all [ord_card_le],
  fun how => (Ordinal.lt_omega0.1 how).rec fun n h => h ▸ isInitial_natCast (n + 1)⟩

Depends on / 依赖: Function, Function.mtr, Ordinal, Ordinal.lt_omega0, isInitial_natCast, lt_omega0, ne_of_lt, ord_card_le
-/
theorem isInitial_succ {o : Ordinal} : IsInitial (succ o) ↔ o < ω :=
⟨Function.mtr fun hwo => ne_of_lt by simp_all [ord_card_le],
  fun how => (Ordinal.lt_omega0.1 how).rec fun n h => h ▸ isInitial_natCast (n + 1)⟩

/--
theorem `not_bddAbove_isInitial` / 定理 `not_bddAbove_isInitial`

English:
theorem not_bddAbove_isInitial
  statement: ¬ BddAbove {x | IsInitial x}
  proof: by
  rintro ⟨a, ha⟩
  have := ha (isInitial_ord (succ a.card))
  rw [ord_le] at this
  exact (lt_succ _).not_ge this

中文:
定理 not_bddAbove_isInitial
  结论: ¬ BddAbove {x | IsInitial x}
  证明: by
  rintro ⟨a, ha⟩
  have := ha (isInitial_ord (succ a.card))
  rw [ord_le] at this
  exact (lt_succ _).not_ge this

Depends on / 依赖: a.card, isInitial_ord, lt_succ, not_ge, ord_le
-/
theorem not_bddAbove_isInitial : ¬ BddAbove {x | IsInitial x} := by
  rintro ⟨a, ha⟩
  have := ha (isInitial_ord (succ a.card))
  rw [ord_le] at this
  exact (lt_succ _).not_ge this

/-- Initial ordinals are order-isomorphic to the cardinals. -/
@[simps!]
/--
Definition of `isInitialIso` / `isInitialIso` 的定义

English:
definition isInitialIso
  signature: : {x // IsInitial x} ≃o Cardinal where
  body: x.1.card
  invFun x := ⟨x.ord, isInitial_ord _⟩
  left_inv x := Subtype.ext x.2.ord_card
  right_inv x := card_ord x
  map_rel_iff' {a _} := a.2.card_le_card

中文:
定义 isInitialIso
  签名: : {x // IsInitial x} ≃o 基数 where
  定义体: x.1.card
  invFun x := ⟨x.ord, isInitial_ord _⟩
  left_inv x := Subtype.ext x.2.ord_card
  right_inv x := card_ord x
  map_rel_iff' {a _} := a.2.card_le_card
-/
def isInitialIso : {x // IsInitial x} ≃o Cardinal where
  toFun x := x.1.card
  invFun x := ⟨x.ord, isInitial_ord _⟩
  left_inv x := Subtype.ext x.2.ord_card
  right_inv x := card_ord x
  map_rel_iff' {a _} := a.2.card_le_card

/--
Definition of `preOmega` / `preOmega` 的定义

English:
definition preOmega
  signature: : Ordinal.{u} ↪o Ordinal.{u} where
  body: enumOrd {x | IsInitial x}
  inj' _ _ h := enumOrd_injective not_bddAbove_isInitial h
  map_rel_iff' := enumOrd_le_enumOrd not_bddAbove_isInitial

中文:
定义 preOmega
  签名: : 序数.{u} ↪o 序数.{u} where
  定义体: enumOrd {x | IsInitial x}
  inj' _ _ h := enumOrd_injective not_bddAbove_isInitial h
  map_rel_iff' := enumOrd_le_enumOrd not_bddAbove_isInitial

Depends on / 依赖: IsInitial, enumOrd
-/
def preOmega : Ordinal.{u} ↪o Ordinal.{u} where
  toFun := enumOrd {x | IsInitial x}
  inj' _ _ h := enumOrd_injective not_bddAbove_isInitial h
  map_rel_iff' := enumOrd_le_enumOrd not_bddAbove_isInitial

/--
theorem `coe_preOmega` / 定理 `coe_preOmega`

English:
theorem coe_preOmega
  statement: preOmega = enumOrd {x | IsInitial x}
  proof: rfl

中文:
定理 coe_preOmega
  结论: preOmega = enumOrd {x | IsInitial x}
  证明: rfl
-/
theorem coe_preOmega : preOmega = enumOrd {x | IsInitial x} :=
  rfl

/--
theorem `preOmega_strictMono` / 定理 `preOmega_strictMono`

English:
theorem preOmega_strictMono
  statement: StrictMono preOmega
  proof: preOmega.strictMono

中文:
定理 preOmega_strictMono
  结论: 严格递增 preOmega
  证明: preOmega.strictMono

Depends on / 依赖: preOmega, preOmega.strictMono, strictMono
-/
theorem preOmega_strictMono : StrictMono preOmega :=
  preOmega.strictMono

/--
theorem `preOmega_lt_preOmega` / 定理 `preOmega_lt_preOmega`

English:
theorem preOmega_lt_preOmega
  given: {o₁ o₂ : Ordinal}
  statement: preOmega o₁ < preOmega o₂ ↔ o₁ < o₂
  proof: preOmega.lt_iff_lt

中文:
定理 preOmega_lt_preOmega
  条件: {o₁ o₂ : 序数}
  结论: preOmega o₁ < preOmega o₂ ↔ o₁ < o₂
  证明: preOmega.lt_iff_lt

Depends on / 依赖: lt_iff_lt, preOmega, preOmega.lt_iff_lt
-/
theorem preOmega_lt_preOmega {o₁ o₂ : Ordinal} : preOmega o₁ < preOmega o₂ ↔ o₁ < o₂ :=
  preOmega.lt_iff_lt

/--
theorem `preOmega_le_preOmega` / 定理 `preOmega_le_preOmega`

English:
theorem preOmega_le_preOmega
  given: {o₁ o₂ : Ordinal}
  statement: preOmega o₁ <= preOmega o₂ ↔ o₁ <= o₂
  proof: preOmega.le_iff_le

中文:
定理 preOmega_le_preOmega
  条件: {o₁ o₂ : 序数}
  结论: preOmega o₁ <= preOmega o₂ ↔ o₁ <= o₂
  证明: preOmega.le_iff_le

Depends on / 依赖: le_iff_le, preOmega, preOmega.le_iff_le
-/
theorem preOmega_le_preOmega {o₁ o₂ : Ordinal} : preOmega o₁ <= preOmega o₂ ↔ o₁ <= o₂ :=
  preOmega.le_iff_le

/--
theorem `preOmega_max` / 定理 `preOmega_max`

English:
theorem preOmega_max
  given: (o₁ o₂ : Ordinal)
  statement: preOmega (max o₁ o₂) = max (preOmega o₁) (preOmega o₂)
  proof: preOmega.monotone.map_max

中文:
定理 preOmega_max
  条件: (o₁ o₂ : 序数)
  结论: preOmega (最大值 o₁ o₂) = 最大值 (preOmega o₁) (preOmega o₂)
  证明: preOmega.monotone.map_max

Depends on / 依赖: map_max, monotone, preOmega, preOmega.monotone.map_max
-/
theorem preOmega_max (o₁ o₂ : Ordinal) : preOmega (max o₁ o₂) = max (preOmega o₁) (preOmega o₂) :=
  preOmega.monotone.map_max

/--
theorem `isInitial_preOmega` / 定理 `isInitial_preOmega`

English:
theorem isInitial_preOmega
  given: (o : Ordinal)
  statement: IsInitial (preOmega o)
  proof: enumOrd_mem not_bddAbove_isInitial o

中文:
定理 isInitial_preOmega
  条件: (o : 序数)
  结论: IsInitial (preOmega o)
  证明: enumOrd_mem not_bddAbove_isInitial o

Depends on / 依赖: enumOrd_mem, not_bddAbove_isInitial
-/
theorem isInitial_preOmega (o : Ordinal) : IsInitial (preOmega o) :=
  enumOrd_mem not_bddAbove_isInitial o

/--
theorem `le_preOmega_self` / 定理 `le_preOmega_self`

English:
theorem le_preOmega_self
  given: (o : Ordinal)
  statement: o <= preOmega o
  proof: preOmega_strictMono.le_apply

@[simp]

中文:
定理 le_preOmega_self
  条件: (o : 序数)
  结论: o <= preOmega o
  证明: preOmega_strictMono.le_apply

@[simp]

Depends on / 依赖: le_apply, preOmega_strictMono, preOmega_strictMono.le_apply
-/
theorem le_preOmega_self (o : Ordinal) : o <= preOmega o :=
  preOmega_strictMono.le_apply

@[simp]
/--
theorem `preOmega_zero` / 定理 `preOmega_zero`

English:
theorem preOmega_zero
  statement: preOmega 0 = 0
  proof: by
  rw [coe_preOmega]; rw [enumOrd_zero]
  exact csInf_eq_bot_of_bot_mem isInitial_zero

@[simp]

中文:
定理 preOmega_zero
  结论: preOmega 0 = 0
  证明: by
  rw [coe_preOmega]; rw [enumOrd_zero]
  exact csInf_eq_bot_of_bot_mem isInitial_zero

@[simp]

Depends on / 依赖: coe_preOmega, csInf_eq_bot_of_bot_mem, enumOrd_zero, isInitial_zero
-/
theorem preOmega_zero : preOmega 0 = 0 := by
  rw [coe_preOmega]; rw [enumOrd_zero]
  exact csInf_eq_bot_of_bot_mem isInitial_zero

@[simp]
/--
theorem `preOmega_natCast` / 定理 `preOmega_natCast`

English:
theorem preOmega_natCast
  given: (n : Nat)
  statement: preOmega n = n
  proof: by
  induction n with
  | zero => exact preOmega_zero
  | succ n IH =>
    apply (le_preOmega_self _).antisymm'
    apply enumOrd_succ_le not_bddAbove_isInitial (isInitial_natCast _) (IH.trans_lt _)
    rw [Nat.cast_lt]
    exact lt_succ n

@[simp]

中文:
定理 preOmega_natCast
  条件: (n : 自然数)
  结论: preOmega n = n
  证明: by
  induction n with
  | zero => exact preOmega_zero
  | succ n IH =>
    apply (le_preOmega_self _).antisymm'
    apply enumOrd_succ_le not_bddAbove_isInitial (isInitial_natCast _) (IH.trans_lt _)
    rw [Nat.cast_lt]
    exact lt_succ n

@[simp]

Depends on / 依赖: IH.trans_lt, Nat.cast_lt, antisymm, cast_lt, enumOrd_succ_le, isInitial_natCast, le_preOmega_self, lt_succ, not_bddAbove_isInitial, preOmega_zero, trans_lt
-/
theorem preOmega_natCast (n : Nat) : preOmega n = n := by
  induction n with
  | zero => exact preOmega_zero
  | succ n IH =>
    apply (le_preOmega_self _).antisymm'
    apply enumOrd_succ_le not_bddAbove_isInitial (isInitial_natCast _) (IH.trans_lt _)
    rw [Nat.cast_lt]
    exact lt_succ n

@[simp]
/--
theorem `preOmega_ofNat` / 定理 `preOmega_ofNat`

English:
theorem preOmega_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: preOmega ofNat(n) = n
  proof: preOmega_natCast n

中文:
定理 preOmega_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: preOmega of自然数(n) = n
  证明: preOmega_natCast n

Depends on / 依赖: preOmega_natCast
-/
theorem preOmega_ofNat (n : Nat) [n.AtLeastTwo] : preOmega ofNat(n) = n :=
  preOmega_natCast n

/--
theorem `preOmega_le_of_forall_lt` / 定理 `preOmega_le_of_forall_lt`

English:
theorem preOmega_le_of_forall_lt
  given: {o a : Ordinal} (ha : IsInitial a) (H : forall b < o, preOmega b < a)
  proof: enumOrd_le_of_forall_lt ha H

中文:
定理 preOmega_le_of_对任意_lt
  条件: {o a : 序数} (ha : IsInitial a) (H : 对任意 b < o, preOmega b < a)
  证明: enumOrd_le_of_forall_lt ha H

Depends on / 依赖: enumOrd_le_of_forall_lt
-/
theorem preOmega_le_of_forall_lt {o a : Ordinal} (ha : IsInitial a) (H : forall b < o, preOmega b < a) :
    preOmega o <= a :=
  enumOrd_le_of_forall_lt ha H

/--
theorem `isNormal_preOmega` / 定理 `isNormal_preOmega`

English:
theorem isNormal_preOmega
  statement: IsNormal preOmega
  proof: by
  rw [isNormal_iff]
  refine ⟨preOmega_strictMono, fun o ho a ha =>
    (preOmega_le_of_forall_lt (isInitial_ord _) fun b hb => ?_).trans (ord_card_le a)⟩
  rw [← (isInitial_ord _).card_lt_card]; rw [card_ord]
  apply lt_of_lt_of_le _ (card_le_card <| ha _ (ho.succ_lt hb))
  rw [(isInitial_preOmega _).card_lt_card]; rw [preOmega_lt_preOmega]
  exact lt_succ b

@[simp]

中文:
定理 isNormal_preOmega
  结论: 是正规 preOmega
  证明: by
  rw [isNormal_iff]
  refine ⟨preOmega_strictMono, fun o ho a ha =>
    (preOmega_le_of_forall_lt (isInitial_ord _) fun b hb => ?_).trans (ord_card_le a)⟩
  rw [← (isInitial_ord _).card_lt_card]; rw [card_ord]
  apply lt_of_lt_of_le _ (card_le_card <| ha _ (ho.succ_lt hb))
  rw [(isInitial_preOmega _).card_lt_card]; rw [preOmega_lt_preOmega]
  exact lt_succ b

@[simp]

Depends on / 依赖: card_le_card, card_lt_card, card_ord, ho.succ_lt, isInitial_ord, isInitial_preOmega, isNormal_iff, lt_of_lt_of_le, lt_succ, ord_card_le, preOmega_le_of_forall_lt, preOmega_lt_preOmega, preOmega_strictMono, succ_lt
-/
theorem isNormal_preOmega : IsNormal preOmega := by
  rw [isNormal_iff]
  refine ⟨preOmega_strictMono, fun o ho a ha =>
    (preOmega_le_of_forall_lt (isInitial_ord _) fun b hb => ?_).trans (ord_card_le a)⟩
  rw [← (isInitial_ord _).card_lt_card]; rw [card_ord]
  apply lt_of_lt_of_le _ (card_le_card <| ha _ (ho.succ_lt hb))
  rw [(isInitial_preOmega _).card_lt_card]; rw [preOmega_lt_preOmega]
  exact lt_succ b

@[simp]
/--
theorem `range_preOmega` / 定理 `range_preOmega`

English:
theorem range_preOmega
  statement: range preOmega = {x | IsInitial x}
  proof: range_enumOrd not_bddAbove_isInitial

中文:
定理 range_preOmega
  结论: range preOmega = {x | IsInitial x}
  证明: range_enumOrd not_bddAbove_isInitial

Depends on / 依赖: not_bddAbove_isInitial, range_enumOrd
-/
theorem range_preOmega : range preOmega = {x | IsInitial x} :=
  range_enumOrd not_bddAbove_isInitial

/--
theorem `mem_range_preOmega_iff` / 定理 `mem_range_preOmega_iff`

English:
theorem mem_range_preOmega_iff
  given: {x : Ordinal}
  statement: x in range preOmega ↔ IsInitial x
  proof: by
  rw [range_preOmega]; rw [mem_ofPred]

alias ⟨_, IsInitial.mem_range_preOmega⟩ := mem_range_preOmega_iff

@[simp]

中文:
定理 mem_range_preOmega_iff
  条件: {x : 序数}
  结论: x in range preOmega ↔ IsInitial x
  证明: by
  rw [range_preOmega]; rw [mem_ofPred]

alias ⟨_, IsInitial.mem_range_preOmega⟩ := mem_range_preOmega_iff

@[simp]

Depends on / 依赖: mem_ofPred, range_preOmega
-/
theorem mem_range_preOmega_iff {x : Ordinal} : x in range preOmega ↔ IsInitial x := by
  rw [range_preOmega]; rw [mem_ofPred]

alias ⟨_, IsInitial.mem_range_preOmega⟩ := mem_range_preOmega_iff

@[simp]
/--
theorem `preOmega_omega0` / 定理 `preOmega_omega0`

English:
theorem preOmega_omega0
  statement: preOmega ω = ω
  proof: by
  simp_rw [← apply_omega0_of_isNormal isNormal_preOmega, preOmega_natCast, iSup_natCast]

@[simp]

中文:
定理 preOmega_omega0
  结论: preOmega ω = ω
  证明: by
  simp_rw [← apply_omega0_of_isNormal isNormal_preOmega, preOmega_natCast, iSup_natCast]

@[simp]

Depends on / 依赖: apply_omega0_of_isNormal, iSup_natCast, isNormal_preOmega, preOmega_natCast, simp_rw
-/
theorem preOmega_omega0 : preOmega ω = ω := by
  simp_rw [← apply_omega0_of_isNormal isNormal_preOmega, preOmega_natCast, iSup_natCast]

@[simp]
/--
theorem `omega0_le_preOmega_iff` / 定理 `omega0_le_preOmega_iff`

English:
theorem omega0_le_preOmega_iff
  given: {x : Ordinal}
  statement: ω <= preOmega x ↔ ω <= x
  proof: by
  conv_lhs => rw [← preOmega_omega0, preOmega_le_preOmega]

@[simp]

中文:
定理 omega0_le_preOmega_iff
  条件: {x : 序数}
  结论: ω <= preOmega x ↔ ω <= x
  证明: by
  conv_lhs => rw [← preOmega_omega0, preOmega_le_preOmega]

@[simp]

Depends on / 依赖: conv_lhs, preOmega_le_preOmega, preOmega_omega0
-/
theorem omega0_le_preOmega_iff {x : Ordinal} : ω <= preOmega x ↔ ω <= x := by
  conv_lhs => rw [← preOmega_omega0, preOmega_le_preOmega]

@[simp]
/--
theorem `omega0_lt_preOmega_iff` / 定理 `omega0_lt_preOmega_iff`

English:
theorem omega0_lt_preOmega_iff
  given: {x : Ordinal}
  statement: ω < preOmega x ↔ ω < x
  proof: by
  conv_lhs => rw [← preOmega_omega0, preOmega_lt_preOmega]

中文:
定理 omega0_lt_preOmega_iff
  条件: {x : 序数}
  结论: ω < preOmega x ↔ ω < x
  证明: by
  conv_lhs => rw [← preOmega_omega0, preOmega_lt_preOmega]

Depends on / 依赖: conv_lhs, preOmega_lt_preOmega, preOmega_omega0
-/
theorem omega0_lt_preOmega_iff {x : Ordinal} : ω < preOmega x ↔ ω < x := by
  conv_lhs => rw [← preOmega_omega0, preOmega_lt_preOmega]

/--
Definition of `omega` / `omega` 的定义

English:
definition omega
  signature: : Ordinal ↪o Ordinal
  body: (OrderEmbedding.addLeft ω).trans preOmega

@[inherit_doc] scoped notation "ω_ " => omega
recommended_spelling "omega" for "ω_" in [omega, «termω_»]

中文:
定义 omega
  签名: : 序数 ↪o 序数
  定义体: (OrderEmbedding.addLeft ω).trans preOmega

@[inherit_doc] scoped notation "ω_ " => omega
recommended_spelling "omega" for "ω_" in [omega, «termω_»]

Depends on / 依赖: OrderEmbedding, OrderEmbedding.addLeft, addLeft, preOmega
-/
def omega : Ordinal ↪o Ordinal :=
  (OrderEmbedding.addLeft ω).trans preOmega

@[inherit_doc] scoped notation "ω_ " => omega
recommended_spelling "omega" for "ω_" in [omega, «termω_»]

/-- `ω₁` is the first uncountable ordinal. -/
scoped notation "ω₁" => ω_ 1
recommended_spelling "omega_one" for "ω₁" in [«termω₁»]

/--
theorem `omega_eq_preOmega` / 定理 `omega_eq_preOmega`

English:
theorem omega_eq_preOmega
  given: (o : Ordinal)
  statement: ω_ o = preOmega (ω + o)
  proof: rfl

中文:
定理 omega_eq_preOmega
  条件: (o : 序数)
  结论: ω_ o = preOmega (ω + o)
  证明: rfl
-/
theorem omega_eq_preOmega (o : Ordinal) : ω_ o = preOmega (ω + o) :=
  rfl

/--
theorem `omega_strictMono` / 定理 `omega_strictMono`

English:
theorem omega_strictMono
  statement: StrictMono omega
  proof: omega.strictMono

中文:
定理 omega_strictMono
  结论: 严格递增 omega
  证明: omega.strictMono

Depends on / 依赖: omega.strictMono, strictMono
-/
theorem omega_strictMono : StrictMono omega :=
  omega.strictMono

/--
theorem `omega_lt_omega` / 定理 `omega_lt_omega`

English:
theorem omega_lt_omega
  given: {o₁ o₂ : Ordinal}
  statement: ω_ o₁ < ω_ o₂ ↔ o₁ < o₂
  proof: omega.lt_iff_lt

中文:
定理 omega_lt_omega
  条件: {o₁ o₂ : 序数}
  结论: ω_ o₁ < ω_ o₂ ↔ o₁ < o₂
  证明: omega.lt_iff_lt

Depends on / 依赖: lt_iff_lt, omega.lt_iff_lt
-/
theorem omega_lt_omega {o₁ o₂ : Ordinal} : ω_ o₁ < ω_ o₂ ↔ o₁ < o₂ :=
  omega.lt_iff_lt

/--
theorem `omega_le_omega` / 定理 `omega_le_omega`

English:
theorem omega_le_omega
  given: {o₁ o₂ : Ordinal}
  statement: ω_ o₁ <= ω_ o₂ ↔ o₁ <= o₂
  proof: omega.le_iff_le

中文:
定理 omega_le_omega
  条件: {o₁ o₂ : 序数}
  结论: ω_ o₁ <= ω_ o₂ ↔ o₁ <= o₂
  证明: omega.le_iff_le

Depends on / 依赖: le_iff_le, omega.le_iff_le
-/
theorem omega_le_omega {o₁ o₂ : Ordinal} : ω_ o₁ <= ω_ o₂ ↔ o₁ <= o₂ :=
  omega.le_iff_le

/--
theorem `omega_max` / 定理 `omega_max`

English:
theorem omega_max
  given: (o₁ o₂ : Ordinal)
  statement: ω_ (max o₁ o₂) = max (ω_ o₁) (ω_ o₂)
  proof: omega.monotone.map_max

中文:
定理 omega_max
  条件: (o₁ o₂ : 序数)
  结论: ω_ (最大值 o₁ o₂) = 最大值 (ω_ o₁) (ω_ o₂)
  证明: omega.monotone.map_max

Depends on / 依赖: map_max, monotone, omega.monotone.map_max
-/
theorem omega_max (o₁ o₂ : Ordinal) : ω_ (max o₁ o₂) = max (ω_ o₁) (ω_ o₂) :=
  omega.monotone.map_max

/--
theorem `preOmega_le_omega` / 定理 `preOmega_le_omega`

English:
theorem preOmega_le_omega
  given: (o : Ordinal)
  statement: preOmega o <= ω_ o
  proof: preOmega_le_preOmega.2 le_add_self

中文:
定理 preOmega_le_omega
  条件: (o : 序数)
  结论: preOmega o <= ω_ o
  证明: preOmega_le_preOmega.2 le_add_self

Depends on / 依赖: le_add_self, preOmega_le_preOmega
-/
theorem preOmega_le_omega (o : Ordinal) : preOmega o <= ω_ o :=
  preOmega_le_preOmega.2 le_add_self

/--
theorem `isInitial_omega` / 定理 `isInitial_omega`

English:
theorem isInitial_omega
  given: (o : Ordinal)
  statement: IsInitial (omega o)
  proof: isInitial_preOmega _

中文:
定理 isInitial_omega
  条件: (o : 序数)
  结论: IsInitial (omega o)
  证明: isInitial_preOmega _

Depends on / 依赖: isInitial_preOmega
-/
theorem isInitial_omega (o : Ordinal) : IsInitial (omega o) :=
  isInitial_preOmega _

/--
theorem `le_omega_self` / 定理 `le_omega_self`

English:
theorem le_omega_self
  given: (o : Ordinal)
  statement: o <= omega o
  proof: omega_strictMono.le_apply

@[simp]

中文:
定理 le_omega_self
  条件: (o : 序数)
  结论: o <= omega o
  证明: omega_strictMono.le_apply

@[simp]

Depends on / 依赖: le_apply, omega_strictMono, omega_strictMono.le_apply
-/
theorem le_omega_self (o : Ordinal) : o <= omega o :=
  omega_strictMono.le_apply

@[simp]
/--
theorem `omega_zero` / 定理 `omega_zero`

English:
theorem omega_zero
  statement: ω_ 0 = ω
  proof: by
  rw [omega_eq_preOmega]; rw [add_zero]; rw [preOmega_omega0]

中文:
定理 omega_zero
  结论: ω_ 0 = ω
  证明: by
  rw [omega_eq_preOmega]; rw [add_zero]; rw [preOmega_omega0]

Depends on / 依赖: add_zero, omega_eq_preOmega, preOmega_omega0
-/
theorem omega_zero : ω_ 0 = ω := by
  rw [omega_eq_preOmega]; rw [add_zero]; rw [preOmega_omega0]

/--
theorem `omega0_le_omega` / 定理 `omega0_le_omega`

English:
theorem omega0_le_omega
  given: (o : Ordinal)
  statement: ω <= ω_ o
  proof: by
  rw [← omega_zero]; rw [omega_le_omega]
  exact zero_le

中文:
定理 omega0_le_omega
  条件: (o : 序数)
  结论: ω <= ω_ o
  证明: by
  rw [← omega_zero]; rw [omega_le_omega]
  exact zero_le

Depends on / 依赖: omega_le_omega, omega_zero, zero_le
-/
theorem omega0_le_omega (o : Ordinal) : ω <= ω_ o := by
  rw [← omega_zero]; rw [omega_le_omega]
  exact zero_le

/--
theorem `omega_pos` / 定理 `omega_pos`

English:
theorem omega_pos
  given: (o : Ordinal)
  statement: 0 < ω_ o
  proof: omega0_pos.trans_le (omega0_le_omega o)

@[simp]

中文:
定理 omega_pos
  条件: (o : 序数)
  结论: 0 < ω_ o
  证明: omega0_pos.trans_le (omega0_le_omega o)

@[simp]

Depends on / 依赖: omega0_le_omega, omega0_pos, omega0_pos.trans_le, trans_le
-/
theorem omega_pos (o : Ordinal) : 0 < ω_ o :=
  omega0_pos.trans_le (omega0_le_omega o)

@[simp]
/--
theorem `omega0_lt_omega_one` / 定理 `omega0_lt_omega_one`

English:
theorem omega0_lt_omega_one
  statement: ω < ω₁
  proof: by
  rw [← omega_zero]; rw [omega_lt_omega]
  exact zero_lt_one

中文:
定理 omega0_lt_omega_one
  结论: ω < ω₁
  证明: by
  rw [← omega_zero]; rw [omega_lt_omega]
  exact zero_lt_one

Depends on / 依赖: omega_lt_omega, omega_zero, zero_lt_one
-/
theorem omega0_lt_omega_one : ω < ω₁ := by
  rw [← omega_zero]; rw [omega_lt_omega]
  exact zero_lt_one

/--
theorem `isNormal_omega` / 定理 `isNormal_omega`

English:
theorem isNormal_omega
  statement: IsNormal omega
  proof: isNormal_preOmega.comp (isNormal_add_right _)

@[simp]

中文:
定理 isNormal_omega
  结论: 是正规 omega
  证明: isNormal_preOmega.comp (isNormal_add_right _)

@[simp]

Depends on / 依赖: isNormal_add_right, isNormal_preOmega, isNormal_preOmega.comp
-/
theorem isNormal_omega : IsNormal omega :=
  isNormal_preOmega.comp (isNormal_add_right _)

@[simp]
/--
theorem `range_omega` / 定理 `range_omega`

English:
theorem range_omega
  statement: range omega = {x | ω <= x ∧ IsInitial x}
  proof: by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨omega0_le_omega a, isInitial_omega a⟩
  · rintro ⟨ha', ha⟩
    obtain ⟨a, rfl⟩ := ha.mem_range_preOmega
    use a - ω
    rw [omega0_le_preOmega_iff] at ha'
    rw [omega_eq_preOmega]; rw [Ordinal.add_sub_cancel_of_le ha']

中文:
定理 range_omega
  结论: range omega = {x | ω <= x ∧ IsInitial x}
  证明: by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨omega0_le_omega a, isInitial_omega a⟩
  · rintro ⟨ha', ha⟩
    obtain ⟨a, rfl⟩ := ha.mem_range_preOmega
    use a - ω
    rw [omega0_le_preOmega_iff] at ha'
    rw [omega_eq_preOmega]; rw [Ordinal.add_sub_cancel_of_le ha']

Depends on / 依赖: Ordinal, Ordinal.add_sub_cancel_of_le, add_sub_cancel_of_le, ha.mem_range_preOmega, isInitial_omega, mem_range_preOmega, omega0_le_omega, omega0_le_preOmega_iff, omega_eq_preOmega
-/
theorem range_omega : range omega = {x | ω <= x ∧ IsInitial x} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨omega0_le_omega a, isInitial_omega a⟩
  · rintro ⟨ha', ha⟩
    obtain ⟨a, rfl⟩ := ha.mem_range_preOmega
    use a - ω
    rw [omega0_le_preOmega_iff] at ha'
    rw [omega_eq_preOmega]; rw [Ordinal.add_sub_cancel_of_le ha']

/--
theorem `mem_range_omega_iff` / 定理 `mem_range_omega_iff`

English:
theorem mem_range_omega_iff
  given: {x : Ordinal}
  statement: x in range omega ↔ ω <= x ∧ IsInitial x
  proof: by
  rw [range_omega]; rw [mem_ofPred]

中文:
定理 mem_range_omega_iff
  条件: {x : 序数}
  结论: x in range omega ↔ ω <= x ∧ IsInitial x
  证明: by
  rw [range_omega]; rw [mem_ofPred]

Depends on / 依赖: mem_ofPred, range_omega
-/
theorem mem_range_omega_iff {x : Ordinal} : x in range omega ↔ ω <= x ∧ IsInitial x := by
  rw [range_omega]; rw [mem_ofPred]

/--
theorem `preOmega_of_omega0_sq_le` / 定理 `preOmega_of_omega0_sq_le`

English:
theorem preOmega_of_omega0_sq_le
  given: {o : Ordinal} (ho : ω ^ 2 <= o)
  statement: preOmega o = ω_ o
  proof: by
  rw [← opow_natCast] at ho
  rw [omega_eq_preOmega]; rw [add_of_omega0_opow_le _ ho]
  apply left_lt_opow one_lt_omega0
  simp

中文:
定理 preOmega_of_omega0_sq_le
  条件: {o : 序数} (ho : ω ^ 2 <= o)
  结论: preOmega o = ω_ o
  证明: by
  rw [← opow_natCast] at ho
  rw [omega_eq_preOmega]; rw [add_of_omega0_opow_le _ ho]
  apply left_lt_opow one_lt_omega0
  simp

Depends on / 依赖: add_of_omega0_opow_le, left_lt_opow, omega_eq_preOmega, one_lt_omega0, opow_natCast
-/
theorem preOmega_of_omega0_sq_le {o : Ordinal} (ho : ω ^ 2 <= o) : preOmega o = ω_ o := by
  rw [← opow_natCast] at ho
  rw [omega_eq_preOmega]; rw [add_of_omega0_opow_le _ ho]
  apply left_lt_opow one_lt_omega0
  simp

end Ordinal

/-! ### Aleph cardinals -/

namespace Cardinal

/--
Definition of `preAleph` / `preAleph` 的定义

English:
definition preAleph
  signature: : Ordinal.{u} ≃o Cardinal.{u}
  body: (enumOrdOrderIso _ not_bddAbove_isInitial).trans isInitialIso

@[simp]

中文:
定义 preAleph
  签名: : 序数.{u} ≃o 基数.{u}
  定义体: (enumOrdOrderIso _ not_bddAbove_isInitial).trans isInitialIso

@[simp]

Depends on / 依赖: enumOrdOrderIso, isInitialIso, not_bddAbove_isInitial
-/
def preAleph : Ordinal.{u} ≃o Cardinal.{u} :=
  (enumOrdOrderIso _ not_bddAbove_isInitial).trans isInitialIso

@[simp]
/--
theorem `_root_.Ordinal.card_preOmega` / 定理 `_root_.Ordinal.card_preOmega`

English:
theorem _root_.Ordinal.card_preOmega
  given: (o : Ordinal)
  statement: (preOmega o).card = preAleph o
  proof: rfl

@[simp]

中文:
定理 _root_.序数.card_preOmega
  条件: (o : 序数)
  结论: (preOmega o).card = preAleph o
  证明: rfl

@[simp]
-/
theorem _root_.Ordinal.card_preOmega (o : Ordinal) : (preOmega o).card = preAleph o :=
  rfl

@[simp]
/--
theorem `ord_preAleph` / 定理 `ord_preAleph`

English:
theorem ord_preAleph
  given: (o : Ordinal)
  statement: (preAleph o).ord = preOmega o
  proof: by
  rw [← o.card_preOmega]; rw [(isInitial_preOmega o).ord_card]

@[simp]

中文:
定理 ord_preAleph
  条件: (o : 序数)
  结论: (preAleph o).ord = preOmega o
  证明: by
  rw [← o.card_preOmega]; rw [(isInitial_preOmega o).ord_card]

@[simp]

Depends on / 依赖: card_preOmega, isInitial_preOmega, o.card_preOmega, ord_card
-/
theorem ord_preAleph (o : Ordinal) : (preAleph o).ord = preOmega o := by
  rw [← o.card_preOmega]; rw [(isInitial_preOmega o).ord_card]

@[simp]
/--
theorem `_root_.Ordinal.type_lt_cardinal` / 定理 `_root_.Ordinal.type_lt_cardinal`

English:
theorem _root_.Ordinal.type_lt_cardinal
  statement: typeLT Cardinal = Ordinal.univ.{u, u + 1}
  proof: by
  simpa using preAleph.symm.ordinalType_congr

@[deprecated (since := "2026-03-20")] alias type_cardinal := type_lt_cardinal

@[simp]

中文:
定理 _root_.序数.type_lt_cardinal
  结论: typeLT 基数 = 序数.univ.{u, u + 1}
  证明: by
  simpa using preAleph.symm.ordinalType_congr

@[deprecated (since := "2026-03-20")] alias type_cardinal := type_lt_cardinal

@[simp]

Depends on / 依赖: ordinalType_congr, preAleph, preAleph.symm.ordinalType_congr
-/
theorem _root_.Ordinal.type_lt_cardinal : typeLT Cardinal = Ordinal.univ.{u, u + 1} := by
  simpa using preAleph.symm.ordinalType_congr

@[deprecated (since := "2026-03-20")] alias type_cardinal := type_lt_cardinal

@[simp]
/--
theorem `mk_cardinal` / 定理 `mk_cardinal`

English:
theorem mk_cardinal
  statement: #Cardinal = univ.{u, u + 1}
  proof: by
  simpa only [card_type, card_univ] using congr_arg card type_lt_cardinal

中文:
定理 mk_cardinal
  结论: #基数 = univ.{u, u + 1}
  证明: by
  simpa only [card_type, card_univ] using congr_arg card type_lt_cardinal

Depends on / 依赖: card_type, card_univ, congr_arg, type_lt_cardinal
-/
theorem mk_cardinal : #Cardinal = univ.{u, u + 1} := by
  simpa only [card_type, card_univ] using congr_arg card type_lt_cardinal

/--
theorem `_root_.Order.cof_cardinal` / 定理 `_root_.Order.cof_cardinal`

English:
theorem _root_.Order.cof_cardinal
  statement: Order.cof Cardinal.{u} = Cardinal.univ.{u, u + 1}
  proof: by
  simpa using preAleph.cof_congr.symm

中文:
定理 _root_.Order.cof_cardinal
  结论: Order.cof 基数.{u} = 基数.univ.{u, u + 1}
  证明: by
  simpa using preAleph.cof_congr.symm

Depends on / 依赖: cof_congr, preAleph, preAleph.cof_congr.symm
-/
theorem _root_.Order.cof_cardinal : Order.cof Cardinal.{u} = Cardinal.univ.{u, u + 1} := by
  simpa using preAleph.cof_congr.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsRegularCardinalOrder Cardinal
  body: ⟨by simp [Order.cof_cardinal]⟩

中文:
实例 :
  签名: 是RegularCardinal序 基数
  定义体: ⟨by simp [Order.cof_cardinal]⟩

Depends on / 依赖: ContractibleSpace, Joined, Order.cof_cardinal, PathConnectedSpace, cof_cardinal, evalAt, h.evalAt, id_nullhomotopic, pathConnectedSpace_iff_eq
-/
instance : IsRegularCardinalOrder Cardinal := ⟨by simp [Order.cof_cardinal]⟩

/--
theorem `preAleph_lt_preAleph` / 定理 `preAleph_lt_preAleph`

English:
theorem preAleph_lt_preAleph
  given: {o₁ o₂ : Ordinal}
  statement: preAleph o₁ < preAleph o₂ ↔ o₁ < o₂
  proof: preAleph.lt_iff_lt

中文:
定理 preAleph_lt_preAleph
  条件: {o₁ o₂ : 序数}
  结论: preAleph o₁ < preAleph o₂ ↔ o₁ < o₂
  证明: preAleph.lt_iff_lt

Depends on / 依赖: lt_iff_lt, preAleph, preAleph.lt_iff_lt
-/
theorem preAleph_lt_preAleph {o₁ o₂ : Ordinal} : preAleph o₁ < preAleph o₂ ↔ o₁ < o₂ :=
  preAleph.lt_iff_lt

/--
theorem `preAleph_le_preAleph` / 定理 `preAleph_le_preAleph`

English:
theorem preAleph_le_preAleph
  given: {o₁ o₂ : Ordinal}
  statement: preAleph o₁ <= preAleph o₂ ↔ o₁ <= o₂
  proof: preAleph.le_iff_le

中文:
定理 preAleph_le_preAleph
  条件: {o₁ o₂ : 序数}
  结论: preAleph o₁ <= preAleph o₂ ↔ o₁ <= o₂
  证明: preAleph.le_iff_le

Depends on / 依赖: le_iff_le, preAleph, preAleph.le_iff_le
-/
theorem preAleph_le_preAleph {o₁ o₂ : Ordinal} : preAleph o₁ <= preAleph o₂ ↔ o₁ <= o₂ :=
  preAleph.le_iff_le

/--
theorem `preAleph_max` / 定理 `preAleph_max`

English:
theorem preAleph_max
  given: (o₁ o₂ : Ordinal)
  statement: preAleph (max o₁ o₂) = max (preAleph o₁) (preAleph o₂)
  proof: preAleph.monotone.map_max

@[simp]

中文:
定理 preAleph_max
  条件: (o₁ o₂ : 序数)
  结论: preAleph (最大值 o₁ o₂) = 最大值 (preAleph o₁) (preAleph o₂)
  证明: preAleph.monotone.map_max

@[simp]

Depends on / 依赖: map_max, monotone, preAleph, preAleph.monotone.map_max
-/
theorem preAleph_max (o₁ o₂ : Ordinal) : preAleph (max o₁ o₂) = max (preAleph o₁) (preAleph o₂) :=
  preAleph.monotone.map_max

@[simp]
/--
theorem `preAleph_zero` / 定理 `preAleph_zero`

English:
theorem preAleph_zero
  statement: preAleph 0 = 0
  proof: preAleph.map_bot

@[simp]

中文:
定理 preAleph_zero
  结论: preAleph 0 = 0
  证明: preAleph.map_bot

@[simp]

Depends on / 依赖: map_bot, preAleph, preAleph.map_bot
-/
theorem preAleph_zero : preAleph 0 = 0 :=
  preAleph.map_bot

@[simp]
/--
theorem `succ_preAleph` / 定理 `succ_preAleph`

English:
theorem succ_preAleph
  given: (o : Ordinal)
  statement: succ (preAleph o) = preAleph (o + 1)
  proof: (preAleph.map_succ o).symm

@[deprecated succ_preAleph (since := "2026-03-24")]

中文:
定理 succ_preAleph
  条件: (o : 序数)
  结论: succ (preAleph o) = preAleph (o + 1)
  证明: (preAleph.map_succ o).symm

@[deprecated succ_preAleph (since := "2026-03-24")]

Depends on / 依赖: map_succ, preAleph, preAleph.map_succ
-/
theorem succ_preAleph (o : Ordinal) : succ (preAleph o) = preAleph (o + 1) :=
  (preAleph.map_succ o).symm

@[deprecated succ_preAleph (since := "2026-03-24")]
/--
theorem `preAleph_add_one` / 定理 `preAleph_add_one`

English:
theorem preAleph_add_one
  given: (o : Ordinal)
  statement: preAleph (o + 1) = succ (preAleph o)
  proof: preAleph.map_succ o

@[deprecated succ_preAleph (since := "2026-03-24")]

中文:
定理 preAleph_add_one
  条件: (o : 序数)
  结论: preAleph (o + 1) = succ (preAleph o)
  证明: preAleph.map_succ o

@[deprecated succ_preAleph (since := "2026-03-24")]

Depends on / 依赖: map_succ, preAleph, preAleph.map_succ
-/
theorem preAleph_add_one (o : Ordinal) : preAleph (o + 1) = succ (preAleph o) :=
  preAleph.map_succ o

@[deprecated succ_preAleph (since := "2026-03-24")]
/--
theorem `preAleph_succ` / 定理 `preAleph_succ`

English:
theorem preAleph_succ
  given: (o : Ordinal)
  statement: preAleph (succ o) = succ (preAleph o)
  proof: preAleph.map_succ o

@[simp]

中文:
定理 preAleph_succ
  条件: (o : 序数)
  结论: preAleph (succ o) = succ (preAleph o)
  证明: preAleph.map_succ o

@[simp]

Depends on / 依赖: map_succ, preAleph, preAleph.map_succ
-/
theorem preAleph_succ (o : Ordinal) : preAleph (succ o) = succ (preAleph o) :=
  preAleph.map_succ o

@[simp]
/--
theorem `preAleph_natCast` / 定理 `preAleph_natCast`

English:
theorem preAleph_natCast
  given: (n : Nat)
  statement: preAleph n = n
  proof: by
  rw [← card_preOmega]; rw [preOmega_natCast]; rw [card_nat]

@[simp]

中文:
定理 preAleph_natCast
  条件: (n : 自然数)
  结论: preAleph n = n
  证明: by
  rw [← card_preOmega]; rw [preOmega_natCast]; rw [card_nat]

@[simp]

Depends on / 依赖: card_nat, card_preOmega, preOmega_natCast
-/
theorem preAleph_natCast (n : Nat) : preAleph n = n := by
  rw [← card_preOmega]; rw [preOmega_natCast]; rw [card_nat]

@[simp]
/--
theorem `preAleph_ofNat` / 定理 `preAleph_ofNat`

English:
theorem preAleph_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: preAleph ofNat(n) = ofNat(n)
  proof: preAleph_natCast n

@[simp]

中文:
定理 preAleph_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: preAleph of自然数(n) = of自然数(n)
  证明: preAleph_natCast n

@[simp]

Depends on / 依赖: h.symm, preAleph_natCast
-/
theorem preAleph_ofNat (n : Nat) [n.AtLeastTwo] : preAleph ofNat(n) = ofNat(n) :=
  preAleph_natCast n

@[simp]
/--
theorem `preAleph_symm_natCast` / 定理 `preAleph_symm_natCast`

English:
theorem preAleph_symm_natCast
  given: (n : Nat)
  statement: preAleph.symm n = n
  proof: by
  simp [OrderIso.symm_apply_eq]

@[simp]

中文:
定理 preAleph_symm_natCast
  条件: (n : 自然数)
  结论: preAleph.symm n = n
  证明: by
  simp [OrderIso.symm_apply_eq]

@[simp]

Depends on / 依赖: OrderIso, OrderIso.symm_apply_eq, symm_apply_eq
-/
theorem preAleph_symm_natCast (n : Nat) : preAleph.symm n = n := by
  simp [OrderIso.symm_apply_eq]

@[simp]
/--
theorem `preAleph_symm_ofNat` / 定理 `preAleph_symm_ofNat`

English:
theorem preAleph_symm_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: preAleph.symm ofNat(n) = ofNat(n)
  proof: preAleph_symm_natCast n

@[deprecated (since := "2026-05-22")] alias preAleph_nat := preAleph_natCast

@[simp]

中文:
定理 preAleph_symm_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: preAleph.symm of自然数(n) = of自然数(n)
  证明: preAleph_symm_natCast n

@[deprecated (since := "2026-05-22")] alias preAleph_nat := preAleph_natCast

@[simp]

Depends on / 依赖: preAleph_symm_natCast
-/
theorem preAleph_symm_ofNat (n : Nat) [n.AtLeastTwo] : preAleph.symm ofNat(n) = ofNat(n) :=
  preAleph_symm_natCast n

@[deprecated (since := "2026-05-22")] alias preAleph_nat := preAleph_natCast

@[simp]
/--
theorem `preAleph_omega0` / 定理 `preAleph_omega0`

English:
theorem preAleph_omega0
  statement: preAleph ω = ℵ₀
  proof: by
  rw [← card_preOmega]; rw [preOmega_omega0]; rw [card_omega0]

@[simp]

中文:
定理 preAleph_omega0
  结论: preAleph ω = ℵ₀
  证明: by
  rw [← card_preOmega]; rw [preOmega_omega0]; rw [card_omega0]

@[simp]

Depends on / 依赖: card_omega0, card_preOmega, preOmega_omega0
-/
theorem preAleph_omega0 : preAleph ω = ℵ₀ := by
  rw [← card_preOmega]; rw [preOmega_omega0]; rw [card_omega0]

@[simp]
/--
theorem `preAleph_symm_aleph0` / 定理 `preAleph_symm_aleph0`

English:
theorem preAleph_symm_aleph0
  statement: preAleph.symm ℵ₀ = ω
  proof: by
  simp [OrderIso.symm_apply_eq]

@[simp]

中文:
定理 preAleph_symm_aleph0
  结论: preAleph.symm ℵ₀ = ω
  证明: by
  simp [OrderIso.symm_apply_eq]

@[simp]

Depends on / 依赖: OrderIso, OrderIso.symm_apply_eq, symm_apply_eq
-/
theorem preAleph_symm_aleph0 : preAleph.symm ℵ₀ = ω := by
  simp [OrderIso.symm_apply_eq]

@[simp]
/--
theorem `preAleph_pos` / 定理 `preAleph_pos`

English:
theorem preAleph_pos
  given: {o : Ordinal}
  statement: 0 < preAleph o ↔ 0 < o
  proof: by
  rw [← preAleph_zero]; rw [preAleph_lt_preAleph]

@[simp]

中文:
定理 preAleph_pos
  条件: {o : 序数}
  结论: 0 < preAleph o ↔ 0 < o
  证明: by
  rw [← preAleph_zero]; rw [preAleph_lt_preAleph]

@[simp]

Depends on / 依赖: preAleph_lt_preAleph, preAleph_zero
-/
theorem preAleph_pos {o : Ordinal} : 0 < preAleph o ↔ 0 < o := by
  rw [← preAleph_zero]; rw [preAleph_lt_preAleph]

@[simp]
/--
theorem `aleph0_le_preAleph` / 定理 `aleph0_le_preAleph`

English:
theorem aleph0_le_preAleph
  given: {o : Ordinal}
  statement: ℵ₀ <= preAleph o ↔ ω <= o
  proof: by
  rw [← preAleph_omega0]; rw [preAleph_le_preAleph]

中文:
定理 aleph0_le_preAleph
  条件: {o : 序数}
  结论: ℵ₀ <= preAleph o ↔ ω <= o
  证明: by
  rw [← preAleph_omega0]; rw [preAleph_le_preAleph]

Depends on / 依赖: preAleph_le_preAleph, preAleph_omega0
-/
theorem aleph0_le_preAleph {o : Ordinal} : ℵ₀ <= preAleph o ↔ ω <= o := by
  rw [← preAleph_omega0]; rw [preAleph_le_preAleph]

/--
theorem `_root_.Ordinal.card_le_preAleph` / 定理 `_root_.Ordinal.card_le_preAleph`

English:
theorem _root_.Ordinal.card_le_preAleph
  given: (o : Ordinal)
  statement: o.card <= preAleph o
  proof: o.card_preOmega.trans_ge card_le_card o.le_preOmega_self

中文:
定理 _root_.序数.card_le_preAleph
  条件: (o : 序数)
  结论: o.card <= preAleph o
  证明: o.card_preOmega.trans_ge card_le_card o.le_preOmega_self

Depends on / 依赖: card_le_card, card_preOmega, le_preOmega_self, o.card_preOmega.trans_ge, o.le_preOmega_self, trans_ge
-/
theorem _root_.Ordinal.card_le_preAleph (o : Ordinal) : o.card <= preAleph o :=
o.card_preOmega.trans_ge card_le_card o.le_preOmega_self

/--
theorem `le_preAleph_ord` / 定理 `le_preAleph_ord`

English:
theorem le_preAleph_ord
  given: (c : Cardinal)
  statement: c <= preAleph c.ord
  proof: by
  simpa using c.ord.card_le_preAleph

@[simp]

中文:
定理 le_preAleph_ord
  条件: (c : 基数)
  结论: c <= preAleph c.ord
  证明: by
  simpa using c.ord.card_le_preAleph

@[simp]

Depends on / 依赖: c.ord.card_le_preAleph, card_le_preAleph
-/
theorem le_preAleph_ord (c : Cardinal) : c <= preAleph c.ord := by
  simpa using c.ord.card_le_preAleph

@[simp]
/--
theorem `lift_preAleph` / 定理 `lift_preAleph`

English:
theorem lift_preAleph
  given: (o : Ordinal.{u})
  statement: lift.{v} (preAleph o) = preAleph (Ordinal.lift.{v} o)
  proof: (preAleph.toInitialSeg.trans liftInitialSeg).eq
    (Ordinal.liftInitialSeg.trans preAleph.toInitialSeg) o

@[simp]

中文:
定理 lift_preAleph
  条件: (o : 序数.{u})
  结论: lift.{v} (preAleph o) = preAleph (序数.lift.{v} o)
  证明: (preAleph.toInitialSeg.trans liftInitialSeg).eq
    (Ordinal.liftInitialSeg.trans preAleph.toInitialSeg) o

@[simp]

Depends on / 依赖: Ordinal, Ordinal.liftInitialSeg.trans, liftInitialSeg, preAleph, preAleph.toInitialSeg, preAleph.toInitialSeg.trans, toInitialSeg
-/
theorem lift_preAleph (o : Ordinal.{u}) : lift.{v} (preAleph o) = preAleph (Ordinal.lift.{v} o) :=
  (preAleph.toInitialSeg.trans liftInitialSeg).eq
    (Ordinal.liftInitialSeg.trans preAleph.toInitialSeg) o

@[simp]
/--
theorem `_root_.Ordinal.lift_preOmega` / 定理 `_root_.Ordinal.lift_preOmega`

English:
theorem _root_.Ordinal.lift_preOmega
  given: (o : Ordinal.{u})
  proof: by
  rw [← ord_preAleph]; rw [lift_ord]; rw [lift_preAleph]; rw [ord_preAleph]

中文:
定理 _root_.序数.lift_preOmega
  条件: (o : 序数.{u})
  证明: by
  rw [← ord_preAleph]; rw [lift_ord]; rw [lift_preAleph]; rw [ord_preAleph]

Depends on / 依赖: lift_ord, lift_preAleph, ord_preAleph
-/
theorem _root_.Ordinal.lift_preOmega (o : Ordinal.{u}) :
    Ordinal.lift.{v} (preOmega o) = preOmega (Ordinal.lift.{v} o) := by
  rw [← ord_preAleph]; rw [lift_ord]; rw [lift_preAleph]; rw [ord_preAleph]

/--
theorem `isNormal_preAleph` / 定理 `isNormal_preAleph`

English:
theorem isNormal_preAleph
  statement: Order.IsNormal preAleph
  proof: OrderIso.isNormal _

中文:
定理 isNormal_preAleph
  结论: Order.是正规 preAleph
  证明: OrderIso.isNormal _

Depends on / 依赖: OrderIso, OrderIso.isNormal, isNormal
-/
theorem isNormal_preAleph : Order.IsNormal preAleph :=
  OrderIso.isNormal _

/--
theorem `preAleph_le_of_isSuccPrelimit` / 定理 `preAleph_le_of_isSuccPrelimit`

English:
theorem preAleph_le_of_isSuccPrelimit
  given: {o : Ordinal} (l : IsSuccPrelimit o) {c}
  proof: by
  obtain rfl | ho := eq_or_ne o 0
  · simp
  · exact isNormal_preAleph.le_iff_forall_le ⟨by simpa, l⟩

中文:
定理 preAleph_le_of_isSuccPrelimit
  条件: {o : 序数} (l : IsSuccPrelimit o) {c}
  证明: by
  obtain rfl | ho := eq_or_ne o 0
  · simp
  · exact isNormal_preAleph.le_iff_forall_le ⟨by simpa, l⟩

Depends on / 依赖: TopologicalSpace, eq_or_ne, hSpace, isNormal_preAleph, isNormal_preAleph.le_iff_forall_le, le_iff_forall_le
-/
theorem preAleph_le_of_isSuccPrelimit {o : Ordinal} (l : IsSuccPrelimit o) {c} :
    preAleph o <= c ↔ forall o' < o, preAleph o' <= c := by
  obtain rfl | ho := eq_or_ne o 0
  · simp
  · exact isNormal_preAleph.le_iff_forall_le ⟨by simpa, l⟩

/--
theorem `preAleph_limit` / 定理 `preAleph_limit`

English:
theorem preAleph_limit
  given: {o : Ordinal} (ho : IsSuccPrelimit o)
  proof: by
  obtain rfl | h := eq_or_ne o 0
  · simp
  · exact isNormal_preAleph.apply_of_isSuccLimit ⟨by simpa, ho⟩

中文:
定理 preAleph_limit
  条件: {o : 序数} (ho : IsSuccPrelimit o)
  证明: by
  obtain rfl | h := eq_or_ne o 0
  · simp
  · exact isNormal_preAleph.apply_of_isSuccLimit ⟨by simpa, ho⟩

Depends on / 依赖: apply_of_isSuccLimit, eq_or_ne, isNormal_preAleph, isNormal_preAleph.apply_of_isSuccLimit
-/
theorem preAleph_limit {o : Ordinal} (ho : IsSuccPrelimit o) :
    preAleph o = ⨆ a : Iio o, preAleph a := by
  obtain rfl | h := eq_or_ne o 0
  · simp
  · exact isNormal_preAleph.apply_of_isSuccLimit ⟨by simpa, ho⟩

/--
theorem `preAleph_le_of_strictMono` / 定理 `preAleph_le_of_strictMono`

English:
theorem preAleph_le_of_strictMono
  given: {f : Ordinal -> Cardinal} (hf : StrictMono f) (o : Ordinal)
  proof: by
  simpa using (hf.comp preAleph.symm.strictMono).id_le (preAleph o)

中文:
定理 preAleph_le_of_strictMono
  条件: {f : 序数 -> 基数} (hf : 严格递增 f) (o : 序数)
  证明: by
  simpa using (hf.comp preAleph.symm.strictMono).id_le (preAleph o)

Depends on / 依赖: hf.comp, id_le, preAleph, preAleph.symm.strictMono, strictMono
-/
theorem preAleph_le_of_strictMono {f : Ordinal -> Cardinal} (hf : StrictMono f) (o : Ordinal) :
    preAleph o <= f o := by
  simpa using (hf.comp preAleph.symm.strictMono).id_le (preAleph o)

/--
Definition of `aleph` / `aleph` 的定义

English:
definition aleph
  signature: : Ordinal ↪o Cardinal
  body: (OrderEmbedding.addLeft ω).trans preAleph

@[inherit_doc] scoped notation "ℵ_ " => aleph
recommended_spelling "aleph" for "ℵ_" in [aleph, «termℵ_»]

中文:
定义 aleph
  签名: : 序数 ↪o 基数
  定义体: (OrderEmbedding.addLeft ω).trans preAleph

@[inherit_doc] scoped notation "ℵ_ " => aleph
recommended_spelling "aleph" for "ℵ_" in [aleph, «termℵ_»]

Depends on / 依赖: OrderEmbedding, OrderEmbedding.addLeft, addLeft, preAleph
-/
def aleph : Ordinal ↪o Cardinal :=
  (OrderEmbedding.addLeft ω).trans preAleph

@[inherit_doc] scoped notation "ℵ_ " => aleph
recommended_spelling "aleph" for "ℵ_" in [aleph, «termℵ_»]

/-- `ℵ₁` is the first uncountable cardinal. -/
scoped notation "ℵ₁" => ℵ_ 1
recommended_spelling "aleph_one" for "ℵ₁" in [«termℵ₁»]

/--
theorem `aleph_eq_preAleph` / 定理 `aleph_eq_preAleph`

English:
theorem aleph_eq_preAleph
  given: (o : Ordinal)
  statement: ℵ_ o = preAleph (ω + o)
  proof: rfl

@[simp]

中文:
定理 aleph_eq_preAleph
  条件: (o : 序数)
  结论: ℵ_ o = preAleph (ω + o)
  证明: rfl

@[simp]
-/
theorem aleph_eq_preAleph (o : Ordinal) : ℵ_ o = preAleph (ω + o) :=
  rfl

@[simp]
/--
theorem `_root_.Ordinal.card_omega` / 定理 `_root_.Ordinal.card_omega`

English:
theorem _root_.Ordinal.card_omega
  given: (o : Ordinal)
  statement: (ω_ o).card = ℵ_ o
  proof: rfl

@[simp]

中文:
定理 _root_.序数.card_omega
  条件: (o : 序数)
  结论: (ω_ o).card = ℵ_ o
  证明: rfl

@[simp]
-/
theorem _root_.Ordinal.card_omega (o : Ordinal) : (ω_ o).card = ℵ_ o :=
  rfl

@[simp]
/--
theorem `preAleph_symm_aleph` / 定理 `preAleph_symm_aleph`

English:
theorem preAleph_symm_aleph
  given: (o : Ordinal)
  statement: preAleph.symm (ℵ_ o) = ω + o
  proof: preAleph.symm_apply_apply _

@[simp]

中文:
定理 preAleph_symm_aleph
  条件: (o : 序数)
  结论: preAleph.symm (ℵ_ o) = ω + o
  证明: preAleph.symm_apply_apply _

@[simp]

Depends on / 依赖: preAleph, preAleph.symm_apply_apply, symm_apply_apply
-/
theorem preAleph_symm_aleph (o : Ordinal) : preAleph.symm (ℵ_ o) = ω + o :=
  preAleph.symm_apply_apply _

@[simp]
/--
theorem `ord_aleph` / 定理 `ord_aleph`

English:
theorem ord_aleph
  given: (o : Ordinal)
  statement: (ℵ_ o).ord = ω_ o
  proof: ord_preAleph _

中文:
定理 ord_aleph
  条件: (o : 序数)
  结论: (ℵ_ o).ord = ω_ o
  证明: ord_preAleph _

Depends on / 依赖: ord_preAleph
-/
theorem ord_aleph (o : Ordinal) : (ℵ_ o).ord = ω_ o :=
  ord_preAleph _

/--
theorem `aleph_lt_aleph` / 定理 `aleph_lt_aleph`

English:
theorem aleph_lt_aleph
  given: {o₁ o₂ : Ordinal}
  statement: ℵ_ o₁ < ℵ_ o₂ ↔ o₁ < o₂
  proof: aleph.lt_iff_lt

中文:
定理 aleph_lt_aleph
  条件: {o₁ o₂ : 序数}
  结论: ℵ_ o₁ < ℵ_ o₂ ↔ o₁ < o₂
  证明: aleph.lt_iff_lt

Depends on / 依赖: aleph.lt_iff_lt, lt_iff_lt
-/
theorem aleph_lt_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ < ℵ_ o₂ ↔ o₁ < o₂ :=
  aleph.lt_iff_lt

/--
theorem `aleph_le_aleph` / 定理 `aleph_le_aleph`

English:
theorem aleph_le_aleph
  given: {o₁ o₂ : Ordinal}
  statement: ℵ_ o₁ <= ℵ_ o₂ ↔ o₁ <= o₂
  proof: aleph.le_iff_le

中文:
定理 aleph_le_aleph
  条件: {o₁ o₂ : 序数}
  结论: ℵ_ o₁ <= ℵ_ o₂ ↔ o₁ <= o₂
  证明: aleph.le_iff_le

Depends on / 依赖: aleph.le_iff_le, le_iff_le
-/
theorem aleph_le_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ <= ℵ_ o₂ ↔ o₁ <= o₂ :=
  aleph.le_iff_le

/--
theorem `aleph_max` / 定理 `aleph_max`

English:
theorem aleph_max
  given: (o₁ o₂ : Ordinal)
  statement: ℵ_ (max o₁ o₂) = max (ℵ_ o₁) (ℵ_ o₂)
  proof: aleph.monotone.map_max

中文:
定理 aleph_max
  条件: (o₁ o₂ : 序数)
  结论: ℵ_ (最大值 o₁ o₂) = 最大值 (ℵ_ o₁) (ℵ_ o₂)
  证明: aleph.monotone.map_max

Depends on / 依赖: aleph.monotone.map_max, map_max, monotone
-/
theorem aleph_max (o₁ o₂ : Ordinal) : ℵ_ (max o₁ o₂) = max (ℵ_ o₁) (ℵ_ o₂) :=
  aleph.monotone.map_max

/--
theorem `preAleph_le_aleph` / 定理 `preAleph_le_aleph`

English:
theorem preAleph_le_aleph
  given: (o : Ordinal)
  statement: preAleph o <= ℵ_ o
  proof: preAleph_le_preAleph.2 le_add_self

@[simp]

中文:
定理 preAleph_le_aleph
  条件: (o : 序数)
  结论: preAleph o <= ℵ_ o
  证明: preAleph_le_preAleph.2 le_add_self

@[simp]

Depends on / 依赖: le_add_self, preAleph_le_preAleph
-/
theorem preAleph_le_aleph (o : Ordinal) : preAleph o <= ℵ_ o :=
  preAleph_le_preAleph.2 le_add_self

@[simp]
/--
theorem `succ_aleph` / 定理 `succ_aleph`

English:
theorem succ_aleph
  given: (o : Ordinal)
  statement: succ (ℵ_ o) = ℵ_ (o + 1)
  proof: by
  rw [aleph_eq_preAleph]; rw [succ_preAleph]; rw [add_assoc]; rw [aleph_eq_preAleph]

@[deprecated succ_aleph (since := "2026-03-24")]

中文:
定理 succ_aleph
  条件: (o : 序数)
  结论: succ (ℵ_ o) = ℵ_ (o + 1)
  证明: by
  rw [aleph_eq_preAleph]; rw [succ_preAleph]; rw [add_assoc]; rw [aleph_eq_preAleph]

@[deprecated succ_aleph (since := "2026-03-24")]

Depends on / 依赖: add_assoc, aleph_eq_preAleph, succ_preAleph
-/
theorem succ_aleph (o : Ordinal) : succ (ℵ_ o) = ℵ_ (o + 1) := by
  rw [aleph_eq_preAleph]; rw [succ_preAleph]; rw [add_assoc]; rw [aleph_eq_preAleph]

@[deprecated succ_aleph (since := "2026-03-24")]
/--
theorem `aleph_add_one` / 定理 `aleph_add_one`

English:
theorem aleph_add_one
  given: (o : Ordinal)
  statement: ℵ_ (o + 1) = succ (ℵ_ o)
  proof: by
  simp

@[deprecated succ_aleph (since := "2026-03-24")]

中文:
定理 aleph_add_one
  条件: (o : 序数)
  结论: ℵ_ (o + 1) = succ (ℵ_ o)
  证明: by
  simp

@[deprecated succ_aleph (since := "2026-03-24")]
-/
theorem aleph_add_one (o : Ordinal) : ℵ_ (o + 1) = succ (ℵ_ o) := by
  simp

@[deprecated succ_aleph (since := "2026-03-24")]
/--
theorem `aleph_succ` / 定理 `aleph_succ`

English:
theorem aleph_succ
  given: (o : Ordinal)
  statement: ℵ_ (succ o) = succ (ℵ_ o)
  proof: (succ_aleph o).symm

@[simp]

中文:
定理 aleph_succ
  条件: (o : 序数)
  结论: ℵ_ (succ o) = succ (ℵ_ o)
  证明: (succ_aleph o).symm

@[simp]

Depends on / 依赖: succ_aleph
-/
theorem aleph_succ (o : Ordinal) : ℵ_ (succ o) = succ (ℵ_ o) :=
  (succ_aleph o).symm

@[simp]
/--
theorem `aleph_zero` / 定理 `aleph_zero`

English:
theorem aleph_zero
  statement: ℵ_ 0 = ℵ₀
  proof: by rw [aleph_eq_preAleph, add_zero, preAleph_omega0]

@[simp]

中文:
定理 aleph_zero
  结论: ℵ_ 0 = ℵ₀
  证明: by rw [aleph_eq_preAleph, add_zero, preAleph_omega0]

@[simp]

Depends on / 依赖: add_zero, aleph_eq_preAleph, preAleph_omega0
-/
theorem aleph_zero : ℵ_ 0 = ℵ₀ := by rw [aleph_eq_preAleph, add_zero, preAleph_omega0]

@[simp]
/--
theorem `lift_aleph` / 定理 `lift_aleph`

English:
theorem lift_aleph
  given: (o : Ordinal.{u})
  statement: lift.{v} (aleph o) = aleph (Ordinal.lift.{v} o)
  proof: by
  simp [aleph_eq_preAleph]

中文:
定理 lift_aleph
  条件: (o : 序数.{u})
  结论: lift.{v} (aleph o) = aleph (序数.lift.{v} o)
  证明: by
  simp [aleph_eq_preAleph]

Depends on / 依赖: aleph_eq_preAleph, continuous_trans
-/
theorem lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) = aleph (Ordinal.lift.{v} o) := by
  simp [aleph_eq_preAleph]

/-- For the theorem `lift ω = ω`, see `lift_omega0`. -/
@[simp]
/--
theorem `_root_.Ordinal.lift_omega` / 定理 `_root_.Ordinal.lift_omega`

English:
theorem _root_.Ordinal.lift_omega
  given: (o : Ordinal.{u})
  proof: by
  simp [omega_eq_preOmega]

中文:
定理 _root_.序数.lift_omega
  条件: (o : 序数.{u})
  证明: by
  simp [omega_eq_preOmega]

Depends on / 依赖: omega_eq_preOmega
-/
theorem _root_.Ordinal.lift_omega (o : Ordinal.{u}) :
    Ordinal.lift.{v} (ω_ o) = ω_ (Ordinal.lift.{v} o) := by
  simp [omega_eq_preOmega]

/--
theorem `isNormal_aleph` / 定理 `isNormal_aleph`

English:
theorem isNormal_aleph
  statement: Order.IsNormal aleph
  proof: isNormal_preAleph.comp (isNormal_add_right _)

中文:
定理 isNormal_aleph
  结论: Order.是正规 aleph
  证明: isNormal_preAleph.comp (isNormal_add_right _)

Depends on / 依赖: isNormal_add_right, isNormal_preAleph, isNormal_preAleph.comp
-/
theorem isNormal_aleph : Order.IsNormal aleph :=
  isNormal_preAleph.comp (isNormal_add_right _)

/--
theorem `aleph_limit` / 定理 `aleph_limit`

English:
theorem aleph_limit
  given: {o : Ordinal} (ho : IsSuccLimit o)
  statement: ℵ_ o = ⨆ a : Iio o, ℵ_ a
  proof: isNormal_aleph.apply_of_isSuccLimit ho

@[simp]

中文:
定理 aleph_limit
  条件: {o : 序数} (ho : 是SuccLimit o)
  结论: ℵ_ o = ⨆ a : 左无界右开区间 o, ℵ_ a
  证明: isNormal_aleph.apply_of_isSuccLimit ho

@[simp]

Depends on / 依赖: apply_of_isSuccLimit, isNormal_aleph, isNormal_aleph.apply_of_isSuccLimit
-/
theorem aleph_limit {o : Ordinal} (ho : IsSuccLimit o) : ℵ_ o = ⨆ a : Iio o, ℵ_ a :=
  isNormal_aleph.apply_of_isSuccLimit ho

@[simp]
/--
theorem `aleph0_le_aleph` / 定理 `aleph0_le_aleph`

English:
theorem aleph0_le_aleph
  given: (o : Ordinal)
  statement: ℵ₀ <= ℵ_ o
  proof: by
  rw [aleph_eq_preAleph]; rw [aleph0_le_preAleph]
  exact le_self_add

@[simp]

中文:
定理 aleph0_le_aleph
  条件: (o : 序数)
  结论: ℵ₀ <= ℵ_ o
  证明: by
  rw [aleph_eq_preAleph]; rw [aleph0_le_preAleph]
  exact le_self_add

@[simp]

Depends on / 依赖: aleph0_le_preAleph, aleph_eq_preAleph, le_self_add
-/
theorem aleph0_le_aleph (o : Ordinal) : ℵ₀ <= ℵ_ o := by
  rw [aleph_eq_preAleph]; rw [aleph0_le_preAleph]
  exact le_self_add

@[simp]
/--
theorem `aleph0_lt_aleph` / 定理 `aleph0_lt_aleph`

English:
theorem aleph0_lt_aleph
  given: {o : Ordinal}
  statement: ℵ₀ < ℵ_ o ↔ 0 < o
  proof: by
  rw [← aleph_zero]; rw [aleph_lt_aleph]

中文:
定理 aleph0_lt_aleph
  条件: {o : 序数}
  结论: ℵ₀ < ℵ_ o ↔ 0 < o
  证明: by
  rw [← aleph_zero]; rw [aleph_lt_aleph]

Depends on / 依赖: aleph_lt_aleph, aleph_zero
-/
theorem aleph0_lt_aleph {o : Ordinal} : ℵ₀ < ℵ_ o ↔ 0 < o := by
  rw [← aleph_zero]; rw [aleph_lt_aleph]

/--
theorem `aleph_pos` / 定理 `aleph_pos`

English:
theorem aleph_pos
  given: (o : Ordinal)
  statement: 0 < ℵ_ o
  proof: aleph0_pos.trans_le (aleph0_le_aleph o)

中文:
定理 aleph_pos
  条件: (o : 序数)
  结论: 0 < ℵ_ o
  证明: aleph0_pos.trans_le (aleph0_le_aleph o)

Depends on / 依赖: aleph0_le_aleph, aleph0_pos, aleph0_pos.trans_le, trans_le
-/
theorem aleph_pos (o : Ordinal) : 0 < ℵ_ o :=
  aleph0_pos.trans_le (aleph0_le_aleph o)

/--
theorem `_root_.Ordinal.card_le_aleph` / 定理 `_root_.Ordinal.card_le_aleph`

English:
theorem _root_.Ordinal.card_le_aleph
  given: (o : Ordinal)
  statement: o.card <= ℵ_ o
  proof: o.card_le_preAleph.trans (preAleph_le_aleph o)

中文:
定理 _root_.序数.card_le_aleph
  条件: (o : 序数)
  结论: o.card <= ℵ_ o
  证明: o.card_le_preAleph.trans (preAleph_le_aleph o)

Depends on / 依赖: card_le_preAleph, o.card_le_preAleph.trans, preAleph_le_aleph
-/
theorem _root_.Ordinal.card_le_aleph (o : Ordinal) : o.card <= ℵ_ o :=
  o.card_le_preAleph.trans (preAleph_le_aleph o)

/--
theorem `le_aleph_ord` / 定理 `le_aleph_ord`

English:
theorem le_aleph_ord
  given: (c : Cardinal)
  statement: c <= ℵ_ c.ord
  proof: by
  simpa using c.ord.card_le_aleph

@[simp]

中文:
定理 le_aleph_ord
  条件: (c : 基数)
  结论: c <= ℵ_ c.ord
  证明: by
  simpa using c.ord.card_le_aleph

@[simp]

Depends on / 依赖: c.ord.card_le_aleph, card_le_aleph
-/
theorem le_aleph_ord (c : Cardinal) : c <= ℵ_ c.ord := by
  simpa using c.ord.card_le_aleph

@[simp]
/--
theorem `aleph_toNat` / 定理 `aleph_toNat`

English:
theorem aleph_toNat
  given: (o : Ordinal)
  statement: toNat (ℵ_ o) = 0
  proof: toNat_apply_of_aleph0_le aleph0_le_aleph o

@[simp]

中文:
定理 aleph_to自然数
  条件: (o : 序数)
  结论: to自然数 (ℵ_ o) = 0
  证明: toNat_apply_of_aleph0_le aleph0_le_aleph o

@[simp]

Depends on / 依赖: aleph0_le_aleph, toNat_apply_of_aleph0_le
-/
theorem aleph_toNat (o : Ordinal) : toNat (ℵ_ o) = 0 :=
toNat_apply_of_aleph0_le aleph0_le_aleph o

@[simp]
/--
theorem `aleph_toENat` / 定理 `aleph_toENat`

English:
theorem aleph_toENat
  given: (o : Ordinal)
  statement: toENat (ℵ_ o) = ⊤
  proof: (toENat_eq_top.2 (aleph0_le_aleph o))

中文:
定理 aleph_toE自然数
  条件: (o : 序数)
  结论: toE自然数 (ℵ_ o) = ⊤
  证明: (toENat_eq_top.2 (aleph0_le_aleph o))

Depends on / 依赖: aleph0_le_aleph, toENat_eq_top
-/
theorem aleph_toENat (o : Ordinal) : toENat (ℵ_ o) = ⊤ :=
  (toENat_eq_top.2 (aleph0_le_aleph o))

/--
theorem `isSuccLimit_omega` / 定理 `isSuccLimit_omega`

English:
theorem isSuccLimit_omega
  given: (o : Ordinal)
  statement: IsSuccLimit (ω_ o)
  proof: by
  rw [← ord_aleph]
  exact isSuccLimit_ord (aleph0_le_aleph _)

@[simp]

中文:
定理 isSuccLimit_omega
  条件: (o : 序数)
  结论: 是SuccLimit (ω_ o)
  证明: by
  rw [← ord_aleph]
  exact isSuccLimit_ord (aleph0_le_aleph _)

@[simp]

Depends on / 依赖: aleph0_le_aleph, isSuccLimit_ord, ord_aleph
-/
theorem isSuccLimit_omega (o : Ordinal) : IsSuccLimit (ω_ o) := by
  rw [← ord_aleph]
  exact isSuccLimit_ord (aleph0_le_aleph _)

@[simp]
/--
theorem `range_aleph` / 定理 `range_aleph`

English:
theorem range_aleph
  statement: range aleph = Set.Ici ℵ₀
  proof: by
  ext c
  refine ⟨fun ⟨o, e⟩ => e ▸ aleph0_le_aleph _, fun hc => ⟨preAleph.symm c - ω, ?_⟩⟩
  rw [aleph_eq_preAleph]; rw [Ordinal.add_sub_cancel_of_le]; rw [preAleph.apply_symm_apply]
  rwa [← aleph0_le_preAleph, preAleph.apply_symm_apply]

中文:
定理 range_aleph
  结论: range aleph = 集合.左闭右无界区间 ℵ₀
  证明: by
  ext c
  refine ⟨fun ⟨o, e⟩ => e ▸ aleph0_le_aleph _, fun hc => ⟨preAleph.symm c - ω, ?_⟩⟩
  rw [aleph_eq_preAleph]; rw [Ordinal.add_sub_cancel_of_le]; rw [preAleph.apply_symm_apply]
  rwa [← aleph0_le_preAleph, preAleph.apply_symm_apply]

Depends on / 依赖: Ordinal, Ordinal.add_sub_cancel_of_le, add_sub_cancel_of_le, aleph0_le_aleph, aleph0_le_preAleph, aleph_eq_preAleph, apply_symm_apply, preAleph, preAleph.apply_symm_apply, preAleph.symm
-/
theorem range_aleph : range aleph = Set.Ici ℵ₀ := by
  ext c
  refine ⟨fun ⟨o, e⟩ => e ▸ aleph0_le_aleph _, fun hc => ⟨preAleph.symm c - ω, ?_⟩⟩
  rw [aleph_eq_preAleph]; rw [Ordinal.add_sub_cancel_of_le]; rw [preAleph.apply_symm_apply]
  rwa [← aleph0_le_preAleph, preAleph.apply_symm_apply]

/--
theorem `mem_range_aleph_iff` / 定理 `mem_range_aleph_iff`

English:
theorem mem_range_aleph_iff
  given: {c : Cardinal}
  statement: c in range aleph ↔ ℵ₀ <= c
  proof: by
  rw [range_aleph]; rw [mem_Ici]

中文:
定理 mem_range_aleph_iff
  条件: {c : 基数}
  结论: c in range aleph ↔ ℵ₀ <= c
  证明: by
  rw [range_aleph]; rw [mem_Ici]

Depends on / 依赖: mem_Ici, range_aleph
-/
theorem mem_range_aleph_iff {c : Cardinal} : c in range aleph ↔ ℵ₀ <= c := by
  rw [range_aleph]; rw [mem_Ici]

/--
theorem `lt_omega_iff_card_lt` / 定理 `lt_omega_iff_card_lt`

English:
theorem lt_omega_iff_card_lt
  given: {x o : Ordinal}
  statement: x < ω_ o ↔ x.card < ℵ_ o
  proof: by
  rw [← (isInitial_omega o).card_lt_card]; rw [card_omega]

@[simp]

中文:
定理 lt_omega_iff_card_lt
  条件: {x o : 序数}
  结论: x < ω_ o ↔ x.card < ℵ_ o
  证明: by
  rw [← (isInitial_omega o).card_lt_card]; rw [card_omega]

@[simp]

Depends on / 依赖: card_lt_card, card_omega, isInitial_omega
-/
theorem lt_omega_iff_card_lt {x o : Ordinal} : x < ω_ o ↔ x.card < ℵ_ o := by
  rw [← (isInitial_omega o).card_lt_card]; rw [card_omega]

@[simp]
/--
theorem `succ_aleph0` / 定理 `succ_aleph0`

English:
theorem succ_aleph0
  statement: succ ℵ₀ = ℵ₁
  proof: by
  rw [← aleph_zero]; rw [succ_aleph]; rw [zero_add]

@[simp]

中文:
定理 succ_aleph0
  结论: succ ℵ₀ = ℵ₁
  证明: by
  rw [← aleph_zero]; rw [succ_aleph]; rw [zero_add]

@[simp]

Depends on / 依赖: aleph_zero, succ_aleph, zero_add
-/
theorem succ_aleph0 : succ ℵ₀ = ℵ₁ := by
  rw [← aleph_zero]; rw [succ_aleph]; rw [zero_add]

@[simp]
/--
theorem `aleph_one_le_iff` / 定理 `aleph_one_le_iff`

English:
theorem aleph_one_le_iff
  given: {c : Cardinal}
  statement: ℵ₁ <= c ↔ ℵ₀ < c
  proof: by
  rw [← succ_aleph0]; rw [succ_le_iff]

@[simp]

中文:
定理 aleph_one_le_iff
  条件: {c : 基数}
  结论: ℵ₁ <= c ↔ ℵ₀ < c
  证明: by
  rw [← succ_aleph0]; rw [succ_le_iff]

@[simp]

Depends on / 依赖: succ_aleph0, succ_le_iff
-/
theorem aleph_one_le_iff {c : Cardinal} : ℵ₁ <= c ↔ ℵ₀ < c := by
  rw [← succ_aleph0]; rw [succ_le_iff]

@[simp]
/--
theorem `lt_aleph_one_iff` / 定理 `lt_aleph_one_iff`

English:
theorem lt_aleph_one_iff
  given: {c : Cardinal}
  statement: c < ℵ₁ ↔ c <= ℵ₀
  proof: by
  rw [← succ_aleph0]; rw [lt_succ_iff]

中文:
定理 lt_aleph_one_iff
  条件: {c : 基数}
  结论: c < ℵ₁ ↔ c <= ℵ₀
  证明: by
  rw [← succ_aleph0]; rw [lt_succ_iff]

Depends on / 依赖: lt_succ_iff, succ_aleph0
-/
theorem lt_aleph_one_iff {c : Cardinal} : c < ℵ₁ ↔ c <= ℵ₀ := by
  rw [← succ_aleph0]; rw [lt_succ_iff]

/--
theorem `aleph0_lt_aleph_one` / 定理 `aleph0_lt_aleph_one`

English:
theorem aleph0_lt_aleph_one
  statement: ℵ₀ < ℵ₁
  proof: by simp

@[deprecated aleph_one_le_iff (since := "2026-03-23")]

中文:
定理 aleph0_lt_aleph_one
  结论: ℵ₀ < ℵ₁
  证明: by simp

@[deprecated aleph_one_le_iff (since := "2026-03-23")]
-/
theorem aleph0_lt_aleph_one : ℵ₀ < ℵ₁ := by simp

@[deprecated aleph_one_le_iff (since := "2026-03-23")]
/--
theorem `aleph0_lt_iff_aleph_one_le` / 定理 `aleph0_lt_iff_aleph_one_le`

English:
theorem aleph0_lt_iff_aleph_one_le
  given: {c}
  statement: ℵ₀ < c ↔ ℵ₁ <= c
  proof: aleph_one_le_iff.symm

@[deprecated aleph0_lt_mk_iff (since := "2026-03-23")]

中文:
定理 aleph0_lt_iff_aleph_one_le
  条件: {c}
  结论: ℵ₀ < c ↔ ℵ₁ <= c
  证明: aleph_one_le_iff.symm

@[deprecated aleph0_lt_mk_iff (since := "2026-03-23")]

Depends on / 依赖: aleph_one_le_iff, aleph_one_le_iff.symm
-/
theorem aleph0_lt_iff_aleph_one_le {c} : ℵ₀ < c ↔ ℵ₁ <= c :=
  aleph_one_le_iff.symm

@[deprecated aleph0_lt_mk_iff (since := "2026-03-23")]
/--
theorem `aleph1_le_mk_iff` / 定理 `aleph1_le_mk_iff`

English:
theorem aleph1_le_mk_iff
  given: {α : Type*}
  statement: ℵ₁ <= #α ↔ Uncountable α
  proof: by
  rw [aleph_one_le_iff]; rw [aleph0_lt_mk_iff]

@[deprecated aleph0_lt_mk (since := "2026-03-23")]

中文:
定理 aleph1_le_mk_iff
  条件: {α : 类型}
  结论: ℵ₁ <= #α ↔ 不可数 α
  证明: by
  rw [aleph_one_le_iff]; rw [aleph0_lt_mk_iff]

@[deprecated aleph0_lt_mk (since := "2026-03-23")]

Depends on / 依赖: aleph0_lt_mk_iff, aleph_one_le_iff
-/
theorem aleph1_le_mk_iff {α : Type*} : ℵ₁ <= #α ↔ Uncountable α := by
  rw [aleph_one_le_iff]; rw [aleph0_lt_mk_iff]

@[deprecated aleph0_lt_mk (since := "2026-03-23")]
/--
theorem `aleph1_le_mk` / 定理 `aleph1_le_mk`

English:
theorem aleph1_le_mk
  given: (α : Type*) [Uncountable α]
  statement: ℵ₁ <= #α
  proof: by
  simp

@[deprecated le_aleph0_iff_set_countable (since := "2026-03-23")]

中文:
定理 aleph1_le_mk
  条件: (α : 类型) [不可数 α]
  结论: ℵ₁ <= #α
  证明: by
  simp

@[deprecated le_aleph0_iff_set_countable (since := "2026-03-23")]
-/
theorem aleph1_le_mk (α : Type*) [Uncountable α] : ℵ₁ <= #α := by
  simp

@[deprecated le_aleph0_iff_set_countable (since := "2026-03-23")]
/--
theorem `countable_iff_lt_aleph_one` / 定理 `countable_iff_lt_aleph_one`

English:
theorem countable_iff_lt_aleph_one
  given: {α : Type*} (s : Set α)
  statement: s.Countable ↔ #s < ℵ₁
  proof: by
  rw [lt_aleph_one_iff]; rw [le_aleph0_iff_set_countable]

中文:
定理 countable_iff_lt_aleph_one
  条件: {α : 类型} (s : 集合 α)
  结论: s.可数 ↔ #s < ℵ₁
  证明: by
  rw [lt_aleph_one_iff]; rw [le_aleph0_iff_set_countable]

Depends on / 依赖: le_aleph0_iff_set_countable, lt_aleph_one_iff
-/
theorem countable_iff_lt_aleph_one {α : Type*} (s : Set α) : s.Countable ↔ #s < ℵ₁ := by
  rw [lt_aleph_one_iff]; rw [le_aleph0_iff_set_countable]

/--
theorem `preAleph_of_omega0_sq_le` / 定理 `preAleph_of_omega0_sq_le`

English:
theorem preAleph_of_omega0_sq_le
  given: {o : Ordinal} (ho : ω ^ 2 <= o)
  statement: preAleph o = ℵ_ o
  proof: by
  simpa [← ord_inj] using preOmega_of_omega0_sq_le ho

中文:
定理 preAleph_of_omega0_sq_le
  条件: {o : 序数} (ho : ω ^ 2 <= o)
  结论: preAleph o = ℵ_ o
  证明: by
  simpa [← ord_inj] using preOmega_of_omega0_sq_le ho

Depends on / 依赖: ord_inj, preOmega_of_omega0_sq_le
-/
theorem preAleph_of_omega0_sq_le {o : Ordinal} (ho : ω ^ 2 <= o) : preAleph o = ℵ_ o := by
  simpa [← ord_inj] using preOmega_of_omega0_sq_le ho

end Cardinal

/-! ### Beth cardinals -/

namespace Cardinal

/--
Definition of `preBeth` / `preBeth` 的定义

English:
definition preBeth
  signature: (o : Ordinal.{u})
  body: ⨆ a : Iio o, 2 ^ preBeth a
termination_by o
decreasing_by exact a.2

中文:
定义 preBeth
  签名: (o : 序数.{u})
  定义体: ⨆ a : Iio o, 2 ^ preBeth a
termination_by o
decreasing_by exact a.2

Depends on / 依赖: decreasing_by, preBeth, termination_by
-/
def preBeth (o : Ordinal.{u}) : Cardinal.{u} :=
  ⨆ a : Iio o, 2 ^ preBeth a
termination_by o
decreasing_by exact a.2

/--
theorem `preBeth_strictMono` / 定理 `preBeth_strictMono`

English:
theorem preBeth_strictMono
  statement: StrictMono preBeth
  proof: by
  intro a b h
  conv_rhs => rw [preBeth]
  rw [lt_ciSup_iff' bddAbove_of_small]
  exact ⟨⟨a, h⟩, cantor _⟩

中文:
定理 preBeth_strictMono
  结论: 严格递增 preBeth
  证明: by
  intro a b h
  conv_rhs => rw [preBeth]
  rw [lt_ciSup_iff' bddAbove_of_small]
  exact ⟨⟨a, h⟩, cantor _⟩

Depends on / 依赖: bddAbove_of_small, cantor, conv_rhs, lt_ciSup_iff, preBeth
-/
theorem preBeth_strictMono : StrictMono preBeth := by
  intro a b h
  conv_rhs => rw [preBeth]
  rw [lt_ciSup_iff' bddAbove_of_small]
  exact ⟨⟨a, h⟩, cantor _⟩

/--
theorem `preBeth_mono` / 定理 `preBeth_mono`

English:
theorem preBeth_mono
  statement: Monotone preBeth
  proof: preBeth_strictMono.monotone

中文:
定理 preBeth_mono
  结论: 递增 preBeth
  证明: preBeth_strictMono.monotone

Depends on / 依赖: monotone, preBeth_strictMono, preBeth_strictMono.monotone
-/
theorem preBeth_mono : Monotone preBeth :=
  preBeth_strictMono.monotone

/--
theorem `preAleph_le_preBeth` / 定理 `preAleph_le_preBeth`

English:
theorem preAleph_le_preBeth
  given: (o : Ordinal)
  statement: preAleph o <= preBeth o
  proof: preAleph_le_of_strictMono preBeth_strictMono o

@[simp]

中文:
定理 preAleph_le_preBeth
  条件: (o : 序数)
  结论: preAleph o <= preBeth o
  证明: preAleph_le_of_strictMono preBeth_strictMono o

@[simp]

Depends on / 依赖: preAleph_le_of_strictMono, preBeth_strictMono
-/
theorem preAleph_le_preBeth (o : Ordinal) : preAleph o <= preBeth o :=
  preAleph_le_of_strictMono preBeth_strictMono o

@[simp]
/--
theorem `preBeth_lt_preBeth` / 定理 `preBeth_lt_preBeth`

English:
theorem preBeth_lt_preBeth
  given: {o₁ o₂ : Ordinal}
  statement: preBeth o₁ < preBeth o₂ ↔ o₁ < o₂
  proof: preBeth_strictMono.lt_iff_lt

@[simp]

中文:
定理 preBeth_lt_preBeth
  条件: {o₁ o₂ : 序数}
  结论: preBeth o₁ < preBeth o₂ ↔ o₁ < o₂
  证明: preBeth_strictMono.lt_iff_lt

@[simp]

Depends on / 依赖: lt_iff_lt, preBeth_strictMono, preBeth_strictMono.lt_iff_lt
-/
theorem preBeth_lt_preBeth {o₁ o₂ : Ordinal} : preBeth o₁ < preBeth o₂ ↔ o₁ < o₂ :=
  preBeth_strictMono.lt_iff_lt

@[simp]
/--
theorem `preBeth_le_preBeth` / 定理 `preBeth_le_preBeth`

English:
theorem preBeth_le_preBeth
  given: {o₁ o₂ : Ordinal}
  statement: preBeth o₁ <= preBeth o₂ ↔ o₁ <= o₂
  proof: preBeth_strictMono.le_iff_le

@[simp]

中文:
定理 preBeth_le_preBeth
  条件: {o₁ o₂ : 序数}
  结论: preBeth o₁ <= preBeth o₂ ↔ o₁ <= o₂
  证明: preBeth_strictMono.le_iff_le

@[simp]

Depends on / 依赖: le_iff_le, preBeth_strictMono, preBeth_strictMono.le_iff_le
-/
theorem preBeth_le_preBeth {o₁ o₂ : Ordinal} : preBeth o₁ <= preBeth o₂ ↔ o₁ <= o₂ :=
  preBeth_strictMono.le_iff_le

@[simp]
/--
theorem `preBeth_inj` / 定理 `preBeth_inj`

English:
theorem preBeth_inj
  given: {o₁ o₂ : Ordinal}
  statement: preBeth o₁ = preBeth o₂ ↔ o₁ = o₂
  proof: preBeth_strictMono.injective.eq_iff

@[simp]

中文:
定理 preBeth_inj
  条件: {o₁ o₂ : 序数}
  结论: preBeth o₁ = preBeth o₂ ↔ o₁ = o₂
  证明: preBeth_strictMono.injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, injective, preBeth_strictMono, preBeth_strictMono.injective.eq_iff
-/
theorem preBeth_inj {o₁ o₂ : Ordinal} : preBeth o₁ = preBeth o₂ ↔ o₁ = o₂ :=
  preBeth_strictMono.injective.eq_iff

@[simp]
/--
theorem `preBeth_zero` / 定理 `preBeth_zero`

English:
theorem preBeth_zero
  statement: preBeth 0 = 0
  proof: by
  rw [preBeth]
  simp

@[simp]

中文:
定理 preBeth_zero
  结论: preBeth 0 = 0
  证明: by
  rw [preBeth]
  simp

@[simp]

Depends on / 依赖: preBeth
-/
theorem preBeth_zero : preBeth 0 = 0 := by
  rw [preBeth]
  simp

@[simp]
/--
theorem `preBeth_add_one` / 定理 `preBeth_add_one`

English:
theorem preBeth_add_one
  given: (o : Ordinal)
  statement: preBeth (o + 1) = 2 ^ preBeth o
  proof: by
  rw [preBeth]; rw [← succ_eq_add_one]; rw [Iio_succ]
  exact ciSup_Iic o fun x y h => power_le_power_left two_ne_zero (preBeth_mono h)

@[deprecated preBeth_add_one (since := "2026-05-26")]

中文:
定理 preBeth_add_one
  条件: (o : 序数)
  结论: preBeth (o + 1) = 2 ^ preBeth o
  证明: by
  rw [preBeth]; rw [← succ_eq_add_one]; rw [Iio_succ]
  exact ciSup_Iic o fun x y h => power_le_power_left two_ne_zero (preBeth_mono h)

@[deprecated preBeth_add_one (since := "2026-05-26")]

Depends on / 依赖: Iio_succ, ciSup_Iic, power_le_power_left, preBeth, preBeth_mono, succ_eq_add_one, two_ne_zero
-/
theorem preBeth_add_one (o : Ordinal) : preBeth (o + 1) = 2 ^ preBeth o := by
  rw [preBeth]; rw [← succ_eq_add_one]; rw [Iio_succ]
  exact ciSup_Iic o fun x y h => power_le_power_left two_ne_zero (preBeth_mono h)

@[deprecated preBeth_add_one (since := "2026-05-26")]
/--
theorem `preBeth_succ` / 定理 `preBeth_succ`

English:
theorem preBeth_succ
  given: (o : Ordinal)
  statement: preBeth (succ o) = 2 ^ preBeth o
  proof: preBeth_add_one o

中文:
定理 preBeth_succ
  条件: (o : 序数)
  结论: preBeth (succ o) = 2 ^ preBeth o
  证明: preBeth_add_one o

Depends on / 依赖: preBeth_add_one
-/
theorem preBeth_succ (o : Ordinal) : preBeth (succ o) = 2 ^ preBeth o :=
  preBeth_add_one o

/--
theorem `preBeth_limit` / 定理 `preBeth_limit`

English:
theorem preBeth_limit
  given: {o : Ordinal} (ho : IsSuccPrelimit o)
  proof: by
  rw [preBeth]
  apply (ciSup_mono bddAbove_of_small fun _ => (cantor _).le).antisymm'
  rw [ciSup_le_iff' bddAbove_of_small]
  intro a
  rw [← preBeth_add_one]
  exact le_ciSup bddAbove_of_small (⟨_, ho.succ_lt a.2⟩ : Iio o)

中文:
定理 preBeth_limit
  条件: {o : 序数} (ho : IsSuccPrelimit o)
  证明: by
  rw [preBeth]
  apply (ciSup_mono bddAbove_of_small fun _ => (cantor _).le).antisymm'
  rw [ciSup_le_iff' bddAbove_of_small]
  intro a
  rw [← preBeth_add_one]
  exact le_ciSup bddAbove_of_small (⟨_, ho.succ_lt a.2⟩ : Iio o)

Depends on / 依赖: antisymm, bddAbove_of_small, cantor, ciSup_le_iff, ciSup_mono, ho.succ_lt, le_ciSup, preBeth, preBeth_add_one, succ_lt
-/
theorem preBeth_limit {o : Ordinal} (ho : IsSuccPrelimit o) :
    preBeth o = ⨆ a : Iio o, preBeth a := by
  rw [preBeth]
  apply (ciSup_mono bddAbove_of_small fun _ => (cantor _).le).antisymm'
  rw [ciSup_le_iff' bddAbove_of_small]
  intro a
  rw [← preBeth_add_one]
  exact le_ciSup bddAbove_of_small (⟨_, ho.succ_lt a.2⟩ : Iio o)

/--
theorem `isNormal_preBeth` / 定理 `isNormal_preBeth`

English:
theorem isNormal_preBeth
  statement: Order.IsNormal preBeth
  proof: by
  rw [isNormal_iff]
  refine ⟨preBeth_strictMono, fun o ho => ?_⟩
  simp [preBeth_limit ho.isSuccPrelimit, ciSup_le_iff' bddAbove_of_small]

中文:
定理 isNormal_preBeth
  结论: Order.是正规 preBeth
  证明: by
  rw [isNormal_iff]
  refine ⟨preBeth_strictMono, fun o ho => ?_⟩
  simp [preBeth_limit ho.isSuccPrelimit, ciSup_le_iff' bddAbove_of_small]

Depends on / 依赖: bddAbove_of_small, ciSup_le_iff, ho.isSuccPrelimit, isNormal_iff, isSuccPrelimit, preBeth_limit, preBeth_strictMono
-/
theorem isNormal_preBeth : Order.IsNormal preBeth := by
  rw [isNormal_iff]
  refine ⟨preBeth_strictMono, fun o ho => ?_⟩
  simp [preBeth_limit ho.isSuccPrelimit, ciSup_le_iff' bddAbove_of_small]

/--
theorem `preBeth_nat` / 定理 `preBeth_nat`

English:
theorem preBeth_nat
  statement: forall n : Nat, preBeth n = (2 ^ ·)^[n] (0 : Nat)

中文:
定理 preBeth_nat
  结论: 对任意 n : 自然数, preBeth n = (2 ^ ·)^[n] (0 : 自然数)
-/
theorem preBeth_nat : forall n : Nat, preBeth n = (2 ^ ·)^[n] (0 : Nat)
  | 0 => by simp
  | n + 1 => by simp [Function.iterate_succ_apply', preBeth_nat]

@[simp]
/--
theorem `preBeth_one` / 定理 `preBeth_one`

English:
theorem preBeth_one
  statement: preBeth 1 = 1
  proof: by
  simpa using preBeth_nat 1

@[simp]

中文:
定理 preBeth_one
  结论: preBeth 1 = 1
  证明: by
  simpa using preBeth_nat 1

@[simp]

Depends on / 依赖: preBeth_nat
-/
theorem preBeth_one : preBeth 1 = 1 := by
  simpa using preBeth_nat 1

@[simp]
/--
theorem `preBeth_omega` / 定理 `preBeth_omega`

English:
theorem preBeth_omega
  statement: preBeth ω = ℵ₀
  proof: by
  apply le_antisymm
  · rw [preBeth_limit isSuccLimit_omega0.isSuccPrelimit, ciSup_le_iff' bddAbove_of_small]
    rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    rw [preBeth_nat]
    exact natCast_le_aleph0
  · simpa using preAleph_le_preBeth ω

@[simp]

中文:
定理 preBeth_omega
  结论: preBeth ω = ℵ₀
  证明: by
  apply le_antisymm
  · rw [preBeth_limit isSuccLimit_omega0.isSuccPrelimit, ciSup_le_iff' bddAbove_of_small]
    rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    rw [preBeth_nat]
    exact natCast_le_aleph0
  · simpa using preAleph_le_preBeth ω

@[simp]

Depends on / 依赖: bddAbove_of_small, ciSup_le_iff, isSuccLimit_omega0, isSuccLimit_omega0.isSuccPrelimit, isSuccPrelimit, le_antisymm, lt_omega0, natCast_le_aleph0, preAleph_le_preBeth, preBeth_limit, preBeth_nat
-/
theorem preBeth_omega : preBeth ω = ℵ₀ := by
  apply le_antisymm
  · rw [preBeth_limit isSuccLimit_omega0.isSuccPrelimit, ciSup_le_iff' bddAbove_of_small]
    rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    rw [preBeth_nat]
    exact natCast_le_aleph0
  · simpa using preAleph_le_preBeth ω

@[simp]
/--
theorem `preBeth_pos` / 定理 `preBeth_pos`

English:
theorem preBeth_pos
  given: {o : Ordinal}
  statement: 0 < preBeth o ↔ 0 < o
  proof: by
  simpa using preBeth_lt_preBeth (o₁ := 0)

中文:
定理 preBeth_pos
  条件: {o : 序数}
  结论: 0 < preBeth o ↔ 0 < o
  证明: by
  simpa using preBeth_lt_preBeth (o₁ := 0)

Depends on / 依赖: preBeth_lt_preBeth
-/
theorem preBeth_pos {o : Ordinal} : 0 < preBeth o ↔ 0 < o := by
  simpa using preBeth_lt_preBeth (o₁ := 0)

/--
theorem `_root_.Ordinal.card_le_preBeth` / 定理 `_root_.Ordinal.card_le_preBeth`

English:
theorem _root_.Ordinal.card_le_preBeth
  given: (o : Ordinal)
  statement: o.card <= preBeth o
  proof: o.card_le_preAleph.trans (preAleph_le_preBeth o)

中文:
定理 _root_.序数.card_le_preBeth
  条件: (o : 序数)
  结论: o.card <= preBeth o
  证明: o.card_le_preAleph.trans (preAleph_le_preBeth o)

Depends on / 依赖: card_le_preAleph, o.card_le_preAleph.trans, preAleph_le_preBeth
-/
theorem _root_.Ordinal.card_le_preBeth (o : Ordinal) : o.card <= preBeth o :=
  o.card_le_preAleph.trans (preAleph_le_preBeth o)

/--
theorem `le_preBeth_ord` / 定理 `le_preBeth_ord`

English:
theorem le_preBeth_ord
  given: (c : Cardinal)
  statement: c <= preBeth c.ord
  proof: by
  simpa using c.ord.card_le_preBeth

@[simp]

中文:
定理 le_preBeth_ord
  条件: (c : 基数)
  结论: c <= preBeth c.ord
  证明: by
  simpa using c.ord.card_le_preBeth

@[simp]

Depends on / 依赖: c.ord.card_le_preBeth, card_le_preBeth
-/
theorem le_preBeth_ord (c : Cardinal) : c <= preBeth c.ord := by
  simpa using c.ord.card_le_preBeth

@[simp]
/--
theorem `preBeth_eq_zero` / 定理 `preBeth_eq_zero`

English:
theorem preBeth_eq_zero
  given: {o : Ordinal}
  statement: preBeth o = 0 ↔ o = 0
  proof: by
  simpa using preBeth_inj (o₂ := 0)

@[simp]

中文:
定理 preBeth_eq_zero
  条件: {o : 序数}
  结论: preBeth o = 0 ↔ o = 0
  证明: by
  simpa using preBeth_inj (o₂ := 0)

@[simp]

Depends on / 依赖: preBeth_inj
-/
theorem preBeth_eq_zero {o : Ordinal} : preBeth o = 0 ↔ o = 0 := by
  simpa using preBeth_inj (o₂ := 0)

@[simp]
/--
theorem `isStrongPrelimit_preBeth` / 定理 `isStrongPrelimit_preBeth`

English:
theorem isStrongPrelimit_preBeth
  given: {o : Ordinal}
  proof: by
  refine ⟨?_, fun ho x hx => ?_⟩
  · contrapose!
    rw [not_isSuccPrelimit_iff_mem_range_succ]; rw [not_isStrongPrelimit_iff]
    rintro ⟨a, rfl⟩
    refine ⟨preBeth a, ?_, ?_⟩
    · rw [preBeth_lt_preBeth, lt_succ_iff]
    · simp
  · rw [preBeth_limit ho] at hx
    obtain ⟨a, ha⟩ := exists_lt_of_lt_ciSup' hx
    apply (preBeth_strictMono (ho.add_one_lt a.2)).trans_le'
    simpa using power_le_power_left two_ne_zero ha.le

@[simp]

中文:
定理 isStrongPrelimit_preBeth
  条件: {o : 序数}
  证明: by
  refine ⟨?_, fun ho x hx => ?_⟩
  · contrapose!
    rw [not_isSuccPrelimit_iff_mem_range_succ]; rw [not_isStrongPrelimit_iff]
    rintro ⟨a, rfl⟩
    refine ⟨preBeth a, ?_, ?_⟩
    · rw [preBeth_lt_preBeth, lt_succ_iff]
    · simp
  · rw [preBeth_limit ho] at hx
    obtain ⟨a, ha⟩ := exists_lt_of_lt_ciSup' hx
    apply (preBeth_strictMono (ho.add_one_lt a.2)).trans_le'
    simpa using power_le_power_left two_ne_zero ha.le

@[simp]

Depends on / 依赖: add_one_lt, contrapose, exists_lt_of_lt_ciSup, ha.le, ho.add_one_lt, lt_succ_iff, not_isStrongPrelimit_iff, not_isSuccPrelimit_iff_mem_range_succ, power_le_power_left, preBeth, preBeth_limit, preBeth_lt_preBeth, preBeth_strictMono, trans_le, two_ne_zero
-/
theorem isStrongPrelimit_preBeth {o : Ordinal} :
    IsStrongPrelimit (preBeth o) ↔ IsSuccPrelimit o := by
  refine ⟨?_, fun ho x hx => ?_⟩
  · contrapose!
    rw [not_isSuccPrelimit_iff_mem_range_succ]; rw [not_isStrongPrelimit_iff]
    rintro ⟨a, rfl⟩
    refine ⟨preBeth a, ?_, ?_⟩
    · rw [preBeth_lt_preBeth, lt_succ_iff]
    · simp
  · rw [preBeth_limit ho] at hx
    obtain ⟨a, ha⟩ := exists_lt_of_lt_ciSup' hx
    apply (preBeth_strictMono (ho.add_one_lt a.2)).trans_le'
    simpa using power_le_power_left two_ne_zero ha.le

@[simp]
/--
theorem `isStrongLimit_preBeth` / 定理 `isStrongLimit_preBeth`

English:
theorem isStrongLimit_preBeth
  given: {o : Ordinal}
  statement: IsStrongLimit (preBeth o) ↔ IsSuccLimit o
  proof: by
  rw [isStrongLimit_iff]; rw [isSuccLimit_iff]; rw [preBeth_eq_zero.ne]; rw [isStrongPrelimit_preBeth]

@[simp]

中文:
定理 isStrongLimit_preBeth
  条件: {o : 序数}
  结论: 是StrongLimit (preBeth o) ↔ 是SuccLimit o
  证明: by
  rw [isStrongLimit_iff]; rw [isSuccLimit_iff]; rw [preBeth_eq_zero.ne]; rw [isStrongPrelimit_preBeth]

@[simp]

Depends on / 依赖: isStrongLimit_iff, isStrongPrelimit_preBeth, isSuccLimit_iff, preBeth_eq_zero, preBeth_eq_zero.ne
-/
theorem isStrongLimit_preBeth {o : Ordinal} : IsStrongLimit (preBeth o) ↔ IsSuccLimit o := by
  rw [isStrongLimit_iff]; rw [isSuccLimit_iff]; rw [preBeth_eq_zero.ne]; rw [isStrongPrelimit_preBeth]

@[simp]
/--
theorem `lift_preBeth` / 定理 `lift_preBeth`

English:
theorem lift_preBeth
  given: (o : Ordinal)
  statement: lift.{v} (preBeth o) = preBeth (Ordinal.lift.{v} o)
  proof: by
  induction o using SuccOrder.prelimitRecOn with
  | succ o _ IH => simp [IH]
  | isSuccPrelimit o ho IH =>
    rw [preBeth_limit ho]; rw [preBeth_limit (isSuccPrelimit_lift.2 ho)]; rw [lift_iSup bddAbove_of_small]
    apply congrArg sSup
    ext x
    constructor <;> rintro ⟨⟨i, hi⟩, rfl⟩
    · refine ⟨⟨i.lift, ?_⟩, (IH _ hi).symm⟩
      simpa
    · obtain ⟨i, rfl⟩ := Ordinal.mem_range_lift_of_le hi.le
      rw [mem_Iio]; rw [Ordinal.lift_lt] at hi
      exact ⟨⟨i, hi⟩, IH _ hi⟩

中文:
定理 lift_preBeth
  条件: (o : 序数)
  结论: lift.{v} (preBeth o) = preBeth (序数.lift.{v} o)
  证明: by
  induction o using SuccOrder.prelimitRecOn with
  | succ o _ IH => simp [IH]
  | isSuccPrelimit o ho IH =>
    rw [preBeth_limit ho]; rw [preBeth_limit (isSuccPrelimit_lift.2 ho)]; rw [lift_iSup bddAbove_of_small]
    apply congrArg sSup
    ext x
    constructor <;> rintro ⟨⟨i, hi⟩, rfl⟩
    · refine ⟨⟨i.lift, ?_⟩, (IH _ hi).symm⟩
      simpa
    · obtain ⟨i, rfl⟩ := Ordinal.mem_range_lift_of_le hi.le
      rw [mem_Iio]; rw [Ordinal.lift_lt] at hi
      exact ⟨⟨i, hi⟩, IH _ hi⟩

Depends on / 依赖: Ordinal, Ordinal.lift_lt, Ordinal.mem_range_lift_of_le, SuccOrder, SuccOrder.prelimitRecOn, bddAbove_of_small, hi.le, i.lift, isSuccPrelimit, isSuccPrelimit_lift, lift_iSup, lift_lt, mem_Iio, mem_range_lift_of_le, preBeth_limit, prelimitRecOn
-/
theorem lift_preBeth (o : Ordinal) : lift.{v} (preBeth o) = preBeth (Ordinal.lift.{v} o) := by
  induction o using SuccOrder.prelimitRecOn with
  | succ o _ IH => simp [IH]
  | isSuccPrelimit o ho IH =>
    rw [preBeth_limit ho]; rw [preBeth_limit (isSuccPrelimit_lift.2 ho)]; rw [lift_iSup bddAbove_of_small]
    apply congrArg sSup
    ext x
    constructor <;> rintro ⟨⟨i, hi⟩, rfl⟩
    · refine ⟨⟨i.lift, ?_⟩, (IH _ hi).symm⟩
      simpa
    · obtain ⟨i, rfl⟩ := Ordinal.mem_range_lift_of_le hi.le
      rw [mem_Iio]; rw [Ordinal.lift_lt] at hi
      exact ⟨⟨i, hi⟩, IH _ hi⟩

/--
Definition of `beth` / `beth` 的定义

English:
definition beth
  signature: (o : Ordinal.{u})
  body: preBeth (ω + o)

@[inherit_doc] scoped notation "ℶ_ " => beth
recommended_spelling "beth" for "ℶ_" in [«termℶ_»]

中文:
定义 beth
  签名: (o : 序数.{u})
  定义体: preBeth (ω + o)

@[inherit_doc] scoped notation "ℶ_ " => beth
recommended_spelling "beth" for "ℶ_" in [«termℶ_»]

Depends on / 依赖: preBeth
-/
def beth (o : Ordinal.{u}) : Cardinal.{u} :=
  preBeth (ω + o)

@[inherit_doc] scoped notation "ℶ_ " => beth
recommended_spelling "beth" for "ℶ_" in [«termℶ_»]

/--
theorem `beth_eq_preBeth` / 定理 `beth_eq_preBeth`

English:
theorem beth_eq_preBeth
  given: (o : Ordinal)
  statement: beth o = preBeth (ω + o)
  proof: rfl

中文:
定理 beth_eq_preBeth
  条件: (o : 序数)
  结论: beth o = preBeth (ω + o)
  证明: rfl
-/
theorem beth_eq_preBeth (o : Ordinal) : beth o = preBeth (ω + o) :=
  rfl

/--
theorem `preBeth_le_beth` / 定理 `preBeth_le_beth`

English:
theorem preBeth_le_beth
  given: (o : Ordinal)
  statement: preBeth o <= ℶ_ o
  proof: preBeth_le_preBeth.2 le_add_self

中文:
定理 preBeth_le_beth
  条件: (o : 序数)
  结论: preBeth o <= ℶ_ o
  证明: preBeth_le_preBeth.2 le_add_self

Depends on / 依赖: le_add_self, preBeth_le_preBeth
-/
theorem preBeth_le_beth (o : Ordinal) : preBeth o <= ℶ_ o :=
  preBeth_le_preBeth.2 le_add_self

/--
theorem `beth_strictMono` / 定理 `beth_strictMono`

English:
theorem beth_strictMono
  statement: StrictMono beth
  proof: preBeth_strictMono.comp fun _ _ h => by gcongr

中文:
定理 beth_strictMono
  结论: 严格递增 beth
  证明: preBeth_strictMono.comp fun _ _ h => by gcongr

Depends on / 依赖: preBeth_strictMono, preBeth_strictMono.comp
-/
theorem beth_strictMono : StrictMono beth :=
  preBeth_strictMono.comp fun _ _ h => by gcongr

/--
theorem `beth_mono` / 定理 `beth_mono`

English:
theorem beth_mono
  statement: Monotone beth
  proof: beth_strictMono.monotone

@[simp]

中文:
定理 beth_mono
  结论: 递增 beth
  证明: beth_strictMono.monotone

@[simp]

Depends on / 依赖: beth_strictMono, beth_strictMono.monotone, monotone
-/
theorem beth_mono : Monotone beth :=
  beth_strictMono.monotone

@[simp]
/--
theorem `beth_lt_beth` / 定理 `beth_lt_beth`

English:
theorem beth_lt_beth
  given: {o₁ o₂ : Ordinal}
  statement: ℶ_ o₁ < ℶ_ o₂ ↔ o₁ < o₂
  proof: beth_strictMono.lt_iff_lt

@[simp]

中文:
定理 beth_lt_beth
  条件: {o₁ o₂ : 序数}
  结论: ℶ_ o₁ < ℶ_ o₂ ↔ o₁ < o₂
  证明: beth_strictMono.lt_iff_lt

@[simp]

Depends on / 依赖: beth_strictMono, beth_strictMono.lt_iff_lt, lt_iff_lt
-/
theorem beth_lt_beth {o₁ o₂ : Ordinal} : ℶ_ o₁ < ℶ_ o₂ ↔ o₁ < o₂ :=
  beth_strictMono.lt_iff_lt

@[simp]
/--
theorem `beth_le_beth` / 定理 `beth_le_beth`

English:
theorem beth_le_beth
  given: {o₁ o₂ : Ordinal}
  statement: ℶ_ o₁ <= ℶ_ o₂ ↔ o₁ <= o₂
  proof: beth_strictMono.le_iff_le

@[simp]

中文:
定理 beth_le_beth
  条件: {o₁ o₂ : 序数}
  结论: ℶ_ o₁ <= ℶ_ o₂ ↔ o₁ <= o₂
  证明: beth_strictMono.le_iff_le

@[simp]

Depends on / 依赖: beth_strictMono, beth_strictMono.le_iff_le, le_iff_le
-/
theorem beth_le_beth {o₁ o₂ : Ordinal} : ℶ_ o₁ <= ℶ_ o₂ ↔ o₁ <= o₂ :=
  beth_strictMono.le_iff_le

@[simp]
/--
theorem `beth_zero` / 定理 `beth_zero`

English:
theorem beth_zero
  statement: ℶ_ 0 = ℵ₀
  proof: by
  simp [beth]

@[simp]

中文:
定理 beth_zero
  结论: ℶ_ 0 = ℵ₀
  证明: by
  simp [beth]

@[simp]
-/
theorem beth_zero : ℶ_ 0 = ℵ₀ := by
  simp [beth]

@[simp]
/--
theorem `beth_add_one` / 定理 `beth_add_one`

English:
theorem beth_add_one
  given: (o : Ordinal)
  statement: ℶ_ (o + 1) = 2 ^ ℶ_ o
  proof: by
  simp [beth, ← add_assoc]

中文:
定理 beth_add_one
  条件: (o : 序数)
  结论: ℶ_ (o + 1) = 2 ^ ℶ_ o
  证明: by
  simp [beth, ← add_assoc]

Depends on / 依赖: add_assoc
-/
theorem beth_add_one (o : Ordinal) : ℶ_ (o + 1) = 2 ^ ℶ_ o := by
  simp [beth, ← add_assoc]

-- TODO; deprecate
/--
theorem `beth_succ` / 定理 `beth_succ`

English:
theorem beth_succ
  given: (o : Ordinal)
  statement: ℶ_ (succ o) = 2 ^ ℶ_ o
  proof: beth_add_one o

中文:
定理 beth_succ
  条件: (o : 序数)
  结论: ℶ_ (succ o) = 2 ^ ℶ_ o
  证明: beth_add_one o

Depends on / 依赖: beth_add_one
-/
theorem beth_succ (o : Ordinal) : ℶ_ (succ o) = 2 ^ ℶ_ o :=
  beth_add_one o

/--
theorem `isNormal_beth` / 定理 `isNormal_beth`

English:
theorem isNormal_beth
  statement: Order.IsNormal beth
  proof: isNormal_preBeth.comp (isNormal_add_right _)

中文:
定理 isNormal_beth
  结论: Order.是正规 beth
  证明: isNormal_preBeth.comp (isNormal_add_right _)

Depends on / 依赖: isNormal_add_right, isNormal_preBeth, isNormal_preBeth.comp
-/
theorem isNormal_beth : Order.IsNormal beth :=
  isNormal_preBeth.comp (isNormal_add_right _)

/--
theorem `beth_limit` / 定理 `beth_limit`

English:
theorem beth_limit
  given: {o : Ordinal} (ho : IsSuccLimit o)
  statement: ℶ_ o = ⨆ a : Iio o, ℶ_ a
  proof: isNormal_beth.apply_of_isSuccLimit ho

中文:
定理 beth_limit
  条件: {o : 序数} (ho : 是SuccLimit o)
  结论: ℶ_ o = ⨆ a : 左无界右开区间 o, ℶ_ a
  证明: isNormal_beth.apply_of_isSuccLimit ho

Depends on / 依赖: apply_of_isSuccLimit, isNormal_beth, isNormal_beth.apply_of_isSuccLimit
-/
theorem beth_limit {o : Ordinal} (ho : IsSuccLimit o) : ℶ_ o = ⨆ a : Iio o, ℶ_ a :=
  isNormal_beth.apply_of_isSuccLimit ho

/--
theorem `aleph_le_beth` / 定理 `aleph_le_beth`

English:
theorem aleph_le_beth
  given: (o : Ordinal)
  statement: ℵ_ o <= ℶ_ o
  proof: preAleph_le_preBeth _

中文:
定理 aleph_le_beth
  条件: (o : 序数)
  结论: ℵ_ o <= ℶ_ o
  证明: preAleph_le_preBeth _

Depends on / 依赖: preAleph_le_preBeth
-/
theorem aleph_le_beth (o : Ordinal) : ℵ_ o <= ℶ_ o :=
  preAleph_le_preBeth _

/--
theorem `aleph0_le_beth` / 定理 `aleph0_le_beth`

English:
theorem aleph0_le_beth
  given: (o : Ordinal)
  statement: ℵ₀ <= ℶ_ o
  proof: (aleph0_le_aleph o).trans aleph_le_beth o

中文:
定理 aleph0_le_beth
  条件: (o : 序数)
  结论: ℵ₀ <= ℶ_ o
  证明: (aleph0_le_aleph o).trans aleph_le_beth o

Depends on / 依赖: aleph0_le_aleph, aleph_le_beth
-/
theorem aleph0_le_beth (o : Ordinal) : ℵ₀ <= ℶ_ o :=
(aleph0_le_aleph o).trans aleph_le_beth o

/--
theorem `beth_pos` / 定理 `beth_pos`

English:
theorem beth_pos
  given: (o : Ordinal)
  statement: 0 < ℶ_ o
  proof: aleph0_pos.trans_le aleph0_le_beth o

中文:
定理 beth_pos
  条件: (o : 序数)
  结论: 0 < ℶ_ o
  证明: aleph0_pos.trans_le aleph0_le_beth o

Depends on / 依赖: aleph0_le_beth, aleph0_pos, aleph0_pos.trans_le, trans_le
-/
theorem beth_pos (o : Ordinal) : 0 < ℶ_ o :=
aleph0_pos.trans_le aleph0_le_beth o

/--
theorem `beth_ne_zero` / 定理 `beth_ne_zero`

English:
theorem beth_ne_zero
  given: (o : Ordinal)
  statement: ℶ_ o != 0
  proof: (beth_pos o).ne'

中文:
定理 beth_ne_zero
  条件: (o : 序数)
  结论: ℶ_ o != 0
  证明: (beth_pos o).ne'

Depends on / 依赖: beth_pos
-/
theorem beth_ne_zero (o : Ordinal) : ℶ_ o != 0 :=
  (beth_pos o).ne'

/--
theorem `_root_.Ordinal.card_le_beth` / 定理 `_root_.Ordinal.card_le_beth`

English:
theorem _root_.Ordinal.card_le_beth
  given: (o : Ordinal)
  statement: o.card <= ℶ_ o
  proof: o.card_le_aleph.trans (aleph_le_beth o)

中文:
定理 _root_.序数.card_le_beth
  条件: (o : 序数)
  结论: o.card <= ℶ_ o
  证明: o.card_le_aleph.trans (aleph_le_beth o)

Depends on / 依赖: aleph_le_beth, card_le_aleph, o.card_le_aleph.trans
-/
theorem _root_.Ordinal.card_le_beth (o : Ordinal) : o.card <= ℶ_ o :=
  o.card_le_aleph.trans (aleph_le_beth o)

/--
theorem `le_beth_ord` / 定理 `le_beth_ord`

English:
theorem le_beth_ord
  given: (c : Cardinal)
  statement: c <= ℶ_ c.ord
  proof: by
  simpa using c.ord.card_le_beth

@[simp]

中文:
定理 le_beth_ord
  条件: (c : 基数)
  结论: c <= ℶ_ c.ord
  证明: by
  simpa using c.ord.card_le_beth

@[simp]

Depends on / 依赖: c.ord.card_le_beth, card_le_beth
-/
theorem le_beth_ord (c : Cardinal) : c <= ℶ_ c.ord := by
  simpa using c.ord.card_le_beth

@[simp]
/--
theorem `isStrongLimit_beth` / 定理 `isStrongLimit_beth`

English:
theorem isStrongLimit_beth
  given: {o : Ordinal}
  statement: IsStrongLimit (ℶ_ o) ↔ IsSuccPrelimit o
  proof: by
  rw [beth_eq_preBeth]; rw [isStrongLimit_preBeth]; rw [isSuccLimit_add_iff_of_isSuccLimit isSuccLimit_omega0]

@[simp]

中文:
定理 isStrongLimit_beth
  条件: {o : 序数}
  结论: 是StrongLimit (ℶ_ o) ↔ IsSuccPrelimit o
  证明: by
  rw [beth_eq_preBeth]; rw [isStrongLimit_preBeth]; rw [isSuccLimit_add_iff_of_isSuccLimit isSuccLimit_omega0]

@[simp]

Depends on / 依赖: beth_eq_preBeth, isStrongLimit_preBeth, isSuccLimit_add_iff_of_isSuccLimit, isSuccLimit_omega0
-/
theorem isStrongLimit_beth {o : Ordinal} : IsStrongLimit (ℶ_ o) ↔ IsSuccPrelimit o := by
  rw [beth_eq_preBeth]; rw [isStrongLimit_preBeth]; rw [isSuccLimit_add_iff_of_isSuccLimit isSuccLimit_omega0]

@[simp]
/--
theorem `lift_beth` / 定理 `lift_beth`

English:
theorem lift_beth
  given: (o : Ordinal)
  statement: lift.{v} (ℶ_ o) = ℶ_ (Ordinal.lift.{v} o)
  proof: by
  rw [beth_eq_preBeth]; rw [beth_eq_preBeth]; rw [lift_preBeth]; rw [Ordinal.lift_add]; rw [lift_omega0]

中文:
定理 lift_beth
  条件: (o : 序数)
  结论: lift.{v} (ℶ_ o) = ℶ_ (序数.lift.{v} o)
  证明: by
  rw [beth_eq_preBeth]; rw [beth_eq_preBeth]; rw [lift_preBeth]; rw [Ordinal.lift_add]; rw [lift_omega0]

Depends on / 依赖: Ordinal, Ordinal.lift_add, beth_eq_preBeth, lift_add, lift_omega0, lift_preBeth
-/
theorem lift_beth (o : Ordinal) : lift.{v} (ℶ_ o) = ℶ_ (Ordinal.lift.{v} o) := by
  rw [beth_eq_preBeth]; rw [beth_eq_preBeth]; rw [lift_preBeth]; rw [Ordinal.lift_add]; rw [lift_omega0]

/--
theorem `preBeth_of_omega0_sq_le` / 定理 `preBeth_of_omega0_sq_le`

English:
theorem preBeth_of_omega0_sq_le
  given: {o : Ordinal} (ho : ω ^ 2 <= o)
  statement: preBeth o = ℶ_ o
  proof: by
  rw [← opow_natCast] at ho
  rw [beth]; rw [add_of_omega0_opow_le _ ho]
  apply left_lt_opow one_lt_omega0
  simp

中文:
定理 preBeth_of_omega0_sq_le
  条件: {o : 序数} (ho : ω ^ 2 <= o)
  结论: preBeth o = ℶ_ o
  证明: by
  rw [← opow_natCast] at ho
  rw [beth]; rw [add_of_omega0_opow_le _ ho]
  apply left_lt_opow one_lt_omega0
  simp

Depends on / 依赖: add_of_omega0_opow_le, left_lt_opow, one_lt_omega0, opow_natCast
-/
theorem preBeth_of_omega0_sq_le {o : Ordinal} (ho : ω ^ 2 <= o) : preBeth o = ℶ_ o := by
  rw [← opow_natCast] at ho
  rw [beth]; rw [add_of_omega0_opow_le _ ho]
  apply left_lt_opow one_lt_omega0
  simp

/-! ### Simp lemmas with `lift` -/

section lift
variable {c : Cardinal.{u}} {n : Nat}

@[deprecated aleph0_lt_lift (since := "2026-03-23")]
/--
theorem `aleph_one_le_lift` / 定理 `aleph_one_le_lift`

English:
theorem aleph_one_le_lift
  statement: ℵ₁ <= lift.{v} c ↔ ℵ₁ <= c
  proof: by
  simp

@[simp]

中文:
定理 aleph_one_le_lift
  结论: ℵ₁ <= lift.{v} c ↔ ℵ₁ <= c
  证明: by
  simp

@[simp]
-/
theorem aleph_one_le_lift : ℵ₁ <= lift.{v} c ↔ ℵ₁ <= c := by
  simp

@[simp]
/--
theorem `lift_le_aleph_one` / 定理 `lift_le_aleph_one`

English:
theorem lift_le_aleph_one
  statement: lift.{v} c <= ℵ₁ ↔ c <= ℵ₁
  proof: by
  simpa using lift_le (b := ℵ₁)

@[simp]

中文:
定理 lift_le_aleph_one
  结论: lift.{v} c <= ℵ₁ ↔ c <= ℵ₁
  证明: by
  simpa using lift_le (b := ℵ₁)

@[simp]

Depends on / 依赖: lift_le
-/
theorem lift_le_aleph_one : lift.{v} c <= ℵ₁ ↔ c <= ℵ₁ := by
  simpa using lift_le (b := ℵ₁)

@[simp]
/--
theorem `aleph_one_lt_lift` / 定理 `aleph_one_lt_lift`

English:
theorem aleph_one_lt_lift
  statement: ℵ₁ < lift.{v} c ↔ ℵ₁ < c
  proof: by
  simpa using lift_lt (a := ℵ₁)

@[deprecated lift_le_aleph0 (since := "2026-03-23")]

中文:
定理 aleph_one_lt_lift
  结论: ℵ₁ < lift.{v} c ↔ ℵ₁ < c
  证明: by
  simpa using lift_lt (a := ℵ₁)

@[deprecated lift_le_aleph0 (since := "2026-03-23")]

Depends on / 依赖: lift_lt
-/
theorem aleph_one_lt_lift : ℵ₁ < lift.{v} c ↔ ℵ₁ < c := by
  simpa using lift_lt (a := ℵ₁)

@[deprecated lift_le_aleph0 (since := "2026-03-23")]
/--
theorem `lift_lt_aleph_one` / 定理 `lift_lt_aleph_one`

English:
theorem lift_lt_aleph_one
  statement: lift.{v} c < ℵ₁ ↔ c < ℵ₁
  proof: by
  simp

@[simp]

中文:
定理 lift_lt_aleph_one
  结论: lift.{v} c < ℵ₁ ↔ c < ℵ₁
  证明: by
  simp

@[simp]
-/
theorem lift_lt_aleph_one : lift.{v} c < ℵ₁ ↔ c < ℵ₁ := by
  simp

@[simp]
/--
theorem `aleph_one_eq_lift` / 定理 `aleph_one_eq_lift`

English:
theorem aleph_one_eq_lift
  statement: ℵ₁ = lift.{v} c ↔ ℵ₁ = c
  proof: by
  simpa using lift_inj (a := ℵ₁)

@[simp]

中文:
定理 aleph_one_eq_lift
  结论: ℵ₁ = lift.{v} c ↔ ℵ₁ = c
  证明: by
  simpa using lift_inj (a := ℵ₁)

@[simp]

Depends on / 依赖: lift_inj
-/
theorem aleph_one_eq_lift : ℵ₁ = lift.{v} c ↔ ℵ₁ = c := by
  simpa using lift_inj (a := ℵ₁)

@[simp]
/--
theorem `lift_eq_aleph_one` / 定理 `lift_eq_aleph_one`

English:
theorem lift_eq_aleph_one
  statement: lift.{v} c = ℵ₁ ↔ c = ℵ₁
  proof: by
  simp [eqComm]

@[simp]

中文:
定理 lift_eq_aleph_one
  结论: lift.{v} c = ℵ₁ ↔ c = ℵ₁
  证明: by
  simp [eqComm]

@[simp]

Depends on / 依赖: eqComm
-/
theorem lift_eq_aleph_one : lift.{v} c = ℵ₁ ↔ c = ℵ₁ := by
  simp [eqComm]

@[simp]
/--
theorem `aleph_natCast_le_lift` / 定理 `aleph_natCast_le_lift`

English:
theorem aleph_natCast_le_lift
  statement: ℵ_ n <= lift.{v} c ↔ ℵ_ n <= c
  proof: by
  simpa using lift_le (a := ℵ_ n)

@[simp]

中文:
定理 aleph_natCast_le_lift
  结论: ℵ_ n <= lift.{v} c ↔ ℵ_ n <= c
  证明: by
  simpa using lift_le (a := ℵ_ n)

@[simp]

Depends on / 依赖: lift_le
-/
theorem aleph_natCast_le_lift : ℵ_ n <= lift.{v} c ↔ ℵ_ n <= c := by
  simpa using lift_le (a := ℵ_ n)

@[simp]
/--
theorem `lift_le_aleph_natCast` / 定理 `lift_le_aleph_natCast`

English:
theorem lift_le_aleph_natCast
  statement: lift.{v} c <= ℵ_ n ↔ c <= ℵ_ n
  proof: by
  simpa using lift_le (b := ℵ_ n)

@[simp]

中文:
定理 lift_le_aleph_natCast
  结论: lift.{v} c <= ℵ_ n ↔ c <= ℵ_ n
  证明: by
  simpa using lift_le (b := ℵ_ n)

@[simp]

Depends on / 依赖: lift_le
-/
theorem lift_le_aleph_natCast : lift.{v} c <= ℵ_ n ↔ c <= ℵ_ n := by
  simpa using lift_le (b := ℵ_ n)

@[simp]
/--
theorem `aleph_natCast_lt_lift` / 定理 `aleph_natCast_lt_lift`

English:
theorem aleph_natCast_lt_lift
  statement: ℵ_ n < lift.{v} c ↔ ℵ_ n < c
  proof: by
  simpa using lift_lt (a := ℵ_ n)

@[simp]

中文:
定理 aleph_natCast_lt_lift
  结论: ℵ_ n < lift.{v} c ↔ ℵ_ n < c
  证明: by
  simpa using lift_lt (a := ℵ_ n)

@[simp]

Depends on / 依赖: lift_lt
-/
theorem aleph_natCast_lt_lift : ℵ_ n < lift.{v} c ↔ ℵ_ n < c := by
  simpa using lift_lt (a := ℵ_ n)

@[simp]
/--
theorem `lift_lt_aleph_natCast` / 定理 `lift_lt_aleph_natCast`

English:
theorem lift_lt_aleph_natCast
  statement: lift.{v} c < ℵ_ n ↔ c < ℵ_ n
  proof: by
  simpa using lift_lt (b := ℵ_ n)

@[simp]

中文:
定理 lift_lt_aleph_natCast
  结论: lift.{v} c < ℵ_ n ↔ c < ℵ_ n
  证明: by
  simpa using lift_lt (b := ℵ_ n)

@[simp]

Depends on / 依赖: lift_lt
-/
theorem lift_lt_aleph_natCast : lift.{v} c < ℵ_ n ↔ c < ℵ_ n := by
  simpa using lift_lt (b := ℵ_ n)

@[simp]
/--
theorem `aleph_natCast_eq_lift` / 定理 `aleph_natCast_eq_lift`

English:
theorem aleph_natCast_eq_lift
  statement: ℵ_ n = lift.{v} c ↔ ℵ_ n = c
  proof: by
  simpa using lift_inj (a := ℵ_ n)

@[simp]

中文:
定理 aleph_natCast_eq_lift
  结论: ℵ_ n = lift.{v} c ↔ ℵ_ n = c
  证明: by
  simpa using lift_inj (a := ℵ_ n)

@[simp]

Depends on / 依赖: lift_inj
-/
theorem aleph_natCast_eq_lift : ℵ_ n = lift.{v} c ↔ ℵ_ n = c := by
  simpa using lift_inj (a := ℵ_ n)

@[simp]
/--
theorem `lift_eq_aleph_natCast` / 定理 `lift_eq_aleph_natCast`

English:
theorem lift_eq_aleph_natCast
  statement: lift.{v} c = ℵ_ n ↔ c = ℵ_ n
  proof: by
  simp [eqComm]

@[simp]

中文:
定理 lift_eq_aleph_natCast
  结论: lift.{v} c = ℵ_ n ↔ c = ℵ_ n
  证明: by
  simp [eqComm]

@[simp]

Depends on / 依赖: eqComm
-/
theorem lift_eq_aleph_natCast : lift.{v} c = ℵ_ n ↔ c = ℵ_ n := by
  simp [eqComm]

@[simp]
/--
theorem `aleph_ofNat_le_lift` / 定理 `aleph_ofNat_le_lift`

English:
theorem aleph_ofNat_le_lift
  given: [n.AtLeastTwo]
  statement: ℵ_ ofNat(n) <= lift.{v} c ↔ ℵ_ ofNat(n) <= c
  proof: aleph_natCast_le_lift

@[simp]

中文:
定理 aleph_of自然数_le_lift
  条件: [n.AtLeastTwo]
  结论: ℵ_ of自然数(n) <= lift.{v} c ↔ ℵ_ of自然数(n) <= c
  证明: aleph_natCast_le_lift

@[simp]

Depends on / 依赖: aleph_natCast_le_lift
-/
theorem aleph_ofNat_le_lift [n.AtLeastTwo] : ℵ_ ofNat(n) <= lift.{v} c ↔ ℵ_ ofNat(n) <= c :=
  aleph_natCast_le_lift

@[simp]
/--
theorem `lift_le_aleph_ofNat` / 定理 `lift_le_aleph_ofNat`

English:
theorem lift_le_aleph_ofNat
  given: [n.AtLeastTwo]
  statement: lift.{v} c <= ℵ_ ofNat(n) ↔ c <= ℵ_ ofNat(n)
  proof: lift_le_aleph_natCast

@[simp]

中文:
定理 lift_le_aleph_of自然数
  条件: [n.AtLeastTwo]
  结论: lift.{v} c <= ℵ_ of自然数(n) ↔ c <= ℵ_ of自然数(n)
  证明: lift_le_aleph_natCast

@[simp]

Depends on / 依赖: lift_le_aleph_natCast
-/
theorem lift_le_aleph_ofNat [n.AtLeastTwo] : lift.{v} c <= ℵ_ ofNat(n) ↔ c <= ℵ_ ofNat(n) :=
  lift_le_aleph_natCast

@[simp]
/--
theorem `aleph_ofNat_lt_lift` / 定理 `aleph_ofNat_lt_lift`

English:
theorem aleph_ofNat_lt_lift
  given: [n.AtLeastTwo]
  statement: ℵ_ ofNat(n) < lift.{v} c ↔ ℵ_ ofNat(n) < c
  proof: aleph_natCast_lt_lift

@[simp]

中文:
定理 aleph_of自然数_lt_lift
  条件: [n.AtLeastTwo]
  结论: ℵ_ of自然数(n) < lift.{v} c ↔ ℵ_ of自然数(n) < c
  证明: aleph_natCast_lt_lift

@[simp]

Depends on / 依赖: aleph_natCast_lt_lift
-/
theorem aleph_ofNat_lt_lift [n.AtLeastTwo] : ℵ_ ofNat(n) < lift.{v} c ↔ ℵ_ ofNat(n) < c :=
  aleph_natCast_lt_lift

@[simp]
/--
theorem `lift_lt_aleph_ofNat` / 定理 `lift_lt_aleph_ofNat`

English:
theorem lift_lt_aleph_ofNat
  given: [n.AtLeastTwo]
  statement: lift.{v} c < ℵ_ ofNat(n) ↔ c < ℵ_ ofNat(n)
  proof: lift_lt_aleph_natCast

@[simp]

中文:
定理 lift_lt_aleph_of自然数
  条件: [n.AtLeastTwo]
  结论: lift.{v} c < ℵ_ of自然数(n) ↔ c < ℵ_ of自然数(n)
  证明: lift_lt_aleph_natCast

@[simp]

Depends on / 依赖: lift_lt_aleph_natCast
-/
theorem lift_lt_aleph_ofNat [n.AtLeastTwo] : lift.{v} c < ℵ_ ofNat(n) ↔ c < ℵ_ ofNat(n) :=
  lift_lt_aleph_natCast

@[simp]
/--
theorem `aleph_ofNat_eq_lift` / 定理 `aleph_ofNat_eq_lift`

English:
theorem aleph_ofNat_eq_lift
  given: [n.AtLeastTwo]
  statement: ℵ_ ofNat(n) = lift.{v} c ↔ ℵ_ ofNat(n) = c
  proof: aleph_natCast_eq_lift

@[simp]

中文:
定理 aleph_of自然数_eq_lift
  条件: [n.AtLeastTwo]
  结论: ℵ_ of自然数(n) = lift.{v} c ↔ ℵ_ of自然数(n) = c
  证明: aleph_natCast_eq_lift

@[simp]

Depends on / 依赖: aleph_natCast_eq_lift
-/
theorem aleph_ofNat_eq_lift [n.AtLeastTwo] : ℵ_ ofNat(n) = lift.{v} c ↔ ℵ_ ofNat(n) = c :=
  aleph_natCast_eq_lift

@[simp]
/--
theorem `lift_eq_aleph_ofNat` / 定理 `lift_eq_aleph_ofNat`

English:
theorem lift_eq_aleph_ofNat
  given: [n.AtLeastTwo]
  statement: lift.{v} c = ℵ_ ofNat(n) ↔ c = ℵ_ ofNat(n)
  proof: lift_eq_aleph_natCast

@[simp]

中文:
定理 lift_eq_aleph_of自然数
  条件: [n.AtLeastTwo]
  结论: lift.{v} c = ℵ_ of自然数(n) ↔ c = ℵ_ of自然数(n)
  证明: lift_eq_aleph_natCast

@[simp]

Depends on / 依赖: lift_eq_aleph_natCast
-/
theorem lift_eq_aleph_ofNat [n.AtLeastTwo] : lift.{v} c = ℵ_ ofNat(n) ↔ c = ℵ_ ofNat(n) :=
  lift_eq_aleph_natCast

@[simp]
/--
theorem `beth_natCast_le_lift` / 定理 `beth_natCast_le_lift`

English:
theorem beth_natCast_le_lift
  statement: ℶ_ n <= lift.{v} c ↔ ℶ_ n <= c
  proof: by
  simpa using lift_le (a := ℶ_ n)

@[simp]

中文:
定理 beth_natCast_le_lift
  结论: ℶ_ n <= lift.{v} c ↔ ℶ_ n <= c
  证明: by
  simpa using lift_le (a := ℶ_ n)

@[simp]

Depends on / 依赖: lift_le
-/
theorem beth_natCast_le_lift : ℶ_ n <= lift.{v} c ↔ ℶ_ n <= c := by
  simpa using lift_le (a := ℶ_ n)

@[simp]
/--
theorem `lift_le_beth_natCast` / 定理 `lift_le_beth_natCast`

English:
theorem lift_le_beth_natCast
  statement: lift.{v} c <= ℶ_ n ↔ c <= ℶ_ n
  proof: by
  simpa using lift_le (b := ℶ_ n)

@[simp]

中文:
定理 lift_le_beth_natCast
  结论: lift.{v} c <= ℶ_ n ↔ c <= ℶ_ n
  证明: by
  simpa using lift_le (b := ℶ_ n)

@[simp]

Depends on / 依赖: lift_le
-/
theorem lift_le_beth_natCast : lift.{v} c <= ℶ_ n ↔ c <= ℶ_ n := by
  simpa using lift_le (b := ℶ_ n)

@[simp]
/--
theorem `beth_natCast_lt_lift` / 定理 `beth_natCast_lt_lift`

English:
theorem beth_natCast_lt_lift
  statement: ℶ_ n < lift.{v} c ↔ ℶ_ n < c
  proof: by
  simpa using lift_lt (a := ℶ_ n)

@[simp]

中文:
定理 beth_natCast_lt_lift
  结论: ℶ_ n < lift.{v} c ↔ ℶ_ n < c
  证明: by
  simpa using lift_lt (a := ℶ_ n)

@[simp]

Depends on / 依赖: lift_lt
-/
theorem beth_natCast_lt_lift : ℶ_ n < lift.{v} c ↔ ℶ_ n < c := by
  simpa using lift_lt (a := ℶ_ n)

@[simp]
/--
theorem `lift_lt_beth_natCast` / 定理 `lift_lt_beth_natCast`

English:
theorem lift_lt_beth_natCast
  statement: lift.{v} c < ℶ_ n ↔ c < ℶ_ n
  proof: by
  simpa using lift_lt (b := ℶ_ n)

@[simp]

中文:
定理 lift_lt_beth_natCast
  结论: lift.{v} c < ℶ_ n ↔ c < ℶ_ n
  证明: by
  simpa using lift_lt (b := ℶ_ n)

@[simp]

Depends on / 依赖: lift_lt
-/
theorem lift_lt_beth_natCast : lift.{v} c < ℶ_ n ↔ c < ℶ_ n := by
  simpa using lift_lt (b := ℶ_ n)

@[simp]
/--
theorem `beth_natCast_eq_lift` / 定理 `beth_natCast_eq_lift`

English:
theorem beth_natCast_eq_lift
  statement: ℶ_ n = lift.{v} c ↔ ℶ_ n = c
  proof: by
  simpa using lift_inj (a := ℶ_ n)

@[simp]

中文:
定理 beth_natCast_eq_lift
  结论: ℶ_ n = lift.{v} c ↔ ℶ_ n = c
  证明: by
  simpa using lift_inj (a := ℶ_ n)

@[simp]

Depends on / 依赖: lift_inj
-/
theorem beth_natCast_eq_lift : ℶ_ n = lift.{v} c ↔ ℶ_ n = c := by
  simpa using lift_inj (a := ℶ_ n)

@[simp]
/--
theorem `lift_eq_beth_natCast` / 定理 `lift_eq_beth_natCast`

English:
theorem lift_eq_beth_natCast
  statement: lift.{v} c = ℶ_ n ↔ c = ℶ_ n
  proof: by
  simp [eqComm]

@[simp]

中文:
定理 lift_eq_beth_natCast
  结论: lift.{v} c = ℶ_ n ↔ c = ℶ_ n
  证明: by
  simp [eqComm]

@[simp]

Depends on / 依赖: eqComm
-/
theorem lift_eq_beth_natCast : lift.{v} c = ℶ_ n ↔ c = ℶ_ n := by
  simp [eqComm]

@[simp]
/--
theorem `beth_ofNat_le_lift` / 定理 `beth_ofNat_le_lift`

English:
theorem beth_ofNat_le_lift
  given: [n.AtLeastTwo]
  statement: ℶ_ ofNat(n) <= lift.{v} c ↔ ℶ_ ofNat(n) <= c
  proof: beth_natCast_le_lift

@[simp]

中文:
定理 beth_of自然数_le_lift
  条件: [n.AtLeastTwo]
  结论: ℶ_ of自然数(n) <= lift.{v} c ↔ ℶ_ of自然数(n) <= c
  证明: beth_natCast_le_lift

@[simp]

Depends on / 依赖: beth_natCast_le_lift
-/
theorem beth_ofNat_le_lift [n.AtLeastTwo] : ℶ_ ofNat(n) <= lift.{v} c ↔ ℶ_ ofNat(n) <= c :=
  beth_natCast_le_lift

@[simp]
/--
theorem `lift_le_beth_ofNat` / 定理 `lift_le_beth_ofNat`

English:
theorem lift_le_beth_ofNat
  given: [n.AtLeastTwo]
  statement: lift.{v} c <= ℶ_ ofNat(n) ↔ c <= ℶ_ ofNat(n)
  proof: lift_le_beth_natCast

@[simp]

中文:
定理 lift_le_beth_of自然数
  条件: [n.AtLeastTwo]
  结论: lift.{v} c <= ℶ_ of自然数(n) ↔ c <= ℶ_ of自然数(n)
  证明: lift_le_beth_natCast

@[simp]

Depends on / 依赖: lift_le_beth_natCast
-/
theorem lift_le_beth_ofNat [n.AtLeastTwo] : lift.{v} c <= ℶ_ ofNat(n) ↔ c <= ℶ_ ofNat(n) :=
  lift_le_beth_natCast

@[simp]
/--
theorem `beth_ofNat_lt_lift` / 定理 `beth_ofNat_lt_lift`

English:
theorem beth_ofNat_lt_lift
  given: [n.AtLeastTwo]
  statement: ℶ_ ofNat(n) < lift.{v} c ↔ ℶ_ ofNat(n) < c
  proof: beth_natCast_lt_lift

@[simp]

中文:
定理 beth_of自然数_lt_lift
  条件: [n.AtLeastTwo]
  结论: ℶ_ of自然数(n) < lift.{v} c ↔ ℶ_ of自然数(n) < c
  证明: beth_natCast_lt_lift

@[simp]

Depends on / 依赖: beth_natCast_lt_lift
-/
theorem beth_ofNat_lt_lift [n.AtLeastTwo] : ℶ_ ofNat(n) < lift.{v} c ↔ ℶ_ ofNat(n) < c :=
  beth_natCast_lt_lift

@[simp]
/--
theorem `lift_lt_beth_ofNat` / 定理 `lift_lt_beth_ofNat`

English:
theorem lift_lt_beth_ofNat
  given: [n.AtLeastTwo]
  statement: lift.{v} c < ℶ_ ofNat(n) ↔ c < ℶ_ ofNat(n)
  proof: lift_lt_beth_natCast

@[simp]

中文:
定理 lift_lt_beth_of自然数
  条件: [n.AtLeastTwo]
  结论: lift.{v} c < ℶ_ of自然数(n) ↔ c < ℶ_ of自然数(n)
  证明: lift_lt_beth_natCast

@[simp]

Depends on / 依赖: lift_lt_beth_natCast
-/
theorem lift_lt_beth_ofNat [n.AtLeastTwo] : lift.{v} c < ℶ_ ofNat(n) ↔ c < ℶ_ ofNat(n) :=
  lift_lt_beth_natCast

@[simp]
/--
theorem `beth_ofNat_eq_lift` / 定理 `beth_ofNat_eq_lift`

English:
theorem beth_ofNat_eq_lift
  given: [n.AtLeastTwo]
  statement: ℶ_ ofNat(n) = lift.{v} c ↔ ℶ_ ofNat(n) = c
  proof: beth_natCast_eq_lift

@[simp]

中文:
定理 beth_of自然数_eq_lift
  条件: [n.AtLeastTwo]
  结论: ℶ_ of自然数(n) = lift.{v} c ↔ ℶ_ of自然数(n) = c
  证明: beth_natCast_eq_lift

@[simp]

Depends on / 依赖: beth_natCast_eq_lift
-/
theorem beth_ofNat_eq_lift [n.AtLeastTwo] : ℶ_ ofNat(n) = lift.{v} c ↔ ℶ_ ofNat(n) = c :=
  beth_natCast_eq_lift

@[simp]
/--
theorem `lift_eq_beth_ofNat` / 定理 `lift_eq_beth_ofNat`

English:
theorem lift_eq_beth_ofNat
  given: [n.AtLeastTwo]
  statement: lift.{v} c = ℶ_ ofNat(n) ↔ c = ℶ_ ofNat(n)
  proof: lift_eq_beth_natCast

中文:
定理 lift_eq_beth_of自然数
  条件: [n.AtLeastTwo]
  结论: lift.{v} c = ℶ_ of自然数(n) ↔ c = ℶ_ of自然数(n)
  证明: lift_eq_beth_natCast

Depends on / 依赖: lift_eq_beth_natCast
-/
theorem lift_eq_beth_ofNat [n.AtLeastTwo] : lift.{v} c = ℶ_ ofNat(n) ↔ c = ℶ_ ofNat(n) :=
  lift_eq_beth_natCast

end lift
end Cardinal

namespace Ordinal
section lift
variable {o : Ordinal.{u}} {n : Nat}

@[simp]
/--
theorem `omega_one_le_lift` / 定理 `omega_one_le_lift`

English:
theorem omega_one_le_lift
  statement: ω₁ <= lift.{v} o ↔ ω₁ <= o
  proof: by
  simpa using lift_le (a := ω₁)

@[simp]

中文:
定理 omega_one_le_lift
  结论: ω₁ <= lift.{v} o ↔ ω₁ <= o
  证明: by
  simpa using lift_le (a := ω₁)

@[simp]

Depends on / 依赖: lift_le
-/
theorem omega_one_le_lift : ω₁ <= lift.{v} o ↔ ω₁ <= o := by
  simpa using lift_le (a := ω₁)

@[simp]
/--
theorem `lift_le_omega_one` / 定理 `lift_le_omega_one`

English:
theorem lift_le_omega_one
  statement: lift.{v} o <= ω₁ ↔ o <= ω₁
  proof: by
  simpa using lift_le (b := ω₁)

@[simp]

中文:
定理 lift_le_omega_one
  结论: lift.{v} o <= ω₁ ↔ o <= ω₁
  证明: by
  simpa using lift_le (b := ω₁)

@[simp]

Depends on / 依赖: lift_le
-/
theorem lift_le_omega_one : lift.{v} o <= ω₁ ↔ o <= ω₁ := by
  simpa using lift_le (b := ω₁)

@[simp]
/--
theorem `omega_one_lt_lift` / 定理 `omega_one_lt_lift`

English:
theorem omega_one_lt_lift
  statement: ω₁ < lift.{v} o ↔ ω₁ < o
  proof: by
  simpa using lift_lt (a := ω₁)

@[simp]

中文:
定理 omega_one_lt_lift
  结论: ω₁ < lift.{v} o ↔ ω₁ < o
  证明: by
  simpa using lift_lt (a := ω₁)

@[simp]

Depends on / 依赖: lift_lt
-/
theorem omega_one_lt_lift : ω₁ < lift.{v} o ↔ ω₁ < o := by
  simpa using lift_lt (a := ω₁)

@[simp]
/--
theorem `lift_lt_omega_one` / 定理 `lift_lt_omega_one`

English:
theorem lift_lt_omega_one
  statement: lift.{v} o < ω₁ ↔ o < ω₁
  proof: by
  simpa using lift_lt (b := ω₁)

@[simp]

中文:
定理 lift_lt_omega_one
  结论: lift.{v} o < ω₁ ↔ o < ω₁
  证明: by
  simpa using lift_lt (b := ω₁)

@[simp]

Depends on / 依赖: lift_lt
-/
theorem lift_lt_omega_one : lift.{v} o < ω₁ ↔ o < ω₁ := by
  simpa using lift_lt (b := ω₁)

@[simp]
/--
theorem `omega_one_eq_lift` / 定理 `omega_one_eq_lift`

English:
theorem omega_one_eq_lift
  statement: ω₁ = lift.{v} o ↔ ω₁ = o
  proof: by
  simpa using lift_inj (a := ω₁)

@[simp]

中文:
定理 omega_one_eq_lift
  结论: ω₁ = lift.{v} o ↔ ω₁ = o
  证明: by
  simpa using lift_inj (a := ω₁)

@[simp]

Depends on / 依赖: lift_inj
-/
theorem omega_one_eq_lift : ω₁ = lift.{v} o ↔ ω₁ = o := by
  simpa using lift_inj (a := ω₁)

@[simp]
/--
theorem `lift_eq_omega_one` / 定理 `lift_eq_omega_one`

English:
theorem lift_eq_omega_one
  statement: lift.{v} o = ω₁ ↔ o = ω₁
  proof: by
  simp [eqComm]

@[simp]

中文:
定理 lift_eq_omega_one
  结论: lift.{v} o = ω₁ ↔ o = ω₁
  证明: by
  simp [eqComm]

@[simp]

Depends on / 依赖: eqComm
-/
theorem lift_eq_omega_one : lift.{v} o = ω₁ ↔ o = ω₁ := by
  simp [eqComm]

@[simp]
/--
theorem `omega_natCast_le_lift` / 定理 `omega_natCast_le_lift`

English:
theorem omega_natCast_le_lift
  statement: ω_ n <= lift.{v} o ↔ ω_ n <= o
  proof: by
  simpa using lift_le (a := ω_ n)

@[simp]

中文:
定理 omega_natCast_le_lift
  结论: ω_ n <= lift.{v} o ↔ ω_ n <= o
  证明: by
  simpa using lift_le (a := ω_ n)

@[simp]

Depends on / 依赖: lift_le
-/
theorem omega_natCast_le_lift : ω_ n <= lift.{v} o ↔ ω_ n <= o := by
  simpa using lift_le (a := ω_ n)

@[simp]
/--
theorem `lift_le_omega_natCast` / 定理 `lift_le_omega_natCast`

English:
theorem lift_le_omega_natCast
  statement: lift.{v} o <= ω_ n ↔ o <= ω_ n
  proof: by
  simpa using lift_le (b := ω_ n)

@[simp]

中文:
定理 lift_le_omega_natCast
  结论: lift.{v} o <= ω_ n ↔ o <= ω_ n
  证明: by
  simpa using lift_le (b := ω_ n)

@[simp]

Depends on / 依赖: lift_le
-/
theorem lift_le_omega_natCast : lift.{v} o <= ω_ n ↔ o <= ω_ n := by
  simpa using lift_le (b := ω_ n)

@[simp]
/--
theorem `omega_natCast_lt_lift` / 定理 `omega_natCast_lt_lift`

English:
theorem omega_natCast_lt_lift
  statement: ω_ n < lift.{v} o ↔ ω_ n < o
  proof: by
  simpa using lift_lt (a := ω_ n)

@[simp]

中文:
定理 omega_natCast_lt_lift
  结论: ω_ n < lift.{v} o ↔ ω_ n < o
  证明: by
  simpa using lift_lt (a := ω_ n)

@[simp]

Depends on / 依赖: lift_lt
-/
theorem omega_natCast_lt_lift : ω_ n < lift.{v} o ↔ ω_ n < o := by
  simpa using lift_lt (a := ω_ n)

@[simp]
/--
theorem `lift_lt_omega_natCast` / 定理 `lift_lt_omega_natCast`

English:
theorem lift_lt_omega_natCast
  statement: lift.{v} o < ω_ n ↔ o < ω_ n
  proof: by
  simpa using lift_lt (b := ω_ n)

@[simp]

中文:
定理 lift_lt_omega_natCast
  结论: lift.{v} o < ω_ n ↔ o < ω_ n
  证明: by
  simpa using lift_lt (b := ω_ n)

@[simp]

Depends on / 依赖: lift_lt
-/
theorem lift_lt_omega_natCast : lift.{v} o < ω_ n ↔ o < ω_ n := by
  simpa using lift_lt (b := ω_ n)

@[simp]
/--
theorem `omega_natCast_eq_lift` / 定理 `omega_natCast_eq_lift`

English:
theorem omega_natCast_eq_lift
  statement: ω_ n = lift.{v} o ↔ ω_ n = o
  proof: by
  simpa using lift_inj (a := ω_ n)

@[simp]

中文:
定理 omega_natCast_eq_lift
  结论: ω_ n = lift.{v} o ↔ ω_ n = o
  证明: by
  simpa using lift_inj (a := ω_ n)

@[simp]

Depends on / 依赖: lift_inj
-/
theorem omega_natCast_eq_lift : ω_ n = lift.{v} o ↔ ω_ n = o := by
  simpa using lift_inj (a := ω_ n)

@[simp]
/--
theorem `lift_eq_omega_natCast` / 定理 `lift_eq_omega_natCast`

English:
theorem lift_eq_omega_natCast
  statement: lift.{v} o = ω_ n ↔ o = ω_ n
  proof: by
  simp [eqComm]

@[simp]

中文:
定理 lift_eq_omega_natCast
  结论: lift.{v} o = ω_ n ↔ o = ω_ n
  证明: by
  simp [eqComm]

@[simp]

Depends on / 依赖: eqComm
-/
theorem lift_eq_omega_natCast : lift.{v} o = ω_ n ↔ o = ω_ n := by
  simp [eqComm]

@[simp]
/--
theorem `omega_ofNat_le_lift` / 定理 `omega_ofNat_le_lift`

English:
theorem omega_ofNat_le_lift
  given: [n.AtLeastTwo]
  statement: ω_ ofNat(n) <= lift.{v} o ↔ ω_ ofNat(n) <= o
  proof: omega_natCast_le_lift

@[simp]

中文:
定理 omega_of自然数_le_lift
  条件: [n.AtLeastTwo]
  结论: ω_ of自然数(n) <= lift.{v} o ↔ ω_ of自然数(n) <= o
  证明: omega_natCast_le_lift

@[simp]

Depends on / 依赖: omega_natCast_le_lift
-/
theorem omega_ofNat_le_lift [n.AtLeastTwo] : ω_ ofNat(n) <= lift.{v} o ↔ ω_ ofNat(n) <= o :=
  omega_natCast_le_lift

@[simp]
/--
theorem `lift_le_omega_ofNat` / 定理 `lift_le_omega_ofNat`

English:
theorem lift_le_omega_ofNat
  given: [n.AtLeastTwo]
  statement: lift.{v} o <= ω_ ofNat(n) ↔ o <= ω_ ofNat(n)
  proof: lift_le_omega_natCast

@[simp]

中文:
定理 lift_le_omega_of自然数
  条件: [n.AtLeastTwo]
  结论: lift.{v} o <= ω_ of自然数(n) ↔ o <= ω_ of自然数(n)
  证明: lift_le_omega_natCast

@[simp]

Depends on / 依赖: lift_le_omega_natCast
-/
theorem lift_le_omega_ofNat [n.AtLeastTwo] : lift.{v} o <= ω_ ofNat(n) ↔ o <= ω_ ofNat(n) :=
  lift_le_omega_natCast

@[simp]
/--
theorem `omega_ofNat_lt_lift` / 定理 `omega_ofNat_lt_lift`

English:
theorem omega_ofNat_lt_lift
  given: [n.AtLeastTwo]
  statement: ω_ ofNat(n) < lift.{v} o ↔ ω_ ofNat(n) < o
  proof: omega_natCast_lt_lift

@[simp]

中文:
定理 omega_of自然数_lt_lift
  条件: [n.AtLeastTwo]
  结论: ω_ of自然数(n) < lift.{v} o ↔ ω_ of自然数(n) < o
  证明: omega_natCast_lt_lift

@[simp]

Depends on / 依赖: omega_natCast_lt_lift
-/
theorem omega_ofNat_lt_lift [n.AtLeastTwo] : ω_ ofNat(n) < lift.{v} o ↔ ω_ ofNat(n) < o :=
  omega_natCast_lt_lift

@[simp]
/--
theorem `lift_lt_omega_ofNat` / 定理 `lift_lt_omega_ofNat`

English:
theorem lift_lt_omega_ofNat
  given: [n.AtLeastTwo]
  statement: lift.{v} o < ω_ ofNat(n) ↔ o < ω_ ofNat(n)
  proof: lift_lt_omega_natCast

@[simp]

中文:
定理 lift_lt_omega_of自然数
  条件: [n.AtLeastTwo]
  结论: lift.{v} o < ω_ of自然数(n) ↔ o < ω_ of自然数(n)
  证明: lift_lt_omega_natCast

@[simp]

Depends on / 依赖: lift_lt_omega_natCast
-/
theorem lift_lt_omega_ofNat [n.AtLeastTwo] : lift.{v} o < ω_ ofNat(n) ↔ o < ω_ ofNat(n) :=
  lift_lt_omega_natCast

@[simp]
/--
theorem `omega_ofNat_eq_lift` / 定理 `omega_ofNat_eq_lift`

English:
theorem omega_ofNat_eq_lift
  given: [n.AtLeastTwo]
  statement: ω_ ofNat(n) = lift.{v} o ↔ ω_ ofNat(n) = o
  proof: omega_natCast_eq_lift

@[simp]

中文:
定理 omega_of自然数_eq_lift
  条件: [n.AtLeastTwo]
  结论: ω_ of自然数(n) = lift.{v} o ↔ ω_ of自然数(n) = o
  证明: omega_natCast_eq_lift

@[simp]

Depends on / 依赖: omega_natCast_eq_lift
-/
theorem omega_ofNat_eq_lift [n.AtLeastTwo] : ω_ ofNat(n) = lift.{v} o ↔ ω_ ofNat(n) = o :=
  omega_natCast_eq_lift

@[simp]
/--
theorem `lift_eq_omega_ofNat` / 定理 `lift_eq_omega_ofNat`

English:
theorem lift_eq_omega_ofNat
  given: [n.AtLeastTwo]
  statement: lift.{v} o = ω_ ofNat(n) ↔ o = ω_ ofNat(n)
  proof: lift_eq_omega_natCast

中文:
定理 lift_eq_omega_of自然数
  条件: [n.AtLeastTwo]
  结论: lift.{v} o = ω_ of自然数(n) ↔ o = ω_ of自然数(n)
  证明: lift_eq_omega_natCast

Depends on / 依赖: lift_eq_omega_natCast
-/
theorem lift_eq_omega_ofNat [n.AtLeastTwo] : lift.{v} o = ω_ ofNat(n) ↔ o = ω_ ofNat(n) :=
  lift_eq_omega_natCast

end lift
end Ordinal
