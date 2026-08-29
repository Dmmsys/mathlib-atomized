/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios, Nir Paz
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Ordinal.FixedPoint

import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.FundamentalSequence

/-!
# Regular cardinals

This file defines regular, singular, and inaccessible cardinals.

## Main definitions

* `Cardinal.IsRegular c` means that `c` is an infinite cardinal, equal to its own cofinality.
* `Cardinal.IsSingular c` means that `c` is an infinite cardinal which is not regular. That is,
  its cofinality is smaller than itself.
* `Cardinal.IsInaccessible c` means that `c` is strongly inaccessible:
  `ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c`.
-/

@[expose] public section

universe u v

open Function Cardinal Set Order Ordinal

namespace Cardinal
variable {c : Cardinal}

/-! ### Regular cardinals -/

/-- A cardinal is regular if it is infinite and it equals its own cofinality. -/
@[mk_iff]
/--
Definition of `IsRegular` / `IsRegular` 的定义

English:
structure IsRegular
  parameters: (c : Cardinal)
  axioms and operations (2):
    - aleph0_le : ℵ₀ <= c
    - le_cof_ord : c <= c.ord.cof

中文:
结构 是正则
  参数: (c : 基数)
  公理与运算 (2 个):
    - aleph0_le : ℵ₀ <= c
    - le_cof_ord : c <= c.ord.cof
-/
structure IsRegular (c : Cardinal) : Prop where
  /-- A regular cardinal is infinite. -/
  aleph0_le : ℵ₀ <= c
  /-- A cardinal equals its own cofinality. See `IsRegular.cof_eq`. -/
  le_cof_ord : c <= c.ord.cof

/--
theorem `IsRegular.cof_ord` / 定理 `IsRegular.cof_ord`

English:
theorem IsRegular.cof_ord
  given: (H : c.IsRegular)
  statement: c.ord.cof = c
  proof: (cof_ord_le c).antisymm H.2

@[deprecated (since := "2026-03-22")] alias IsRegular.cof_eq := IsRegular.cof_ord

中文:
定理 是正则.cof_ord
  条件: (H : c.是正则)
  结论: c.ord.cof = c
  证明: (cof_ord_le c).antisymm H.2

@[deprecated (since := "2026-03-22")] alias IsRegular.cof_eq := IsRegular.cof_ord

Depends on / 依赖: antisymm, cof_ord_le
-/
theorem IsRegular.cof_ord (H : c.IsRegular) : c.ord.cof = c :=
  (cof_ord_le c).antisymm H.2

@[deprecated (since := "2026-03-22")] alias IsRegular.cof_eq := IsRegular.cof_ord

/--
theorem `IsRegular.cof_omega_eq` / 定理 `IsRegular.cof_omega_eq`

English:
theorem IsRegular.cof_omega_eq
  given: {o : Ordinal} (H : (ℵ_ o).IsRegular)
  statement: (ω_ o).cof = ℵ_ o
  proof: by
  rw [← ord_aleph]; rw [H.cof_ord]

中文:
定理 是正则.cof_omega_eq
  条件: {o : 序数} (H : (ℵ_ o).是正则)
  结论: (ω_ o).cof = ℵ_ o
  证明: by
  rw [← ord_aleph]; rw [H.cof_ord]

Depends on / 依赖: H.cof_ord, cof_ord, ord_aleph
-/
theorem IsRegular.cof_omega_eq {o : Ordinal} (H : (ℵ_ o).IsRegular) : (ω_ o).cof = ℵ_ o := by
  rw [← ord_aleph]; rw [H.cof_ord]

/--
theorem `IsRegular.pos` / 定理 `IsRegular.pos`

English:
theorem IsRegular.pos
  given: (H : c.IsRegular)
  statement: 0 < c
  proof: aleph0_pos.trans_le H.1

中文:
定理 是正则.pos
  条件: (H : c.是正则)
  结论: 0 < c
  证明: aleph0_pos.trans_le H.1

Depends on / 依赖: aleph0_pos, aleph0_pos.trans_le, trans_le
-/
theorem IsRegular.pos (H : c.IsRegular) : 0 < c :=
  aleph0_pos.trans_le H.1

/--
theorem `IsRegular.nat_lt` / 定理 `IsRegular.nat_lt`

English:
theorem IsRegular.nat_lt
  given: (H : c.IsRegular) (n : Nat)
  statement: n < c
  proof: lt_of_lt_of_le natCast_lt_aleph0 H.aleph0_le

中文:
定理 是正则.nat_lt
  条件: (H : c.是正则) (n : 自然数)
  结论: n < c
  证明: lt_of_lt_of_le natCast_lt_aleph0 H.aleph0_le

Depends on / 依赖: H.aleph0_le, aleph0_le, lt_of_lt_of_le, natCast_lt_aleph0
-/
theorem IsRegular.nat_lt (H : c.IsRegular) (n : Nat) : n < c :=
  lt_of_lt_of_le natCast_lt_aleph0 H.aleph0_le

/--
theorem `IsRegular.ord_pos` / 定理 `IsRegular.ord_pos`

English:
theorem IsRegular.ord_pos
  given: (H : c.IsRegular)
  statement: 0 < c.ord
  proof: by
  rw [Cardinal.lt_ord]; rw [card_zero]
  exact H.pos

中文:
定理 是正则.ord_pos
  条件: (H : c.是正则)
  结论: 0 < c.ord
  证明: by
  rw [Cardinal.lt_ord]; rw [card_zero]
  exact H.pos

Depends on / 依赖: Cardinal, Cardinal.lt_ord, H.pos, card_zero, lt_ord
-/
theorem IsRegular.ord_pos (H : c.IsRegular) : 0 < c.ord := by
  rw [Cardinal.lt_ord]; rw [card_zero]
  exact H.pos

/--
theorem `isRegular_cof` / 定理 `isRegular_cof`

English:
theorem isRegular_cof
  given: {o : Ordinal} (h : IsSuccLimit o)
  statement: IsRegular o.cof
  proof: by
  refine ⟨?_, (cof_ord_cof o).ge⟩
  rwa [aleph0_le_cof_iff, one_lt_cof_iff]

中文:
定理 isRegular_cof
  条件: {o : 序数} (h : 是SuccLimit o)
  结论: 是正则 o.cof
  证明: by
  refine ⟨?_, (cof_ord_cof o).ge⟩
  rwa [aleph0_le_cof_iff, one_lt_cof_iff]

Depends on / 依赖: aleph0_le_cof_iff, cof_ord_cof, one_lt_cof_iff
-/
theorem isRegular_cof {o : Ordinal} (h : IsSuccLimit o) : IsRegular o.cof := by
  refine ⟨?_, (cof_ord_cof o).ge⟩
  rwa [aleph0_le_cof_iff, one_lt_cof_iff]

/--
lemma `IsRegular.ne_zero` / 引理 `IsRegular.ne_zero`

English:
lemma IsRegular.ne_zero
  given: (H : c.IsRegular)
  statement: c != 0
  proof: H.pos.ne'

中文:
引理 是正则.ne_zero
  条件: (H : c.是正则)
  结论: c != 0
  证明: H.pos.ne'
-/
lemma IsRegular.ne_zero (H : c.IsRegular) : c != 0 :=
  H.pos.ne'

/--
theorem `isRegular_aleph0` / 定理 `isRegular_aleph0`

English:
theorem isRegular_aleph0
  statement: IsRegular ℵ₀
  proof: ⟨le_rfl, by simp⟩

中文:
定理 isRegular_aleph0
  结论: 是正则 ℵ₀
  证明: ⟨le_rfl, by simp⟩

Depends on / 依赖: Quotient, Quotient.ind, dist_smul_pair, le_rfl
-/
theorem isRegular_aleph0 : IsRegular ℵ₀ :=
  ⟨le_rfl, by simp⟩

/--
lemma `fact_isRegular_aleph0` / 引理 `fact_isRegular_aleph0`

English:
lemma fact_isRegular_aleph0
  statement: Fact (IsRegular ℵ₀) where
  proof: isRegular_aleph0

中文:
引理 fact_isRegular_aleph0
  结论: Fact (是正则 ℵ₀) where
  证明: isRegular_aleph0

Depends on / 依赖: isRegular_aleph0
-/
lemma fact_isRegular_aleph0 : Fact (IsRegular ℵ₀) where
  out := isRegular_aleph0

/--
theorem `isRegular_succ` / 定理 `isRegular_succ`

English:
theorem isRegular_succ
  given: {c : Cardinal} (hc : ℵ₀ <= c)
  statement: IsRegular (succ c)
  proof: by
  have hc₀ := hc.trans (le_succ c)
  use hc₀
  by_contra! hc'
  obtain ⟨f, hf⟩ := exists_isFundamentalSeq (o := (succ c).ord) rfl
  apply hf.iSup_add_one_eq.not_lt
  rw [← card_le_iff]
  refine card_iSup_Iio_le ?_ fun i => ?_
  · simpa using hc'
  · rw [card_le_iff]
    exact (isSuccLimit_ord hc₀

中文:
定理 isRegular_succ
  条件: {c : 基数} (hc : ℵ₀ <= c)
  结论: 是正则 (succ c)
  证明: by
  have hc₀ := hc.trans (le_succ c)
  use hc₀
  by_contra! hc'
  obtain ⟨f, hf⟩ := exists_isFundamentalSeq (o := (succ c).ord) rfl
  apply hf.iSup_add_one_eq.not_lt
  rw [← card_le_iff]
  refine card_iSup_Iio_le ?_ fun i => ?_
  · simpa using hc'
  · rw [card_le_iff]
    exact (isSuccLimit_ord hc₀

Depends on / 依赖: add_one_lt, card_iSup_Iio_le, card_le_iff, exists_isFundamentalSeq, hc.trans, hf.iSup_add_one_eq.not_lt, iSup_add_one_eq, isSuccLimit_ord, le_succ, not_lt
-/
theorem isRegular_succ {c : Cardinal} (hc : ℵ₀ <= c) : IsRegular (succ c) := by
  have hc₀ := hc.trans (le_succ c)
  use hc₀
  by_contra! hc'
  obtain ⟨f, hf⟩ := exists_isFundamentalSeq (o := (succ c).ord) rfl
  apply hf.iSup_add_one_eq.not_lt
  rw [← card_le_iff]
  refine card_iSup_Iio_le ?_ fun i => ?_
  · simpa using hc'
  · rw [card_le_iff]
    exact (isSuccLimit_ord hc₀).add_one_lt (f i).2

/--
theorem `isRegular_aleph_one` / 定理 `isRegular_aleph_one`

English:
theorem isRegular_aleph_one
  statement: IsRegular ℵ₁
  proof: by
  rw [← succ_aleph0]
  exact isRegular_succ le_rfl

@[simp]

中文:
定理 isRegular_aleph_one
  结论: 是正则 ℵ₁
  证明: by
  rw [← succ_aleph0]
  exact isRegular_succ le_rfl

@[simp]

Depends on / 依赖: isRegular_succ, le_rfl, succ_aleph0
-/
theorem isRegular_aleph_one : IsRegular ℵ₁ := by
  rw [← succ_aleph0]
  exact isRegular_succ le_rfl

@[simp]
/--
theorem `cof_omega_one` / 定理 `cof_omega_one`

English:
theorem cof_omega_one
  statement: cof ω₁ = ℵ₁
  proof: by
  simpa using isRegular_aleph_one.cof_omega_eq

中文:
定理 cof_omega_one
  结论: cof ω₁ = ℵ₁
  证明: by
  simpa using isRegular_aleph_one.cof_omega_eq

Depends on / 依赖: cof_omega_eq, isRegular_aleph_one, isRegular_aleph_one.cof_omega_eq
-/
theorem cof_omega_one : cof ω₁ = ℵ₁ := by
  simpa using isRegular_aleph_one.cof_omega_eq

/--
theorem `_root_.Ordinal.iSup_lt_omega_one` / 定理 `_root_.Ordinal.iSup_lt_omega_one`

English:
theorem _root_.Ordinal.iSup_lt_omega_one
  given: {α : Type*} [Countable α] {f : α -> Ordinal}
  proof: Ordinal.lift_iSup_lt_of_lt_cof (by simp)

@[deprecated (since := "2026-03-23")]
alias iSup_sequence_lt_omega_one := Ordinal.iSup_lt_omega_one

中文:
定理 _root_.序数.iSup_lt_omega_one
  条件: {α : 类型} [可数 α] {f : α -> 序数}
  证明: Ordinal.lift_iSup_lt_of_lt_cof (by simp)

@[deprecated (since := "2026-03-23")]
alias iSup_sequence_lt_omega_one := Ordinal.iSup_lt_omega_one

Depends on / 依赖: Ordinal, Ordinal.lift_iSup_lt_of_lt_cof, lift_iSup_lt_of_lt_cof
-/
theorem _root_.Ordinal.iSup_lt_omega_one {α : Type*} [Countable α] {f : α -> Ordinal} :
    (forall i, f i < ω₁) -> ⨆ i, f i < ω₁ :=
  Ordinal.lift_iSup_lt_of_lt_cof (by simp)

@[deprecated (since := "2026-03-23")]
alias iSup_sequence_lt_omega_one := Ordinal.iSup_lt_omega_one

/--
theorem `isRegular_preAleph_add_one` / 定理 `isRegular_preAleph_add_one`

English:
theorem isRegular_preAleph_add_one
  given: {o : Ordinal} (h : ω <= o)
  statement: IsRegular (preAleph (o + 1))
  proof: by
  rw [← succ_preAleph]
  exact isRegular_succ (aleph0_le_preAleph.2 h)

@[deprecated isRegular_preAleph_add_one (since := "2026-03-23")]

中文:
定理 isRegular_preAleph_add_one
  条件: {o : 序数} (h : ω <= o)
  结论: 是正则 (preAleph (o + 1))
  证明: by
  rw [← succ_preAleph]
  exact isRegular_succ (aleph0_le_preAleph.2 h)

@[deprecated isRegular_preAleph_add_one (since := "2026-03-23")]

Depends on / 依赖: aleph0_le_preAleph, isRegular_succ, succ_preAleph
-/
theorem isRegular_preAleph_add_one {o : Ordinal} (h : ω <= o) : IsRegular (preAleph (o + 1)) := by
  rw [← succ_preAleph]
  exact isRegular_succ (aleph0_le_preAleph.2 h)

@[deprecated isRegular_preAleph_add_one (since := "2026-03-23")]
/--
theorem `isRegular_preAleph_succ` / 定理 `isRegular_preAleph_succ`

English:
theorem isRegular_preAleph_succ
  given: {o : Ordinal} (h : ω <= o)
  statement: IsRegular (preAleph (succ o))
  proof: isRegular_preAleph_add_one h

中文:
定理 isRegular_preAleph_succ
  条件: {o : 序数} (h : ω <= o)
  结论: 是正则 (preAleph (succ o))
  证明: isRegular_preAleph_add_one h

Depends on / 依赖: isRegular_preAleph_add_one
-/
theorem isRegular_preAleph_succ {o : Ordinal} (h : ω <= o) : IsRegular (preAleph (succ o)) :=
  isRegular_preAleph_add_one h

/--
theorem `cof_preOmega_add_one` / 定理 `cof_preOmega_add_one`

English:
theorem cof_preOmega_add_one
  given: {o : Ordinal} (h : ω <= o)
  proof: by
  rw [← ord_preAleph]; rw [(isRegular_preAleph_add_one h).cof_ord]

中文:
定理 cof_preOmega_add_one
  条件: {o : 序数} (h : ω <= o)
  证明: by
  rw [← ord_preAleph]; rw [(isRegular_preAleph_add_one h).cof_ord]

Depends on / 依赖: cof_ord, isRegular_preAleph_add_one, ord_preAleph
-/
theorem cof_preOmega_add_one {o : Ordinal} (h : ω <= o) :
    (preOmega (o + 1)).cof = preAleph (o + 1) := by
  rw [← ord_preAleph]; rw [(isRegular_preAleph_add_one h).cof_ord]

/--
theorem `isRegular_aleph_add_one` / 定理 `isRegular_aleph_add_one`

English:
theorem isRegular_aleph_add_one
  given: (o : Ordinal)
  statement: IsRegular (ℵ_ (o + 1))
  proof: by
  rw [← succ_aleph]
  exact isRegular_succ (aleph0_le_aleph o)

@[deprecated isRegular_aleph_add_one (since := "2026-03-23")]

中文:
定理 isRegular_aleph_add_one
  条件: (o : 序数)
  结论: 是正则 (ℵ_ (o + 1))
  证明: by
  rw [← succ_aleph]
  exact isRegular_succ (aleph0_le_aleph o)

@[deprecated isRegular_aleph_add_one (since := "2026-03-23")]

Depends on / 依赖: aleph0_le_aleph, isRegular_succ, succ_aleph
-/
theorem isRegular_aleph_add_one (o : Ordinal) : IsRegular (ℵ_ (o + 1)) := by
  rw [← succ_aleph]
  exact isRegular_succ (aleph0_le_aleph o)

@[deprecated isRegular_aleph_add_one (since := "2026-03-23")]
/--
theorem `isRegular_aleph_succ` / 定理 `isRegular_aleph_succ`

English:
theorem isRegular_aleph_succ
  given: (o : Ordinal)
  statement: IsRegular (ℵ_ (succ o))
  proof: isRegular_aleph_add_one o

@[simp]

中文:
定理 isRegular_aleph_succ
  条件: (o : 序数)
  结论: 是正则 (ℵ_ (succ o))
  证明: isRegular_aleph_add_one o

@[simp]

Depends on / 依赖: isRegular_aleph_add_one
-/
theorem isRegular_aleph_succ (o : Ordinal) : IsRegular (ℵ_ (succ o)) :=
  isRegular_aleph_add_one o

@[simp]
/--
theorem `cof_omega_add_one` / 定理 `cof_omega_add_one`

English:
theorem cof_omega_add_one
  given: (o : Ordinal)
  statement: (ω_ (o + 1)).cof = ℵ_ (o + 1)
  proof: (isRegular_aleph_add_one o).cof_omega_eq

中文:
定理 cof_omega_add_one
  条件: (o : 序数)
  结论: (ω_ (o + 1)).cof = ℵ_ (o + 1)
  证明: (isRegular_aleph_add_one o).cof_omega_eq

Depends on / 依赖: cof_omega_eq, isRegular_aleph_add_one
-/
theorem cof_omega_add_one (o : Ordinal) : (ω_ (o + 1)).cof = ℵ_ (o + 1) :=
  (isRegular_aleph_add_one o).cof_omega_eq

/--
lemma `IsRegular.lift` / 引理 `IsRegular.lift`

English:
lemma IsRegular.lift
  given: {κ : Cardinal.{v}} (h : κ.IsRegular)
  proof: by
  obtain ⟨h₁, h₂⟩ := h
  constructor
  · simpa
  · rwa [← Cardinal.lift_ord, ← Ordinal.lift_cof, lift_le]

@[simp]

中文:
引理 是正则.lift
  条件: {κ : 基数.{v}} (h : κ.是正则)
  证明: by
  obtain ⟨h₁, h₂⟩ := h
  constructor
  · simpa
  · rwa [← Cardinal.lift_ord, ← Ordinal.lift_cof, lift_le]

@[simp]

Depends on / 依赖: Cardinal, Cardinal.lift_ord, Ordinal, Ordinal.lift_cof, lift_cof, lift_le, lift_ord
-/
lemma IsRegular.lift {κ : Cardinal.{v}} (h : κ.IsRegular) :
    (Cardinal.lift.{u} κ).IsRegular := by
  obtain ⟨h₁, h₂⟩ := h
  constructor
  · simpa
  · rwa [← Cardinal.lift_ord, ← Ordinal.lift_cof, lift_le]

@[simp]
/--
lemma `isRegular_lift_iff` / 引理 `isRegular_lift_iff`

English:
lemma isRegular_lift_iff
  given: {κ : Cardinal.{v}}
  proof: ⟨fun ⟨h₁, h₂⟩ => ⟨by simpa using h₁, by simpa [← lift_le.{u, v}]⟩, fun h => h.lift⟩

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

中文:
引理 isRegular_lift_iff
  条件: {κ : 基数.{v}}
  证明: ⟨fun ⟨h₁, h₂⟩ => ⟨by simpa using h₁, by simpa [← lift_le.{u, v}]⟩, fun h => h.lift⟩

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: h.lift, lift_le
-/
lemma isRegular_lift_iff {κ : Cardinal.{v}} :
    (Cardinal.lift.{u} κ).IsRegular ↔ κ.IsRegular :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨by simpa using h₁, by simpa [← lift_le.{u, v}]⟩, fun h => h.lift⟩

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `lsub_lt_ord_lift_of_isRegular` / 定理 `lsub_lt_ord_lift_of_isRegular`

English:
theorem lsub_lt_ord_lift_of_isRegular
  statement: {ι} {f : ι -> Ordinal} {c} (hc : IsRegular c)
  proof: by
  apply lift_iSup_add_one_lt_of_lt_cof _ hf
  rwa [lift_umax, c.ord.lift_id', hc.cof_ord]

@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 lsub_lt_ord_lift_of_isRegular
  结论: {ι} {f : ι -> 序数} {c} (hc : 是正则 c)
  证明: by
  apply lift_iSup_add_one_lt_of_lt_cof _ hf
  rwa [lift_umax, c.ord.lift_id', hc.cof_ord]

@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: c.ord.lift_id, cof_ord, hc.cof_ord, lift_iSup_add_one_lt_of_lt_cof, lift_id, lift_umax
-/
theorem lsub_lt_ord_lift_of_isRegular {ι} {f : ι -> Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hf : forall i, f i < c.ord) : Ordinal.lsub.{u, v} f < c.ord := by
  apply lift_iSup_add_one_lt_of_lt_cof _ hf
  rwa [lift_umax, c.ord.lift_id', hc.cof_ord]

@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `lsub_lt_ord_of_isRegular` / 定理 `lsub_lt_ord_of_isRegular`

English:
theorem lsub_lt_ord_of_isRegular
  given: {ι} {f : ι -> Ordinal} {c} (hc : IsRegular c) (hι : #ι < c)
  proof: iSup_add_one_lt_of_lt_cof (by rwa [hc.cof_ord])

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 lsub_lt_ord_of_isRegular
  条件: {ι} {f : ι -> 序数} {c} (hc : 是正则 c) (hι : #ι < c)
  证明: iSup_add_one_lt_of_lt_cof (by rwa [hc.cof_ord])

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: cof_ord, hc.cof_ord, iSup_add_one_lt_of_lt_cof
-/
theorem lsub_lt_ord_of_isRegular {ι} {f : ι -> Ordinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (forall i, f i < c.ord) -> Ordinal.lsub f < c.ord :=
  iSup_add_one_lt_of_lt_cof (by rwa [hc.cof_ord])

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `iSup_lt_ord_lift_of_isRegular` / 定理 `iSup_lt_ord_lift_of_isRegular`

English:
theorem iSup_lt_ord_lift_of_isRegular
  statement: {ι} {f : ι -> Ordinal} {c} (hc : IsRegular c)
  proof: by
  apply Ordinal.lift_iSup_lt_of_lt_cof _ hf
  rwa [lift_umax, Ordinal.lift_id', hc.cof_ord]

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 iSup_lt_ord_lift_of_isRegular
  结论: {ι} {f : ι -> 序数} {c} (hc : 是正则 c)
  证明: by
  apply Ordinal.lift_iSup_lt_of_lt_cof _ hf
  rwa [lift_umax, Ordinal.lift_id', hc.cof_ord]

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: Ordinal, Ordinal.lift_iSup_lt_of_lt_cof, Ordinal.lift_id, cof_ord, hc.cof_ord, lift_iSup_lt_of_lt_cof, lift_id, lift_umax
-/
theorem iSup_lt_ord_lift_of_isRegular {ι} {f : ι -> Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hf : forall i, f i < c.ord) : iSup f < c.ord := by
  apply Ordinal.lift_iSup_lt_of_lt_cof _ hf
  rwa [lift_umax, Ordinal.lift_id', hc.cof_ord]

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `iSup_lt_ord_of_isRegular` / 定理 `iSup_lt_ord_of_isRegular`

English:
theorem iSup_lt_ord_of_isRegular
  given: {ι} {f : ι -> Ordinal} {c} (hc : IsRegular c) (hι : #ι < c)
  proof: Ordinal.iSup_lt_of_lt_cof (by rwa [hc.cof_ord])

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 iSup_lt_ord_of_isRegular
  条件: {ι} {f : ι -> 序数} {c} (hc : 是正则 c) (hι : #ι < c)
  证明: Ordinal.iSup_lt_of_lt_cof (by rwa [hc.cof_ord])

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: Ordinal, Ordinal.iSup_lt_of_lt_cof, cof_ord, hc.cof_ord, iSup_lt_of_lt_cof
-/
theorem iSup_lt_ord_of_isRegular {ι} {f : ι -> Ordinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (forall i, f i < c.ord) -> iSup f < c.ord :=
  Ordinal.iSup_lt_of_lt_cof (by rwa [hc.cof_ord])

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `blsub_lt_ord_lift_of_isRegular` / 定理 `blsub_lt_ord_lift_of_isRegular`

English:
theorem blsub_lt_ord_lift_of_isRegular
  statement: {o : Ordinal} {f : forall a < o, Ordinal} {c} (hc : IsRegular c)
  proof: blsub_lt_ord_lift (by rwa [hc.cof_ord])

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 blsub_lt_ord_lift_of_isRegular
  结论: {o : 序数} {f : 对任意 a < o, 序数} {c} (hc : 是正则 c)
  证明: blsub_lt_ord_lift (by rwa [hc.cof_ord])

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: blsub_lt_ord_lift, cof_ord, hc.cof_ord
-/
theorem blsub_lt_ord_lift_of_isRegular {o : Ordinal} {f : forall a < o, Ordinal} {c} (hc : IsRegular c)
    (ho : Cardinal.lift.{v, u} o.card < c) :
    (forall i hi, f i hi < c.ord) -> Ordinal.blsub.{u, v} o f < c.ord :=
  blsub_lt_ord_lift (by rwa [hc.cof_ord])

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `blsub_lt_ord_of_isRegular` / 定理 `blsub_lt_ord_of_isRegular`

English:
theorem blsub_lt_ord_of_isRegular
  statement: {o : Ordinal} {f : forall a < o, Ordinal} {c} (hc : IsRegular c)
  proof: blsub_lt_ord (by rwa [hc.cof_ord])

@[deprecated iSup_lt_ord_lift_of_isRegular (since := "2026-03-22")]

中文:
定理 blsub_lt_ord_of_isRegular
  结论: {o : 序数} {f : 对任意 a < o, 序数} {c} (hc : 是正则 c)
  证明: blsub_lt_ord (by rwa [hc.cof_ord])

@[deprecated iSup_lt_ord_lift_of_isRegular (since := "2026-03-22")]

Depends on / 依赖: blsub_lt_ord, cof_ord, hc.cof_ord
-/
theorem blsub_lt_ord_of_isRegular {o : Ordinal} {f : forall a < o, Ordinal} {c} (hc : IsRegular c)
    (ho : o.card < c) : (forall i hi, f i hi < c.ord) -> Ordinal.blsub o f < c.ord :=
  blsub_lt_ord (by rwa [hc.cof_ord])

@[deprecated iSup_lt_ord_lift_of_isRegular (since := "2026-03-22")]
/--
theorem `bsup_lt_ord_lift_of_isRegular` / 定理 `bsup_lt_ord_lift_of_isRegular`

English:
theorem bsup_lt_ord_lift_of_isRegular
  statement: {o : Ordinal} {f : forall a < o, Ordinal} {c} (hc : IsRegular c)
  proof: bsup_lt_ord_lift (by rwa [hc.cof_ord])

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 bsup_lt_ord_lift_of_isRegular
  结论: {o : 序数} {f : 对任意 a < o, 序数} {c} (hc : 是正则 c)
  证明: bsup_lt_ord_lift (by rwa [hc.cof_ord])

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: bsup_lt_ord_lift, cof_ord, hc.cof_ord
-/
theorem bsup_lt_ord_lift_of_isRegular {o : Ordinal} {f : forall a < o, Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} o.card < c) :
    (forall i hi, f i hi < c.ord) -> Ordinal.bsup.{u, v} o f < c.ord :=
  bsup_lt_ord_lift (by rwa [hc.cof_ord])

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `bsup_lt_ord_of_isRegular` / 定理 `bsup_lt_ord_of_isRegular`

English:
theorem bsup_lt_ord_of_isRegular
  statement: {o : Ordinal} {f : forall a < o, Ordinal} {c} (hc : IsRegular c)
  proof: bsup_lt_ord (by rwa [hc.cof_ord])

@[deprecated lift_iSup_lt_of_lt_cof_ord (since := "2026-03-22")]

中文:
定理 bsup_lt_ord_of_isRegular
  结论: {o : 序数} {f : 对任意 a < o, 序数} {c} (hc : 是正则 c)
  证明: bsup_lt_ord (by rwa [hc.cof_ord])

@[deprecated lift_iSup_lt_of_lt_cof_ord (since := "2026-03-22")]

Depends on / 依赖: bsup_lt_ord, cof_ord, hc.cof_ord
-/
theorem bsup_lt_ord_of_isRegular {o : Ordinal} {f : forall a < o, Ordinal} {c} (hc : IsRegular c)
    (hι : o.card < c) : (forall i hi, f i hi < c.ord) -> Ordinal.bsup o f < c.ord :=
  bsup_lt_ord (by rwa [hc.cof_ord])

@[deprecated lift_iSup_lt_of_lt_cof_ord (since := "2026-03-22")]
/--
theorem `iSup_lt_lift_of_isRegular` / 定理 `iSup_lt_lift_of_isRegular`

English:
theorem iSup_lt_lift_of_isRegular
  statement: {ι} {f : ι -> Cardinal} {c} (hc : IsRegular c)
  proof: by
  apply lift_iSup_lt_of_lt_cof_ord _ hf
  rwa [lift_umax, c.lift_id', hc.cof_ord]

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]

中文:
定理 iSup_lt_lift_of_isRegular
  结论: {ι} {f : ι -> 基数} {c} (hc : 是正则 c)
  证明: by
  apply lift_iSup_lt_of_lt_cof_ord _ hf
  rwa [lift_umax, c.lift_id', hc.cof_ord]

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]

Depends on / 依赖: c.lift_id, cof_ord, hc.cof_ord, lift_iSup_lt_of_lt_cof_ord, lift_id, lift_umax
-/
theorem iSup_lt_lift_of_isRegular {ι} {f : ι -> Cardinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hf : forall i, f i < c) : iSup f < c := by
  apply lift_iSup_lt_of_lt_cof_ord _ hf
  rwa [lift_umax, c.lift_id', hc.cof_ord]

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
/--
theorem `iSup_lt_of_isRegular` / 定理 `iSup_lt_of_isRegular`

English:
theorem iSup_lt_of_isRegular
  given: {ι} {f : ι -> Cardinal} {c} (hc : IsRegular c) (hι : #ι < c)
  proof: iSup_lt_of_lt_cof_ord (by rwa [hc.cof_ord])

中文:
定理 iSup_lt_of_isRegular
  条件: {ι} {f : ι -> 基数} {c} (hc : 是正则 c) (hι : #ι < c)
  证明: iSup_lt_of_lt_cof_ord (by rwa [hc.cof_ord])

Depends on / 依赖: cof_ord, hc.cof_ord, iSup_lt_of_lt_cof_ord
-/
theorem iSup_lt_of_isRegular {ι} {f : ι -> Cardinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (forall i, f i < c) -> iSup f < c :=
  iSup_lt_of_lt_cof_ord (by rwa [hc.cof_ord])

/--
theorem `sum_lt_lift_of_isRegular` / 定理 `sum_lt_lift_of_isRegular`

English:
theorem sum_lt_lift_of_isRegular
  statement: {ι : Type u} {f : ι -> Cardinal} (hc : IsRegular c)
  proof: by
apply (sum_le_lift_mk_mul_iSup _).trans_lt
    mul_lt_of_lt hc.1 hι (lift_iSup_lt_of_lt_cof_ord _ hf)
  rwa [lift_umax, c.lift_id', hc.cof_ord]

中文:
定理 sum_lt_lift_of_isRegular
  结论: {ι : 类型u} {f : ι -> 基数} (hc : 是正则 c)
  证明: by
apply (sum_le_lift_mk_mul_iSup _).trans_lt
    mul_lt_of_lt hc.1 hι (lift_iSup_lt_of_lt_cof_ord _ hf)
  rwa [lift_umax, c.lift_id', hc.cof_ord]

Depends on / 依赖: c.lift_id, cof_ord, hc.cof_ord, lift_iSup_lt_of_lt_cof_ord, lift_id, lift_umax, mul_lt_of_lt, sum_le_lift_mk_mul_iSup, trans_lt
-/
theorem sum_lt_lift_of_isRegular {ι : Type u} {f : ι -> Cardinal} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hf : forall i, f i < c) : sum f < c := by
apply (sum_le_lift_mk_mul_iSup _).trans_lt
    mul_lt_of_lt hc.1 hι (lift_iSup_lt_of_lt_cof_ord _ hf)
  rwa [lift_umax, c.lift_id', hc.cof_ord]

/--
theorem `sum_lt_of_isRegular` / 定理 `sum_lt_of_isRegular`

English:
theorem sum_lt_of_isRegular
  statement: {ι : Type u} {f : ι -> Cardinal} (hc : IsRegular c)
  proof: sum_lt_lift_of_isRegular.{u, u} hc (by rwa [lift_id])

@[simp]

中文:
定理 sum_lt_of_isRegular
  结论: {ι : 类型u} {f : ι -> 基数} (hc : 是正则 c)
  证明: sum_lt_lift_of_isRegular.{u, u} hc (by rwa [lift_id])

@[simp]

Depends on / 依赖: lift_id, sum_lt_lift_of_isRegular
-/
theorem sum_lt_of_isRegular {ι : Type u} {f : ι -> Cardinal} (hc : IsRegular c)
    (hι : #ι < c) : (forall i, f i < c) -> sum f < c :=
  sum_lt_lift_of_isRegular.{u, u} hc (by rwa [lift_id])

@[simp]
/--
theorem `card_lt_of_card_iUnion_lt` / 定理 `card_lt_of_card_iUnion_lt`

English:
theorem card_lt_of_card_iUnion_lt
  statement: {ι : Type u} {α : Type u} {t : ι -> Set α} {c : Cardinal}
  proof: lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset <| subset_iUnion _ _) h

@[simp]

中文:
定理 card_lt_of_card_iUnion_lt
  结论: {ι : 类型u} {α : 类型u} {t : ι -> 集合 α} {c : 基数}
  证明: lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset <| subset_iUnion _ _) h

@[simp]

Depends on / 依赖: Cardinal, Cardinal.mk_le_mk_of_subset, lt_of_le_of_lt, mk_le_mk_of_subset, subset_iUnion
-/
theorem card_lt_of_card_iUnion_lt {ι : Type u} {α : Type u} {t : ι -> Set α} {c : Cardinal}
    (h : #(⋃ i, t i) < c) (i : ι) : #(t i) < c :=
  lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset <| subset_iUnion _ _) h

@[simp]
/--
theorem `card_iUnion_lt_iff_forall_of_isRegular` / 定理 `card_iUnion_lt_iff_forall_of_isRegular`

English:
theorem card_iUnion_lt_iff_forall_of_isRegular
  statement: {ι : Type u} {α : Type u} {t : ι -> Set α}
  proof: by
  refine ⟨card_lt_of_card_iUnion_lt, fun h => ?_⟩
  apply lt_of_le_of_lt (Cardinal.mk_sUnion_le _)
  apply Cardinal.mul_lt_of_lt hc.aleph0_le (mk_range_le.trans_lt hι)
  apply Cardinal.iSup_lt_of_lt_cof_ord (mk_range_le.trans_lt _)
  · simpa
  · rwa [hc.cof_ord]

中文:
定理 card_iUnion_lt_iff_对任意_of_isRegular
  结论: {ι : 类型u} {α : 类型u} {t : ι -> 集合 α}
  证明: by
  refine ⟨card_lt_of_card_iUnion_lt, fun h => ?_⟩
  apply lt_of_le_of_lt (Cardinal.mk_sUnion_le _)
  apply Cardinal.mul_lt_of_lt hc.aleph0_le (mk_range_le.trans_lt hι)
  apply Cardinal.iSup_lt_of_lt_cof_ord (mk_range_le.trans_lt _)
  · simpa
  · rwa [hc.cof_ord]

Depends on / 依赖: Cardinal, Cardinal.iSup_lt_of_lt_cof_ord, Cardinal.mk_sUnion_le, Cardinal.mul_lt_of_lt, aleph0_le, card_lt_of_card_iUnion_lt, cof_ord, hc.aleph0_le, hc.cof_ord, iSup_lt_of_lt_cof_ord, lt_of_le_of_lt, mk_range_le, mk_range_le.trans_lt, mk_sUnion_le, mul_lt_of_lt, trans_lt
-/
theorem card_iUnion_lt_iff_forall_of_isRegular {ι : Type u} {α : Type u} {t : ι -> Set α}
    (hc : c.IsRegular) (hι : #ι < c) : #(⋃ i, t i) < c ↔ forall i, #(t i) < c := by
  refine ⟨card_lt_of_card_iUnion_lt, fun h => ?_⟩
  apply lt_of_le_of_lt (Cardinal.mk_sUnion_le _)
  apply Cardinal.mul_lt_of_lt hc.aleph0_le (mk_range_le.trans_lt hι)
  apply Cardinal.iSup_lt_of_lt_cof_ord (mk_range_le.trans_lt _)
  · simpa
  · rwa [hc.cof_ord]

/--
theorem `card_lt_of_card_biUnion_lt` / 定理 `card_lt_of_card_biUnion_lt`

English:
theorem card_lt_of_card_biUnion_lt
  statement: {α β : Type u} {s : Set α} {t : forall a in s, Set β} {c : Cardinal}
  proof: by
  rw [biUnion_eq_iUnion] at h
  have := card_lt_of_card_iUnion_lt h
  simp_all only [iUnion_coe_set, Subtype.forall]

中文:
定理 card_lt_of_card_biUnion_lt
  结论: {α β : 类型u} {s : 集合 α} {t : 对任意 a in s, 集合 β} {c : 基数}
  证明: by
  rw [biUnion_eq_iUnion] at h
  have := card_lt_of_card_iUnion_lt h
  simp_all only [iUnion_coe_set, Subtype.forall]

Depends on / 依赖: Subtype, Subtype.forall, biUnion_eq_iUnion, card_lt_of_card_iUnion_lt, iUnion_coe_set
-/
theorem card_lt_of_card_biUnion_lt {α β : Type u} {s : Set α} {t : forall a in s, Set β} {c : Cardinal}
    (h : #(⋃ a in s, t a ‹_›) < c) (a : α) (ha : a in s) : #(t a ha) < c := by
  rw [biUnion_eq_iUnion] at h
  have := card_lt_of_card_iUnion_lt h
  simp_all only [iUnion_coe_set, Subtype.forall]

/--
theorem `card_biUnion_lt_iff_forall_of_isRegular` / 定理 `card_biUnion_lt_iff_forall_of_isRegular`

English:
theorem card_biUnion_lt_iff_forall_of_isRegular
  statement: {α β : Type u} {s : Set α} {t : forall a in s, Set β}
  proof: by
  rw [biUnion_eq_iUnion]; rw [card_iUnion_lt_iff_forall_of_isRegular hc hs]; rw [SetCoe.forall']

中文:
定理 card_biUnion_lt_iff_对任意_of_isRegular
  结论: {α β : 类型u} {s : 集合 α} {t : 对任意 a in s, 集合 β}
  证明: by
  rw [biUnion_eq_iUnion]; rw [card_iUnion_lt_iff_forall_of_isRegular hc hs]; rw [SetCoe.forall']

Depends on / 依赖: SetCoe, SetCoe.forall, biUnion_eq_iUnion, card_iUnion_lt_iff_forall_of_isRegular
-/
theorem card_biUnion_lt_iff_forall_of_isRegular {α β : Type u} {s : Set α} {t : forall a in s, Set β}
    (hc : c.IsRegular) (hs : #s < c) :
    #(⋃ a in s, t a ‹_›) < c ↔ forall a (ha : a in s), #(t a ha) < c := by
  rw [biUnion_eq_iUnion]; rw [card_iUnion_lt_iff_forall_of_isRegular hc hs]; rw [SetCoe.forall']

/--
theorem `nfpFamily_lt_ord_lift_of_isRegular` / 定理 `nfpFamily_lt_ord_lift_of_isRegular`

English:
theorem nfpFamily_lt_ord_lift_of_isRegular
  statement: {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : IsRegular c)
  proof: by
  apply nfpFamily_lt_ord_lift _ _ hf ha <;> rw [hc.cof_ord]
  · exact lt_of_le_of_ne hc.1 hc'.symm
  · exact hι

中文:
定理 nfpFamily_lt_ord_lift_of_isRegular
  结论: {ι} {f : ι -> 序数 -> 序数} {c} (hc : 是正则 c)
  证明: by
  apply nfpFamily_lt_ord_lift _ _ hf ha <;> rw [hc.cof_ord]
  · exact lt_of_le_of_ne hc.1 hc'.symm
  · exact hι

Depends on / 依赖: cof_ord, hc.cof_ord, lt_of_le_of_ne, nfpFamily_lt_ord_lift
-/
theorem nfpFamily_lt_ord_lift_of_isRegular {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hc' : c != ℵ₀) (hf : forall (i), forall b < c.ord, f i b < c.ord) {a}
    (ha : a < c.ord) : nfpFamily f a < c.ord := by
  apply nfpFamily_lt_ord_lift _ _ hf ha <;> rw [hc.cof_ord]
  · exact lt_of_le_of_ne hc.1 hc'.symm
  · exact hι

/--
theorem `nfpFamily_lt_ord_of_isRegular` / 定理 `nfpFamily_lt_ord_of_isRegular`

English:
theorem nfpFamily_lt_ord_of_isRegular
  statement: {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : IsRegular c)
  proof: nfpFamily_lt_ord_lift_of_isRegular hc (by rwa [lift_id]) hc' hf

中文:
定理 nfpFamily_lt_ord_of_isRegular
  结论: {ι} {f : ι -> 序数 -> 序数} {c} (hc : 是正则 c)
  证明: nfpFamily_lt_ord_lift_of_isRegular hc (by rwa [lift_id]) hc' hf

Depends on / 依赖: lift_id, nfpFamily_lt_ord_lift_of_isRegular
-/
theorem nfpFamily_lt_ord_of_isRegular {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : IsRegular c)
    (hι : #ι < c) (hc' : c != ℵ₀) {a} (hf : forall (i), forall b < c.ord, f i b < c.ord) :
    a < c.ord -> nfpFamily.{u, u} f a < c.ord :=
  nfpFamily_lt_ord_lift_of_isRegular hc (by rwa [lift_id]) hc' hf

/--
theorem `nfp_lt_ord_of_isRegular` / 定理 `nfp_lt_ord_of_isRegular`

English:
theorem nfp_lt_ord_of_isRegular
  statement: {f : Ordinal -> Ordinal} {c} (hc : IsRegular c) (hc' : c != ℵ₀)
  proof: nfp_lt_ord (by rw [hc.cof_ord]; exact lt_of_le_of_ne hc.1 hc'.symm) hf

中文:
定理 nfp_lt_ord_of_isRegular
  结论: {f : 序数 -> 序数} {c} (hc : 是正则 c) (hc' : c != ℵ₀)
  证明: nfp_lt_ord (by rw [hc.cof_ord]; exact lt_of_le_of_ne hc.1 hc'.symm) hf

Depends on / 依赖: MetricSpace, T0Space, _root_, _root_.MetricSpace.instT0Space, cof_ord, hc.cof_ord, instT0Space, lt_of_le_of_ne, nfp_lt_ord
-/
theorem nfp_lt_ord_of_isRegular {f : Ordinal -> Ordinal} {c} (hc : IsRegular c) (hc' : c != ℵ₀)
    (hf : forall i < c.ord, f i < c.ord) {a} : a < c.ord -> nfp f a < c.ord :=
  nfp_lt_ord (by rw [hc.cof_ord]; exact lt_of_le_of_ne hc.1 hc'.symm) hf

/--
theorem `derivFamily_lt_ord_lift` / 定理 `derivFamily_lt_ord_lift`

English:
theorem derivFamily_lt_ord_lift
  statement: {ι : Type u} {f : ι -> Ordinal -> Ordinal} {c} (hc : IsRegular c)
  proof: by
  have hω : ℵ₀ < c.ord.cof := by
    rw [hc.cof_ord]
    exact lt_of_le_of_ne hc.1 hc'.symm
  induction a using limitRecOn with
  | zero =>
    rw [derivFamily_zero]
    exact nfpFamily_lt_ord_lift hω (by rwa [hc.cof_ord]) hf
  | add_one b hb =>
    intro hb'
    rw [derivFamily_add_one]
    exac

中文:
定理 derivFamily_lt_ord_lift
  结论: {ι : 类型u} {f : ι -> 序数 -> 序数} {c} (hc : 是正则 c)
  证明: by
  have hω : ℵ₀ < c.ord.cof := by
    rw [hc.cof_ord]
    exact lt_of_le_of_ne hc.1 hc'.symm
  induction a using limitRecOn with
  | zero =>
    rw [derivFamily_zero]
    exact nfpFamily_lt_ord_lift hω (by rwa [hc.cof_ord]) hf
  | add_one b hb =>
    intro hb'
    rw [derivFamily_add_one]
    exac

Depends on / 依赖: Ordinal, Ordinal.lift_iSup_lt_of_lt_cof, add_one, c.ord.cof, cof_ord, derivFamily_add_one, derivFamily_limit, derivFamily_zero, hc.cof_ord, isSuccLimit_ord, lift_cof, lift_iSup_lt_of_lt_cof, limitRecOn, lt_of_le_of_ne, lt_succ, nfpFamily_lt_ord_lift, succ_lt
-/
theorem derivFamily_lt_ord_lift {ι : Type u} {f : ι -> Ordinal -> Ordinal} {c} (hc : IsRegular c)
    (hι : lift.{v} #ι < c) (hc' : c != ℵ₀) (hf : forall i, forall b < c.ord, f i b < c.ord) {a} :
    a < c.ord -> derivFamily f a < c.ord := by
  have hω : ℵ₀ < c.ord.cof := by
    rw [hc.cof_ord]
    exact lt_of_le_of_ne hc.1 hc'.symm
  induction a using limitRecOn with
  | zero =>
    rw [derivFamily_zero]
    exact nfpFamily_lt_ord_lift hω (by rwa [hc.cof_ord]) hf
  | add_one b hb =>
    intro hb'
    rw [derivFamily_add_one]
    exact
      nfpFamily_lt_ord_lift hω (by rwa [hc.cof_ord]) hf
        ((isSuccLimit_ord hc.1).succ_lt (hb ((lt_succ b).trans hb')))
  | limit b hb H =>
    intro hb'
    rw [derivFamily_limit f hb]
    apply Ordinal.lift_iSup_lt_of_lt_cof
    · rwa [← lift_cof, hc.cof_ord, mk_Iio_ordinal, lift_lift, lift_lt, ← lt_ord]
· exact fun i => H i.1 i.2 i.2.trans hb'

/--
theorem `derivFamily_lt_ord` / 定理 `derivFamily_lt_ord`

English:
theorem derivFamily_lt_ord
  statement: {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : IsRegular c) (hι : #ι < c)
  proof: derivFamily_lt_ord_lift hc (by rwa [lift_id]) hc' hf

中文:
定理 derivFamily_lt_ord
  结论: {ι} {f : ι -> 序数 -> 序数} {c} (hc : 是正则 c) (hι : #ι < c)
  证明: derivFamily_lt_ord_lift hc (by rwa [lift_id]) hc' hf

Depends on / 依赖: derivFamily_lt_ord_lift, lift_id
-/
theorem derivFamily_lt_ord {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : IsRegular c) (hι : #ι < c)
    (hc' : c != ℵ₀) (hf : forall (i), forall b < c.ord, f i b < c.ord) {a} :
    a < c.ord -> derivFamily.{u, u} f a < c.ord :=
  derivFamily_lt_ord_lift hc (by rwa [lift_id]) hc' hf

/--
theorem `deriv_lt_ord` / 定理 `deriv_lt_ord`

English:
theorem deriv_lt_ord
  statement: {f : Ordinal.{u} -> Ordinal} {c} (hc : IsRegular c) (hc' : c != ℵ₀)
  proof: derivFamily_lt_ord_lift hc
    (by simpa using Cardinal.one_lt_aleph0.trans (lt_of_le_of_ne hc.1 hc'.symm)) hc' fun _ => hf

中文:
定理 deriv_lt_ord
  结论: {f : 序数.{u} -> 序数} {c} (hc : 是正则 c) (hc' : c != ℵ₀)
  证明: derivFamily_lt_ord_lift hc
    (by simpa using Cardinal.one_lt_aleph0.trans (lt_of_le_of_ne hc.1 hc'.symm)) hc' fun _ => hf

Depends on / 依赖: Cardinal, Cardinal.one_lt_aleph0.trans, EMetricSpace, MetricSpace, _root_, _root_.MetricSpace.toEMetricSpace, derivFamily_lt_ord_lift, lt_of_le_of_ne, one_lt_aleph0, toEMetricSpace
-/
theorem deriv_lt_ord {f : Ordinal.{u} -> Ordinal} {c} (hc : IsRegular c) (hc' : c != ℵ₀)
    (hf : forall i < c.ord, f i < c.ord) {a} : a < c.ord -> deriv f a < c.ord :=
  derivFamily_lt_ord_lift hc
    (by simpa using Cardinal.one_lt_aleph0.trans (lt_of_le_of_ne hc.1 hc'.symm)) hc' fun _ => hf

/-! ### Singular cardinals -/

/-- A cardinal is singular if it is infinite and not regular. -/
@[mk_iff]
/--
Definition of `IsSingular` / `IsSingular` 的定义

English:
structure IsSingular
  parameters: (c : Cardinal)
  axioms and operations (2):
    - aleph0_le : ℵ₀ <= c
    - cof_ord_ne : c.ord.cof != c

中文:
结构 是奇异
  参数: (c : 基数)
  公理与运算 (2 个):
    - aleph0_le : ℵ₀ <= c
    - cof_ord_ne : c.ord.cof != c
-/
structure IsSingular (c : Cardinal) : Prop where
  /-- A singular cardinal is infinite. -/
  aleph0_le : ℵ₀ <= c
  /-- A singular cardinal is not regular, see `IsSingular.not_isRegular`. -/
  cof_ord_ne : c.ord.cof != c

/--
theorem `IsSingular.cof_ord_lt` / 定理 `IsSingular.cof_ord_lt`

English:
theorem IsSingular.cof_ord_lt
  given: (hc : c.IsSingular)
  statement: c.ord.cof < c
  proof: (cof_ord_le c).lt_of_ne hc.cof_ord_ne

中文:
定理 是奇异.cof_ord_lt
  条件: (hc : c.是奇异)
  结论: c.ord.cof < c
  证明: (cof_ord_le c).lt_of_ne hc.cof_ord_ne

Depends on / 依赖: cof_ord_le, cof_ord_ne, hc.cof_ord_ne, lt_of_ne
-/
theorem IsSingular.cof_ord_lt (hc : c.IsSingular) : c.ord.cof < c :=
  (cof_ord_le c).lt_of_ne hc.cof_ord_ne

/--
theorem `IsSingular.natCast_lt` / 定理 `IsSingular.natCast_lt`

English:
theorem IsSingular.natCast_lt
  given: (hc : c.IsSingular) (n : Nat)
  statement: n < c
  proof: natCast_lt_aleph0.trans_le hc.aleph0_le

中文:
定理 是奇异.natCast_lt
  条件: (hc : c.是奇异) (n : 自然数)
  结论: n < c
  证明: natCast_lt_aleph0.trans_le hc.aleph0_le

Depends on / 依赖: aleph0_le, hc.aleph0_le, natCast_lt_aleph0, natCast_lt_aleph0.trans_le, trans_le
-/
theorem IsSingular.natCast_lt (hc : c.IsSingular) (n : Nat) : n < c :=
  natCast_lt_aleph0.trans_le hc.aleph0_le

/--
theorem `IsSingular.pos` / 定理 `IsSingular.pos`

English:
theorem IsSingular.pos
  given: (hc : c.IsSingular)
  statement: 0 < c
  proof: hc.natCast_lt 0

中文:
定理 是奇异.pos
  条件: (hc : c.是奇异)
  结论: 0 < c
  证明: hc.natCast_lt 0

Depends on / 依赖: hc.natCast_lt, natCast_lt
-/
theorem IsSingular.pos (hc : c.IsSingular) : 0 < c :=
  hc.natCast_lt 0

/--
theorem `IsSingular.not_isRegular` / 定理 `IsSingular.not_isRegular`

English:
theorem IsSingular.not_isRegular
  given: (hc : c.IsSingular)
  statement: ¬ c.IsRegular
  proof: fun hc' => hc'.le_cof_ord.not_gt hc.cof_ord_lt

中文:
定理 是奇异.not_isRegular
  条件: (hc : c.是奇异)
  结论: ¬ c.是正则
  证明: fun hc' => hc'.le_cof_ord.not_gt hc.cof_ord_lt

Depends on / 依赖: cof_ord_lt, hc.cof_ord_lt, le_cof_ord, le_cof_ord.not_gt, not_gt
-/
theorem IsSingular.not_isRegular (hc : c.IsSingular) : ¬ c.IsRegular :=
  fun hc' => hc'.le_cof_ord.not_gt hc.cof_ord_lt

/--
theorem `IsRegular.not_isSingular` / 定理 `IsRegular.not_isSingular`

English:
theorem IsRegular.not_isSingular
  given: (hc : c.IsRegular)
  statement: ¬ c.IsSingular
  proof: imp_not_comm.1 IsSingular.not_isRegular hc

@[simp]

中文:
定理 是正则.not_isSingular
  条件: (hc : c.是正则)
  结论: ¬ c.是奇异
  证明: imp_not_comm.1 IsSingular.not_isRegular hc

@[simp]

Depends on / 依赖: IsSingular, IsSingular.not_isRegular, imp_not_comm, not_isRegular
-/
theorem IsRegular.not_isSingular (hc : c.IsRegular) : ¬ c.IsSingular :=
  imp_not_comm.1 IsSingular.not_isRegular hc

@[simp]
/--
theorem `not_isSingular_aleph0` / 定理 `not_isSingular_aleph0`

English:
theorem not_isSingular_aleph0
  statement: ¬ IsSingular ℵ₀
  proof: isRegular_aleph0.not_isSingular

@[simp]

中文:
定理 not_isSingular_aleph0
  结论: ¬ 是奇异 ℵ₀
  证明: isRegular_aleph0.not_isSingular

@[simp]

Depends on / 依赖: isRegular_aleph0, isRegular_aleph0.not_isSingular, not_isSingular
-/
theorem not_isSingular_aleph0 : ¬ IsSingular ℵ₀ :=
  isRegular_aleph0.not_isSingular

@[simp]
/--
theorem `not_isSingular_aleph_one` / 定理 `not_isSingular_aleph_one`

English:
theorem not_isSingular_aleph_one
  statement: ¬ IsSingular ℵ₁
  proof: isRegular_aleph_one.not_isSingular

@[simp]

中文:
定理 not_isSingular_aleph_one
  结论: ¬ 是奇异 ℵ₁
  证明: isRegular_aleph_one.not_isSingular

@[simp]

Depends on / 依赖: isRegular_aleph_one, isRegular_aleph_one.not_isSingular, not_isSingular
-/
theorem not_isSingular_aleph_one : ¬ IsSingular ℵ₁ :=
  isRegular_aleph_one.not_isSingular

@[simp]
/--
theorem `not_isSingular_succ` / 定理 `not_isSingular_succ`

English:
theorem not_isSingular_succ
  given: (c : Cardinal)
  statement: ¬ IsSingular (succ c)
  proof: by
  obtain hc | hc := lt_or_ge c ℵ₀
  · obtain ⟨n, rfl⟩ := lt_aleph0.1 hc
    refine fun h => h.aleph0_le.not_gt ?_
    rw [succ_natCast]; rw [← Nat.cast_add_one]
    exact natCast_lt_aleph0
  · exact (isRegular_succ hc).not_isSingular

@[simp]

中文:
定理 not_isSingular_succ
  条件: (c : 基数)
  结论: ¬ 是奇异 (succ c)
  证明: by
  obtain hc | hc := lt_or_ge c ℵ₀
  · obtain ⟨n, rfl⟩ := lt_aleph0.1 hc
    refine fun h => h.aleph0_le.not_gt ?_
    rw [succ_natCast]; rw [← Nat.cast_add_one]
    exact natCast_lt_aleph0
  · exact (isRegular_succ hc).not_isSingular

@[simp]

Depends on / 依赖: Nat.cast_add_one, aleph0_le, cast_add_one, h.aleph0_le.not_gt, isRegular_succ, lt_aleph0, lt_or_ge, natCast_lt_aleph0, not_gt, not_isSingular, succ_natCast
-/
theorem not_isSingular_succ (c : Cardinal) : ¬ IsSingular (succ c) := by
  obtain hc | hc := lt_or_ge c ℵ₀
  · obtain ⟨n, rfl⟩ := lt_aleph0.1 hc
    refine fun h => h.aleph0_le.not_gt ?_
    rw [succ_natCast]; rw [← Nat.cast_add_one]
    exact natCast_lt_aleph0
  · exact (isRegular_succ hc).not_isSingular

@[simp]
/--
theorem `not_isRegular_aleph_add_one` / 定理 `not_isRegular_aleph_add_one`

English:
theorem not_isRegular_aleph_add_one
  given: (o : Ordinal)
  statement: ¬ IsSingular (ℵ_ (o + 1))
  proof: by
  simp [← succ_aleph]

中文:
定理 not_isRegular_aleph_add_one
  条件: (o : 序数)
  结论: ¬ 是奇异 (ℵ_ (o + 1))
  证明: by
  simp [← succ_aleph]

Depends on / 依赖: succ_aleph
-/
theorem not_isRegular_aleph_add_one (o : Ordinal) : ¬ IsSingular (ℵ_ (o + 1)) := by
  simp [← succ_aleph]

/--
theorem `IsSingular.isSuccLimit` / 定理 `IsSingular.isSuccLimit`

English:
theorem IsSingular.isSuccLimit
  given: (hc : IsSingular c)
  statement: IsSuccLimit c
  proof: by
  rw [Cardinal.isSuccLimit_iff]; rw [isSuccPrelimit_iff_succ_ne]
  refine ⟨hc.pos.ne', ?_⟩
  rintro c rfl
  exact not_isSingular_succ c hc

中文:
定理 是奇异.isSuccLimit
  条件: (hc : 是奇异 c)
  结论: 是SuccLimit c
  证明: by
  rw [Cardinal.isSuccLimit_iff]; rw [isSuccPrelimit_iff_succ_ne]
  refine ⟨hc.pos.ne', ?_⟩
  rintro c rfl
  exact not_isSingular_succ c hc

Depends on / 依赖: Cardinal, Cardinal.isSuccLimit_iff, hc.pos.ne, isSuccLimit_iff, isSuccPrelimit_iff_succ_ne, not_isSingular_succ
-/
theorem IsSingular.isSuccLimit (hc : IsSingular c) : IsSuccLimit c := by
  rw [Cardinal.isSuccLimit_iff]; rw [isSuccPrelimit_iff_succ_ne]
  refine ⟨hc.pos.ne', ?_⟩
  rintro c rfl
  exact not_isSingular_succ c hc

/--
theorem `isRegular_or_isSingular` / 定理 `isRegular_or_isSingular`

English:
theorem isRegular_or_isSingular
  given: (h : ℵ₀ <= c)
  statement: c.IsRegular ∨ c.IsSingular
  proof: by
  rw [isSingular_iff]; rw [← (cof_ord_le c).lt_iff_ne]; rw [← not_le]
  tauto

中文:
定理 isRegular_or_isSingular
  条件: (h : ℵ₀ <= c)
  结论: c.是正则 ∨ c.是奇异
  证明: by
  rw [isSingular_iff]; rw [← (cof_ord_le c).lt_iff_ne]; rw [← not_le]
  tauto

Depends on / 依赖: MetricSpace, Subtype, cof_ord_le, isSingular_iff, lt_iff_ne, not_le
-/
theorem isRegular_or_isSingular (h : ℵ₀ <= c) : c.IsRegular ∨ c.IsSingular := by
  rw [isSingular_iff]; rw [← (cof_ord_le c).lt_iff_ne]; rw [← not_le]
  tauto

/--
theorem `lt_aleph0_or_isRegular_or_isSingular` / 定理 `lt_aleph0_or_isRegular_or_isSingular`

English:
theorem lt_aleph0_or_isRegular_or_isSingular
  statement: c < ℵ₀ ∨ c.IsRegular ∨ c.IsSingular
  proof: by
  have := isRegular_or_isSingular (c := c)
  rw [← not_le]
  tauto

中文:
定理 lt_aleph0_or_isRegular_or_isSingular
  结论: c < ℵ₀ ∨ c.是正则 ∨ c.是奇异
  证明: by
  have := isRegular_or_isSingular (c := c)
  rw [← not_le]
  tauto

Depends on / 依赖: isRegular_or_isSingular, not_le
-/
theorem lt_aleph0_or_isRegular_or_isSingular : c < ℵ₀ ∨ c.IsRegular ∨ c.IsSingular := by
  have := isRegular_or_isSingular (c := c)
  rw [← not_le]
  tauto

/--
theorem `IsSingular.of_not_isRegular` / 定理 `IsSingular.of_not_isRegular`

English:
theorem IsSingular.of_not_isRegular
  given: (h₀ : ℵ₀ <= c) (hc : ¬ IsRegular c)
  statement: IsSingular c
  proof: (isRegular_or_isSingular h₀).resolve_left hc

中文:
定理 是奇异.of_not_isRegular
  条件: (h₀ : ℵ₀ <= c) (hc : ¬ 是正则 c)
  结论: 是奇异 c
  证明: (isRegular_or_isSingular h₀).resolve_left hc

Depends on / 依赖: isRegular_or_isSingular, resolve_left
-/
theorem IsSingular.of_not_isRegular (h₀ : ℵ₀ <= c) (hc : ¬ IsRegular c) : IsSingular c :=
  (isRegular_or_isSingular h₀).resolve_left hc

/--
theorem `IsRegular.of_not_isSingular` / 定理 `IsRegular.of_not_isSingular`

English:
theorem IsRegular.of_not_isSingular
  given: (h₀ : ℵ₀ <= c) (hc : ¬ IsSingular c)
  statement: IsRegular c
  proof: (isRegular_or_isSingular h₀).resolve_right hc

中文:
定理 是正则.of_not_isSingular
  条件: (h₀ : ℵ₀ <= c) (hc : ¬ 是奇异 c)
  结论: 是正则 c
  证明: (isRegular_or_isSingular h₀).resolve_right hc

Depends on / 依赖: isRegular_or_isSingular, resolve_right
-/
theorem IsRegular.of_not_isSingular (h₀ : ℵ₀ <= c) (hc : ¬ IsSingular c) : IsRegular c :=
  (isRegular_or_isSingular h₀).resolve_right hc

/--
theorem `isSingular_aleph_iff` / 定理 `isSingular_aleph_iff`

English:
theorem isSingular_aleph_iff
  given: {o : Ordinal}
  statement: (ℵ_ o).IsSingular ↔ IsSuccLimit o ∧ o.cof < ℵ_ o
  proof: by
  obtain rfl | ⟨a, rfl⟩ | ho := zero_or_succ_or_isSuccLimit o
  · simp
  · simp
  · rw [isSingular_iff, ← (cof_ord_le _).lt_iff_ne]
    simp [ho]

中文:
定理 isSingular_aleph_iff
  条件: {o : 序数}
  结论: (ℵ_ o).是奇异 ↔ 是SuccLimit o ∧ o.cof < ℵ_ o
  证明: by
  obtain rfl | ⟨a, rfl⟩ | ho := zero_or_succ_or_isSuccLimit o
  · simp
  · simp
  · rw [isSingular_iff, ← (cof_ord_le _).lt_iff_ne]
    simp [ho]

Depends on / 依赖: cof_ord_le, isSingular_iff, lt_iff_ne, zero_or_succ_or_isSuccLimit
-/
theorem isSingular_aleph_iff {o : Ordinal} : (ℵ_ o).IsSingular ↔ IsSuccLimit o ∧ o.cof < ℵ_ o := by
  obtain rfl | ⟨a, rfl⟩ | ho := zero_or_succ_or_isSuccLimit o
  · simp
  · simp
  · rw [isSingular_iff, ← (cof_ord_le _).lt_iff_ne]
    simp [ho]

/--
theorem `IsSingular.isSuccLimit_of_aleph` / 定理 `IsSingular.isSuccLimit_of_aleph`

English:
theorem IsSingular.isSuccLimit_of_aleph
  given: {o : Ordinal} (hc : IsSingular (ℵ_ o))
  statement: IsSuccLimit o
  proof: (isSingular_aleph_iff.1 hc).1

中文:
定理 是奇异.isSuccLimit_of_aleph
  条件: {o : 序数} (hc : 是奇异 (ℵ_ o))
  结论: 是SuccLimit o
  证明: (isSingular_aleph_iff.1 hc).1

Depends on / 依赖: isSingular_aleph_iff
-/
theorem IsSingular.isSuccLimit_of_aleph {o : Ordinal} (hc : IsSingular (ℵ_ o)) : IsSuccLimit o :=
  (isSingular_aleph_iff.1 hc).1

/--
theorem `isSingular_aleph_omega0` / 定理 `isSingular_aleph_omega0`

English:
theorem isSingular_aleph_omega0
  statement: (ℵ_ ω).IsSingular
  proof: by simp [isSingular_aleph_iff]

中文:
定理 isSingular_aleph_omega0
  结论: (ℵ_ ω).是奇异
  证明: by simp [isSingular_aleph_iff]

Depends on / 依赖: isSingular_aleph_iff
-/
theorem isSingular_aleph_omega0 : (ℵ_ ω).IsSingular := by simp [isSingular_aleph_iff]

/--
theorem `IsSingular.aleph_omega0_le` / 定理 `IsSingular.aleph_omega0_le`

English:
theorem IsSingular.aleph_omega0_le
  given: (hc : IsSingular c)
  statement: ℵ_ ω <= c
  proof: by
  obtain ⟨o, rfl⟩ := mem_range_aleph_iff.2 hc.aleph0_le
  rw [isSingular_aleph_iff] at hc
  rw [aleph_le_aleph]
  exact omega0_le_of_isSuccLimit hc.1

中文:
定理 是奇异.aleph_omega0_le
  条件: (hc : 是奇异 c)
  结论: ℵ_ ω <= c
  证明: by
  obtain ⟨o, rfl⟩ := mem_range_aleph_iff.2 hc.aleph0_le
  rw [isSingular_aleph_iff] at hc
  rw [aleph_le_aleph]
  exact omega0_le_of_isSuccLimit hc.1

Depends on / 依赖: aleph0_le, aleph_le_aleph, hc.aleph0_le, isSingular_aleph_iff, mem_range_aleph_iff, omega0_le_of_isSuccLimit
-/
theorem IsSingular.aleph_omega0_le (hc : IsSingular c) : ℵ_ ω <= c := by
  obtain ⟨o, rfl⟩ := mem_range_aleph_iff.2 hc.aleph0_le
  rw [isSingular_aleph_iff] at hc
  rw [aleph_le_aleph]
  exact omega0_le_of_isSuccLimit hc.1

/-! ### Inaccessible cardinals -/

/--
Definition of `IsInaccessible` / `IsInaccessible` 的定义

English:
structure IsInaccessible
  parameters: (c : Cardinal)
  axioms and operations (3):
    - aleph0_lt : ℵ₀ < c
    - le_cof_ord : c <= c.ord.cof
    - isStrongPrelimit : IsStrongPrelimit c

中文:
结构 是Inaccessible
  参数: (c : 基数)
  公理与运算 (3 个):
    - aleph0_lt : ℵ₀ < c
    - le_cof_ord : c <= c.ord.cof
    - isStrongPrelimit : IsStrongPrelimit c
-/
structure IsInaccessible (c : Cardinal) : Prop where
  /-- An inaccessible cardinal is uncountable. -/
  aleph0_lt : ℵ₀ < c
  /-- An inaccessible cardinal is equal to its own cofinality, see `IsInaccessible.isRegular`. -/
  le_cof_ord : c <= c.ord.cof
  /-- An inaccessible cardinal is a strong limit, see `IsInaccessible.isStrongLimit`. -/
  protected isStrongPrelimit : IsStrongPrelimit c

/--
theorem `IsInaccessible.nat_lt` / 定理 `IsInaccessible.nat_lt`

English:
theorem IsInaccessible.nat_lt
  given: (h : IsInaccessible c) (n : Nat)
  statement: n < c
  proof: natCast_lt_aleph0.trans h.1

中文:
定理 是Inaccessible.nat_lt
  条件: (h : 是Inaccessible c) (n : 自然数)
  结论: n < c
  证明: natCast_lt_aleph0.trans h.1

Depends on / 依赖: natCast_lt_aleph0, natCast_lt_aleph0.trans
-/
theorem IsInaccessible.nat_lt (h : IsInaccessible c) (n : Nat) : n < c :=
  natCast_lt_aleph0.trans h.1

/--
theorem `IsInaccessible.pos` / 定理 `IsInaccessible.pos`

English:
theorem IsInaccessible.pos
  given: (h : IsInaccessible c)
  statement: 0 < c
  proof: aleph0_pos.trans h.1

中文:
定理 是Inaccessible.pos
  条件: (h : 是Inaccessible c)
  结论: 0 < c
  证明: aleph0_pos.trans h.1

Depends on / 依赖: aleph0_pos, aleph0_pos.trans
-/
theorem IsInaccessible.pos (h : IsInaccessible c) : 0 < c :=
  aleph0_pos.trans h.1

/--
theorem `IsInaccessible.ne_zero` / 定理 `IsInaccessible.ne_zero`

English:
theorem IsInaccessible.ne_zero
  given: (h : IsInaccessible c)
  statement: c != 0
  proof: h.pos.ne'

中文:
定理 是Inaccessible.ne_zero
  条件: (h : 是Inaccessible c)
  结论: c != 0
  证明: h.pos.ne'

Depends on / 依赖: h.pos.ne
-/
theorem IsInaccessible.ne_zero (h : IsInaccessible c) : c != 0 :=
  h.pos.ne'

/--
theorem `IsInaccessible.isRegular` / 定理 `IsInaccessible.isRegular`

English:
theorem IsInaccessible.isRegular
  given: (h : IsInaccessible c)
  statement: IsRegular c
  proof: ⟨h.aleph0_lt.le, h.le_cof_ord⟩

中文:
定理 是Inaccessible.isRegular
  条件: (h : 是Inaccessible c)
  结论: 是正则 c
  证明: ⟨h.aleph0_lt.le, h.le_cof_ord⟩

Depends on / 依赖: aleph0_lt, h.aleph0_lt.le, h.le_cof_ord, le_cof_ord
-/
theorem IsInaccessible.isRegular (h : IsInaccessible c) : IsRegular c :=
  ⟨h.aleph0_lt.le, h.le_cof_ord⟩

/--
theorem `IsInaccessible.isStrongLimit` / 定理 `IsInaccessible.isStrongLimit`

English:
theorem IsInaccessible.isStrongLimit
  given: {c : Cardinal} (h : IsInaccessible c)
  statement: IsStrongLimit c
  proof: ⟨h.ne_zero, h.isStrongPrelimit⟩

中文:
定理 是Inaccessible.isStrongLimit
  条件: {c : 基数} (h : 是Inaccessible c)
  结论: 是StrongLimit c
  证明: ⟨h.ne_zero, h.isStrongPrelimit⟩

Depends on / 依赖: h.isStrongPrelimit, h.ne_zero, isStrongPrelimit, ne_zero
-/
theorem IsInaccessible.isStrongLimit {c : Cardinal} (h : IsInaccessible c) : IsStrongLimit c :=
  ⟨h.ne_zero, h.isStrongPrelimit⟩

/--
theorem `IsInaccessible.isSuccLimit` / 定理 `IsInaccessible.isSuccLimit`

English:
theorem IsInaccessible.isSuccLimit
  given: {c : Cardinal} (h : IsInaccessible c)
  statement: IsSuccLimit c
  proof: h.isStrongLimit.isSuccLimit

中文:
定理 是Inaccessible.isSuccLimit
  条件: {c : 基数} (h : 是Inaccessible c)
  结论: 是SuccLimit c
  证明: h.isStrongLimit.isSuccLimit

Depends on / 依赖: h.isStrongLimit.isSuccLimit, isStrongLimit, isSuccLimit
-/
theorem IsInaccessible.isSuccLimit {c : Cardinal} (h : IsInaccessible c) : IsSuccLimit c :=
  h.isStrongLimit.isSuccLimit

/--
theorem `isInaccessible_def` / 定理 `isInaccessible_def`

English:
theorem isInaccessible_def
  statement: IsInaccessible c ↔ ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c where
  proof: ⟨h.aleph0_lt, h.isRegular, h.isStrongLimit⟩
  mpr := fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂.2, h₃.isStrongPrelimit⟩

中文:
定理 isInaccessible_def
  结论: 是Inaccessible c ↔ ℵ₀ < c ∧ 是正则 c ∧ 是StrongLimit c where
  证明: ⟨h.aleph0_lt, h.isRegular, h.isStrongLimit⟩
  mpr := fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂.2, h₃.isStrongPrelimit⟩

Depends on / 依赖: aleph0_lt, h.aleph0_lt, h.isRegular, h.isStrongLimit, isRegular, isStrongLimit
-/
theorem isInaccessible_def : IsInaccessible c ↔ ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c where
  mp h := ⟨h.aleph0_lt, h.isRegular, h.isStrongLimit⟩
  mpr := fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂.2, h₃.isStrongPrelimit⟩

/--
theorem `IsInaccessible.univ` / 定理 `IsInaccessible.univ`

English:
theorem IsInaccessible.univ
  statement: IsInaccessible univ.{u, v}
  proof: ⟨aleph0_lt_univ, by simp, IsStrongLimit.univ.isStrongPrelimit⟩

中文:
定理 是Inaccessible.univ
  结论: 是Inaccessible univ.{u, v}
  证明: ⟨aleph0_lt_univ, by simp, IsStrongLimit.univ.isStrongPrelimit⟩

Depends on / 依赖: IsStrongLimit, IsStrongLimit.univ.isStrongPrelimit, aleph0_lt_univ, isStrongPrelimit
-/
theorem IsInaccessible.univ : IsInaccessible univ.{u, v} :=
  ⟨aleph0_lt_univ, by simp, IsStrongLimit.univ.isStrongPrelimit⟩

/--
theorem `IsInaccessible.preBeth_ord` / 定理 `IsInaccessible.preBeth_ord`

English:
theorem IsInaccessible.preBeth_ord
  given: (hc : IsInaccessible c)
  statement: preBeth c.ord = c
  proof: by
  apply (preBeth_strictMono.comp ord_strictMono).le_apply.antisymm'
  apply (isNormal_preBeth.le_iff_forall_le (isSuccLimit_ord hc.aleph0_lt.le)).2
  refine fun a ha => le_of_lt ?_
  induction a using WellFoundedLT.induction with | ind a IH
  rw [preBeth]
  apply lift_iSup_lt_of_lt_cof_ord _ _
  

中文:
定理 是Inaccessible.preBeth_ord
  条件: (hc : 是Inaccessible c)
  结论: preBeth c.ord = c
  证明: by
  apply (preBeth_strictMono.comp ord_strictMono).le_apply.antisymm'
  apply (isNormal_preBeth.le_iff_forall_le (isSuccLimit_ord hc.aleph0_lt.le)).2
  refine fun a ha => le_of_lt ?_
  induction a using WellFoundedLT.induction with | ind a IH
  rw [preBeth]
  apply lift_iSup_lt_of_lt_cof_ord _ _
  

Depends on / 依赖: WellFoundedLT, WellFoundedLT.induction, aleph0_lt, antisymm, cof_ord, hb.trans, hc.aleph0_lt.le, hc.isRegular.lift.cof_ord, hc.isStrongPrelimit, isNormal_preBeth, isNormal_preBeth.le_iff_forall_le, isRegular, isStrongPrelimit, isSuccLimit_ord, le_apply, le_apply.antisymm, le_iff_forall_le, le_of_lt, lift_iSup_lt_of_lt_cof_ord, lift_lift
-/
theorem IsInaccessible.preBeth_ord (hc : IsInaccessible c) : preBeth c.ord = c := by
  apply (preBeth_strictMono.comp ord_strictMono).le_apply.antisymm'
  apply (isNormal_preBeth.le_iff_forall_le (isSuccLimit_ord hc.aleph0_lt.le)).2
  refine fun a ha => le_of_lt ?_
  induction a using WellFoundedLT.induction with | ind a IH
  rw [preBeth]
  apply lift_iSup_lt_of_lt_cof_ord _ _
  · rwa [mk_Iio_ordinal, lift_lift, hc.isRegular.lift.cof_ord, lift_lt, ← lt_ord]
  · rintro ⟨b, hb⟩
exact hc.isStrongPrelimit IH _ hb (hb.trans ha)

/--
theorem `IsInaccessible.beth_ord` / 定理 `IsInaccessible.beth_ord`

English:
theorem IsInaccessible.beth_ord
  given: (hc : IsInaccessible c)
  statement: ℶ_ c.ord = c
  proof: by
  rw [← preBeth_of_omega0_sq_le (le_of_lt _)]; rw [hc.preBeth_ord]
  rw [lt_ord]; rw [pow_two]; rw [card_mul]; rw [card_omega0]; rw [aleph0_mul_aleph0]
  exact hc.aleph0_lt

中文:
定理 是Inaccessible.beth_ord
  条件: (hc : 是Inaccessible c)
  结论: ℶ_ c.ord = c
  证明: by
  rw [← preBeth_of_omega0_sq_le (le_of_lt _)]; rw [hc.preBeth_ord]
  rw [lt_ord]; rw [pow_two]; rw [card_mul]; rw [card_omega0]; rw [aleph0_mul_aleph0]
  exact hc.aleph0_lt

Depends on / 依赖: aleph0_lt, aleph0_mul_aleph0, card_mul, card_omega0, hc.aleph0_lt, hc.preBeth_ord, le_of_lt, lt_ord, pow_two, preBeth_of_omega0_sq_le, preBeth_ord
-/
theorem IsInaccessible.beth_ord (hc : IsInaccessible c) : ℶ_ c.ord = c := by
  rw [← preBeth_of_omega0_sq_le (le_of_lt _)]; rw [hc.preBeth_ord]
  rw [lt_ord]; rw [pow_two]; rw [card_mul]; rw [card_omega0]; rw [aleph0_mul_aleph0]
  exact hc.aleph0_lt

/--
theorem `IsInaccessible.preAleph_ord` / 定理 `IsInaccessible.preAleph_ord`

English:
theorem IsInaccessible.preAleph_ord
  given: (hc : IsInaccessible c)
  statement: preAleph c.ord = c
  proof: ((preAleph_le_preBeth _).trans hc.preBeth_ord.le).antisymm
    (preAleph.strictMono.comp ord_strictMono).le_apply

中文:
定理 是Inaccessible.preAleph_ord
  条件: (hc : 是Inaccessible c)
  结论: preAleph c.ord = c
  证明: ((preAleph_le_preBeth _).trans hc.preBeth_ord.le).antisymm
    (preAleph.strictMono.comp ord_strictMono).le_apply

Depends on / 依赖: UniformSpace, antisymm, hc.preBeth_ord.le, le_apply, ord_strictMono, preAleph, preAleph.strictMono.comp, preAleph_le_preBeth, preBeth_ord, strictMono
-/
theorem IsInaccessible.preAleph_ord (hc : IsInaccessible c) : preAleph c.ord = c :=
  ((preAleph_le_preBeth _).trans hc.preBeth_ord.le).antisymm
    (preAleph.strictMono.comp ord_strictMono).le_apply

/--
theorem `IsInaccessible.preAleph_symm_eq_ord` / 定理 `IsInaccessible.preAleph_symm_eq_ord`

English:
theorem IsInaccessible.preAleph_symm_eq_ord
  given: (hc : IsInaccessible c)
  statement: preAleph.symm c = c.ord
  proof: by
  rw [OrderIso.symm_apply_eq]; rw [hc.preAleph_ord]

中文:
定理 是Inaccessible.preAleph_symm_eq_ord
  条件: (hc : 是Inaccessible c)
  结论: preAleph.symm c = c.ord
  证明: by
  rw [OrderIso.symm_apply_eq]; rw [hc.preAleph_ord]

Depends on / 依赖: OrderIso, OrderIso.symm_apply_eq, UniformSpace, hc.preAleph_ord, preAleph_ord, symm_apply_eq
-/
theorem IsInaccessible.preAleph_symm_eq_ord (hc : IsInaccessible c) : preAleph.symm c = c.ord := by
  rw [OrderIso.symm_apply_eq]; rw [hc.preAleph_ord]

/--
theorem `IsInaccessible.aleph_ord` / 定理 `IsInaccessible.aleph_ord`

English:
theorem IsInaccessible.aleph_ord
  given: (hc : IsInaccessible c)
  statement: ℵ_ c.ord = c
  proof: ((aleph_le_beth _).trans hc.beth_ord.le).antisymm (aleph.strictMono.comp ord_strictMono).le_apply

中文:
定理 是Inaccessible.aleph_ord
  条件: (hc : 是Inaccessible c)
  结论: ℵ_ c.ord = c
  证明: ((aleph_le_beth _).trans hc.beth_ord.le).antisymm (aleph.strictMono.comp ord_strictMono).le_apply

Depends on / 依赖: aleph.strictMono.comp, aleph_le_beth, antisymm, beth_ord, hc.beth_ord.le, le_apply, ord_strictMono, strictMono
-/
theorem IsInaccessible.aleph_ord (hc : IsInaccessible c) : ℵ_ c.ord = c :=
  ((aleph_le_beth _).trans hc.beth_ord.le).antisymm (aleph.strictMono.comp ord_strictMono).le_apply

/--
theorem `IsInaccessible.preOmega_ord` / 定理 `IsInaccessible.preOmega_ord`

English:
theorem IsInaccessible.preOmega_ord
  given: (hc : IsInaccessible c)
  statement: preOmega c.ord = c.ord
  proof: by
  rw [← ord_preAleph]; rw [hc.preAleph_ord]

中文:
定理 是Inaccessible.preOmega_ord
  条件: (hc : 是Inaccessible c)
  结论: preOmega c.ord = c.ord
  证明: by
  rw [← ord_preAleph]; rw [hc.preAleph_ord]

Depends on / 依赖: hc.preAleph_ord, ord_preAleph, preAleph_ord
-/
theorem IsInaccessible.preOmega_ord (hc : IsInaccessible c) : preOmega c.ord = c.ord := by
  rw [← ord_preAleph]; rw [hc.preAleph_ord]

/--
theorem `IsInaccessible.omega_ord` / 定理 `IsInaccessible.omega_ord`

English:
theorem IsInaccessible.omega_ord
  given: (hc : IsInaccessible c)
  statement: ω_ c.ord = c.ord
  proof: by
  rw [← ord_aleph]; rw [hc.aleph_ord]

@[simp]

中文:
定理 是Inaccessible.omega_ord
  条件: (hc : 是Inaccessible c)
  结论: ω_ c.ord = c.ord
  证明: by
  rw [← ord_aleph]; rw [hc.aleph_ord]

@[simp]

Depends on / 依赖: Bornology, aleph_ord, hc.aleph_ord, ord_aleph
-/
theorem IsInaccessible.omega_ord (hc : IsInaccessible c) : ω_ c.ord = c.ord := by
  rw [← ord_aleph]; rw [hc.aleph_ord]

@[simp]
/--
theorem `preBeth_univ` / 定理 `preBeth_univ`

English:
theorem preBeth_univ
  statement: preBeth Ordinal.univ.{u, v} = univ.{u, v}
  proof: by
  simpa using IsInaccessible.univ.preBeth_ord

@[simp]

中文:
定理 preBeth_univ
  结论: preBeth 序数.univ.{u, v} = univ.{u, v}
  证明: by
  simpa using IsInaccessible.univ.preBeth_ord

@[simp]

Depends on / 依赖: Bornology, Bornology.induced, IsInaccessible, IsInaccessible.univ.preBeth_ord, induced, preBeth_ord
-/
theorem preBeth_univ : preBeth Ordinal.univ.{u, v} = univ.{u, v} := by
  simpa using IsInaccessible.univ.preBeth_ord

@[simp]
/--
theorem `beth_univ` / 定理 `beth_univ`

English:
theorem beth_univ
  statement: ℶ_ Ordinal.univ.{u, v} = univ.{u, v}
  proof: by
  simpa using IsInaccessible.univ.beth_ord

@[simp]

中文:
定理 beth_univ
  结论: ℶ_ 序数.univ.{u, v} = univ.{u, v}
  证明: by
  simpa using IsInaccessible.univ.beth_ord

@[simp]

Depends on / 依赖: IsInaccessible, IsInaccessible.univ.beth_ord, beth_ord
-/
theorem beth_univ : ℶ_ Ordinal.univ.{u, v} = univ.{u, v} := by
  simpa using IsInaccessible.univ.beth_ord

@[simp]
/--
theorem `preAleph_univ` / 定理 `preAleph_univ`

English:
theorem preAleph_univ
  statement: preAleph Ordinal.univ.{u, v} = univ.{u, v}
  proof: by
  simpa using IsInaccessible.univ.preAleph_ord

@[simp]

中文:
定理 preAleph_univ
  结论: preAleph 序数.univ.{u, v} = univ.{u, v}
  证明: by
  simpa using IsInaccessible.univ.preAleph_ord

@[simp]

Depends on / 依赖: IsInaccessible, IsInaccessible.univ.preAleph_ord, preAleph_ord
-/
theorem preAleph_univ : preAleph Ordinal.univ.{u, v} = univ.{u, v} := by
  simpa using IsInaccessible.univ.preAleph_ord

@[simp]
/--
theorem `preAleph_symm_univ` / 定理 `preAleph_symm_univ`

English:
theorem preAleph_symm_univ
  statement: preAleph.symm univ.{u, v} = Ordinal.univ.{u, v}
  proof: by
  simp [OrderIso.symm_apply_eq]

@[simp]

中文:
定理 preAleph_symm_univ
  结论: preAleph.symm univ.{u, v} = 序数.univ.{u, v}
  证明: by
  simp [OrderIso.symm_apply_eq]

@[simp]

Depends on / 依赖: OrderIso, OrderIso.symm_apply_eq, symm_apply_eq
-/
theorem preAleph_symm_univ : preAleph.symm univ.{u, v} = Ordinal.univ.{u, v} := by
  simp [OrderIso.symm_apply_eq]

@[simp]
/--
theorem `aleph_univ` / 定理 `aleph_univ`

English:
theorem aleph_univ
  statement: ℵ_ Ordinal.univ.{u, v} = univ.{u, v}
  proof: by
  simpa using IsInaccessible.univ.aleph_ord

@[simp]

中文:
定理 aleph_univ
  结论: ℵ_ 序数.univ.{u, v} = univ.{u, v}
  证明: by
  simpa using IsInaccessible.univ.aleph_ord

@[simp]

Depends on / 依赖: IsInaccessible, IsInaccessible.univ.aleph_ord, aleph_ord
-/
theorem aleph_univ : ℵ_ Ordinal.univ.{u, v} = univ.{u, v} := by
  simpa using IsInaccessible.univ.aleph_ord

@[simp]
/--
theorem `_root_.Ordinal.preOmega_univ` / 定理 `_root_.Ordinal.preOmega_univ`

English:
theorem _root_.Ordinal.preOmega_univ
  statement: preOmega Ordinal.univ.{u, v} = Ordinal.univ.{u, v}
  proof: by
  simpa using IsInaccessible.univ.preOmega_ord

@[simp]

中文:
定理 _root_.序数.preOmega_univ
  结论: preOmega 序数.univ.{u, v} = 序数.univ.{u, v}
  证明: by
  simpa using IsInaccessible.univ.preOmega_ord

@[simp]

Depends on / 依赖: IsInaccessible, IsInaccessible.univ.preOmega_ord, preOmega_ord
-/
theorem _root_.Ordinal.preOmega_univ : preOmega Ordinal.univ.{u, v} = Ordinal.univ.{u, v} := by
  simpa using IsInaccessible.univ.preOmega_ord

@[simp]
/--
theorem `_root_.Ordinal.omega_univ` / 定理 `_root_.Ordinal.omega_univ`

English:
theorem _root_.Ordinal.omega_univ
  statement: ω_ Ordinal.univ.{u, v} = Ordinal.univ.{u, v}
  proof: by
  simpa using IsInaccessible.univ.omega_ord

中文:
定理 _root_.序数.omega_univ
  结论: ω_ 序数.univ.{u, v} = 序数.univ.{u, v}
  证明: by
  simpa using IsInaccessible.univ.omega_ord

Depends on / 依赖: IsInaccessible, IsInaccessible.univ.omega_ord, omega_ord
-/
theorem _root_.Ordinal.omega_univ : ω_ Ordinal.univ.{u, v} = Ordinal.univ.{u, v} := by
  simpa using IsInaccessible.univ.omega_ord

end Cardinal
