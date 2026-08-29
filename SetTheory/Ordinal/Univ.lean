/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Universal ordinal and cardinal

`Cardinal.univ` is the cardinality of the cardinals themselves. Likewise, `Ordinal.univ` is the
order type of the ordinals. These are related via `Cardinal.univ.ord = Ordinal.univ` and
`Ordinal.univ.card = Cardinal.univ`.

The cardinal `Cardinal.univ` is strongly inaccessible. This reflects the fact that in ZFC, the
cardinals form a proper class. See `Cardinal.IsInaccessible.univ` for a proof.

## Implementation notes

We actually define `Cardinal.univ` as the cardinality of `Ordinal`, rather than that of `Cardinal`.
This makes the basic API easier to set up. See `Cardinal.mk_cardinal` for a proof that
`Cardinal.univ = #Cardinal`.
-/

@[expose] public section

universe u v w

set_option linter.checkUnivs false in
open Ordinal in
-- intended to be used with explicit universe parameters
/-- The ordinal `univ.{u, v}` is the order type of `Ordinal.{u}` or `Cardinal.{u}`, as an element of
`Ordinal.{v}` (when `u < v`). -/
@[pp_with_univ]
/--
Definition of `Ordinal.univ` / `Ordinal.univ` 的定义

English:
definition Ordinal.univ
  signature: : Ordinal.{max (u + 1) v}
  body: lift.{v, u + 1} (typeLT Ordinal)

中文:
定义 Ordinal.univ
  签名: : Ordinal.{max (u + 1) v}
  定义体: lift.{v, u + 1} (typeLT Ordinal)

Depends on / 依赖: Ordinal, typeLT
-/
def Ordinal.univ : Ordinal.{max (u + 1) v} :=
  lift.{v, u + 1} (typeLT Ordinal)

set_option linter.checkUnivs false in
open Cardinal in
-- intended to be used with explicit universe parameters
/-- The cardinal `univ.{u, v}` is the cardinality of `Ordinal.{u}` or `Cardinal.{u}`, as an element
of `Cardinal.{v}` (when `u < v`). -/
@[pp_with_univ]
/--
Definition of `Cardinal.univ` / `Cardinal.univ` 的定义

English:
definition Cardinal.univ
  signature: : Cardinal.{max (u + 1) v}
  body: lift.{v, u + 1} #Ordinal

中文:
定义 Cardinal.univ
  签名: : Cardinal.{max (u + 1) v}
  定义体: lift.{v, u + 1} #Ordinal

Depends on / 依赖: Ordinal
-/
def Cardinal.univ : Cardinal.{max (u + 1) v} :=
  lift.{v, u + 1} #Ordinal

/-! ### Universal ordinal -/

namespace Ordinal

@[simp]
/--
theorem `type_lt_ordinal` / 定理 `type_lt_ordinal`

English:
theorem type_lt_ordinal
  statement: typeLT Ordinal = univ.{u, u + 1}
  proof: (lift_id _).symm

@[deprecated type_lt_ordinal (since := "2026-03-20")]

中文:
定理 type_lt_ordinal
  结论: typeLT Ordinal = univ.{u, u + 1}
  证明: (lift_id _).symm

@[deprecated type_lt_ordinal (since := "2026-03-20")]

Depends on / 依赖: lift_id
-/
theorem type_lt_ordinal : typeLT Ordinal = univ.{u, u + 1} :=
  (lift_id _).symm

@[deprecated type_lt_ordinal (since := "2026-03-20")]
/--
theorem `univ_id` / 定理 `univ_id`

English:
theorem univ_id
  statement: univ.{u, u + 1} = typeLT Ordinal
  proof: lift_id _

@[simp]

中文:
定理 univ_id
  结论: univ.{u, u + 1} = typeLT Ordinal
  证明: lift_id _

@[simp]

Depends on / 依赖: lift_id
-/
theorem univ_id : univ.{u, u + 1} = typeLT Ordinal :=
  lift_id _

@[simp]
/--
theorem `lift_univ` / 定理 `lift_univ`

English:
theorem lift_univ
  statement: lift.{w} univ.{u, v} = univ.{u, max v w}
  proof: lift_lift _

中文:
定理 lift_univ
  结论: lift.{w} univ.{u, v} = univ.{u, max v w}
  证明: lift_lift _

Depends on / 依赖: lift_lift
-/
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _

/--
theorem `univ_umax` / 定理 `univ_umax`

English:
theorem univ_umax
  statement: univ.{u, max (u + 1) v} = univ.{u, v}
  proof: congr_fun lift_umax _

中文:
定理 univ_umax
  结论: univ.{u, max (u + 1) v} = univ.{u, v}
  证明: congr_fun lift_umax _

Depends on / 依赖: congr_fun, lift_umax
-/
theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _

/--
Definition of `liftPrincipalSeg` / `liftPrincipalSeg` 的定义

English:
definition liftPrincipalSeg
  signature: : Ordinal.{u} <i Ordinal.{max (u + 1) v}
  body: ⟨liftInitialSeg.{max (u + 1) v, u}, univ.{u, v}, by
    refine fun b => inductionOn b ?_; intro β s _
    rw [univ]; rw [← lift_umax]; constructor <;> intro h
    · obtain ⟨a, e⟩ := h
      rw [← e]
      refine inductionOn a ?_
      intro α r _
      exact lift_type_lt.{u, u + 1, max (u + 1) v}.2 

中文:
定义 liftPrincipalSeg
  签名: : Ordinal.{u} <i Ordinal.{max (u + 1) v}
  定义体: ⟨liftInitialSeg.{max (u + 1) v, u}, univ.{u, v}, by
    refine fun b => inductionOn b ?_; intro β s _
    rw [univ]; rw [← lift_umax]; constructor <;> intro h
    · obtain ⟨a, e⟩ := h
      rw [← e]
      refine inductionOn a ?_
      intro α r _
      exact lift_type_lt.{u, u + 1, max (u + 1) v}.2 

Depends on / 依赖: RelIso, RelIso.ofSurjecti, inductionOn, liftInitialSeg, lift_id, lift_type_eq, lift_type_lt, lift_umax, ofSurjecti, typein
-/
def liftPrincipalSeg : Ordinal.{u} <i Ordinal.{max (u + 1) v} :=
  ⟨liftInitialSeg.{max (u + 1) v, u}, univ.{u, v}, by
    refine fun b => inductionOn b ?_; intro β s _
    rw [univ]; rw [← lift_umax]; constructor <;> intro h
    · obtain ⟨a, e⟩ := h
      rw [← e]
      refine inductionOn a ?_
      intro α r _
      exact lift_type_lt.{u, u + 1, max (u + 1) v}.2 ⟨typein r⟩
    · rw [← lift_id (type s)] at h ⊢
      obtain ⟨f⟩ := lift_type_lt.{_,_,v}.1 h
      obtain ⟨f, a, hf⟩ := f
      exists a
      induction a using inductionOn with | type α r
      refine lift_type_eq.{u, max (u + 1) v, max (u + 1) v}.2
        ⟨(RelIso.ofSurjective (RelEmbedding.ofMonotone ?_ ?_) ?_).symm⟩
      · exact fun b => enum r ⟨f b, (hf _).1 ⟨_, rfl⟩⟩
      · refine fun a b h => (typein_lt_typein r).1 ?_
        rw [typein_enum]; rw [typein_enum]
        exact f.map_rel_iff.2 h
      · intro a'
        obtain ⟨b, e⟩ := (hf _).2 (typein_lt_type _ a')
        exists b
        simp only [RelEmbedding.ofMonotone_coe]
        simp [e]⟩

@[simp]
/--
theorem `liftPrincipalSeg_coe` / 定理 `liftPrincipalSeg_coe`

English:
theorem liftPrincipalSeg_coe
  proof: rfl

@[simp]

中文:
定理 liftPrincipalSeg_coe
  证明: rfl

@[simp]
-/
theorem liftPrincipalSeg_coe :
    (liftPrincipalSeg.{u, v} : Ordinal -> Ordinal) = lift.{max (u + 1) v} :=
  rfl

@[simp]
/--
theorem `liftPrincipalSeg_top` / 定理 `liftPrincipalSeg_top`

English:
theorem liftPrincipalSeg_top
  statement: (liftPrincipalSeg.{u, v}).top = univ.{u, v}
  proof: rfl

@[deprecated liftPrincipalSeg_top (since := "2026-03-20")]

中文:
定理 liftPrincipalSeg_top
  结论: (liftPrincipalSeg.{u, v}).top = univ.{u, v}
  证明: rfl

@[deprecated liftPrincipalSeg_top (since := "2026-03-20")]
-/
theorem liftPrincipalSeg_top : (liftPrincipalSeg.{u, v}).top = univ.{u, v} :=
  rfl

@[deprecated liftPrincipalSeg_top (since := "2026-03-20")]
/--
theorem `liftPrincipalSeg_top'` / 定理 `liftPrincipalSeg_top'`

English:
theorem liftPrincipalSeg_top'
  statement: liftPrincipalSeg.{u, u + 1}.top = typeLT Ordinal
  proof: by
  simp

@[simp]

中文:
定理 liftPrincipalSeg_top'
  结论: liftPrincipalSeg.{u, u + 1}.top = typeLT Ordinal
  证明: by
  simp

@[simp]
-/
theorem liftPrincipalSeg_top' : liftPrincipalSeg.{u, u + 1}.top = typeLT Ordinal := by
  simp

@[simp]
/--
theorem `card_univ` / 定理 `card_univ`

English:
theorem card_univ
  statement: card univ.{u, v} = Cardinal.univ.{u, v}
  proof: rfl

中文:
定理 card_univ
  结论: card univ.{u, v} = Cardinal.univ.{u, v}
  证明: rfl
-/
theorem card_univ : card univ.{u, v} = Cardinal.univ.{u, v} :=
  rfl

end Ordinal

/-! ### Universal cardinal -/

namespace Cardinal

@[simp]
/--
theorem `mk_ordinal` / 定理 `mk_ordinal`

English:
theorem mk_ordinal
  statement: #Ordinal = univ.{u, u + 1}
  proof: (lift_id _).symm

@[deprecated mk_ordinal (since := "2026-04-22")]

中文:
定理 mk_ordinal
  结论: #Ordinal = univ.{u, u + 1}
  证明: (lift_id _).symm

@[deprecated mk_ordinal (since := "2026-04-22")]

Depends on / 依赖: lift_id
-/
theorem mk_ordinal : #Ordinal = univ.{u, u + 1} :=
  (lift_id _).symm

@[deprecated mk_ordinal (since := "2026-04-22")]
/--
theorem `univ_id` / 定理 `univ_id`

English:
theorem univ_id
  statement: univ.{u, u + 1} = #Ordinal
  proof: lift_id _

@[simp]

中文:
定理 univ_id
  结论: univ.{u, u + 1} = #Ordinal
  证明: lift_id _

@[simp]

Depends on / 依赖: lift_id
-/
theorem univ_id : univ.{u, u + 1} = #Ordinal :=
  lift_id _

@[simp]
/--
theorem `lift_univ` / 定理 `lift_univ`

English:
theorem lift_univ
  statement: lift.{w} univ.{u, v} = univ.{u, max v w}
  proof: lift_lift _

中文:
定理 lift_univ
  结论: lift.{w} univ.{u, v} = univ.{u, max v w}
  证明: lift_lift _

Depends on / 依赖: lift_lift
-/
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _

/--
theorem `univ_umax` / 定理 `univ_umax`

English:
theorem univ_umax
  statement: univ.{u, max (u + 1) v} = univ.{u, v}
  proof: congr_fun lift_umax _

中文:
定理 univ_umax
  结论: univ.{u, max (u + 1) v} = univ.{u, v}
  证明: congr_fun lift_umax _

Depends on / 依赖: congr_fun, lift_umax
-/
theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _

/--
theorem `lift_lt_univ` / 定理 `lift_lt_univ`

English:
theorem lift_lt_univ
  given: (c : Cardinal)
  statement: lift.{u + 1, u} c < univ.{u, u + 1}
  proof: by
  simpa only [Ordinal.liftPrincipalSeg_coe, lift_ord, lift_succ, ord_le, Order.succ_le_iff] using!
    le_of_lt (Ordinal.liftPrincipalSeg.{u, u + 1}.lt_top (Order.succ c).ord)

中文:
定理 lift_lt_univ
  条件: (c : Cardinal)
  结论: lift.{u + 1, u} c < univ.{u, u + 1}
  证明: by
  simpa only [Ordinal.liftPrincipalSeg_coe, lift_ord, lift_succ, ord_le, Order.succ_le_iff] using!
    le_of_lt (Ordinal.liftPrincipalSeg.{u, u + 1}.lt_top (Order.succ c).ord)

Depends on / 依赖: Order.succ, Order.succ_le_iff, Ordinal, Ordinal.liftPrincipalSeg, Ordinal.liftPrincipalSeg_coe, le_of_lt, liftPrincipalSeg, liftPrincipalSeg_coe, lift_ord, lift_succ, lt_top, ord_le, succ_le_iff
-/
theorem lift_lt_univ (c : Cardinal) : lift.{u + 1, u} c < univ.{u, u + 1} := by
  simpa only [Ordinal.liftPrincipalSeg_coe, lift_ord, lift_succ, ord_le, Order.succ_le_iff] using!
    le_of_lt (Ordinal.liftPrincipalSeg.{u, u + 1}.lt_top (Order.succ c).ord)

/--
theorem `lift_lt_univ'` / 定理 `lift_lt_univ'`

English:
theorem lift_lt_univ'
  given: (c : Cardinal)
  statement: lift.{max (u + 1) v, u} c < univ.{u, v}
  proof: by
  have := lift_lt.{_, max (u + 1) v}.2 (lift_lt_univ c)
  rw [lift_lift]; rw [lift_univ]; rw [univ_umax.{u]; rw [v}] at this
  exact this

@[simp]

中文:
定理 lift_lt_univ'
  条件: (c : Cardinal)
  结论: lift.{max (u + 1) v, u} c < univ.{u, v}
  证明: by
  have := lift_lt.{_, max (u + 1) v}.2 (lift_lt_univ c)
  rw [lift_lift]; rw [lift_univ]; rw [univ_umax.{u]; rw [v}] at this
  exact this

@[simp]

Depends on / 依赖: lift_lift, lift_lt, lift_lt_univ, lift_univ, univ_umax
-/
theorem lift_lt_univ' (c : Cardinal) : lift.{max (u + 1) v, u} c < univ.{u, v} := by
  have := lift_lt.{_, max (u + 1) v}.2 (lift_lt_univ c)
  rw [lift_lift]; rw [lift_univ]; rw [univ_umax.{u]; rw [v}] at this
  exact this

@[simp]
/--
theorem `aleph0_lt_univ` / 定理 `aleph0_lt_univ`

English:
theorem aleph0_lt_univ
  statement: ℵ₀ < univ.{u, v}
  proof: by
  simpa using lift_lt_univ' ℵ₀

@[simp]

中文:
定理 aleph0_lt_univ
  结论: ℵ₀ < univ.{u, v}
  证明: by
  simpa using lift_lt_univ' ℵ₀

@[simp]

Depends on / 依赖: lift_lt_univ
-/
theorem aleph0_lt_univ : ℵ₀ < univ.{u, v} := by
  simpa using lift_lt_univ' ℵ₀

@[simp]
/--
theorem `nat_lt_univ` / 定理 `nat_lt_univ`

English:
theorem nat_lt_univ
  given: (n : Nat)
  statement: n < univ.{u, v}
  proof: natCast_lt_aleph0.trans aleph0_lt_univ

@[simp]

中文:
定理 nat_lt_univ
  条件: (n : 自然数)
  结论: n < univ.{u, v}
  证明: natCast_lt_aleph0.trans aleph0_lt_univ

@[simp]

Depends on / 依赖: aleph0_lt_univ, natCast_lt_aleph0, natCast_lt_aleph0.trans
-/
theorem nat_lt_univ (n : Nat) : n < univ.{u, v} := natCast_lt_aleph0.trans aleph0_lt_univ

@[simp]
/--
theorem `univ_pos` / 定理 `univ_pos`

English:
theorem univ_pos
  statement: 0 < univ.{u, v}
  proof: aleph0_lt_univ.pos

@[simp]

中文:
定理 univ_pos
  结论: 0 < univ.{u, v}
  证明: aleph0_lt_univ.pos

@[simp]

Depends on / 依赖: aleph0_lt_univ, aleph0_lt_univ.pos
-/
theorem univ_pos : 0 < univ.{u, v} :=
  aleph0_lt_univ.pos

@[simp]
/--
theorem `univ_ne_zero` / 定理 `univ_ne_zero`

English:
theorem univ_ne_zero
  statement: univ.{u, v} != 0
  proof: univ_pos.ne'

@[simp]

中文:
定理 univ_ne_zero
  结论: univ.{u, v} != 0
  证明: univ_pos.ne'

@[simp]

Depends on / 依赖: univ_pos, univ_pos.ne
-/
theorem univ_ne_zero : univ.{u, v} != 0 :=
  univ_pos.ne'

@[simp]
/--
theorem `ord_univ` / 定理 `ord_univ`

English:
theorem ord_univ
  statement: ord univ.{u, v} = Ordinal.univ.{u, v}
  proof: by
refine le_antisymm (ord_card_le _) le_of_forall_lt fun o h => lt_ord.2 ?_
  have := Ordinal.liftPrincipalSeg.mem_range_of_rel_top (by simpa using h)
  rcases this with ⟨o, h'⟩
  rw [← h']; rw [Ordinal.liftPrincipalSeg_coe]; rw [← Ordinal.lift_card]
  apply lift_lt_univ'

中文:
定理 ord_univ
  结论: ord univ.{u, v} = Ordinal.univ.{u, v}
  证明: by
refine le_antisymm (ord_card_le _) le_of_forall_lt fun o h => lt_ord.2 ?_
  have := Ordinal.liftPrincipalSeg.mem_range_of_rel_top (by simpa using h)
  rcases this with ⟨o, h'⟩
  rw [← h']; rw [Ordinal.liftPrincipalSeg_coe]; rw [← Ordinal.lift_card]
  apply lift_lt_univ'

Depends on / 依赖: Ordinal, Ordinal.liftPrincipalSeg.mem_range_of_rel_top, Ordinal.liftPrincipalSeg_coe, Ordinal.lift_card, le_antisymm, le_of_forall_lt, liftPrincipalSeg, liftPrincipalSeg_coe, lift_card, lift_lt_univ, lt_ord, mem_range_of_rel_top, ord_card_le
-/
theorem ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v} := by
refine le_antisymm (ord_card_le _) le_of_forall_lt fun o h => lt_ord.2 ?_
  have := Ordinal.liftPrincipalSeg.mem_range_of_rel_top (by simpa using h)
  rcases this with ⟨o, h'⟩
  rw [← h']; rw [Ordinal.liftPrincipalSeg_coe]; rw [← Ordinal.lift_card]
  apply lift_lt_univ'

/--
theorem `lt_univ` / 定理 `lt_univ`

English:
theorem lt_univ
  given: {c}
  statement: c < univ.{u, u + 1} ↔ exists c', c = lift.{u + 1, u} c'
  proof: ⟨fun h => by
    have := ord_lt_ord.2 h
    rw [ord_univ] at this
    obtain ⟨o, e⟩ := Ordinal.liftPrincipalSeg.mem_range_of_rel_top (by simpa)
    have := card_ord c
    rw [← e]; rw [Ordinal.liftPrincipalSeg_coe]; rw [← Ordinal.lift_card] at this
    exact ⟨_, this.symm⟩, fun ⟨_, e⟩ => e.symm ▸ li

中文:
定理 lt_univ
  条件: {c}
  结论: c < univ.{u, u + 1} ↔ 存在 c', c = lift.{u + 1, u} c'
  证明: ⟨fun h => by
    have := ord_lt_ord.2 h
    rw [ord_univ] at this
    obtain ⟨o, e⟩ := Ordinal.liftPrincipalSeg.mem_range_of_rel_top (by simpa)
    have := card_ord c
    rw [← e]; rw [Ordinal.liftPrincipalSeg_coe]; rw [← Ordinal.lift_card] at this
    exact ⟨_, this.symm⟩, fun ⟨_, e⟩ => e.symm ▸ li

Depends on / 依赖: Ordinal, Ordinal.liftPrincipalSeg.mem_range_of_rel_top, Ordinal.liftPrincipalSeg_coe, Ordinal.lift_card, card_ord, e.symm, liftPrincipalSeg, liftPrincipalSeg_coe, lift_card, lift_lt_univ, mem_range_of_rel_top, ord_lt_ord, ord_univ, this.symm
-/
theorem lt_univ {c} : c < univ.{u, u + 1} ↔ exists c', c = lift.{u + 1, u} c' :=
  ⟨fun h => by
    have := ord_lt_ord.2 h
    rw [ord_univ] at this
    obtain ⟨o, e⟩ := Ordinal.liftPrincipalSeg.mem_range_of_rel_top (by simpa)
    have := card_ord c
    rw [← e]; rw [Ordinal.liftPrincipalSeg_coe]; rw [← Ordinal.lift_card] at this
    exact ⟨_, this.symm⟩, fun ⟨_, e⟩ => e.symm ▸ lift_lt_univ _⟩

/--
theorem `lt_univ'` / 定理 `lt_univ'`

English:
theorem lt_univ'
  given: {c}
  statement: c < univ.{u, v} ↔ exists c', c = lift.{max (u + 1) v, u} c'
  proof: ⟨fun h => by
    let ⟨a, h', e⟩ := lt_lift_iff.1 h
    rw [mk_ordinal] at h'
    rcases lt_univ.{u}.1 h' with ⟨c', rfl⟩
    exact ⟨c', by simp only [e.symm, lift_lift]⟩, fun ⟨_, e⟩ => e.symm ▸ lift_lt_univ' _⟩

中文:
定理 lt_univ'
  条件: {c}
  结论: c < univ.{u, v} ↔ 存在 c', c = lift.{max (u + 1) v, u} c'
  证明: ⟨fun h => by
    let ⟨a, h', e⟩ := lt_lift_iff.1 h
    rw [mk_ordinal] at h'
    rcases lt_univ.{u}.1 h' with ⟨c', rfl⟩
    exact ⟨c', by simp only [e.symm, lift_lift]⟩, fun ⟨_, e⟩ => e.symm ▸ lift_lt_univ' _⟩

Depends on / 依赖: e.symm, lift_lift, lift_lt_univ, lt_lift_iff, lt_univ, mk_ordinal
-/
theorem lt_univ' {c} : c < univ.{u, v} ↔ exists c', c = lift.{max (u + 1) v, u} c' :=
  ⟨fun h => by
    let ⟨a, h', e⟩ := lt_lift_iff.1 h
    rw [mk_ordinal] at h'
    rcases lt_univ.{u}.1 h' with ⟨c', rfl⟩
    exact ⟨c', by simp only [e.symm, lift_lift]⟩, fun ⟨_, e⟩ => e.symm ▸ lift_lt_univ' _⟩

/--
theorem `IsStrongLimit.univ` / 定理 `IsStrongLimit.univ`

English:
theorem IsStrongLimit.univ
  statement: IsStrongLimit univ.{u, v}
  proof: ⟨univ_ne_zero, fun c h => let ⟨w, h⟩ := lt_univ'.1 h; lt_univ'.2 ⟨2 ^ w, by simp [h]⟩⟩

中文:
定理 IsStrongLimit.univ
  结论: IsStrongLimit univ.{u, v}
  证明: ⟨univ_ne_zero, fun c h => let ⟨w, h⟩ := lt_univ'.1 h; lt_univ'.2 ⟨2 ^ w, by simp [h]⟩⟩

Depends on / 依赖: lt_univ, univ_ne_zero
-/
theorem IsStrongLimit.univ : IsStrongLimit univ.{u, v} :=
  ⟨univ_ne_zero, fun c h => let ⟨w, h⟩ := lt_univ'.1 h; lt_univ'.2 ⟨2 ^ w, by simp [h]⟩⟩

/--
theorem `small_iff_lift_mk_lt_univ` / 定理 `small_iff_lift_mk_lt_univ`

English:
theorem small_iff_lift_mk_lt_univ
  given: {α : Type u}
  proof: by
  rw [lt_univ']
  constructor
  · rintro ⟨β, e⟩
    exact ⟨#β, lift_mk_eq.{u, _, v + 1}.2 e⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c.out, lift_mk_eq.{u, _, v + 1}.1 (hc.trans (congr rfl c.mk_out.symm))⟩⟩

中文:
定理 small_iff_lift_mk_lt_univ
  条件: {α : 类型u}
  证明: by
  rw [lt_univ']
  constructor
  · rintro ⟨β, e⟩
    exact ⟨#β, lift_mk_eq.{u, _, v + 1}.2 e⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c.out, lift_mk_eq.{u, _, v + 1}.1 (hc.trans (congr rfl c.mk_out.symm))⟩⟩

Depends on / 依赖: c.mk_out.symm, c.out, hc.trans, lift_mk_eq, lt_univ, mk_out
-/
theorem small_iff_lift_mk_lt_univ {α : Type u} :
    Small.{v} α ↔ Cardinal.lift.{v + 1, _} #α < univ.{v, max u (v + 1)} := by
  rw [lt_univ']
  constructor
  · rintro ⟨β, e⟩
    exact ⟨#β, lift_mk_eq.{u, _, v + 1}.2 e⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c.out, lift_mk_eq.{u, _, v + 1}.1 (hc.trans (congr rfl c.mk_out.symm))⟩⟩

end Cardinal
