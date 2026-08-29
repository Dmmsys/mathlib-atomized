/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li, Joachim Breitner
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.SuccPred.WithBot
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Order.Atoms
public import Mathlib.Order.RelSeries
public import Mathlib.Tactic.FinCases

/-!
# Krull dimension of a preordered set and height of an element

If `α` is a preordered set, then `krullDim α : WithBot ℕ∞` is defined to be
`sup {n | a₀ < a₁ < ... < aₙ}`.

In case that `α` is empty, then its Krull dimension is defined to be negative infinity; if the
length of all series `a₀ < a₁ < ... < aₙ` is unbounded, then its Krull dimension is defined to be
positive infinity.

For `a : α`, its height (in `ℕ∞`) is defined to be `sup {n | a₀ < a₁ < ... < aₙ ≤ a}`, while its
coheight is defined to be `sup {n | a ≤ a₀ < a₁ < ... < aₙ}` .

## Main results

* The Krull dimension is the same as that of the dual order (`krullDim_orderDual`).

* The Krull dimension is the supremum of the heights of the elements (`krullDim_eq_iSup_height`),
  or their coheights (`krullDim_eq_iSup_coheight`), or their sums of height and coheight
  (`krullDim_eq_iSup_height_add_coheight_of_nonempty`)

* The height in the dual order equals the coheight, and vice versa.

* The height is monotone (`height_mono`), and strictly monotone if finite (`height_strictMono`).

* The coheight is antitone (`coheight_anti`), and strictly antitone if finite
  (`coheight_strictAnti`).

* The height is the supremum of the successor of the height of all smaller elements
  (`height_eq_iSup_lt_height`).

* The elements of height zero are the minimal elements (`height_eq_zero`), and the elements of
  height `n` are minimal among those of height `≥ n` (`height_eq_coe_iff_minimal_le_height`).

* Concrete calculations for the height, coheight and Krull dimension in `ℕ`, `ℤ`, `WithTop`,
  `WithBot` and `ℕ∞`.

## Design notes

Krull dimensions are defined to take value in `WithBot ℕ∞` so that `(-∞) + (+∞)` is
also negative infinity. This is because we want Krull dimensions to be additive with respect
to product of varieties so that `-∞` being the Krull dimension of empty variety is equal to
sum of `-∞` and the Krull dimension of any other varieties.

We could generalize the notion of Krull dimension to an arbitrary binary relation; many results
in this file would generalize as well. But we don't think it would be useful, so we only define
Krull dimension of a preorder.
-/

@[expose] public section

assert_not_exists Field

namespace Order

section definitions

/--
Definition of `krullDim` / `krullDim` 的定义

English:
definition krullDim
  signature: (α : Type*) [Preorder α]
  body: ⨆ (p : LTSeries α), p.length

中文:
定义 krullDim
  签名: (α : 类型) [预序 α]
  定义体: ⨆ (p : LTSeries α), p.length

Depends on / 依赖: LTSeries, length, p.length
-/
noncomputable def krullDim (α : Type*) [Preorder α] : WithBot Nat∞ :=
  ⨆ (p : LTSeries α), p.length

/--
Definition of `height` / `height` 的定义

English:
definition height
  signature: {α : Type*} [Preorder α] (a : α)
  body: ⨆ (p : LTSeries α) (_ : p.last <= a), p.length

中文:
定义 height
  签名: {α : 类型} [预序 α] (a : α)
  定义体: ⨆ (p : LTSeries α) (_ : p.last <= a), p.length

Depends on / 依赖: LTSeries, length, p.last, p.length
-/
noncomputable def height {α : Type*} [Preorder α] (a : α) : Nat∞ :=
  ⨆ (p : LTSeries α) (_ : p.last <= a), p.length

/--
Definition of `coheight` / `coheight` 的定义

English:
definition coheight
  signature: {α : Type*} [Preorder α] (a : α)
  body: height (α := αᵒᵈ) a

中文:
定义 coheight
  签名: {α : 类型} [预序 α] (a : α)
  定义体: height (α := αᵒᵈ) a

Depends on / 依赖: height
-/
noncomputable def coheight {α : Type*} [Preorder α] (a : α) : Nat∞ := height (α := αᵒᵈ) a

end definitions

/-!
## Height
-/

section height

variable {α β : Type*}

variable [Preorder α] [Preorder β]

/--
lemma `height_toDual` / 引理 `height_toDual`

English:
lemma height_toDual
  given: (x : α)
  statement: height (OrderDual.toDual x) = coheight x
  proof: rfl

中文:
引理 height_toDual
  条件: (x : α)
  结论: height (OrderDual.toDual x) = coheight x
  证明: rfl
-/
@[simp] lemma height_toDual (x : α) : height (OrderDual.toDual x) = coheight x := rfl
/--
lemma `height_ofDual` / 引理 `height_ofDual`

English:
lemma height_ofDual
  given: (x : αᵒᵈ)
  statement: height (OrderDual.ofDual x) = coheight x
  proof: rfl

中文:
引理 height_ofDual
  条件: (x : αᵒᵈ)
  结论: height (OrderDual.ofDual x) = coheight x
  证明: rfl
-/
@[simp] lemma height_ofDual (x : αᵒᵈ) : height (OrderDual.ofDual x) = coheight x := rfl
/--
lemma `coheight_toDual` / 引理 `coheight_toDual`

English:
lemma coheight_toDual
  given: (x : α)
  statement: coheight (OrderDual.toDual x) = height x
  proof: rfl

中文:
引理 coheight_toDual
  条件: (x : α)
  结论: coheight (OrderDual.toDual x) = height x
  证明: rfl
-/
@[simp] lemma coheight_toDual (x : α) : coheight (OrderDual.toDual x) = height x := rfl
/--
lemma `coheight_ofDual` / 引理 `coheight_ofDual`

English:
lemma coheight_ofDual
  given: (x : αᵒᵈ)
  statement: coheight (OrderDual.ofDual x) = height x
  proof: rfl

中文:
引理 coheight_ofDual
  条件: (x : αᵒᵈ)
  结论: coheight (OrderDual.ofDual x) = height x
  证明: rfl
-/
@[simp] lemma coheight_ofDual (x : αᵒᵈ) : coheight (OrderDual.ofDual x) = height x := rfl

/--
lemma `coheight_eq` / 引理 `coheight_eq`

English:
lemma coheight_eq
  given: (a : α)
  proof: by
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, fun _ => RelSeries.reverse_reverse _,
    fun _ => RelSeries.reverse_reverse _⟩
  congr! 1

中文:
引理 coheight_eq
  条件: (a : α)
  证明: by
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, fun _ => RelSeries.reverse_reverse _,
    fun _ => RelSeries.reverse_reverse _⟩
  congr! 1

Depends on / 依赖: Equiv.iSup_congr, RelSeries, RelSeries.reverse, RelSeries.reverse_reverse, iSup_congr, reverse, reverse_reverse
-/
lemma coheight_eq (a : α) :
    coheight a = ⨆ (p : LTSeries α) (_ : a <= p.head), (p.length : Nat∞) := by
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, fun _ => RelSeries.reverse_reverse _,
    fun _ => RelSeries.reverse_reverse _⟩
  congr! 1

/--
lemma `height_le_iff` / 引理 `height_le_iff`

English:
lemma height_le_iff
  given: {a : α} {n : Nat∞}
  proof: by
  rw [height]; rw [iSup₂_le_iff]

中文:
引理 height_le_iff
  条件: {a : α} {n : 自然数∞}
  证明: by
  rw [height]; rw [iSup₂_le_iff]

Depends on / 依赖: height
-/
lemma height_le_iff {a : α} {n : Nat∞} :
    height a <= n ↔ forall ⦃p : LTSeries α⦄, p.last <= a -> p.length <= n := by
  rw [height]; rw [iSup₂_le_iff]

/--
lemma `coheight_le_iff` / 引理 `coheight_le_iff`

English:
lemma coheight_le_iff
  given: {a : α} {n : Nat∞}
  proof: by
  rw [coheight_eq]; rw [iSup₂_le_iff]

中文:
引理 coheight_le_iff
  条件: {a : α} {n : 自然数∞}
  证明: by
  rw [coheight_eq]; rw [iSup₂_le_iff]

Depends on / 依赖: coheight_eq
-/
lemma coheight_le_iff {a : α} {n : Nat∞} :
    coheight a <= n ↔ forall ⦃p : LTSeries α⦄, a <= p.head -> p.length <= n := by
  rw [coheight_eq]; rw [iSup₂_le_iff]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `height_le` / 引理 `height_le`

English:
lemma height_le
  given: {a : α} {n : Nat∞} (h : forall (p : LTSeries α), p.last = a -> p.length <= n)
  proof: by
  apply height_le_iff.mpr
  intro p hlast
  wlog hlenpos : p.length != 0
  · simp_all
  -- We replace the last element in the series with `a`
  let p' := p.eraseLast.snoc a (lt_of_lt_of_le (p.eraseLast_last_rel_last (by simp_all)) hlast)
  rw [show p.length = p'.length by simp [p']; lia]
  apply h
  simp [p']

中文:
引理 height_le
  条件: {a : α} {n : 自然数∞} (h : 对任意 (p : LTSeries α), p.last = a -> p.length <= n)
  证明: by
  apply height_le_iff.mpr
  intro p hlast
  wlog hlenpos : p.length != 0
  · simp_all
  -- We replace the last element in the series with `a`
  let p' := p.eraseLast.snoc a (lt_of_lt_of_le (p.eraseLast_last_rel_last (by simp_all)) hlast)
  rw [show p.length = p'.length by simp [p']; lia]
  apply h
  simp [p']

Depends on / 依赖: height_le_iff, height_le_iff.mpr, hlenpos, length, p.length
-/
lemma height_le {a : α} {n : Nat∞} (h : forall (p : LTSeries α), p.last = a -> p.length <= n) :
    height a <= n := by
  apply height_le_iff.mpr
  intro p hlast
  wlog hlenpos : p.length != 0
  · simp_all
  -- We replace the last element in the series with `a`
  let p' := p.eraseLast.snoc a (lt_of_lt_of_le (p.eraseLast_last_rel_last (by simp_all)) hlast)
  rw [show p.length = p'.length by simp [p']; lia]
  apply h
  simp [p']

/--
lemma `height_le_iff'` / 引理 `height_le_iff'`

English:
lemma height_le_iff'
  given: {a : α} {n : Nat∞}
  proof: by
  constructor
  · rw [height_le_iff]
    exact fun h p hlast => h (le_of_eq hlast)
  · exact height_le

中文:
引理 height_le_iff'
  条件: {a : α} {n : 自然数∞}
  证明: by
  constructor
  · rw [height_le_iff]
    exact fun h p hlast => h (le_of_eq hlast)
  · exact height_le

Depends on / 依赖: height_le, height_le_iff, le_of_eq
-/
lemma height_le_iff' {a : α} {n : Nat∞} :
    height a <= n ↔ forall ⦃p : LTSeries α⦄, p.last = a -> p.length <= n := by
  constructor
  · rw [height_le_iff]
    exact fun h p hlast => h (le_of_eq hlast)
  · exact height_le

/--
lemma `height_eq_iSup_last_eq` / 引理 `height_eq_iSup_last_eq`

English:
lemma height_eq_iSup_last_eq
  given: (a : α)
  proof: by
  apply eq_of_forall_ge_iff
  intro n
  rw [height_le_iff']; rw [iSup₂_le_iff]

中文:
引理 height_eq_iSup_last_eq
  条件: (a : α)
  证明: by
  apply eq_of_forall_ge_iff
  intro n
  rw [height_le_iff']; rw [iSup₂_le_iff]

Depends on / 依赖: eq_of_forall_ge_iff, height_le_iff
-/
lemma height_eq_iSup_last_eq (a : α) :
    height a = ⨆ (p : LTSeries α) (_ : p.last = a), ↑(p.length) := by
  apply eq_of_forall_ge_iff
  intro n
  rw [height_le_iff']; rw [iSup₂_le_iff]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coheight_eq_iSup_head_eq` / 引理 `coheight_eq_iSup_head_eq`

English:
lemma coheight_eq_iSup_head_eq
  given: (a : α)
  proof: by
  change height (α := αᵒᵈ) a = ⨆ (p : LTSeries α) (_ : p.head = a), ↑(p.length)
  rw [height_eq_iSup_last_eq]
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, fun _ => RelSeries.reverse_reverse _,
    fun _ => RelSeries.reverse_reverse _⟩
  simp

中文:
引理 coheight_eq_iSup_head_eq
  条件: (a : α)
  证明: by
  change height (α := αᵒᵈ) a = ⨆ (p : LTSeries α) (_ : p.head = a), ↑(p.length)
  rw [height_eq_iSup_last_eq]
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, fun _ => RelSeries.reverse_reverse _,
    fun _ => RelSeries.reverse_reverse _⟩
  simp

Depends on / 依赖: Equiv.iSup_congr, LTSeries, RelSeries, RelSeries.reverse, RelSeries.reverse_reverse, height, height_eq_iSup_last_eq, iSup_congr, length, p.head, p.length, reverse, reverse_reverse
-/
lemma coheight_eq_iSup_head_eq (a : α) :
    coheight a = ⨆ (p : LTSeries α) (_ : p.head = a), ↑(p.length) := by
  change height (α := αᵒᵈ) a = ⨆ (p : LTSeries α) (_ : p.head = a), ↑(p.length)
  rw [height_eq_iSup_last_eq]
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, fun _ => RelSeries.reverse_reverse _,
    fun _ => RelSeries.reverse_reverse _⟩
  simp

/--
lemma `coheight_le_iff'` / 引理 `coheight_le_iff'`

English:
lemma coheight_le_iff'
  given: {a : α} {n : Nat∞}
  proof: by
  rw [coheight_eq_iSup_head_eq]; rw [iSup₂_le_iff]

中文:
引理 coheight_le_iff'
  条件: {a : α} {n : 自然数∞}
  证明: by
  rw [coheight_eq_iSup_head_eq]; rw [iSup₂_le_iff]

Depends on / 依赖: coheight_eq_iSup_head_eq
-/
lemma coheight_le_iff' {a : α} {n : Nat∞} :
    coheight a <= n ↔ forall ⦃p : LTSeries α⦄, p.head = a -> p.length <= n := by
  rw [coheight_eq_iSup_head_eq]; rw [iSup₂_le_iff]

/--
lemma `coheight_le` / 引理 `coheight_le`

English:
lemma coheight_le
  given: {a : α} {n : Nat∞} (h : forall (p : LTSeries α), p.head = a -> p.length <= n)
  proof: coheight_le_iff'.mpr h

中文:
引理 coheight_le
  条件: {a : α} {n : 自然数∞} (h : 对任意 (p : LTSeries α), p.head = a -> p.length <= n)
  证明: coheight_le_iff'.mpr h

Depends on / 依赖: coheight_le_iff
-/
lemma coheight_le {a : α} {n : Nat∞} (h : forall (p : LTSeries α), p.head = a -> p.length <= n) :
    coheight a <= n :=
  coheight_le_iff'.mpr h

set_option backward.isDefEq.respectTransparency false in
/--
lemma `length_le_height` / 引理 `length_le_height`

English:
lemma length_le_height
  given: {p : LTSeries α} {x : α} (hlast : p.last <= x)
  proof: by
  by_cases hlen0 : p.length != 0
  · let p' := p.eraseLast.snoc x (by
      apply lt_of_lt_of_le
      · apply p.step ⟨p.length - 1, by lia⟩
      · convert! hlast
        simp only [Fin.succ_mk, RelSeries.last, Fin.last]
        congr; lia)
    suffices p'.length <= height x by
      simp only [RelSeries.snoc_length, RelSeries.eraseLast_length, Nat.cast_add, ENat.natCast_sub,
        Nat.cast_one, p'] at this
      convert! this
      norm_cast
      lia
    refine le_iSup₂_of_le p' ?_ le_rfl
    simp [p']
  · simp_all

中文:
引理 length_le_height
  条件: {p : LTSeries α} {x : α} (hlast : p.last <= x)
  证明: by
  by_cases hlen0 : p.length != 0
  · let p' := p.eraseLast.snoc x (by
      apply lt_of_lt_of_le
      · apply p.step ⟨p.length - 1, by lia⟩
      · convert! hlast
        simp only [Fin.succ_mk, RelSeries.last, Fin.last]
        congr; lia)
    suffices p'.length <= height x by
      simp only [RelSeries.snoc_length, RelSeries.eraseLast_length, Nat.cast_add, ENat.natCast_sub,
        Nat.cast_one, p'] at this
      convert! this
      norm_cast
      lia
    refine le_iSup₂_of_le p' ?_ le_rfl
    simp [p']
  · simp_all

Depends on / 依赖: ENat.natCast_sub, Fin.last, Fin.succ_mk, Nat.cast_add, Nat.cast_one, RelSeries, RelSeries.eraseLast_length, RelSeries.last, RelSeries.snoc_length, cast_add, cast_one, convert, eraseLast, eraseLast_length, height, le_rfl, length, lt_of_lt_of_le, natCast_sub, p.eraseLast.snoc
-/
lemma length_le_height {p : LTSeries α} {x : α} (hlast : p.last <= x) :
    p.length <= height x := by
  by_cases hlen0 : p.length != 0
  · let p' := p.eraseLast.snoc x (by
      apply lt_of_lt_of_le
      · apply p.step ⟨p.length - 1, by lia⟩
      · convert! hlast
        simp only [Fin.succ_mk, RelSeries.last, Fin.last]
        congr; lia)
    suffices p'.length <= height x by
      simp only [RelSeries.snoc_length, RelSeries.eraseLast_length, Nat.cast_add, ENat.natCast_sub,
        Nat.cast_one, p'] at this
      convert! this
      norm_cast
      lia
    refine le_iSup₂_of_le p' ?_ le_rfl
    simp [p']
  · simp_all

set_option backward.isDefEq.respectTransparency false in
/--
lemma `length_le_coheight` / 引理 `length_le_coheight`

English:
lemma length_le_coheight
  given: {x : α} {p : LTSeries α} (hhead : x <= p.head)
  proof: length_le_height (α := αᵒᵈ) (p := p.reverse) (by simpa)

中文:
引理 length_le_coheight
  条件: {x : α} {p : LTSeries α} (hhead : x <= p.head)
  证明: length_le_height (α := αᵒᵈ) (p := p.reverse) (by simpa)

Depends on / 依赖: length_le_height, p.reverse, reverse
-/
lemma length_le_coheight {x : α} {p : LTSeries α} (hhead : x <= p.head) :
    p.length <= coheight x :=
  length_le_height (α := αᵒᵈ) (p := p.reverse) (by simpa)

/--
lemma `length_le_height_last` / 引理 `length_le_height_last`

English:
lemma length_le_height_last
  given: {p : LTSeries α}
  statement: p.length <= height p.last
  proof: length_le_height le_rfl

中文:
引理 length_le_height_last
  条件: {p : LTSeries α}
  结论: p.length <= height p.last
  证明: length_le_height le_rfl

Depends on / 依赖: le_rfl, length_le_height
-/
lemma length_le_height_last {p : LTSeries α} : p.length <= height p.last :=
  length_le_height le_rfl

/--
lemma `length_le_coheight_head` / 引理 `length_le_coheight_head`

English:
lemma length_le_coheight_head
  given: {p : LTSeries α}
  statement: p.length <= coheight p.head
  proof: length_le_coheight le_rfl

中文:
引理 length_le_coheight_head
  条件: {p : LTSeries α}
  结论: p.length <= coheight p.head
  证明: length_le_coheight le_rfl

Depends on / 依赖: le_rfl, length_le_coheight
-/
lemma length_le_coheight_head {p : LTSeries α} : p.length <= coheight p.head :=
  length_le_coheight le_rfl

/--
lemma `index_le_height` / 引理 `index_le_height`

English:
lemma index_le_height
  given: (p : LTSeries α) (i : Fin (p.length + 1))
  statement: i <= height (p i)
  proof: length_le_height_last (p := p.take i)

中文:
引理 index_le_height
  条件: (p : LTSeries α) (i : 有限集 (p.length + 1))
  结论: i <= height (p i)
  证明: length_le_height_last (p := p.take i)

Depends on / 依赖: length_le_height_last, p.take
-/
lemma index_le_height (p : LTSeries α) (i : Fin (p.length + 1)) : i <= height (p i) :=
  length_le_height_last (p := p.take i)

/--
lemma `rev_index_le_coheight` / 引理 `rev_index_le_coheight`

English:
lemma rev_index_le_coheight
  given: (p : LTSeries α) (i : Fin (p.length + 1))
  statement: i.rev <= coheight (p i)
  proof: by
  simpa using! index_le_height (α := αᵒᵈ) p.reverse i.rev

中文:
引理 rev_index_le_coheight
  条件: (p : LTSeries α) (i : 有限集 (p.length + 1))
  结论: i.rev <= coheight (p i)
  证明: by
  simpa using! index_le_height (α := αᵒᵈ) p.reverse i.rev

Depends on / 依赖: i.rev, index_le_height, p.reverse, reverse
-/
lemma rev_index_le_coheight (p : LTSeries α) (i : Fin (p.length + 1)) : i.rev <= coheight (p i) := by
  simpa using! index_le_height (α := αᵒᵈ) p.reverse i.rev

/--
lemma `height_eq_index_of_length_eq_height_last` / 引理 `height_eq_index_of_length_eq_height_last`

English:
lemma height_eq_index_of_length_eq_height_last
  statement: {p : LTSeries α} (h : p.length = height p.last)
  proof: by
  refine le_antisymm (height_le ?_) (index_le_height p i)
  intro p' hp'
  have hp'' := length_le_height_last (p := p'.smash (p.drop i) (by simpa))
  simp [← h] at hp''; clear h
  norm_cast at *
  lia

中文:
引理 height_eq_index_of_length_eq_height_last
  结论: {p : LTSeries α} (h : p.length = height p.last)
  证明: by
  refine le_antisymm (height_le ?_) (index_le_height p i)
  intro p' hp'
  have hp'' := length_le_height_last (p := p'.smash (p.drop i) (by simpa))
  simp [← h] at hp''; clear h
  norm_cast at *
  lia

Depends on / 依赖: height_le, index_le_height, le_antisymm, length_le_height_last, p.drop
-/
lemma height_eq_index_of_length_eq_height_last {p : LTSeries α} (h : p.length = height p.last)
    (i : Fin (p.length + 1)) : height (p i) = i := by
  refine le_antisymm (height_le ?_) (index_le_height p i)
  intro p' hp'
  have hp'' := length_le_height_last (p := p'.smash (p.drop i) (by simpa))
  simp [← h] at hp''; clear h
  norm_cast at *
  lia

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coheight_eq_index_of_length_eq_head_coheight` / 引理 `coheight_eq_index_of_length_eq_head_coheight`

English:
lemma coheight_eq_index_of_length_eq_head_coheight
  statement: {p : LTSeries α} (h : p.length = coheight p.head)
  proof: by
  simpa using! height_eq_index_of_length_eq_height_last (α := αᵒᵈ) (p := p.reverse) (by simpa) i.rev

@[gcongr]

中文:
引理 coheight_eq_index_of_length_eq_head_coheight
  结论: {p : LTSeries α} (h : p.length = coheight p.head)
  证明: by
  simpa using! height_eq_index_of_length_eq_height_last (α := αᵒᵈ) (p := p.reverse) (by simpa) i.rev

@[gcongr]

Depends on / 依赖: height_eq_index_of_length_eq_height_last, i.rev, p.reverse, reverse
-/
lemma coheight_eq_index_of_length_eq_head_coheight {p : LTSeries α} (h : p.length = coheight p.head)
    (i : Fin (p.length + 1)) : coheight (p i) = i.rev := by
  simpa using! height_eq_index_of_length_eq_height_last (α := αᵒᵈ) (p := p.reverse) (by simpa) i.rev

@[gcongr]
/--
lemma `height_mono` / 引理 `height_mono`

English:
lemma height_mono
  statement: Monotone (α := α) height
  proof: fun _ _ hab => biSup_mono (fun _ hla => hla.trans hab)

@[gcongr]

中文:
引理 height_mono
  结论: 递增 (α := α) height
  证明: fun _ _ hab => biSup_mono (fun _ hla => hla.trans hab)

@[gcongr]

Depends on / 依赖: height
-/
lemma height_mono : Monotone (α := α) height :=
  fun _ _ hab => biSup_mono (fun _ hla => hla.trans hab)

@[gcongr]
/--
lemma `coheight_anti` / 引理 `coheight_anti`

English:
lemma coheight_anti
  statement: Antitone (α := α) coheight
  proof: (height_mono (α := αᵒᵈ)).dual_left

中文:
引理 coheight_anti
  结论: 递减 (α := α) coheight
  证明: (height_mono (α := αᵒᵈ)).dual_left

Depends on / 依赖: coheight
-/
lemma coheight_anti : Antitone (α := α) coheight :=
  (height_mono (α := αᵒᵈ)).dual_left

/--
lemma `height_add_const` / 引理 `height_add_const`

English:
lemma height_add_const
  given: (a : α) (n : Nat∞)
  proof: by
  have hne : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩
  rw [height_eq_iSup_last_eq]; rw [iSup_subtype']; rw [iSup_subtype']; rw [ENat.iSup_add]

中文:
引理 height_add_const
  条件: (a : α) (n : 自然数∞)
  证明: by
  have hne : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩
  rw [height_eq_iSup_last_eq]; rw [iSup_subtype']; rw [iSup_subtype']; rw [ENat.iSup_add]
-/
private lemma height_add_const (a : α) (n : Nat∞) :
    height a + n = ⨆ (p : LTSeries α) (_ : p.last = a), p.length + n := by
  have hne : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩
  rw [height_eq_iSup_last_eq]; rw [iSup_subtype']; rw [iSup_subtype']; rw [ENat.iSup_add]

/--
lemma `height_strictMono` / 引理 `height_strictMono`

English:
lemma height_strictMono
  given: {x y : α} (hxy : x < y) (hfin : height x < ⊤)
  proof: by
  rw [← ENat.add_one_le_iff hfin.ne]; rw [height_add_const]; rw [iSup₂_le_iff]
  intro p hlast
  have := length_le_height_last (p := p.snoc y (by simp [*]))
  simpa using this

中文:
引理 height_strictMono
  条件: {x y : α} (hxy : x < y) (hfin : height x < ⊤)
  证明: by
  rw [← ENat.add_one_le_iff hfin.ne]; rw [height_add_const]; rw [iSup₂_le_iff]
  intro p hlast
  have := length_le_height_last (p := p.snoc y (by simp [*]))
  simpa using this
-/
@[gcongr] lemma height_strictMono {x y : α} (hxy : x < y) (hfin : height x < ⊤) :
    height x < height y := by
  rw [← ENat.add_one_le_iff hfin.ne]; rw [height_add_const]; rw [iSup₂_le_iff]
  intro p hlast
  have := length_le_height_last (p := p.snoc y (by simp [*]))
  simpa using this

/--
lemma `height_add_one_le` / 引理 `height_add_one_le`

English:
lemma height_add_one_le
  given: {a b : α} (hab : a < b)
  statement: height a + 1 <= height b
  proof: by
  cases hfin : height a with
  | top =>
    have : ⊤ <= height b := by
      rw [← hfin]
      gcongr
    simp [this]
  | coe n =>
    apply Order.add_one_le_of_lt
    rw [← hfin]
    gcongr
    simp [hfin]

中文:
引理 height_add_one_le
  条件: {a b : α} (hab : a < b)
  结论: height a + 1 <= height b
  证明: by
  cases hfin : height a with
  | top =>
    have : ⊤ <= height b := by
      rw [← hfin]
      gcongr
    simp [this]
  | coe n =>
    apply Order.add_one_le_of_lt
    rw [← hfin]
    gcongr
    simp [hfin]

Depends on / 依赖: Order.add_one_le_of_lt, add_one_le_of_lt, height
-/
lemma height_add_one_le {a b : α} (hab : a < b) : height a + 1 <= height b := by
  cases hfin : height a with
  | top =>
    have : ⊤ <= height b := by
      rw [← hfin]
      gcongr
    simp [this]
  | coe n =>
    apply Order.add_one_le_of_lt
    rw [← hfin]
    gcongr
    simp [hfin]

/--
lemma `coheight_strictAnti` / 引理 `coheight_strictAnti`

English:
lemma coheight_strictAnti
  given: {x y : α} (hyx : y < x) (hfin : coheight x < ⊤)
  proof: height_strictMono (α := αᵒᵈ) hyx hfin

中文:
引理 coheight_strictAnti
  条件: {x y : α} (hyx : y < x) (hfin : coheight x < ⊤)
  证明: height_strictMono (α := αᵒᵈ) hyx hfin
-/
@[gcongr] lemma coheight_strictAnti {x y : α} (hyx : y < x) (hfin : coheight x < ⊤) :
    coheight x < coheight y :=
  height_strictMono (α := αᵒᵈ) hyx hfin

/--
lemma `coheight_add_one_le` / 引理 `coheight_add_one_le`

English:
lemma coheight_add_one_le
  given: {a b : α} (hab : b < a)
  statement: coheight a + 1 <= coheight b
  proof: by
  cases hfin : coheight a with
  | top =>
    have : ⊤ <= coheight b := by
      rw [← hfin]
      gcongr
    simp [this]
  | coe n =>
    apply Order.add_one_le_of_lt
    rw [← hfin]
    gcongr
    simp [hfin]

中文:
引理 coheight_add_one_le
  条件: {a b : α} (hab : b < a)
  结论: coheight a + 1 <= coheight b
  证明: by
  cases hfin : coheight a with
  | top =>
    have : ⊤ <= coheight b := by
      rw [← hfin]
      gcongr
    simp [this]
  | coe n =>
    apply Order.add_one_le_of_lt
    rw [← hfin]
    gcongr
    simp [hfin]

Depends on / 依赖: Order.add_one_le_of_lt, add_one_le_of_lt, coheight
-/
lemma coheight_add_one_le {a b : α} (hab : b < a) : coheight a + 1 <= coheight b := by
  cases hfin : coheight a with
  | top =>
    have : ⊤ <= coheight b := by
      rw [← hfin]
      gcongr
    simp [this]
  | coe n =>
    apply Order.add_one_le_of_lt
    rw [← hfin]
    gcongr
    simp [hfin]

/--
lemma `height_le_height_apply_of_strictMono` / 引理 `height_le_height_apply_of_strictMono`

English:
lemma height_le_height_apply_of_strictMono
  given: (f : α -> β) (hf : StrictMono f) (x : α)
  proof: by
  simp only [height_eq_iSup_last_eq]
  apply iSup₂_le
  intro p hlast
  apply le_iSup₂_of_le (p.map f hf) (by simp [hlast]) (by simp)

中文:
引理 height_le_height_apply_of_strictMono
  条件: (f : α -> β) (hf : 严格递增 f) (x : α)
  证明: by
  simp only [height_eq_iSup_last_eq]
  apply iSup₂_le
  intro p hlast
  apply le_iSup₂_of_le (p.map f hf) (by simp [hlast]) (by simp)

Depends on / 依赖: height_eq_iSup_last_eq, p.map
-/
lemma height_le_height_apply_of_strictMono (f : α -> β) (hf : StrictMono f) (x : α) :
    height x <= height (f x) := by
  simp only [height_eq_iSup_last_eq]
  apply iSup₂_le
  intro p hlast
  apply le_iSup₂_of_le (p.map f hf) (by simp [hlast]) (by simp)

/--
lemma `coheight_le_coheight_apply_of_strictMono` / 引理 `coheight_le_coheight_apply_of_strictMono`

English:
lemma coheight_le_coheight_apply_of_strictMono
  given: (f : α -> β) (hf : StrictMono f) (x : α)
  proof: by
  apply height_le_height_apply_of_strictMono (α := αᵒᵈ)
  exact fun _ _ h => hf h

中文:
引理 coheight_le_coheight_apply_of_strictMono
  条件: (f : α -> β) (hf : 严格递增 f) (x : α)
  证明: by
  apply height_le_height_apply_of_strictMono (α := αᵒᵈ)
  exact fun _ _ h => hf h

Depends on / 依赖: height_le_height_apply_of_strictMono
-/
lemma coheight_le_coheight_apply_of_strictMono (f : α -> β) (hf : StrictMono f) (x : α) :
    coheight x <= coheight (f x) := by
  apply height_le_height_apply_of_strictMono (α := αᵒᵈ)
  exact fun _ _ h => hf h

/--
lemma `coheight_eq_of_strictMono` / 引理 `coheight_eq_of_strictMono`

English:
lemma coheight_eq_of_strictMono
  statement: (f : α -> β) (hf : StrictMono f)
  proof: by
  refine le_antisymm (Order.coheight_le_coheight_apply_of_strictMono _ hf _) ?_
  refine coheight_le_iff'.mpr fun p hp => ?_
  induction p using RelSeries.inductionOn generalizing a with
  | singleton x => simp
  | cons p x hx ih =>
    simp only [RelSeries.head_cons] at hp
    obtain ⟨a', haa', ha'⟩ := h a p.head (by grind)
    grw [RelSeries.cons_length, Nat.cast_add, Nat.cast_one, ih a' ha'.symm]
    exact coheight_add_one_le haa'

中文:
引理 coheight_eq_of_strictMono
  结论: (f : α -> β) (hf : 严格递增 f)
  证明: by
  refine le_antisymm (Order.coheight_le_coheight_apply_of_strictMono _ hf _) ?_
  refine coheight_le_iff'.mpr fun p hp => ?_
  induction p using RelSeries.inductionOn generalizing a with
  | singleton x => simp
  | cons p x hx ih =>
    simp only [RelSeries.head_cons] at hp
    obtain ⟨a', haa', ha'⟩ := h a p.head (by grind)
    grw [RelSeries.cons_length, Nat.cast_add, Nat.cast_one, ih a' ha'.symm]
    exact coheight_add_one_le haa'

Depends on / 依赖: Nat.cast_add, Nat.cast_one, Order.coheight_le_coheight_apply_of_strictMono, RelSeries, RelSeries.cons_length, RelSeries.head_cons, RelSeries.inductionOn, cast_add, cast_one, coheight_add_one_le, coheight_le_coheight_apply_of_strictMono, coheight_le_iff, cons_length, generalizing, head_cons, inductionOn, le_antisymm, p.head, singleton
-/
lemma coheight_eq_of_strictMono (f : α -> β) (hf : StrictMono f)
    (h : forall a : α, forall b : β, f a < b -> exists (a' : α), a < a' ∧ f a' = b) (a : α) :
    coheight a = coheight (f a) := by
  refine le_antisymm (Order.coheight_le_coheight_apply_of_strictMono _ hf _) ?_
  refine coheight_le_iff'.mpr fun p hp => ?_
  induction p using RelSeries.inductionOn generalizing a with
  | singleton x => simp
  | cons p x hx ih =>
    simp only [RelSeries.head_cons] at hp
    obtain ⟨a', haa', ha'⟩ := h a p.head (by grind)
    grw [RelSeries.cons_length, Nat.cast_add, Nat.cast_one, ih a' ha'.symm]
    exact coheight_add_one_le haa'

/--
lemma `height_eq_of_strictMono` / 引理 `height_eq_of_strictMono`

English:
lemma height_eq_of_strictMono
  statement: (f : α -> β) (hf : StrictMono f)
  proof: by
  have : coheight (OrderDual.toDual a) = coheight (OrderDual.toDual (f a)) :=
    coheight_eq_of_strictMono (α := αᵒᵈ) (β := βᵒᵈ) (f := OrderDual.toDual ∘ f ∘ OrderDual.toDual)
    (strictMono_dual_iff.mp hf) (fun a b hab => h a b hab) _
  simpa [Order.coheight_toDual] using this

@[simp]

中文:
引理 height_eq_of_strictMono
  结论: (f : α -> β) (hf : 严格递增 f)
  证明: by
  have : coheight (OrderDual.toDual a) = coheight (OrderDual.toDual (f a)) :=
    coheight_eq_of_strictMono (α := αᵒᵈ) (β := βᵒᵈ) (f := OrderDual.toDual ∘ f ∘ OrderDual.toDual)
    (strictMono_dual_iff.mp hf) (fun a b hab => h a b hab) _
  simpa [Order.coheight_toDual] using this

@[simp]

Depends on / 依赖: Order.coheight_toDual, OrderDual, OrderDual.toDual, coheight, coheight_eq_of_strictMono, coheight_toDual, strictMono_dual_iff, strictMono_dual_iff.mp, toDual
-/
lemma height_eq_of_strictMono (f : α -> β) (hf : StrictMono f)
    (h : forall a : α, forall b : β, b < f a -> exists (a' : α), a' < a ∧ f a' = b) (a : α) :
    height a = height (f a) := by
  have : coheight (OrderDual.toDual a) = coheight (OrderDual.toDual (f a)) :=
    coheight_eq_of_strictMono (α := αᵒᵈ) (β := βᵒᵈ) (f := OrderDual.toDual ∘ f ∘ OrderDual.toDual)
    (strictMono_dual_iff.mp hf) (fun a b hab => h a b hab) _
  simpa [Order.coheight_toDual] using this

@[simp]
/--
lemma `height_orderIso` / 引理 `height_orderIso`

English:
lemma height_orderIso
  given: (f : α ≃o β) (x : α)
  statement: height (f x) = height x
  proof: by
  apply le_antisymm
  · simpa using height_le_height_apply_of_strictMono _ f.symm.strictMono (f x)
  · exact height_le_height_apply_of_strictMono _ f.strictMono x

中文:
引理 height_orderIso
  条件: (f : α ≃o β) (x : α)
  结论: height (f x) = height x
  证明: by
  apply le_antisymm
  · simpa using height_le_height_apply_of_strictMono _ f.symm.strictMono (f x)
  · exact height_le_height_apply_of_strictMono _ f.strictMono x

Depends on / 依赖: f.strictMono, f.symm.strictMono, height_le_height_apply_of_strictMono, le_antisymm, strictMono
-/
lemma height_orderIso (f : α ≃o β) (x : α) : height (f x) = height x := by
  apply le_antisymm
  · simpa using height_le_height_apply_of_strictMono _ f.symm.strictMono (f x)
  · exact height_le_height_apply_of_strictMono _ f.strictMono x

/--
lemma `coheight_orderIso` / 引理 `coheight_orderIso`

English:
lemma coheight_orderIso
  given: (f : α ≃o β) (x : α)
  statement: coheight (f x) = coheight x
  proof: height_orderIso (α := αᵒᵈ) f.dual x

中文:
引理 coheight_orderIso
  条件: (f : α ≃o β) (x : α)
  结论: coheight (f x) = coheight x
  证明: height_orderIso (α := αᵒᵈ) f.dual x

Depends on / 依赖: f.dual, height_orderIso
-/
lemma coheight_orderIso (f : α ≃o β) (x : α) : coheight (f x) = coheight x :=
  height_orderIso (α := αᵒᵈ) f.dual x

/--
lemma `exists_eq_iSup_of_iSup_eq_coe` / 引理 `exists_eq_iSup_of_iSup_eq_coe`

English:
lemma exists_eq_iSup_of_iSup_eq_coe
  statement: {α : Type*} [Nonempty α] {f : α -> Nat∞} {n : Nat}
  proof: by
  obtain ⟨x, hx⟩ := ENat.sSup_mem_of_nonempty_of_lt_top (h ▸ ENat.natCast_lt_top _)
  use x
  simpa [hx] using! h

中文:
引理 存在_eq_iSup_of_iSup_eq_coe
  结论: {α : 类型} [非空 α] {f : α -> 自然数∞} {n : 自然数}
  证明: by
  obtain ⟨x, hx⟩ := ENat.sSup_mem_of_nonempty_of_lt_top (h ▸ ENat.natCast_lt_top _)
  use x
  simpa [hx] using! h
-/
private lemma exists_eq_iSup_of_iSup_eq_coe {α : Type*} [Nonempty α] {f : α -> Nat∞} {n : Nat}
    (h : (⨆ x, f x) = n) : exists x, f x = n := by
  obtain ⟨x, hx⟩ := ENat.sSup_mem_of_nonempty_of_lt_top (h ▸ ENat.natCast_lt_top _)
  use x
  simpa [hx] using! h

/--
lemma `exists_series_of_le_height` / 引理 `exists_series_of_le_height`

English:
lemma exists_series_of_le_height
  given: (a : α) {n : Nat} (h : n <= height a)
  proof: by
  have hne : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩
  cases ha : height a with
  | top =>
    clear h
    rw [height_eq_iSup_last_eq]; rw [iSup_subtype']; rw [ENat.iSup_natCast_eq_top]; rw [bddAbove_def] at ha
    contrapose! ha
    use n
    rintro m ⟨⟨p, rfl⟩, hp⟩
    simp only at hp
    by_contra! hnm
    apply ha (p.drop ⟨m-n, by lia⟩) (by simp) (by simp; lia)
  | coe m =>
    rw [ha]; rw [Nat.cast_le] at h
    rw [height_eq_iSup_last_eq]; rw [iSup_subtype'] at ha
    obtain ⟨⟨p, hlast⟩, hlen⟩ := exists_eq_iSup_of_iSup_eq_coe ha
    simp only [Nat.cast_inj] at hlen
    use p.drop ⟨m-n, by lia⟩
    constructor
    · simp [hlast]
    · simp [hlen]; lia

中文:
引理 存在_series_of_le_height
  条件: (a : α) {n : 自然数} (h : n <= height a)
  证明: by
  have hne : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩
  cases ha : height a with
  | top =>
    clear h
    rw [height_eq_iSup_last_eq]; rw [iSup_subtype']; rw [ENat.iSup_natCast_eq_top]; rw [bddAbove_def] at ha
    contrapose! ha
    use n
    rintro m ⟨⟨p, rfl⟩, hp⟩
    simp only at hp
    by_contra! hnm
    apply ha (p.drop ⟨m-n, by lia⟩) (by simp) (by simp; lia)
  | coe m =>
    rw [ha]; rw [Nat.cast_le] at h
    rw [height_eq_iSup_last_eq]; rw [iSup_subtype'] at ha
    obtain ⟨⟨p, hlast⟩, hlen⟩ := exists_eq_iSup_of_iSup_eq_coe ha
    simp only [Nat.cast_inj] at hlen
    use p.drop ⟨m-n, by lia⟩
    constructor
    · simp [hlast]
    · simp [hlen]; lia

Depends on / 依赖: ENat.iSup_natCast_eq_top, LTSeries, Nat.cast_le, Nonempty, RelSeries, RelSeries.singleton, bddAbove_def, cast_le, contrapose, height, height_eq_iSup_last_eq, iSup_natCast_eq_top, iSup_subtype, p.drop, p.last, singleton
-/
lemma exists_series_of_le_height (a : α) {n : Nat} (h : n <= height a) :
    exists p : LTSeries α, p.last = a ∧ p.length = n := by
  have hne : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩
  cases ha : height a with
  | top =>
    clear h
    rw [height_eq_iSup_last_eq]; rw [iSup_subtype']; rw [ENat.iSup_natCast_eq_top]; rw [bddAbove_def] at ha
    contrapose! ha
    use n
    rintro m ⟨⟨p, rfl⟩, hp⟩
    simp only at hp
    by_contra! hnm
    apply ha (p.drop ⟨m-n, by lia⟩) (by simp) (by simp; lia)
  | coe m =>
    rw [ha]; rw [Nat.cast_le] at h
    rw [height_eq_iSup_last_eq]; rw [iSup_subtype'] at ha
    obtain ⟨⟨p, hlast⟩, hlen⟩ := exists_eq_iSup_of_iSup_eq_coe ha
    simp only [Nat.cast_inj] at hlen
    use p.drop ⟨m-n, by lia⟩
    constructor
    · simp [hlast]
    · simp [hlen]; lia

/--
lemma `exists_series_of_le_coheight` / 引理 `exists_series_of_le_coheight`

English:
lemma exists_series_of_le_coheight
  given: (a : α) {n : Nat} (h : n <= coheight a)
  proof: by
  obtain ⟨p, hp, hl⟩ := exists_series_of_le_height (α := αᵒᵈ) a h
  exact ⟨p.reverse, by simpa, by simpa⟩

中文:
引理 存在_series_of_le_coheight
  条件: (a : α) {n : 自然数} (h : n <= coheight a)
  证明: by
  obtain ⟨p, hp, hl⟩ := exists_series_of_le_height (α := αᵒᵈ) a h
  exact ⟨p.reverse, by simpa, by simpa⟩

Depends on / 依赖: Ideal.map_span, Ideal.span, Ideal.submodule_span_eq, IsPrincipal, Set.image_singleton, Submodule, Submodule.IsPrincipal.principal, exists_series_of_le_height, image_singleton, map_span, p.reverse, principal, reverse, submodule_span_eq
-/
lemma exists_series_of_le_coheight (a : α) {n : Nat} (h : n <= coheight a) :
    exists p : LTSeries α, p.head = a ∧ p.length = n := by
  obtain ⟨p, hp, hl⟩ := exists_series_of_le_height (α := αᵒᵈ) a h
  exact ⟨p.reverse, by simpa, by simpa⟩

/--
lemma `exists_series_of_height_eq_coe` / 引理 `exists_series_of_height_eq_coe`

English:
lemma exists_series_of_height_eq_coe
  given: (a : α) {n : Nat} (h : height a = n)
  proof: exists_series_of_le_height a (le_of_eq h.symm)

中文:
引理 存在_series_of_height_eq_coe
  条件: (a : α) {n : 自然数} (h : height a = n)
  证明: exists_series_of_le_height a (le_of_eq h.symm)

Depends on / 依赖: exists_series_of_le_height, h.symm, le_of_eq
-/
lemma exists_series_of_height_eq_coe (a : α) {n : Nat} (h : height a = n) :
    exists p : LTSeries α, p.last = a ∧ p.length = n :=
  exists_series_of_le_height a (le_of_eq h.symm)

/--
lemma `exists_series_of_coheight_eq_coe` / 引理 `exists_series_of_coheight_eq_coe`

English:
lemma exists_series_of_coheight_eq_coe
  given: (a : α) {n : Nat} (h : coheight a = n)
  proof: exists_series_of_le_coheight a (le_of_eq h.symm)

中文:
引理 存在_series_of_coheight_eq_coe
  条件: (a : α) {n : 自然数} (h : coheight a = n)
  证明: exists_series_of_le_coheight a (le_of_eq h.symm)

Depends on / 依赖: exists_series_of_le_coheight, h.symm, le_of_eq
-/
lemma exists_series_of_coheight_eq_coe (a : α) {n : Nat} (h : coheight a = n) :
    exists p : LTSeries α, p.head = a ∧ p.length = n :=
  exists_series_of_le_coheight a (le_of_eq h.symm)

/--
lemma `height_eq_iSup_lt_height` / 引理 `height_eq_iSup_lt_height`

English:
lemma height_eq_iSup_lt_height
  given: (x : α)
  statement: height x = ⨆ y < x, height y + 1
  proof: by
  apply le_antisymm
  · apply height_le
    intro p hp
    cases hlen : p.length with
    | zero => simp
    | succ n =>
      apply le_iSup_of_le p.eraseLast.last
      apply le_iSup_of_le (by rw [← hp]; exact p.eraseLast_last_rel_last (by lia))
      rw [height_add_const]
      apply le_iSup₂_of_le p.eraseLast (by rfl) (by simp [hlen])
  · apply iSup₂_le; intro y hyx
    rw [height_add_const]
    apply iSup₂_le; intro p hp
    apply le_iSup₂_of_le (p.snoc x (hp ▸ hyx)) (by simp) (by simp)

中文:
引理 height_eq_iSup_lt_height
  条件: (x : α)
  结论: height x = ⨆ y < x, height y + 1
  证明: by
  apply le_antisymm
  · apply height_le
    intro p hp
    cases hlen : p.length with
    | zero => simp
    | succ n =>
      apply le_iSup_of_le p.eraseLast.last
      apply le_iSup_of_le (by rw [← hp]; exact p.eraseLast_last_rel_last (by lia))
      rw [height_add_const]
      apply le_iSup₂_of_le p.eraseLast (by rfl) (by simp [hlen])
  · apply iSup₂_le; intro y hyx
    rw [height_add_const]
    apply iSup₂_le; intro p hp
    apply le_iSup₂_of_le (p.snoc x (hp ▸ hyx)) (by simp) (by simp)

Depends on / 依赖: eraseLast, eraseLast_last_rel_last, height_add_const, height_le, le_antisymm, le_iSup_of_le, length, p.eraseLast, p.eraseLast.last, p.eraseLast_last_rel_last, p.length, p.snoc
-/
lemma height_eq_iSup_lt_height (x : α) : height x = ⨆ y < x, height y + 1 := by
  apply le_antisymm
  · apply height_le
    intro p hp
    cases hlen : p.length with
    | zero => simp
    | succ n =>
      apply le_iSup_of_le p.eraseLast.last
      apply le_iSup_of_le (by rw [← hp]; exact p.eraseLast_last_rel_last (by lia))
      rw [height_add_const]
      apply le_iSup₂_of_le p.eraseLast (by rfl) (by simp [hlen])
  · apply iSup₂_le; intro y hyx
    rw [height_add_const]
    apply iSup₂_le; intro p hp
    apply le_iSup₂_of_le (p.snoc x (hp ▸ hyx)) (by simp) (by simp)

/--
lemma `coheight_eq_iSup_gt_coheight` / 引理 `coheight_eq_iSup_gt_coheight`

English:
lemma coheight_eq_iSup_gt_coheight
  given: (x : α)
  statement: coheight x = ⨆ y > x, coheight y + 1
  proof: height_eq_iSup_lt_height (α := αᵒᵈ) x

中文:
引理 coheight_eq_iSup_gt_coheight
  条件: (x : α)
  结论: coheight x = ⨆ y > x, coheight y + 1
  证明: height_eq_iSup_lt_height (α := αᵒᵈ) x

Depends on / 依赖: height_eq_iSup_lt_height
-/
lemma coheight_eq_iSup_gt_coheight (x : α) : coheight x = ⨆ y > x, coheight y + 1 :=
  height_eq_iSup_lt_height (α := αᵒᵈ) x

/--
lemma `height_le_coe_iff` / 引理 `height_le_coe_iff`

English:
lemma height_le_coe_iff
  given: {x : α} {n : Nat}
  statement: height x <= n ↔ forall y < x, height y < n
  proof: by
  conv_lhs => rw [height_eq_iSup_lt_height, iSup₂_le_iff]
  congr! 2 with y _
  cases height y
  · simp
  · norm_cast

中文:
引理 height_le_coe_iff
  条件: {x : α} {n : 自然数}
  结论: height x <= n ↔ 对任意 y < x, height y < n
  证明: by
  conv_lhs => rw [height_eq_iSup_lt_height, iSup₂_le_iff]
  congr! 2 with y _
  cases height y
  · simp
  · norm_cast

Depends on / 依赖: conv_lhs, height, height_eq_iSup_lt_height
-/
lemma height_le_coe_iff {x : α} {n : Nat} : height x <= n ↔ forall y < x, height y < n := by
  conv_lhs => rw [height_eq_iSup_lt_height, iSup₂_le_iff]
  congr! 2 with y _
  cases height y
  · simp
  · norm_cast

/--
lemma `coheight_le_coe_iff` / 引理 `coheight_le_coe_iff`

English:
lemma coheight_le_coe_iff
  given: {x : α} {n : Nat}
  statement: coheight x <= n ↔ forall y > x, coheight y < n
  proof: height_le_coe_iff (α := αᵒᵈ)

中文:
引理 coheight_le_coe_iff
  条件: {x : α} {n : 自然数}
  结论: coheight x <= n ↔ 对任意 y > x, coheight y < n
  证明: height_le_coe_iff (α := αᵒᵈ)

Depends on / 依赖: height_le_coe_iff
-/
lemma coheight_le_coe_iff {x : α} {n : Nat} : coheight x <= n ↔ forall y > x, coheight y < n :=
  height_le_coe_iff (α := αᵒᵈ)

/--
lemma `height_eq_top_iff` / 引理 `height_eq_top_iff`

English:
lemma height_eq_top_iff
  given: {x : α}
  proof: by
    apply exists_series_of_le_height x (n := n)
    simp [h]
  mpr h := by
    rw [height_eq_iSup_last_eq]; rw [iSup_subtype']; rw [ENat.iSup_natCast_eq_top]; rw [bddAbove_def]
    push Not
    intro n
    obtain ⟨p, hlast, hp⟩ := h (n + 1)
    exact ⟨p.length, ⟨⟨⟨p, hlast⟩, by simp [hp]⟩, by simp [hp]⟩⟩

中文:
引理 height_eq_top_iff
  条件: {x : α}
  证明: by
    apply exists_series_of_le_height x (n := n)
    simp [h]
  mpr h := by
    rw [height_eq_iSup_last_eq]; rw [iSup_subtype']; rw [ENat.iSup_natCast_eq_top]; rw [bddAbove_def]
    push Not
    intro n
    obtain ⟨p, hlast, hp⟩ := h (n + 1)
    exact ⟨p.length, ⟨⟨⟨p, hlast⟩, by simp [hp]⟩, by simp [hp]⟩⟩

Depends on / 依赖: ENat.iSup_natCast_eq_top, bddAbove_def, exists_series_of_le_height, height_eq_iSup_last_eq, iSup_natCast_eq_top, iSup_subtype, length, p.length
-/
lemma height_eq_top_iff {x : α} :
    height x = ⊤ ↔ forall n, exists p : LTSeries α, p.last = x ∧ p.length = n where
  mp h n := by
    apply exists_series_of_le_height x (n := n)
    simp [h]
  mpr h := by
    rw [height_eq_iSup_last_eq]; rw [iSup_subtype']; rw [ENat.iSup_natCast_eq_top]; rw [bddAbove_def]
    push Not
    intro n
    obtain ⟨p, hlast, hp⟩ := h (n + 1)
    exact ⟨p.length, ⟨⟨⟨p, hlast⟩, by simp [hp]⟩, by simp [hp]⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coheight_eq_top_iff` / 引理 `coheight_eq_top_iff`

English:
lemma coheight_eq_top_iff
  given: {x : α}
  proof: by
  convert! height_eq_top_iff (α := αᵒᵈ) (x := x) using 2 with n
  constructor <;> (intro ⟨p, hp, hl⟩; use p.reverse; constructor <;> simpa)

中文:
引理 coheight_eq_top_iff
  条件: {x : α}
  证明: by
  convert! height_eq_top_iff (α := αᵒᵈ) (x := x) using 2 with n
  constructor <;> (intro ⟨p, hp, hl⟩; use p.reverse; constructor <;> simpa)

Depends on / 依赖: convert, height_eq_top_iff, p.reverse, reverse
-/
lemma coheight_eq_top_iff {x : α} :
    coheight x = ⊤ ↔ forall n, exists p : LTSeries α, p.head = x ∧ p.length = n := by
  convert! height_eq_top_iff (α := αᵒᵈ) (x := x) using 2 with n
  constructor <;> (intro ⟨p, hp, hl⟩; use p.reverse; constructor <;> simpa)

/--
lemma `height_eq_zero` / 引理 `height_eq_zero`

English:
lemma height_eq_zero
  given: {x : α}
  statement: height x = 0 ↔ IsMin x
  proof: by
  simpa [isMin_iff_forall_not_lt] using height_le_coe_iff (x := x) (n := 0)

protected alias ⟨_, IsMin.height_eq_zero⟩ := height_eq_zero

中文:
引理 height_eq_zero
  条件: {x : α}
  结论: height x = 0 ↔ IsMin x
  证明: by
  simpa [isMin_iff_forall_not_lt] using height_le_coe_iff (x := x) (n := 0)

protected alias ⟨_, IsMin.height_eq_zero⟩ := height_eq_zero
-/
@[simp] lemma height_eq_zero {x : α} : height x = 0 ↔ IsMin x := by
  simpa [isMin_iff_forall_not_lt] using height_le_coe_iff (x := x) (n := 0)

protected alias ⟨_, IsMin.height_eq_zero⟩ := height_eq_zero

/--
lemma `coheight_eq_zero` / 引理 `coheight_eq_zero`

English:
lemma coheight_eq_zero
  given: {x : α}
  statement: coheight x = 0 ↔ IsMax x
  proof: height_eq_zero (α := αᵒᵈ)

protected alias ⟨_, IsMax.coheight_eq_zero⟩ := coheight_eq_zero

中文:
引理 coheight_eq_zero
  条件: {x : α}
  结论: coheight x = 0 ↔ IsMax x
  证明: height_eq_zero (α := αᵒᵈ)

protected alias ⟨_, IsMax.coheight_eq_zero⟩ := coheight_eq_zero
-/
@[simp] lemma coheight_eq_zero {x : α} : coheight x = 0 ↔ IsMax x :=
  height_eq_zero (α := αᵒᵈ)

protected alias ⟨_, IsMax.coheight_eq_zero⟩ := coheight_eq_zero

/--
lemma `height_ne_zero` / 引理 `height_ne_zero`

English:
lemma height_ne_zero
  given: {x : α}
  statement: height x != 0 ↔ ¬ IsMin x
  proof: height_eq_zero.not

中文:
引理 height_ne_zero
  条件: {x : α}
  结论: height x != 0 ↔ ¬ IsMin x
  证明: height_eq_zero.not

Depends on / 依赖: height_eq_zero, height_eq_zero.not
-/
lemma height_ne_zero {x : α} : height x != 0 ↔ ¬ IsMin x := height_eq_zero.not

/--
lemma `height_pos` / 引理 `height_pos`

English:
lemma height_pos
  given: {x : α}
  statement: 0 < height x ↔ ¬ IsMin x
  proof: by
  simp [pos_iff_ne_zero]

中文:
引理 height_pos
  条件: {x : α}
  结论: 0 < height x ↔ ¬ IsMin x
  证明: by
  simp [pos_iff_ne_zero]
-/
@[simp] lemma height_pos {x : α} : 0 < height x ↔ ¬ IsMin x := by
  simp [pos_iff_ne_zero]

/--
lemma `coheight_ne_zero` / 引理 `coheight_ne_zero`

English:
lemma coheight_ne_zero
  given: {x : α}
  statement: coheight x != 0 ↔ ¬ IsMax x
  proof: coheight_eq_zero.not

中文:
引理 coheight_ne_zero
  条件: {x : α}
  结论: coheight x != 0 ↔ ¬ IsMax x
  证明: coheight_eq_zero.not

Depends on / 依赖: coheight_eq_zero, coheight_eq_zero.not
-/
lemma coheight_ne_zero {x : α} : coheight x != 0 ↔ ¬ IsMax x := coheight_eq_zero.not

/--
lemma `coheight_pos` / 引理 `coheight_pos`

English:
lemma coheight_pos
  given: {x : α}
  statement: 0 < coheight x ↔ ¬ IsMax x
  proof: by
  simp [pos_iff_ne_zero]

中文:
引理 coheight_pos
  条件: {x : α}
  结论: 0 < coheight x ↔ ¬ IsMax x
  证明: by
  simp [pos_iff_ne_zero]
-/
@[simp] lemma coheight_pos {x : α} : 0 < coheight x ↔ ¬ IsMax x := by
  simp [pos_iff_ne_zero]

/--
lemma `height_bot` / 引理 `height_bot`

English:
lemma height_bot
  given: (α : Type*) [Preorder α] [OrderBot α]
  statement: height (⊥ : α) = 0
  proof: by simp

中文:
引理 height_bot
  条件: (α : 类型) [预序 α] [有底序 α]
  结论: height (⊥ : α) = 0
  证明: by simp
-/
@[simp] lemma height_bot (α : Type*) [Preorder α] [OrderBot α] : height (⊥ : α) = 0 := by simp

/--
lemma `coheight_top` / 引理 `coheight_top`

English:
lemma coheight_top
  given: (α : Type*) [Preorder α] [OrderTop α]
  statement: coheight (⊤ : α) = 0
  proof: by simp

中文:
引理 coheight_top
  条件: (α : 类型) [预序 α] [有顶序 α]
  结论: coheight (⊤ : α) = 0
  证明: by simp
-/
@[simp] lemma coheight_top (α : Type*) [Preorder α] [OrderTop α] : coheight (⊤ : α) = 0 := by simp

/--
lemma `height_pos_of_bot_lt` / 引理 `height_pos_of_bot_lt`

English:
lemma height_pos_of_bot_lt
  given: {x : α} [OrderBot α] (h : ⊥ < x)
  statement: 0 < height x
  proof: by
  rw [height_pos]
  grind [not_isMin_iff]

中文:
引理 height_pos_of_bot_lt
  条件: {x : α} [有底序 α] (h : ⊥ < x)
  结论: 0 < height x
  证明: by
  rw [height_pos]
  grind [not_isMin_iff]

Depends on / 依赖: height_pos, not_isMin_iff
-/
lemma height_pos_of_bot_lt {x : α} [OrderBot α] (h : ⊥ < x) : 0 < height x := by
  rw [height_pos]
  grind [not_isMin_iff]

/--
lemma `coheight_pos_of_lt_top` / 引理 `coheight_pos_of_lt_top`

English:
lemma coheight_pos_of_lt_top
  given: {x : α} [OrderTop α] (h : x < ⊤)
  statement: 0 < coheight x
  proof: by
  rw [coheight_pos]
  grind [not_isMax_iff]

中文:
引理 coheight_pos_of_lt_top
  条件: {x : α} [有顶序 α] (h : x < ⊤)
  结论: 0 < coheight x
  证明: by
  rw [coheight_pos]
  grind [not_isMax_iff]

Depends on / 依赖: coheight_pos, not_isMax_iff
-/
lemma coheight_pos_of_lt_top {x : α} [OrderTop α] (h : x < ⊤) : 0 < coheight x := by
  rw [coheight_pos]
  grind [not_isMax_iff]

/--
lemma `coe_lt_height_iff` / 引理 `coe_lt_height_iff`

English:
lemma coe_lt_height_iff
  given: {x : α} {n : Nat} (hfin : height x < ⊤)
  proof: by
    obtain ⟨m, hx : height x = m⟩ := Option.ne_none_iff_exists'.mp hfin.ne_top
    rw [hx] at h; norm_cast at h
    obtain ⟨p, hp, hlen⟩ := exists_series_of_height_eq_coe x hx
    use p ⟨n, by lia⟩
    constructor
    · rw [← hp]
      apply LTSeries.strictMono
      simp [Fin.last]; lia
    · exact height_eq_index_of_length_eq_height_last (by simp [hlen, hp, hx]) ⟨n, by lia⟩
  mpr := fun ⟨y, hyx, hy⟩ =>
    hy ▸ height_strictMono hyx (lt_of_le_of_lt (height_mono hyx.le) hfin)

中文:
引理 coe_lt_height_iff
  条件: {x : α} {n : 自然数} (hfin : height x < ⊤)
  证明: by
    obtain ⟨m, hx : height x = m⟩ := Option.ne_none_iff_exists'.mp hfin.ne_top
    rw [hx] at h; norm_cast at h
    obtain ⟨p, hp, hlen⟩ := exists_series_of_height_eq_coe x hx
    use p ⟨n, by lia⟩
    constructor
    · rw [← hp]
      apply LTSeries.strictMono
      simp [Fin.last]; lia
    · exact height_eq_index_of_length_eq_height_last (by simp [hlen, hp, hx]) ⟨n, by lia⟩
  mpr := fun ⟨y, hyx, hy⟩ =>
    hy ▸ height_strictMono hyx (lt_of_le_of_lt (height_mono hyx.le) hfin)

Depends on / 依赖: Fin.last, LTSeries, LTSeries.strictMono, Option.ne_none_iff_exists, exists_series_of_height_eq_coe, height, height_eq_index_of_length_eq_height_last, height_mono, height_strictMono, hfin.ne_top, hyx.le, lt_of_le_of_lt, ne_none_iff_exists, ne_top, strictMono
-/
lemma coe_lt_height_iff {x : α} {n : Nat} (hfin : height x < ⊤) :
    n < height x ↔ exists y < x, height y = n where
  mp h := by
    obtain ⟨m, hx : height x = m⟩ := Option.ne_none_iff_exists'.mp hfin.ne_top
    rw [hx] at h; norm_cast at h
    obtain ⟨p, hp, hlen⟩ := exists_series_of_height_eq_coe x hx
    use p ⟨n, by lia⟩
    constructor
    · rw [← hp]
      apply LTSeries.strictMono
      simp [Fin.last]; lia
    · exact height_eq_index_of_length_eq_height_last (by simp [hlen, hp, hx]) ⟨n, by lia⟩
  mpr := fun ⟨y, hyx, hy⟩ =>
    hy ▸ height_strictMono hyx (lt_of_le_of_lt (height_mono hyx.le) hfin)

/--
lemma `coe_lt_coheight_iff` / 引理 `coe_lt_coheight_iff`

English:
lemma coe_lt_coheight_iff
  given: {x : α} {n : Nat} (hfin : coheight x < ⊤)
  proof: coe_lt_height_iff (α := αᵒᵈ) hfin

中文:
引理 coe_lt_coheight_iff
  条件: {x : α} {n : 自然数} (hfin : coheight x < ⊤)
  证明: coe_lt_height_iff (α := αᵒᵈ) hfin

Depends on / 依赖: coe_lt_height_iff
-/
lemma coe_lt_coheight_iff {x : α} {n : Nat} (hfin : coheight x < ⊤) :
    n < coheight x ↔ exists y > x, coheight y = n :=
  coe_lt_height_iff (α := αᵒᵈ) hfin

/--
lemma `height_eq_coe_add_one_iff` / 引理 `height_eq_coe_add_one_iff`

English:
lemma height_eq_coe_add_one_iff
  given: {x : α} {n : Nat}
  proof: by
  wlog hfin : height x < ⊤
  · simp_all [← Nat.cast_add_one, -Nat.cast_add]
  simp only [hfin, true_and]
  trans n < height x ∧ height x <= n + 1
  · rw [le_antisymm_iff, and_comm]
    simp [ENat.add_one_le_iff]
  · congr! 1
    · exact coe_lt_height_iff hfin
    · simpa [hfin, ENat.lt_add_one_iff] using height_le_coe_iff (x := x) (n := n + 1)

中文:
引理 height_eq_coe_add_one_iff
  条件: {x : α} {n : 自然数}
  证明: by
  wlog hfin : height x < ⊤
  · simp_all [← Nat.cast_add_one, -Nat.cast_add]
  simp only [hfin, true_and]
  trans n < height x ∧ height x <= n + 1
  · rw [le_antisymm_iff, and_comm]
    simp [ENat.add_one_le_iff]
  · congr! 1
    · exact coe_lt_height_iff hfin
    · simpa [hfin, ENat.lt_add_one_iff] using height_le_coe_iff (x := x) (n := n + 1)

Depends on / 依赖: ENat.add_one_le_iff, ENat.lt_add_one_iff, Nat.cast_add, Nat.cast_add_one, add_one_le_iff, and_comm, cast_add, cast_add_one, coe_lt_height_iff, height, height_le_coe_iff, le_antisymm_iff, lt_add_one_iff, true_and
-/
lemma height_eq_coe_add_one_iff {x : α} {n : Nat} :
    height x = n + 1 ↔ height x < ⊤ ∧ (exists y < x, height y = n) ∧ (forall y < x, height y <= n) := by
  wlog hfin : height x < ⊤
  · simp_all [← Nat.cast_add_one, -Nat.cast_add]
  simp only [hfin, true_and]
  trans n < height x ∧ height x <= n + 1
  · rw [le_antisymm_iff, and_comm]
    simp [ENat.add_one_le_iff]
  · congr! 1
    · exact coe_lt_height_iff hfin
    · simpa [hfin, ENat.lt_add_one_iff] using height_le_coe_iff (x := x) (n := n + 1)

/--
lemma `coheight_eq_coe_add_one_iff` / 引理 `coheight_eq_coe_add_one_iff`

English:
lemma coheight_eq_coe_add_one_iff
  given: {x : α} {n : Nat}
  proof: height_eq_coe_add_one_iff (α := αᵒᵈ)

中文:
引理 coheight_eq_coe_add_one_iff
  条件: {x : α} {n : 自然数}
  证明: height_eq_coe_add_one_iff (α := αᵒᵈ)

Depends on / 依赖: I.IsMaximal, I.IsPrime, IsMaximal, IsMaximal.isPrime, IsPrime, height_eq_coe_add_one_iff, isPrime
-/
lemma coheight_eq_coe_add_one_iff {x : α} {n : Nat} :
    coheight x = n + 1 ↔
      coheight x < ⊤ ∧ (exists y > x, coheight y = n) ∧ (forall y > x, coheight y <= n) :=
  height_eq_coe_add_one_iff (α := αᵒᵈ)

/--
lemma `height_eq_coe_iff` / 引理 `height_eq_coe_iff`

English:
lemma height_eq_coe_iff
  given: {x : α} {n : Nat}
  proof: by
  wlog hfin : height x < ⊤
  · simp_all
  simp only [hfin, true_and]
  cases n
  case zero => simp [isMin_iff_forall_not_lt]
  case succ n =>
    simp only [Nat.cast_add, Nat.cast_one, add_eq_zero, one_ne_zero, and_false, false_or]
    rw [height_eq_coe_add_one_iff]
    simp only [hfin, true_and]
    congr! 3
    rename_i y _
    cases height y <;> simp; norm_cast; lia

中文:
引理 height_eq_coe_iff
  条件: {x : α} {n : 自然数}
  证明: by
  wlog hfin : height x < ⊤
  · simp_all
  simp only [hfin, true_and]
  cases n
  case zero => simp [isMin_iff_forall_not_lt]
  case succ n =>
    simp only [Nat.cast_add, Nat.cast_one, add_eq_zero, one_ne_zero, and_false, false_or]
    rw [height_eq_coe_add_one_iff]
    simp only [hfin, true_and]
    congr! 3
    rename_i y _
    cases height y <;> simp; norm_cast; lia

Depends on / 依赖: Nat.cast_add, Nat.cast_one, add_eq_zero, and_false, cast_add, cast_one, false_or, height, height_eq_coe_add_one_iff, isMin_iff_forall_not_lt, one_ne_zero, rename_i, true_and
-/
lemma height_eq_coe_iff {x : α} {n : Nat} :
    height x = n ↔
      height x < ⊤ ∧ (n = 0 ∨ exists y < x, height y = n - 1) ∧ (forall y < x, height y < n) := by
  wlog hfin : height x < ⊤
  · simp_all
  simp only [hfin, true_and]
  cases n
  case zero => simp [isMin_iff_forall_not_lt]
  case succ n =>
    simp only [Nat.cast_add, Nat.cast_one, add_eq_zero, one_ne_zero, and_false, false_or]
    rw [height_eq_coe_add_one_iff]
    simp only [hfin, true_and]
    congr! 3
    rename_i y _
    cases height y <;> simp; norm_cast; lia

/--
lemma `coheight_eq_coe_iff` / 引理 `coheight_eq_coe_iff`

English:
lemma coheight_eq_coe_iff
  given: {x : α} {n : Nat}
  proof: height_eq_coe_iff (α := αᵒᵈ)

中文:
引理 coheight_eq_coe_iff
  条件: {x : α} {n : 自然数}
  证明: height_eq_coe_iff (α := αᵒᵈ)

Depends on / 依赖: height_eq_coe_iff
-/
lemma coheight_eq_coe_iff {x : α} {n : Nat} :
    coheight x = n ↔
      coheight x < ⊤ ∧ (n = 0 ∨ exists y > x, coheight y = n - 1) ∧ (forall y > x, coheight y < n) :=
  height_eq_coe_iff (α := αᵒᵈ)

/--
lemma `height_eq_coe_iff_minimal_le_height` / 引理 `height_eq_coe_iff_minimal_le_height`

English:
lemma height_eq_coe_iff_minimal_le_height
  given: {a : α} {n : Nat}
  proof: by
  by_cases! hfin : height a < ⊤
  · cases hn : n with
    | zero => simp
    | succ => simp [minimal_iff_forall_lt, height_eq_coe_add_one_iff, ENat.add_one_le_iff,
        coe_lt_height_iff, *]
  · suffices exists x < a, ↑n <= height x by
      simp_all [minimal_iff_forall_lt]
    simp only [top_le_iff, height_eq_top_iff] at hfin
    obtain ⟨p, rfl, hp⟩ := hfin (n + 1)
    use p.eraseLast.last, p.eraseLast_last_rel_last (by lia)
    simpa [hp] using length_le_height_last (p := p.eraseLast)

中文:
引理 height_eq_coe_iff_minimal_le_height
  条件: {a : α} {n : 自然数}
  证明: by
  by_cases! hfin : height a < ⊤
  · cases hn : n with
    | zero => simp
    | succ => simp [minimal_iff_forall_lt, height_eq_coe_add_one_iff, ENat.add_one_le_iff,
        coe_lt_height_iff, *]
  · suffices exists x < a, ↑n <= height x by
      simp_all [minimal_iff_forall_lt]
    simp only [top_le_iff, height_eq_top_iff] at hfin
    obtain ⟨p, rfl, hp⟩ := hfin (n + 1)
    use p.eraseLast.last, p.eraseLast_last_rel_last (by lia)
    simpa [hp] using length_le_height_last (p := p.eraseLast)

Depends on / 依赖: ENat.add_one_le_iff, add_one_le_iff, coe_lt_height_iff, eraseLast, eraseLast_last_rel_last, height, height_eq_coe_add_one_iff, height_eq_top_iff, length_le_height_last, minimal_iff_forall_lt, p.eraseLast, p.eraseLast.last, p.eraseLast_last_rel_last, top_le_iff
-/
lemma height_eq_coe_iff_minimal_le_height {a : α} {n : Nat} :
    height a = n ↔ Minimal (fun y => n <= height y) a := by
  by_cases! hfin : height a < ⊤
  · cases hn : n with
    | zero => simp
    | succ => simp [minimal_iff_forall_lt, height_eq_coe_add_one_iff, ENat.add_one_le_iff,
        coe_lt_height_iff, *]
  · suffices exists x < a, ↑n <= height x by
      simp_all [minimal_iff_forall_lt]
    simp only [top_le_iff, height_eq_top_iff] at hfin
    obtain ⟨p, rfl, hp⟩ := hfin (n + 1)
    use p.eraseLast.last, p.eraseLast_last_rel_last (by lia)
    simpa [hp] using length_le_height_last (p := p.eraseLast)

/--
lemma `coheight_eq_coe_iff_maximal_le_coheight` / 引理 `coheight_eq_coe_iff_maximal_le_coheight`

English:
lemma coheight_eq_coe_iff_maximal_le_coheight
  given: {a : α} {n : Nat}
  proof: height_eq_coe_iff_minimal_le_height (α := αᵒᵈ)

中文:
引理 coheight_eq_coe_iff_maximal_le_coheight
  条件: {a : α} {n : 自然数}
  证明: height_eq_coe_iff_minimal_le_height (α := αᵒᵈ)

Depends on / 依赖: height_eq_coe_iff_minimal_le_height
-/
lemma coheight_eq_coe_iff_maximal_le_coheight {a : α} {n : Nat} :
    coheight a = n ↔ Maximal (fun y => n <= coheight y) a :=
  height_eq_coe_iff_minimal_le_height (α := αᵒᵈ)

/--
lemma `one_lt_height_iff` / 引理 `one_lt_height_iff`

English:
lemma one_lt_height_iff
  given: {x : α}
  statement: 1 < Order.height x ↔ exists y z, z < y ∧ y < x
  proof: by
  rw [← ENat.add_one_le_iff ENat.one_ne_top]; rw [one_add_one_eq_two]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨p, hp, hlen⟩ := Order.exists_series_of_le_height x (n := 2) h
    refine ⟨p 1, p 0, p.rel_of_lt ?_, hp ▸ p.rel_of_lt ?_⟩ <;> simp [Fin.lt_def, hlen]
  · rintro ⟨y, z, hzy, hyx⟩
    let p : LTSeries α := RelSeries.fromListIsChain [z, y, x] (List.cons_ne_nil z [y, x])
      (List.IsChain.cons_cons hzy <| List.isChain_pair.mpr hyx)
    have : p.last = x := by simp [p, ← RelSeries.getLast_toList]
    exact Order.length_le_height this.le

中文:
引理 one_lt_height_iff
  条件: {x : α}
  结论: 1 < Order.height x ↔ 存在 y z, z < y ∧ y < x
  证明: by
  rw [← ENat.add_one_le_iff ENat.one_ne_top]; rw [one_add_one_eq_two]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨p, hp, hlen⟩ := Order.exists_series_of_le_height x (n := 2) h
    refine ⟨p 1, p 0, p.rel_of_lt ?_, hp ▸ p.rel_of_lt ?_⟩ <;> simp [Fin.lt_def, hlen]
  · rintro ⟨y, z, hzy, hyx⟩
    let p : LTSeries α := RelSeries.fromListIsChain [z, y, x] (List.cons_ne_nil z [y, x])
      (List.IsChain.cons_cons hzy <| List.isChain_pair.mpr hyx)
    have : p.last = x := by simp [p, ← RelSeries.getLast_toList]
    exact Order.length_le_height this.le

Depends on / 依赖: ENat.add_one_le_iff, ENat.one_ne_top, Fin.lt_def, IsChain, LTSeries, List.IsChain.cons_cons, List.cons_ne_nil, List.isChain_pair.mpr, Order.exists_series_of_le_height, Order.length, RelSeries, RelSeries.fromListIsChain, RelSeries.getLast_toList, add_one_le_iff, cons_cons, cons_ne_nil, exists_series_of_le_height, fromListIsChain, getLast_toList, isChain_pair
-/
lemma one_lt_height_iff {x : α} : 1 < Order.height x ↔ exists y z, z < y ∧ y < x := by
  rw [← ENat.add_one_le_iff ENat.one_ne_top]; rw [one_add_one_eq_two]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨p, hp, hlen⟩ := Order.exists_series_of_le_height x (n := 2) h
    refine ⟨p 1, p 0, p.rel_of_lt ?_, hp ▸ p.rel_of_lt ?_⟩ <;> simp [Fin.lt_def, hlen]
  · rintro ⟨y, z, hzy, hyx⟩
    let p : LTSeries α := RelSeries.fromListIsChain [z, y, x] (List.cons_ne_nil z [y, x])
      (List.IsChain.cons_cons hzy <| List.isChain_pair.mpr hyx)
    have : p.last = x := by simp [p, ← RelSeries.getLast_toList]
    exact Order.length_le_height this.le

end height

/-!
## Krull dimension
-/

section krullDim

variable {α β : Type*}

variable [Preorder α] [Preorder β]

/--
lemma `LTSeries.length_le_krullDim` / 引理 `LTSeries.length_le_krullDim`

English:
lemma LTSeries.length_le_krullDim
  given: (p : LTSeries α)
  statement: p.length <= krullDim α
  proof: le_sSup ⟨_, rfl⟩

@[simp]

中文:
引理 LTSeries.length_le_krullDim
  条件: (p : LTSeries α)
  结论: p.length <= krullDim α
  证明: le_sSup ⟨_, rfl⟩

@[simp]

Depends on / 依赖: le_sSup
-/
lemma LTSeries.length_le_krullDim (p : LTSeries α) : p.length <= krullDim α := le_sSup ⟨_, rfl⟩

@[simp]
/--
lemma `krullDim_eq_bot_iff` / 引理 `krullDim_eq_bot_iff`

English:
lemma krullDim_eq_bot_iff
  statement: krullDim α = ⊥ ↔ IsEmpty α
  proof: by
  rw [eq_bot_iff]; rw [krullDim]; rw [iSup_le_iff]
  simp only [le_bot_iff, WithBot.natCast_ne_bot, isEmpty_iff]
  exact ⟨fun H x => H ⟨0, fun _ => x, by simp⟩, (· <| · 1)⟩

中文:
引理 krullDim_eq_bot_iff
  结论: krullDim α = ⊥ ↔ 是空 α
  证明: by
  rw [eq_bot_iff]; rw [krullDim]; rw [iSup_le_iff]
  simp only [le_bot_iff, WithBot.natCast_ne_bot, isEmpty_iff]
  exact ⟨fun H x => H ⟨0, fun _ => x, by simp⟩, (· <| · 1)⟩

Depends on / 依赖: WithBot, WithBot.natCast_ne_bot, eq_bot_iff, iSup_le_iff, isEmpty_iff, krullDim, le_bot_iff, natCast_ne_bot
-/
lemma krullDim_eq_bot_iff : krullDim α = ⊥ ↔ IsEmpty α := by
  rw [eq_bot_iff]; rw [krullDim]; rw [iSup_le_iff]
  simp only [le_bot_iff, WithBot.natCast_ne_bot, isEmpty_iff]
  exact ⟨fun H x => H ⟨0, fun _ => x, by simp⟩, (· <| · 1)⟩

/--
lemma `krullDim_nonneg_iff` / 引理 `krullDim_nonneg_iff`

English:
lemma krullDim_nonneg_iff
  statement: 0 <= krullDim α ↔ Nonempty α
  proof: by
  contrapose!
  rw [← krullDim_eq_bot_iff]; rw [← WithBot.lt_coe_bot]; rw [bot_eq_zero]; rw [WithBot.coe_zero]

中文:
引理 krullDim_nonneg_iff
  结论: 0 <= krullDim α ↔ 非空 α
  证明: by
  contrapose!
  rw [← krullDim_eq_bot_iff]; rw [← WithBot.lt_coe_bot]; rw [bot_eq_zero]; rw [WithBot.coe_zero]

Depends on / 依赖: WithBot, WithBot.coe_zero, WithBot.lt_coe_bot, bot_eq_zero, coe_zero, contrapose, krullDim_eq_bot_iff, lt_coe_bot
-/
lemma krullDim_nonneg_iff : 0 <= krullDim α ↔ Nonempty α := by
  contrapose!
  rw [← krullDim_eq_bot_iff]; rw [← WithBot.lt_coe_bot]; rw [bot_eq_zero]; rw [WithBot.coe_zero]

/--
lemma `krullDim_eq_bot` / 引理 `krullDim_eq_bot`

English:
lemma krullDim_eq_bot
  given: [IsEmpty α]
  statement: krullDim α = ⊥
  proof: krullDim_eq_bot_iff.mpr ‹_›

中文:
引理 krullDim_eq_bot
  条件: [是空 α]
  结论: krullDim α = ⊥
  证明: krullDim_eq_bot_iff.mpr ‹_›

Depends on / 依赖: krullDim_eq_bot_iff, krullDim_eq_bot_iff.mpr
-/
lemma krullDim_eq_bot [IsEmpty α] : krullDim α = ⊥ := krullDim_eq_bot_iff.mpr ‹_›

/--
lemma `krullDim_nonneg` / 引理 `krullDim_nonneg`

English:
lemma krullDim_nonneg
  given: [Nonempty α]
  statement: 0 <= krullDim α
  proof: krullDim_nonneg_iff.mpr ‹_›

中文:
引理 krullDim_nonneg
  条件: [非空 α]
  结论: 0 <= krullDim α
  证明: krullDim_nonneg_iff.mpr ‹_›

Depends on / 依赖: krullDim_nonneg_iff, krullDim_nonneg_iff.mpr
-/
lemma krullDim_nonneg [Nonempty α] : 0 <= krullDim α := krullDim_nonneg_iff.mpr ‹_›

/--
theorem `krullDim_ne_bot_iff` / 定理 `krullDim_ne_bot_iff`

English:
theorem krullDim_ne_bot_iff
  statement: krullDim α != ⊥ ↔ Nonempty α
  proof: by
  rw [ne_eq]; rw [krullDim_eq_bot_iff]; rw [not_isEmpty_iff]

中文:
定理 krullDim_ne_bot_iff
  结论: krullDim α != ⊥ ↔ 非空 α
  证明: by
  rw [ne_eq]; rw [krullDim_eq_bot_iff]; rw [not_isEmpty_iff]

Depends on / 依赖: krullDim_eq_bot_iff, ne_eq, not_isEmpty_iff
-/
theorem krullDim_ne_bot_iff : krullDim α != ⊥ ↔ Nonempty α := by
  rw [ne_eq]; rw [krullDim_eq_bot_iff]; rw [not_isEmpty_iff]

/--
theorem `bot_lt_krullDim_iff` / 定理 `bot_lt_krullDim_iff`

English:
theorem bot_lt_krullDim_iff
  statement: ⊥ < krullDim α ↔ Nonempty α
  proof: by
  rw [bot_lt_iff_ne_bot]; rw [krullDim_ne_bot_iff]

中文:
定理 bot_lt_krullDim_iff
  结论: ⊥ < krullDim α ↔ 非空 α
  证明: by
  rw [bot_lt_iff_ne_bot]; rw [krullDim_ne_bot_iff]

Depends on / 依赖: bot_lt_iff_ne_bot, krullDim_ne_bot_iff
-/
theorem bot_lt_krullDim_iff : ⊥ < krullDim α ↔ Nonempty α := by
  rw [bot_lt_iff_ne_bot]; rw [krullDim_ne_bot_iff]

/--
theorem `bot_lt_krullDim` / 定理 `bot_lt_krullDim`

English:
theorem bot_lt_krullDim
  given: [Nonempty α]
  statement: ⊥ < krullDim α
  proof: bot_lt_krullDim_iff.mpr ‹_›

中文:
定理 bot_lt_krullDim
  条件: [非空 α]
  结论: ⊥ < krullDim α
  证明: bot_lt_krullDim_iff.mpr ‹_›

Depends on / 依赖: bot_lt_krullDim_iff, bot_lt_krullDim_iff.mpr
-/
theorem bot_lt_krullDim [Nonempty α] : ⊥ < krullDim α :=
  bot_lt_krullDim_iff.mpr ‹_›

/--
lemma `krullDim_nonpos_iff_forall_isMax` / 引理 `krullDim_nonpos_iff_forall_isMax`

English:
lemma krullDim_nonpos_iff_forall_isMax
  statement: krullDim α <= 0 ↔ forall x : α, IsMax x
  proof: by
  simp only [krullDim, iSup_le_iff, isMax_iff_forall_not_lt]
  refine ⟨fun H x y h => (H ⟨1, ![x, y],
    fun i => by obtain rfl := Subsingleton.elim i 0; simpa⟩).not_gt (by simp), ?_⟩
  · rintro H ⟨_ | n, l, h⟩
    · simp
    · cases H (l 0) (l 1) (h 0)

中文:
引理 krullDim_nonpos_iff_对任意_isMax
  结论: krullDim α <= 0 ↔ 对任意 x : α, IsMax x
  证明: by
  simp only [krullDim, iSup_le_iff, isMax_iff_forall_not_lt]
  refine ⟨fun H x y h => (H ⟨1, ![x, y],
    fun i => by obtain rfl := Subsingleton.elim i 0; simpa⟩).not_gt (by simp), ?_⟩
  · rintro H ⟨_ | n, l, h⟩
    · simp
    · cases H (l 0) (l 1) (h 0)

Depends on / 依赖: Subsingleton, Subsingleton.elim, iSup_le_iff, isMax_iff_forall_not_lt, krullDim, not_gt
-/
lemma krullDim_nonpos_iff_forall_isMax : krullDim α <= 0 ↔ forall x : α, IsMax x := by
  simp only [krullDim, iSup_le_iff, isMax_iff_forall_not_lt]
  refine ⟨fun H x y h => (H ⟨1, ![x, y],
    fun i => by obtain rfl := Subsingleton.elim i 0; simpa⟩).not_gt (by simp), ?_⟩
  · rintro H ⟨_ | n, l, h⟩
    · simp
    · cases H (l 0) (l 1) (h 0)

/--
lemma `krullDim_nonpos_iff_forall_isMin` / 引理 `krullDim_nonpos_iff_forall_isMin`

English:
lemma krullDim_nonpos_iff_forall_isMin
  statement: krullDim α <= 0 ↔ forall x : α, IsMin x
  proof: by
  simp only [krullDim_nonpos_iff_forall_isMax, IsMax, IsMin]
  exact forall_comm

中文:
引理 krullDim_nonpos_iff_对任意_isMin
  结论: krullDim α <= 0 ↔ 对任意 x : α, IsMin x
  证明: by
  simp only [krullDim_nonpos_iff_forall_isMax, IsMax, IsMin]
  exact forall_comm

Depends on / 依赖: forall_comm, krullDim_nonpos_iff_forall_isMax
-/
lemma krullDim_nonpos_iff_forall_isMin : krullDim α <= 0 ↔ forall x : α, IsMin x := by
  simp only [krullDim_nonpos_iff_forall_isMax, IsMax, IsMin]
  exact forall_comm

/--
lemma `krullDim_le_one_iff` / 引理 `krullDim_le_one_iff`

English:
lemma krullDim_le_one_iff
  statement: krullDim α <= 1 ↔ forall x : α, IsMin x ∨ IsMax x
  proof: by
  simp_rw [isMax_iff_forall_not_lt, isMin_iff_forall_not_lt, krullDim, iSup_le_iff]
  contrapose!
  constructor
  · rintro ⟨⟨_ | _ | n, l, hl⟩, hl'⟩
    iterate 2 · cases hl'.not_ge (by simp)
    exact ⟨l 1, ⟨l 0, hl 0⟩, l 2, hl 1⟩
  · rintro ⟨x, ⟨y, hxy⟩, z, hzx⟩
    exact ⟨⟨2, ![y, x, z], fun i => by fin_cases i <;> simpa⟩, by simp⟩

中文:
引理 krullDim_le_one_iff
  结论: krullDim α <= 1 ↔ 对任意 x : α, IsMin x ∨ IsMax x
  证明: by
  simp_rw [isMax_iff_forall_not_lt, isMin_iff_forall_not_lt, krullDim, iSup_le_iff]
  contrapose!
  constructor
  · rintro ⟨⟨_ | _ | n, l, hl⟩, hl'⟩
    iterate 2 · cases hl'.not_ge (by simp)
    exact ⟨l 1, ⟨l 0, hl 0⟩, l 2, hl 1⟩
  · rintro ⟨x, ⟨y, hxy⟩, z, hzx⟩
    exact ⟨⟨2, ![y, x, z], fun i => by fin_cases i <;> simpa⟩, by simp⟩

Depends on / 依赖: contrapose, fin_cases, iSup_le_iff, isMax_iff_forall_not_lt, isMin_iff_forall_not_lt, iterate, krullDim, not_ge, simp_rw
-/
lemma krullDim_le_one_iff : krullDim α <= 1 ↔ forall x : α, IsMin x ∨ IsMax x := by
  simp_rw [isMax_iff_forall_not_lt, isMin_iff_forall_not_lt, krullDim, iSup_le_iff]
  contrapose!
  constructor
  · rintro ⟨⟨_ | _ | n, l, hl⟩, hl'⟩
    iterate 2 · cases hl'.not_ge (by simp)
    exact ⟨l 1, ⟨l 0, hl 0⟩, l 2, hl 1⟩
  · rintro ⟨x, ⟨y, hxy⟩, z, hzx⟩
    exact ⟨⟨2, ![y, x, z], fun i => by fin_cases i <;> simpa⟩, by simp⟩

/--
lemma `krullDim_pos_iff` / 引理 `krullDim_pos_iff`

English:
lemma krullDim_pos_iff
  statement: 0 < krullDim α ↔ exists x y : α, x < y
  proof: by
  contrapose!
  simp_rw [← isMax_iff_forall_not_lt, ← krullDim_nonpos_iff_forall_isMax]

中文:
引理 krullDim_pos_iff
  结论: 0 < krullDim α ↔ 存在 x y : α, x < y
  证明: by
  contrapose!
  simp_rw [← isMax_iff_forall_not_lt, ← krullDim_nonpos_iff_forall_isMax]

Depends on / 依赖: contrapose, isMax_iff_forall_not_lt, krullDim_nonpos_iff_forall_isMax, simp_rw
-/
lemma krullDim_pos_iff : 0 < krullDim α ↔ exists x y : α, x < y := by
  contrapose!
  simp_rw [← isMax_iff_forall_not_lt, ← krullDim_nonpos_iff_forall_isMax]

/--
lemma `one_le_krullDim_iff` / 引理 `one_le_krullDim_iff`

English:
lemma one_le_krullDim_iff
  statement: 1 <= krullDim α ↔ exists x y : α, x < y
  proof: by
  rw [← krullDim_pos_iff]; rw [← Nat.cast_zero]; rw [← ENat.WithBot.add_one_le_iff]; rw [Nat.cast_zero]; rw [zero_add]

中文:
引理 one_le_krullDim_iff
  结论: 1 <= krullDim α ↔ 存在 x y : α, x < y
  证明: by
  rw [← krullDim_pos_iff]; rw [← Nat.cast_zero]; rw [← ENat.WithBot.add_one_le_iff]; rw [Nat.cast_zero]; rw [zero_add]

Depends on / 依赖: ENat.WithBot.add_one_le_iff, Nat.cast_zero, WithBot, add_one_le_iff, cast_zero, krullDim_pos_iff, zero_add
-/
lemma one_le_krullDim_iff : 1 <= krullDim α ↔ exists x y : α, x < y := by
  rw [← krullDim_pos_iff]; rw [← Nat.cast_zero]; rw [← ENat.WithBot.add_one_le_iff]; rw [Nat.cast_zero]; rw [zero_add]

/--
lemma `krullDim_nonpos_of_subsingleton` / 引理 `krullDim_nonpos_of_subsingleton`

English:
lemma krullDim_nonpos_of_subsingleton
  given: [Subsingleton α]
  statement: krullDim α <= 0
  proof: by
  rw [krullDim_nonpos_iff_forall_isMax]
  exact fun x y h => (Subsingleton.elim x y).ge

中文:
引理 krullDim_nonpos_of_subsingleton
  条件: [子单例 α]
  结论: krullDim α <= 0
  证明: by
  rw [krullDim_nonpos_iff_forall_isMax]
  exact fun x y h => (Subsingleton.elim x y).ge

Depends on / 依赖: Subsingleton, Subsingleton.elim, krullDim_nonpos_iff_forall_isMax
-/
lemma krullDim_nonpos_of_subsingleton [Subsingleton α] : krullDim α <= 0 := by
  rw [krullDim_nonpos_iff_forall_isMax]
  exact fun x y h => (Subsingleton.elim x y).ge

/--
lemma `krullDim_eq_zero` / 引理 `krullDim_eq_zero`

English:
lemma krullDim_eq_zero
  given: [Nonempty α] [Subsingleton α]
  proof: le_antisymm krullDim_nonpos_of_subsingleton krullDim_nonneg

中文:
引理 krullDim_eq_zero
  条件: [非空 α] [子单例 α]
  证明: le_antisymm krullDim_nonpos_of_subsingleton krullDim_nonneg

Depends on / 依赖: krullDim_nonneg, krullDim_nonpos_of_subsingleton, le_antisymm
-/
lemma krullDim_eq_zero [Nonempty α] [Subsingleton α] :
    krullDim α = 0 :=
  le_antisymm krullDim_nonpos_of_subsingleton krullDim_nonneg

/--
lemma `krullDim_eq_zero_of_unique` / 引理 `krullDim_eq_zero_of_unique`

English:
lemma krullDim_eq_zero_of_unique
  given: [Unique α]
  statement: krullDim α = 0
  proof: le_antisymm krullDim_nonpos_of_subsingleton krullDim_nonneg

中文:
引理 krullDim_eq_zero_of_unique
  条件: [唯一 α]
  结论: krullDim α = 0
  证明: le_antisymm krullDim_nonpos_of_subsingleton krullDim_nonneg

Depends on / 依赖: krullDim_nonneg, krullDim_nonpos_of_subsingleton, le_antisymm
-/
lemma krullDim_eq_zero_of_unique [Unique α] : krullDim α = 0 :=
  le_antisymm krullDim_nonpos_of_subsingleton krullDim_nonneg

section PartialOrder

variable {α : Type*} [PartialOrder α]

/--
lemma `krullDim_le_one_iff_forall_isMax` / 引理 `krullDim_le_one_iff_forall_isMax`

English:
lemma krullDim_le_one_iff_forall_isMax
  given: [OrderBot α]
  proof: by
  simp [krullDim_le_one_iff, ← or_iff_not_imp_left]

中文:
引理 krullDim_le_one_iff_对任意_isMax
  条件: [有底序 α]
  证明: by
  simp [krullDim_le_one_iff, ← or_iff_not_imp_left]

Depends on / 依赖: krullDim_le_one_iff, or_iff_not_imp_left
-/
lemma krullDim_le_one_iff_forall_isMax [OrderBot α] :
    krullDim α <= 1 ↔ forall x : α, x != ⊥ -> IsMax x := by
  simp [krullDim_le_one_iff, ← or_iff_not_imp_left]

/--
lemma `krullDim_eq_zero_iff_of_orderBot` / 引理 `krullDim_eq_zero_iff_of_orderBot`

English:
lemma krullDim_eq_zero_iff_of_orderBot
  given: [OrderBot α]
  proof: ⟨fun H => subsingleton_of_forall_eq ⊥ fun _ => le_bot_iff.mp
    (krullDim_nonpos_iff_forall_isMax.mp H.le ⊥ bot_le), fun _ => Order.krullDim_eq_zero⟩

中文:
引理 krullDim_eq_zero_iff_of_orderBot
  条件: [有底序 α]
  证明: ⟨fun H => subsingleton_of_forall_eq ⊥ fun _ => le_bot_iff.mp
    (krullDim_nonpos_iff_forall_isMax.mp H.le ⊥ bot_le), fun _ => Order.krullDim_eq_zero⟩

Depends on / 依赖: H.le, Order.krullDim_eq_zero, bot_le, krullDim_eq_zero, krullDim_nonpos_iff_forall_isMax, krullDim_nonpos_iff_forall_isMax.mp, le_bot_iff, le_bot_iff.mp, subsingleton_of_forall_eq
-/
lemma krullDim_eq_zero_iff_of_orderBot [OrderBot α] :
    krullDim α = 0 ↔ Subsingleton α :=
  ⟨fun H => subsingleton_of_forall_eq ⊥ fun _ => le_bot_iff.mp
    (krullDim_nonpos_iff_forall_isMax.mp H.le ⊥ bot_le), fun _ => Order.krullDim_eq_zero⟩

/--
lemma `krullDim_pos_iff_of_orderBot` / 引理 `krullDim_pos_iff_of_orderBot`

English:
lemma krullDim_pos_iff_of_orderBot
  given: [OrderBot α]
  proof: by
  rw [← not_subsingleton_iff_nontrivial]; rw [← Order.krullDim_eq_zero_iff_of_orderBot]; rw [← ne_eq]; rw [← lt_or_lt_iff_ne]; rw [or_iff_right]
  simp [Order.krullDim_nonneg]

中文:
引理 krullDim_pos_iff_of_orderBot
  条件: [有底序 α]
  证明: by
  rw [← not_subsingleton_iff_nontrivial]; rw [← Order.krullDim_eq_zero_iff_of_orderBot]; rw [← ne_eq]; rw [← lt_or_lt_iff_ne]; rw [or_iff_right]
  simp [Order.krullDim_nonneg]

Depends on / 依赖: Order.krullDim_eq_zero_iff_of_orderBot, Order.krullDim_nonneg, krullDim_eq_zero_iff_of_orderBot, krullDim_nonneg, lt_or_lt_iff_ne, ne_eq, not_subsingleton_iff_nontrivial, or_iff_right
-/
lemma krullDim_pos_iff_of_orderBot [OrderBot α] :
    0 < krullDim α ↔ Nontrivial α := by
  rw [← not_subsingleton_iff_nontrivial]; rw [← Order.krullDim_eq_zero_iff_of_orderBot]; rw [← ne_eq]; rw [← lt_or_lt_iff_ne]; rw [or_iff_right]
  simp [Order.krullDim_nonneg]

/--
lemma `krullDim_le_one_iff_forall_isMin` / 引理 `krullDim_le_one_iff_forall_isMin`

English:
lemma krullDim_le_one_iff_forall_isMin
  given: [OrderTop α]
  proof: by
  simp [krullDim_le_one_iff, ← or_iff_not_imp_right]

中文:
引理 krullDim_le_one_iff_对任意_isMin
  条件: [有顶序 α]
  证明: by
  simp [krullDim_le_one_iff, ← or_iff_not_imp_right]

Depends on / 依赖: krullDim_le_one_iff, or_iff_not_imp_right
-/
lemma krullDim_le_one_iff_forall_isMin [OrderTop α] :
    krullDim α <= 1 ↔ forall x : α, x != ⊤ -> IsMin x := by
  simp [krullDim_le_one_iff, ← or_iff_not_imp_right]

/--
lemma `krullDim_eq_zero_iff_of_orderTop` / 引理 `krullDim_eq_zero_iff_of_orderTop`

English:
lemma krullDim_eq_zero_iff_of_orderTop
  given: [OrderTop α]
  proof: ⟨fun H => subsingleton_of_forall_eq ⊤ fun _ => top_le_iff.mp
    (krullDim_nonpos_iff_forall_isMin.mp H.le ⊤ le_top), fun _ => Order.krullDim_eq_zero⟩

中文:
引理 krullDim_eq_zero_iff_of_orderTop
  条件: [有顶序 α]
  证明: ⟨fun H => subsingleton_of_forall_eq ⊤ fun _ => top_le_iff.mp
    (krullDim_nonpos_iff_forall_isMin.mp H.le ⊤ le_top), fun _ => Order.krullDim_eq_zero⟩

Depends on / 依赖: H.le, Order.krullDim_eq_zero, krullDim_eq_zero, krullDim_nonpos_iff_forall_isMin, krullDim_nonpos_iff_forall_isMin.mp, le_top, subsingleton_of_forall_eq, top_le_iff, top_le_iff.mp
-/
lemma krullDim_eq_zero_iff_of_orderTop [OrderTop α] :
    krullDim α = 0 ↔ Subsingleton α :=
  ⟨fun H => subsingleton_of_forall_eq ⊤ fun _ => top_le_iff.mp
    (krullDim_nonpos_iff_forall_isMin.mp H.le ⊤ le_top), fun _ => Order.krullDim_eq_zero⟩

/--
lemma `krullDim_pos_iff_of_orderTop` / 引理 `krullDim_pos_iff_of_orderTop`

English:
lemma krullDim_pos_iff_of_orderTop
  given: [OrderTop α]
  proof: by
  rw [← not_subsingleton_iff_nontrivial]; rw [← Order.krullDim_eq_zero_iff_of_orderTop]; rw [← ne_eq]; rw [← lt_or_lt_iff_ne]; rw [or_iff_right]
  simp [Order.krullDim_nonneg]

中文:
引理 krullDim_pos_iff_of_orderTop
  条件: [有顶序 α]
  证明: by
  rw [← not_subsingleton_iff_nontrivial]; rw [← Order.krullDim_eq_zero_iff_of_orderTop]; rw [← ne_eq]; rw [← lt_or_lt_iff_ne]; rw [or_iff_right]
  simp [Order.krullDim_nonneg]

Depends on / 依赖: Order.krullDim_eq_zero_iff_of_orderTop, Order.krullDim_nonneg, krullDim_eq_zero_iff_of_orderTop, krullDim_nonneg, lt_or_lt_iff_ne, ne_eq, not_subsingleton_iff_nontrivial, or_iff_right
-/
lemma krullDim_pos_iff_of_orderTop [OrderTop α] :
    0 < krullDim α ↔ Nontrivial α := by
  rw [← not_subsingleton_iff_nontrivial]; rw [← Order.krullDim_eq_zero_iff_of_orderTop]; rw [← ne_eq]; rw [← lt_or_lt_iff_ne]; rw [or_iff_right]
  simp [Order.krullDim_nonneg]

/--
lemma `krullDim_le_one_iff_of_boundedOrder` / 引理 `krullDim_le_one_iff_of_boundedOrder`

English:
lemma krullDim_le_one_iff_of_boundedOrder
  given: [BoundedOrder α]
  proof: by
  simp [Order.krullDim_le_one_iff]

中文:
引理 krullDim_le_one_iff_of_boundedOrder
  条件: [有界序 α]
  证明: by
  simp [Order.krullDim_le_one_iff]

Depends on / 依赖: Order.krullDim_le_one_iff, krullDim_le_one_iff
-/
lemma krullDim_le_one_iff_of_boundedOrder [BoundedOrder α] :
    krullDim α <= 1 ↔ forall x : α, x = ⊥ ∨ x = ⊤ := by
  simp [Order.krullDim_le_one_iff]

end PartialOrder

/--
lemma `krullDim_eq_length_of_finiteDimensionalOrder` / 引理 `krullDim_eq_length_of_finiteDimensionalOrder`

English:
lemma krullDim_eq_length_of_finiteDimensionalOrder
  given: [FiniteDimensionalOrder α]
  proof: le_antisymm
    (iSup_le <| fun _ => WithBot.coe_le_coe.mpr <| WithTop.coe_le_coe.mpr <|
      RelSeries.length_le_length_longestOf _ _) <|
le_iSup (fun (i : LTSeries _) => (i.length : WithBot (WithTop Nat))) LTSeries.longestOf _

中文:
引理 krullDim_eq_length_of_finiteDimensionalOrder
  条件: [FiniteDimensionalOrder α]
  证明: le_antisymm
    (iSup_le <| fun _ => WithBot.coe_le_coe.mpr <| WithTop.coe_le_coe.mpr <|
      RelSeries.length_le_length_longestOf _ _) <|
le_iSup (fun (i : LTSeries _) => (i.length : WithBot (WithTop Nat))) LTSeries.longestOf _

Depends on / 依赖: LTSeries, LTSeries.longestOf, RelSeries, RelSeries.length_le_length_longestOf, WithBot, WithBot.coe_le_coe.mpr, WithTop, WithTop.coe_le_coe.mpr, coe_le_coe, i.length, iSup_le, le_antisymm, le_iSup, length, length_le_length_longestOf, longestOf
-/
lemma krullDim_eq_length_of_finiteDimensionalOrder [FiniteDimensionalOrder α] :
    krullDim α = (LTSeries.longestOf α).length :=
  le_antisymm
    (iSup_le <| fun _ => WithBot.coe_le_coe.mpr <| WithTop.coe_le_coe.mpr <|
      RelSeries.length_le_length_longestOf _ _) <|
le_iSup (fun (i : LTSeries _) => (i.length : WithBot (WithTop Nat))) LTSeries.longestOf _

/--
lemma `krullDim_eq_top` / 引理 `krullDim_eq_top`

English:
lemma krullDim_eq_top
  given: [InfiniteDimensionalOrder α]
  proof: le_antisymm le_top le_iSup_iff.mpr fun m hm => match m, hm with
| ⊥, hm => False.elim by
    have : Inhabited α := ⟨LTSeries.withLength _ 0 0⟩
exact not_le_of_gt (WithBot.bot_lt_coe _ : ⊥ < (0 : WithBot (WithTop Nat))) hm default
  | ⊤, _ => le_refl _
  | m, hm => by
    rw [top_le_iff]; rw [ENat.WithBot.eq_top_iff_forall_ge]
    intro n
    simpa using hm (LTSeries.withLength _ n)

中文:
引理 krullDim_eq_top
  条件: [InfiniteDimensionalOrder α]
  证明: le_antisymm le_top le_iSup_iff.mpr fun m hm => match m, hm with
| ⊥, hm => False.elim by
    have : Inhabited α := ⟨LTSeries.withLength _ 0 0⟩
exact not_le_of_gt (WithBot.bot_lt_coe _ : ⊥ < (0 : WithBot (WithTop Nat))) hm default
  | ⊤, _ => le_refl _
  | m, hm => by
    rw [top_le_iff]; rw [ENat.WithBot.eq_top_iff_forall_ge]
    intro n
    simpa using hm (LTSeries.withLength _ n)

Depends on / 依赖: ENat.WithBot.eq_top_iff_forall_ge, False.elim, Inhabited, LTSeries, LTSeries.withLength, WithBot, WithBot.bot_lt_coe, WithTop, bot_lt_coe, eq_top_iff_forall_ge, le_antisymm, le_iSup_iff, le_iSup_iff.mpr, le_refl, le_top, not_le_of_gt, top_le_iff, withLength
-/
lemma krullDim_eq_top [InfiniteDimensionalOrder α] :
    krullDim α = ⊤ :=
le_antisymm le_top le_iSup_iff.mpr fun m hm => match m, hm with
| ⊥, hm => False.elim by
    have : Inhabited α := ⟨LTSeries.withLength _ 0 0⟩
exact not_le_of_gt (WithBot.bot_lt_coe _ : ⊥ < (0 : WithBot (WithTop Nat))) hm default
  | ⊤, _ => le_refl _
  | m, hm => by
    rw [top_le_iff]; rw [ENat.WithBot.eq_top_iff_forall_ge]
    intro n
    simpa using hm (LTSeries.withLength _ n)

/--
lemma `krullDim_eq_top_iff` / 引理 `krullDim_eq_top_iff`

English:
lemma krullDim_eq_top_iff
  statement: krullDim α = ⊤ ↔ InfiniteDimensionalOrder α
  proof: by
  refine ⟨fun h => ?_, fun _ => krullDim_eq_top⟩
  cases isEmpty_or_nonempty α
  · simp [krullDim_eq_bot] at h
  cases finiteDimensionalOrder_or_infiniteDimensionalOrder α
  · rw [krullDim_eq_length_of_finiteDimensionalOrder] at h
    cases h
  · infer_instance

中文:
引理 krullDim_eq_top_iff
  结论: krullDim α = ⊤ ↔ InfiniteDimensionalOrder α
  证明: by
  refine ⟨fun h => ?_, fun _ => krullDim_eq_top⟩
  cases isEmpty_or_nonempty α
  · simp [krullDim_eq_bot] at h
  cases finiteDimensionalOrder_or_infiniteDimensionalOrder α
  · rw [krullDim_eq_length_of_finiteDimensionalOrder] at h
    cases h
  · infer_instance

Depends on / 依赖: finiteDimensionalOrder_or_infiniteDimensionalOrder, infer_instance, isEmpty_or_nonempty, krullDim_eq_bot, krullDim_eq_length_of_finiteDimensionalOrder, krullDim_eq_top
-/
lemma krullDim_eq_top_iff : krullDim α = ⊤ ↔ InfiniteDimensionalOrder α := by
  refine ⟨fun h => ?_, fun _ => krullDim_eq_top⟩
  cases isEmpty_or_nonempty α
  · simp [krullDim_eq_bot] at h
  cases finiteDimensionalOrder_or_infiniteDimensionalOrder α
  · rw [krullDim_eq_length_of_finiteDimensionalOrder] at h
    cases h
  · infer_instance

/--
lemma `le_krullDim_iff` / 引理 `le_krullDim_iff`

English:
lemma le_krullDim_iff
  given: {n : Nat}
  statement: n <= krullDim α ↔ exists l : LTSeries α, l.length = n
  proof: by
  cases isEmpty_or_nonempty α
  · simp [krullDim_eq_bot]
  cases finiteDimensionalOrder_or_infiniteDimensionalOrder α
  · rw [krullDim_eq_length_of_finiteDimensionalOrder, Nat.cast_le]
    constructor
    · exact fun H => ⟨(LTSeries.longestOf α).take ⟨_, Nat.lt_succ_of_le H⟩, rfl⟩
    · exact fun ⟨l, hl⟩ => hl ▸ l.longestOf_is_longest
  · simpa [krullDim_eq_top] using SetRel.InfiniteDimensional.exists_relSeries_with_length n

中文:
引理 le_krullDim_iff
  条件: {n : 自然数}
  结论: n <= krullDim α ↔ 存在 l : LTSeries α, l.length = n
  证明: by
  cases isEmpty_or_nonempty α
  · simp [krullDim_eq_bot]
  cases finiteDimensionalOrder_or_infiniteDimensionalOrder α
  · rw [krullDim_eq_length_of_finiteDimensionalOrder, Nat.cast_le]
    constructor
    · exact fun H => ⟨(LTSeries.longestOf α).take ⟨_, Nat.lt_succ_of_le H⟩, rfl⟩
    · exact fun ⟨l, hl⟩ => hl ▸ l.longestOf_is_longest
  · simpa [krullDim_eq_top] using SetRel.InfiniteDimensional.exists_relSeries_with_length n

Depends on / 依赖: InfiniteDimensional, LTSeries, LTSeries.longestOf, Nat.cast_le, Nat.lt_succ_of_le, SetRel, SetRel.InfiniteDimensional.exists_relSeries_with_length, cast_le, exists_relSeries_with_length, finiteDimensionalOrder_or_infiniteDimensionalOrder, isEmpty_or_nonempty, krullDim_eq_bot, krullDim_eq_length_of_finiteDimensionalOrder, krullDim_eq_top, l.longestOf_is_longest, longestOf, longestOf_is_longest, lt_succ_of_le
-/
lemma le_krullDim_iff {n : Nat} : n <= krullDim α ↔ exists l : LTSeries α, l.length = n := by
  cases isEmpty_or_nonempty α
  · simp [krullDim_eq_bot]
  cases finiteDimensionalOrder_or_infiniteDimensionalOrder α
  · rw [krullDim_eq_length_of_finiteDimensionalOrder, Nat.cast_le]
    constructor
    · exact fun H => ⟨(LTSeries.longestOf α).take ⟨_, Nat.lt_succ_of_le H⟩, rfl⟩
    · exact fun ⟨l, hl⟩ => hl ▸ l.longestOf_is_longest
  · simpa [krullDim_eq_top] using SetRel.InfiniteDimensional.exists_relSeries_with_length n

/--
lemma `krullDim_eq_iSup_length` / 引理 `krullDim_eq_iSup_length`

English:
lemma krullDim_eq_iSup_length
  given: [Nonempty α]
  proof: by
  simp [krullDim, WithBot.coe_iSup (OrderTop.bddAbove _), WithBot.coe_natCast]

中文:
引理 krullDim_eq_iSup_length
  条件: [非空 α]
  证明: by
  simp [krullDim, WithBot.coe_iSup (OrderTop.bddAbove _), WithBot.coe_natCast]

Depends on / 依赖: OrderTop, OrderTop.bddAbove, WithBot, WithBot.coe_iSup, WithBot.coe_natCast, bddAbove, coe_iSup, coe_natCast, krullDim
-/
lemma krullDim_eq_iSup_length [Nonempty α] :
    krullDim α = ⨆ (p : LTSeries α), (p.length : Nat∞) := by
  simp [krullDim, WithBot.coe_iSup (OrderTop.bddAbove _), WithBot.coe_natCast]

/--
lemma `krullDim_lt_coe_iff` / 引理 `krullDim_lt_coe_iff`

English:
lemma krullDim_lt_coe_iff
  given: {n : Nat}
  statement: krullDim α < n ↔ forall l : LTSeries α, l.length < n
  proof: by
  rw [krullDim]; rw [← WithBot.coe_natCast]
  rcases n with - | n
  · rw [ENat.natCast_zero, ← bot_eq_zero, WithBot.lt_coe_bot]
    simp
  · simp [ENat.WithBot.lt_add_one_iff, WithBot.coe_natCast]

中文:
引理 krullDim_lt_coe_iff
  条件: {n : 自然数}
  结论: krullDim α < n ↔ 对任意 l : LTSeries α, l.length < n
  证明: by
  rw [krullDim]; rw [← WithBot.coe_natCast]
  rcases n with - | n
  · rw [ENat.natCast_zero, ← bot_eq_zero, WithBot.lt_coe_bot]
    simp
  · simp [ENat.WithBot.lt_add_one_iff, WithBot.coe_natCast]

Depends on / 依赖: ENat.WithBot.lt_add_one_iff, ENat.natCast_zero, WithBot, WithBot.coe_natCast, WithBot.lt_coe_bot, bot_eq_zero, coe_natCast, krullDim, lt_add_one_iff, lt_coe_bot, natCast_zero
-/
lemma krullDim_lt_coe_iff {n : Nat} : krullDim α < n ↔ forall l : LTSeries α, l.length < n := by
  rw [krullDim]; rw [← WithBot.coe_natCast]
  rcases n with - | n
  · rw [ENat.natCast_zero, ← bot_eq_zero, WithBot.lt_coe_bot]
    simp
  · simp [ENat.WithBot.lt_add_one_iff, WithBot.coe_natCast]

/--
lemma `krullDim_le_of_strictMono` / 引理 `krullDim_le_of_strictMono`

English:
lemma krullDim_le_of_strictMono
  given: (f : α -> β) (hf : StrictMono f)
  statement: krullDim α <= krullDim β
  proof: iSup_le fun p => le_sSup ⟨p.map f hf, rfl⟩

中文:
引理 krullDim_le_of_strictMono
  条件: (f : α -> β) (hf : 严格递增 f)
  结论: krullDim α <= krullDim β
  证明: iSup_le fun p => le_sSup ⟨p.map f hf, rfl⟩

Depends on / 依赖: iSup_le, le_sSup, p.map
-/
lemma krullDim_le_of_strictMono (f : α -> β) (hf : StrictMono f) : krullDim α <= krullDim β :=
  iSup_le fun p => le_sSup ⟨p.map f hf, rfl⟩

/--
lemma `krullDim_le_of_strictComono_and_surj` / 引理 `krullDim_le_of_strictComono_and_surj`

English:
lemma krullDim_le_of_strictComono_and_surj
  proof: iSup_le fun p => le_sSup ⟨p.comap _ hf hf', rfl⟩

中文:
引理 krullDim_le_of_strictComono_and_surj
  证明: iSup_le fun p => le_sSup ⟨p.comap _ hf hf', rfl⟩

Depends on / 依赖: iSup_le, le_sSup, p.comap
-/
lemma krullDim_le_of_strictComono_and_surj
    (f : α -> β) (hf : forall ⦃a b⦄, f a < f b -> a < b) (hf' : Function.Surjective f) :
    krullDim β <= krullDim α :=
  iSup_le fun p => le_sSup ⟨p.comap _ hf hf', rfl⟩

/--
lemma `krullDim_eq_of_orderIso` / 引理 `krullDim_eq_of_orderIso`

English:
lemma krullDim_eq_of_orderIso
  given: (f : α ≃o β)
  statement: krullDim α = krullDim β
  proof: le_antisymm (krullDim_le_of_strictMono _ f.strictMono)
    krullDim_le_of_strictMono _ f.symm.strictMono

中文:
引理 krullDim_eq_of_orderIso
  条件: (f : α ≃o β)
  结论: krullDim α = krullDim β
  证明: le_antisymm (krullDim_le_of_strictMono _ f.strictMono)
    krullDim_le_of_strictMono _ f.symm.strictMono

Depends on / 依赖: f.strictMono, f.symm.strictMono, krullDim_le_of_strictMono, le_antisymm, strictMono
-/
lemma krullDim_eq_of_orderIso (f : α ≃o β) : krullDim α = krullDim β :=
le_antisymm (krullDim_le_of_strictMono _ f.strictMono)
    krullDim_le_of_strictMono _ f.symm.strictMono

/--
lemma `krullDim_orderDual` / 引理 `krullDim_orderDual`

English:
lemma krullDim_orderDual
  statement: krullDim αᵒᵈ = krullDim α
  proof: le_antisymm (iSup_le fun i => le_sSup ⟨i.reverse, rfl⟩)
    iSup_le fun i => le_sSup ⟨i.reverse, rfl⟩

中文:
引理 krullDim_orderDual
  结论: krullDim αᵒᵈ = krullDim α
  证明: le_antisymm (iSup_le fun i => le_sSup ⟨i.reverse, rfl⟩)
    iSup_le fun i => le_sSup ⟨i.reverse, rfl⟩
-/
@[simp] lemma krullDim_orderDual : krullDim αᵒᵈ = krullDim α :=
le_antisymm (iSup_le fun i => le_sSup ⟨i.reverse, rfl⟩)
    iSup_le fun i => le_sSup ⟨i.reverse, rfl⟩

/--
lemma `height_le_krullDim` / 引理 `height_le_krullDim`

English:
lemma height_le_krullDim
  given: (a : α)
  statement: height a <= krullDim α
  proof: by
  have : Nonempty α := ⟨a⟩
  rw [krullDim_eq_iSup_length]
  simp only [WithBot.coe_le_coe]
  exact height_le fun p _ => le_iSup_of_le p le_rfl

中文:
引理 height_le_krullDim
  条件: (a : α)
  结论: height a <= krullDim α
  证明: by
  have : Nonempty α := ⟨a⟩
  rw [krullDim_eq_iSup_length]
  simp only [WithBot.coe_le_coe]
  exact height_le fun p _ => le_iSup_of_le p le_rfl

Depends on / 依赖: Nonempty, WithBot, WithBot.coe_le_coe, coe_le_coe, height_le, krullDim_eq_iSup_length, le_iSup_of_le, le_rfl
-/
lemma height_le_krullDim (a : α) : height a <= krullDim α := by
  have : Nonempty α := ⟨a⟩
  rw [krullDim_eq_iSup_length]
  simp only [WithBot.coe_le_coe]
  exact height_le fun p _ => le_iSup_of_le p le_rfl

/--
lemma `coheight_le_krullDim` / 引理 `coheight_le_krullDim`

English:
lemma coheight_le_krullDim
  given: (a : α)
  statement: coheight a <= krullDim α
  proof: by
  simpa using! height_le_krullDim (α := αᵒᵈ) a

@[simp]

中文:
引理 coheight_le_krullDim
  条件: (a : α)
  结论: coheight a <= krullDim α
  证明: by
  simpa using! height_le_krullDim (α := αᵒᵈ) a

@[simp]

Depends on / 依赖: height_le_krullDim
-/
lemma coheight_le_krullDim (a : α) : coheight a <= krullDim α := by
  simpa using! height_le_krullDim (α := αᵒᵈ) a

@[simp]
/--
lemma `_root_.LTSeries.height_last_longestOf` / 引理 `_root_.LTSeries.height_last_longestOf`

English:
lemma _root_.LTSeries.height_last_longestOf
  given: [FiniteDimensionalOrder α]
  proof: by
  refine le_antisymm (height_le_krullDim _) ?_
  rw [krullDim_eq_length_of_finiteDimensionalOrder]; rw [height]
  norm_cast
exact le_iSup_iff.mpr fun _ h => iSup_le_iff.mp (h _) le_rfl

中文:
引理 _root_.LTSeries.height_last_longestOf
  条件: [FiniteDimensionalOrder α]
  证明: by
  refine le_antisymm (height_le_krullDim _) ?_
  rw [krullDim_eq_length_of_finiteDimensionalOrder]; rw [height]
  norm_cast
exact le_iSup_iff.mpr fun _ h => iSup_le_iff.mp (h _) le_rfl

Depends on / 依赖: height, height_le_krullDim, iSup_le_iff, iSup_le_iff.mp, krullDim_eq_length_of_finiteDimensionalOrder, le_antisymm, le_iSup_iff, le_iSup_iff.mpr, le_rfl
-/
lemma _root_.LTSeries.height_last_longestOf [FiniteDimensionalOrder α] :
    height (LTSeries.longestOf α).last = krullDim α := by
  refine le_antisymm (height_le_krullDim _) ?_
  rw [krullDim_eq_length_of_finiteDimensionalOrder]; rw [height]
  norm_cast
exact le_iSup_iff.mpr fun _ h => iSup_le_iff.mp (h _) le_rfl

/--
lemma `krullDim_eq_iSup_height_of_nonempty` / 引理 `krullDim_eq_iSup_height_of_nonempty`

English:
lemma krullDim_eq_iSup_height_of_nonempty
  given: [Nonempty α]
  statement: krullDim α = ↑(⨆ (a : α), height a)
  proof: by
  apply le_antisymm
  · apply iSup_le
    intro p
    suffices p.length <= ⨆ (a : α), height a from (WithBot.unbotD_le_iff fun _ => this).mp this
    apply le_iSup_of_le p.last (length_le_height_last (p := p))
  · rw [WithBot.coe_iSup (by bddDefault)]
    apply iSup_le
    apply height_le_krullDim

中文:
引理 krullDim_eq_iSup_height_of_nonempty
  条件: [非空 α]
  结论: krullDim α = ↑(⨆ (a : α), height a)
  证明: by
  apply le_antisymm
  · apply iSup_le
    intro p
    suffices p.length <= ⨆ (a : α), height a from (WithBot.unbotD_le_iff fun _ => this).mp this
    apply le_iSup_of_le p.last (length_le_height_last (p := p))
  · rw [WithBot.coe_iSup (by bddDefault)]
    apply iSup_le
    apply height_le_krullDim

Depends on / 依赖: WithBot, WithBot.coe_iSup, WithBot.unbotD_le_iff, bddDefault, coe_iSup, height, height_le_krullDim, iSup_le, le_antisymm, le_iSup_of_le, length, length_le_height_last, p.last, p.length, unbotD_le_iff
-/
lemma krullDim_eq_iSup_height_of_nonempty [Nonempty α] : krullDim α = ↑(⨆ (a : α), height a) := by
  apply le_antisymm
  · apply iSup_le
    intro p
    suffices p.length <= ⨆ (a : α), height a from (WithBot.unbotD_le_iff fun _ => this).mp this
    apply le_iSup_of_le p.last (length_le_height_last (p := p))
  · rw [WithBot.coe_iSup (by bddDefault)]
    apply iSup_le
    apply height_le_krullDim

/--
lemma `krullDim_eq_iSup_coheight_of_nonempty` / 引理 `krullDim_eq_iSup_coheight_of_nonempty`

English:
lemma krullDim_eq_iSup_coheight_of_nonempty
  given: [Nonempty α]
  proof: by
  simpa using! krullDim_eq_iSup_height_of_nonempty (α := αᵒᵈ)

中文:
引理 krullDim_eq_iSup_coheight_of_nonempty
  条件: [非空 α]
  证明: by
  simpa using! krullDim_eq_iSup_height_of_nonempty (α := αᵒᵈ)

Depends on / 依赖: krullDim_eq_iSup_height_of_nonempty
-/
lemma krullDim_eq_iSup_coheight_of_nonempty [Nonempty α] :
    krullDim α = ↑(⨆ (a : α), coheight a) := by
  simpa using! krullDim_eq_iSup_height_of_nonempty (α := αᵒᵈ)

/--
lemma `krullDim_eq_iSup_height_add_coheight_of_nonempty` / 引理 `krullDim_eq_iSup_height_add_coheight_of_nonempty`

English:
lemma krullDim_eq_iSup_height_add_coheight_of_nonempty
  given: [Nonempty α]
  proof: by
  apply le_antisymm
  · rw [krullDim_eq_iSup_height_of_nonempty, WithBot.coe_le_coe]
    apply ciSup_mono (by bddDefault) (by simp)
  · wlog hnottop : krullDim α < ⊤
    · simp_all
    rw [krullDim_eq_iSup_length]; rw [WithBot.coe_le_coe]
    apply iSup_le
    intro a
    have : height a < ⊤ := WithBot.coe_lt_coe.mp (lt_of_le_of_lt (height_le_krullDim a) hnottop)
    have : coheight a < ⊤ := WithBot.coe_lt_coe.mp (lt_of_le_of_lt (coheight_le_krullDim a) hnottop)
    cases hh : height a with
    | top => simp_all
    | coe n =>
      cases hch : coheight a with
      | top => simp_all
      | coe m =>
        obtain ⟨p₁, hlast, hlen₁⟩ := exists_series_of_height_eq_coe a hh
        obtain ⟨p₂, hhead, hlen₂⟩ := exists_series_of_coheight_eq_coe a hch
        apply le_iSup_of_le ((p₁.smash p₂) (by simp [*])) (by simp [*])

中文:
引理 krullDim_eq_iSup_height_add_coheight_of_nonempty
  条件: [非空 α]
  证明: by
  apply le_antisymm
  · rw [krullDim_eq_iSup_height_of_nonempty, WithBot.coe_le_coe]
    apply ciSup_mono (by bddDefault) (by simp)
  · wlog hnottop : krullDim α < ⊤
    · simp_all
    rw [krullDim_eq_iSup_length]; rw [WithBot.coe_le_coe]
    apply iSup_le
    intro a
    have : height a < ⊤ := WithBot.coe_lt_coe.mp (lt_of_le_of_lt (height_le_krullDim a) hnottop)
    have : coheight a < ⊤ := WithBot.coe_lt_coe.mp (lt_of_le_of_lt (coheight_le_krullDim a) hnottop)
    cases hh : height a with
    | top => simp_all
    | coe n =>
      cases hch : coheight a with
      | top => simp_all
      | coe m =>
        obtain ⟨p₁, hlast, hlen₁⟩ := exists_series_of_height_eq_coe a hh
        obtain ⟨p₂, hhead, hlen₂⟩ := exists_series_of_coheight_eq_coe a hch
        apply le_iSup_of_le ((p₁.smash p₂) (by simp [*])) (by simp [*])

Depends on / 依赖: WithBot, WithBot.coe_le_coe, WithBot.coe_lt_coe.mp, bddDefault, ciSup_mono, coe_le_coe, coe_lt_coe, coheight, coheight_le_krullDim, height, height_le_krullDim, hnottop, iSup_le, krullDim, krullDim_eq_iSup_height_of_nonempty, krullDim_eq_iSup_length, le_antisymm, lt_of_le_of_lt
-/
lemma krullDim_eq_iSup_height_add_coheight_of_nonempty [Nonempty α] :
    krullDim α = ↑(⨆ (a : α), height a + coheight a) := by
  apply le_antisymm
  · rw [krullDim_eq_iSup_height_of_nonempty, WithBot.coe_le_coe]
    apply ciSup_mono (by bddDefault) (by simp)
  · wlog hnottop : krullDim α < ⊤
    · simp_all
    rw [krullDim_eq_iSup_length]; rw [WithBot.coe_le_coe]
    apply iSup_le
    intro a
    have : height a < ⊤ := WithBot.coe_lt_coe.mp (lt_of_le_of_lt (height_le_krullDim a) hnottop)
    have : coheight a < ⊤ := WithBot.coe_lt_coe.mp (lt_of_le_of_lt (coheight_le_krullDim a) hnottop)
    cases hh : height a with
    | top => simp_all
    | coe n =>
      cases hch : coheight a with
      | top => simp_all
      | coe m =>
        obtain ⟨p₁, hlast, hlen₁⟩ := exists_series_of_height_eq_coe a hh
        obtain ⟨p₂, hhead, hlen₂⟩ := exists_series_of_coheight_eq_coe a hch
        apply le_iSup_of_le ((p₁.smash p₂) (by simp [*])) (by simp [*])

/--
lemma `krullDim_eq_iSup_height` / 引理 `krullDim_eq_iSup_height`

English:
lemma krullDim_eq_iSup_height
  statement: krullDim α = ⨆ (a : α), ↑(height a)
  proof: by
  cases isEmpty_or_nonempty α with
  | inl h => rw [krullDim_eq_bot, ciSup_of_empty]
  | inr h => rw [krullDim_eq_iSup_height_of_nonempty, WithBot.coe_iSup (OrderTop.bddAbove _)]

中文:
引理 krullDim_eq_iSup_height
  结论: krullDim α = ⨆ (a : α), ↑(height a)
  证明: by
  cases isEmpty_or_nonempty α with
  | inl h => rw [krullDim_eq_bot, ciSup_of_empty]
  | inr h => rw [krullDim_eq_iSup_height_of_nonempty, WithBot.coe_iSup (OrderTop.bddAbove _)]

Depends on / 依赖: OrderTop, OrderTop.bddAbove, WithBot, WithBot.coe_iSup, bddAbove, ciSup_of_empty, coe_iSup, isEmpty_or_nonempty, krullDim_eq_bot, krullDim_eq_iSup_height_of_nonempty
-/
lemma krullDim_eq_iSup_height : krullDim α = ⨆ (a : α), ↑(height a) := by
  cases isEmpty_or_nonempty α with
  | inl h => rw [krullDim_eq_bot, ciSup_of_empty]
  | inr h => rw [krullDim_eq_iSup_height_of_nonempty, WithBot.coe_iSup (OrderTop.bddAbove _)]

/--
lemma `krullDim_eq_iSup_coheight` / 引理 `krullDim_eq_iSup_coheight`

English:
lemma krullDim_eq_iSup_coheight
  statement: krullDim α = ⨆ (a : α), ↑(coheight a)
  proof: by
  cases isEmpty_or_nonempty α with
  | inl h => rw [krullDim_eq_bot, ciSup_of_empty]
  | inr h => rw [krullDim_eq_iSup_coheight_of_nonempty, WithBot.coe_iSup (OrderTop.bddAbove _)]

@[simp] -- not as useful as a simp lemma as it looks, due to the coe on the left

中文:
引理 krullDim_eq_iSup_coheight
  结论: krullDim α = ⨆ (a : α), ↑(coheight a)
  证明: by
  cases isEmpty_or_nonempty α with
  | inl h => rw [krullDim_eq_bot, ciSup_of_empty]
  | inr h => rw [krullDim_eq_iSup_coheight_of_nonempty, WithBot.coe_iSup (OrderTop.bddAbove _)]

@[simp] -- not as useful as a simp lemma as it looks, due to the coe on the left

Depends on / 依赖: OrderTop, OrderTop.bddAbove, WithBot, WithBot.coe_iSup, bddAbove, ciSup_of_empty, coe_iSup, isEmpty_or_nonempty, krullDim_eq_bot, krullDim_eq_iSup_coheight_of_nonempty
-/
lemma krullDim_eq_iSup_coheight : krullDim α = ⨆ (a : α), ↑(coheight a) := by
  cases isEmpty_or_nonempty α with
  | inl h => rw [krullDim_eq_bot, ciSup_of_empty]
  | inr h => rw [krullDim_eq_iSup_coheight_of_nonempty, WithBot.coe_iSup (OrderTop.bddAbove _)]

@[simp] -- not as useful as a simp lemma as it looks, due to the coe on the left
/--
lemma `height_top_eq_krullDim` / 引理 `height_top_eq_krullDim`

English:
lemma height_top_eq_krullDim
  given: [OrderTop α]
  statement: height (⊤ : α) = krullDim α
  proof: by
  rw [krullDim_eq_iSup_length]
  simp only [WithBot.coe_inj]
  apply le_antisymm
  · exact height_le fun p _ => le_iSup_of_le p le_rfl
  · exact iSup_le fun _ => length_le_height le_top

@[simp] -- not as useful as a simp lemma as it looks, due to the coe on the left

中文:
引理 height_top_eq_krullDim
  条件: [有顶序 α]
  结论: height (⊤ : α) = krullDim α
  证明: by
  rw [krullDim_eq_iSup_length]
  simp only [WithBot.coe_inj]
  apply le_antisymm
  · exact height_le fun p _ => le_iSup_of_le p le_rfl
  · exact iSup_le fun _ => length_le_height le_top

@[simp] -- not as useful as a simp lemma as it looks, due to the coe on the left

Depends on / 依赖: WithBot, WithBot.coe_inj, coe_inj, height_le, iSup_le, krullDim_eq_iSup_length, le_antisymm, le_iSup_of_le, le_rfl, le_top, length_le_height
-/
lemma height_top_eq_krullDim [OrderTop α] : height (⊤ : α) = krullDim α := by
  rw [krullDim_eq_iSup_length]
  simp only [WithBot.coe_inj]
  apply le_antisymm
  · exact height_le fun p _ => le_iSup_of_le p le_rfl
  · exact iSup_le fun _ => length_le_height le_top

@[simp] -- not as useful as a simp lemma as it looks, due to the coe on the left
/--
lemma `coheight_bot_eq_krullDim` / 引理 `coheight_bot_eq_krullDim`

English:
lemma coheight_bot_eq_krullDim
  given: [OrderBot α]
  statement: coheight (⊥ : α) = krullDim α
  proof: by
  rw [← krullDim_orderDual]
  exact height_top_eq_krullDim (α := αᵒᵈ)

中文:
引理 coheight_bot_eq_krullDim
  条件: [有底序 α]
  结论: coheight (⊥ : α) = krullDim α
  证明: by
  rw [← krullDim_orderDual]
  exact height_top_eq_krullDim (α := αᵒᵈ)

Depends on / 依赖: height_top_eq_krullDim, krullDim_orderDual
-/
lemma coheight_bot_eq_krullDim [OrderBot α] : coheight (⊥ : α) = krullDim α := by
  rw [← krullDim_orderDual]
  exact height_top_eq_krullDim (α := αᵒᵈ)

/--
lemma `height_eq_krullDim_Iic` / 引理 `height_eq_krullDim_Iic`

English:
lemma height_eq_krullDim_Iic
  given: (x : α)
  statement: (height x : Nat∞) = krullDim (Set.Iic x)
  proof: by
  rw [← height_top_eq_krullDim]; rw [height]; rw [height]; rw [WithBot.coe_inj]
  apply le_antisymm
  · apply iSup_le; intro p; apply iSup_le; intro hp
    let q := LTSeries.mk p.length (fun i => (⟨p.toFun i, le_trans (p.monotone (Fin.le_last _)) hp⟩
     : Set.Iic x)) (fun _ _ h => p.strictMono h)
    simp only [le_top, iSup_pos, ge_iff_le]
    exact le_iSup (fun p => (p.length : Nat∞)) q
  · apply iSup_le; intro p; apply iSup_le; intro _
    have mono : StrictMono (fun (y : Set.Iic x) => y.1) := fun _ _ h => h
    rw [← LTSeries.map_length p (fun x => x.1) mono, ]
    refine le_iSup₂ (f := fun p hp => (p.length : Nat∞)) (p.map (fun x => x.1) mono) ?_
    exact (p.toFun (Fin.last p.length)).2

中文:
引理 height_eq_krullDim_Iic
  条件: (x : α)
  结论: (height x : 自然数∞) = krullDim (集合.左无界右闭区间 x)
  证明: by
  rw [← height_top_eq_krullDim]; rw [height]; rw [height]; rw [WithBot.coe_inj]
  apply le_antisymm
  · apply iSup_le; intro p; apply iSup_le; intro hp
    let q := LTSeries.mk p.length (fun i => (⟨p.toFun i, le_trans (p.monotone (Fin.le_last _)) hp⟩
     : Set.Iic x)) (fun _ _ h => p.strictMono h)
    simp only [le_top, iSup_pos, ge_iff_le]
    exact le_iSup (fun p => (p.length : Nat∞)) q
  · apply iSup_le; intro p; apply iSup_le; intro _
    have mono : StrictMono (fun (y : Set.Iic x) => y.1) := fun _ _ h => h
    rw [← LTSeries.map_length p (fun x => x.1) mono, ]
    refine le_iSup₂ (f := fun p hp => (p.length : Nat∞)) (p.map (fun x => x.1) mono) ?_
    exact (p.toFun (Fin.last p.length)).2

Depends on / 依赖: Fin.le_last, LTSeries, LTSeries.mk, Set.Iic, StrictMono, WithBot, WithBot.coe_inj, coe_inj, ge_iff_le, height, height_top_eq_krullDim, iSup_le, iSup_pos, le_antisymm, le_iSup, le_last, le_top, le_trans, length, monotone
-/
lemma height_eq_krullDim_Iic (x : α) : (height x : Nat∞) = krullDim (Set.Iic x) := by
  rw [← height_top_eq_krullDim]; rw [height]; rw [height]; rw [WithBot.coe_inj]
  apply le_antisymm
  · apply iSup_le; intro p; apply iSup_le; intro hp
    let q := LTSeries.mk p.length (fun i => (⟨p.toFun i, le_trans (p.monotone (Fin.le_last _)) hp⟩
     : Set.Iic x)) (fun _ _ h => p.strictMono h)
    simp only [le_top, iSup_pos, ge_iff_le]
    exact le_iSup (fun p => (p.length : Nat∞)) q
  · apply iSup_le; intro p; apply iSup_le; intro _
    have mono : StrictMono (fun (y : Set.Iic x) => y.1) := fun _ _ h => h
    rw [← LTSeries.map_length p (fun x => x.1) mono, ]
    refine le_iSup₂ (f := fun p hp => (p.length : Nat∞)) (p.map (fun x => x.1) mono) ?_
    exact (p.toFun (Fin.last p.length)).2

/--
lemma `coheight_eq_krullDim_Ici` / 引理 `coheight_eq_krullDim_Ici`

English:
lemma coheight_eq_krullDim_Ici
  given: {α : Type*} [Preorder α] (x : α)
  proof: by
  rw [coheight]; rw [← krullDim_orderDual]; rw [Order.krullDim_eq_of_orderIso (OrderIso.refl _)]
  exact height_eq_krullDim_Iic _

中文:
引理 coheight_eq_krullDim_Ici
  条件: {α : 类型} [预序 α] (x : α)
  证明: by
  rw [coheight]; rw [← krullDim_orderDual]; rw [Order.krullDim_eq_of_orderIso (OrderIso.refl _)]
  exact height_eq_krullDim_Iic _

Depends on / 依赖: Order.krullDim_eq_of_orderIso, OrderIso, OrderIso.refl, coheight, height_eq_krullDim_Iic, krullDim_eq_of_orderIso, krullDim_orderDual
-/
lemma coheight_eq_krullDim_Ici {α : Type*} [Preorder α] (x : α) :
    (coheight x : Nat∞) = krullDim (Set.Ici x) := by
  rw [coheight]; rw [← krullDim_orderDual]; rw [Order.krullDim_eq_of_orderIso (OrderIso.refl _)]
  exact height_eq_krullDim_Iic _

end krullDim

section finiteDimensional

variable {α : Type*} [Preorder α]

/--
lemma `finiteDimensionalOrder_iff_krullDim_ne_bot_and_top` / 引理 `finiteDimensionalOrder_iff_krullDim_ne_bot_and_top`

English:
lemma finiteDimensionalOrder_iff_krullDim_ne_bot_and_top
  proof: by
  by_cases h : Nonempty α
  · simp [← not_infiniteDimensionalOrder_iff, ← krullDim_eq_top_iff]
  · constructor
    · exact (fun h1 => False.elim (h (LTSeries.nonempty_of_finiteDimensionalOrder α)))
    · exact (fun h1 => False.elim (h1.1 (krullDim_eq_bot_iff.mpr (not_nonempty_iff.mp h))))

中文:
引理 finiteDimensionalOrder_iff_krullDim_ne_bot_and_top
  证明: by
  by_cases h : Nonempty α
  · simp [← not_infiniteDimensionalOrder_iff, ← krullDim_eq_top_iff]
  · constructor
    · exact (fun h1 => False.elim (h (LTSeries.nonempty_of_finiteDimensionalOrder α)))
    · exact (fun h1 => False.elim (h1.1 (krullDim_eq_bot_iff.mpr (not_nonempty_iff.mp h))))

Depends on / 依赖: False.elim, LTSeries, LTSeries.nonempty_of_finiteDimensionalOrder, Nonempty, krullDim_eq_bot_iff, krullDim_eq_bot_iff.mpr, krullDim_eq_top_iff, nonempty_of_finiteDimensionalOrder, not_infiniteDimensionalOrder_iff, not_nonempty_iff, not_nonempty_iff.mp
-/
lemma finiteDimensionalOrder_iff_krullDim_ne_bot_and_top :
    FiniteDimensionalOrder α ↔ krullDim α != ⊥ ∧ krullDim α != ⊤ := by
  by_cases h : Nonempty α
  · simp [← not_infiniteDimensionalOrder_iff, ← krullDim_eq_top_iff]
  · constructor
    · exact (fun h1 => False.elim (h (LTSeries.nonempty_of_finiteDimensionalOrder α)))
    · exact (fun h1 => False.elim (h1.1 (krullDim_eq_bot_iff.mpr (not_nonempty_iff.mp h))))

/--
lemma `krullDim_ne_bot_of_finiteDimensionalOrder` / 引理 `krullDim_ne_bot_of_finiteDimensionalOrder`

English:
lemma krullDim_ne_bot_of_finiteDimensionalOrder
  given: [FiniteDimensionalOrder α]
  statement: krullDim α != ⊥
  proof: (finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mp ‹_›).1

中文:
引理 krullDim_ne_bot_of_finiteDimensionalOrder
  条件: [FiniteDimensionalOrder α]
  结论: krullDim α != ⊥
  证明: (finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mp ‹_›).1

Depends on / 依赖: finiteDimensionalOrder_iff_krullDim_ne_bot_and_top, finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mp
-/
lemma krullDim_ne_bot_of_finiteDimensionalOrder [FiniteDimensionalOrder α] : krullDim α != ⊥ :=
  (finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mp ‹_›).1

/--
lemma `krullDim_ne_top_of_finiteDimensionalOrder` / 引理 `krullDim_ne_top_of_finiteDimensionalOrder`

English:
lemma krullDim_ne_top_of_finiteDimensionalOrder
  given: [FiniteDimensionalOrder α]
  statement: krullDim α != ⊤
  proof: (finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mp ‹_›).2

中文:
引理 krullDim_ne_top_of_finiteDimensionalOrder
  条件: [FiniteDimensionalOrder α]
  结论: krullDim α != ⊤
  证明: (finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mp ‹_›).2

Depends on / 依赖: finiteDimensionalOrder_iff_krullDim_ne_bot_and_top, finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mp
-/
lemma krullDim_ne_top_of_finiteDimensionalOrder [FiniteDimensionalOrder α] : krullDim α != ⊤ :=
  (finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mp ‹_›).2

/--
lemma `coheight_lt_top` / 引理 `coheight_lt_top`

English:
lemma coheight_lt_top
  given: [FiniteDimensionalOrder α] (x : α)
  statement: coheight x < ⊤
  proof: by
  rw [← WithBot.coe_lt_coe]
  apply lt_of_le_of_lt (coheight_le_krullDim x)
  simpa using krullDim_ne_top_of_finiteDimensionalOrder.lt_top

中文:
引理 coheight_lt_top
  条件: [FiniteDimensionalOrder α] (x : α)
  结论: coheight x < ⊤
  证明: by
  rw [← WithBot.coe_lt_coe]
  apply lt_of_le_of_lt (coheight_le_krullDim x)
  simpa using krullDim_ne_top_of_finiteDimensionalOrder.lt_top

Depends on / 依赖: WithBot, WithBot.coe_lt_coe, coe_lt_coe, coheight_le_krullDim, krullDim_ne_top_of_finiteDimensionalOrder, krullDim_ne_top_of_finiteDimensionalOrder.lt_top, lt_of_le_of_lt, lt_top
-/
lemma coheight_lt_top [FiniteDimensionalOrder α] (x : α) : coheight x < ⊤ := by
  rw [← WithBot.coe_lt_coe]
  apply lt_of_le_of_lt (coheight_le_krullDim x)
  simpa using krullDim_ne_top_of_finiteDimensionalOrder.lt_top

end finiteDimensional

section typeclass

/-- Typeclass for orders with krull dimension at most `n`. -/
@[mk_iff]
/--
Definition of `KrullDimLE` / `KrullDimLE` 的定义

English:
class KrullDimLE
  parameters: (n : Nat) (α : Type*) [Preorder α]
  axioms and operations (1):
    - krullDim_le : krullDim α <= n

中文:
类 Krull维数不超过
  参数: (n : 自然数) (α : 类型) [预序 α]
  公理与运算 (1 个):
    - krullDim_le : krullDim α <= n
-/
class KrullDimLE (n : Nat) (α : Type*) [Preorder α] : Prop where
  krullDim_le : krullDim α <= n

/--
lemma `KrullDimLE.mono` / 引理 `KrullDimLE.mono`

English:
lemma KrullDimLE.mono
  given: {n m : Nat} (e : n <= m) (α : Type*) [Preorder α] [KrullDimLE n α]
  proof: ⟨KrullDimLE.krullDim_le (n := n).trans (Nat.cast_le.mpr e)⟩

中文:
引理 Krull维数不超过.mono
  条件: {n m : 自然数} (e : n <= m) (α : 类型) [预序 α] [Krull维数不超过 n α]
  证明: ⟨KrullDimLE.krullDim_le (n := n).trans (Nat.cast_le.mpr e)⟩

Depends on / 依赖: KrullDimLE, KrullDimLE.krullDim_le, Nat.cast_le.mpr, cast_le, krullDim_le
-/
lemma KrullDimLE.mono {n m : Nat} (e : n <= m) (α : Type*) [Preorder α] [KrullDimLE n α] :
    KrullDimLE m α :=
  ⟨KrullDimLE.krullDim_le (n := n).trans (Nat.cast_le.mpr e)⟩

instance {α} [Preorder α] [Subsingleton α] : KrullDimLE 0 α := ⟨krullDim_nonpos_of_subsingleton⟩

end typeclass

/-!
## Concrete calculations
-/

section calculations

/--
lemma `krullDim_eq_one_iff_of_boundedOrder` / 引理 `krullDim_eq_one_iff_of_boundedOrder`

English:
lemma krullDim_eq_one_iff_of_boundedOrder
  given: {α : Type*} [PartialOrder α] [BoundedOrder α]
  proof: by
  rw [le_antisymm_iff]; rw [krullDim_le_one_iff_of_boundedOrder]; rw [WithBot.one_le_iff_pos]; rw [Order.krullDim_pos_iff_of_orderBot]; rw [isSimpleOrder_iff]; rw [and_comm]

中文:
引理 krullDim_eq_one_iff_of_boundedOrder
  条件: {α : 类型} [偏序 α] [有界序 α]
  证明: by
  rw [le_antisymm_iff]; rw [krullDim_le_one_iff_of_boundedOrder]; rw [WithBot.one_le_iff_pos]; rw [Order.krullDim_pos_iff_of_orderBot]; rw [isSimpleOrder_iff]; rw [and_comm]

Depends on / 依赖: Order.krullDim_pos_iff_of_orderBot, WithBot, WithBot.one_le_iff_pos, and_comm, isSimpleOrder_iff, krullDim_le_one_iff_of_boundedOrder, krullDim_pos_iff_of_orderBot, le_antisymm_iff, one_le_iff_pos
-/
lemma krullDim_eq_one_iff_of_boundedOrder {α : Type*} [PartialOrder α] [BoundedOrder α] :
    krullDim α = 1 ↔ IsSimpleOrder α := by
  rw [le_antisymm_iff]; rw [krullDim_le_one_iff_of_boundedOrder]; rw [WithBot.one_le_iff_pos]; rw [Order.krullDim_pos_iff_of_orderBot]; rw [isSimpleOrder_iff]; rw [and_comm]

/--
lemma `krullDim_of_isSimpleOrder` / 引理 `krullDim_of_isSimpleOrder`

English:
lemma krullDim_of_isSimpleOrder
  statement: {α : Type*} [PartialOrder α] [BoundedOrder α]
  proof: krullDim_eq_one_iff_of_boundedOrder.mpr ‹_›

中文:
引理 krullDim_of_isSimpleOrder
  结论: {α : 类型} [偏序 α] [有界序 α]
  证明: krullDim_eq_one_iff_of_boundedOrder.mpr ‹_›
-/
@[simp] lemma krullDim_of_isSimpleOrder {α : Type*} [PartialOrder α] [BoundedOrder α]
    [IsSimpleOrder α] : krullDim α = 1 :=
  krullDim_eq_one_iff_of_boundedOrder.mpr ‹_›

variable {α : Type*} [Preorder α]


/--
lemma `height_nat` / 引理 `height_nat`

English:
lemma height_nat
  given: (n : Nat)
  statement: height n = n
  proof: by
  induction n using Nat.strongRecOn with | ind n ih =>
  apply le_antisymm
  · apply height_le_coe_iff.mpr
    simp +contextual only [ih, Nat.cast_lt, implies_true]
  · exact length_le_height_last (p := LTSeries.range n)

中文:
引理 height_nat
  条件: (n : 自然数)
  结论: height n = n
  证明: by
  induction n using Nat.strongRecOn with | ind n ih =>
  apply le_antisymm
  · apply height_le_coe_iff.mpr
    simp +contextual only [ih, Nat.cast_lt, implies_true]
  · exact length_le_height_last (p := LTSeries.range n)
-/
@[simp] lemma height_nat (n : Nat) : height n = n := by
  induction n using Nat.strongRecOn with | ind n ih =>
  apply le_antisymm
  · apply height_le_coe_iff.mpr
    simp +contextual only [ih, Nat.cast_lt, implies_true]
  · exact length_le_height_last (p := LTSeries.range n)

/--
lemma `coheight_of_noMaxOrder` / 引理 `coheight_of_noMaxOrder`

English:
lemma coheight_of_noMaxOrder
  given: [NoMaxOrder α] (a : α)
  statement: coheight a = ⊤
  proof: by
  obtain ⟨f, hstrictmono⟩ := Nat.exists_strictMono ↑(Set.Ioi a)
  apply coheight_eq_top_iff.mpr
  intro m
  use { length := m, toFun := fun i => if i = 0 then a else f i, step := ?step }
  case h => simp [RelSeries.head]
  case step =>
    intro ⟨i, hi⟩
    by_cases hzero : i = 0
    · subst i
      exact (f 1).prop
    · suffices f i < f (i + 1) by simp [Fin.ext_iff, hzero, this]
      apply hstrictmono
      lia

中文:
引理 coheight_of_noMaxOrder
  条件: [NoMax序 α] (a : α)
  结论: coheight a = ⊤
  证明: by
  obtain ⟨f, hstrictmono⟩ := Nat.exists_strictMono ↑(Set.Ioi a)
  apply coheight_eq_top_iff.mpr
  intro m
  use { length := m, toFun := fun i => if i = 0 then a else f i, step := ?step }
  case h => simp [RelSeries.head]
  case step =>
    intro ⟨i, hi⟩
    by_cases hzero : i = 0
    · subst i
      exact (f 1).prop
    · suffices f i < f (i + 1) by simp [Fin.ext_iff, hzero, this]
      apply hstrictmono
      lia
-/
@[simp] lemma coheight_of_noMaxOrder [NoMaxOrder α] (a : α) : coheight a = ⊤ := by
  obtain ⟨f, hstrictmono⟩ := Nat.exists_strictMono ↑(Set.Ioi a)
  apply coheight_eq_top_iff.mpr
  intro m
  use { length := m, toFun := fun i => if i = 0 then a else f i, step := ?step }
  case h => simp [RelSeries.head]
  case step =>
    intro ⟨i, hi⟩
    by_cases hzero : i = 0
    · subst i
      exact (f 1).prop
    · suffices f i < f (i + 1) by simp [Fin.ext_iff, hzero, this]
      apply hstrictmono
      lia

/--
lemma `height_of_noMinOrder` / 引理 `height_of_noMinOrder`

English:
lemma height_of_noMinOrder
  given: [NoMinOrder α] (a : α)
  statement: height a = ⊤
  proof: -- Implementation note: Here it's a bit easier to define the coheight variant first
  coheight_of_noMaxOrder (α := αᵒᵈ) a

中文:
引理 height_of_noMinOrder
  条件: [NoMin序 α] (a : α)
  结论: height a = ⊤
  证明: -- Implementation note: Here it's a bit easier to define the coheight variant first
  coheight_of_noMaxOrder (α := αᵒᵈ) a
-/
@[simp] lemma height_of_noMinOrder [NoMinOrder α] (a : α) : height a = ⊤ :=
  -- Implementation note: Here it's a bit easier to define the coheight variant first
  coheight_of_noMaxOrder (α := αᵒᵈ) a

/--
lemma `krullDim_of_noMaxOrder` / 引理 `krullDim_of_noMaxOrder`

English:
lemma krullDim_of_noMaxOrder
  given: [Nonempty α] [NoMaxOrder α]
  statement: krullDim α = ⊤
  proof: by
  simp [krullDim_eq_iSup_coheight, coheight_of_noMaxOrder]

中文:
引理 krullDim_of_noMaxOrder
  条件: [非空 α] [NoMax序 α]
  结论: krullDim α = ⊤
  证明: by
  simp [krullDim_eq_iSup_coheight, coheight_of_noMaxOrder]
-/
@[simp] lemma krullDim_of_noMaxOrder [Nonempty α] [NoMaxOrder α] : krullDim α = ⊤ := by
  simp [krullDim_eq_iSup_coheight, coheight_of_noMaxOrder]

/--
lemma `krullDim_of_noMinOrder` / 引理 `krullDim_of_noMinOrder`

English:
lemma krullDim_of_noMinOrder
  given: [Nonempty α] [NoMinOrder α]
  statement: krullDim α = ⊤
  proof: by
  simp [krullDim_eq_iSup_height, height_of_noMinOrder]

中文:
引理 krullDim_of_noMinOrder
  条件: [非空 α] [NoMin序 α]
  结论: krullDim α = ⊤
  证明: by
  simp [krullDim_eq_iSup_height, height_of_noMinOrder]
-/
@[simp] lemma krullDim_of_noMinOrder [Nonempty α] [NoMinOrder α] : krullDim α = ⊤ := by
  simp [krullDim_eq_iSup_height, height_of_noMinOrder]

/--
lemma `coheight_nat` / 引理 `coheight_nat`

English:
lemma coheight_nat
  given: (n : Nat)
  statement: coheight n = ⊤
  proof: coheight_of_noMaxOrder ..

中文:
引理 coheight_nat
  条件: (n : 自然数)
  结论: coheight n = ⊤
  证明: coheight_of_noMaxOrder ..

Depends on / 依赖: coheight_of_noMaxOrder
-/
lemma coheight_nat (n : Nat) : coheight n = ⊤ := coheight_of_noMaxOrder ..

/--
lemma `krullDim_nat` / 引理 `krullDim_nat`

English:
lemma krullDim_nat
  statement: krullDim Nat = ⊤
  proof: krullDim_of_noMaxOrder ..

中文:
引理 krullDim_nat
  结论: krullDim 自然数 = ⊤
  证明: krullDim_of_noMaxOrder ..

Depends on / 依赖: krullDim_of_noMaxOrder
-/
lemma krullDim_nat : krullDim Nat = ⊤ := krullDim_of_noMaxOrder ..

/--
lemma `height_int` / 引理 `height_int`

English:
lemma height_int
  given: (n : Int)
  statement: height n = ⊤
  proof: height_of_noMinOrder ..

中文:
引理 height_int
  条件: (n : 整数)
  结论: height n = ⊤
  证明: height_of_noMinOrder ..

Depends on / 依赖: height_of_noMinOrder
-/
lemma height_int (n : Int) : height n = ⊤ := height_of_noMinOrder ..

/--
lemma `coheight_int` / 引理 `coheight_int`

English:
lemma coheight_int
  given: (n : Int)
  statement: coheight n = ⊤
  proof: coheight_of_noMaxOrder ..

中文:
引理 coheight_int
  条件: (n : 整数)
  结论: coheight n = ⊤
  证明: coheight_of_noMaxOrder ..

Depends on / 依赖: coheight_of_noMaxOrder
-/
lemma coheight_int (n : Int) : coheight n = ⊤ := coheight_of_noMaxOrder ..

/--
lemma `krullDim_int` / 引理 `krullDim_int`

English:
lemma krullDim_int
  statement: krullDim Int = ⊤
  proof: krullDim_of_noMaxOrder ..

中文:
引理 krullDim_int
  结论: krullDim 整数 = ⊤
  证明: krullDim_of_noMaxOrder ..

Depends on / 依赖: krullDim_of_noMaxOrder
-/
lemma krullDim_int : krullDim Int = ⊤ := krullDim_of_noMaxOrder ..

set_option backward.isDefEq.respectTransparency false in
/--
lemma `height_coe_withBot` / 引理 `height_coe_withBot`

English:
lemma height_coe_withBot
  given: (x : α)
  statement: height (x : WithBot α) = height x + 1
  proof: by
  apply le_antisymm
  · apply height_le
    intro p hlast
    wlog hlenpos : p.length != 0
    · simp_all
    -- essentially p' := (p.drop 1).map unbot
    let p' : LTSeries α := {
      length := p.length - 1
      toFun := fun ⟨i, hi⟩ => (p ⟨i+1, by lia⟩).unbot (by
        apply ne_bot_of_gt (b := p.head)
        apply p.strictMono
        exact compare_gt_iff_gt.mp rfl)
      step := fun i => by simpa [WithBot.unbot_lt_iff] using! p.step ⟨i + 1, by lia⟩ }
    have hlast' : p'.last = x := by
      simp only [p', RelSeries.last, WithBot.unbot_eq_iff, ← hlast, Fin.last]
      congr
      lia
    suffices p'.length <= height p'.last by
      simpa [p', hlast'] using! this
    apply length_le_height_last
  · rw [height_add_const]
    apply iSup₂_le
    intro p hlast
    let p' := (p.map _ WithBot.coe_strictMono).cons ⊥ (by simp)
    apply le_iSup₂_of_le p' (by simp [p', hlast]) (by simp [p'])

中文:
引理 height_coe_withBot
  条件: (x : α)
  结论: height (x : WithBot α) = height x + 1
  证明: by
  apply le_antisymm
  · apply height_le
    intro p hlast
    wlog hlenpos : p.length != 0
    · simp_all
    -- essentially p' := (p.drop 1).map unbot
    let p' : LTSeries α := {
      length := p.length - 1
      toFun := fun ⟨i, hi⟩ => (p ⟨i+1, by lia⟩).unbot (by
        apply ne_bot_of_gt (b := p.head)
        apply p.strictMono
        exact compare_gt_iff_gt.mp rfl)
      step := fun i => by simpa [WithBot.unbot_lt_iff] using! p.step ⟨i + 1, by lia⟩ }
    have hlast' : p'.last = x := by
      simp only [p', RelSeries.last, WithBot.unbot_eq_iff, ← hlast, Fin.last]
      congr
      lia
    suffices p'.length <= height p'.last by
      simpa [p', hlast'] using! this
    apply length_le_height_last
  · rw [height_add_const]
    apply iSup₂_le
    intro p hlast
    let p' := (p.map _ WithBot.coe_strictMono).cons ⊥ (by simp)
    apply le_iSup₂_of_le p' (by simp [p', hlast]) (by simp [p'])
-/
@[simp] lemma height_coe_withBot (x : α) : height (x : WithBot α) = height x + 1 := by
  apply le_antisymm
  · apply height_le
    intro p hlast
    wlog hlenpos : p.length != 0
    · simp_all
    -- essentially p' := (p.drop 1).map unbot
    let p' : LTSeries α := {
      length := p.length - 1
      toFun := fun ⟨i, hi⟩ => (p ⟨i+1, by lia⟩).unbot (by
        apply ne_bot_of_gt (b := p.head)
        apply p.strictMono
        exact compare_gt_iff_gt.mp rfl)
      step := fun i => by simpa [WithBot.unbot_lt_iff] using! p.step ⟨i + 1, by lia⟩ }
    have hlast' : p'.last = x := by
      simp only [p', RelSeries.last, WithBot.unbot_eq_iff, ← hlast, Fin.last]
      congr
      lia
    suffices p'.length <= height p'.last by
      simpa [p', hlast'] using! this
    apply length_le_height_last
  · rw [height_add_const]
    apply iSup₂_le
    intro p hlast
    let p' := (p.map _ WithBot.coe_strictMono).cons ⊥ (by simp)
    apply le_iSup₂_of_le p' (by simp [p', hlast]) (by simp [p'])

/--
lemma `coheight_coe_withTop` / 引理 `coheight_coe_withTop`

English:
lemma coheight_coe_withTop
  given: (x : α)
  statement: coheight (x : WithTop α) = coheight x + 1
  proof: height_coe_withBot (α := αᵒᵈ) x

中文:
引理 coheight_coe_withTop
  条件: (x : α)
  结论: coheight (x : WithTop α) = coheight x + 1
  证明: height_coe_withBot (α := αᵒᵈ) x
-/
@[simp] lemma coheight_coe_withTop (x : α) : coheight (x : WithTop α) = coheight x + 1 :=
  height_coe_withBot (α := αᵒᵈ) x

/--
lemma `height_coe_withTop` / 引理 `height_coe_withTop`

English:
lemma height_coe_withTop
  given: (x : α)
  statement: height (x : WithTop α) = height x
  proof: by
  apply le_antisymm
  · apply height_le
    intro p hlast
    -- essentially p' := p.map untop
    let p' : LTSeries α := {
      length := p.length
      toFun := fun i => (p i).untop (by
        apply WithTop.lt_top_iff_ne_top.mp
        apply lt_of_le_of_lt
        · exact p.monotone (Fin.le_last _)
        · rw [RelSeries.last] at hlast
          simp [hlast])
      step := fun i => by simpa [WithTop.untop_lt_iff, WithTop.coe_untop] using p.step i }
    have hlast' : p'.last = x := by
      simp only [p', RelSeries.last, WithTop.untop_eq_iff, ← hlast]
    suffices p'.length <= height p'.last by
      rw [hlast'] at this
      simpa [p'] using this
    apply length_le_height_last
  · apply height_le
    intro p hlast
    let p' := p.map _ WithTop.coe_strictMono
    apply le_iSup₂_of_le p' (by simp [p', hlast]) (by simp [p'])

中文:
引理 height_coe_withTop
  条件: (x : α)
  结论: height (x : WithTop α) = height x
  证明: by
  apply le_antisymm
  · apply height_le
    intro p hlast
    -- essentially p' := p.map untop
    let p' : LTSeries α := {
      length := p.length
      toFun := fun i => (p i).untop (by
        apply WithTop.lt_top_iff_ne_top.mp
        apply lt_of_le_of_lt
        · exact p.monotone (Fin.le_last _)
        · rw [RelSeries.last] at hlast
          simp [hlast])
      step := fun i => by simpa [WithTop.untop_lt_iff, WithTop.coe_untop] using p.step i }
    have hlast' : p'.last = x := by
      simp only [p', RelSeries.last, WithTop.untop_eq_iff, ← hlast]
    suffices p'.length <= height p'.last by
      rw [hlast'] at this
      simpa [p'] using this
    apply length_le_height_last
  · apply height_le
    intro p hlast
    let p' := p.map _ WithTop.coe_strictMono
    apply le_iSup₂_of_le p' (by simp [p', hlast]) (by simp [p'])
-/
@[simp] lemma height_coe_withTop (x : α) : height (x : WithTop α) = height x := by
  apply le_antisymm
  · apply height_le
    intro p hlast
    -- essentially p' := p.map untop
    let p' : LTSeries α := {
      length := p.length
      toFun := fun i => (p i).untop (by
        apply WithTop.lt_top_iff_ne_top.mp
        apply lt_of_le_of_lt
        · exact p.monotone (Fin.le_last _)
        · rw [RelSeries.last] at hlast
          simp [hlast])
      step := fun i => by simpa [WithTop.untop_lt_iff, WithTop.coe_untop] using p.step i }
    have hlast' : p'.last = x := by
      simp only [p', RelSeries.last, WithTop.untop_eq_iff, ← hlast]
    suffices p'.length <= height p'.last by
      rw [hlast'] at this
      simpa [p'] using this
    apply length_le_height_last
  · apply height_le
    intro p hlast
    let p' := p.map _ WithTop.coe_strictMono
    apply le_iSup₂_of_le p' (by simp [p', hlast]) (by simp [p'])

/--
lemma `coheight_coe_withBot` / 引理 `coheight_coe_withBot`

English:
lemma coheight_coe_withBot
  given: (x : α)
  statement: coheight (x : WithBot α) = coheight x
  proof: height_coe_withTop (α := αᵒᵈ) x

中文:
引理 coheight_coe_withBot
  条件: (x : α)
  结论: coheight (x : WithBot α) = coheight x
  证明: height_coe_withTop (α := αᵒᵈ) x
-/
@[simp] lemma coheight_coe_withBot (x : α) : coheight (x : WithBot α) = coheight x :=
  height_coe_withTop (α := αᵒᵈ) x

/--
lemma `krullDim_WithTop` / 引理 `krullDim_WithTop`

English:
lemma krullDim_WithTop
  given: [Nonempty α]
  statement: krullDim (WithTop α) = krullDim α + 1
  proof: by
  rw [← height_top_eq_krullDim]; rw [krullDim_eq_iSup_height_of_nonempty]; rw [height_eq_iSup_lt_height]
  norm_cast
  simp_rw [WithTop.lt_top_iff_ne_top]
  rw [ENat.iSup_add]; rw [iSup_subtype']
  symm
  apply Equiv.withTopSubtypeNe.symm.iSup_congr
  simp

中文:
引理 krullDim_WithTop
  条件: [非空 α]
  结论: krullDim (WithTop α) = krullDim α + 1
  证明: by
  rw [← height_top_eq_krullDim]; rw [krullDim_eq_iSup_height_of_nonempty]; rw [height_eq_iSup_lt_height]
  norm_cast
  simp_rw [WithTop.lt_top_iff_ne_top]
  rw [ENat.iSup_add]; rw [iSup_subtype']
  symm
  apply Equiv.withTopSubtypeNe.symm.iSup_congr
  simp
-/
@[simp] lemma krullDim_WithTop [Nonempty α] : krullDim (WithTop α) = krullDim α + 1 := by
  rw [← height_top_eq_krullDim]; rw [krullDim_eq_iSup_height_of_nonempty]; rw [height_eq_iSup_lt_height]
  norm_cast
  simp_rw [WithTop.lt_top_iff_ne_top]
  rw [ENat.iSup_add]; rw [iSup_subtype']
  symm
  apply Equiv.withTopSubtypeNe.symm.iSup_congr
  simp

/--
lemma `krullDim_withBot` / 引理 `krullDim_withBot`

English:
lemma krullDim_withBot
  given: [Nonempty α]
  statement: krullDim (WithBot α) = krullDim α + 1
  proof: by
  conv_lhs => rw [← krullDim_orderDual]
  conv_rhs => rw [← krullDim_orderDual]
  exact krullDim_WithTop (α := αᵒᵈ)

@[simp]

中文:
引理 krullDim_withBot
  条件: [非空 α]
  结论: krullDim (WithBot α) = krullDim α + 1
  证明: by
  conv_lhs => rw [← krullDim_orderDual]
  conv_rhs => rw [← krullDim_orderDual]
  exact krullDim_WithTop (α := αᵒᵈ)

@[simp]
-/
@[simp] lemma krullDim_withBot [Nonempty α] : krullDim (WithBot α) = krullDim α + 1 := by
  conv_lhs => rw [← krullDim_orderDual]
  conv_rhs => rw [← krullDim_orderDual]
  exact krullDim_WithTop (α := αᵒᵈ)

@[simp]
/--
lemma `krullDim_enat` / 引理 `krullDim_enat`

English:
lemma krullDim_enat
  statement: krullDim Nat∞ = ⊤
  proof: by
  change (krullDim (WithTop Nat) = ⊤)
  simp [← WithBot.coe_top, ← WithBot.coe_one, ← WithBot.coe_add]

@[simp]

中文:
引理 krullDim_enat
  结论: krullDim 自然数∞ = ⊤
  证明: by
  change (krullDim (WithTop Nat) = ⊤)
  simp [← WithBot.coe_top, ← WithBot.coe_one, ← WithBot.coe_add]

@[simp]

Depends on / 依赖: WithBot, WithBot.coe_add, WithBot.coe_one, WithBot.coe_top, WithTop, coe_add, coe_one, coe_top, krullDim
-/
lemma krullDim_enat : krullDim Nat∞ = ⊤ := by
  change (krullDim (WithTop Nat) = ⊤)
  simp [← WithBot.coe_top, ← WithBot.coe_one, ← WithBot.coe_add]

@[simp]
/--
lemma `height_enat` / 引理 `height_enat`

English:
lemma height_enat
  given: (n : Nat∞)
  statement: height n = n
  proof: by
  cases n with
  | top => simp only [← WithBot.coe_eq_coe, height_top_eq_krullDim, krullDim_enat, WithBot.coe_top]
  | coe n => exact (height_coe_withTop _).trans (height_nat _)

@[simp]

中文:
引理 height_enat
  条件: (n : 自然数∞)
  结论: height n = n
  证明: by
  cases n with
  | top => simp only [← WithBot.coe_eq_coe, height_top_eq_krullDim, krullDim_enat, WithBot.coe_top]
  | coe n => exact (height_coe_withTop _).trans (height_nat _)

@[simp]

Depends on / 依赖: WithBot, WithBot.coe_eq_coe, WithBot.coe_top, coe_eq_coe, coe_top, height_coe_withTop, height_nat, height_top_eq_krullDim, krullDim_enat
-/
lemma height_enat (n : Nat∞) : height n = n := by
  cases n with
  | top => simp only [← WithBot.coe_eq_coe, height_top_eq_krullDim, krullDim_enat, WithBot.coe_top]
  | coe n => exact (height_coe_withTop _).trans (height_nat _)

@[simp]
/--
lemma `coheight_coe_enat` / 引理 `coheight_coe_enat`

English:
lemma coheight_coe_enat
  given: (n : Nat)
  statement: coheight (n : Nat∞) = ⊤
  proof: by
  apply (coheight_coe_withTop _).trans
  simp only [coheight_nat, top_add]

中文:
引理 coheight_coe_enat
  条件: (n : 自然数)
  结论: coheight (n : 自然数∞) = ⊤
  证明: by
  apply (coheight_coe_withTop _).trans
  simp only [coheight_nat, top_add]

Depends on / 依赖: coheight_coe_withTop, coheight_nat, top_add
-/
lemma coheight_coe_enat (n : Nat) : coheight (n : Nat∞) = ⊤ := by
  apply (coheight_coe_withTop _).trans
  simp only [coheight_nat, top_add]

end calculations

section orderHom

variable {α β : Type*} [Preorder α] [PartialOrder β]
variable {m : Nat} (f : α ->o β) (h : forall (x : β), Order.krullDim (f ⁻¹' {x}) <= m)

include h in
/--
lemma `height_le_of_krullDim_preimage_le` / 引理 `height_le_of_krullDim_preimage_le`

English:
lemma height_le_of_krullDim_preimage_le
  given: (x : α)
  proof: by
  generalize h' : Order.height (f x) = n
  cases n with | top => simp | coe n =>
    induction n using Nat.strong_induction_on generalizing x with | h n ih =>
    refine height_le_iff.mpr fun p hp => le_of_not_gt fun h_len => ?_
    let i : Fin (p.length + 1) := ⟨p.length - (m + 1), Nat.sub_lt_succ p.length _⟩
    suffices h'' : f (p i) < f x by
      obtain ⟨n', hn'⟩ : exists (n' : Nat), n' = height (f (p i)) := ENat.ne_top_iff_exists.mp
        ((height_mono h''.le).trans_lt (h' ▸ ENat.natCast_lt_top _)).ne
      have h_lt : n' < n := ENat.natCast_lt_natCast.mp
        (h' ▸ hn' ▸ height_strictMono h'' (hn' ▸ ENat.natCast_lt_top _))
have := (length_le_height_last (p := p.take i)).trans ih n' h_lt (p i) hn'.symm
      rw [RelSeries.take_length]; rw [ENat.natCast_sub]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [tsub_le_iff_right]; rw [add_assoc]; rw [add_comm _ (_ + 1)]; rw [← add_assoc]; rw [← mul_add_one] at this
      refine not_lt_of_ge ?_ (h_len.trans_le this)
      gcongr
      rwa [← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_le_natCast]
    refine (f.monotone ((p.monotone (Fin.le_last _)).trans hp)).lt_of_not_ge fun h'' => ?_
    let q' : LTSeries α := p.drop i
    let q : LTSeries (f ⁻¹' {f x}) := ⟨q'.length, fun j => ⟨q' j, le_antisymm
      (f.monotone (le_trans (b := q'.last) (q'.monotone (Fin.le_last _)) (p.last_drop _ ▸ hp)))
      (le_trans (b := f q'.head) (p.head_drop _ ▸ h'')
        (f.monotone (q'.monotone (Fin.zero_le _))))⟩, fun i => q'.step i⟩
    have := (LTSeries.length_le_krullDim q).trans (h (f x))
    simp only [RelSeries.drop_length, Nat.cast_le, tsub_le_iff_right, q', i, q] at this
    have : p.length > m := ENat.natCast_lt_natCast.mp ((le_add_left le_rfl).trans_lt h_len)
    lia

include h in

中文:
引理 height_le_of_krullDim_preimage_le
  条件: (x : α)
  证明: by
  generalize h' : Order.height (f x) = n
  cases n with | top => simp | coe n =>
    induction n using Nat.strong_induction_on generalizing x with | h n ih =>
    refine height_le_iff.mpr fun p hp => le_of_not_gt fun h_len => ?_
    let i : Fin (p.length + 1) := ⟨p.length - (m + 1), Nat.sub_lt_succ p.length _⟩
    suffices h'' : f (p i) < f x by
      obtain ⟨n', hn'⟩ : exists (n' : Nat), n' = height (f (p i)) := ENat.ne_top_iff_exists.mp
        ((height_mono h''.le).trans_lt (h' ▸ ENat.natCast_lt_top _)).ne
      have h_lt : n' < n := ENat.natCast_lt_natCast.mp
        (h' ▸ hn' ▸ height_strictMono h'' (hn' ▸ ENat.natCast_lt_top _))
have := (length_le_height_last (p := p.take i)).trans ih n' h_lt (p i) hn'.symm
      rw [RelSeries.take_length]; rw [ENat.natCast_sub]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [tsub_le_iff_right]; rw [add_assoc]; rw [add_comm _ (_ + 1)]; rw [← add_assoc]; rw [← mul_add_one] at this
      refine not_lt_of_ge ?_ (h_len.trans_le this)
      gcongr
      rwa [← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_le_natCast]
    refine (f.monotone ((p.monotone (Fin.le_last _)).trans hp)).lt_of_not_ge fun h'' => ?_
    let q' : LTSeries α := p.drop i
    let q : LTSeries (f ⁻¹' {f x}) := ⟨q'.length, fun j => ⟨q' j, le_antisymm
      (f.monotone (le_trans (b := q'.last) (q'.monotone (Fin.le_last _)) (p.last_drop _ ▸ hp)))
      (le_trans (b := f q'.head) (p.head_drop _ ▸ h'')
        (f.monotone (q'.monotone (Fin.zero_le _))))⟩, fun i => q'.step i⟩
    have := (LTSeries.length_le_krullDim q).trans (h (f x))
    simp only [RelSeries.drop_length, Nat.cast_le, tsub_le_iff_right, q', i, q] at this
    have : p.length > m := ENat.natCast_lt_natCast.mp ((le_add_left le_rfl).trans_lt h_len)
    lia

include h in

Depends on / 依赖: ENat.natCast_lt_top, ENat.ne_top_iff_exists.mp, Nat.strong_induction_on, Nat.sub_lt_succ, Order.height, generalize, generalizing, h_len, h_lt, height, height_le_iff, height_le_iff.mpr, height_mono, le_of_not_gt, length, natCast_lt_top, ne_top_iff_exists, p.length, strong_induction_on, sub_lt_succ
-/
lemma height_le_of_krullDim_preimage_le (x : α) :
    Order.height x <= (m + 1) * Order.height (f x) + m := by
  generalize h' : Order.height (f x) = n
  cases n with | top => simp | coe n =>
    induction n using Nat.strong_induction_on generalizing x with | h n ih =>
    refine height_le_iff.mpr fun p hp => le_of_not_gt fun h_len => ?_
    let i : Fin (p.length + 1) := ⟨p.length - (m + 1), Nat.sub_lt_succ p.length _⟩
    suffices h'' : f (p i) < f x by
      obtain ⟨n', hn'⟩ : exists (n' : Nat), n' = height (f (p i)) := ENat.ne_top_iff_exists.mp
        ((height_mono h''.le).trans_lt (h' ▸ ENat.natCast_lt_top _)).ne
      have h_lt : n' < n := ENat.natCast_lt_natCast.mp
        (h' ▸ hn' ▸ height_strictMono h'' (hn' ▸ ENat.natCast_lt_top _))
have := (length_le_height_last (p := p.take i)).trans ih n' h_lt (p i) hn'.symm
      rw [RelSeries.take_length]; rw [ENat.natCast_sub]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [tsub_le_iff_right]; rw [add_assoc]; rw [add_comm _ (_ + 1)]; rw [← add_assoc]; rw [← mul_add_one] at this
      refine not_lt_of_ge ?_ (h_len.trans_le this)
      gcongr
      rwa [← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_le_natCast]
    refine (f.monotone ((p.monotone (Fin.le_last _)).trans hp)).lt_of_not_ge fun h'' => ?_
    let q' : LTSeries α := p.drop i
    let q : LTSeries (f ⁻¹' {f x}) := ⟨q'.length, fun j => ⟨q' j, le_antisymm
      (f.monotone (le_trans (b := q'.last) (q'.monotone (Fin.le_last _)) (p.last_drop _ ▸ hp)))
      (le_trans (b := f q'.head) (p.head_drop _ ▸ h'')
        (f.monotone (q'.monotone (Fin.zero_le _))))⟩, fun i => q'.step i⟩
    have := (LTSeries.length_le_krullDim q).trans (h (f x))
    simp only [RelSeries.drop_length, Nat.cast_le, tsub_le_iff_right, q', i, q] at this
    have : p.length > m := ENat.natCast_lt_natCast.mp ((le_add_left le_rfl).trans_lt h_len)
    lia

include h in
/--
lemma `coheight_le_of_krullDim_preimage_le` / 引理 `coheight_le_of_krullDim_preimage_le`

English:
lemma coheight_le_of_krullDim_preimage_le
  given: (x : α)
  proof: by
  rw [Order.coheight]; rw [Order.coheight]
  apply height_le_of_krullDim_preimage_le (f := f.dual)
  exact fun x => le_of_eq_of_le (krullDim_orderDual (α := f ⁻¹' {x})) (h x)

include f h in

中文:
引理 coheight_le_of_krullDim_preimage_le
  条件: (x : α)
  证明: by
  rw [Order.coheight]; rw [Order.coheight]
  apply height_le_of_krullDim_preimage_le (f := f.dual)
  exact fun x => le_of_eq_of_le (krullDim_orderDual (α := f ⁻¹' {x})) (h x)

include f h in

Depends on / 依赖: Order.coheight, coheight, f.dual, height_le_of_krullDim_preimage_le, krullDim_orderDual, le_of_eq_of_le
-/
lemma coheight_le_of_krullDim_preimage_le (x : α) :
    Order.coheight x <= (m + 1) * Order.coheight (f x) + m := by
  rw [Order.coheight]; rw [Order.coheight]
  apply height_le_of_krullDim_preimage_le (f := f.dual)
  exact fun x => le_of_eq_of_le (krullDim_orderDual (α := f ⁻¹' {x})) (h x)

include f h in
/--
lemma `krullDim_le_of_krullDim_preimage_le` / 引理 `krullDim_le_of_krullDim_preimage_le`

English:
lemma krullDim_le_of_krullDim_preimage_le
  proof: by
  rw [Order.krullDim_eq_iSup_height]; rw [Order.krullDim_eq_iSup_height]; rw [iSup_le_iff]
  refine fun x => (WithBot.coe_mono (height_le_of_krullDim_preimage_le f h x)).trans ?_
  push_cast
  gcongr
  exacts [right_eq_inf.mp rfl, le_iSup_iff.mpr fun b a => a (f x)]

中文:
引理 krullDim_le_of_krullDim_preimage_le
  证明: by
  rw [Order.krullDim_eq_iSup_height]; rw [Order.krullDim_eq_iSup_height]; rw [iSup_le_iff]
  refine fun x => (WithBot.coe_mono (height_le_of_krullDim_preimage_le f h x)).trans ?_
  push_cast
  gcongr
  exacts [right_eq_inf.mp rfl, le_iSup_iff.mpr fun b a => a (f x)]

Depends on / 依赖: Order.krullDim_eq_iSup_height, WithBot, WithBot.coe_mono, coe_mono, exacts, height_le_of_krullDim_preimage_le, iSup_le_iff, krullDim_eq_iSup_height, le_iSup_iff, le_iSup_iff.mpr, right_eq_inf, right_eq_inf.mp
-/
lemma krullDim_le_of_krullDim_preimage_le :
    Order.krullDim α <= (m + 1) * Order.krullDim β + m := by
  rw [Order.krullDim_eq_iSup_height]; rw [Order.krullDim_eq_iSup_height]; rw [iSup_le_iff]
  refine fun x => (WithBot.coe_mono (height_le_of_krullDim_preimage_le f h x)).trans ?_
  push_cast
  gcongr
  exacts [right_eq_inf.mp rfl, le_iSup_iff.mpr fun b a => a (f x)]

/--
lemma `krullDim_le_of_krullDim_preimage_le'` / 引理 `krullDim_le_of_krullDim_preimage_le'`

English:
lemma krullDim_le_of_krullDim_preimage_le'
  statement: (f : α -> β) (h_mono : Monotone f)
  proof: Order.krullDim_le_of_krullDim_preimage_le ⟨f, h_mono⟩ h

中文:
引理 krullDim_le_of_krullDim_preimage_le'
  结论: (f : α -> β) (h_mono : 递增 f)
  证明: Order.krullDim_le_of_krullDim_preimage_le ⟨f, h_mono⟩ h

Depends on / 依赖: Order.krullDim_le_of_krullDim_preimage_le, h_mono, krullDim_le_of_krullDim_preimage_le
-/
lemma krullDim_le_of_krullDim_preimage_le' (f : α -> β) (h_mono : Monotone f)
    (h : forall (x : β), Order.krullDim (f ⁻¹' {x}) <= m) :
    Order.krullDim α <= (m + 1) * Order.krullDim β + m :=
  Order.krullDim_le_of_krullDim_preimage_le ⟨f, h_mono⟩ h

/--
lemma `krullDim_le_of_orderEmbedding` / 引理 `krullDim_le_of_orderEmbedding`

English:
lemma krullDim_le_of_orderEmbedding
  given: (e : α ↪o β)
  statement: Order.krullDim α <= Order.krullDim β
  proof: by
have (b : β) : Subsingleton (e ⁻¹' {b}) := Set.Subsingleton.coe_sort
    Set.Subsingleton.preimage Set.subsingleton_singleton e.injective
  simpa using Order.krullDim_le_of_krullDim_preimage_le' e e.monotone fun _ =>
    Order.krullDim_nonpos_of_subsingleton

中文:
引理 krullDim_le_of_orderEmbedding
  条件: (e : α ↪o β)
  结论: Order.krullDim α <= Order.krullDim β
  证明: by
have (b : β) : Subsingleton (e ⁻¹' {b}) := Set.Subsingleton.coe_sort
    Set.Subsingleton.preimage Set.subsingleton_singleton e.injective
  simpa using Order.krullDim_le_of_krullDim_preimage_le' e e.monotone fun _ =>
    Order.krullDim_nonpos_of_subsingleton

Depends on / 依赖: Order.krullDim_le_of_krullDim_preimage_le, Order.krullDim_nonpos_of_subsingleton, Set.Subsingleton.coe_sort, Set.Subsingleton.preimage, Set.subsingleton_singleton, Subsingleton, coe_sort, e.injective, e.monotone, injective, krullDim_le_of_krullDim_preimage_le, krullDim_nonpos_of_subsingleton, monotone, preimage, subsingleton_singleton
-/
lemma krullDim_le_of_orderEmbedding (e : α ↪o β) : Order.krullDim α <= Order.krullDim β := by
have (b : β) : Subsingleton (e ⁻¹' {b}) := Set.Subsingleton.coe_sort
    Set.Subsingleton.preimage Set.subsingleton_singleton e.injective
  simpa using Order.krullDim_le_of_krullDim_preimage_le' e e.monotone fun _ =>
    Order.krullDim_nonpos_of_subsingleton

end orderHom

end Order
