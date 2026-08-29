/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.ZFC.Class

/-!
# Von Neumann hierarchy

This file defines the von Neumann hierarchy of sets `V_ o` for ordinal `o`, which is recursively
defined so that `V_ a = ⋃ b < a, powerset (V_ b)`. This stratifies the universal class, in the sense
that `⋃ o, V_ o = univ`.

## Notation

- `V_ o` is notation for `vonNeumann o`. It is scoped in the `ZFSet` namespace.
-/

@[expose] public section

universe u

open Order

namespace ZFSet

/--
Definition of `vonNeumann` / `vonNeumann` 的定义

English:
definition vonNeumann
  signature: (o : Ordinal.{u})
  body: ⋃ a : Set.Iio o, powerset (vonNeumann a)
termination_by o
decreasing_by exact a.2

@[inherit_doc]
scoped notation "V_ " => vonNeumann

中文:
定义 vonNeumann
  签名: (o : 序数.{u})
  定义体: ⋃ a : Set.Iio o, powerset (vonNeumann a)
termination_by o
decreasing_by exact a.2

@[inherit_doc]
scoped notation "V_ " => vonNeumann

Depends on / 依赖: Set.Iio, decreasing_by, powerset, termination_by, vonNeumann
-/
noncomputable def vonNeumann (o : Ordinal.{u}) : ZFSet.{u} :=
  ⋃ a : Set.Iio o, powerset (vonNeumann a)
termination_by o
decreasing_by exact a.2

@[inherit_doc]
scoped notation "V_ " => vonNeumann

variable {a b o : Ordinal.{u}} {x : ZFSet.{u}}

/--
lemma `mem_vonNeumann'` / 引理 `mem_vonNeumann'`

English:
lemma mem_vonNeumann'
  statement: x in V_ o ↔ exists a < o, x subseteq V_ a
  proof: by rw [vonNeumann]; simp

中文:
引理 mem_vonNeumann'
  结论: x in V_ o ↔ 存在 a < o, x subseteq V_ a
  证明: by rw [vonNeumann]; simp

Depends on / 依赖: vonNeumann
-/
lemma mem_vonNeumann' : x in V_ o ↔ exists a < o, x subseteq V_ a := by rw [vonNeumann]; simp

/--
theorem `isTransitive_vonNeumann` / 定理 `isTransitive_vonNeumann`

English:
theorem isTransitive_vonNeumann
  given: (o : Ordinal)
  statement: IsTransitive (V_ o)
  proof: by
  rw [vonNeumann]
  exact .iUnion fun ⟨a, _⟩ => (isTransitive_vonNeumann a).powerset
termination_by o

中文:
定理 isTransitive_vonNeumann
  条件: (o : 序数)
  结论: IsTransitive (V_ o)
  证明: by
  rw [vonNeumann]
  exact .iUnion fun ⟨a, _⟩ => (isTransitive_vonNeumann a).powerset
termination_by o

Depends on / 依赖: iUnion, isTransitive_vonNeumann, powerset, termination_by, vonNeumann
-/
theorem isTransitive_vonNeumann (o : Ordinal) : IsTransitive (V_ o) := by
  rw [vonNeumann]
  exact .iUnion fun ⟨a, _⟩ => (isTransitive_vonNeumann a).powerset
termination_by o

/--
theorem `vonNeumann_mem_of_lt` / 定理 `vonNeumann_mem_of_lt`

English:
theorem vonNeumann_mem_of_lt
  given: (h : a < b)
  statement: V_ a in V_ b
  proof: by
  rw [vonNeumann]; aesop

中文:
定理 vonNeumann_mem_of_lt
  条件: (h : a < b)
  结论: V_ a in V_ b
  证明: by
  rw [vonNeumann]; aesop
-/
@[gcongr] theorem vonNeumann_mem_of_lt (h : a < b) : V_ a in V_ b := by
  rw [vonNeumann]; aesop

/--
theorem `vonNeumann_subset_of_le` / 定理 `vonNeumann_subset_of_le`

English:
theorem vonNeumann_subset_of_le
  given: (h : a <= b)
  statement: V_ a subseteq V_ b
  proof: h.eq_or_lt.rec (by simp_all) fun h => isTransitive_vonNeumann _ _ vonNeumann_mem_of_lt h

中文:
定理 vonNeumann_subset_of_le
  条件: (h : a <= b)
  结论: V_ a subseteq V_ b
  证明: h.eq_or_lt.rec (by simp_all) fun h => isTransitive_vonNeumann _ _ vonNeumann_mem_of_lt h
-/
@[gcongr] theorem vonNeumann_subset_of_le (h : a <= b) : V_ a subseteq V_ b :=
h.eq_or_lt.rec (by simp_all) fun h => isTransitive_vonNeumann _ _ vonNeumann_mem_of_lt h

/--
theorem `subset_vonNeumann` / 定理 `subset_vonNeumann`

English:
theorem subset_vonNeumann
  given: {o : Ordinal} {x : ZFSet}
  statement: x subseteq V_ o ↔ rank x <= o
  proof: by
  rw [rank_le_iff]
  constructor <;> intro hx y hy
  · apply (rank_lt_of_mem (hx hy)).trans_le
    simp_rw [rank_le_iff, mem_vonNeumann']
    rintro z ⟨a, ha, hz⟩
    exact (subset_vonNeumann.1 hz).trans_lt ha
  · rw [mem_vonNeumann']
    have := hx hy
    exact ⟨_, this, subset_vonNeumann.2 le_rfl⟩
termination_by o

中文:
定理 subset_vonNeumann
  条件: {o : 序数} {x : ZFSet}
  结论: x subseteq V_ o ↔ rank x <= o
  证明: by
  rw [rank_le_iff]
  constructor <;> intro hx y hy
  · apply (rank_lt_of_mem (hx hy)).trans_le
    simp_rw [rank_le_iff, mem_vonNeumann']
    rintro z ⟨a, ha, hz⟩
    exact (subset_vonNeumann.1 hz).trans_lt ha
  · rw [mem_vonNeumann']
    have := hx hy
    exact ⟨_, this, subset_vonNeumann.2 le_rfl⟩
termination_by o

Depends on / 依赖: le_rfl, mem_vonNeumann, rank_le_iff, rank_lt_of_mem, simp_rw, subset_vonNeumann, termination_by, trans_le, trans_lt
-/
theorem subset_vonNeumann {o : Ordinal} {x : ZFSet} : x subseteq V_ o ↔ rank x <= o := by
  rw [rank_le_iff]
  constructor <;> intro hx y hy
  · apply (rank_lt_of_mem (hx hy)).trans_le
    simp_rw [rank_le_iff, mem_vonNeumann']
    rintro z ⟨a, ha, hz⟩
    exact (subset_vonNeumann.1 hz).trans_lt ha
  · rw [mem_vonNeumann']
    have := hx hy
    exact ⟨_, this, subset_vonNeumann.2 le_rfl⟩
termination_by o

/--
theorem `subset_vonNeumann_self` / 定理 `subset_vonNeumann_self`

English:
theorem subset_vonNeumann_self
  given: (x : ZFSet)
  statement: x subseteq V_ (rank x)
  proof: by
  simp [subset_vonNeumann]

中文:
定理 subset_vonNeumann_self
  条件: (x : ZFSet)
  结论: x subseteq V_ (rank x)
  证明: by
  simp [subset_vonNeumann]

Depends on / 依赖: subset_vonNeumann
-/
theorem subset_vonNeumann_self (x : ZFSet) : x subseteq V_ (rank x) := by
  simp [subset_vonNeumann]

/--
theorem `mem_vonNeumann` / 定理 `mem_vonNeumann`

English:
theorem mem_vonNeumann
  statement: x in V_ o ↔ rank x < o
  proof: by
  simp_rw [mem_vonNeumann', subset_vonNeumann]
  exact ⟨fun ⟨a, h₁, h₂⟩ => h₂.trans_lt h₁, by aesop⟩

中文:
定理 mem_vonNeumann
  结论: x in V_ o ↔ rank x < o
  证明: by
  simp_rw [mem_vonNeumann', subset_vonNeumann]
  exact ⟨fun ⟨a, h₁, h₂⟩ => h₂.trans_lt h₁, by aesop⟩

Depends on / 依赖: mem_vonNeumann, simp_rw, subset_vonNeumann, trans_lt
-/
theorem mem_vonNeumann : x in V_ o ↔ rank x < o := by
  simp_rw [mem_vonNeumann', subset_vonNeumann]
  exact ⟨fun ⟨a, h₁, h₂⟩ => h₂.trans_lt h₁, by aesop⟩

/--
theorem `mem_vonNeumann_succ` / 定理 `mem_vonNeumann_succ`

English:
theorem mem_vonNeumann_succ
  given: (x : ZFSet)
  statement: x in V_ (succ (rank x))
  proof: by
  simp [mem_vonNeumann]

中文:
定理 mem_vonNeumann_succ
  条件: (x : ZFSet)
  结论: x in V_ (succ (rank x))
  证明: by
  simp [mem_vonNeumann]

Depends on / 依赖: mem_vonNeumann
-/
theorem mem_vonNeumann_succ (x : ZFSet) : x in V_ (succ (rank x)) := by
  simp [mem_vonNeumann]

/--
theorem `exists_mem_vonNeumann` / 定理 `exists_mem_vonNeumann`

English:
theorem exists_mem_vonNeumann
  given: (x : ZFSet)
  statement: exists o, x in V_ o
  proof: ⟨_, mem_vonNeumann_succ x⟩

@[simp]

中文:
定理 存在_mem_vonNeumann
  条件: (x : ZFSet)
  结论: 存在 o, x in V_ o
  证明: ⟨_, mem_vonNeumann_succ x⟩

@[simp]

Depends on / 依赖: mem_vonNeumann_succ
-/
theorem exists_mem_vonNeumann (x : ZFSet) : exists o, x in V_ o :=
  ⟨_, mem_vonNeumann_succ x⟩

@[simp]
/--
theorem `rank_vonNeumann` / 定理 `rank_vonNeumann`

English:
theorem rank_vonNeumann
  given: (o : Ordinal)
  statement: rank (V_ o) = o
  proof: le_antisymm (by rw [← subset_vonNeumann]) le_of_forall_lt fun a ha =>
    rank_vonNeumann a ▸ rank_lt_of_mem (vonNeumann_mem_of_lt ha)
termination_by o

@[simp]

中文:
定理 rank_vonNeumann
  条件: (o : 序数)
  结论: rank (V_ o) = o
  证明: le_antisymm (by rw [← subset_vonNeumann]) le_of_forall_lt fun a ha =>
    rank_vonNeumann a ▸ rank_lt_of_mem (vonNeumann_mem_of_lt ha)
termination_by o

@[simp]

Depends on / 依赖: le_antisymm, le_of_forall_lt, rank_lt_of_mem, rank_vonNeumann, subset_vonNeumann, termination_by, vonNeumann_mem_of_lt
-/
theorem rank_vonNeumann (o : Ordinal) : rank (V_ o) = o :=
le_antisymm (by rw [← subset_vonNeumann]) le_of_forall_lt fun a ha =>
    rank_vonNeumann a ▸ rank_lt_of_mem (vonNeumann_mem_of_lt ha)
termination_by o

@[simp]
/--
theorem `vonNeumann_mem_vonNeumann_iff` / 定理 `vonNeumann_mem_vonNeumann_iff`

English:
theorem vonNeumann_mem_vonNeumann_iff
  statement: V_ a in V_ b ↔ a < b
  proof: by
  simp [mem_vonNeumann]

@[simp]

中文:
定理 vonNeumann_mem_vonNeumann_iff
  结论: V_ a in V_ b ↔ a < b
  证明: by
  simp [mem_vonNeumann]

@[simp]

Depends on / 依赖: mem_vonNeumann
-/
theorem vonNeumann_mem_vonNeumann_iff : V_ a in V_ b ↔ a < b := by
  simp [mem_vonNeumann]

@[simp]
/--
theorem `vonNeumann_subset_vonNeumann_iff` / 定理 `vonNeumann_subset_vonNeumann_iff`

English:
theorem vonNeumann_subset_vonNeumann_iff
  statement: V_ a subseteq V_ b ↔ a <= b
  proof: by
  simp [subset_vonNeumann]

中文:
定理 vonNeumann_subset_vonNeumann_iff
  结论: V_ a subseteq V_ b ↔ a <= b
  证明: by
  simp [subset_vonNeumann]

Depends on / 依赖: subset_vonNeumann
-/
theorem vonNeumann_subset_vonNeumann_iff : V_ a subseteq V_ b ↔ a <= b := by
  simp [subset_vonNeumann]

/--
theorem `mem_vonNeumann_of_subset` / 定理 `mem_vonNeumann_of_subset`

English:
theorem mem_vonNeumann_of_subset
  given: {y : ZFSet} (h : x subseteq y) (hy : y in V_ o)
  statement: x in V_ o
  proof: by
  rw [mem_vonNeumann] at *
  exact (rank_mono h).trans_lt hy

中文:
定理 mem_vonNeumann_of_subset
  条件: {y : ZFSet} (h : x subseteq y) (hy : y in V_ o)
  结论: x in V_ o
  证明: by
  rw [mem_vonNeumann] at *
  exact (rank_mono h).trans_lt hy

Depends on / 依赖: mem_vonNeumann, rank_mono, trans_lt
-/
theorem mem_vonNeumann_of_subset {y : ZFSet} (h : x subseteq y) (hy : y in V_ o) : x in V_ o := by
  rw [mem_vonNeumann] at *
  exact (rank_mono h).trans_lt hy

/--
theorem `vonNeumann_strictMono` / 定理 `vonNeumann_strictMono`

English:
theorem vonNeumann_strictMono
  statement: StrictMono vonNeumann
  proof: strictMono_of_le_iff_le (by simp)

中文:
定理 vonNeumann_strictMono
  结论: 严格递增 vonNeumann
  证明: strictMono_of_le_iff_le (by simp)

Depends on / 依赖: strictMono_of_le_iff_le
-/
theorem vonNeumann_strictMono : StrictMono vonNeumann :=
  strictMono_of_le_iff_le (by simp)

/--
theorem `vonNeumann_injective` / 定理 `vonNeumann_injective`

English:
theorem vonNeumann_injective
  statement: Function.Injective vonNeumann
  proof: vonNeumann_strictMono.injective

@[simp]

中文:
定理 vonNeumann_injective
  结论: 函数.单射 vonNeumann
  证明: vonNeumann_strictMono.injective

@[simp]

Depends on / 依赖: injective, vonNeumann_strictMono, vonNeumann_strictMono.injective
-/
theorem vonNeumann_injective : Function.Injective vonNeumann :=
  vonNeumann_strictMono.injective

@[simp]
/--
theorem `vonNeumann_inj` / 定理 `vonNeumann_inj`

English:
theorem vonNeumann_inj
  statement: V_ a = V_ b ↔ a = b
  proof: vonNeumann_injective.eq_iff

@[simp]

中文:
定理 vonNeumann_inj
  结论: V_ a = V_ b ↔ a = b
  证明: vonNeumann_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, vonNeumann_injective, vonNeumann_injective.eq_iff
-/
theorem vonNeumann_inj : V_ a = V_ b ↔ a = b :=
  vonNeumann_injective.eq_iff

@[simp]
/--
theorem `vonNeumann_zero` / 定理 `vonNeumann_zero`

English:
theorem vonNeumann_zero
  statement: V_ 0 = ∅
  proof: (eq_empty _).2 (by simp [mem_vonNeumann])

@[simp]

中文:
定理 vonNeumann_zero
  结论: V_ 0 = ∅
  证明: (eq_empty _).2 (by simp [mem_vonNeumann])

@[simp]

Depends on / 依赖: eq_empty, mem_vonNeumann
-/
theorem vonNeumann_zero : V_ 0 = ∅ :=
  (eq_empty _).2 (by simp [mem_vonNeumann])

@[simp]
/--
theorem `vonNeumann_add_one` / 定理 `vonNeumann_add_one`

English:
theorem vonNeumann_add_one
  given: (o : Ordinal)
  statement: V_ (o + 1) = powerset (V_ o)
  proof: ext fun z => by rw [mem_vonNeumann, mem_powerset, subset_vonNeumann, lt_add_one_iff]

@[deprecated vonNeumann_add_one (since := "2026-05-25")]

中文:
定理 vonNeumann_add_one
  条件: (o : 序数)
  结论: V_ (o + 1) = powerset (V_ o)
  证明: ext fun z => by rw [mem_vonNeumann, mem_powerset, subset_vonNeumann, lt_add_one_iff]

@[deprecated vonNeumann_add_one (since := "2026-05-25")]

Depends on / 依赖: lt_add_one_iff, mem_powerset, mem_vonNeumann, subset_vonNeumann
-/
theorem vonNeumann_add_one (o : Ordinal) : V_ (o + 1) = powerset (V_ o) :=
  ext fun z => by rw [mem_vonNeumann, mem_powerset, subset_vonNeumann, lt_add_one_iff]

@[deprecated vonNeumann_add_one (since := "2026-05-25")]
/--
theorem `vonNeumann_succ` / 定理 `vonNeumann_succ`

English:
theorem vonNeumann_succ
  given: (o : Ordinal)
  statement: V_ (succ o) = powerset (V_ o)
  proof: vonNeumann_add_one o

中文:
定理 vonNeumann_succ
  条件: (o : 序数)
  结论: V_ (succ o) = powerset (V_ o)
  证明: vonNeumann_add_one o

Depends on / 依赖: vonNeumann_add_one
-/
theorem vonNeumann_succ (o : Ordinal) : V_ (succ o) = powerset (V_ o) :=
  vonNeumann_add_one o

/--
theorem `vonNeumann_of_isSuccPrelimit` / 定理 `vonNeumann_of_isSuccPrelimit`

English:
theorem vonNeumann_of_isSuccPrelimit
  given: (h : IsSuccPrelimit o)
  proof: ext fun z => by simpa [mem_vonNeumann] using h.lt_iff_exists_lt

中文:
定理 vonNeumann_of_isSuccPrelimit
  条件: (h : IsSuccPrelimit o)
  证明: ext fun z => by simpa [mem_vonNeumann] using h.lt_iff_exists_lt

Depends on / 依赖: h.lt_iff_exists_lt, lt_iff_exists_lt, mem_vonNeumann
-/
theorem vonNeumann_of_isSuccPrelimit (h : IsSuccPrelimit o) :
    V_ o = ⋃ a : Set.Iio o, vonNeumann a :=
  ext fun z => by simpa [mem_vonNeumann] using h.lt_iff_exists_lt

/--
theorem `iUnion_vonNeumann` / 定理 `iUnion_vonNeumann`

English:
theorem iUnion_vonNeumann
  statement: ⋃ o, (V_ o : Class) = Class.univ
  proof: Class.eq_univ_of_forall fun x => Set.mem_iUnion.2 exists_mem_vonNeumann x

中文:
定理 iUnion_vonNeumann
  结论: ⋃ o, (V_ o : 类) = 类.univ
  证明: Class.eq_univ_of_forall fun x => Set.mem_iUnion.2 exists_mem_vonNeumann x

Depends on / 依赖: Class.eq_univ_of_forall, Set.mem_iUnion, eq_univ_of_forall, exists_mem_vonNeumann, mem_iUnion
-/
theorem iUnion_vonNeumann : ⋃ o, (V_ o : Class) = Class.univ :=
Class.eq_univ_of_forall fun x => Set.mem_iUnion.2 exists_mem_vonNeumann x

/--
theorem `_root_.Ordinal.toZFSet_subset_vonNeumann` / 定理 `_root_.Ordinal.toZFSet_subset_vonNeumann`

English:
theorem _root_.Ordinal.toZFSet_subset_vonNeumann
  given: (o : Ordinal)
  statement: o.toZFSet subseteq V_ o
  proof: by
  simp [subset_vonNeumann]

中文:
定理 _root_.序数.toZFSet_subset_vonNeumann
  条件: (o : 序数)
  结论: o.toZFSet subseteq V_ o
  证明: by
  simp [subset_vonNeumann]

Depends on / 依赖: subset_vonNeumann
-/
theorem _root_.Ordinal.toZFSet_subset_vonNeumann (o : Ordinal) : o.toZFSet subseteq V_ o := by
  simp [subset_vonNeumann]

/--
lemma `_root_.Ordinal.card_le_card_vonNeumann` / 引理 `_root_.Ordinal.card_le_card_vonNeumann`

English:
lemma _root_.Ordinal.card_le_card_vonNeumann
  given: (o : Ordinal)
  statement: o.card <= card (V_ o)
  proof: by
  simpa using card_mono o.toZFSet_subset_vonNeumann

中文:
引理 _root_.序数.card_le_card_vonNeumann
  条件: (o : 序数)
  结论: o.card <= card (V_ o)
  证明: by
  simpa using card_mono o.toZFSet_subset_vonNeumann

Depends on / 依赖: card_mono, o.toZFSet_subset_vonNeumann, toZFSet_subset_vonNeumann
-/
lemma _root_.Ordinal.card_le_card_vonNeumann (o : Ordinal) : o.card <= card (V_ o) := by
  simpa using card_mono o.toZFSet_subset_vonNeumann

open Cardinal in
/--
theorem `card_vonNeumann` / 定理 `card_vonNeumann`

English:
theorem card_vonNeumann
  given: (o : Ordinal.{u})
  statement: card (V_ o) = preBeth o
  proof: by
  induction o using Ordinal.limitRecOn with
  | zero => simp
  | add_one o ih => simp [ih]
  | limit o ho ih =>
    simp_rw [preBeth_limit ho.isSuccPrelimit, ← fun i : Set.Iio o => ih i i.2,
      vonNeumann_of_isSuccPrelimit ho.isSuccPrelimit]
    apply iSup_card_le_card_iUnion.antisymm'
    rw [← lift_le.{u + 1}]
    apply lift_card_iUnion_le_sum_card.trans
    refine (sum_eq_lift_iSup_of_lift_mk_le_lift_iSup ?_ ?_).le
    · rw [mk_Iio_ordinal, ← lift_aleph0.{u + 1, u}, lift_le, Ordinal.aleph0_le_card]
      exact Ordinal.omega0_le_of_isSuccLimit ho
    · rw [mk_Iio_ordinal, lift_lift, lift_le]
      by_contra! h
refine (⨆ i : Set.Iio o, (V_ ↑i).card).card_ord.not_lt
(Ordinal.card_le_card_vonNeumann _).trans_lt (cantor _).trans_le ?_
      rw [← card_powerset]; rw [← vonNeumann_add_one]
      refine le_ciSup bddAbove_of_small (⟨_, ho.succ_lt ?_⟩ : Set.Iio o)
      exact (ord_card_le _).trans_lt' (ord_strictMono h)

中文:
定理 card_vonNeumann
  条件: (o : 序数.{u})
  结论: card (V_ o) = preBeth o
  证明: by
  induction o using Ordinal.limitRecOn with
  | zero => simp
  | add_one o ih => simp [ih]
  | limit o ho ih =>
    simp_rw [preBeth_limit ho.isSuccPrelimit, ← fun i : Set.Iio o => ih i i.2,
      vonNeumann_of_isSuccPrelimit ho.isSuccPrelimit]
    apply iSup_card_le_card_iUnion.antisymm'
    rw [← lift_le.{u + 1}]
    apply lift_card_iUnion_le_sum_card.trans
    refine (sum_eq_lift_iSup_of_lift_mk_le_lift_iSup ?_ ?_).le
    · rw [mk_Iio_ordinal, ← lift_aleph0.{u + 1, u}, lift_le, Ordinal.aleph0_le_card]
      exact Ordinal.omega0_le_of_isSuccLimit ho
    · rw [mk_Iio_ordinal, lift_lift, lift_le]
      by_contra! h
refine (⨆ i : Set.Iio o, (V_ ↑i).card).card_ord.not_lt
(Ordinal.card_le_card_vonNeumann _).trans_lt (cantor _).trans_le ?_
      rw [← card_powerset]; rw [← vonNeumann_add_one]
      refine le_ciSup bddAbove_of_small (⟨_, ho.succ_lt ?_⟩ : Set.Iio o)
      exact (ord_card_le _).trans_lt' (ord_strictMono h)

Depends on / 依赖: Ordinal, Ordinal.aleph0_le_card, Ordinal.limitRecOn, Ordinal.omega0_le_o, Set.Iio, add_one, aleph0_le_card, antisymm, ho.isSuccPrelimit, iSup_card_le_card_iUnion, iSup_card_le_card_iUnion.antisymm, isSuccPrelimit, lift_aleph0, lift_card_iUnion_le_sum_card, lift_card_iUnion_le_sum_card.trans, lift_le, limitRecOn, mk_Iio_ordinal, omega0_le_o, preBeth_limit
-/
theorem card_vonNeumann (o : Ordinal.{u}) : card (V_ o) = preBeth o := by
  induction o using Ordinal.limitRecOn with
  | zero => simp
  | add_one o ih => simp [ih]
  | limit o ho ih =>
    simp_rw [preBeth_limit ho.isSuccPrelimit, ← fun i : Set.Iio o => ih i i.2,
      vonNeumann_of_isSuccPrelimit ho.isSuccPrelimit]
    apply iSup_card_le_card_iUnion.antisymm'
    rw [← lift_le.{u + 1}]
    apply lift_card_iUnion_le_sum_card.trans
    refine (sum_eq_lift_iSup_of_lift_mk_le_lift_iSup ?_ ?_).le
    · rw [mk_Iio_ordinal, ← lift_aleph0.{u + 1, u}, lift_le, Ordinal.aleph0_le_card]
      exact Ordinal.omega0_le_of_isSuccLimit ho
    · rw [mk_Iio_ordinal, lift_lift, lift_le]
      by_contra! h
refine (⨆ i : Set.Iio o, (V_ ↑i).card).card_ord.not_lt
(Ordinal.card_le_card_vonNeumann _).trans_lt (cantor _).trans_le ?_
      rw [← card_powerset]; rw [← vonNeumann_add_one]
      refine le_ciSup bddAbove_of_small (⟨_, ho.succ_lt ?_⟩ : Set.Iio o)
      exact (ord_card_le _).trans_lt' (ord_strictMono h)

end ZFSet
