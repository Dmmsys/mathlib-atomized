/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.Family

/-!
# Enumerating sets of ordinals by ordinals

The ordinals have the peculiar property that every subset bounded above is a small type, while
themselves not being small. As a consequence of this, every unbounded subset of `Ordinal` is order
isomorphic to `Ordinal`.

We define this correspondence as `enumOrd`, and use it to then define an order isomorphism
`enumOrdOrderIso`.

This can be thought of as an ordinal analog of `Nat.nth`.
-/

@[expose] public section

universe u

open Order Set

namespace Ordinal

variable {o a b : Ordinal.{u}}

/-- Enumerator function for an unbounded set of ordinals.

The definition is an implementation detail; this function is entirely characterized by being an
order isomorphism. See `enumOrdOrderIso`. -/
@[no_expose]
/--
Definition of `enumOrd` / `enumOrd` 的定义

English:
definition enumOrd
  signature: (s : Set Ordinal.{u}) (o : Ordinal.{u})
  body: sInf (s inter { b | forall c, c < o -> enumOrd s c < b })
termination_by o

中文:
定义 enumOrd
  签名: (s : 集合 序数.{u}) (o : 序数.{u})
  定义体: sInf (s inter { b | forall c, c < o -> enumOrd s c < b })
termination_by o

Depends on / 依赖: enumOrd, termination_by
-/
noncomputable def enumOrd (s : Set Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} :=
  sInf (s inter { b | forall c, c < o -> enumOrd s c < b })
termination_by o

variable {s : Set Ordinal.{u}}

/--
theorem `enumOrd_le_of_forall_lt` / 定理 `enumOrd_le_of_forall_lt`

English:
theorem enumOrd_le_of_forall_lt
  given: (ha : a in s) (H : forall b < o, enumOrd s b < a)
  statement: enumOrd s o <= a
  proof: by
  rw [enumOrd]
  exact csInf_le' ⟨ha, H⟩

中文:
定理 enumOrd_le_of_对任意_lt
  条件: (ha : a in s) (H : 对任意 b < o, enumOrd s b < a)
  结论: enumOrd s o <= a
  证明: by
  rw [enumOrd]
  exact csInf_le' ⟨ha, H⟩

Depends on / 依赖: csInf_le, enumOrd
-/
theorem enumOrd_le_of_forall_lt (ha : a in s) (H : forall b < o, enumOrd s b < a) : enumOrd s o <= a := by
  rw [enumOrd]
  exact csInf_le' ⟨ha, H⟩

/--
theorem `enumOrd_nonempty` / 定理 `enumOrd_nonempty`

English:
theorem enumOrd_nonempty
  given: (hs : ¬ BddAbove s) (o : Ordinal)
  proof: by
  rw [not_bddAbove_iff] at hs
  obtain ⟨a, ha⟩ := bddAbove_of_small (s := enumOrd s '' Iio o)
  obtain ⟨b, hb, hba⟩ := hs a
  exact ⟨b, hb, fun c hc => (ha (mem_image_of_mem _ hc)).trans_lt hba⟩

中文:
定理 enumOrd_nonempty
  条件: (hs : ¬ BddAbove s) (o : 序数)
  证明: by
  rw [not_bddAbove_iff] at hs
  obtain ⟨a, ha⟩ := bddAbove_of_small (s := enumOrd s '' Iio o)
  obtain ⟨b, hb, hba⟩ := hs a
  exact ⟨b, hb, fun c hc => (ha (mem_image_of_mem _ hc)).trans_lt hba⟩
-/
private theorem enumOrd_nonempty (hs : ¬ BddAbove s) (o : Ordinal) :
    (s inter { b | forall c, c < o -> enumOrd s c < b }).Nonempty := by
  rw [not_bddAbove_iff] at hs
  obtain ⟨a, ha⟩ := bddAbove_of_small (s := enumOrd s '' Iio o)
  obtain ⟨b, hb, hba⟩ := hs a
  exact ⟨b, hb, fun c hc => (ha (mem_image_of_mem _ hc)).trans_lt hba⟩

/--
theorem `enumOrd_mem_aux` / 定理 `enumOrd_mem_aux`

English:
theorem enumOrd_mem_aux
  given: (hs : ¬ BddAbove s) (o : Ordinal)
  proof: by
  rw [enumOrd]
  exact csInf_mem (enumOrd_nonempty hs o)

中文:
定理 enumOrd_mem_aux
  条件: (hs : ¬ BddAbove s) (o : 序数)
  证明: by
  rw [enumOrd]
  exact csInf_mem (enumOrd_nonempty hs o)
-/
private theorem enumOrd_mem_aux (hs : ¬ BddAbove s) (o : Ordinal) :
    enumOrd s o in s inter { b | forall c, c < o -> enumOrd s c < b } := by
  rw [enumOrd]
  exact csInf_mem (enumOrd_nonempty hs o)

/--
theorem `enumOrd_mem` / 定理 `enumOrd_mem`

English:
theorem enumOrd_mem
  given: (hs : ¬ BddAbove s) (o : Ordinal)
  statement: enumOrd s o in s
  proof: (enumOrd_mem_aux hs o).1

中文:
定理 enumOrd_mem
  条件: (hs : ¬ BddAbove s) (o : 序数)
  结论: enumOrd s o in s
  证明: (enumOrd_mem_aux hs o).1

Depends on / 依赖: enumOrd_mem_aux
-/
theorem enumOrd_mem (hs : ¬ BddAbove s) (o : Ordinal) : enumOrd s o in s :=
  (enumOrd_mem_aux hs o).1

/--
theorem `enumOrd_strictMono` / 定理 `enumOrd_strictMono`

English:
theorem enumOrd_strictMono
  given: (hs : ¬ BddAbove s)
  statement: StrictMono (enumOrd s)
  proof: fun a b => (enumOrd_mem_aux hs b).2 a

中文:
定理 enumOrd_strictMono
  条件: (hs : ¬ BddAbove s)
  结论: 严格递增 (enumOrd s)
  证明: fun a b => (enumOrd_mem_aux hs b).2 a

Depends on / 依赖: enumOrd_mem_aux
-/
theorem enumOrd_strictMono (hs : ¬ BddAbove s) : StrictMono (enumOrd s) :=
  fun a b => (enumOrd_mem_aux hs b).2 a

/--
theorem `enumOrd_injective` / 定理 `enumOrd_injective`

English:
theorem enumOrd_injective
  given: (hs : ¬ BddAbove s)
  statement: Function.Injective (enumOrd s)
  proof: (enumOrd_strictMono hs).injective

中文:
定理 enumOrd_injective
  条件: (hs : ¬ BddAbove s)
  结论: 函数.单射 (enumOrd s)
  证明: (enumOrd_strictMono hs).injective

Depends on / 依赖: enumOrd_strictMono, injective
-/
theorem enumOrd_injective (hs : ¬ BddAbove s) : Function.Injective (enumOrd s) :=
  (enumOrd_strictMono hs).injective

/--
theorem `enumOrd_inj` / 定理 `enumOrd_inj`

English:
theorem enumOrd_inj
  given: (hs : ¬ BddAbove s) {a b : Ordinal}
  statement: enumOrd s a = enumOrd s b ↔ a = b
  proof: (enumOrd_injective hs).eq_iff

中文:
定理 enumOrd_inj
  条件: (hs : ¬ BddAbove s) {a b : 序数}
  结论: enumOrd s a = enumOrd s b ↔ a = b
  证明: (enumOrd_injective hs).eq_iff

Depends on / 依赖: enumOrd_injective, eq_iff
-/
theorem enumOrd_inj (hs : ¬ BddAbove s) {a b : Ordinal} : enumOrd s a = enumOrd s b ↔ a = b :=
  (enumOrd_injective hs).eq_iff

/--
theorem `enumOrd_le_enumOrd` / 定理 `enumOrd_le_enumOrd`

English:
theorem enumOrd_le_enumOrd
  given: (hs : ¬ BddAbove s) {a b : Ordinal}
  proof: (enumOrd_strictMono hs).le_iff_le

中文:
定理 enumOrd_le_enumOrd
  条件: (hs : ¬ BddAbove s) {a b : 序数}
  证明: (enumOrd_strictMono hs).le_iff_le

Depends on / 依赖: enumOrd_strictMono, le_iff_le
-/
theorem enumOrd_le_enumOrd (hs : ¬ BddAbove s) {a b : Ordinal} :
    enumOrd s a <= enumOrd s b ↔ a <= b :=
  (enumOrd_strictMono hs).le_iff_le

/--
theorem `enumOrd_lt_enumOrd` / 定理 `enumOrd_lt_enumOrd`

English:
theorem enumOrd_lt_enumOrd
  given: (hs : ¬ BddAbove s) {a b : Ordinal}
  proof: (enumOrd_strictMono hs).lt_iff_lt

中文:
定理 enumOrd_lt_enumOrd
  条件: (hs : ¬ BddAbove s) {a b : 序数}
  证明: (enumOrd_strictMono hs).lt_iff_lt

Depends on / 依赖: enumOrd_strictMono, lt_iff_lt
-/
theorem enumOrd_lt_enumOrd (hs : ¬ BddAbove s) {a b : Ordinal} :
    enumOrd s a < enumOrd s b ↔ a < b :=
  (enumOrd_strictMono hs).lt_iff_lt

/--
theorem `id_le_enumOrd` / 定理 `id_le_enumOrd`

English:
theorem id_le_enumOrd
  given: (hs : ¬ BddAbove s)
  statement: id <= enumOrd s
  proof: (enumOrd_strictMono hs).id_le

中文:
定理 id_le_enumOrd
  条件: (hs : ¬ BddAbove s)
  结论: id <= enumOrd s
  证明: (enumOrd_strictMono hs).id_le

Depends on / 依赖: enumOrd_strictMono, id_le
-/
theorem id_le_enumOrd (hs : ¬ BddAbove s) : id <= enumOrd s :=
  (enumOrd_strictMono hs).id_le

/--
theorem `le_enumOrd_self` / 定理 `le_enumOrd_self`

English:
theorem le_enumOrd_self
  given: (hs : ¬ BddAbove s) {a}
  statement: a <= enumOrd s a
  proof: (enumOrd_strictMono hs).le_apply

中文:
定理 le_enumOrd_self
  条件: (hs : ¬ BddAbove s) {a}
  结论: a <= enumOrd s a
  证明: (enumOrd_strictMono hs).le_apply

Depends on / 依赖: enumOrd_strictMono, le_apply
-/
theorem le_enumOrd_self (hs : ¬ BddAbove s) {a} : a <= enumOrd s a :=
  (enumOrd_strictMono hs).le_apply

/--
theorem `enumOrd_succ_le` / 定理 `enumOrd_succ_le`

English:
theorem enumOrd_succ_le
  given: (hs : ¬ BddAbove s) (ha : a in s) (hb : enumOrd s b < a)
  proof: by
  apply enumOrd_le_of_forall_lt ha
  intro c hc
  rw [lt_succ_iff] at hc
  exact ((enumOrd_strictMono hs).monotone hc).trans_lt hb

中文:
定理 enumOrd_succ_le
  条件: (hs : ¬ BddAbove s) (ha : a in s) (hb : enumOrd s b < a)
  证明: by
  apply enumOrd_le_of_forall_lt ha
  intro c hc
  rw [lt_succ_iff] at hc
  exact ((enumOrd_strictMono hs).monotone hc).trans_lt hb

Depends on / 依赖: enumOrd_le_of_forall_lt, enumOrd_strictMono, lt_succ_iff, monotone, trans_lt
-/
theorem enumOrd_succ_le (hs : ¬ BddAbove s) (ha : a in s) (hb : enumOrd s b < a) :
    enumOrd s (succ b) <= a := by
  apply enumOrd_le_of_forall_lt ha
  intro c hc
  rw [lt_succ_iff] at hc
  exact ((enumOrd_strictMono hs).monotone hc).trans_lt hb

/--
theorem `range_enumOrd` / 定理 `range_enumOrd`

English:
theorem range_enumOrd
  given: (hs : ¬ BddAbove s)
  statement: range (enumOrd s) = s
  proof: by
  ext a
  let t := { b | a <= enumOrd s b }
  constructor
  · rintro ⟨b, rfl⟩
    exact enumOrd_mem hs b
  · intro ha
    refine ⟨sInf t, (enumOrd_le_of_forall_lt ha ?_).antisymm ?_⟩
    · intro b hb
      by_contra! hb'
      exact hb.not_ge (csInf_le' hb')
    · exact csInf_mem (s := t) ⟨a, (en

中文:
定理 range_enumOrd
  条件: (hs : ¬ BddAbove s)
  结论: range (enumOrd s) = s
  证明: by
  ext a
  let t := { b | a <= enumOrd s b }
  constructor
  · rintro ⟨b, rfl⟩
    exact enumOrd_mem hs b
  · intro ha
    refine ⟨sInf t, (enumOrd_le_of_forall_lt ha ?_).antisymm ?_⟩
    · intro b hb
      by_contra! hb'
      exact hb.not_ge (csInf_le' hb')
    · exact csInf_mem (s := t) ⟨a, (en

Depends on / 依赖: antisymm, csInf_le, csInf_mem, enumOrd, enumOrd_le_of_forall_lt, enumOrd_mem, enumOrd_strictMono, hb.not_ge, id_le, not_ge
-/
theorem range_enumOrd (hs : ¬ BddAbove s) : range (enumOrd s) = s := by
  ext a
  let t := { b | a <= enumOrd s b }
  constructor
  · rintro ⟨b, rfl⟩
    exact enumOrd_mem hs b
  · intro ha
    refine ⟨sInf t, (enumOrd_le_of_forall_lt ha ?_).antisymm ?_⟩
    · intro b hb
      by_contra! hb'
      exact hb.not_ge (csInf_le' hb')
    · exact csInf_mem (s := t) ⟨a, (enumOrd_strictMono hs).id_le a⟩

/--
theorem `enumOrd_surjective` / 定理 `enumOrd_surjective`

English:
theorem enumOrd_surjective
  given: (hs : ¬ BddAbove s) {b : Ordinal} (hb : b in s)
  proof: by
  rwa [← range_enumOrd hs] at hb

中文:
定理 enumOrd_surjective
  条件: (hs : ¬ BddAbove s) {b : 序数} (hb : b in s)
  证明: by
  rwa [← range_enumOrd hs] at hb

Depends on / 依赖: range_enumOrd
-/
theorem enumOrd_surjective (hs : ¬ BddAbove s) {b : Ordinal} (hb : b in s) :
    exists a, enumOrd s a = b := by
  rwa [← range_enumOrd hs] at hb

/--
theorem `enumOrd_le_of_subset` / 定理 `enumOrd_le_of_subset`

English:
theorem enumOrd_le_of_subset
  given: {t : Set Ordinal} (hs : ¬ BddAbove s) (hst : s subseteq t)
  proof: by
  intro a
  rw [enumOrd]; rw [enumOrd]
  gcongr with b c
  exacts [enumOrd_nonempty hs a, enumOrd_le_of_subset hs hst c]
termination_by a => a

中文:
定理 enumOrd_le_of_subset
  条件: {t : 集合 序数} (hs : ¬ BddAbove s) (hst : s subseteq t)
  证明: by
  intro a
  rw [enumOrd]; rw [enumOrd]
  gcongr with b c
  exacts [enumOrd_nonempty hs a, enumOrd_le_of_subset hs hst c]
termination_by a => a

Depends on / 依赖: enumOrd, enumOrd_le_of_subset, enumOrd_nonempty, exacts, termination_by
-/
theorem enumOrd_le_of_subset {t : Set Ordinal} (hs : ¬ BddAbove s) (hst : s subseteq t) :
    enumOrd t <= enumOrd s := by
  intro a
  rw [enumOrd]; rw [enumOrd]
  gcongr with b c
  exacts [enumOrd_nonempty hs a, enumOrd_le_of_subset hs hst c]
termination_by a => a

/--
theorem `eq_enumOrd` / 定理 `eq_enumOrd`

English:
theorem eq_enumOrd
  given: (f : Ordinal -> Ordinal) (hs : ¬ BddAbove s)
  proof: by
  constructor
  · rintro rfl
    exact ⟨enumOrd_strictMono hs, range_enumOrd hs⟩
  · rintro ⟨h₁, h₂⟩
    rwa [← (enumOrd_strictMono hs).range_inj h₁, range_enumOrd hs, eq_comm]

中文:
定理 eq_enumOrd
  条件: (f : 序数 -> 序数) (hs : ¬ BddAbove s)
  证明: by
  constructor
  · rintro rfl
    exact ⟨enumOrd_strictMono hs, range_enumOrd hs⟩
  · rintro ⟨h₁, h₂⟩
    rwa [← (enumOrd_strictMono hs).range_inj h₁, range_enumOrd hs, eq_comm]

Depends on / 依赖: enumOrd_strictMono, eq_comm, range_enumOrd, range_inj
-/
theorem eq_enumOrd (f : Ordinal -> Ordinal) (hs : ¬ BddAbove s) :
    enumOrd s = f ↔ StrictMono f ∧ range f = s := by
  constructor
  · rintro rfl
    exact ⟨enumOrd_strictMono hs, range_enumOrd hs⟩
  · rintro ⟨h₁, h₂⟩
    rwa [← (enumOrd_strictMono hs).range_inj h₁, range_enumOrd hs, eq_comm]

/--
theorem `enumOrd_range` / 定理 `enumOrd_range`

English:
theorem enumOrd_range
  given: {f : Ordinal -> Ordinal} (hf : StrictMono f)
  statement: enumOrd (range f) = f
  proof: (eq_enumOrd _ hf.not_bddAbove_range_of_wellFoundedLT).2 ⟨hf, rfl⟩

中文:
定理 enumOrd_range
  条件: {f : 序数 -> 序数} (hf : 严格递增 f)
  结论: enumOrd (range f) = f
  证明: (eq_enumOrd _ hf.not_bddAbove_range_of_wellFoundedLT).2 ⟨hf, rfl⟩

Depends on / 依赖: eq_enumOrd, hf.not_bddAbove_range_of_wellFoundedLT, not_bddAbove_range_of_wellFoundedLT
-/
theorem enumOrd_range {f : Ordinal -> Ordinal} (hf : StrictMono f) : enumOrd (range f) = f :=
  (eq_enumOrd _ hf.not_bddAbove_range_of_wellFoundedLT).2 ⟨hf, rfl⟩

/--
theorem `isNormal_enumOrd` / 定理 `isNormal_enumOrd`

English:
theorem isNormal_enumOrd
  given: (H : forall t subseteq s, t.Nonempty -> BddAbove t -> sSup t in s) (hs : ¬ BddAbove s)
  proof: by
  refine isNormal_iff.2 ⟨enumOrd_strictMono hs, fun o ho a ha => ?_⟩
  trans ⨆ b : Iio o, enumOrd s b
  · refine enumOrd_le_of_forall_lt ?_ (fun b hb => (enumOrd_strictMono hs (lt_succ b)).trans_le ?_)
    · have : Nonempty (Iio o) := ⟨0, ho.bot_lt⟩
      apply H _ _ (range_nonempty _) bddAbove_o

中文:
定理 isNormal_enumOrd
  条件: (H : 对任意 t subseteq s, t.非空 -> BddAbove t -> sSup t in s) (hs : ¬ BddAbove s)
  证明: by
  refine isNormal_iff.2 ⟨enumOrd_strictMono hs, fun o ho a ha => ?_⟩
  trans ⨆ b : Iio o, enumOrd s b
  · refine enumOrd_le_of_forall_lt ?_ (fun b hb => (enumOrd_strictMono hs (lt_succ b)).trans_le ?_)
    · have : Nonempty (Iio o) := ⟨0, ho.bot_lt⟩
      apply H _ _ (range_nonempty _) bddAbove_o

Depends on / 依赖: Nonempty, Ordinal, Ordinal.iSup_le, Ordinal.le_iSup, bddAbove_of_small, bot_lt, enumOrd, enumOrd_le_of_forall_lt, enumOrd_mem, enumOrd_strictMono, ho.bot_lt, ho.succ_lt, iSup_le, isNormal_iff, le_iSup, lt_succ, range_nonempty, succ_lt, trans_le
-/
theorem isNormal_enumOrd (H : forall t subseteq s, t.Nonempty -> BddAbove t -> sSup t in s) (hs : ¬ BddAbove s) :
    IsNormal (enumOrd s) := by
  refine isNormal_iff.2 ⟨enumOrd_strictMono hs, fun o ho a ha => ?_⟩
  trans ⨆ b : Iio o, enumOrd s b
  · refine enumOrd_le_of_forall_lt ?_ (fun b hb => (enumOrd_strictMono hs (lt_succ b)).trans_le ?_)
    · have : Nonempty (Iio o) := ⟨0, ho.bot_lt⟩
      apply H _ _ (range_nonempty _) bddAbove_of_small
      rintro _ ⟨c, rfl⟩
      exact enumOrd_mem hs c
    · exact Ordinal.le_iSup _ (⟨_, ho.succ_lt hb⟩ : Iio o)
  · exact Ordinal.iSup_le fun x => ha _ x.2

@[simp]
/--
theorem `enumOrd_univ` / 定理 `enumOrd_univ`

English:
theorem enumOrd_univ
  statement: enumOrd Set.univ = id
  proof: by
  rw [← range_id]
  exact enumOrd_range strictMono_id

中文:
定理 enumOrd_univ
  结论: enumOrd 集合.univ = id
  证明: by
  rw [← range_id]
  exact enumOrd_range strictMono_id

Depends on / 依赖: enumOrd_range, range_id, strictMono_id
-/
theorem enumOrd_univ : enumOrd Set.univ = id := by
  rw [← range_id]
  exact enumOrd_range strictMono_id

/--
lemma `enumOrd_zero` / 引理 `enumOrd_zero`

English:
lemma enumOrd_zero
  statement: enumOrd s 0 = sInf s
  proof: by rw [enumOrd]; simp

中文:
引理 enumOrd_zero
  结论: enumOrd s 0 = sInf s
  证明: by rw [enumOrd]; simp
-/
@[simp] lemma enumOrd_zero : enumOrd s 0 = sInf s := by rw [enumOrd]; simp

/--
Definition of `enumOrdOrderIso` / `enumOrdOrderIso` 的定义

English:
definition enumOrdOrderIso
  signature: (s : Set Ordinal) (hs : ¬ BddAbove s)
  body: StrictMono.orderIsoOfSurjective (fun o => ⟨_, enumOrd_mem hs o⟩) (enumOrd_strictMono hs) fun s =>
    let ⟨a, ha⟩ := enumOrd_surjective hs s.prop
    ⟨a, Subtype.ext ha⟩

中文:
定义 enumOrdOrderIso
  签名: (s : 集合 序数) (hs : ¬ BddAbove s)
  定义体: StrictMono.orderIsoOfSurjective (fun o => ⟨_, enumOrd_mem hs o⟩) (enumOrd_strictMono hs) fun s =>
    let ⟨a, ha⟩ := enumOrd_surjective hs s.prop
    ⟨a, Subtype.ext ha⟩

Depends on / 依赖: StrictMono, StrictMono.orderIsoOfSurjective, Subtype, Subtype.ext, enumOrd_mem, enumOrd_strictMono, enumOrd_surjective, orderIsoOfSurjective, s.prop
-/
noncomputable def enumOrdOrderIso (s : Set Ordinal) (hs : ¬ BddAbove s) : Ordinal ≃o s :=
  StrictMono.orderIsoOfSurjective (fun o => ⟨_, enumOrd_mem hs o⟩) (enumOrd_strictMono hs) fun s =>
    let ⟨a, ha⟩ := enumOrd_surjective hs s.prop
    ⟨a, Subtype.ext ha⟩

end Ordinal
