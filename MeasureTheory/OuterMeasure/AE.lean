/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The “almost everywhere” filter of co-null sets.

If `μ` is an outer measure or a measure on `α`,
then `MeasureTheory.ae μ` is the filter of co-null sets: `s ∈ ae μ ↔ μ sᶜ = 0`.

In this file we define the filter and prove some basic theorems about it.

## Notation

- `∀ᵐ x ∂μ, p x`: the predicate `p` holds for `μ`-a.e. all `x`;
- `∃ᶠ x ∂μ, p x`: the predicate `p` holds on a set of nonzero measure;
- `f =ᵐ[μ] g`: `f x = g x` for `μ`-a.e. all `x`;
- `f ≤ᵐ[μ] g`: `f x ≤ g x` for `μ`-a.e. all `x`.

## Implementation details

All notation introduced in this file
reducibly unfolds to the corresponding definitions about filters,
so generic lemmas about `Filter.Eventually`, `Filter.EventuallyEq` etc. apply.
However, we restate some lemmas specifically for `ae`.

## Tags

outer measure, measure, almost everywhere
-/

@[expose] public section

open Filter Set
open scoped ENNReal

namespace MeasureTheory

variable {α β F : Type*} [FunLike F (Set α) Real>=0∞] [OuterMeasureClass F α] {μ : F} {s t : Set α}

/-- The “almost everywhere” filter of co-null sets. -/
@[wikidata Q1139334]
/--
Definition of `ae` / `ae` 的定义

English:
definition ae
  signature: (μ : F)
  body: .ofCountableUnion (μ · = 0) (fun _S hSc => (measure_sUnion_null_iff hSc).2) fun _t ht _s hs =>
    measure_mono_null hs ht
deriving CountableInterFilter

中文:
定义 ae
  签名: (μ : F)
  定义体: .ofCountableUnion (μ · = 0) (fun _S hSc => (measure_sUnion_null_iff hSc).2) fun _t ht _s hs =>
    measure_mono_null hs ht
deriving CountableInterFilter

Depends on / 依赖: measure_mono_null, measure_sUnion_null_iff, ofCountableUnion
-/
def ae (μ : F) : Filter α :=
  .ofCountableUnion (μ · = 0) (fun _S hSc => (measure_sUnion_null_iff hSc).2) fun _t ht _s hs =>
    measure_mono_null hs ht
deriving CountableInterFilter

/-- `∀ᵐ a ∂μ, p a` means that `p a` for a.e. `a`, i.e. `p` holds true away from a null set.

This is notation for `Filter.Eventually p (MeasureTheory.ae μ)`. -/
notation3 "forallᵐ "(...)" ∂"μ", "r:(scoped p => Filter.Eventually p <| MeasureTheory.ae μ) => r

/-- `∃ᵐ a ∂μ, p a` means that `p` holds `∂μ`-frequently,
i.e. `p` holds on a set of positive measure.

This is notation for `Filter.Frequently p (MeasureTheory.ae μ)`. -/
notation3 "existsᵐ "(...)" ∂"μ", "r:(scoped P => Filter.Frequently P <| MeasureTheory.ae μ) => r

/-- `f =ᵐ[μ] g` means `f` and `g` are eventually equal along the a.e. filter,
i.e. `f=g` away from a null set.

This is notation for `Filter.EventuallyEq (MeasureTheory.ae μ) f g`. -/
notation3:50 f " =ᵐ[" μ:50 "] " g:50 => Filter.EventuallyEq (MeasureTheory.ae μ) f g

/-- `f ≤ᵐ[μ] g` means `f` is eventually less than `g` along the a.e. filter,
i.e. `f ≤ g` away from a null set.

This is notation for `Filter.EventuallyLE (MeasureTheory.ae μ) f g`. -/
notation3:50 f " <=ᵐ[" μ:50 "] " g:50 => Filter.EventuallyLE (MeasureTheory.ae μ) f g

/--
theorem `mem_ae_iff` / 定理 `mem_ae_iff`

English:
theorem mem_ae_iff
  given: {s : Set α}
  statement: s in ae μ ↔ μ sᶜ = 0
  proof: Iff.rfl

中文:
定理 mem_ae_iff
  条件: {s : 集合 α}
  结论: s in ae μ ↔ μ sᶜ = 0
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0 :=
  Iff.rfl

/--
theorem `ae_iff` / 定理 `ae_iff`

English:
theorem ae_iff
  given: {p : α -> Prop}
  statement: (forallᵐ a ∂μ, p a) ↔ μ { a | ¬p a } = 0
  proof: Iff.rfl

中文:
定理 ae_iff
  条件: {p : α -> 命题}
  结论: (对任意ᵐ a ∂μ, p a) ↔ μ { a | ¬p a } = 0
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ { a | ¬p a } = 0 :=
  Iff.rfl

/--
theorem `compl_mem_ae_iff` / 定理 `compl_mem_ae_iff`

English:
theorem compl_mem_ae_iff
  given: {s : Set α}
  statement: sᶜ in ae μ ↔ μ s = 0
  proof: by simp only [mem_ae_iff, compl_compl]

中文:
定理 compl_mem_ae_iff
  条件: {s : 集合 α}
  结论: sᶜ in ae μ ↔ μ s = 0
  证明: by simp only [mem_ae_iff, compl_compl]

Depends on / 依赖: compl_compl, mem_ae_iff
-/
theorem compl_mem_ae_iff {s : Set α} : sᶜ in ae μ ↔ μ s = 0 := by simp only [mem_ae_iff, compl_compl]

/--
theorem `frequently_ae_iff` / 定理 `frequently_ae_iff`

English:
theorem frequently_ae_iff
  given: {p : α -> Prop}
  statement: (existsᵐ a ∂μ, p a) ↔ μ { a | p a } != 0
  proof: not_congr compl_mem_ae_iff

中文:
定理 frequently_ae_iff
  条件: {p : α -> 命题}
  结论: (存在ᵐ a ∂μ, p a) ↔ μ { a | p a } != 0
  证明: not_congr compl_mem_ae_iff

Depends on / 依赖: compl_mem_ae_iff, not_congr
-/
theorem frequently_ae_iff {p : α -> Prop} : (existsᵐ a ∂μ, p a) ↔ μ { a | p a } != 0 :=
  not_congr compl_mem_ae_iff

/--
theorem `frequently_ae_mem_iff` / 定理 `frequently_ae_mem_iff`

English:
theorem frequently_ae_mem_iff
  given: {s : Set α}
  statement: (existsᵐ a ∂μ, a in s) ↔ μ s != 0
  proof: not_congr compl_mem_ae_iff

中文:
定理 frequently_ae_mem_iff
  条件: {s : 集合 α}
  结论: (存在ᵐ a ∂μ, a in s) ↔ μ s != 0
  证明: not_congr compl_mem_ae_iff

Depends on / 依赖: compl_mem_ae_iff, not_congr
-/
theorem frequently_ae_mem_iff {s : Set α} : (existsᵐ a ∂μ, a in s) ↔ μ s != 0 :=
  not_congr compl_mem_ae_iff

/--
theorem `measure_eq_zero_iff_ae_notMem` / 定理 `measure_eq_zero_iff_ae_notMem`

English:
theorem measure_eq_zero_iff_ae_notMem
  given: {s : Set α}
  statement: μ s = 0 ↔ forallᵐ a ∂μ, a ∉ s
  proof: compl_mem_ae_iff.symm

中文:
定理 measure_eq_zero_iff_ae_notMem
  条件: {s : 集合 α}
  结论: μ s = 0 ↔ 对任意ᵐ a ∂μ, a ∉ s
  证明: compl_mem_ae_iff.symm

Depends on / 依赖: compl_mem_ae_iff, compl_mem_ae_iff.symm
-/
theorem measure_eq_zero_iff_ae_notMem {s : Set α} : μ s = 0 ↔ forallᵐ a ∂μ, a ∉ s :=
  compl_mem_ae_iff.symm

/--
theorem `ae_of_all` / 定理 `ae_of_all`

English:
theorem ae_of_all
  given: {p : α -> Prop} (μ : F)
  statement: (forall a, p a) -> forallᵐ a ∂μ, p a
  proof: Eventually.of_forall

中文:
定理 ae_of_all
  条件: {p : α -> 命题} (μ : F)
  结论: (对任意 a, p a) -> 对任意ᵐ a ∂μ, p a
  证明: Eventually.of_forall

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall
-/
theorem ae_of_all {p : α -> Prop} (μ : F) : (forall a, p a) -> forallᵐ a ∂μ, p a :=
  Eventually.of_forall

/--
theorem `ae_all_iff` / 定理 `ae_all_iff`

English:
theorem ae_all_iff
  given: {ι : Sort*} [Countable ι] {p : α -> ι -> Prop}
  proof: eventually_countable_forall

中文:
定理 ae_all_iff
  条件: {ι : 类型层*} [可数 ι] {p : α -> ι -> 命题}
  证明: eventually_countable_forall

Depends on / 依赖: eventually_countable_forall
-/
theorem ae_all_iff {ι : Sort*} [Countable ι] {p : α -> ι -> Prop} :
    (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i :=
  eventually_countable_forall

/--
theorem `all_ae_of` / 定理 `all_ae_of`

English:
theorem all_ae_of
  given: {ι : Sort*} {p : α -> ι -> Prop} (hp : forallᵐ a ∂μ, forall i, p a i) (i : ι)
  proof: by
  filter_upwards [hp] with a ha using ha i

中文:
定理 all_ae_of
  条件: {ι : 类型层*} {p : α -> ι -> 命题} (hp : 对任意ᵐ a ∂μ, 对任意 i, p a i) (i : ι)
  证明: by
  filter_upwards [hp] with a ha using ha i

Depends on / 依赖: filter_upwards
-/
theorem all_ae_of {ι : Sort*} {p : α -> ι -> Prop} (hp : forallᵐ a ∂μ, forall i, p a i) (i : ι) :
    forallᵐ a ∂μ, p a i := by
  filter_upwards [hp] with a ha using ha i

/--
lemma `ae_iff_of_countable` / 引理 `ae_iff_of_countable`

English:
lemma ae_iff_of_countable
  given: [Countable α] {p : α -> Prop}
  statement: (forallᵐ x ∂μ, p x) ↔ forall x, μ {x} != 0 -> p x
  proof: by
  rw [ae_iff]; rw [measure_null_iff_singleton]
  exacts [forall_congr' fun _ => not_imp_comm, Set.to_countable _]

中文:
引理 ae_iff_of_countable
  条件: [可数 α] {p : α -> 命题}
  结论: (对任意ᵐ x ∂μ, p x) ↔ 对任意 x, μ {x} != 0 -> p x
  证明: by
  rw [ae_iff]; rw [measure_null_iff_singleton]
  exacts [forall_congr' fun _ => not_imp_comm, Set.to_countable _]

Depends on / 依赖: Set.to_countable, ae_iff, exacts, forall_congr, measure_null_iff_singleton, not_imp_comm, to_countable
-/
lemma ae_iff_of_countable [Countable α] {p : α -> Prop} : (forallᵐ x ∂μ, p x) ↔ forall x, μ {x} != 0 -> p x := by
  rw [ae_iff]; rw [measure_null_iff_singleton]
  exacts [forall_congr' fun _ => not_imp_comm, Set.to_countable _]

/--
theorem `ae_ball_iff` / 定理 `ae_ball_iff`

English:
theorem ae_ball_iff
  given: {ι : Type*} {S : Set ι} (hS : S.Countable) {p : α -> forall i in S, Prop}
  proof: eventually_countable_ball hS

中文:
定理 ae_ball_iff
  条件: {ι : 类型} {S : 集合 ι} (hS : S.可数) {p : α -> 对任意 i in S, 命题}
  证明: eventually_countable_ball hS

Depends on / 依赖: eventually_countable_ball
-/
theorem ae_ball_iff {ι : Type*} {S : Set ι} (hS : S.Countable) {p : α -> forall i in S, Prop} :
    (forallᵐ x ∂μ, forall i (hi : i in S), p x i hi) ↔ forall i (hi : i in S), forallᵐ x ∂μ, p x i hi :=
  eventually_countable_ball hS

/--
lemma `ae_eq_refl` / 引理 `ae_eq_refl`

English:
lemma ae_eq_refl
  given: (f : α -> β)
  statement: f =ᵐ[μ] f
  proof: EventuallyEq.rfl

中文:
引理 ae_eq_refl
  条件: (f : α -> β)
  结论: f =ᵐ[μ] f
  证明: EventuallyEq.rfl

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl
-/
lemma ae_eq_refl (f : α -> β) : f =ᵐ[μ] f := EventuallyEq.rfl
/--
lemma `ae_eq_rfl` / 引理 `ae_eq_rfl`

English:
lemma ae_eq_rfl
  given: {f : α -> β}
  statement: f =ᵐ[μ] f
  proof: EventuallyEq.rfl

中文:
引理 ae_eq_rfl
  条件: {f : α -> β}
  结论: f =ᵐ[μ] f
  证明: EventuallyEq.rfl

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl
-/
lemma ae_eq_rfl {f : α -> β} : f =ᵐ[μ] f := EventuallyEq.rfl
/--
lemma `ae_eq_comm` / 引理 `ae_eq_comm`

English:
lemma ae_eq_comm
  given: {f g : α -> β}
  statement: f =ᵐ[μ] g ↔ g =ᵐ[μ] f
  proof: eventuallyEq_comm

中文:
引理 ae_eq_comm
  条件: {f g : α -> β}
  结论: f =ᵐ[μ] g ↔ g =ᵐ[μ] f
  证明: eventuallyEq_comm

Depends on / 依赖: eventuallyEq_comm
-/
lemma ae_eq_comm {f g : α -> β} : f =ᵐ[μ] g ↔ g =ᵐ[μ] f := eventuallyEq_comm

/--
theorem `ae_eq_symm` / 定理 `ae_eq_symm`

English:
theorem ae_eq_symm
  given: {f g : α -> β} (h : f =ᵐ[μ] g)
  statement: g =ᵐ[μ] f
  proof: h.symm

中文:
定理 ae_eq_symm
  条件: {f g : α -> β} (h : f =ᵐ[μ] g)
  结论: g =ᵐ[μ] f
  证明: h.symm

Depends on / 依赖: h.symm
-/
theorem ae_eq_symm {f g : α -> β} (h : f =ᵐ[μ] g) : g =ᵐ[μ] f :=
  h.symm

/--
theorem `ae_eq_trans` / 定理 `ae_eq_trans`

English:
theorem ae_eq_trans
  given: {f g h : α -> β} (h₁ : f =ᵐ[μ] g) (h₂ : g =ᵐ[μ] h)
  statement: f =ᵐ[μ] h
  proof: h₁.trans h₂

中文:
定理 ae_eq_trans
  条件: {f g h : α -> β} (h₁ : f =ᵐ[μ] g) (h₂ : g =ᵐ[μ] h)
  结论: f =ᵐ[μ] h
  证明: h₁.trans h₂
-/
theorem ae_eq_trans {f g h : α -> β} (h₁ : f =ᵐ[μ] g) (h₂ : g =ᵐ[μ] h) : f =ᵐ[μ] h :=
  h₁.trans h₂

/--
lemma `aeEq_iff` / 引理 `aeEq_iff`

English:
lemma aeEq_iff
  given: {f g : α -> β}
  statement: f =ᵐ[μ] g ↔ μ {x | f x != g x} = 0
  proof: by rfl

中文:
引理 aeEq_iff
  条件: {f g : α -> β}
  结论: f =ᵐ[μ] g ↔ μ {x | f x != g x} = 0
  证明: by rfl
-/
lemma aeEq_iff {f g : α -> β} : f =ᵐ[μ] g ↔ μ {x | f x != g x} = 0 := by rfl

/--
lemma `_root_.Set.EqOn.aeEq` / 引理 `_root_.Set.EqOn.aeEq`

English:
lemma _root_.Set.EqOn.aeEq
  given: {f g : α -> β} (h : s.EqOn f g) (h2 : μ sᶜ = 0)
  statement: f =ᵐ[μ] g
  proof: eventuallyEq_of_mem h2 h

中文:
引理 _root_.集合.EqOn.aeEq
  条件: {f g : α -> β} (h : s.EqOn f g) (h2 : μ sᶜ = 0)
  结论: f =ᵐ[μ] g
  证明: eventuallyEq_of_mem h2 h

Depends on / 依赖: eventuallyEq_of_mem
-/
lemma _root_.Set.EqOn.aeEq {f g : α -> β} (h : s.EqOn f g) (h2 : μ sᶜ = 0) : f =ᵐ[μ] g :=
  eventuallyEq_of_mem h2 h

/--
lemma `ae_eq_top` / 引理 `ae_eq_top`

English:
lemma ae_eq_top
  statement: ae μ = ⊤ ↔ forall a, μ {a} != 0
  proof: by
  simp only [Filter.ext_iff, mem_ae_iff, mem_top, ne_eq]
  refine ⟨fun h a ha => by simpa [ha] using (h {a}ᶜ).1, fun h s => ⟨fun hs => ?_, ?_⟩⟩
  · rw [← compl_empty_iff, ← not_nonempty_iff_eq_empty]
    rintro ⟨a, ha⟩
exact h _ measure_mono_null (singleton_subset_iff.2 ha) hs
  · rintro rfl
    

中文:
引理 ae_eq_top
  结论: ae μ = ⊤ ↔ 对任意 a, μ {a} != 0
  证明: by
  simp only [Filter.ext_iff, mem_ae_iff, mem_top, ne_eq]
  refine ⟨fun h a ha => by simpa [ha] using (h {a}ᶜ).1, fun h s => ⟨fun hs => ?_, ?_⟩⟩
  · rw [← compl_empty_iff, ← not_nonempty_iff_eq_empty]
    rintro ⟨a, ha⟩
exact h _ measure_mono_null (singleton_subset_iff.2 ha) hs
  · rintro rfl
    
-/
@[simp] lemma ae_eq_top : ae μ = ⊤ ↔ forall a, μ {a} != 0 := by
  simp only [Filter.ext_iff, mem_ae_iff, mem_top, ne_eq]
  refine ⟨fun h a ha => by simpa [ha] using (h {a}ᶜ).1, fun h s => ⟨fun hs => ?_, ?_⟩⟩
  · rw [← compl_empty_iff, ← not_nonempty_iff_eq_empty]
    rintro ⟨a, ha⟩
exact h _ measure_mono_null (singleton_subset_iff.2 ha) hs
  · rintro rfl
    simp

/--
theorem `ae_le_of_ae_lt` / 定理 `ae_le_of_ae_lt`

English:
theorem ae_le_of_ae_lt
  given: {β : Type*} [Preorder β] {f g : α -> β} (h : forallᵐ x ∂μ, f x < g x)
  proof: h.mono fun _ => le_of_lt

@[simp]

中文:
定理 ae_le_of_ae_lt
  条件: {β : 类型} [预序 β] {f g : α -> β} (h : 对任意ᵐ x ∂μ, f x < g x)
  证明: h.mono fun _ => le_of_lt

@[simp]

Depends on / 依赖: h.mono, le_of_lt
-/
theorem ae_le_of_ae_lt {β : Type*} [Preorder β] {f g : α -> β} (h : forallᵐ x ∂μ, f x < g x) :
    f <=ᵐ[μ] g :=
  h.mono fun _ => le_of_lt

@[simp]
/--
theorem `ae_eq_empty` / 定理 `ae_eq_empty`

English:
theorem ae_eq_empty
  statement: s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0
  proof: eventuallyEq_empty.trans by simp only [ae_iff, Classical.not_not, ofPred_mem_eq]

中文:
定理 ae_eq_empty
  结论: s =ᵐ[μ] (∅ : 集合 α) ↔ μ s = 0
  证明: eventuallyEq_empty.trans by simp only [ae_iff, Classical.not_not, ofPred_mem_eq]

Depends on / 依赖: Classical, Classical.not_not, ae_iff, eventuallyEq_empty, eventuallyEq_empty.trans, not_not, ofPred_mem_eq
-/
theorem ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0 :=
eventuallyEq_empty.trans by simp only [ae_iff, Classical.not_not, ofPred_mem_eq]

-- The priority should be higher than `eventuallyEq_univ`.
@[simp high]
/--
theorem `ae_eq_univ` / 定理 `ae_eq_univ`

English:
theorem ae_eq_univ
  statement: s =ᵐ[μ] (univ : Set α) ↔ μ sᶜ = 0
  proof: eventuallyEq_univ

中文:
定理 ae_eq_univ
  结论: s =ᵐ[μ] (univ : 集合 α) ↔ μ sᶜ = 0
  证明: eventuallyEq_univ

Depends on / 依赖: eventuallyEq_univ
-/
theorem ae_eq_univ : s =ᵐ[μ] (univ : Set α) ↔ μ sᶜ = 0 :=
  eventuallyEq_univ

/--
theorem `ae_le_set` / 定理 `ae_le_set`

English:
theorem ae_le_set
  statement: s <=ᵐ[μ] t ↔ μ (s \ t) = 0
  proof: calc
    s <=ᵐ[μ] t ↔ forallᵐ x ∂μ, x in s -> x in t := Iff.rfl
    _ ↔ μ (s \ t) = 0 := by simp [ae_iff]; rfl

中文:
定理 ae_le_set
  结论: s <=ᵐ[μ] t ↔ μ (s \ t) = 0
  证明: calc
    s <=ᵐ[μ] t ↔ forallᵐ x ∂μ, x in s -> x in t := Iff.rfl
    _ ↔ μ (s \ t) = 0 := by simp [ae_iff]; rfl

Depends on / 依赖: Iff.rfl, ae_iff
-/
theorem ae_le_set : s <=ᵐ[μ] t ↔ μ (s \ t) = 0 :=
  calc
    s <=ᵐ[μ] t ↔ forallᵐ x ∂μ, x in s -> x in t := Iff.rfl
    _ ↔ μ (s \ t) = 0 := by simp [ae_iff]; rfl

/--
theorem `ae_le_set_inter` / 定理 `ae_le_set_inter`

English:
theorem ae_le_set_inter
  given: {s' t' : Set α} (h : s <=ᵐ[μ] t) (h' : s' <=ᵐ[μ] t')
  proof: h.inter h'

中文:
定理 ae_le_set_inter
  条件: {s' t' : 集合 α} (h : s <=ᵐ[μ] t) (h' : s' <=ᵐ[μ] t')
  证明: h.inter h'

Depends on / 依赖: h.inter
-/
theorem ae_le_set_inter {s' t' : Set α} (h : s <=ᵐ[μ] t) (h' : s' <=ᵐ[μ] t') :
    (s inter s' : Set α) <=ᵐ[μ] (t inter t' : Set α) :=
  h.inter h'

/--
theorem `ae_le_set_union` / 定理 `ae_le_set_union`

English:
theorem ae_le_set_union
  given: {s' t' : Set α} (h : s <=ᵐ[μ] t) (h' : s' <=ᵐ[μ] t')
  proof: h.union h'

中文:
定理 ae_le_set_union
  条件: {s' t' : 集合 α} (h : s <=ᵐ[μ] t) (h' : s' <=ᵐ[μ] t')
  证明: h.union h'

Depends on / 依赖: h.union
-/
theorem ae_le_set_union {s' t' : Set α} (h : s <=ᵐ[μ] t) (h' : s' <=ᵐ[μ] t') :
    (s union s' : Set α) <=ᵐ[μ] (t union t' : Set α) :=
  h.union h'

set_option backward.isDefEq.respectTransparency false in
/--
theorem `union_ae_eq_right` / 定理 `union_ae_eq_right`

English:
theorem union_ae_eq_right
  statement: (s union t : Set α) =ᵐ[μ] t ↔ μ (s \ t) = 0
  proof: by
  simp [eventuallyLE_antisymm_iff, ae_le_set, union_sdiff_right,
    sdiff_eq_empty.2 Set.subset_union_right]

中文:
定理 union_ae_eq_right
  结论: (s union t : 集合 α) =ᵐ[μ] t ↔ μ (s \ t) = 0
  证明: by
  simp [eventuallyLE_antisymm_iff, ae_le_set, union_sdiff_right,
    sdiff_eq_empty.2 Set.subset_union_right]

Depends on / 依赖: Set.subset_union_right, ae_le_set, eventuallyLE_antisymm_iff, sdiff_eq_empty, subset_union_right, union_sdiff_right
-/
theorem union_ae_eq_right : (s union t : Set α) =ᵐ[μ] t ↔ μ (s \ t) = 0 := by
  simp [eventuallyLE_antisymm_iff, ae_le_set, union_sdiff_right,
    sdiff_eq_empty.2 Set.subset_union_right]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sdiff_ae_eq_self` / 定理 `sdiff_ae_eq_self`

English:
theorem sdiff_ae_eq_self
  statement: (s \ t : Set α) =ᵐ[μ] s ↔ μ (s inter t) = 0
  proof: by
  simp [eventuallyLE_antisymm_iff, ae_le_set]

@[deprecated (since := "2026-06-03")] alias diff_ae_eq_self := sdiff_ae_eq_self

中文:
定理 sdiff_ae_eq_self
  结论: (s \ t : 集合 α) =ᵐ[μ] s ↔ μ (s inter t) = 0
  证明: by
  simp [eventuallyLE_antisymm_iff, ae_le_set]

@[deprecated (since := "2026-06-03")] alias diff_ae_eq_self := sdiff_ae_eq_self

Depends on / 依赖: ae_le_set, eventuallyLE_antisymm_iff
-/
theorem sdiff_ae_eq_self : (s \ t : Set α) =ᵐ[μ] s ↔ μ (s inter t) = 0 := by
  simp [eventuallyLE_antisymm_iff, ae_le_set]

@[deprecated (since := "2026-06-03")] alias diff_ae_eq_self := sdiff_ae_eq_self

/--
theorem `sdiff_null_ae_eq_self` / 定理 `sdiff_null_ae_eq_self`

English:
theorem sdiff_null_ae_eq_self
  given: (ht : μ t = 0)
  statement: (s \ t : Set α) =ᵐ[μ] s
  proof: sdiff_ae_eq_self.mpr (measure_mono_null inter_subset_right ht)

@[deprecated (since := "2026-06-03")] alias diff_null_ae_eq_self := sdiff_null_ae_eq_self

中文:
定理 sdiff_null_ae_eq_self
  条件: (ht : μ t = 0)
  结论: (s \ t : 集合 α) =ᵐ[μ] s
  证明: sdiff_ae_eq_self.mpr (measure_mono_null inter_subset_right ht)

@[deprecated (since := "2026-06-03")] alias diff_null_ae_eq_self := sdiff_null_ae_eq_self

Depends on / 依赖: inter_subset_right, measure_mono_null, sdiff_ae_eq_self, sdiff_ae_eq_self.mpr
-/
theorem sdiff_null_ae_eq_self (ht : μ t = 0) : (s \ t : Set α) =ᵐ[μ] s :=
  sdiff_ae_eq_self.mpr (measure_mono_null inter_subset_right ht)

@[deprecated (since := "2026-06-03")] alias diff_null_ae_eq_self := sdiff_null_ae_eq_self

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ae_eq_set` / 定理 `ae_eq_set`

English:
theorem ae_eq_set
  given: {s t : Set α}
  statement: s =ᵐ[μ] t ↔ μ (s \ t) = 0 ∧ μ (t \ s) = 0
  proof: by
  simp [eventuallyLE_antisymm_iff, ae_le_set]

中文:
定理 ae_eq_set
  条件: {s t : 集合 α}
  结论: s =ᵐ[μ] t ↔ μ (s \ t) = 0 ∧ μ (t \ s) = 0
  证明: by
  simp [eventuallyLE_antisymm_iff, ae_le_set]

Depends on / 依赖: ae_le_set, eventuallyLE_antisymm_iff
-/
theorem ae_eq_set {s t : Set α} : s =ᵐ[μ] t ↔ μ (s \ t) = 0 ∧ μ (t \ s) = 0 := by
  simp [eventuallyLE_antisymm_iff, ae_le_set]

open scoped symmDiff in
@[simp]
/--
theorem `measure_symmDiff_eq_zero_iff` / 定理 `measure_symmDiff_eq_zero_iff`

English:
theorem measure_symmDiff_eq_zero_iff
  given: {s t : Set α}
  statement: μ (s ∆ t) = 0 ↔ s =ᵐ[μ] t
  proof: by
  simp [ae_eq_set, symmDiff_def]

中文:
定理 measure_symmDiff_eq_zero_iff
  条件: {s t : 集合 α}
  结论: μ (s ∆ t) = 0 ↔ s =ᵐ[μ] t
  证明: by
  simp [ae_eq_set, symmDiff_def]

Depends on / 依赖: ae_eq_set, symmDiff_def
-/
theorem measure_symmDiff_eq_zero_iff {s t : Set α} : μ (s ∆ t) = 0 ↔ s =ᵐ[μ] t := by
  simp [ae_eq_set, symmDiff_def]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ae_eq_set_compl_compl` / 定理 `ae_eq_set_compl_compl`

English:
theorem ae_eq_set_compl_compl
  given: {s t : Set α}
  statement: sᶜ =ᵐ[μ] tᶜ ↔ s =ᵐ[μ] t
  proof: by
  simp only [← measure_symmDiff_eq_zero_iff, compl_symmDiff_compl]

中文:
定理 ae_eq_set_compl_compl
  条件: {s t : 集合 α}
  结论: sᶜ =ᵐ[μ] tᶜ ↔ s =ᵐ[μ] t
  证明: by
  simp only [← measure_symmDiff_eq_zero_iff, compl_symmDiff_compl]

Depends on / 依赖: compl_symmDiff_compl, measure_symmDiff_eq_zero_iff
-/
theorem ae_eq_set_compl_compl {s t : Set α} : sᶜ =ᵐ[μ] tᶜ ↔ s =ᵐ[μ] t := by
  simp only [← measure_symmDiff_eq_zero_iff, compl_symmDiff_compl]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ae_eq_set_compl` / 定理 `ae_eq_set_compl`

English:
theorem ae_eq_set_compl
  given: {s t : Set α}
  statement: sᶜ =ᵐ[μ] t ↔ s =ᵐ[μ] tᶜ
  proof: by
  rw [← ae_eq_set_compl_compl]; rw [compl_compl]

中文:
定理 ae_eq_set_compl
  条件: {s t : 集合 α}
  结论: sᶜ =ᵐ[μ] t ↔ s =ᵐ[μ] tᶜ
  证明: by
  rw [← ae_eq_set_compl_compl]; rw [compl_compl]

Depends on / 依赖: ae_eq_set_compl_compl, compl_compl
-/
theorem ae_eq_set_compl {s t : Set α} : sᶜ =ᵐ[μ] t ↔ s =ᵐ[μ] tᶜ := by
  rw [← ae_eq_set_compl_compl]; rw [compl_compl]

/--
theorem `ae_eq_set_inter` / 定理 `ae_eq_set_inter`

English:
theorem ae_eq_set_inter
  given: {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t')
  proof: h.inter h'

中文:
定理 ae_eq_set_inter
  条件: {s' t' : 集合 α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t')
  证明: h.inter h'

Depends on / 依赖: h.inter
-/
theorem ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') :
    (s inter s' : Set α) =ᵐ[μ] (t inter t' : Set α) :=
  h.inter h'

/--
theorem `ae_eq_set_union` / 定理 `ae_eq_set_union`

English:
theorem ae_eq_set_union
  given: {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t')
  proof: h.union h'

中文:
定理 ae_eq_set_union
  条件: {s' t' : 集合 α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t')
  证明: h.union h'

Depends on / 依赖: h.union
-/
theorem ae_eq_set_union {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') :
    (s union s' : Set α) =ᵐ[μ] (t union t' : Set α) :=
  h.union h'

/--
theorem `ae_eq_set_sdiff` / 定理 `ae_eq_set_sdiff`

English:
theorem ae_eq_set_sdiff
  given: {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t')
  proof: h.diff h'

@[deprecated (since := "2026-06-03")] alias ae_eq_set_diff := ae_eq_set_sdiff

中文:
定理 ae_eq_set_sdiff
  条件: {s' t' : 集合 α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t')
  证明: h.diff h'

@[deprecated (since := "2026-06-03")] alias ae_eq_set_diff := ae_eq_set_sdiff

Depends on / 依赖: h.diff
-/
theorem ae_eq_set_sdiff {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') :
    s \ s' =ᵐ[μ] t \ t' :=
  h.diff h'

@[deprecated (since := "2026-06-03")] alias ae_eq_set_diff := ae_eq_set_sdiff

open scoped symmDiff in
/--
theorem `ae_eq_set_symmDiff` / 定理 `ae_eq_set_symmDiff`

English:
theorem ae_eq_set_symmDiff
  given: {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t')
  proof: h.symmDiff h'

中文:
定理 ae_eq_set_symmDiff
  条件: {s' t' : 集合 α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t')
  证明: h.symmDiff h'

Depends on / 依赖: h.symmDiff, symmDiff
-/
theorem ae_eq_set_symmDiff {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') :
    s ∆ s' =ᵐ[μ] t ∆ t' :=
  h.symmDiff h'

set_option backward.isDefEq.respectTransparency false in
/--
theorem `union_ae_eq_univ_of_ae_eq_univ_left` / 定理 `union_ae_eq_univ_of_ae_eq_univ_left`

English:
theorem union_ae_eq_univ_of_ae_eq_univ_left
  given: (h : s =ᵐ[μ] univ)
  statement: (s union t : Set α) =ᵐ[μ] univ
  proof: (ae_eq_set_union h (ae_eq_refl t)).trans by rw [univ_union]

中文:
定理 union_ae_eq_univ_of_ae_eq_univ_left
  条件: (h : s =ᵐ[μ] univ)
  结论: (s union t : 集合 α) =ᵐ[μ] univ
  证明: (ae_eq_set_union h (ae_eq_refl t)).trans by rw [univ_union]

Depends on / 依赖: ae_eq_refl, ae_eq_set_union, univ_union
-/
theorem union_ae_eq_univ_of_ae_eq_univ_left (h : s =ᵐ[μ] univ) : (s union t : Set α) =ᵐ[μ] univ :=
(ae_eq_set_union h (ae_eq_refl t)).trans by rw [univ_union]

/--
theorem `union_ae_eq_univ_of_ae_eq_univ_right` / 定理 `union_ae_eq_univ_of_ae_eq_univ_right`

English:
theorem union_ae_eq_univ_of_ae_eq_univ_right
  given: (h : t =ᵐ[μ] univ)
  statement: (s union t : Set α) =ᵐ[μ] univ
  proof: by
  convert! ae_eq_set_union (ae_eq_refl s) h
  rw [union_univ]

中文:
定理 union_ae_eq_univ_of_ae_eq_univ_right
  条件: (h : t =ᵐ[μ] univ)
  结论: (s union t : 集合 α) =ᵐ[μ] univ
  证明: by
  convert! ae_eq_set_union (ae_eq_refl s) h
  rw [union_univ]

Depends on / 依赖: ae_eq_refl, ae_eq_set_union, convert, union_univ
-/
theorem union_ae_eq_univ_of_ae_eq_univ_right (h : t =ᵐ[μ] univ) : (s union t : Set α) =ᵐ[μ] univ := by
  convert! ae_eq_set_union (ae_eq_refl s) h
  rw [union_univ]

/--
theorem `union_ae_eq_right_of_ae_eq_empty` / 定理 `union_ae_eq_right_of_ae_eq_empty`

English:
theorem union_ae_eq_right_of_ae_eq_empty
  given: (h : s =ᵐ[μ] (∅ : Set α))
  statement: (s union t : Set α) =ᵐ[μ] t
  proof: by
  convert! ae_eq_set_union h (ae_eq_refl t)
  rw [empty_union]

中文:
定理 union_ae_eq_right_of_ae_eq_empty
  条件: (h : s =ᵐ[μ] (∅ : 集合 α))
  结论: (s union t : 集合 α) =ᵐ[μ] t
  证明: by
  convert! ae_eq_set_union h (ae_eq_refl t)
  rw [empty_union]

Depends on / 依赖: ae_eq_refl, ae_eq_set_union, convert, empty_union
-/
theorem union_ae_eq_right_of_ae_eq_empty (h : s =ᵐ[μ] (∅ : Set α)) : (s union t : Set α) =ᵐ[μ] t := by
  convert! ae_eq_set_union h (ae_eq_refl t)
  rw [empty_union]

/--
theorem `union_ae_eq_left_of_ae_eq_empty` / 定理 `union_ae_eq_left_of_ae_eq_empty`

English:
theorem union_ae_eq_left_of_ae_eq_empty
  given: (h : t =ᵐ[μ] (∅ : Set α))
  statement: (s union t : Set α) =ᵐ[μ] s
  proof: by
  convert! ae_eq_set_union (ae_eq_refl s) h
  rw [union_empty]

中文:
定理 union_ae_eq_left_of_ae_eq_empty
  条件: (h : t =ᵐ[μ] (∅ : 集合 α))
  结论: (s union t : 集合 α) =ᵐ[μ] s
  证明: by
  convert! ae_eq_set_union (ae_eq_refl s) h
  rw [union_empty]

Depends on / 依赖: ae_eq_refl, ae_eq_set_union, convert, union_empty
-/
theorem union_ae_eq_left_of_ae_eq_empty (h : t =ᵐ[μ] (∅ : Set α)) : (s union t : Set α) =ᵐ[μ] s := by
  convert! ae_eq_set_union (ae_eq_refl s) h
  rw [union_empty]

/--
theorem `inter_ae_eq_right_of_ae_eq_univ` / 定理 `inter_ae_eq_right_of_ae_eq_univ`

English:
theorem inter_ae_eq_right_of_ae_eq_univ
  given: (h : s =ᵐ[μ] univ)
  statement: (s inter t : Set α) =ᵐ[μ] t
  proof: by
  convert! ae_eq_set_inter h (ae_eq_refl t)
  rw [univ_inter]

中文:
定理 inter_ae_eq_right_of_ae_eq_univ
  条件: (h : s =ᵐ[μ] univ)
  结论: (s inter t : 集合 α) =ᵐ[μ] t
  证明: by
  convert! ae_eq_set_inter h (ae_eq_refl t)
  rw [univ_inter]

Depends on / 依赖: ae_eq_refl, ae_eq_set_inter, convert, univ_inter
-/
theorem inter_ae_eq_right_of_ae_eq_univ (h : s =ᵐ[μ] univ) : (s inter t : Set α) =ᵐ[μ] t := by
  convert! ae_eq_set_inter h (ae_eq_refl t)
  rw [univ_inter]

/--
theorem `inter_ae_eq_left_of_ae_eq_univ` / 定理 `inter_ae_eq_left_of_ae_eq_univ`

English:
theorem inter_ae_eq_left_of_ae_eq_univ
  given: (h : t =ᵐ[μ] univ)
  statement: (s inter t : Set α) =ᵐ[μ] s
  proof: by
  convert! ae_eq_set_inter (ae_eq_refl s) h
  rw [inter_univ]

中文:
定理 inter_ae_eq_left_of_ae_eq_univ
  条件: (h : t =ᵐ[μ] univ)
  结论: (s inter t : 集合 α) =ᵐ[μ] s
  证明: by
  convert! ae_eq_set_inter (ae_eq_refl s) h
  rw [inter_univ]

Depends on / 依赖: ae_eq_refl, ae_eq_set_inter, convert, inter_univ
-/
theorem inter_ae_eq_left_of_ae_eq_univ (h : t =ᵐ[μ] univ) : (s inter t : Set α) =ᵐ[μ] s := by
  convert! ae_eq_set_inter (ae_eq_refl s) h
  rw [inter_univ]

/--
theorem `inter_ae_eq_empty_of_ae_eq_empty_left` / 定理 `inter_ae_eq_empty_of_ae_eq_empty_left`

English:
theorem inter_ae_eq_empty_of_ae_eq_empty_left
  given: (h : s =ᵐ[μ] (∅ : Set α))
  proof: by
  convert! ae_eq_set_inter h (ae_eq_refl t)
  rw [empty_inter]

中文:
定理 inter_ae_eq_empty_of_ae_eq_empty_left
  条件: (h : s =ᵐ[μ] (∅ : 集合 α))
  证明: by
  convert! ae_eq_set_inter h (ae_eq_refl t)
  rw [empty_inter]

Depends on / 依赖: ae_eq_refl, ae_eq_set_inter, convert, empty_inter
-/
theorem inter_ae_eq_empty_of_ae_eq_empty_left (h : s =ᵐ[μ] (∅ : Set α)) :
    (s inter t : Set α) =ᵐ[μ] (∅ : Set α) := by
  convert! ae_eq_set_inter h (ae_eq_refl t)
  rw [empty_inter]

/--
theorem `inter_ae_eq_empty_of_ae_eq_empty_right` / 定理 `inter_ae_eq_empty_of_ae_eq_empty_right`

English:
theorem inter_ae_eq_empty_of_ae_eq_empty_right
  given: (h : t =ᵐ[μ] (∅ : Set α))
  proof: by
  convert! ae_eq_set_inter (ae_eq_refl s) h
  rw [inter_empty]

中文:
定理 inter_ae_eq_empty_of_ae_eq_empty_right
  条件: (h : t =ᵐ[μ] (∅ : 集合 α))
  证明: by
  convert! ae_eq_set_inter (ae_eq_refl s) h
  rw [inter_empty]

Depends on / 依赖: ae_eq_refl, ae_eq_set_inter, convert, inter_empty
-/
theorem inter_ae_eq_empty_of_ae_eq_empty_right (h : t =ᵐ[μ] (∅ : Set α)) :
    (s inter t : Set α) =ᵐ[μ] (∅ : Set α) := by
  convert! ae_eq_set_inter (ae_eq_refl s) h
  rw [inter_empty]

/--
theorem `ae_eq_set_biInter` / 定理 `ae_eq_set_biInter`

English:
theorem ae_eq_set_biInter
  statement: {s : Set β} (hs : s.Countable) {t t' : β -> Set α}
  proof: .countable_bInter hs h

中文:
定理 ae_eq_set_bi整数er
  结论: {s : 集合 β} (hs : s.可数) {t t' : β -> 集合 α}
  证明: .countable_bInter hs h

Depends on / 依赖: countable_bInter
-/
theorem ae_eq_set_biInter {s : Set β} (hs : s.Countable) {t t' : β -> Set α}
    (h : forall b in s, t b =ᵐ[μ] t' b) :
    (⋂ b in s, t b : Set α) =ᵐ[μ] (⋂ b in s, t' b : Set α) :=
  .countable_bInter hs h

/--
theorem `ae_eq_set_biUnion` / 定理 `ae_eq_set_biUnion`

English:
theorem ae_eq_set_biUnion
  statement: {s : Set β} (hs : s.Countable) {t t' : β -> Set α}
  proof: .countable_bUnion hs h

中文:
定理 ae_eq_set_biUnion
  结论: {s : 集合 β} (hs : s.可数) {t t' : β -> 集合 α}
  证明: .countable_bUnion hs h

Depends on / 依赖: countable_bUnion
-/
theorem ae_eq_set_biUnion {s : Set β} (hs : s.Countable) {t t' : β -> Set α}
    (h : forall b in s, t b =ᵐ[μ] t' b) :
    (⋃ b in s, t b : Set α) =ᵐ[μ] (⋃ b in s, t' b : Set α) :=
  .countable_bUnion hs h

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `_root_.Set.mulIndicator_ae_eq_one` / 定理 `_root_.Set.mulIndicator_ae_eq_one`

English:
theorem _root_.Set.mulIndicator_ae_eq_one
  given: {M : Type*} [One M] {f : α -> M} {s : Set α}
  proof: by
  simp [EventuallyEq, eventually_iff, ae, compl_ofPred]; rfl

中文:
定理 _root_.集合.mulIndicator_ae_eq_one
  条件: {M : 类型} [幺 M] {f : α -> M} {s : 集合 α}
  证明: by
  simp [EventuallyEq, eventually_iff, ae, compl_ofPred]; rfl

Depends on / 依赖: EventuallyEq, compl_ofPred, eventually_iff
-/
theorem _root_.Set.mulIndicator_ae_eq_one {M : Type*} [One M] {f : α -> M} {s : Set α} :
    s.mulIndicator f =ᵐ[μ] 1 ↔ μ (s inter f.mulSupport) = 0 := by
  simp [EventuallyEq, eventually_iff, ae, compl_ofPred]; rfl

/-- If `s ⊆ t` modulo a set of measure `0`, then `μ s ≤ μ t`. -/
@[mono]
/--
theorem `measure_mono_ae` / 定理 `measure_mono_ae`

English:
theorem measure_mono_ae
  given: (H : s <=ᵐ[μ] t)
  statement: μ s <= μ t
  proof: calc
    μ s <= μ (s union t) := measure_mono subset_union_left
    _ = μ (t union s \ t) := by rw [union_sdiff_self, Set.union_comm]
    _ <= μ t + μ (s \ t) := measure_union_le _ _
    _ = μ t := by rw [ae_le_set.1 H, add_zero]

alias _root_.Filter.EventuallyLE.measure_le := measure_mono_ae

中文:
定理 measure_mono_ae
  条件: (H : s <=ᵐ[μ] t)
  结论: μ s <= μ t
  证明: calc
    μ s <= μ (s union t) := measure_mono subset_union_left
    _ = μ (t union s \ t) := by rw [union_sdiff_self, Set.union_comm]
    _ <= μ t + μ (s \ t) := measure_union_le _ _
    _ = μ t := by rw [ae_le_set.1 H, add_zero]

alias _root_.Filter.EventuallyLE.measure_le := measure_mono_ae

Depends on / 依赖: Set.union_comm, add_zero, ae_le_set, measure_mono, measure_union_le, subset_union_left, union_comm, union_sdiff_self
-/
theorem measure_mono_ae (H : s <=ᵐ[μ] t) : μ s <= μ t :=
  calc
    μ s <= μ (s union t) := measure_mono subset_union_left
    _ = μ (t union s \ t) := by rw [union_sdiff_self, Set.union_comm]
    _ <= μ t + μ (s \ t) := measure_union_le _ _
    _ = μ t := by rw [ae_le_set.1 H, add_zero]

alias _root_.Filter.EventuallyLE.measure_le := measure_mono_ae

/--
theorem `measure_congr` / 定理 `measure_congr`

English:
theorem measure_congr
  given: (H : s =ᵐ[μ] t)
  statement: μ s = μ t
  proof: le_antisymm H.le.measure_le H.symm.le.measure_le

alias _root_.Filter.EventuallyEq.measure_eq := measure_congr

中文:
定理 measure_congr
  条件: (H : s =ᵐ[μ] t)
  结论: μ s = μ t
  证明: le_antisymm H.le.measure_le H.symm.le.measure_le

alias _root_.Filter.EventuallyEq.measure_eq := measure_congr

Depends on / 依赖: H.le.measure_le, H.symm.le.measure_le, le_antisymm, measure_le
-/
theorem measure_congr (H : s =ᵐ[μ] t) : μ s = μ t :=
  le_antisymm H.le.measure_le H.symm.le.measure_le

alias _root_.Filter.EventuallyEq.measure_eq := measure_congr

/--
theorem `measure_mono_null_ae` / 定理 `measure_mono_null_ae`

English:
theorem measure_mono_null_ae
  given: (H : s <=ᵐ[μ] t) (ht : μ t = 0)
  statement: μ s = 0
  proof: nonpos_iff_eq_zero.1 ht ▸ H.measure_le

中文:
定理 measure_mono_null_ae
  条件: (H : s <=ᵐ[μ] t) (ht : μ t = 0)
  结论: μ s = 0
  证明: nonpos_iff_eq_zero.1 ht ▸ H.measure_le

Depends on / 依赖: H.measure_le, measure_le, nonpos_iff_eq_zero
-/
theorem measure_mono_null_ae (H : s <=ᵐ[μ] t) (ht : μ t = 0) : μ s = 0 :=
nonpos_iff_eq_zero.1 ht ▸ H.measure_le

end MeasureTheory
