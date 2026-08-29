/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.OfMap

/-!
# Subsets of finite types

In a `Fintype`, all `Set`s are automatically `Finset`s, and there are only finitely many of them.

## Main results

* `Set.toFinset`: convert a subset of a finite type to a `Finset`
* `Finset.fintypeCoeSort`: `((s : Finset α) : Type*)` is a finite type
* `Fintype.finsetEquivSet`: `Finset α` and `Set α` are equivalent if `α` is a `Fintype`
-/

@[expose] public section

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset

namespace Set

variable {s t : Set α}

/--
Definition of `toFinset` / `toFinset` 的定义

English:
definition toFinset
  signature: (s : Set α) [Fintype s]
  body: (@Finset.univ s _).map Function.Embedding.subtype _

@[congr]

中文:
定义 toFinset
  签名: (s : Set α) [Fintype s]
  定义体: (@Finset.univ s _).map Function.Embedding.subtype _

@[congr]

Depends on / 依赖: Embedding, Finset, Finset.univ, Function, Function.Embedding.subtype, subtype
-/
def toFinset (s : Set α) [Fintype s] : Finset α :=
(@Finset.univ s _).map Function.Embedding.subtype _

@[congr]
/--
theorem `toFinset_congr` / 定理 `toFinset_congr`

English:
theorem toFinset_congr
  given: {s t : Set α} [Fintype s] [Fintype t] (h : s = t)
  proof: by subst h; congr!

@[simp, grind =]

中文:
定理 toFinset_congr
  条件: {s t : Set α} [Fintype s] [Fintype t] (h : s = t)
  证明: by subst h; congr!

@[simp, grind =]
-/
theorem toFinset_congr {s t : Set α} [Fintype s] [Fintype t] (h : s = t) :
    toFinset s = toFinset t := by subst h; congr!

@[simp, grind =]
/--
theorem `mem_toFinset` / 定理 `mem_toFinset`

English:
theorem mem_toFinset
  given: {s : Set α} [Fintype s] {a : α}
  statement: a in s.toFinset ↔ a in s
  proof: by
  simp [toFinset]

中文:
定理 mem_toFinset
  条件: {s : Set α} [Fintype s] {a : α}
  结论: a in s.toFinset ↔ a in s
  证明: by
  simp [toFinset]

Depends on / 依赖: toFinset
-/
theorem mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.toFinset ↔ a in s := by
  simp [toFinset]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toFinset_ofFinset` / 定理 `toFinset_ofFinset`

English:
theorem toFinset_ofFinset
  given: {p : Set α} (s : Finset α) (H : forall x, x in s ↔ x in p)
  proof: Finset.ext fun x => by rw [@mem_toFinset _ _ (id _), H]

中文:
定理 toFinset_ofFinset
  条件: {p : Set α} (s : Finset α) (H : 对任意 x, x in s ↔ x in p)
  证明: Finset.ext fun x => by rw [@mem_toFinset _ _ (id _), H]

Depends on / 依赖: Finset, Finset.ext, mem_toFinset
-/
theorem toFinset_ofFinset {p : Set α} (s : Finset α) (H : forall x, x in s ↔ x in p) :
    @Set.toFinset _ p (Fintype.ofFinset s H) = s :=
  Finset.ext fun x => by rw [@mem_toFinset _ _ (id _), H]

/--
Definition of `decidableMemOfFintype` / `decidableMemOfFintype` 的定义

English:
definition decidableMemOfFintype
  signature: [DecidableEq α] (s : Set α) [Fintype s] (a)
  body: decidable_of_iff _ mem_toFinset

@[simp]

中文:
定义 decidableMemOfFintype
  签名: [DecidableEq α] (s : Set α) [Fintype s] (a)
  定义体: decidable_of_iff _ mem_toFinset

@[simp]

Depends on / 依赖: decidable_of_iff, mem_toFinset
-/
def decidableMemOfFintype [DecidableEq α] (s : Set α) [Fintype s] (a) : Decidable (a in s) :=
  decidable_of_iff _ mem_toFinset

@[simp]
/--
theorem `coe_toFinset` / 定理 `coe_toFinset`

English:
theorem coe_toFinset
  given: (s : Set α) [Fintype s]
  statement: (↑s.toFinset : Set α) = s
  proof: Set.ext fun _ => mem_toFinset

@[simp]

中文:
定理 coe_toFinset
  条件: (s : Set α) [Fintype s]
  结论: (↑s.toFinset : Set α) = s
  证明: Set.ext fun _ => mem_toFinset

@[simp]

Depends on / 依赖: Set.ext, mem_toFinset
-/
theorem coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : Set α) = s :=
  Set.ext fun _ => mem_toFinset

@[simp]
/--
theorem `toFinset_nonempty` / 定理 `toFinset_nonempty`

English:
theorem toFinset_nonempty
  given: {s : Set α} [Fintype s]
  statement: s.toFinset.Nonempty ↔ s.Nonempty
  proof: by
  rw [← Finset.coe_nonempty]; rw [coe_toFinset]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.toFinset_nonempty_of_nonempty⟩ := toFinset_nonempty

@[simp]

中文:
定理 toFinset_nonempty
  条件: {s : Set α} [Fintype s]
  结论: s.toFinset.Nonempty ↔ s.Nonempty
  证明: by
  rw [← Finset.coe_nonempty]; rw [coe_toFinset]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.toFinset_nonempty_of_nonempty⟩ := toFinset_nonempty

@[simp]

Depends on / 依赖: Finset, Finset.coe_nonempty, coe_nonempty, coe_toFinset
-/
theorem toFinset_nonempty {s : Set α} [Fintype s] : s.toFinset.Nonempty ↔ s.Nonempty := by
  rw [← Finset.coe_nonempty]; rw [coe_toFinset]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.toFinset_nonempty_of_nonempty⟩ := toFinset_nonempty

@[simp]
/--
theorem `toFinset_inj` / 定理 `toFinset_inj`

English:
theorem toFinset_inj
  given: {s t : Set α} [Fintype s] [Fintype t]
  statement: s.toFinset = t.toFinset ↔ s = t
  proof: ⟨fun h => by rw [← s.coe_toFinset, h, t.coe_toFinset], fun h => by simp [h]⟩

@[gcongr, mono]

中文:
定理 toFinset_inj
  条件: {s t : Set α} [Fintype s] [Fintype t]
  结论: s.toFinset = t.toFinset ↔ s = t
  证明: ⟨fun h => by rw [← s.coe_toFinset, h, t.coe_toFinset], fun h => by simp [h]⟩

@[gcongr, mono]

Depends on / 依赖: coe_toFinset, s.coe_toFinset, t.coe_toFinset
-/
theorem toFinset_inj {s t : Set α} [Fintype s] [Fintype t] : s.toFinset = t.toFinset ↔ s = t :=
  ⟨fun h => by rw [← s.coe_toFinset, h, t.coe_toFinset], fun h => by simp [h]⟩

@[gcongr, mono]
/--
theorem `toFinset_subset_toFinset` / 定理 `toFinset_subset_toFinset`

English:
theorem toFinset_subset_toFinset
  given: [Fintype s] [Fintype t]
  statement: s.toFinset subseteq t.toFinset ↔ s subseteq t
  proof: by
  simp [Finset.subset_iff, Set.subset_def]

@[simp]

中文:
定理 toFinset_subset_toFinset
  条件: [Fintype s] [Fintype t]
  结论: s.toFinset subseteq t.toFinset ↔ s subseteq t
  证明: by
  simp [Finset.subset_iff, Set.subset_def]

@[simp]

Depends on / 依赖: Finset, Finset.subset_iff, Set.subset_def, subset_def, subset_iff
-/
theorem toFinset_subset_toFinset [Fintype s] [Fintype t] : s.toFinset subseteq t.toFinset ↔ s subseteq t := by
  simp [Finset.subset_iff, Set.subset_def]

@[simp]
/--
theorem `toFinset_ssubset` / 定理 `toFinset_ssubset`

English:
theorem toFinset_ssubset
  given: [Fintype s] {t : Finset α}
  statement: s.toFinset ⊂ t ↔ s ⊂ t
  proof: by
  rw [← Finset.coe_ssubset]; rw [coe_toFinset]

@[simp]

中文:
定理 toFinset_ssubset
  条件: [Fintype s] {t : Finset α}
  结论: s.toFinset ⊂ t ↔ s ⊂ t
  证明: by
  rw [← Finset.coe_ssubset]; rw [coe_toFinset]

@[simp]

Depends on / 依赖: Finset, Finset.coe_ssubset, coe_ssubset, coe_toFinset
-/
theorem toFinset_ssubset [Fintype s] {t : Finset α} : s.toFinset ⊂ t ↔ s ⊂ t := by
  rw [← Finset.coe_ssubset]; rw [coe_toFinset]

@[simp]
/--
theorem `subset_toFinset` / 定理 `subset_toFinset`

English:
theorem subset_toFinset
  given: {s : Finset α} [Fintype t]
  statement: s subseteq t.toFinset ↔ ↑s subseteq t
  proof: by
  rw [← Finset.coe_subset]; rw [coe_toFinset]

@[simp]

中文:
定理 subset_toFinset
  条件: {s : Finset α} [Fintype t]
  结论: s subseteq t.toFinset ↔ ↑s subseteq t
  证明: by
  rw [← Finset.coe_subset]; rw [coe_toFinset]

@[simp]

Depends on / 依赖: Finset, Finset.coe_subset, coe_subset, coe_toFinset
-/
theorem subset_toFinset {s : Finset α} [Fintype t] : s subseteq t.toFinset ↔ ↑s subseteq t := by
  rw [← Finset.coe_subset]; rw [coe_toFinset]

@[simp]
/--
theorem `ssubset_toFinset` / 定理 `ssubset_toFinset`

English:
theorem ssubset_toFinset
  given: {s : Finset α} [Fintype t]
  statement: s ⊂ t.toFinset ↔ ↑s ⊂ t
  proof: by
  rw [← Finset.coe_ssubset]; rw [coe_toFinset]

@[gcongr, mono]

中文:
定理 ssubset_toFinset
  条件: {s : Finset α} [Fintype t]
  结论: s ⊂ t.toFinset ↔ ↑s ⊂ t
  证明: by
  rw [← Finset.coe_ssubset]; rw [coe_toFinset]

@[gcongr, mono]

Depends on / 依赖: Finset, Finset.coe_ssubset, coe_ssubset, coe_toFinset
-/
theorem ssubset_toFinset {s : Finset α} [Fintype t] : s ⊂ t.toFinset ↔ ↑s ⊂ t := by
  rw [← Finset.coe_ssubset]; rw [coe_toFinset]

@[gcongr, mono]
/--
theorem `toFinset_ssubset_toFinset` / 定理 `toFinset_ssubset_toFinset`

English:
theorem toFinset_ssubset_toFinset
  given: [Fintype s] [Fintype t]
  statement: s.toFinset ⊂ t.toFinset ↔ s ⊂ t
  proof: by
  simp only [Finset.ssubset_def, toFinset_subset_toFinset, ssubset_def]

@[simp]

中文:
定理 toFinset_ssubset_toFinset
  条件: [Fintype s] [Fintype t]
  结论: s.toFinset ⊂ t.toFinset ↔ s ⊂ t
  证明: by
  simp only [Finset.ssubset_def, toFinset_subset_toFinset, ssubset_def]

@[simp]

Depends on / 依赖: Finset, Finset.ssubset_def, ssubset_def, toFinset_subset_toFinset
-/
theorem toFinset_ssubset_toFinset [Fintype s] [Fintype t] : s.toFinset ⊂ t.toFinset ↔ s ⊂ t := by
  simp only [Finset.ssubset_def, toFinset_subset_toFinset, ssubset_def]

@[simp]
/--
theorem `toFinset_subset` / 定理 `toFinset_subset`

English:
theorem toFinset_subset
  given: [Fintype s] {t : Finset α}
  statement: s.toFinset subseteq t ↔ s subseteq t
  proof: by
  rw [← Finset.coe_subset]; rw [coe_toFinset]

@[gcongr]
alias ⟨_, toFinset_mono⟩ := toFinset_subset_toFinset

alias ⟨_, toFinset_strict_mono⟩ := toFinset_ssubset_toFinset

@[simp]

中文:
定理 toFinset_subset
  条件: [Fintype s] {t : Finset α}
  结论: s.toFinset subseteq t ↔ s subseteq t
  证明: by
  rw [← Finset.coe_subset]; rw [coe_toFinset]

@[gcongr]
alias ⟨_, toFinset_mono⟩ := toFinset_subset_toFinset

alias ⟨_, toFinset_strict_mono⟩ := toFinset_ssubset_toFinset

@[simp]

Depends on / 依赖: Finset, Finset.coe_subset, coe_subset, coe_toFinset
-/
theorem toFinset_subset [Fintype s] {t : Finset α} : s.toFinset subseteq t ↔ s subseteq t := by
  rw [← Finset.coe_subset]; rw [coe_toFinset]

@[gcongr]
alias ⟨_, toFinset_mono⟩ := toFinset_subset_toFinset

alias ⟨_, toFinset_strict_mono⟩ := toFinset_ssubset_toFinset

@[simp]
/--
theorem `disjoint_toFinset` / 定理 `disjoint_toFinset`

English:
theorem disjoint_toFinset
  given: [Fintype s] [Fintype t]
  proof: by simp only [← disjoint_coe, coe_toFinset]

@[simp]

中文:
定理 disjoint_toFinset
  条件: [Fintype s] [Fintype t]
  证明: by simp only [← disjoint_coe, coe_toFinset]

@[simp]

Depends on / 依赖: coe_toFinset, disjoint_coe
-/
theorem disjoint_toFinset [Fintype s] [Fintype t] :
    Disjoint s.toFinset t.toFinset ↔ Disjoint s t := by simp only [← disjoint_coe, coe_toFinset]

@[simp]
/--
theorem `toFinset_nontrivial` / 定理 `toFinset_nontrivial`

English:
theorem toFinset_nontrivial
  given: [Fintype s]
  statement: s.toFinset.Nontrivial ↔ s.Nontrivial
  proof: by
  rw [Finset.Nontrivial]; rw [coe_toFinset]

中文:
定理 toFinset_nontrivial
  条件: [Fintype s]
  结论: s.toFinset.Nontrivial ↔ s.Nontrivial
  证明: by
  rw [Finset.Nontrivial]; rw [coe_toFinset]

Depends on / 依赖: Finset, Finset.Nontrivial, Nontrivial, coe_toFinset
-/
theorem toFinset_nontrivial [Fintype s] : s.toFinset.Nontrivial ↔ s.Nontrivial := by
  rw [Finset.Nontrivial]; rw [coe_toFinset]

/--
theorem `subsingleton_toFinset_iff` / 定理 `subsingleton_toFinset_iff`

English:
theorem subsingleton_toFinset_iff
  given: [Fintype s]
  statement: Subsingleton s.toFinset ↔ s.Subsingleton
  proof: by
  simp

中文:
定理 subsingleton_toFinset_iff
  条件: [Fintype s]
  结论: Subsingleton s.toFinset ↔ s.Subsingleton
  证明: by
  simp
-/
theorem subsingleton_toFinset_iff [Fintype s] : Subsingleton s.toFinset ↔ s.Subsingleton := by
  simp

section DecidableEq

variable [DecidableEq α] (s t) [Fintype s] [Fintype t]

@[simp]
/--
theorem `toFinset_inter` / 定理 `toFinset_inter`

English:
theorem toFinset_inter
  given: [Fintype (s inter t : Set _)]
  statement: (s inter t).toFinset = s.toFinset inter t.toFinset
  proof: by
  ext
  simp

@[simp]

中文:
定理 toFinset_inter
  条件: [Fintype (s inter t : Set _)]
  结论: (s inter t).toFinset = s.toFinset inter t.toFinset
  证明: by
  ext
  simp

@[simp]
-/
theorem toFinset_inter [Fintype (s inter t : Set _)] : (s inter t).toFinset = s.toFinset inter t.toFinset := by
  ext
  simp

@[simp]
/--
theorem `toFinset_union` / 定理 `toFinset_union`

English:
theorem toFinset_union
  given: [Fintype (s union t : Set _)]
  statement: (s union t).toFinset = s.toFinset union t.toFinset
  proof: by
  ext
  simp

@[simp]

中文:
定理 toFinset_union
  条件: [Fintype (s union t : Set _)]
  结论: (s union t).toFinset = s.toFinset union t.toFinset
  证明: by
  ext
  simp

@[simp]
-/
theorem toFinset_union [Fintype (s union t : Set _)] : (s union t).toFinset = s.toFinset union t.toFinset := by
  ext
  simp

@[simp]
/--
theorem `toFinset_sdiff` / 定理 `toFinset_sdiff`

English:
theorem toFinset_sdiff
  given: [Fintype (s \ t : Set _)]
  statement: (s \ t).toFinset = s.toFinset \ t.toFinset
  proof: by
  ext
  simp

@[deprecated (since := "2026-06-03")] alias toFinset_diff := toFinset_sdiff

中文:
定理 toFinset_sdiff
  条件: [Fintype (s \ t : Set _)]
  结论: (s \ t).toFinset = s.toFinset \ t.toFinset
  证明: by
  ext
  simp

@[deprecated (since := "2026-06-03")] alias toFinset_diff := toFinset_sdiff
-/
theorem toFinset_sdiff [Fintype (s \ t : Set _)] : (s \ t).toFinset = s.toFinset \ t.toFinset := by
  ext
  simp

@[deprecated (since := "2026-06-03")] alias toFinset_diff := toFinset_sdiff

open scoped symmDiff in
@[simp]
/--
theorem `toFinset_symmDiff` / 定理 `toFinset_symmDiff`

English:
theorem toFinset_symmDiff
  given: [Fintype (s ∆ t : Set _)]
  proof: by
  ext
  simp [mem_symmDiff, Finset.mem_symmDiff]

@[simp]

中文:
定理 toFinset_symmDiff
  条件: [Fintype (s ∆ t : Set _)]
  证明: by
  ext
  simp [mem_symmDiff, Finset.mem_symmDiff]

@[simp]

Depends on / 依赖: Finset, Finset.mem_symmDiff, mem_symmDiff
-/
theorem toFinset_symmDiff [Fintype (s ∆ t : Set _)] :
    (s ∆ t).toFinset = s.toFinset ∆ t.toFinset := by
  ext
  simp [mem_symmDiff, Finset.mem_symmDiff]

@[simp]
/--
theorem `toFinset_compl` / 定理 `toFinset_compl`

English:
theorem toFinset_compl
  given: [Fintype α] [Fintype (sᶜ : Set _)]
  statement: sᶜ.toFinset = s.toFinsetᶜ
  proof: by
  ext
  simp

中文:
定理 toFinset_compl
  条件: [Fintype α] [Fintype (sᶜ : Set _)]
  结论: sᶜ.toFinset = s.toFinsetᶜ
  证明: by
  ext
  simp
-/
theorem toFinset_compl [Fintype α] [Fintype (sᶜ : Set _)] : sᶜ.toFinset = s.toFinsetᶜ := by
  ext
  simp

end DecidableEq

@[simp]
/--
theorem `toFinset_empty` / 定理 `toFinset_empty`

English:
theorem toFinset_empty
  given: [Fintype (∅ : Set α)]
  statement: (∅ : Set α).toFinset = ∅
  proof: by
  ext
  simp

@[simp]

中文:
定理 toFinset_empty
  条件: [Fintype (∅ : Set α)]
  结论: (∅ : Set α).toFinset = ∅
  证明: by
  ext
  simp

@[simp]
-/
theorem toFinset_empty [Fintype (∅ : Set α)] : (∅ : Set α).toFinset = ∅ := by
  ext
  simp

@[simp]
/--
theorem `toFinset_univ` / 定理 `toFinset_univ`

English:
theorem toFinset_univ
  given: [Fintype α] [Fintype (Set.univ : Set α)]
  proof: by
  ext
  simp

@[simp]

中文:
定理 toFinset_univ
  条件: [Fintype α] [Fintype (Set.univ : Set α)]
  证明: by
  ext
  simp

@[simp]
-/
theorem toFinset_univ [Fintype α] [Fintype (Set.univ : Set α)] :
    (Set.univ : Set α).toFinset = Finset.univ := by
  ext
  simp

@[simp]
/--
theorem `toFinset_eq_empty` / 定理 `toFinset_eq_empty`

English:
theorem toFinset_eq_empty
  given: [Fintype s]
  statement: s.toFinset = ∅ ↔ s = ∅
  proof: by
  let A : Fintype (∅ : Set α) := Fintype.ofIsEmpty
  rw [← toFinset_empty]; rw [toFinset_inj]

@[simp]

中文:
定理 toFinset_eq_empty
  条件: [Fintype s]
  结论: s.toFinset = ∅ ↔ s = ∅
  证明: by
  let A : Fintype (∅ : Set α) := Fintype.ofIsEmpty
  rw [← toFinset_empty]; rw [toFinset_inj]

@[simp]

Depends on / 依赖: Fintype, Fintype.ofIsEmpty, ofIsEmpty, toFinset_empty, toFinset_inj
-/
theorem toFinset_eq_empty [Fintype s] : s.toFinset = ∅ ↔ s = ∅ := by
  let A : Fintype (∅ : Set α) := Fintype.ofIsEmpty
  rw [← toFinset_empty]; rw [toFinset_inj]

@[simp]
/--
theorem `toFinset_eq_univ` / 定理 `toFinset_eq_univ`

English:
theorem toFinset_eq_univ
  given: [Fintype α] [Fintype s]
  statement: s.toFinset = Finset.univ ↔ s = univ
  proof: by
  rw [← coe_inj]; rw [coe_toFinset]; rw [coe_univ]

@[simp]

中文:
定理 toFinset_eq_univ
  条件: [Fintype α] [Fintype s]
  结论: s.toFinset = Finset.univ ↔ s = univ
  证明: by
  rw [← coe_inj]; rw [coe_toFinset]; rw [coe_univ]

@[simp]

Depends on / 依赖: coe_inj, coe_toFinset, coe_univ
-/
theorem toFinset_eq_univ [Fintype α] [Fintype s] : s.toFinset = Finset.univ ↔ s = univ := by
  rw [← coe_inj]; rw [coe_toFinset]; rw [coe_univ]

@[simp]
/--
theorem `toFinset_ofPred` / 定理 `toFinset_ofPred`

English:
theorem toFinset_ofPred
  given: [Fintype α] (p : α -> Prop) [DecidablePred p] [Fintype { x | p x }]
  proof: by
  ext
  simp

@[deprecated (since := "2026-07-09")] alias toFinset_setOf := toFinset_ofPred

中文:
定理 toFinset_ofPred
  条件: [Fintype α] (p : α -> 命题) [DecidablePred p] [Fintype { x | p x }]
  证明: by
  ext
  simp

@[deprecated (since := "2026-07-09")] alias toFinset_setOf := toFinset_ofPred
-/
theorem toFinset_ofPred [Fintype α] (p : α -> Prop) [DecidablePred p] [Fintype { x | p x }] :
    Set.toFinset {x | p x} = Finset.univ.filter p := by
  ext
  simp

@[deprecated (since := "2026-07-09")] alias toFinset_setOf := toFinset_ofPred

/--
theorem `toFinset_ssubset_univ` / 定理 `toFinset_ssubset_univ`

English:
theorem toFinset_ssubset_univ
  given: [Fintype α] {s : Set α} [Fintype s]
  proof: by simp

@[simp]

中文:
定理 toFinset_ssubset_univ
  条件: [Fintype α] {s : Set α} [Fintype s]
  证明: by simp

@[simp]
-/
theorem toFinset_ssubset_univ [Fintype α] {s : Set α} [Fintype s] :
    s.toFinset ⊂ Finset.univ ↔ s ⊂ univ := by simp

@[simp]
/--
theorem `toFinset_image` / 定理 `toFinset_image`

English:
theorem toFinset_image
  given: [DecidableEq β] (f : α -> β) (s : Set α) [Fintype s] [Fintype (f '' s)]
  proof: Finset.coe_injective by simp

@[simp]

中文:
定理 toFinset_image
  条件: [DecidableEq β] (f : α -> β) (s : Set α) [Fintype s] [Fintype (f '' s)]
  证明: Finset.coe_injective by simp

@[simp]

Depends on / 依赖: Finset, Finset.coe_injective, coe_injective
-/
theorem toFinset_image [DecidableEq β] (f : α -> β) (s : Set α) [Fintype s] [Fintype (f '' s)] :
    (f '' s).toFinset = s.toFinset.image f :=
Finset.coe_injective by simp

@[simp]
/--
theorem `toFinset_range` / 定理 `toFinset_range`

English:
theorem toFinset_range
  given: [DecidableEq α] [Fintype β] (f : β -> α) [Fintype (Set.range f)]
  proof: by
  ext
  simp

@[simp]

中文:
定理 toFinset_range
  条件: [DecidableEq α] [Fintype β] (f : β -> α) [Fintype (Set.range f)]
  证明: by
  ext
  simp

@[simp]
-/
theorem toFinset_range [DecidableEq α] [Fintype β] (f : β -> α) [Fintype (Set.range f)] :
    (Set.range f).toFinset = Finset.univ.image f := by
  ext
  simp

@[simp]
/--
theorem `toFinset_singleton` / 定理 `toFinset_singleton`

English:
theorem toFinset_singleton
  given: (a : α) [Fintype ({a} : Set α)]
  statement: ({a} : Set α).toFinset = {a}
  proof: by
  ext
  simp

@[simp]

中文:
定理 toFinset_singleton
  条件: (a : α) [Fintype ({a} : Set α)]
  结论: ({a} : Set α).toFinset = {a}
  证明: by
  ext
  simp

@[simp]
-/
theorem toFinset_singleton (a : α) [Fintype ({a} : Set α)] : ({a} : Set α).toFinset = {a} := by
  ext
  simp

@[simp]
/--
theorem `toFinset_insert` / 定理 `toFinset_insert`

English:
theorem toFinset_insert
  statement: [DecidableEq α] {a : α} {s : Set α} [Fintype (insert a s : Set α)]
  proof: by
  ext
  simp

中文:
定理 toFinset_insert
  结论: [DecidableEq α] {a : α} {s : Set α} [Fintype (insert a s : Set α)]
  证明: by
  ext
  simp
-/
theorem toFinset_insert [DecidableEq α] {a : α} {s : Set α} [Fintype (insert a s : Set α)]
    [Fintype s] : (insert a s).toFinset = insert a s.toFinset := by
  ext
  simp

/--
theorem `filter_mem_univ_eq_toFinset` / 定理 `filter_mem_univ_eq_toFinset`

English:
theorem filter_mem_univ_eq_toFinset
  given: [Fintype α] (s : Set α) [Fintype s] [DecidablePred (· in s)]
  proof: by
  ext
  rw [mem_filter_univ]; rw [mem_toFinset]

中文:
定理 filter_mem_univ_eq_toFinset
  条件: [Fintype α] (s : Set α) [Fintype s] [DecidablePred (· in s)]
  证明: by
  ext
  rw [mem_filter_univ]; rw [mem_toFinset]

Depends on / 依赖: mem_filter_univ, mem_toFinset
-/
theorem filter_mem_univ_eq_toFinset [Fintype α] (s : Set α) [Fintype s] [DecidablePred (· in s)] :
    Finset.univ.filter (· in s) = s.toFinset := by
  ext
  rw [mem_filter_univ]; rw [mem_toFinset]

end Set

@[simp]
/--
theorem `Finset.toFinset_coe` / 定理 `Finset.toFinset_coe`

English:
theorem Finset.toFinset_coe
  given: (s : Finset α) [Fintype (s : Set α)]
  statement: (s : Set α).toFinset = s
  proof: ext fun _ => Set.mem_toFinset

中文:
定理 Finset.toFinset_coe
  条件: (s : Finset α) [Fintype (s : Set α)]
  结论: (s : Set α).toFinset = s
  证明: ext fun _ => Set.mem_toFinset

Depends on / 依赖: Set.mem_toFinset, mem_toFinset
-/
theorem Finset.toFinset_coe (s : Finset α) [Fintype (s : Set α)] : (s : Set α).toFinset = s :=
  ext fun _ => Set.mem_toFinset

section Finset



/--
Instance `Finset.fintypeCoeSort` / 实例 `Finset.fintypeCoeSort`

English:
instance Finset.fintypeCoeSort
  signature: {α : Type u} (s : Finset α)
  body: ⟨s.attach, s.mem_attach⟩

@[simp]

中文:
实例 Finset.fintypeCoeSort
  签名: {α : 类型u} (s : Finset α)
  定义体: ⟨s.attach, s.mem_attach⟩

@[simp]

Depends on / 依赖: attach, mem_attach, s.attach, s.mem_attach
-/
instance Finset.fintypeCoeSort {α : Type u} (s : Finset α) : Fintype s :=
  ⟨s.attach, s.mem_attach⟩

@[simp]
/--
theorem `Finset.univ_eq_attach` / 定理 `Finset.univ_eq_attach`

English:
theorem Finset.univ_eq_attach
  given: {α : Type u} (s : Finset α)
  statement: (univ : Finset s) = s.attach
  proof: rfl

中文:
定理 Finset.univ_eq_attach
  条件: {α : 类型u} (s : Finset α)
  结论: (univ : Finset s) = s.attach
  证明: rfl
-/
theorem Finset.univ_eq_attach {α : Type u} (s : Finset α) : (univ : Finset s) = s.attach :=
  rfl

end Finset

/--
theorem `Fintype.coe_image_univ` / 定理 `Fintype.coe_image_univ`

English:
theorem Fintype.coe_image_univ
  given: [Fintype α] [DecidableEq β] {f : α -> β}
  proof: by
  simp

中文:
定理 Fintype.coe_image_univ
  条件: [Fintype α] [DecidableEq β] {f : α -> β}
  证明: by
  simp
-/
theorem Fintype.coe_image_univ [Fintype α] [DecidableEq β] {f : α -> β} :
    ↑(Finset.image f Finset.univ) = Set.range f := by
  simp

/--
Instance `List.Subtype.fintype` / 实例 `List.Subtype.fintype`

English:
instance List.Subtype.fintype
  signature: [DecidableEq α] (l : List α)
  body: Fintype.ofList l.attach l.mem_attach

中文:
实例 List.Subtype.fintype
  签名: [DecidableEq α] (l : List α)
  定义体: Fintype.ofList l.attach l.mem_attach

Depends on / 依赖: Fintype, Fintype.ofList, attach, l.attach, l.mem_attach, mem_attach, ofList
-/
instance List.Subtype.fintype [DecidableEq α] (l : List α) : Fintype { x // x in l } :=
  Fintype.ofList l.attach l.mem_attach

/--
Instance `Multiset.Subtype.fintype` / 实例 `Multiset.Subtype.fintype`

English:
instance Multiset.Subtype.fintype
  signature: [DecidableEq α] (s : Multiset α)
  body: Fintype.ofMultiset s.attach s.mem_attach

中文:
实例 Multiset.Subtype.fintype
  签名: [DecidableEq α] (s : Multiset α)
  定义体: Fintype.ofMultiset s.attach s.mem_attach

Depends on / 依赖: Fintype, Fintype.ofMultiset, attach, mem_attach, ofMultiset, s.attach, s.mem_attach
-/
instance Multiset.Subtype.fintype [DecidableEq α] (s : Multiset α) : Fintype { x // x in s } :=
  Fintype.ofMultiset s.attach s.mem_attach

/--
Instance `Finset.Subtype.fintype` / 实例 `Finset.Subtype.fintype`

English:
instance Finset.Subtype.fintype
  signature: (s : Finset α)
  body: ⟨s.attach, s.mem_attach⟩

中文:
实例 Finset.Subtype.fintype
  签名: (s : Finset α)
  定义体: ⟨s.attach, s.mem_attach⟩

Depends on / 依赖: attach, mem_attach, s.attach, s.mem_attach
-/
instance Finset.Subtype.fintype (s : Finset α) : Fintype { x // x in s } :=
  ⟨s.attach, s.mem_attach⟩

/--
Instance `FinsetCoe.fintype` / 实例 `FinsetCoe.fintype`

English:
instance FinsetCoe.fintype
  signature: (s : Finset α)
  body: Finset.Subtype.fintype s

中文:
实例 FinsetCoe.fintype
  签名: (s : Finset α)
  定义体: Finset.Subtype.fintype s

Depends on / 依赖: Finset, Finset.Subtype.fintype, Subtype, fintype
-/
instance FinsetCoe.fintype (s : Finset α) : Fintype (↑s : Set α) :=
  Finset.Subtype.fintype s

/--
theorem `Finset.attach_eq_univ` / 定理 `Finset.attach_eq_univ`

English:
theorem Finset.attach_eq_univ
  given: {s : Finset α}
  statement: s.attach = Finset.univ
  proof: rfl

中文:
定理 Finset.attach_eq_univ
  条件: {s : Finset α}
  结论: s.attach = Finset.univ
  证明: rfl
-/
theorem Finset.attach_eq_univ {s : Finset α} : s.attach = Finset.univ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Prop.fintype` / 实例 `Prop.fintype`

English:
instance Prop.fintype
  signature: : Fintype Prop
  body: ⟨⟨{True, False}, by simp⟩, by simpa using em⟩

@[simp]

中文:
实例 Prop.fintype
  签名: : Fintype 命题
  定义体: ⟨⟨{True, False}, by simp⟩, by simpa using em⟩

@[simp]
-/
instance Prop.fintype : Fintype Prop :=
  ⟨⟨{True, False}, by simp⟩, by simpa using em⟩

@[simp]
/--
theorem `Fintype.univ_Prop` / 定理 `Fintype.univ_Prop`

English:
theorem Fintype.univ_Prop
  statement: (Finset.univ : Finset Prop) = {True, False}
  proof: Finset.eq_of_veq by simp; rfl

中文:
定理 Fintype.univ_Prop
  结论: (Finset.univ : Finset 命题) = {True, False}
  证明: Finset.eq_of_veq by simp; rfl

Depends on / 依赖: Finset, Finset.eq_of_veq, eq_of_veq
-/
theorem Fintype.univ_Prop : (Finset.univ : Finset Prop) = {True, False} :=
Finset.eq_of_veq by simp; rfl

/--
Instance `Subtype.fintype` / 实例 `Subtype.fintype`

English:
instance Subtype.fintype
  signature: (p : α -> Prop) [DecidablePred p] [Fintype α]
  body: Fintype.subtype (univ.filter p) (by simp)

中文:
实例 Subtype.fintype
  签名: (p : α -> 命题) [DecidablePred p] [Fintype α]
  定义体: Fintype.subtype (univ.filter p) (by simp)

Depends on / 依赖: Fintype, Fintype.subtype, filter, subtype, univ.filter
-/
instance Subtype.fintype (p : α -> Prop) [DecidablePred p] [Fintype α] : Fintype { x // p x } :=
  Fintype.subtype (univ.filter p) (by simp)

/-- A set on a fintype, when coerced to a type, is a fintype. -/
@[instance_reducible]
/--
Definition of `setFintype` / `setFintype` 的定义

English:
definition setFintype
  signature: [Fintype α] (s : Set α) [DecidablePred (· in s)]
  body: Subtype.fintype fun x => x in s

中文:
定义 setFintype
  签名: [Fintype α] (s : Set α) [DecidablePred (· in s)]
  定义体: Subtype.fintype fun x => x in s

Depends on / 依赖: Subtype, Subtype.fintype, fintype
-/
def setFintype [Fintype α] (s : Set α) [DecidablePred (· in s)] : Fintype s :=
  Subtype.fintype fun x => x in s

namespace Fintype
variable [Fintype α]

/--
Definition of `finsetEquivSet` / `finsetEquivSet` 的定义

English:
definition finsetEquivSet
  signature: : Finset α ≃ Set α where
  body: (↑)
  invFun := by classical exact fun s => s.toFinset
  left_inv s := by convert! Finset.toFinset_coe s
  right_inv s := by classical exact s.coe_toFinset

中文:
定义 finsetEquivSet
  签名: : Finset α ≃ Set α where
  定义体: (↑)
  invFun := by classical exact fun s => s.toFinset
  left_inv s := by convert! Finset.toFinset_coe s
  right_inv s := by classical exact s.coe_toFinset
-/
noncomputable def finsetEquivSet : Finset α ≃ Set α where
  toFun := (↑)
  invFun := by classical exact fun s => s.toFinset
  left_inv s := by convert! Finset.toFinset_coe s
  right_inv s := by classical exact s.coe_toFinset

/--
lemma `coe_finsetEquivSet` / 引理 `coe_finsetEquivSet`

English:
lemma coe_finsetEquivSet
  statement: ⇑finsetEquivSet = ((↑) : Finset α -> Set α)
  proof: rfl

中文:
引理 coe_finsetEquivSet
  结论: ⇑finsetEquivSet = ((↑) : Finset α -> Set α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_finsetEquivSet : ⇑finsetEquivSet = ((↑) : Finset α -> Set α) := rfl

/--
lemma `finsetEquivSet_apply` / 引理 `finsetEquivSet_apply`

English:
lemma finsetEquivSet_apply
  given: (s : Finset α)
  statement: finsetEquivSet s = s
  proof: rfl

中文:
引理 finsetEquivSet_apply
  条件: (s : Finset α)
  结论: finsetEquivSet s = s
  证明: rfl
-/
@[simp] lemma finsetEquivSet_apply (s : Finset α) : finsetEquivSet s = s := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `finsetEquivSet_symm_apply` / 引理 `finsetEquivSet_symm_apply`

English:
lemma finsetEquivSet_symm_apply
  given: (s : Set α) [Fintype s]
  proof: by simp [finsetEquivSet]

中文:
引理 finsetEquivSet_symm_apply
  条件: (s : Set α) [Fintype s]
  证明: by simp [finsetEquivSet]
-/
@[simp] lemma finsetEquivSet_symm_apply (s : Set α) [Fintype s] :
    finsetEquivSet.symm s = s.toFinset := by simp [finsetEquivSet]

/-- Given a fintype `α`, `finsetOrderIsoSet` is the order isomorphism between `Finset α` and `Set α`
(all sets on a finite type are finite). -/
@[simps toEquiv]
/--
Definition of `finsetOrderIsoSet` / `finsetOrderIsoSet` 的定义

English:
definition finsetOrderIsoSet
  signature: : Finset α ≃o Set α where
  body: finsetEquivSet
  map_rel_iff' := Finset.coe_subset

@[simp, norm_cast]

中文:
定义 finsetOrderIsoSet
  签名: : Finset α ≃o Set α where
  定义体: finsetEquivSet
  map_rel_iff' := Finset.coe_subset

@[simp, norm_cast]

Depends on / 依赖: finsetEquivSet
-/
noncomputable def finsetOrderIsoSet : Finset α ≃o Set α where
  toEquiv := finsetEquivSet
  map_rel_iff' := Finset.coe_subset

@[simp, norm_cast]
/--
lemma `coe_finsetOrderIsoSet` / 引理 `coe_finsetOrderIsoSet`

English:
lemma coe_finsetOrderIsoSet
  statement: ⇑finsetOrderIsoSet = ((↑) : Finset α -> Set α)
  proof: rfl

中文:
引理 coe_finsetOrderIsoSet
  结论: ⇑finsetOrderIsoSet = ((↑) : Finset α -> Set α)
  证明: rfl
-/
lemma coe_finsetOrderIsoSet : ⇑finsetOrderIsoSet = ((↑) : Finset α -> Set α) := rfl

/--
lemma `coe_finsetOrderIsoSet_symm` / 引理 `coe_finsetOrderIsoSet_symm`

English:
lemma coe_finsetOrderIsoSet_symm
  proof: rfl

中文:
引理 coe_finsetOrderIsoSet_symm
  证明: rfl
-/
@[simp] lemma coe_finsetOrderIsoSet_symm :
    ⇑(finsetOrderIsoSet : Finset α ≃o Set α).symm = ⇑finsetEquivSet.symm := rfl

end Fintype

/--
theorem `mem_image_univ_iff_mem_range` / 定理 `mem_image_univ_iff_mem_range`

English:
theorem mem_image_univ_iff_mem_range
  statement: {α β : Type*} [Fintype α] [DecidableEq β] {f : α -> β}
  proof: by simp

中文:
定理 mem_image_univ_iff_mem_range
  结论: {α β : 类型} [Fintype α] [DecidableEq β] {f : α -> β}
  证明: by simp
-/
theorem mem_image_univ_iff_mem_range {α β : Type*} [Fintype α] [DecidableEq β] {f : α -> β}
    {b : β} : b in univ.image f ↔ b in Set.range f := by simp

open Batteries.ExtendedBinder Lean Meta

/-- `finset% t` elaborates `t` as a `Finset`.
If `t` is a `Set`, then inserts `Set.toFinset`.
Does not make use of the expected type; useful for big operators over finsets.
```
#check finset% Finset.range 2 -- Finset Nat
#check finset% (Set.univ : Set Bool) -- Finset Bool
```
-/
elab (name := finsetStx) "finset% " t:term : term => do
  let u ← mkFreshLevelMVar
  let ty ← mkFreshExprMVar (mkSort (.succ u))
  let x ← Elab.Term.elabTerm t (mkApp (.const ``Finset [u]) ty)
  let xty ← whnfR (← inferType x)
  if xty.isAppOfArity ``Set 1 then
    Elab.Term.elabAppArgs (.const ``Set.toFinset [u]) #[] #[.expr x] none false false
  else
    return x

open Lean.Elab.Term.Quotation in
/-- `quot_precheck` for the `finset%` syntax. -/
@[quot_precheck finsetStx] meta def precheckFinsetStx : Precheck
  | `(finset% $t) => precheck t
  | _ => Elab.throwUnsupportedSyntax
