/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Nontriviality

/-!
# Finite sets

This file provides `Fintype` instances for many set constructions. It also proves basic facts about
finite sets and gives ways to manipulate `Set.Finite` expressions.

Note that the instances in this file are selected somewhat arbitrarily on the basis of them not
needing any imports beyond `Data.Fintype.Card` (which is required by `Finite.ofFinset`); they can
certainly be organized better.

## Main definitions

* `Set.Finite.toFinset` to noncomputably produce a `Finset` from a `Set.Finite` proof.
  (See `Set.toFinset` for a computable version.)

## Implementation

A finite set is defined to be a set whose coercion to a type has a `Finite` instance.

There are two components to finiteness constructions. The first is `Fintype` instances for each
construction. This gives a way to actually compute a `Finset` that represents the set, and these
may be accessed using `set.toFinset`. This gets the `Finset` in the correct form, since otherwise
`Finset.univ : Finset s` is a `Finset` for the subtype for `s`. The second component is
"constructors" for `Set.Finite` that give proofs that `Fintype` instances exist classically given
other `Set.Finite` proofs. Unlike the `Fintype` instances, these *do not* use any decidability
instances since they do not compute anything.

## Tags

finite sets
-/

@[expose] public section

assert_not_exists Monoid

open Set Function
open scoped symmDiff

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/--
theorem `finite_def` / 定理 `finite_def`

English:
theorem finite_def
  given: {s : Set α}
  statement: s.Finite ↔ Nonempty (Fintype s)
  proof: finite_iff_nonempty_fintype s

protected alias ⟨Finite.nonempty_fintype, _⟩ := finite_def

中文:
定理 finite_def
  条件: {s : 集合 α}
  结论: s.有限 ↔ 非空 (有限类型 s)
  证明: finite_iff_nonempty_fintype s

protected alias ⟨Finite.nonempty_fintype, _⟩ := finite_def

Depends on / 依赖: finite_iff_nonempty_fintype
-/
theorem finite_def {s : Set α} : s.Finite ↔ Nonempty (Fintype s) :=
  finite_iff_nonempty_fintype s

protected alias ⟨Finite.nonempty_fintype, _⟩ := finite_def

/--
theorem `Finite.ofFinset` / 定理 `Finite.ofFinset`

English:
theorem Finite.ofFinset
  given: {p : Set α} (s : Finset α) (H : forall x, x in s ↔ x in p)
  statement: p.Finite
  proof: have := Fintype.ofFinset s H; p.toFinite

中文:
定理 有限.ofFinset
  条件: {p : 集合 α} (s : 有限集 α) (H : 对任意 x, x in s ↔ x in p)
  结论: p.有限
  证明: have := Fintype.ofFinset s H; p.toFinite
-/
protected theorem Finite.ofFinset {p : Set α} (s : Finset α) (H : forall x, x in s ↔ x in p) : p.Finite :=
  have := Fintype.ofFinset s H; p.toFinite

/-- A finite set coerced to a type is a `Fintype`.
This is the `Fintype` projection for a `Set.Finite`.

Note that because `Finite` isn't a typeclass, this definition will not fire if it
is made into an instance -/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Finite.fintype {s : Set α} (h : s.Finite)
  body: h.nonempty_fintype.some

中文:
定义 noncomputable
  签名: def 有限.fintype {s : 集合 α} (h : s.有限)
  定义体: h.nonempty_fintype.some
-/
protected noncomputable def Finite.fintype {s : Set α} (h : s.Finite) : Fintype s :=
  h.nonempty_fintype.some

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Finite.toFinset {s : Set α} (h : s.Finite)
  body: @Set.toFinset _ _ h.fintype

中文:
定义 noncomputable
  签名: def 有限.toFinset {s : 集合 α} (h : s.有限)
  定义体: @Set.toFinset _ _ h.fintype
-/
protected noncomputable def Finite.toFinset {s : Set α} (h : s.Finite) : Finset α :=
  @Set.toFinset _ _ h.fintype

/--
theorem `Finite.toFinset_eq_toFinset` / 定理 `Finite.toFinset_eq_toFinset`

English:
theorem Finite.toFinset_eq_toFinset
  given: {s : Set α} [Fintype s] (h : s.Finite)
  proof: by
  rw [Finite.toFinset]; rw [Subsingleton.elim h.fintype]

@[simp]

中文:
定理 有限.toFinset_eq_toFinset
  条件: {s : 集合 α} [有限类型 s] (h : s.有限)
  证明: by
  rw [Finite.toFinset]; rw [Subsingleton.elim h.fintype]

@[simp]

Depends on / 依赖: Finite, Finite.toFinset, Subsingleton, Subsingleton.elim, fintype, h.fintype, toFinset
-/
theorem Finite.toFinset_eq_toFinset {s : Set α} [Fintype s] (h : s.Finite) :
    h.toFinset = s.toFinset := by
  rw [Finite.toFinset]; rw [Subsingleton.elim h.fintype]

@[simp]
/--
theorem `toFinite_toFinset` / 定理 `toFinite_toFinset`

English:
theorem toFinite_toFinset
  given: (s : Set α) [Fintype s]
  statement: s.toFinite.toFinset = s.toFinset
  proof: s.toFinite.toFinset_eq_toFinset

中文:
定理 toFinite_toFinset
  条件: (s : 集合 α) [有限类型 s]
  结论: s.toFinite.toFinset = s.toFinset
  证明: s.toFinite.toFinset_eq_toFinset

Depends on / 依赖: s.toFinite.toFinset_eq_toFinset, toFinite, toFinset_eq_toFinset
-/
theorem toFinite_toFinset (s : Set α) [Fintype s] : s.toFinite.toFinset = s.toFinset :=
  s.toFinite.toFinset_eq_toFinset

/--
theorem `Finite.exists_finset` / 定理 `Finite.exists_finset`

English:
theorem Finite.exists_finset
  given: {s : Set α} (h : s.Finite)
  proof: by
  cases h.nonempty_fintype
  exact ⟨s.toFinset, fun _ => mem_toFinset⟩

中文:
定理 有限.存在_finset
  条件: {s : 集合 α} (h : s.有限)
  证明: by
  cases h.nonempty_fintype
  exact ⟨s.toFinset, fun _ => mem_toFinset⟩

Depends on / 依赖: h.nonempty_fintype, mem_toFinset, nonempty_fintype, s.toFinset, toFinset
-/
theorem Finite.exists_finset {s : Set α} (h : s.Finite) :
    exists s' : Finset α, forall a : α, a in s' ↔ a in s := by
  cases h.nonempty_fintype
  exact ⟨s.toFinset, fun _ => mem_toFinset⟩

/--
theorem `Finite.exists_finset_coe` / 定理 `Finite.exists_finset_coe`

English:
theorem Finite.exists_finset_coe
  given: {s : Set α} (h : s.Finite)
  statement: exists s' : Finset α, ↑s' = s
  proof: by
  cases h.nonempty_fintype
  exact ⟨s.toFinset, s.coe_toFinset⟩

中文:
定理 有限.存在_finset_coe
  条件: {s : 集合 α} (h : s.有限)
  结论: 存在 s' : 有限集 α, ↑s' = s
  证明: by
  cases h.nonempty_fintype
  exact ⟨s.toFinset, s.coe_toFinset⟩

Depends on / 依赖: coe_toFinset, h.nonempty_fintype, nonempty_fintype, s.coe_toFinset, s.toFinset, toFinset
-/
theorem Finite.exists_finset_coe {s : Set α} (h : s.Finite) : exists s' : Finset α, ↑s' = s := by
  cases h.nonempty_fintype
  exact ⟨s.toFinset, s.coe_toFinset⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift (Set α) (Finset α) (↑) Set.Finite
  body: hs.exists_finset_coe

中文:
实例 :
  签名: CanLift (集合 α) (有限集 α) (↑) 集合.有限
  定义体: hs.exists_finset_coe

Depends on / 依赖: exists_finset_coe, hs.exists_finset_coe
-/
instance : CanLift (Set α) (Finset α) (↑) Set.Finite where prf _ hs := hs.exists_finset_coe

/-! ### Basic properties of `Set.Finite.toFinset` -/


namespace Finite

variable {s t : Set α} {a : α} (hs : s.Finite) {ht : t.Finite}

@[simp]
/--
theorem `mem_toFinset` / 定理 `mem_toFinset`

English:
theorem mem_toFinset
  statement: a in hs.toFinset ↔ a in s
  proof: @mem_toFinset _ _ hs.fintype _

@[simp]

中文:
定理 mem_toFinset
  结论: a in hs.toFinset ↔ a in s
  证明: @mem_toFinset _ _ hs.fintype _

@[simp]
-/
protected theorem mem_toFinset : a in hs.toFinset ↔ a in s :=
  @mem_toFinset _ _ hs.fintype _

@[simp]
/--
theorem `coe_toFinset` / 定理 `coe_toFinset`

English:
theorem coe_toFinset
  statement: (hs.toFinset : Set α) = s
  proof: @coe_toFinset _ _ hs.fintype

@[simp]

中文:
定理 coe_toFinset
  结论: (hs.toFinset : 集合 α) = s
  证明: @coe_toFinset _ _ hs.fintype

@[simp]
-/
protected theorem coe_toFinset : (hs.toFinset : Set α) = s :=
  @coe_toFinset _ _ hs.fintype

@[simp]
/--
theorem `toFinset_nonempty` / 定理 `toFinset_nonempty`

English:
theorem toFinset_nonempty
  statement: hs.toFinset.Nonempty ↔ s.Nonempty
  proof: by
  rw [← Finset.coe_nonempty]; rw [Finite.coe_toFinset]

中文:
定理 toFinset_nonempty
  结论: hs.toFinset.非空 ↔ s.非空
  证明: by
  rw [← Finset.coe_nonempty]; rw [Finite.coe_toFinset]
-/
protected theorem toFinset_nonempty : hs.toFinset.Nonempty ↔ s.Nonempty := by
  rw [← Finset.coe_nonempty]; rw [Finite.coe_toFinset]

/--
theorem `coeSort_toFinset` / 定理 `coeSort_toFinset`

English:
theorem coeSort_toFinset
  statement: ↥hs.toFinset = ↥s
  proof: by
  rw [← Finset.coe_sort_coe _]; rw [hs.coe_toFinset]

中文:
定理 coeSort_toFinset
  结论: ↥hs.toFinset = ↥s
  证明: by
  rw [← Finset.coe_sort_coe _]; rw [hs.coe_toFinset]

Depends on / 依赖: Finset, Finset.coe_sort_coe, coe_sort_coe, coe_toFinset, hs.coe_toFinset
-/
theorem coeSort_toFinset : ↥hs.toFinset = ↥s := by
  rw [← Finset.coe_sort_coe _]; rw [hs.coe_toFinset]

/--
Definition of `subtypeEquivToFinset` / `subtypeEquivToFinset` 的定义

English:
definition subtypeEquivToFinset
  signature: : {x // x in s} ≃ {x // x in hs.toFinset}
  body: (Equiv.refl α).subtypeEquiv fun _ => hs.mem_toFinset.symm

中文:
定义 subtypeEquivToFinset
  签名: : {x // x in s} ≃ {x // x in hs.toFinset}
  定义体: (Equiv.refl α).subtypeEquiv fun _ => hs.mem_toFinset.symm
-/
@[simps!] def subtypeEquivToFinset : {x // x in s} ≃ {x // x in hs.toFinset} :=
  (Equiv.refl α).subtypeEquiv fun _ => hs.mem_toFinset.symm

variable {hs}

@[simp]
/--
theorem `toFinset_inj` / 定理 `toFinset_inj`

English:
theorem toFinset_inj
  statement: hs.toFinset = ht.toFinset ↔ s = t
  proof: @toFinset_inj _ _ _ hs.fintype ht.fintype

@[simp]

中文:
定理 toFinset_inj
  结论: hs.toFinset = ht.toFinset ↔ s = t
  证明: @toFinset_inj _ _ _ hs.fintype ht.fintype

@[simp]
-/
protected theorem toFinset_inj : hs.toFinset = ht.toFinset ↔ s = t :=
  @toFinset_inj _ _ _ hs.fintype ht.fintype

@[simp]
/--
theorem `toFinset_subset` / 定理 `toFinset_subset`

English:
theorem toFinset_subset
  given: {t : Finset α}
  statement: hs.toFinset subseteq t ↔ s subseteq t
  proof: by
  rw [← Finset.coe_subset]; rw [Finite.coe_toFinset]

@[simp]

中文:
定理 toFinset_subset
  条件: {t : 有限集 α}
  结论: hs.toFinset subseteq t ↔ s subseteq t
  证明: by
  rw [← Finset.coe_subset]; rw [Finite.coe_toFinset]

@[simp]

Depends on / 依赖: Finite, Finite.coe_toFinset, Finset, Finset.coe_subset, coe_subset, coe_toFinset
-/
theorem toFinset_subset {t : Finset α} : hs.toFinset subseteq t ↔ s subseteq t := by
  rw [← Finset.coe_subset]; rw [Finite.coe_toFinset]

@[simp]
/--
theorem `toFinset_ssubset` / 定理 `toFinset_ssubset`

English:
theorem toFinset_ssubset
  given: {t : Finset α}
  statement: hs.toFinset ⊂ t ↔ s ⊂ t
  proof: by
  rw [← Finset.coe_ssubset]; rw [Finite.coe_toFinset]

@[simp]

中文:
定理 toFinset_ssubset
  条件: {t : 有限集 α}
  结论: hs.toFinset ⊂ t ↔ s ⊂ t
  证明: by
  rw [← Finset.coe_ssubset]; rw [Finite.coe_toFinset]

@[simp]

Depends on / 依赖: Finite, Finite.coe_toFinset, Finset, Finset.coe_ssubset, coe_ssubset, coe_toFinset
-/
theorem toFinset_ssubset {t : Finset α} : hs.toFinset ⊂ t ↔ s ⊂ t := by
  rw [← Finset.coe_ssubset]; rw [Finite.coe_toFinset]

@[simp]
/--
theorem `subset_toFinset` / 定理 `subset_toFinset`

English:
theorem subset_toFinset
  given: {s : Finset α}
  statement: s subseteq ht.toFinset ↔ ↑s subseteq t
  proof: by
  rw [← Finset.coe_subset]; rw [Finite.coe_toFinset]

@[simp]

中文:
定理 subset_toFinset
  条件: {s : 有限集 α}
  结论: s subseteq ht.toFinset ↔ ↑s subseteq t
  证明: by
  rw [← Finset.coe_subset]; rw [Finite.coe_toFinset]

@[simp]

Depends on / 依赖: Finite, Finite.coe_toFinset, Finset, Finset.coe_subset, coe_subset, coe_toFinset
-/
theorem subset_toFinset {s : Finset α} : s subseteq ht.toFinset ↔ ↑s subseteq t := by
  rw [← Finset.coe_subset]; rw [Finite.coe_toFinset]

@[simp]
/--
theorem `ssubset_toFinset` / 定理 `ssubset_toFinset`

English:
theorem ssubset_toFinset
  given: {s : Finset α}
  statement: s ⊂ ht.toFinset ↔ ↑s ⊂ t
  proof: by
  rw [← Finset.coe_ssubset]; rw [Finite.coe_toFinset]

@[gcongr, mono]

中文:
定理 ssubset_toFinset
  条件: {s : 有限集 α}
  结论: s ⊂ ht.toFinset ↔ ↑s ⊂ t
  证明: by
  rw [← Finset.coe_ssubset]; rw [Finite.coe_toFinset]

@[gcongr, mono]

Depends on / 依赖: Finite, Finite.coe_toFinset, Finset, Finset.coe_ssubset, coe_ssubset, coe_toFinset
-/
theorem ssubset_toFinset {s : Finset α} : s ⊂ ht.toFinset ↔ ↑s ⊂ t := by
  rw [← Finset.coe_ssubset]; rw [Finite.coe_toFinset]

@[gcongr, mono]
/--
theorem `toFinset_subset_toFinset` / 定理 `toFinset_subset_toFinset`

English:
theorem toFinset_subset_toFinset
  statement: hs.toFinset subseteq ht.toFinset ↔ s subseteq t
  proof: by
  simp only [← Finset.coe_subset, Finite.coe_toFinset]

@[gcongr, mono]

中文:
定理 toFinset_subset_toFinset
  结论: hs.toFinset subseteq ht.toFinset ↔ s subseteq t
  证明: by
  simp only [← Finset.coe_subset, Finite.coe_toFinset]

@[gcongr, mono]
-/
protected theorem toFinset_subset_toFinset : hs.toFinset subseteq ht.toFinset ↔ s subseteq t := by
  simp only [← Finset.coe_subset, Finite.coe_toFinset]

@[gcongr, mono]
/--
theorem `toFinset_ssubset_toFinset` / 定理 `toFinset_ssubset_toFinset`

English:
theorem toFinset_ssubset_toFinset
  statement: hs.toFinset ⊂ ht.toFinset ↔ s ⊂ t
  proof: by
  simp only [← Finset.coe_ssubset, Finite.coe_toFinset]

protected alias ⟨_, toFinset_mono⟩ := Finite.toFinset_subset_toFinset

protected alias ⟨_, toFinset_strictMono⟩ := Finite.toFinset_ssubset_toFinset

@[simp high]

中文:
定理 toFinset_ssubset_toFinset
  结论: hs.toFinset ⊂ ht.toFinset ↔ s ⊂ t
  证明: by
  simp only [← Finset.coe_ssubset, Finite.coe_toFinset]

protected alias ⟨_, toFinset_mono⟩ := Finite.toFinset_subset_toFinset

protected alias ⟨_, toFinset_strictMono⟩ := Finite.toFinset_ssubset_toFinset

@[simp high]
-/
protected theorem toFinset_ssubset_toFinset : hs.toFinset ⊂ ht.toFinset ↔ s ⊂ t := by
  simp only [← Finset.coe_ssubset, Finite.coe_toFinset]

protected alias ⟨_, toFinset_mono⟩ := Finite.toFinset_subset_toFinset

protected alias ⟨_, toFinset_strictMono⟩ := Finite.toFinset_ssubset_toFinset

@[simp high]
/--
theorem `toFinset_ofPred` / 定理 `toFinset_ofPred`

English:
theorem toFinset_ofPred
  statement: [Fintype α] (p : α -> Prop) [DecidablePred p]
  proof: by simp

@[deprecated (since := "2026-07-09")] protected alias toFinset_setOf := Set.Finite.toFinset_ofPred

@[simp]
nonrec theorem disjoint_toFinset {hs : s.Finite} {ht : t.Finite} :
    Disjoint hs.toFinset ht.toFinset ↔ Disjoint s t :=
  @disjoint_toFinset _ _ _ hs.fintype ht.fintype

中文:
定理 toFinset_ofPred
  结论: [有限类型 α] (p : α -> 命题) [DecidablePred p]
  证明: by simp

@[deprecated (since := "2026-07-09")] protected alias toFinset_setOf := Set.Finite.toFinset_ofPred

@[simp]
nonrec theorem disjoint_toFinset {hs : s.Finite} {ht : t.Finite} :
    Disjoint hs.toFinset ht.toFinset ↔ Disjoint s t :=
  @disjoint_toFinset _ _ _ hs.fintype ht.fintype
-/
protected theorem toFinset_ofPred [Fintype α] (p : α -> Prop) [DecidablePred p]
    (h : { x | p x }.Finite) : h.toFinset = ({x | p x} : Finset α) := by simp

@[deprecated (since := "2026-07-09")] protected alias toFinset_setOf := Set.Finite.toFinset_ofPred

@[simp]
nonrec theorem disjoint_toFinset {hs : s.Finite} {ht : t.Finite} :
    Disjoint hs.toFinset ht.toFinset ↔ Disjoint s t :=
  @disjoint_toFinset _ _ _ hs.fintype ht.fintype

/--
theorem `toFinset_inter` / 定理 `toFinset_inter`

English:
theorem toFinset_inter
  statement: [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
  proof: by
  ext
  simp

中文:
定理 toFinset_inter
  结论: [DecidableEq α] (hs : s.有限) (ht : t.有限)
  证明: by
  ext
  simp
-/
protected theorem toFinset_inter [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s inter t).Finite) : h.toFinset = hs.toFinset inter ht.toFinset := by
  ext
  simp

/--
theorem `toFinset_union` / 定理 `toFinset_union`

English:
theorem toFinset_union
  statement: [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
  proof: by
  ext
  simp

中文:
定理 toFinset_union
  结论: [DecidableEq α] (hs : s.有限) (ht : t.有限)
  证明: by
  ext
  simp
-/
protected theorem toFinset_union [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s union t).Finite) : h.toFinset = hs.toFinset union ht.toFinset := by
  ext
  simp

/--
theorem `toFinset_sdiff` / 定理 `toFinset_sdiff`

English:
theorem toFinset_sdiff
  statement: [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
  proof: by
  ext
  simp

@[deprecated (since := "2026-06-03")] alias toFinset_diff := toFinset_sdiff

中文:
定理 toFinset_sdiff
  结论: [DecidableEq α] (hs : s.有限) (ht : t.有限)
  证明: by
  ext
  simp

@[deprecated (since := "2026-06-03")] alias toFinset_diff := toFinset_sdiff
-/
protected theorem toFinset_sdiff [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s \ t).Finite) : h.toFinset = hs.toFinset \ ht.toFinset := by
  ext
  simp

@[deprecated (since := "2026-06-03")] alias toFinset_diff := toFinset_sdiff

open scoped symmDiff in
/--
theorem `toFinset_symmDiff` / 定理 `toFinset_symmDiff`

English:
theorem toFinset_symmDiff
  statement: [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
  proof: by
  ext
  simp [mem_symmDiff, Finset.mem_symmDiff]

中文:
定理 toFinset_symmDiff
  结论: [DecidableEq α] (hs : s.有限) (ht : t.有限)
  证明: by
  ext
  simp [mem_symmDiff, Finset.mem_symmDiff]
-/
protected theorem toFinset_symmDiff [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s ∆ t).Finite) : h.toFinset = hs.toFinset ∆ ht.toFinset := by
  ext
  simp [mem_symmDiff, Finset.mem_symmDiff]

/--
theorem `toFinset_compl` / 定理 `toFinset_compl`

English:
theorem toFinset_compl
  given: [DecidableEq α] [Fintype α] (hs : s.Finite) (h : sᶜ.Finite)
  proof: by
  ext
  simp

中文:
定理 toFinset_compl
  条件: [DecidableEq α] [有限类型 α] (hs : s.有限) (h : sᶜ.有限)
  证明: by
  ext
  simp
-/
protected theorem toFinset_compl [DecidableEq α] [Fintype α] (hs : s.Finite) (h : sᶜ.Finite) :
    h.toFinset = hs.toFinsetᶜ := by
  ext
  simp

/--
theorem `toFinset_univ` / 定理 `toFinset_univ`

English:
theorem toFinset_univ
  given: [Fintype α] (h : (Set.univ : Set α).Finite)
  proof: by
  simp

@[simp]

中文:
定理 toFinset_univ
  条件: [有限类型 α] (h : (集合.univ : 集合 α).有限)
  证明: by
  simp

@[simp]
-/
protected theorem toFinset_univ [Fintype α] (h : (Set.univ : Set α).Finite) :
    h.toFinset = Finset.univ := by
  simp

@[simp]
/--
theorem `toFinset_eq_empty` / 定理 `toFinset_eq_empty`

English:
theorem toFinset_eq_empty
  given: {h : s.Finite}
  statement: h.toFinset = ∅ ↔ s = ∅
  proof: @toFinset_eq_empty _ _ h.fintype

中文:
定理 toFinset_eq_empty
  条件: {h : s.有限}
  结论: h.toFinset = ∅ ↔ s = ∅
  证明: @toFinset_eq_empty _ _ h.fintype
-/
protected theorem toFinset_eq_empty {h : s.Finite} : h.toFinset = ∅ ↔ s = ∅ :=
  @toFinset_eq_empty _ _ h.fintype

/--
theorem `toFinset_empty` / 定理 `toFinset_empty`

English:
theorem toFinset_empty
  given: (h : (∅ : Set α).Finite)
  statement: h.toFinset = ∅
  proof: by
  simp

@[simp]

中文:
定理 toFinset_empty
  条件: (h : (∅ : 集合 α).有限)
  结论: h.toFinset = ∅
  证明: by
  simp

@[simp]
-/
protected theorem toFinset_empty (h : (∅ : Set α).Finite) : h.toFinset = ∅ := by
  simp

@[simp]
/--
theorem `toFinset_eq_univ` / 定理 `toFinset_eq_univ`

English:
theorem toFinset_eq_univ
  given: [Fintype α] {h : s.Finite}
  proof: @toFinset_eq_univ _ _ _ h.fintype

中文:
定理 toFinset_eq_univ
  条件: [有限类型 α] {h : s.有限}
  证明: @toFinset_eq_univ _ _ _ h.fintype
-/
protected theorem toFinset_eq_univ [Fintype α] {h : s.Finite} :
    h.toFinset = Finset.univ ↔ s = univ :=
  @toFinset_eq_univ _ _ _ h.fintype

/--
theorem `toFinset_image` / 定理 `toFinset_image`

English:
theorem toFinset_image
  given: [DecidableEq β] (f : α -> β) (hs : s.Finite) (h : (f '' s).Finite)
  proof: by
  ext
  simp

中文:
定理 toFinset_image
  条件: [DecidableEq β] (f : α -> β) (hs : s.有限) (h : (f '' s).有限)
  证明: by
  ext
  simp
-/
protected theorem toFinset_image [DecidableEq β] (f : α -> β) (hs : s.Finite) (h : (f '' s).Finite) :
    h.toFinset = hs.toFinset.image f := by
  ext
  simp

/--
theorem `toFinset_range` / 定理 `toFinset_range`

English:
theorem toFinset_range
  given: [DecidableEq α] [Fintype β] (f : β -> α) (h : (range f).Finite)
  proof: by
  ext
  simp

@[simp]

中文:
定理 toFinset_range
  条件: [DecidableEq α] [有限类型 β] (f : β -> α) (h : (range f).有限)
  证明: by
  ext
  simp

@[simp]
-/
protected theorem toFinset_range [DecidableEq α] [Fintype β] (f : β -> α) (h : (range f).Finite) :
    h.toFinset = Finset.univ.image f := by
  ext
  simp

@[simp]
/--
theorem `toFinset_nontrivial` / 定理 `toFinset_nontrivial`

English:
theorem toFinset_nontrivial
  given: (h : s.Finite)
  statement: h.toFinset.Nontrivial ↔ s.Nontrivial
  proof: by
  rw [Finset.Nontrivial]; rw [h.coe_toFinset]

中文:
定理 toFinset_nontrivial
  条件: (h : s.有限)
  结论: h.toFinset.非平凡 ↔ s.非平凡
  证明: by
  rw [Finset.Nontrivial]; rw [h.coe_toFinset]
-/
protected theorem toFinset_nontrivial (h : s.Finite) : h.toFinset.Nontrivial ↔ s.Nontrivial := by
  rw [Finset.Nontrivial]; rw [h.coe_toFinset]

end Finite

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

/--
Instance `fintypeUniv` / 实例 `fintypeUniv`

English:
instance fintypeUniv
  signature: [Fintype α]
  body: Fintype.ofEquiv α (Equiv.Set.univ α).symm

中文:
实例 fintypeUniv
  签名: [有限类型 α]
  定义体: Fintype.ofEquiv α (Equiv.Set.univ α).symm

Depends on / 依赖: Equiv.Set.univ, Fintype, Fintype.ofEquiv, ofEquiv
-/
instance fintypeUniv [Fintype α] : Fintype (@univ α) :=
  Fintype.ofEquiv α (Equiv.Set.univ α).symm

-- Redeclared with appropriate keys
/--
Instance `fintypeTop` / 实例 `fintypeTop`

English:
instance fintypeTop
  signature: [Fintype α]
  body: inferInstanceAs (Fintype (univ : Set α))

中文:
实例 fintypeTop
  签名: [有限类型 α]
  定义体: inferInstanceAs (Fintype (univ : Set α))

Depends on / 依赖: Fintype
-/
instance fintypeTop [Fintype α] : Fintype (⊤ : Set α) := inferInstanceAs (Fintype (univ : Set α))

/-- If `(Set.univ : Set α)` is finite then `α` is a finite type. -/
@[instance_reducible]
/--
Definition of `fintypeOfFiniteUniv` / `fintypeOfFiniteUniv` 的定义

English:
definition fintypeOfFiniteUniv
  signature: (H : (univ (α := α)).Finite)
  body: @Fintype.ofEquiv _ (univ : Set α) H.fintype (Equiv.Set.univ _)

中文:
定义 fintypeOfFiniteUniv
  签名: (H : (univ (α := α)).有限)
  定义体: @Fintype.ofEquiv _ (univ : Set α) H.fintype (Equiv.Set.univ _)

Depends on / 依赖: Finite, Fintype
-/
noncomputable def fintypeOfFiniteUniv (H : (univ (α := α)).Finite) : Fintype α :=
  @Fintype.ofEquiv _ (univ : Set α) H.fintype (Equiv.Set.univ _)

/--
Instance `fintypeUnion` / 实例 `fintypeUnion`

English:
instance fintypeUnion
  signature: [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t]
  body: Fintype.ofFinset (s.toFinset union t.toFinset) by simp

中文:
实例 fintypeUnion
  签名: [DecidableEq α] (s t : 集合 α) [有限类型 s] [有限类型 t]
  定义体: Fintype.ofFinset (s.toFinset union t.toFinset) by simp

Depends on / 依赖: Fintype, Fintype.ofFinset, ofFinset, s.toFinset, t.toFinset, toFinset
-/
instance fintypeUnion [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] :
    Fintype (s union t : Set α) :=
Fintype.ofFinset (s.toFinset union t.toFinset) by simp

/--
Instance `fintypeSep` / 实例 `fintypeSep`

English:
instance fintypeSep
  signature: (s : Set α) (p : α -> Prop) [Fintype s] [DecidablePred p]
  body: Fintype.ofFinset {a in s.toFinset | p a} by simp

中文:
实例 fintypeSep
  签名: (s : 集合 α) (p : α -> 命题) [有限类型 s] [DecidablePred p]
  定义体: Fintype.ofFinset {a in s.toFinset | p a} by simp

Depends on / 依赖: Fintype, Fintype.ofFinset, ofFinset, s.toFinset, toFinset
-/
instance fintypeSep (s : Set α) (p : α -> Prop) [Fintype s] [DecidablePred p] :
    Fintype ({ a in s | p a } : Set α) :=
Fintype.ofFinset {a in s.toFinset | p a} by simp

/--
Instance `fintypeInter` / 实例 `fintypeInter`

English:
instance fintypeInter
  signature: (s t : Set α) [DecidableEq α] [Fintype s] [Fintype t]
  body: Fintype.ofFinset (s.toFinset inter t.toFinset) by simp

中文:
实例 fintype整数er
  签名: (s t : 集合 α) [DecidableEq α] [有限类型 s] [有限类型 t]
  定义体: Fintype.ofFinset (s.toFinset inter t.toFinset) by simp

Depends on / 依赖: Fintype, Fintype.ofFinset, ofFinset, s.toFinset, t.toFinset, toFinset
-/
instance fintypeInter (s t : Set α) [DecidableEq α] [Fintype s] [Fintype t] :
    Fintype (s inter t : Set α) :=
Fintype.ofFinset (s.toFinset inter t.toFinset) by simp

/--
Instance `fintypeInterOfLeft` / 实例 `fintypeInterOfLeft`

English:
instance fintypeInterOfLeft
  signature: (s t : Set α) [Fintype s] [DecidablePred (· in t)]
  body: Fintype.ofFinset {a in s.toFinset | a in t} by simp

中文:
实例 fintype整数erOfLeft
  签名: (s t : 集合 α) [有限类型 s] [DecidablePred (· in t)]
  定义体: Fintype.ofFinset {a in s.toFinset | a in t} by simp

Depends on / 依赖: Fintype, Fintype.ofFinset, ofFinset, s.toFinset, toFinset
-/
instance fintypeInterOfLeft (s t : Set α) [Fintype s] [DecidablePred (· in t)] :
    Fintype (s inter t : Set α) :=
Fintype.ofFinset {a in s.toFinset | a in t} by simp

/--
Instance `fintypeInterOfRight` / 实例 `fintypeInterOfRight`

English:
instance fintypeInterOfRight
  signature: (s t : Set α) [Fintype t] [DecidablePred (· in s)]
  body: Fintype.ofFinset {a in t.toFinset | a in s} by simp [and_comm]

中文:
实例 fintype整数erOfRight
  签名: (s t : 集合 α) [有限类型 t] [DecidablePred (· in s)]
  定义体: Fintype.ofFinset {a in t.toFinset | a in s} by simp [and_comm]

Depends on / 依赖: Fintype, Fintype.ofFinset, and_comm, ofFinset, t.toFinset, toFinset
-/
instance fintypeInterOfRight (s t : Set α) [Fintype t] [DecidablePred (· in s)] :
    Fintype (s inter t : Set α) :=
Fintype.ofFinset {a in t.toFinset | a in s} by simp [and_comm]

/-- A `Fintype` structure on a set defines a `Fintype` structure on its subset. -/
@[instance_reducible]
/--
Definition of `fintypeSubset` / `fintypeSubset` 的定义

English:
definition fintypeSubset
  signature: (s : Set α) {t : Set α} [Fintype s] [DecidablePred (· in t)] (h : t subseteq s)
  body: by
  rw [← inter_eq_self_of_subset_right h]
  apply Set.fintypeInterOfLeft

中文:
定义 fintypeSubset
  签名: (s : 集合 α) {t : 集合 α} [有限类型 s] [DecidablePred (· in t)] (h : t subseteq s)
  定义体: by
  rw [← inter_eq_self_of_subset_right h]
  apply Set.fintypeInterOfLeft

Depends on / 依赖: Set.fintypeInterOfLeft, fintypeInterOfLeft, inter_eq_self_of_subset_right
-/
def fintypeSubset (s : Set α) {t : Set α} [Fintype s] [DecidablePred (· in t)] (h : t subseteq s) :
    Fintype t := by
  rw [← inter_eq_self_of_subset_right h]
  apply Set.fintypeInterOfLeft

/--
Instance `fintypeDiff` / 实例 `fintypeDiff`

English:
instance fintypeDiff
  signature: [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t]
  body: Fintype.ofFinset (s.toFinset \ t.toFinset) by simp

中文:
实例 fintypeDiff
  签名: [DecidableEq α] (s t : 集合 α) [有限类型 s] [有限类型 t]
  定义体: Fintype.ofFinset (s.toFinset \ t.toFinset) by simp

Depends on / 依赖: Fintype, Fintype.ofFinset, ofFinset, s.toFinset, t.toFinset, toFinset
-/
instance fintypeDiff [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] :
    Fintype (s \ t : Set α) :=
Fintype.ofFinset (s.toFinset \ t.toFinset) by simp

/--
Instance `fintypeDiffLeft` / 实例 `fintypeDiffLeft`

English:
instance fintypeDiffLeft
  signature: (s t : Set α) [Fintype s] [DecidablePred (· in t)]
  body: Set.fintypeSep s (· in tᶜ)

中文:
实例 fintypeDiffLeft
  签名: (s t : 集合 α) [有限类型 s] [DecidablePred (· in t)]
  定义体: Set.fintypeSep s (· in tᶜ)

Depends on / 依赖: Set.fintypeSep, fintypeSep
-/
instance fintypeDiffLeft (s t : Set α) [Fintype s] [DecidablePred (· in t)] :
    Fintype (s \ t : Set α) :=
  Set.fintypeSep s (· in tᶜ)

/--
Instance `fintypeEmpty` / 实例 `fintypeEmpty`

English:
instance fintypeEmpty
  signature: : Fintype (∅ : Set α)
  body: Fintype.ofFinset ∅ by simp

中文:
实例 fintypeEmpty
  签名: : 有限类型 (∅ : 集合 α)
  定义体: Fintype.ofFinset ∅ by simp

Depends on / 依赖: Fintype, Fintype.ofFinset, ofFinset
-/
instance fintypeEmpty : Fintype (∅ : Set α) :=
Fintype.ofFinset ∅ by simp

/--
Instance `fintypeSingleton` / 实例 `fintypeSingleton`

English:
instance fintypeSingleton
  signature: (a : α)
  body: Fintype.ofFinset {a} by simp

中文:
实例 fintypeSingleton
  签名: (a : α)
  定义体: Fintype.ofFinset {a} by simp

Depends on / 依赖: Fintype, Fintype.ofFinset, ofFinset
-/
instance fintypeSingleton (a : α) : Fintype ({a} : Set α) :=
Fintype.ofFinset {a} by simp

/--
Instance `fintypeInsert` / 实例 `fintypeInsert`

English:
instance fintypeInsert
  signature: (a : α) (s : Set α) [DecidableEq α] [Fintype s]
  body: Fintype.ofFinset (insert a s.toFinset) by simp

中文:
实例 fintypeInsert
  签名: (a : α) (s : 集合 α) [DecidableEq α] [有限类型 s]
  定义体: Fintype.ofFinset (insert a s.toFinset) by simp

Depends on / 依赖: Fintype, Fintype.ofFinset, insert, ofFinset, s.toFinset, toFinset
-/
instance fintypeInsert (a : α) (s : Set α) [DecidableEq α] [Fintype s] :
    Fintype (insert a s : Set α) :=
Fintype.ofFinset (insert a s.toFinset) by simp

set_option backward.isDefEq.respectTransparency false in
/-- A `Fintype` structure on `insert a s` when inserting a new element. -/
@[instance_reducible]
/--
Definition of `fintypeInsertOfNotMem` / `fintypeInsertOfNotMem` 的定义

English:
definition fintypeInsertOfNotMem
  signature: {a : α} (s : Set α) [Fintype s] (h : a ∉ s)
  body: Fintype.ofFinset ⟨a ::ₘ s.toFinset.1, s.toFinset.nodup.cons (by simp [h])⟩ by simp

中文:
定义 fintypeInsertOfNotMem
  签名: {a : α} (s : 集合 α) [有限类型 s] (h : a ∉ s)
  定义体: Fintype.ofFinset ⟨a ::ₘ s.toFinset.1, s.toFinset.nodup.cons (by simp [h])⟩ by simp

Depends on / 依赖: Fintype, Fintype.ofFinset, I.symm, ofFinset, s.toFinset, s.toFinset.nodup.cons, toFinset
-/
def fintypeInsertOfNotMem {a : α} (s : Set α) [Fintype s] (h : a ∉ s) :
    Fintype (insert a s : Set α) :=
Fintype.ofFinset ⟨a ::ₘ s.toFinset.1, s.toFinset.nodup.cons (by simp [h])⟩ by simp

/-- A `Fintype` structure on `insert a s` when inserting a pre-existing element. -/
@[instance_reducible]
/--
Definition of `fintypeInsertOfMem` / `fintypeInsertOfMem` 的定义

English:
definition fintypeInsertOfMem
  signature: {a : α} (s : Set α) [Fintype s] (h : a in s)
  body: Fintype.ofFinset s.toFinset by simp [h]

中文:
定义 fintypeInsertOfMem
  签名: {a : α} (s : 集合 α) [有限类型 s] (h : a in s)
  定义体: Fintype.ofFinset s.toFinset by simp [h]

Depends on / 依赖: Fintype, Fintype.ofFinset, ofFinset, s.toFinset, toFinset
-/
def fintypeInsertOfMem {a : α} (s : Set α) [Fintype s] (h : a in s) : Fintype (insert a s : Set α) :=
Fintype.ofFinset s.toFinset by simp [h]

/-- The `Set.fintypeInsert` instance requires decidable equality, but when `a ∈ s`
is decidable for this particular `a` we can still get a `Fintype` instance by using
`Set.fintypeInsertOfNotMem` or `Set.fintypeInsertOfMem`.

This instance pre-dates `Set.fintypeInsert`, and it is less efficient.
When `Set.decidableMemOfFintype` is made a local instance, then this instance would
override `Set.fintypeInsert` if not for the fact that its priority has been
adjusted. See Note [lower instance priority]. -/
instance (priority := 100) fintypeInsert' (a : α) (s : Set α) [Decidable <| a in s] [Fintype s] :
    Fintype (insert a s : Set α) :=
  if h : a in s then fintypeInsertOfMem s h else fintypeInsertOfNotMem s h

/--
Instance `fintypeImage` / 实例 `fintypeImage`

English:
instance fintypeImage
  signature: [DecidableEq β] (s : Set α) (f : α -> β) [Fintype s]
  body: Fintype.ofFinset (s.toFinset.image f) by simp

中文:
实例 fintypeImage
  签名: [DecidableEq β] (s : 集合 α) (f : α -> β) [有限类型 s]
  定义体: Fintype.ofFinset (s.toFinset.image f) by simp

Depends on / 依赖: Fintype, Fintype.ofFinset, ofFinset, s.toFinset.image, toFinset
-/
instance fintypeImage [DecidableEq β] (s : Set α) (f : α -> β) [Fintype s] : Fintype (f '' s) :=
Fintype.ofFinset (s.toFinset.image f) by simp

/-- If a function `f` has a partial inverse `g` and the image of `s` under `f` is a set with
a `Fintype` instance, then `s` has a `Fintype` structure as well. -/
@[instance_reducible]
/--
Definition of `fintypeOfFintypeImage` / `fintypeOfFintypeImage` 的定义

English:
definition fintypeOfFintypeImage
  signature: (s : Set α) {f : α -> β} {g} (I : IsPartialInv f g) [Fintype (f '' s)]
  body: Fintype.ofFinset ⟨_, (f '' s).toFinset.2.filterMap g injective_of_isPartialInv_right I⟩
    (by simp [I.eq])

中文:
定义 fintypeOfFintypeImage
  签名: (s : 集合 α) {f : α -> β} {g} (I : IsPartialInv f g) [有限类型 (f '' s)]
  定义体: Fintype.ofFinset ⟨_, (f '' s).toFinset.2.filterMap g injective_of_isPartialInv_right I⟩
    (by simp [I.eq])

Depends on / 依赖: Fintype, Fintype.ofFinset, I.eq, filterMap, injective_of_isPartialInv_right, ofFinset, toFinset
-/
def fintypeOfFintypeImage (s : Set α) {f : α -> β} {g} (I : IsPartialInv f g) [Fintype (f '' s)] :
    Fintype s :=
Fintype.ofFinset ⟨_, (f '' s).toFinset.2.filterMap g injective_of_isPartialInv_right I⟩
    (by simp [I.eq])

/--
Instance `fintypeMap` / 实例 `fintypeMap`

English:
instance fintypeMap
  signature: {α β} [DecidableEq β]
  body: Set.fintypeImage

中文:
实例 fintypeMap
  签名: {α β} [DecidableEq β]
  定义体: Set.fintypeImage

Depends on / 依赖: Set.fintypeImage, fintypeImage
-/
instance fintypeMap {α β} [DecidableEq β] :
    forall (s : Set α) (f : α -> β) [Fintype s], Fintype (f <$> s) :=
  Set.fintypeImage

/--
Instance `fintypeLTNat` / 实例 `fintypeLTNat`

English:
instance fintypeLTNat
  signature: (n : Nat)
  body: Fintype.ofFinset (Finset.range n) by simp

中文:
实例 fintypeLT自然数
  签名: (n : 自然数)
  定义体: Fintype.ofFinset (Finset.range n) by simp

Depends on / 依赖: Finset, Finset.range, Fintype, Fintype.ofFinset, ofFinset
-/
instance fintypeLTNat (n : Nat) : Fintype { i | i < n } :=
Fintype.ofFinset (Finset.range n) by simp

/--
Instance `fintypeLENat` / 实例 `fintypeLENat`

English:
instance fintypeLENat
  signature: (n : Nat)
  body: by
  simpa [Nat.lt_succ_iff] using Set.fintypeLTNat (n + 1)

中文:
实例 fintypeLE自然数
  签名: (n : 自然数)
  定义体: by
  simpa [Nat.lt_succ_iff] using Set.fintypeLTNat (n + 1)

Depends on / 依赖: Nat.lt_succ_iff, Set.fintypeLTNat, fintypeLTNat, lt_succ_iff
-/
instance fintypeLENat (n : Nat) : Fintype { i | i <= n } := by
  simpa [Nat.lt_succ_iff] using Set.fintypeLTNat (n + 1)

/-- This is not an instance so that it does not conflict with the one
in `Mathlib/Order/Interval/Finset/Defs.lean`. -/
@[instance_reducible]
/--
Definition of `Nat.fintypeIio` / `Nat.fintypeIio` 的定义

English:
definition Nat.fintypeIio
  signature: (n : Nat)
  body: Set.fintypeLTNat n

中文:
定义 自然数.fintypeIio
  签名: (n : 自然数)
  定义体: Set.fintypeLTNat n

Depends on / 依赖: Set.fintypeLTNat, fintypeLTNat
-/
def Nat.fintypeIio (n : Nat) : Fintype (Iio n) :=
  Set.fintypeLTNat n

/--
Instance `fintypeMemFinset` / 实例 `fintypeMemFinset`

English:
instance fintypeMemFinset
  signature: (s : Finset α)
  body: Finset.fintypeCoeSort s

中文:
实例 fintypeMemFinset
  签名: (s : 有限集 α)
  定义体: Finset.fintypeCoeSort s

Depends on / 依赖: Finset, Finset.fintypeCoeSort, fintypeCoeSort
-/
instance fintypeMemFinset (s : Finset α) : Fintype { a | a in s } :=
  Finset.fintypeCoeSort s

end FintypeInstances

end Set

/-! ### Finset -/

namespace Finset

/-- Gives a `Set.Finite` for the `Finset` coerced to a `Set`.
This is a wrapper around `Set.toFinite`. -/
@[simp]
/--
theorem `finite_toSet` / 定理 `finite_toSet`

English:
theorem finite_toSet
  given: (s : Finset α)
  statement: (s : Set α).Finite
  proof: Set.toFinite _

中文:
定理 finite_toSet
  条件: (s : 有限集 α)
  结论: (s : 集合 α).有限
  证明: Set.toFinite _

Depends on / 依赖: Set.toFinite, toFinite
-/
theorem finite_toSet (s : Finset α) : (s : Set α).Finite :=
  Set.toFinite _

/--
theorem `finite_toSet_toFinset` / 定理 `finite_toSet_toFinset`

English:
theorem finite_toSet_toFinset
  given: (s : Finset α)
  statement: s.finite_toSet.toFinset = s
  proof: by
  rw [toFinite_toFinset]; rw [toFinset_coe]

中文:
定理 finite_toSet_toFinset
  条件: (s : 有限集 α)
  结论: s.finite_toSet.toFinset = s
  证明: by
  rw [toFinite_toFinset]; rw [toFinset_coe]

Depends on / 依赖: toFinite_toFinset, toFinset_coe
-/
theorem finite_toSet_toFinset (s : Finset α) : s.finite_toSet.toFinset = s := by
  rw [toFinite_toFinset]; rw [toFinset_coe]

/--
lemma `«forall»` / 引理 `«forall»`

English:
lemma «forall»
  given: {p : Finset α -> Prop}
  proof: h _
  mpr h s := by simpa using h s s.finite_toSet

中文:
引理 «对任意»
  条件: {p : 有限集 α -> 命题}
  证明: h _
  mpr h s := by simpa using h s s.finite_toSet
-/
lemma «forall» {p : Finset α -> Prop} :
    (forall s, p s) ↔ forall (s : Set α) (hs : s.Finite), p hs.toFinset where
  mp h s hs := h _
  mpr h s := by simpa using h s s.finite_toSet

/--
lemma `«exists»` / 引理 `«exists»`

English:
lemma «exists»
  given: {p : Finset α -> Prop}
  proof: fun ⟨s, hs⟩ => ⟨s, s.finite_toSet, by simpa⟩
  mpr := fun ⟨s, hs, hs'⟩ => ⟨hs.toFinset, hs'⟩

中文:
引理 «存在»
  条件: {p : 有限集 α -> 命题}
  证明: fun ⟨s, hs⟩ => ⟨s, s.finite_toSet, by simpa⟩
  mpr := fun ⟨s, hs, hs'⟩ => ⟨hs.toFinset, hs'⟩
-/
lemma «exists» {p : Finset α -> Prop} :
    (exists s, p s) ↔ exists (s : Set α) (hs : s.Finite), p hs.toFinset where
  mp := fun ⟨s, hs⟩ => ⟨s, s.finite_toSet, by simpa⟩
  mpr := fun ⟨s, hs, hs'⟩ => ⟨hs.toFinset, hs'⟩

/--
lemma `mem_range_coe_iff` / 引理 `mem_range_coe_iff`

English:
lemma mem_range_coe_iff
  given: {s : Set α}
  statement: s in Set.range ((↑) : Finset α -> Set α) ↔ s.Finite where
  proof: by
    rintro ⟨t, rfl⟩
    simp
  mpr hs := ⟨hs.toFinset, by simp⟩

中文:
引理 mem_range_coe_iff
  条件: {s : 集合 α}
  结论: s in 集合.range ((↑) : 有限集 α -> 集合 α) ↔ s.有限 where
  证明: by
    rintro ⟨t, rfl⟩
    simp
  mpr hs := ⟨hs.toFinset, by simp⟩

Depends on / 依赖: hs.toFinset, toFinset
-/
lemma mem_range_coe_iff {s : Set α} : s in Set.range ((↑) : Finset α -> Set α) ↔ s.Finite where
  mp := by
    rintro ⟨t, rfl⟩
    simp
  mpr hs := ⟨hs.toFinset, by simp⟩

end Finset

namespace Multiset

@[simp]
/--
theorem `finite_toSet` / 定理 `finite_toSet`

English:
theorem finite_toSet
  given: (s : Multiset α)
  statement: { x | x in s }.Finite
  proof: by
  classical simpa only [← Multiset.mem_toFinset] using! s.toFinset.finite_toSet

@[simp]

中文:
定理 finite_toSet
  条件: (s : Multiset α)
  结论: { x | x in s }.有限
  证明: by
  classical simpa only [← Multiset.mem_toFinset] using! s.toFinset.finite_toSet

@[simp]

Depends on / 依赖: Multiset, Multiset.mem_toFinset, classical, finite_toSet, mem_toFinset, s.toFinset.finite_toSet, toFinset
-/
theorem finite_toSet (s : Multiset α) : { x | x in s }.Finite := by
  classical simpa only [← Multiset.mem_toFinset] using! s.toFinset.finite_toSet

@[simp]
/--
theorem `finite_toSet_toFinset` / 定理 `finite_toSet_toFinset`

English:
theorem finite_toSet_toFinset
  given: [DecidableEq α] (s : Multiset α)
  proof: by
  ext x
  simp

中文:
定理 finite_toSet_toFinset
  条件: [DecidableEq α] (s : Multiset α)
  证明: by
  ext x
  simp
-/
theorem finite_toSet_toFinset [DecidableEq α] (s : Multiset α) :
    s.finite_toSet.toFinset = s.toFinset := by
  ext x
  simp

end Multiset

@[simp]
/--
theorem `List.finite_toSet` / 定理 `List.finite_toSet`

English:
theorem List.finite_toSet
  given: (l : List α)
  statement: { x | x in l }.Finite
  proof: (show Multiset α from ⟦l⟧).finite_toSet

中文:
定理 列表.finite_toSet
  条件: (l : 列表 α)
  结论: { x | x in l }.有限
  证明: (show Multiset α from ⟦l⟧).finite_toSet

Depends on / 依赖: Multiset, finite_toSet
-/
theorem List.finite_toSet (l : List α) : { x | x in l }.Finite :=
  (show Multiset α from ⟦l⟧).finite_toSet

/--
Definition of `OrderIso.finsetSetFinite` / `OrderIso.finsetSetFinite` 的定义

English:
definition OrderIso.finsetSetFinite
  signature: : Finset α ≃o {s : Set α // s.Finite} where
  body: ⟨s, s.finite_toSet⟩
  invFun s := s.2.toFinset
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' := .rfl

中文:
定义 OrderIso.finsetSetFinite
  签名: : 有限集 α ≃o {s : 集合 α // s.有限} where
  定义体: ⟨s, s.finite_toSet⟩
  invFun s := s.2.toFinset
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' := .rfl
-/
@[simps] noncomputable def OrderIso.finsetSetFinite : Finset α ≃o {s : Set α // s.Finite} where
  toFun s := ⟨s, s.finite_toSet⟩
  invFun s := s.2.toFinset
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedLT {s : Set α // s.Finite}
  body: OrderIso.finsetSetFinite.symm.toOrderEmbedding.wellFoundedLT

中文:
实例 :
  签名: WellFoundedLT {s : 集合 α // s.有限}
  定义体: OrderIso.finsetSetFinite.symm.toOrderEmbedding.wellFoundedLT
-/
instance : WellFoundedLT {s : Set α // s.Finite} :=
  OrderIso.finsetSetFinite.symm.toOrderEmbedding.wellFoundedLT

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/


namespace Finite.Set

example {s : Set α} [Finite α] : Finite s :=
  inferInstance

example : Finite (∅ : Set α) :=
  inferInstance

example (a : α) : Finite ({a} : Set α) :=
  inferInstance

/--
Instance `finite_union` / 实例 `finite_union`

English:
instance finite_union
  signature: (s t : Set α) [Finite s] [Finite t]
  body: by
  cases nonempty_fintype s
  cases nonempty_fintype t
  classical
  infer_instance

中文:
实例 finite_union
  签名: (s t : 集合 α) [有限 s] [有限 t]
  定义体: by
  cases nonempty_fintype s
  cases nonempty_fintype t
  classical
  infer_instance

Depends on / 依赖: classical, infer_instance, nonempty_fintype
-/
instance finite_union (s t : Set α) [Finite s] [Finite t] : Finite (s union t : Set α) := by
  cases nonempty_fintype s
  cases nonempty_fintype t
  classical
  infer_instance

/--
Instance `finite_sep` / 实例 `finite_sep`

English:
instance finite_sep
  signature: (s : Set α) (p : α -> Prop) [Finite s]
  body: by
  cases nonempty_fintype s
  classical
  infer_instance

中文:
实例 finite_sep
  签名: (s : 集合 α) (p : α -> 命题) [有限 s]
  定义体: by
  cases nonempty_fintype s
  classical
  infer_instance

Depends on / 依赖: classical, infer_instance, nonempty_fintype
-/
instance finite_sep (s : Set α) (p : α -> Prop) [Finite s] : Finite ({ a in s | p a } : Set α) := by
  cases nonempty_fintype s
  classical
  infer_instance

/--
theorem `subset` / 定理 `subset`

English:
theorem subset
  given: (s : Set α) {t : Set α} [Finite s] (h : t subseteq s)
  statement: Finite t
  proof: by
  rw [← sep_eq_of_subset h]
  infer_instance

中文:
定理 subset
  条件: (s : 集合 α) {t : 集合 α} [有限 s] (h : t subseteq s)
  结论: 有限 t
  证明: by
  rw [← sep_eq_of_subset h]
  infer_instance
-/
protected theorem subset (s : Set α) {t : Set α} [Finite s] (h : t subseteq s) : Finite t := by
  rw [← sep_eq_of_subset h]
  infer_instance

/--
Instance `finite_inter_of_right` / 实例 `finite_inter_of_right`

English:
instance finite_inter_of_right
  signature: (s t : Set α) [Finite t]
  body: Finite.Set.subset t inter_subset_right

中文:
实例 finite_inter_of_right
  签名: (s t : 集合 α) [有限 t]
  定义体: Finite.Set.subset t inter_subset_right

Depends on / 依赖: Finite, Finite.Set.subset, inter_subset_right, subset
-/
instance finite_inter_of_right (s t : Set α) [Finite t] : Finite (s inter t : Set α) :=
  Finite.Set.subset t inter_subset_right

/--
Instance `finite_inter_of_left` / 实例 `finite_inter_of_left`

English:
instance finite_inter_of_left
  signature: (s t : Set α) [Finite s]
  body: Finite.Set.subset s inter_subset_left

中文:
实例 finite_inter_of_left
  签名: (s t : 集合 α) [有限 s]
  定义体: Finite.Set.subset s inter_subset_left

Depends on / 依赖: Finite, Finite.Set.subset, inter_subset_left, subset
-/
instance finite_inter_of_left (s t : Set α) [Finite s] : Finite (s inter t : Set α) :=
  Finite.Set.subset s inter_subset_left

/--
Instance `finite_diff` / 实例 `finite_diff`

English:
instance finite_diff
  signature: (s t : Set α) [Finite s]
  body: Finite.Set.subset s sdiff_subset

中文:
实例 finite_diff
  签名: (s t : 集合 α) [有限 s]
  定义体: Finite.Set.subset s sdiff_subset

Depends on / 依赖: Finite, Finite.Set.subset, sdiff_subset, subset
-/
instance finite_diff (s t : Set α) [Finite s] : Finite (s \ t : Set α) :=
  Finite.Set.subset s sdiff_subset

/--
Instance `finite_insert` / 实例 `finite_insert`

English:
instance finite_insert
  signature: (a : α) (s : Set α) [Finite s]
  body: Finite.Set.finite_union {a} s

中文:
实例 finite_insert
  签名: (a : α) (s : 集合 α) [有限 s]
  定义体: Finite.Set.finite_union {a} s

Depends on / 依赖: Finite, Finite.Set.finite_union, finite_union
-/
instance finite_insert (a : α) (s : Set α) [Finite s] : Finite (insert a s : Set α) :=
  Finite.Set.finite_union {a} s

/--
Instance `finite_image` / 实例 `finite_image`

English:
instance finite_image
  signature: (s : Set α) (f : α -> β) [Finite s]
  body: by
  cases nonempty_fintype s
  classical
  infer_instance

中文:
实例 finite_image
  签名: (s : 集合 α) (f : α -> β) [有限 s]
  定义体: by
  cases nonempty_fintype s
  classical
  infer_instance

Depends on / 依赖: classical, infer_instance, nonempty_fintype
-/
instance finite_image (s : Set α) (f : α -> β) [Finite s] : Finite (f '' s) := by
  cases nonempty_fintype s
  classical
  infer_instance

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/

section SetFiniteConstructors
variable {s t u : Set α} {a : α}

@[nontriviality]
/--
theorem `Finite.of_subsingleton` / 定理 `Finite.of_subsingleton`

English:
theorem Finite.of_subsingleton
  given: [Subsingleton α] (s : Set α)
  statement: s.Finite
  proof: s.toFinite

中文:
定理 有限.of_subsingleton
  条件: [子单例 α] (s : 集合 α)
  结论: s.有限
  证明: s.toFinite

Depends on / 依赖: s.toFinite, toFinite
-/
theorem Finite.of_subsingleton [Subsingleton α] (s : Set α) : s.Finite :=
  s.toFinite

/--
theorem `finite_univ` / 定理 `finite_univ`

English:
theorem finite_univ
  given: [Finite α]
  statement: (@univ α).Finite
  proof: Set.toFinite _

中文:
定理 finite_univ
  条件: [有限 α]
  结论: (@univ α).有限
  证明: Set.toFinite _
-/
@[simp] theorem finite_univ [Finite α] : (@univ α).Finite := Set.toFinite _

/--
theorem `finite_univ_iff` / 定理 `finite_univ_iff`

English:
theorem finite_univ_iff
  statement: (@univ α).Finite ↔ Finite α
  proof: (Equiv.Set.univ α).finite_iff

alias ⟨_root_.Finite.of_finite_univ, _⟩ := finite_univ_iff

中文:
定理 finite_univ_iff
  结论: (@univ α).有限 ↔ 有限 α
  证明: (Equiv.Set.univ α).finite_iff

alias ⟨_root_.Finite.of_finite_univ, _⟩ := finite_univ_iff

Depends on / 依赖: Equiv.Set.univ, finite_iff
-/
theorem finite_univ_iff : (@univ α).Finite ↔ Finite α := (Equiv.Set.univ α).finite_iff

alias ⟨_root_.Finite.of_finite_univ, _⟩ := finite_univ_iff

/--
theorem `Finite.subset` / 定理 `Finite.subset`

English:
theorem Finite.subset
  given: {s : Set α} (hs : s.Finite) {t : Set α} (ht : t subseteq s)
  statement: t.Finite
  proof: by
  have := hs.to_subtype
  exact Finite.Set.subset _ ht

中文:
定理 有限.subset
  条件: {s : 集合 α} (hs : s.有限) {t : 集合 α} (ht : t subseteq s)
  结论: t.有限
  证明: by
  have := hs.to_subtype
  exact Finite.Set.subset _ ht

Depends on / 依赖: Finite, Finite.Set.subset, hs.to_subtype, subset, to_subtype
-/
theorem Finite.subset {s : Set α} (hs : s.Finite) {t : Set α} (ht : t subseteq s) : t.Finite := by
  have := hs.to_subtype
  exact Finite.Set.subset _ ht

/--
theorem `Finite.union` / 定理 `Finite.union`

English:
theorem Finite.union
  given: (hs : s.Finite) (ht : t.Finite)
  statement: (s union t).Finite
  proof: by
  rw [Set.Finite] at hs ht
  apply toFinite

中文:
定理 有限.union
  条件: (hs : s.有限) (ht : t.有限)
  结论: (s union t).有限
  证明: by
  rw [Set.Finite] at hs ht
  apply toFinite

Depends on / 依赖: Finite, Set.Finite, toFinite
-/
theorem Finite.union (hs : s.Finite) (ht : t.Finite) : (s union t).Finite := by
  rw [Set.Finite] at hs ht
  apply toFinite

/--
theorem `Finite.finite_of_compl` / 定理 `Finite.finite_of_compl`

English:
theorem Finite.finite_of_compl
  given: {s : Set α} (hs : s.Finite) (hsc : sᶜ.Finite)
  statement: Finite α
  proof: by
  rw [← finite_univ_iff]; rw [← union_compl_self s]
  exact hs.union hsc

中文:
定理 有限.finite_of_compl
  条件: {s : 集合 α} (hs : s.有限) (hsc : sᶜ.有限)
  结论: 有限 α
  证明: by
  rw [← finite_univ_iff]; rw [← union_compl_self s]
  exact hs.union hsc

Depends on / 依赖: finite_univ_iff, hs.union, union_compl_self
-/
theorem Finite.finite_of_compl {s : Set α} (hs : s.Finite) (hsc : sᶜ.Finite) : Finite α := by
  rw [← finite_univ_iff]; rw [← union_compl_self s]
  exact hs.union hsc

/--
theorem `Finite.sup` / 定理 `Finite.sup`

English:
theorem Finite.sup
  given: {s t : Set α}
  statement: s.Finite -> t.Finite -> (s ⊔ t).Finite
  proof: Finite.union

中文:
定理 有限.上确界
  条件: {s t : 集合 α}
  结论: s.有限 -> t.有限 -> (s ⊔ t).有限
  证明: Finite.union

Depends on / 依赖: Finite, Finite.union
-/
theorem Finite.sup {s t : Set α} : s.Finite -> t.Finite -> (s ⊔ t).Finite :=
  Finite.union

/--
theorem `Finite.sep` / 定理 `Finite.sep`

English:
theorem Finite.sep
  given: {s : Set α} (hs : s.Finite) (p : α -> Prop)
  statement: { a in s | p a }.Finite
  proof: hs.subset sep_subset _ _

中文:
定理 有限.sep
  条件: {s : 集合 α} (hs : s.有限) (p : α -> 命题)
  结论: { a in s | p a }.有限
  证明: hs.subset sep_subset _ _

Depends on / 依赖: hs.subset, sep_subset, subset
-/
theorem Finite.sep {s : Set α} (hs : s.Finite) (p : α -> Prop) : { a in s | p a }.Finite :=
hs.subset sep_subset _ _

/--
theorem `Finite.inter_of_left` / 定理 `Finite.inter_of_left`

English:
theorem Finite.inter_of_left
  given: {s : Set α} (hs : s.Finite) (t : Set α)
  statement: (s inter t).Finite
  proof: hs.subset inter_subset_left

中文:
定理 有限.inter_of_left
  条件: {s : 集合 α} (hs : s.有限) (t : 集合 α)
  结论: (s inter t).有限
  证明: hs.subset inter_subset_left

Depends on / 依赖: hs.subset, inter_subset_left, subset
-/
theorem Finite.inter_of_left {s : Set α} (hs : s.Finite) (t : Set α) : (s inter t).Finite :=
  hs.subset inter_subset_left

/--
theorem `Finite.inter_of_right` / 定理 `Finite.inter_of_right`

English:
theorem Finite.inter_of_right
  given: {s : Set α} (hs : s.Finite) (t : Set α)
  statement: (t inter s).Finite
  proof: hs.subset inter_subset_right

中文:
定理 有限.inter_of_right
  条件: {s : 集合 α} (hs : s.有限) (t : 集合 α)
  结论: (t inter s).有限
  证明: hs.subset inter_subset_right

Depends on / 依赖: hs.subset, inter_subset_right, subset
-/
theorem Finite.inter_of_right {s : Set α} (hs : s.Finite) (t : Set α) : (t inter s).Finite :=
  hs.subset inter_subset_right

/--
theorem `Finite.inf_of_left` / 定理 `Finite.inf_of_left`

English:
theorem Finite.inf_of_left
  given: {s : Set α} (h : s.Finite) (t : Set α)
  statement: (s ⊓ t).Finite
  proof: h.inter_of_left t

中文:
定理 有限.inf_of_left
  条件: {s : 集合 α} (h : s.有限) (t : 集合 α)
  结论: (s ⊓ t).有限
  证明: h.inter_of_left t

Depends on / 依赖: h.inter_of_left, inter_of_left
-/
theorem Finite.inf_of_left {s : Set α} (h : s.Finite) (t : Set α) : (s ⊓ t).Finite :=
  h.inter_of_left t

/--
theorem `Finite.inf_of_right` / 定理 `Finite.inf_of_right`

English:
theorem Finite.inf_of_right
  given: {s : Set α} (h : s.Finite) (t : Set α)
  statement: (t ⊓ s).Finite
  proof: h.inter_of_right t

中文:
定理 有限.inf_of_right
  条件: {s : 集合 α} (h : s.有限) (t : 集合 α)
  结论: (t ⊓ s).有限
  证明: h.inter_of_right t

Depends on / 依赖: h.inter_of_right, inter_of_right
-/
theorem Finite.inf_of_right {s : Set α} (h : s.Finite) (t : Set α) : (t ⊓ s).Finite :=
  h.inter_of_right t

/--
lemma `Infinite.mono` / 引理 `Infinite.mono`

English:
lemma Infinite.mono
  given: {s t : Set α} (h : s subseteq t)
  statement: s.Infinite -> t.Infinite
  proof: mt fun ht => ht.subset h

中文:
引理 无限.mono
  条件: {s t : 集合 α} (h : s subseteq t)
  结论: s.无限 -> t.无限
  证明: mt fun ht => ht.subset h
-/
protected lemma Infinite.mono {s t : Set α} (h : s subseteq t) : s.Infinite -> t.Infinite :=
  mt fun ht => ht.subset h

/--
theorem `Finite.sdiff` / 定理 `Finite.sdiff`

English:
theorem Finite.sdiff
  given: (hs : s.Finite)
  statement: (s \ t).Finite
  proof: hs.subset sdiff_subset

@[deprecated (since := "2026-06-03")] alias Finite.diff := Finite.sdiff

中文:
定理 有限.sdiff
  条件: (hs : s.有限)
  结论: (s \ t).有限
  证明: hs.subset sdiff_subset

@[deprecated (since := "2026-06-03")] alias Finite.diff := Finite.sdiff
-/
@[simp] theorem Finite.sdiff (hs : s.Finite) : (s \ t).Finite := hs.subset sdiff_subset

@[deprecated (since := "2026-06-03")] alias Finite.diff := Finite.sdiff

/--
theorem `Finite.of_sdiff` / 定理 `Finite.of_sdiff`

English:
theorem Finite.of_sdiff
  given: {s t : Set α} (hd : (s \ t).Finite) (ht : t.Finite)
  statement: s.Finite
  proof: (hd.union ht).subset subset_sdiff_union _ _

@[deprecated (since := "2026-06-03")] alias Finite.of_diff := Finite.of_sdiff

@[simp]

中文:
定理 有限.of_sdiff
  条件: {s t : 集合 α} (hd : (s \ t).有限) (ht : t.有限)
  结论: s.有限
  证明: (hd.union ht).subset subset_sdiff_union _ _

@[deprecated (since := "2026-06-03")] alias Finite.of_diff := Finite.of_sdiff

@[simp]

Depends on / 依赖: hd.union, subset, subset_sdiff_union
-/
theorem Finite.of_sdiff {s t : Set α} (hd : (s \ t).Finite) (ht : t.Finite) : s.Finite :=
(hd.union ht).subset subset_sdiff_union _ _

@[deprecated (since := "2026-06-03")] alias Finite.of_diff := Finite.of_sdiff

@[simp]
/--
lemma `Finite.symmDiff` / 引理 `Finite.symmDiff`

English:
lemma Finite.symmDiff
  given: (hs : s.Finite) (ht : t.Finite)
  statement: (s ∆ t).Finite
  proof: hs.sdiff.union ht.sdiff

中文:
引理 有限.symmDiff
  条件: (hs : s.有限) (ht : t.有限)
  结论: (s ∆ t).有限
  证明: hs.sdiff.union ht.sdiff

Depends on / 依赖: hs.sdiff.union, ht.sdiff
-/
lemma Finite.symmDiff (hs : s.Finite) (ht : t.Finite) : (s ∆ t).Finite := hs.sdiff.union ht.sdiff

/--
lemma `Finite.symmDiff_congr` / 引理 `Finite.symmDiff_congr`

English:
lemma Finite.symmDiff_congr
  given: (hst : (s ∆ t).Finite)
  statement: (s ∆ u).Finite ↔ (t ∆ u).Finite where
  proof: (hst.union hsu).subset (symmDiff_comm s t ▸ symmDiff_triangle ..)
  mpr htu := (hst.union htu).subset (symmDiff_triangle ..)

@[simp, grind .]

中文:
引理 有限.symmDiff_congr
  条件: (hst : (s ∆ t).有限)
  结论: (s ∆ u).有限 ↔ (t ∆ u).有限 where
  证明: (hst.union hsu).subset (symmDiff_comm s t ▸ symmDiff_triangle ..)
  mpr htu := (hst.union htu).subset (symmDiff_triangle ..)

@[simp, grind .]

Depends on / 依赖: hst.union, subset, symmDiff_comm, symmDiff_triangle
-/
lemma Finite.symmDiff_congr (hst : (s ∆ t).Finite) : (s ∆ u).Finite ↔ (t ∆ u).Finite where
  mp hsu := (hst.union hsu).subset (symmDiff_comm s t ▸ symmDiff_triangle ..)
  mpr htu := (hst.union htu).subset (symmDiff_triangle ..)

@[simp, grind .]
/--
theorem `finite_empty` / 定理 `finite_empty`

English:
theorem finite_empty
  statement: (∅ : Set α).Finite
  proof: toFinite _

中文:
定理 finite_empty
  结论: (∅ : 集合 α).有限
  证明: toFinite _

Depends on / 依赖: toFinite
-/
theorem finite_empty : (∅ : Set α).Finite :=
  toFinite _

/--
theorem `Infinite.nonempty` / 定理 `Infinite.nonempty`

English:
theorem Infinite.nonempty
  given: {s : Set α} (h : s.Infinite)
  statement: s.Nonempty
  proof: nonempty_iff_ne_empty.2 by
    rintro rfl
    exact h finite_empty

@[simp]

中文:
定理 无限.nonempty
  条件: {s : 集合 α} (h : s.无限)
  结论: s.非空
  证明: nonempty_iff_ne_empty.2 by
    rintro rfl
    exact h finite_empty

@[simp]
-/
protected theorem Infinite.nonempty {s : Set α} (h : s.Infinite) : s.Nonempty :=
nonempty_iff_ne_empty.2 by
    rintro rfl
    exact h finite_empty

@[simp]
/--
theorem `finite_singleton` / 定理 `finite_singleton`

English:
theorem finite_singleton
  given: (a : α)
  statement: ({a} : Set α).Finite
  proof: toFinite _

中文:
定理 finite_singleton
  条件: (a : α)
  结论: ({a} : 集合 α).有限
  证明: toFinite _

Depends on / 依赖: toFinite
-/
theorem finite_singleton (a : α) : ({a} : Set α).Finite :=
  toFinite _

/--
theorem `Finite.insert` / 定理 `Finite.insert`

English:
theorem Finite.insert
  given: (a : α) {s : Set α} (hs : s.Finite)
  statement: (insert a s).Finite
  proof: (finite_singleton a).union hs

中文:
定理 有限.insert
  条件: (a : α) {s : 集合 α} (hs : s.有限)
  结论: (insert a s).有限
  证明: (finite_singleton a).union hs
-/
protected theorem Finite.insert (a : α) {s : Set α} (hs : s.Finite) : (insert a s).Finite :=
  (finite_singleton a).union hs

/--
lemma `finite_insert` / 引理 `finite_insert`

English:
lemma finite_insert
  statement: (insert a s).Finite ↔ s.Finite where
  proof: hs.subset subset_insert ..
  mpr := .insert _

中文:
引理 finite_insert
  结论: (insert a s).有限 ↔ s.有限 where
  证明: hs.subset subset_insert ..
  mpr := .insert _
-/
@[simp] lemma finite_insert : (insert a s).Finite ↔ s.Finite where
mp hs := hs.subset subset_insert ..
  mpr := .insert _

/--
theorem `Finite.image` / 定理 `Finite.image`

English:
theorem Finite.image
  given: {s : Set α} (f : α -> β) (hs : s.Finite)
  statement: (f '' s).Finite
  proof: by
  have := hs.to_subtype
  apply toFinite

中文:
定理 有限.像
  条件: {s : 集合 α} (f : α -> β) (hs : s.有限)
  结论: (f '' s).有限
  证明: by
  have := hs.to_subtype
  apply toFinite

Depends on / 依赖: hs.to_subtype, toFinite, to_subtype
-/
theorem Finite.image {s : Set α} (f : α -> β) (hs : s.Finite) : (f '' s).Finite := by
  have := hs.to_subtype
  apply toFinite

/--
lemma `Finite.of_surjOn` / 引理 `Finite.of_surjOn`

English:
lemma Finite.of_surjOn
  given: {s : Set α} {t : Set β} (f : α -> β) (hf : SurjOn f s t) (hs : s.Finite)
  proof: (hs.image _).subset hf

中文:
引理 有限.of_surjOn
  条件: {s : 集合 α} {t : 集合 β} (f : α -> β) (hf : 满射限制 f s t) (hs : s.有限)
  证明: (hs.image _).subset hf

Depends on / 依赖: hs.image, subset
-/
lemma Finite.of_surjOn {s : Set α} {t : Set β} (f : α -> β) (hf : SurjOn f s t) (hs : s.Finite) :
    t.Finite := (hs.image _).subset hf

/--
theorem `Finite.map` / 定理 `Finite.map`

English:
theorem Finite.map
  given: {α β} {s : Set α}
  statement: forall f : α -> β, s.Finite -> (f <$> s).Finite
  proof: Finite.image

中文:
定理 有限.map
  条件: {α β} {s : 集合 α}
  结论: 对任意 f : α -> β, s.有限 -> (f <$> s).有限
  证明: Finite.image

Depends on / 依赖: Finite, Finite.image
-/
theorem Finite.map {α β} {s : Set α} : forall f : α -> β, s.Finite -> (f <$> s).Finite :=
  Finite.image

/--
theorem `Finite.of_finite_image` / 定理 `Finite.of_finite_image`

English:
theorem Finite.of_finite_image
  given: {s : Set α} {f : α -> β} (h : (f '' s).Finite) (hi : Set.InjOn f s)
  proof: have := h.to_subtype
  .of_injective _ hi.bijOn_image.bijective.injective

中文:
定理 有限.of_finite_image
  条件: {s : 集合 α} {f : α -> β} (h : (f '' s).有限) (hi : 集合.单射限制 f s)
  证明: have := h.to_subtype
  .of_injective _ hi.bijOn_image.bijective.injective

Depends on / 依赖: bijOn_image, bijective, h.to_subtype, hi.bijOn_image.bijective.injective, injective, of_injective, to_subtype
-/
theorem Finite.of_finite_image {s : Set α} {f : α -> β} (h : (f '' s).Finite) (hi : Set.InjOn f s) :
    s.Finite :=
  have := h.to_subtype
  .of_injective _ hi.bijOn_image.bijective.injective

/--
theorem `Finite.of_injOn` / 定理 `Finite.of_injOn`

English:
theorem Finite.of_injOn
  statement: {f : α -> β} {s : Set α} {t : Set β} (hm : MapsTo f s t) (hi : InjOn f s)
  proof: .of_finite_image (ht.subset (image_subset_iff.mpr hm)) hi

中文:
定理 有限.of_injOn
  结论: {f : α -> β} {s : 集合 α} {t : 集合 β} (hm : 映射到 f s t) (hi : 单射限制 f s)
  证明: .of_finite_image (ht.subset (image_subset_iff.mpr hm)) hi

Depends on / 依赖: ht.subset, image_subset_iff, image_subset_iff.mpr, of_finite_image, subset
-/
theorem Finite.of_injOn {f : α -> β} {s : Set α} {t : Set β} (hm : MapsTo f s t) (hi : InjOn f s)
    (ht : t.Finite) : s.Finite :=
  .of_finite_image (ht.subset (image_subset_iff.mpr hm)) hi

/--
theorem `BijOn.finite_iff_finite` / 定理 `BijOn.finite_iff_finite`

English:
theorem BijOn.finite_iff_finite
  given: {f : α -> β} {s : Set α} {t : Set β} (h : BijOn f s t)
  proof: ⟨fun h1 => h1.of_surjOn _ h.2.2, fun h1 => h1.of_injOn h.1 h.2.1⟩

中文:
定理 双射限制.finite_iff_finite
  条件: {f : α -> β} {s : 集合 α} {t : 集合 β} (h : 双射限制 f s t)
  证明: ⟨fun h1 => h1.of_surjOn _ h.2.2, fun h1 => h1.of_injOn h.1 h.2.1⟩

Depends on / 依赖: h1.of_injOn, h1.of_surjOn, of_injOn, of_surjOn
-/
theorem BijOn.finite_iff_finite {f : α -> β} {s : Set α} {t : Set β} (h : BijOn f s t) :
    s.Finite ↔ t.Finite :=
  ⟨fun h1 => h1.of_surjOn _ h.2.2, fun h1 => h1.of_injOn h.1 h.2.1⟩

section preimage
variable {f : α -> β} {s : Set β}

/--
theorem `finite_of_finite_preimage` / 定理 `finite_of_finite_preimage`

English:
theorem finite_of_finite_preimage
  given: (h : (f ⁻¹' s).Finite) (hs : s subseteq range f)
  statement: s.Finite
  proof: by
  rw [← image_preimage_eq_of_subset hs]
  exact Finite.image f h

中文:
定理 finite_of_finite_preimage
  条件: (h : (f ⁻¹' s).有限) (hs : s subseteq range f)
  结论: s.有限
  证明: by
  rw [← image_preimage_eq_of_subset hs]
  exact Finite.image f h

Depends on / 依赖: Finite, Finite.image, image_preimage_eq_of_subset
-/
theorem finite_of_finite_preimage (h : (f ⁻¹' s).Finite) (hs : s subseteq range f) : s.Finite := by
  rw [← image_preimage_eq_of_subset hs]
  exact Finite.image f h

/--
theorem `Finite.of_preimage` / 定理 `Finite.of_preimage`

English:
theorem Finite.of_preimage
  given: (h : (f ⁻¹' s).Finite) (hf : Surjective f)
  statement: s.Finite
  proof: hf.image_preimage s ▸ h.image _

中文:
定理 有限.of_preimage
  条件: (h : (f ⁻¹' s).有限) (hf : 满射 f)
  结论: s.有限
  证明: hf.image_preimage s ▸ h.image _

Depends on / 依赖: h.image, hf.image_preimage, image_preimage
-/
theorem Finite.of_preimage (h : (f ⁻¹' s).Finite) (hf : Surjective f) : s.Finite :=
  hf.image_preimage s ▸ h.image _

/--
theorem `Finite.preimage` / 定理 `Finite.preimage`

English:
theorem Finite.preimage
  given: (I : Set.InjOn f (f ⁻¹' s)) (h : s.Finite)
  statement: (f ⁻¹' s).Finite
  proof: (h.subset (image_preimage_subset f s)).of_finite_image I

中文:
定理 有限.原像
  条件: (I : 集合.单射限制 f (f ⁻¹' s)) (h : s.有限)
  结论: (f ⁻¹' s).有限
  证明: (h.subset (image_preimage_subset f s)).of_finite_image I

Depends on / 依赖: h.subset, image_preimage_subset, of_finite_image, subset
-/
theorem Finite.preimage (I : Set.InjOn f (f ⁻¹' s)) (h : s.Finite) : (f ⁻¹' s).Finite :=
  (h.subset (image_preimage_subset f s)).of_finite_image I

/--
lemma `Infinite.preimage` / 引理 `Infinite.preimage`

English:
lemma Infinite.preimage
  given: (hs : s.Infinite) (hf : s subseteq range f)
  statement: (f ⁻¹' s).Infinite
  proof: fun h => hs finite_of_finite_preimage h hf

中文:
引理 无限.原像
  条件: (hs : s.无限) (hf : s subseteq range f)
  结论: (f ⁻¹' s).无限
  证明: fun h => hs finite_of_finite_preimage h hf
-/
protected lemma Infinite.preimage (hs : s.Infinite) (hf : s subseteq range f) : (f ⁻¹' s).Infinite :=
fun h => hs finite_of_finite_preimage h hf

/--
lemma `Infinite.preimage'` / 引理 `Infinite.preimage'`

English:
lemma Infinite.preimage'
  given: (hs : (s inter range f).Infinite)
  statement: (f ⁻¹' s).Infinite
  proof: (hs.preimage inter_subset_right).mono preimage_mono inter_subset_left

中文:
引理 无限.原像'
  条件: (hs : (s inter range f).无限)
  结论: (f ⁻¹' s).无限
  证明: (hs.preimage inter_subset_right).mono preimage_mono inter_subset_left

Depends on / 依赖: hs.preimage, inter_subset_left, inter_subset_right, le_top, mod_cast, preimage, preimage_mono
-/
lemma Infinite.preimage' (hs : (s inter range f).Infinite) : (f ⁻¹' s).Infinite :=
(hs.preimage inter_subset_right).mono preimage_mono inter_subset_left

/--
theorem `Finite.preimage_embedding` / 定理 `Finite.preimage_embedding`

English:
theorem Finite.preimage_embedding
  given: {s : Set β} (f : α ↪ β) (h : s.Finite)
  statement: (f ⁻¹' s).Finite
  proof: h.preimage fun _ _ _ _ h' => f.injective h'

中文:
定理 有限.preimage_embedding
  条件: {s : 集合 β} (f : α ↪ β) (h : s.有限)
  结论: (f ⁻¹' s).有限
  证明: h.preimage fun _ _ _ _ h' => f.injective h'

Depends on / 依赖: f.injective, h.preimage, injective, le_top, mod_cast, preimage
-/
theorem Finite.preimage_embedding {s : Set β} (f : α ↪ β) (h : s.Finite) : (f ⁻¹' s).Finite :=
  h.preimage fun _ _ _ _ h' => f.injective h'

end preimage

/--
theorem `finite_lt_nat` / 定理 `finite_lt_nat`

English:
theorem finite_lt_nat
  given: (n : Nat)
  statement: Set.Finite { i | i < n }
  proof: toFinite _

中文:
定理 finite_lt_nat
  条件: (n : 自然数)
  结论: 集合.有限 { i | i < n }
  证明: toFinite _

Depends on / 依赖: LEInfty, toFinite
-/
theorem finite_lt_nat (n : Nat) : Set.Finite { i | i < n } :=
  toFinite _

/--
theorem `finite_le_nat` / 定理 `finite_le_nat`

English:
theorem finite_le_nat
  given: (n : Nat)
  statement: Set.Finite { i | i <= n }
  proof: toFinite _

中文:
定理 finite_le_nat
  条件: (n : 自然数)
  结论: 集合.有限 { i | i <= n }
  证明: toFinite _

Depends on / 依赖: toFinite
-/
theorem finite_le_nat (n : Nat) : Set.Finite { i | i <= n } :=
  toFinite _

section MapsTo

variable {s : Set α} {f : α -> α}

/--
theorem `Finite.surjOn_iff_bijOn_of_mapsTo` / 定理 `Finite.surjOn_iff_bijOn_of_mapsTo`

English:
theorem Finite.surjOn_iff_bijOn_of_mapsTo
  given: (hs : s.Finite) (hm : MapsTo f s s)
  proof: by
  refine ⟨fun h => ⟨hm, ?_, h⟩, BijOn.surjOn⟩
  have : Finite s := finite_coe_iff.mpr hs
  exact hm.restrict_inj.mp (Finite.injective_iff_surjective.mpr <| hm.restrict_surjective_iff.mpr h)

中文:
定理 有限.surjOn_iff_bijOn_of_mapsTo
  条件: (hs : s.有限) (hm : 映射到 f s s)
  证明: by
  refine ⟨fun h => ⟨hm, ?_, h⟩, BijOn.surjOn⟩
  have : Finite s := finite_coe_iff.mpr hs
  exact hm.restrict_inj.mp (Finite.injective_iff_surjective.mpr <| hm.restrict_surjective_iff.mpr h)

Depends on / 依赖: BijOn.surjOn, Finite, Finite.injective_iff_surjective.mpr, finite_coe_iff, finite_coe_iff.mpr, hm.restrict_inj.mp, hm.restrict_surjective_iff.mpr, injective_iff_surjective, restrict_inj, restrict_surjective_iff, surjOn
-/
theorem Finite.surjOn_iff_bijOn_of_mapsTo (hs : s.Finite) (hm : MapsTo f s s) :
    SurjOn f s s ↔ BijOn f s s := by
  refine ⟨fun h => ⟨hm, ?_, h⟩, BijOn.surjOn⟩
  have : Finite s := finite_coe_iff.mpr hs
  exact hm.restrict_inj.mp (Finite.injective_iff_surjective.mpr <| hm.restrict_surjective_iff.mpr h)

/--
theorem `Finite.injOn_iff_bijOn_of_mapsTo` / 定理 `Finite.injOn_iff_bijOn_of_mapsTo`

English:
theorem Finite.injOn_iff_bijOn_of_mapsTo
  given: (hs : s.Finite) (hm : MapsTo f s s)
  proof: by
  refine ⟨fun h => ⟨hm, h, ?_⟩, BijOn.injOn⟩
  have : Finite s := finite_coe_iff.mpr hs
  exact hm.restrict_surjective_iff.mp (Finite.injective_iff_surjective.mp <| hm.restrict_inj.mpr h)

中文:
定理 有限.injOn_iff_bijOn_of_mapsTo
  条件: (hs : s.有限) (hm : 映射到 f s s)
  证明: by
  refine ⟨fun h => ⟨hm, h, ?_⟩, BijOn.injOn⟩
  have : Finite s := finite_coe_iff.mpr hs
  exact hm.restrict_surjective_iff.mp (Finite.injective_iff_surjective.mp <| hm.restrict_inj.mpr h)

Depends on / 依赖: BijOn.injOn, Finite, Finite.injective_iff_surjective.mp, IsManifold, IsManifold.of_le, finite_coe_iff, finite_coe_iff.mpr, h.out, hm.restrict_inj.mpr, hm.restrict_surjective_iff.mp, injective_iff_surjective, of_le, restrict_inj, restrict_surjective_iff
-/
theorem Finite.injOn_iff_bijOn_of_mapsTo (hs : s.Finite) (hm : MapsTo f s s) :
    InjOn f s ↔ BijOn f s s := by
  refine ⟨fun h => ⟨hm, h, ?_⟩, BijOn.injOn⟩
  have : Finite s := finite_coe_iff.mpr hs
  exact hm.restrict_surjective_iff.mp (Finite.injective_iff_surjective.mp <| hm.restrict_inj.mpr h)

end MapsTo

/--
theorem `finite_mem_finset` / 定理 `finite_mem_finset`

English:
theorem finite_mem_finset
  given: (s : Finset α)
  statement: { a | a in s }.Finite
  proof: toFinite _

中文:
定理 finite_mem_finset
  条件: (s : 有限集 α)
  结论: { a | a in s }.有限
  证明: toFinite _

Depends on / 依赖: IsManifold, IsManifold.of_le, le_top, of_le, toFinite
-/
theorem finite_mem_finset (s : Finset α) : { a | a in s }.Finite :=
  toFinite _

/--
theorem `Subsingleton.finite` / 定理 `Subsingleton.finite`

English:
theorem Subsingleton.finite
  given: {s : Set α} (h : s.Subsingleton)
  statement: s.Finite
  proof: h.induction_on finite_empty finite_singleton

中文:
定理 子单例.finite
  条件: {s : 集合 α} (h : s.子单例)
  结论: s.有限
  证明: h.induction_on finite_empty finite_singleton

Depends on / 依赖: finite_empty, finite_singleton, h.induction_on, induction_on
-/
theorem Subsingleton.finite {s : Set α} (h : s.Subsingleton) : s.Finite :=
  h.induction_on finite_empty finite_singleton

/--
theorem `Infinite.nontrivial` / 定理 `Infinite.nontrivial`

English:
theorem Infinite.nontrivial
  given: {s : Set α} (hs : s.Infinite)
  statement: s.Nontrivial
  proof: not_subsingleton_iff.1 mt Subsingleton.finite hs

中文:
定理 无限.nontrivial
  条件: {s : 集合 α} (hs : s.无限)
  结论: s.非平凡
  证明: not_subsingleton_iff.1 mt Subsingleton.finite hs

Depends on / 依赖: Subsingleton, Subsingleton.finite, finite, not_subsingleton_iff
-/
theorem Infinite.nontrivial {s : Set α} (hs : s.Infinite) : s.Nontrivial :=
not_subsingleton_iff.1 mt Subsingleton.finite hs

/--
theorem `finite_preimage_inl_and_inr` / 定理 `finite_preimage_inl_and_inr`

English:
theorem finite_preimage_inl_and_inr
  given: {s : Set (α oplus β)}
  proof: ⟨fun h => image_preimage_inl_union_image_preimage_inr s ▸ (h.1.image _).union (h.2.image _),
    fun h => ⟨h.preimage Sum.inl_injective.injOn, h.preimage Sum.inr_injective.injOn⟩⟩

中文:
定理 finite_preimage_inl_and_inr
  条件: {s : 集合 (α oplus β)}
  证明: ⟨fun h => image_preimage_inl_union_image_preimage_inr s ▸ (h.1.image _).union (h.2.image _),
    fun h => ⟨h.preimage Sum.inl_injective.injOn, h.preimage Sum.inr_injective.injOn⟩⟩

Depends on / 依赖: Sum.inl_injective.injOn, Sum.inr_injective.injOn, h.preimage, image_preimage_inl_union_image_preimage_inr, inl_injective, inr_injective, preimage
-/
theorem finite_preimage_inl_and_inr {s : Set (α oplus β)} :
    (Sum.inl ⁻¹' s).Finite ∧ (Sum.inr ⁻¹' s).Finite ↔ s.Finite :=
  ⟨fun h => image_preimage_inl_union_image_preimage_inr s ▸ (h.1.image _).union (h.2.image _),
    fun h => ⟨h.preimage Sum.inl_injective.injOn, h.preimage Sum.inr_injective.injOn⟩⟩

/--
theorem `exists_finite_iff_finset` / 定理 `exists_finite_iff_finset`

English:
theorem exists_finite_iff_finset
  given: {p : Set α -> Prop}
  proof: ⟨fun ⟨_, hs, hps⟩ => ⟨hs.toFinset, hs.coe_toFinset.symm ▸ hps⟩, fun ⟨s, hs⟩ =>
    ⟨s, s.finite_toSet, hs⟩⟩

中文:
定理 存在_finite_iff_finset
  条件: {p : 集合 α -> 命题}
  证明: ⟨fun ⟨_, hs, hps⟩ => ⟨hs.toFinset, hs.coe_toFinset.symm ▸ hps⟩, fun ⟨s, hs⟩ =>
    ⟨s, s.finite_toSet, hs⟩⟩

Depends on / 依赖: coe_toFinset, finite_toSet, hs.coe_toFinset.symm, hs.toFinset, s.finite_toSet, toFinset
-/
theorem exists_finite_iff_finset {p : Set α -> Prop} :
    (exists s : Set α, s.Finite ∧ p s) ↔ exists s : Finset α, p ↑s :=
  ⟨fun ⟨_, hs, hps⟩ => ⟨hs.toFinset, hs.coe_toFinset.symm ▸ hps⟩, fun ⟨s, hs⟩ =>
    ⟨s, s.finite_toSet, hs⟩⟩

/--
theorem `exists_subset_image_finite_and` / 定理 `exists_subset_image_finite_and`

English:
theorem exists_subset_image_finite_and
  given: {f : α -> β} {s : Set α} {p : Set β -> Prop}
  proof: by
  classical
  simp_rw [@and_comm ((_ : Set _) subseteq _), and_assoc, exists_finite_iff_finset, @and_comm (p _),
    Finset.subset_set_image_iff]
  aesop

中文:
定理 存在_subset_image_finite_and
  条件: {f : α -> β} {s : 集合 α} {p : 集合 β -> 命题}
  证明: by
  classical
  simp_rw [@and_comm ((_ : Set _) subseteq _), and_assoc, exists_finite_iff_finset, @and_comm (p _),
    Finset.subset_set_image_iff]
  aesop

Depends on / 依赖: Finset, Finset.subset_set_image_iff, and_assoc, and_comm, classical, exists_finite_iff_finset, simp_rw, subset_set_image_iff, subseteq
-/
theorem exists_subset_image_finite_and {f : α -> β} {s : Set α} {p : Set β -> Prop} :
    (exists t subseteq f '' s, t.Finite ∧ p t) ↔ exists t subseteq s, t.Finite ∧ p (f '' t) := by
  classical
  simp_rw [@and_comm ((_ : Set _) subseteq _), and_assoc, exists_finite_iff_finset, @and_comm (p _),
    Finset.subset_set_image_iff]
  aesop

/--
theorem `finite_range_ite` / 定理 `finite_range_ite`

English:
theorem finite_range_ite
  statement: {p : α -> Prop} [DecidablePred p] {f g : α -> β} (hf : (range f).Finite)
  proof: (hf.union hg).subset range_ite_subset

中文:
定理 finite_range_ite
  结论: {p : α -> 命题} [DecidablePred p] {f g : α -> β} (hf : (range f).有限)
  证明: (hf.union hg).subset range_ite_subset

Depends on / 依赖: hf.union, range_ite_subset, subset
-/
theorem finite_range_ite {p : α -> Prop} [DecidablePred p] {f g : α -> β} (hf : (range f).Finite)
    (hg : (range g).Finite) : (range fun x => if p x then f x else g x).Finite :=
  (hf.union hg).subset range_ite_subset

/--
theorem `finite_range_const` / 定理 `finite_range_const`

English:
theorem finite_range_const
  given: {c : β}
  statement: (range fun _ : α => c).Finite
  proof: (finite_singleton c).subset range_const_subset

中文:
定理 finite_range_const
  条件: {c : β}
  结论: (range fun _ : α => c).有限
  证明: (finite_singleton c).subset range_const_subset

Depends on / 依赖: finite_singleton, range_const_subset, subset
-/
theorem finite_range_const {c : β} : (range fun _ : α => c).Finite :=
  (finite_singleton c).subset range_const_subset

end SetFiniteConstructors


/--
Instance `Finite.inhabited` / 实例 `Finite.inhabited`

English:
instance Finite.inhabited
  signature: : Inhabited { s : Set α // s.Finite }
  body: ⟨⟨∅, finite_empty⟩⟩

@[simp]

中文:
实例 有限.inhabited
  签名: : 可居 { s : 集合 α // s.有限 }
  定义体: ⟨⟨∅, finite_empty⟩⟩

@[simp]

Depends on / 依赖: finite_empty
-/
instance Finite.inhabited : Inhabited { s : Set α // s.Finite } :=
  ⟨⟨∅, finite_empty⟩⟩

@[simp]
/--
theorem `finite_union` / 定理 `finite_union`

English:
theorem finite_union
  given: {s t : Set α}
  statement: (s union t).Finite ↔ s.Finite ∧ t.Finite
  proof: ⟨fun h => ⟨h.subset subset_union_left, h.subset subset_union_right⟩, fun ⟨hs, ht⟩ =>
    hs.union ht⟩

中文:
定理 finite_union
  条件: {s t : 集合 α}
  结论: (s union t).有限 ↔ s.有限 ∧ t.有限
  证明: ⟨fun h => ⟨h.subset subset_union_left, h.subset subset_union_right⟩, fun ⟨hs, ht⟩ =>
    hs.union ht⟩

Depends on / 依赖: h.subset, hs.union, subset, subset_union_left, subset_union_right
-/
theorem finite_union {s t : Set α} : (s union t).Finite ↔ s.Finite ∧ t.Finite :=
  ⟨fun h => ⟨h.subset subset_union_left, h.subset subset_union_right⟩, fun ⟨hs, ht⟩ =>
    hs.union ht⟩

/--
theorem `finite_image_iff` / 定理 `finite_image_iff`

English:
theorem finite_image_iff
  given: {s : Set α} {f : α -> β} (hi : InjOn f s)
  statement: (f '' s).Finite ↔ s.Finite
  proof: ⟨fun h => h.of_finite_image hi, Finite.image _⟩

中文:
定理 finite_image_iff
  条件: {s : 集合 α} {f : α -> β} (hi : 单射限制 f s)
  结论: (f '' s).有限 ↔ s.有限
  证明: ⟨fun h => h.of_finite_image hi, Finite.image _⟩

Depends on / 依赖: Finite, Finite.image, h.of_finite_image, of_finite_image
-/
theorem finite_image_iff {s : Set α} {f : α -> β} (hi : InjOn f s) : (f '' s).Finite ↔ s.Finite :=
  ⟨fun h => h.of_finite_image hi, Finite.image _⟩

/--
lemma `finite_range_iff` / 引理 `finite_range_iff`

English:
lemma finite_range_iff
  given: {f : α -> β} (hf : f.Injective)
  statement: (range f).Finite ↔ Finite α
  proof: by
  simpa [finite_univ_iff] using finite_image_iff (s := univ) hf.injOn

中文:
引理 finite_range_iff
  条件: {f : α -> β} (hf : f.单射)
  结论: (range f).有限 ↔ 有限 α
  证明: by
  simpa [finite_univ_iff] using finite_image_iff (s := univ) hf.injOn

Depends on / 依赖: finite_image_iff, finite_univ_iff, hf.injOn
-/
lemma finite_range_iff {f : α -> β} (hf : f.Injective) : (range f).Finite ↔ Finite α := by
  simpa [finite_univ_iff] using finite_image_iff (s := univ) hf.injOn

/--
theorem `univ_finite_iff_nonempty_fintype` / 定理 `univ_finite_iff_nonempty_fintype`

English:
theorem univ_finite_iff_nonempty_fintype
  statement: (univ : Set α).Finite ↔ Nonempty (Fintype α)
  proof: ⟨fun h => ⟨fintypeOfFiniteUniv h⟩, fun ⟨_i⟩ => finite_univ⟩

中文:
定理 univ_finite_iff_nonempty_fintype
  结论: (univ : 集合 α).有限 ↔ 非空 (有限类型 α)
  证明: ⟨fun h => ⟨fintypeOfFiniteUniv h⟩, fun ⟨_i⟩ => finite_univ⟩

Depends on / 依赖: finite_univ, fintypeOfFiniteUniv
-/
theorem univ_finite_iff_nonempty_fintype : (univ : Set α).Finite ↔ Nonempty (Fintype α) :=
  ⟨fun h => ⟨fintypeOfFiniteUniv h⟩, fun ⟨_i⟩ => finite_univ⟩

-- `simp`-normal form is `Set.toFinset_singleton`.
/--
theorem `Finite.toFinset_singleton` / 定理 `Finite.toFinset_singleton`

English:
theorem Finite.toFinset_singleton
  given: {a : α} (ha : ({a} : Set α).Finite := finite_singleton _)
  proof: Set.toFinite_toFinset _

@[simp]

中文:
定理 有限.toFinset_singleton
  条件: {a : α} (ha : ({a} : 集合 α).有限 := finite_singleton _)
  证明: Set.toFinite_toFinset _

@[simp]

Depends on / 依赖: finite_singleton
-/
theorem Finite.toFinset_singleton {a : α} (ha : ({a} : Set α).Finite := finite_singleton _) :
    ha.toFinset = {a} :=
  Set.toFinite_toFinset _

@[simp]
/--
theorem `Finite.toFinset_insert` / 定理 `Finite.toFinset_insert`

English:
theorem Finite.toFinset_insert
  given: [DecidableEq α] {s : Set α} {a : α} (hs : (insert a s).Finite)
  proof: Finset.ext by simp

中文:
定理 有限.toFinset_insert
  条件: [DecidableEq α] {s : 集合 α} {a : α} (hs : (insert a s).有限)
  证明: Finset.ext by simp

Depends on / 依赖: Finset, Finset.ext
-/
theorem Finite.toFinset_insert [DecidableEq α] {s : Set α} {a : α} (hs : (insert a s).Finite) :
    hs.toFinset = insert a (hs.subset <| subset_insert _ _).toFinset :=
Finset.ext by simp

/--
theorem `Finite.toFinset_insert'` / 定理 `Finite.toFinset_insert'`

English:
theorem Finite.toFinset_insert'
  given: [DecidableEq α] {a : α} {s : Set α} (hs : s.Finite)
  proof: Finite.toFinset_insert _

中文:
定理 有限.toFinset_insert'
  条件: [DecidableEq α] {a : α} {s : 集合 α} (hs : s.有限)
  证明: Finite.toFinset_insert _

Depends on / 依赖: Finite, Finite.toFinset_insert, toFinset_insert
-/
theorem Finite.toFinset_insert' [DecidableEq α] {a : α} {s : Set α} (hs : s.Finite) :
    (hs.insert a).toFinset = insert a hs.toFinset :=
  Finite.toFinset_insert _

/--
theorem `finite_option` / 定理 `finite_option`

English:
theorem finite_option
  given: {s : Set (Option α)}
  statement: s.Finite ↔ { x : α | some x in s }.Finite
  proof: ⟨fun h => h.preimage_embedding Embedding.some, fun h =>
    ((h.image some).insert none).subset fun x =>
x.casesOn (fun _ => Or.inl rfl) fun _ hx => Or.inr mem_image_of_mem _ hx⟩

中文:
定理 finite_option
  条件: {s : 集合 (选项类型 α)}
  结论: s.有限 ↔ { x : α | some x in s }.有限
  证明: ⟨fun h => h.preimage_embedding Embedding.some, fun h =>
    ((h.image some).insert none).subset fun x =>
x.casesOn (fun _ => Or.inl rfl) fun _ hx => Or.inr mem_image_of_mem _ hx⟩

Depends on / 依赖: Embedding, Embedding.some, Or.inl, Or.inr, casesOn, h.image, h.preimage_embedding, insert, mem_image_of_mem, preimage_embedding, subset, x.casesOn
-/
theorem finite_option {s : Set (Option α)} : s.Finite ↔ { x : α | some x in s }.Finite :=
  ⟨fun h => h.preimage_embedding Embedding.some, fun h =>
    ((h.image some).insert none).subset fun x =>
x.casesOn (fun _ => Or.inl rfl) fun _ hx => Or.inr mem_image_of_mem _ hx⟩

/-- Induction principle for finite sets: To prove a property `motive` of a finite set `s`, it's
enough to prove for the empty set and to prove that `motive t → motive ({a} ∪ t)` for all `t`.

See also `Set.Finite.induction_on_subset` for the version requiring to check
`motive t → motive ({a} ∪ t)` only for `t ⊆ s`. -/
@[elab_as_elim]
/--
theorem `Finite.induction_on` / 定理 `Finite.induction_on`

English:
theorem Finite.induction_on
  statement: {motive : forall s : Set α, s.Finite -> Prop} (s : Set α) (hs : s.Finite)
  proof: by
  lift s to Finset α using hs
  induction s using Finset.cons_induction_on with
  | empty => simpa
  | cons a s ha ih => simpa using @insert a s ha (Set.toFinite _) (ih _)

中文:
定理 有限.induction_on
  结论: {motive : 对任意 s : 集合 α, s.有限 -> 命题} (s : 集合 α) (hs : s.有限)
  证明: by
  lift s to Finset α using hs
  induction s using Finset.cons_induction_on with
  | empty => simpa
  | cons a s ha ih => simpa using @insert a s ha (Set.toFinite _) (ih _)

Depends on / 依赖: Finset, Finset.cons_induction_on, Set.toFinite, cons_induction_on, insert, toFinite
-/
theorem Finite.induction_on {motive : forall s : Set α, s.Finite -> Prop} (s : Set α) (hs : s.Finite)
    (empty : motive ∅ finite_empty)
    (insert : forall {a s}, a ∉ s ->
      forall hs : Set.Finite s, motive s hs -> motive (insert a s) (hs.insert a)) :
    motive s hs := by
  lift s to Finset α using hs
  induction s using Finset.cons_induction_on with
  | empty => simpa
  | cons a s ha ih => simpa using @insert a s ha (Set.toFinite _) (ih _)

/-- Induction principle for finite sets: To prove a property `C` of a finite set `s`, it's enough
to prove for the empty set and to prove that `C t → C ({a} ∪ t)` for all `t ⊆ s`.

This is analogous to `Finset.induction_on'`. See also `Set.Finite.induction_on` for the version
requiring `motive t → motive ({a} ∪ t)` for all `t`. -/
@[elab_as_elim]
/--
theorem `Finite.induction_on_subset` / 定理 `Finite.induction_on_subset`

English:
theorem Finite.induction_on_subset
  statement: {motive : forall s : Set α, s.Finite -> Prop} (s : Set α)
  proof: by
  refine Set.Finite.induction_on (motive := fun t _ => forall hts : t subseteq s, motive t (hs.subset hts)) s hs
    (fun _ => empty) ?_ .rfl
  intro a s has _ hCs haS
  rw [insert_subset_iff] at haS
  exact insert haS.1 haS.2 has (hCs haS.2)

中文:
定理 有限.induction_on_subset
  结论: {motive : 对任意 s : 集合 α, s.有限 -> 命题} (s : 集合 α)
  证明: by
  refine Set.Finite.induction_on (motive := fun t _ => forall hts : t subseteq s, motive t (hs.subset hts)) s hs
    (fun _ => empty) ?_ .rfl
  intro a s has _ hCs haS
  rw [insert_subset_iff] at haS
  exact insert haS.1 haS.2 has (hCs haS.2)

Depends on / 依赖: Finite, Set.Finite.induction_on, hs.subset, induction_on, insert, insert_subset_iff, motive, subset, subseteq
-/
theorem Finite.induction_on_subset {motive : forall s : Set α, s.Finite -> Prop} (s : Set α)
    (hs : s.Finite) (empty : motive ∅ finite_empty)
    (insert : forall {a t}, a in s -> forall hts : t subseteq s, a ∉ t -> motive t (hs.subset hts) ->
      motive (insert a t) ((hs.subset hts).insert a)) : motive s hs := by
  refine Set.Finite.induction_on (motive := fun t _ => forall hts : t subseteq s, motive t (hs.subset hts)) s hs
    (fun _ => empty) ?_ .rfl
  intro a s has _ hCs haS
  rw [insert_subset_iff] at haS
  exact insert haS.1 haS.2 has (hCs haS.2)

section

attribute [local instance] Nat.fintypeIio

/--
theorem `seq_of_forall_finite_exists` / 定理 `seq_of_forall_finite_exists`

English:
theorem seq_of_forall_finite_exists
  statement: {γ : Type*} {P : γ -> Set γ -> Prop}
  proof: by
  have : Nonempty γ := (h ∅ finite_empty).nonempty
  choose! c hc using h
  set f : (n : Nat) -> (g : (m : Nat) -> m < n -> γ) -> γ := fun n g => c (range fun k : Iio n => g k.1 k.2)
  set u : Nat -> γ := fun n => Nat.strongRecOn n f
  refine ⟨u, fun n => ?_⟩
  convert! hc (u '' Iio n) ((finite_l

中文:
定理 seq_of_对任意_finite_存在
  结论: {γ : 类型} {P : γ -> 集合 γ -> 命题}
  证明: by
  have : Nonempty γ := (h ∅ finite_empty).nonempty
  choose! c hc using h
  set f : (n : Nat) -> (g : (m : Nat) -> m < n -> γ) -> γ := fun n g => c (range fun k : Iio n => g k.1 k.2)
  set u : Nat -> γ := fun n => Nat.strongRecOn n f
  refine ⟨u, fun n => ?_⟩
  convert! hc (u '' Iio n) ((finite_l

Depends on / 依赖: Nat.strongRecOn, Nat.strongRecOn_eq, Nonempty, convert, finite_empty, finite_lt_nat, image_eq_range, nonempty, strongRecOn, strongRecOn_eq
-/
theorem seq_of_forall_finite_exists {γ : Type*} {P : γ -> Set γ -> Prop}
    (h : forall t : Set γ, t.Finite -> exists c, P c t) : exists u : Nat -> γ, forall n, P (u n) (u '' Iio n) := by
  have : Nonempty γ := (h ∅ finite_empty).nonempty
  choose! c hc using h
  set f : (n : Nat) -> (g : (m : Nat) -> m < n -> γ) -> γ := fun n g => c (range fun k : Iio n => g k.1 k.2)
  set u : Nat -> γ := fun n => Nat.strongRecOn n f
  refine ⟨u, fun n => ?_⟩
  convert! hc (u '' Iio n) ((finite_lt_nat _).image _)
  rw [image_eq_range]
  exact Nat.strongRecOn_eq f n

end


/--
theorem `card_empty` / 定理 `card_empty`

English:
theorem card_empty
  statement: Fintype.card (∅ : Set α) = 0
  proof: rfl

中文:
定理 card_empty
  结论: 有限类型.card (∅ : 集合 α) = 0
  证明: rfl
-/
theorem card_empty : Fintype.card (∅ : Set α) = 0 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `card_fintypeInsertOfNotMem` / 定理 `card_fintypeInsertOfNotMem`

English:
theorem card_fintypeInsertOfNotMem
  given: {a : α} (s : Set α) [Fintype s] (h : a ∉ s)
  proof: by
  simp [Fintype.card_ofFinset]

中文:
定理 card_fintypeInsertOfNotMem
  条件: {a : α} (s : 集合 α) [有限类型 s] (h : a ∉ s)
  证明: by
  simp [Fintype.card_ofFinset]

Depends on / 依赖: Fintype, Fintype.card_ofFinset, card_ofFinset
-/
theorem card_fintypeInsertOfNotMem {a : α} (s : Set α) [Fintype s] (h : a ∉ s) :
    @Fintype.card _ (fintypeInsertOfNotMem s h) = Fintype.card s + 1 := by
  simp [Fintype.card_ofFinset]

/--
theorem `card_insert` / 定理 `card_insert`

English:
theorem card_insert
  statement: {a : α} (s : Set α) [Fintype s] (h : a ∉ s)
  proof: by
  rw [← card_fintypeInsertOfNotMem s h]; congr!

中文:
定理 card_insert
  结论: {a : α} (s : 集合 α) [有限类型 s] (h : a ∉ s)
  证明: by
  rw [← card_fintypeInsertOfNotMem s h]; congr!

Depends on / 依赖: card_fintypeInsertOfNotMem
-/
theorem card_insert {a : α} (s : Set α) [Fintype s] (h : a ∉ s)
    {d : Fintype (insert a s : Set α)} : @Fintype.card _ d = Fintype.card s + 1 := by
  rw [← card_fintypeInsertOfNotMem s h]; congr!

/--
theorem `card_image_of_inj_on` / 定理 `card_image_of_inj_on`

English:
theorem card_image_of_inj_on
  statement: {s : Set α} [Fintype s] {f : α -> β} [Fintype (f '' s)]
  proof: haveI := Classical.propDecidable
  calc
    Fintype.card (f '' s) = (s.toFinset.image f).card := Fintype.card_of_finset' _ (by simp)
    _ = s.toFinset.card :=
      Finset.card_image_of_injOn fun x hx y hy hxy =>
        H x (mem_toFinset.1 hx) y (mem_toFinset.1 hy) hxy
    _ = Fintype.card s := (F

中文:
定理 card_image_of_inj_on
  结论: {s : 集合 α} [有限类型 s] {f : α -> β} [有限类型 (f '' s)]
  证明: haveI := Classical.propDecidable
  calc
    Fintype.card (f '' s) = (s.toFinset.image f).card := Fintype.card_of_finset' _ (by simp)
    _ = s.toFinset.card :=
      Finset.card_image_of_injOn fun x hx y hy hxy =>
        H x (mem_toFinset.1 hx) y (mem_toFinset.1 hy) hxy
    _ = Fintype.card s := (F

Depends on / 依赖: Classical, Classical.propDecidable, Finset, Finset.card_image_of_injOn, Fintype, Fintype.card, Fintype.card_of_finset, card_image_of_injOn, card_of_finset, mem_toFinset, propDecidable, s.toFinset.card, s.toFinset.image, toFinset
-/
theorem card_image_of_inj_on {s : Set α} [Fintype s] {f : α -> β} [Fintype (f '' s)]
    (H : forall x in s, forall y in s, f x = f y -> x = y) : Fintype.card (f '' s) = Fintype.card s :=
  haveI := Classical.propDecidable
  calc
    Fintype.card (f '' s) = (s.toFinset.image f).card := Fintype.card_of_finset' _ (by simp)
    _ = s.toFinset.card :=
      Finset.card_image_of_injOn fun x hx y hy hxy =>
        H x (mem_toFinset.1 hx) y (mem_toFinset.1 hy) hxy
    _ = Fintype.card s := (Fintype.card_of_finset' _ fun _ => mem_toFinset).symm

/--
theorem `card_image_of_injective` / 定理 `card_image_of_injective`

English:
theorem card_image_of_injective
  statement: (s : Set α) [Fintype s] {f : α -> β} [Fintype (f '' s)]
  proof: card_image_of_inj_on fun _ _ _ _ h => H h

@[simp]

中文:
定理 card_image_of_injective
  结论: (s : 集合 α) [有限类型 s] {f : α -> β} [有限类型 (f '' s)]
  证明: card_image_of_inj_on fun _ _ _ _ h => H h

@[simp]

Depends on / 依赖: card_image_of_inj_on
-/
theorem card_image_of_injective (s : Set α) [Fintype s] {f : α -> β} [Fintype (f '' s)]
    (H : Function.Injective f) : Fintype.card (f '' s) = Fintype.card s :=
  card_image_of_inj_on fun _ _ _ _ h => H h

@[simp]
/--
theorem `card_singleton` / 定理 `card_singleton`

English:
theorem card_singleton
  given: (a : α)
  statement: Fintype.card ({a} : Set α) = 1
  proof: rfl

中文:
定理 card_singleton
  条件: (a : α)
  结论: 有限类型.card ({a} : 集合 α) = 1
  证明: rfl
-/
theorem card_singleton (a : α) : Fintype.card ({a} : Set α) = 1 :=
  rfl

/--
theorem `card_lt_card` / 定理 `card_lt_card`

English:
theorem card_lt_card
  given: {s t : Set α} [Fintype s] [Fintype t] (h : s ⊂ t)
  proof: Fintype.card_lt_of_injective_not_surjective (Set.inclusion h.1) (Set.inclusion_injective h.1)
    fun hst => (ssubset_iff_subset_ne.1 h).2 (eq_of_inclusion_surjective hst)

中文:
定理 card_lt_card
  条件: {s t : 集合 α} [有限类型 s] [有限类型 t] (h : s ⊂ t)
  证明: Fintype.card_lt_of_injective_not_surjective (Set.inclusion h.1) (Set.inclusion_injective h.1)
    fun hst => (ssubset_iff_subset_ne.1 h).2 (eq_of_inclusion_surjective hst)

Depends on / 依赖: Fintype, Fintype.card_lt_of_injective_not_surjective, Set.inclusion, Set.inclusion_injective, card_lt_of_injective_not_surjective, eq_of_inclusion_surjective, inclusion, inclusion_injective, ssubset_iff_subset_ne
-/
theorem card_lt_card {s t : Set α} [Fintype s] [Fintype t] (h : s ⊂ t) :
    Fintype.card s < Fintype.card t :=
  Fintype.card_lt_of_injective_not_surjective (Set.inclusion h.1) (Set.inclusion_injective h.1)
    fun hst => (ssubset_iff_subset_ne.1 h).2 (eq_of_inclusion_surjective hst)

/--
theorem `card_le_card` / 定理 `card_le_card`

English:
theorem card_le_card
  given: {s t : Set α} [Fintype s] [Fintype t] (hsub : s subseteq t)
  proof: Fintype.card_le_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)

中文:
定理 card_le_card
  条件: {s t : 集合 α} [有限类型 s] [有限类型 t] (hsub : s subseteq t)
  证明: Fintype.card_le_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)

Depends on / 依赖: Fintype, Fintype.card_le_of_injective, Set.inclusion, Set.inclusion_injective, card_le_of_injective, inclusion, inclusion_injective
-/
theorem card_le_card {s t : Set α} [Fintype s] [Fintype t] (hsub : s subseteq t) :
    Fintype.card s <= Fintype.card t :=
  Fintype.card_le_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)

/--
theorem `eq_of_subset_of_card_le` / 定理 `eq_of_subset_of_card_le`

English:
theorem eq_of_subset_of_card_le
  statement: {s t : Set α} [Fintype s] [Fintype t] (hsub : s subseteq t)
  proof: (eq_or_ssubset_of_subset hsub).elim id fun h => absurd hcard not_le_of_gt card_lt_card h

中文:
定理 eq_of_subset_of_card_le
  结论: {s t : 集合 α} [有限类型 s] [有限类型 t] (hsub : s subseteq t)
  证明: (eq_or_ssubset_of_subset hsub).elim id fun h => absurd hcard not_le_of_gt card_lt_card h

Depends on / 依赖: absurd, card_lt_card, eq_or_ssubset_of_subset, not_le_of_gt
-/
theorem eq_of_subset_of_card_le {s t : Set α} [Fintype s] [Fintype t] (hsub : s subseteq t)
    (hcard : Fintype.card t <= Fintype.card s) : s = t :=
(eq_or_ssubset_of_subset hsub).elim id fun h => absurd hcard not_le_of_gt card_lt_card h

/--
theorem `card_range_of_injective` / 定理 `card_range_of_injective`

English:
theorem card_range_of_injective
  given: [Fintype α] {f : α -> β} (hf : Injective f) [Fintype (range f)]
  proof: Eq.symm Fintype.card_congr Equiv.ofInjective f hf

中文:
定理 card_range_of_injective
  条件: [有限类型 α] {f : α -> β} (hf : 单射 f) [有限类型 (range f)]
  证明: Eq.symm Fintype.card_congr Equiv.ofInjective f hf

Depends on / 依赖: Eq.symm, Equiv.ofInjective, Fintype, Fintype.card_congr, card_congr, ofInjective
-/
theorem card_range_of_injective [Fintype α] {f : α -> β} (hf : Injective f) [Fintype (range f)] :
    Fintype.card (range f) = Fintype.card α :=
Eq.symm Fintype.card_congr Equiv.ofInjective f hf

/--
theorem `Finite.card_toFinset` / 定理 `Finite.card_toFinset`

English:
theorem Finite.card_toFinset
  given: {s : Set α} [Fintype s] (h : s.Finite)
  proof: Eq.symm Fintype.card_of_finset' _ fun _ => h.mem_toFinset

中文:
定理 有限.card_toFinset
  条件: {s : 集合 α} [有限类型 s] (h : s.有限)
  证明: Eq.symm Fintype.card_of_finset' _ fun _ => h.mem_toFinset

Depends on / 依赖: Eq.symm, Fintype, Fintype.card_of_finset, card_of_finset, h.mem_toFinset, mem_toFinset
-/
theorem Finite.card_toFinset {s : Set α} [Fintype s] (h : s.Finite) :
    h.toFinset.card = Fintype.card s :=
Eq.symm Fintype.card_of_finset' _ fun _ => h.mem_toFinset

/--
theorem `card_ne_eq` / 定理 `card_ne_eq`

English:
theorem card_ne_eq
  given: [Fintype α] (a : α) [Fintype { x : α | x != a }]
  proof: by
  have := Classical.decEq α
  rw [← toFinset_card]; rw [toFinset_ofPred]; rw [Finset.filter_ne']; rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; rw [Finset.card_univ]

中文:
定理 card_ne_eq
  条件: [有限类型 α] (a : α) [有限类型 { x : α | x != a }]
  证明: by
  have := Classical.decEq α
  rw [← toFinset_card]; rw [toFinset_ofPred]; rw [Finset.filter_ne']; rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; rw [Finset.card_univ]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.card_erase_of_mem, Finset.card_univ, Finset.filter_ne, Finset.mem_univ, card_erase_of_mem, card_univ, filter_ne, mem_univ, toFinset_card, toFinset_ofPred
-/
theorem card_ne_eq [Fintype α] (a : α) [Fintype { x : α | x != a }] :
    Fintype.card { x : α | x != a } = Fintype.card α - 1 := by
  have := Classical.decEq α
  rw [← toFinset_card]; rw [toFinset_ofPred]; rw [Finset.filter_ne']; rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; rw [Finset.card_univ]

/-! ### Infinite sets -/

variable {s t : Set α}

/--
theorem `infinite_univ_iff` / 定理 `infinite_univ_iff`

English:
theorem infinite_univ_iff
  statement: (@univ α).Infinite ↔ Infinite α
  proof: by
  rw [Set.Infinite]; rw [finite_univ_iff]; rw [not_finite_iff_infinite]

中文:
定理 infinite_univ_iff
  结论: (@univ α).无限 ↔ 无限 α
  证明: by
  rw [Set.Infinite]; rw [finite_univ_iff]; rw [not_finite_iff_infinite]

Depends on / 依赖: Infinite, Set.Infinite, finite_univ_iff, not_finite_iff_infinite
-/
theorem infinite_univ_iff : (@univ α).Infinite ↔ Infinite α := by
  rw [Set.Infinite]; rw [finite_univ_iff]; rw [not_finite_iff_infinite]

/--
theorem `infinite_univ` / 定理 `infinite_univ`

English:
theorem infinite_univ
  given: [h : Infinite α]
  statement: (@univ α).Infinite
  proof: infinite_univ_iff.2 h

中文:
定理 infinite_univ
  条件: [h : 无限 α]
  结论: (@univ α).无限
  证明: infinite_univ_iff.2 h

Depends on / 依赖: infinite_univ_iff
-/
theorem infinite_univ [h : Infinite α] : (@univ α).Infinite :=
  infinite_univ_iff.2 h

/--
lemma `Infinite.exists_notMem_finite` / 引理 `Infinite.exists_notMem_finite`

English:
lemma Infinite.exists_notMem_finite
  given: (hs : s.Infinite) (ht : t.Finite)
  statement: exists a, a in s ∧ a ∉ t
  proof: by
by_contra! h; exact hs ht.subset h

中文:
引理 无限.存在_notMem_finite
  条件: (hs : s.无限) (ht : t.有限)
  结论: 存在 a, a in s ∧ a ∉ t
  证明: by
by_contra! h; exact hs ht.subset h

Depends on / 依赖: ht.subset, subset
-/
lemma Infinite.exists_notMem_finite (hs : s.Infinite) (ht : t.Finite) : exists a, a in s ∧ a ∉ t := by
by_contra! h; exact hs ht.subset h

/--
lemma `Infinite.exists_notMem_finset` / 引理 `Infinite.exists_notMem_finset`

English:
lemma Infinite.exists_notMem_finset
  given: (hs : s.Infinite) (t : Finset α)
  statement: exists a in s, a ∉ t
  proof: hs.exists_notMem_finite t.finite_toSet

中文:
引理 无限.存在_notMem_finset
  条件: (hs : s.无限) (t : 有限集 α)
  结论: 存在 a in s, a ∉ t
  证明: hs.exists_notMem_finite t.finite_toSet
-/
lemma Infinite.exists_notMem_finset (hs : s.Infinite) (t : Finset α) : exists a in s, a ∉ t :=
  hs.exists_notMem_finite t.finite_toSet

section Infinite
variable [Infinite α]

/--
lemma `Finite.exists_notMem` / 引理 `Finite.exists_notMem`

English:
lemma Finite.exists_notMem
  given: (hs : s.Finite)
  statement: exists a, a ∉ s
  proof: by
  by_contra! h; exact infinite_univ (hs.subset fun a _ => h _)

中文:
引理 有限.存在_notMem
  条件: (hs : s.有限)
  结论: 存在 a, a ∉ s
  证明: by
  by_contra! h; exact infinite_univ (hs.subset fun a _ => h _)

Depends on / 依赖: hs.subset, infinite_univ, subset
-/
lemma Finite.exists_notMem (hs : s.Finite) : exists a, a ∉ s := by
  by_contra! h; exact infinite_univ (hs.subset fun a _ => h _)

/--
lemma `_root_.Finset.exists_notMem` / 引理 `_root_.Finset.exists_notMem`

English:
lemma _root_.Finset.exists_notMem
  given: (s : Finset α)
  statement: exists a, a ∉ s
  proof: s.finite_toSet.exists_notMem

中文:
引理 _root_.有限集.存在_notMem
  条件: (s : 有限集 α)
  结论: 存在 a, a ∉ s
  证明: s.finite_toSet.exists_notMem

Depends on / 依赖: exists_notMem, finite_toSet, s.finite_toSet.exists_notMem
-/
lemma _root_.Finset.exists_notMem (s : Finset α) : exists a, a ∉ s := s.finite_toSet.exists_notMem

end Infinite

/--
Definition of `Infinite.natEmbedding` / `Infinite.natEmbedding` 的定义

English:
definition Infinite.natEmbedding
  signature: (s : Set α) (h : s.Infinite)
  body: h.to_subtype.natEmbedding

中文:
定义 无限.natEmbedding
  签名: (s : 集合 α) (h : s.无限)
  定义体: h.to_subtype.natEmbedding
-/
noncomputable def Infinite.natEmbedding (s : Set α) (h : s.Infinite) : Nat ↪ s :=
  h.to_subtype.natEmbedding

/--
theorem `Infinite.exists_subset_card_eq` / 定理 `Infinite.exists_subset_card_eq`

English:
theorem Infinite.exists_subset_card_eq
  given: {s : Set α} (hs : s.Infinite) (n : Nat)
  proof: ⟨((Finset.range n).map (hs.natEmbedding _)).map (Embedding.subtype _), by simp⟩

中文:
定理 无限.存在_subset_card_eq
  条件: {s : 集合 α} (hs : s.无限) (n : 自然数)
  证明: ⟨((Finset.range n).map (hs.natEmbedding _)).map (Embedding.subtype _), by simp⟩
-/
theorem Infinite.exists_subset_card_eq {s : Set α} (hs : s.Infinite) (n : Nat) :
    exists t : Finset α, ↑t subseteq s ∧ t.card = n :=
  ⟨((Finset.range n).map (hs.natEmbedding _)).map (Embedding.subtype _), by simp⟩

/--
theorem `infinite_of_finite_compl` / 定理 `infinite_of_finite_compl`

English:
theorem infinite_of_finite_compl
  given: [Infinite α] {s : Set α} (hs : sᶜ.Finite)
  statement: s.Infinite
  proof: fun h =>
  Set.infinite_univ (α := α) (by simpa using hs.union h)

中文:
定理 infinite_of_finite_compl
  条件: [无限 α] {s : 集合 α} (hs : sᶜ.有限)
  结论: s.无限
  证明: fun h =>
  Set.infinite_univ (α := α) (by simpa using hs.union h)
-/
theorem infinite_of_finite_compl [Infinite α] {s : Set α} (hs : sᶜ.Finite) : s.Infinite := fun h =>
  Set.infinite_univ (α := α) (by simpa using hs.union h)

/--
theorem `Finite.infinite_compl` / 定理 `Finite.infinite_compl`

English:
theorem Finite.infinite_compl
  given: [Infinite α] {s : Set α} (hs : s.Finite)
  statement: sᶜ.Infinite
  proof: fun h =>
  Set.infinite_univ (α := α) (by simpa using hs.union h)

中文:
定理 有限.infinite_compl
  条件: [无限 α] {s : 集合 α} (hs : s.有限)
  结论: sᶜ.无限
  证明: fun h =>
  Set.infinite_univ (α := α) (by simpa using hs.union h)
-/
theorem Finite.infinite_compl [Infinite α] {s : Set α} (hs : s.Finite) : sᶜ.Infinite := fun h =>
  Set.infinite_univ (α := α) (by simpa using hs.union h)

/--
theorem `Infinite.sdiff` / 定理 `Infinite.sdiff`

English:
theorem Infinite.sdiff
  given: {s t : Set α} (hs : s.Infinite) (ht : t.Finite)
  proof: fun h => hs h.of_sdiff ht

@[deprecated (since := "2026-06-03")] alias Infinite.diff := Infinite.sdiff

中文:
定理 无限.sdiff
  条件: {s t : 集合 α} (hs : s.无限) (ht : t.有限)
  证明: fun h => hs h.of_sdiff ht

@[deprecated (since := "2026-06-03")] alias Infinite.diff := Infinite.sdiff

Depends on / 依赖: h.of_sdiff, of_sdiff
-/
theorem Infinite.sdiff {s t : Set α} (hs : s.Infinite) (ht : t.Finite) :
(s \ t).Infinite := fun h => hs h.of_sdiff ht

@[deprecated (since := "2026-06-03")] alias Infinite.diff := Infinite.sdiff

/--
lemma `Infinite.inter_of_finite_sdiff` / 引理 `Infinite.inter_of_finite_sdiff`

English:
lemma Infinite.inter_of_finite_sdiff
  statement: {α : Type*} {s t : Set α} (hs : s.Infinite)
  proof: by
  simpa using hs.sdiff ht

@[deprecated (since := "2026-06-03")]
alias Infinite.inter_of_finite_diff := Infinite.inter_of_finite_sdiff

@[simp]

中文:
引理 无限.inter_of_finite_sdiff
  结论: {α : 类型} {s t : 集合 α} (hs : s.无限)
  证明: by
  simpa using hs.sdiff ht

@[deprecated (since := "2026-06-03")]
alias Infinite.inter_of_finite_diff := Infinite.inter_of_finite_sdiff

@[simp]

Depends on / 依赖: hs.sdiff
-/
lemma Infinite.inter_of_finite_sdiff {α : Type*} {s t : Set α} (hs : s.Infinite)
    (ht : (s \ t).Finite) : (s inter t).Infinite := by
  simpa using hs.sdiff ht

@[deprecated (since := "2026-06-03")]
alias Infinite.inter_of_finite_diff := Infinite.inter_of_finite_sdiff

@[simp]
/--
theorem `infinite_union` / 定理 `infinite_union`

English:
theorem infinite_union
  given: {s t : Set α}
  statement: (s union t).Infinite ↔ s.Infinite ∨ t.Infinite
  proof: by
  simp only [Set.Infinite, finite_union, not_and_or]

中文:
定理 infinite_union
  条件: {s t : 集合 α}
  结论: (s union t).无限 ↔ s.无限 ∨ t.无限
  证明: by
  simp only [Set.Infinite, finite_union, not_and_or]

Depends on / 依赖: Infinite, Set.Infinite, finite_union, not_and_or
-/
theorem infinite_union {s t : Set α} : (s union t).Infinite ↔ s.Infinite ∨ t.Infinite := by
  simp only [Set.Infinite, finite_union, not_and_or]

/--
theorem `Infinite.of_image` / 定理 `Infinite.of_image`

English:
theorem Infinite.of_image
  given: (f : α -> β) {s : Set α} (hs : (f '' s).Infinite)
  statement: s.Infinite
  proof: mt (Finite.image f) hs

中文:
定理 无限.of_image
  条件: (f : α -> β) {s : 集合 α} (hs : (f '' s).无限)
  结论: s.无限
  证明: mt (Finite.image f) hs

Depends on / 依赖: Finite, Finite.image
-/
theorem Infinite.of_image (f : α -> β) {s : Set α} (hs : (f '' s).Infinite) : s.Infinite :=
  mt (Finite.image f) hs

/--
theorem `infinite_image_iff` / 定理 `infinite_image_iff`

English:
theorem infinite_image_iff
  given: {s : Set α} {f : α -> β} (hi : InjOn f s)
  proof: not_congr finite_image_iff hi

中文:
定理 infinite_image_iff
  条件: {s : 集合 α} {f : α -> β} (hi : 单射限制 f s)
  证明: not_congr finite_image_iff hi

Depends on / 依赖: finite_image_iff, not_congr
-/
theorem infinite_image_iff {s : Set α} {f : α -> β} (hi : InjOn f s) :
    (f '' s).Infinite ↔ s.Infinite :=
not_congr finite_image_iff hi

/--
theorem `infinite_range_iff` / 定理 `infinite_range_iff`

English:
theorem infinite_range_iff
  given: {f : α -> β} (hf : Injective f)
  statement: (range f).Infinite ↔ Infinite α
  proof: by
  simpa using (finite_range_iff hf).not

protected alias ⟨_, Infinite.image⟩ := infinite_image_iff

中文:
定理 infinite_range_iff
  条件: {f : α -> β} (hf : 单射 f)
  结论: (range f).无限 ↔ 无限 α
  证明: by
  simpa using (finite_range_iff hf).not

protected alias ⟨_, Infinite.image⟩ := infinite_image_iff

Depends on / 依赖: finite_range_iff
-/
theorem infinite_range_iff {f : α -> β} (hf : Injective f) : (range f).Infinite ↔ Infinite α := by
  simpa using (finite_range_iff hf).not

protected alias ⟨_, Infinite.image⟩ := infinite_image_iff

/--
theorem `infinite_of_injOn_mapsTo` / 定理 `infinite_of_injOn_mapsTo`

English:
theorem infinite_of_injOn_mapsTo
  statement: {s : Set α} {t : Set β} {f : α -> β} (hi : InjOn f s)
  proof: ((infinite_image_iff hi).2 hs).mono (mapsTo_iff_image_subset.mp hm)

中文:
定理 infinite_of_injOn_mapsTo
  结论: {s : 集合 α} {t : 集合 β} {f : α -> β} (hi : 单射限制 f s)
  证明: ((infinite_image_iff hi).2 hs).mono (mapsTo_iff_image_subset.mp hm)

Depends on / 依赖: infinite_image_iff, mapsTo_iff_image_subset, mapsTo_iff_image_subset.mp
-/
theorem infinite_of_injOn_mapsTo {s : Set α} {t : Set β} {f : α -> β} (hi : InjOn f s)
    (hm : MapsTo f s t) (hs : s.Infinite) : t.Infinite :=
  ((infinite_image_iff hi).2 hs).mono (mapsTo_iff_image_subset.mp hm)

/--
theorem `Infinite.exists_ne_map_eq_of_mapsTo` / 定理 `Infinite.exists_ne_map_eq_of_mapsTo`

English:
theorem Infinite.exists_ne_map_eq_of_mapsTo
  statement: {s : Set α} {t : Set β} {f : α -> β} (hs : s.Infinite)
  proof: by
  contrapose! ht
  exact infinite_of_injOn_mapsTo (fun x hx y hy => not_imp_not.1 (ht x hx y hy)) hf hs

中文:
定理 无限.存在_ne_map_eq_of_mapsTo
  结论: {s : 集合 α} {t : 集合 β} {f : α -> β} (hs : s.无限)
  证明: by
  contrapose! ht
  exact infinite_of_injOn_mapsTo (fun x hx y hy => not_imp_not.1 (ht x hx y hy)) hf hs

Depends on / 依赖: contrapose, infinite_of_injOn_mapsTo, not_imp_not
-/
theorem Infinite.exists_ne_map_eq_of_mapsTo {s : Set α} {t : Set β} {f : α -> β} (hs : s.Infinite)
    (hf : MapsTo f s t) (ht : t.Finite) : exists x in s, exists y in s, x != y ∧ f x = f y := by
  contrapose! ht
  exact infinite_of_injOn_mapsTo (fun x hx y hy => not_imp_not.1 (ht x hx y hy)) hf hs

/--
theorem `infinite_range_of_injective` / 定理 `infinite_range_of_injective`

English:
theorem infinite_range_of_injective
  given: [Infinite α] {f : α -> β} (hi : Injective f)
  proof: by
  rw [← image_univ]; rw [infinite_image_iff hi.injOn]
  exact infinite_univ

中文:
定理 infinite_range_of_injective
  条件: [无限 α] {f : α -> β} (hi : 单射 f)
  证明: by
  rw [← image_univ]; rw [infinite_image_iff hi.injOn]
  exact infinite_univ

Depends on / 依赖: hi.injOn, image_univ, infinite_image_iff, infinite_univ
-/
theorem infinite_range_of_injective [Infinite α] {f : α -> β} (hi : Injective f) :
    (range f).Infinite := by
  rw [← image_univ]; rw [infinite_image_iff hi.injOn]
  exact infinite_univ

/--
theorem `infinite_of_injective_forall_mem` / 定理 `infinite_of_injective_forall_mem`

English:
theorem infinite_of_injective_forall_mem
  statement: [Infinite α] {s : Set β} {f : α -> β} (hi : Injective f)
  proof: by
  rw [← range_subset_iff] at hf
  exact (infinite_range_of_injective hi).mono hf

中文:
定理 infinite_of_injective_对任意_mem
  结论: [无限 α] {s : 集合 β} {f : α -> β} (hi : 单射 f)
  证明: by
  rw [← range_subset_iff] at hf
  exact (infinite_range_of_injective hi).mono hf

Depends on / 依赖: infinite_range_of_injective, range_subset_iff
-/
theorem infinite_of_injective_forall_mem [Infinite α] {s : Set β} {f : α -> β} (hi : Injective f)
    (hf : forall x : α, f x in s) : s.Infinite := by
  rw [← range_subset_iff] at hf
  exact (infinite_range_of_injective hi).mono hf

set_option backward.isDefEq.respectTransparency false in
/--
theorem `not_injOn_infinite_finite_image` / 定理 `not_injOn_infinite_finite_image`

English:
theorem not_injOn_infinite_finite_image
  statement: {f : α -> β} {s : Set α} (h_inf : s.Infinite)
  proof: by
  have : Finite (f '' s) := finite_coe_iff.mpr h_fin
  have : Infinite s := infinite_coe_iff.mpr h_inf
  have h := not_injective_infinite_finite
            ((f '' s).codRestrict (s.domRestrict f) fun x => ⟨x, x.property, rfl⟩)
  contrapose h
  rwa [injective_codRestrict, ← injOn_iff_injective]

中文:
定理 not_injOn_infinite_finite_image
  结论: {f : α -> β} {s : 集合 α} (h_inf : s.无限)
  证明: by
  have : Finite (f '' s) := finite_coe_iff.mpr h_fin
  have : Infinite s := infinite_coe_iff.mpr h_inf
  have h := not_injective_infinite_finite
            ((f '' s).codRestrict (s.domRestrict f) fun x => ⟨x, x.property, rfl⟩)
  contrapose h
  rwa [injective_codRestrict, ← injOn_iff_injective]

Depends on / 依赖: Finite, Infinite, codRestrict, contrapose, domRestrict, finite_coe_iff, finite_coe_iff.mpr, h_fin, h_inf, infinite_coe_iff, infinite_coe_iff.mpr, injOn_iff_injective, injective_codRestrict, not_injective_infinite_finite, property, s.domRestrict, x.property
-/
theorem not_injOn_infinite_finite_image {f : α -> β} {s : Set α} (h_inf : s.Infinite)
    (h_fin : (f '' s).Finite) : ¬InjOn f s := by
  have : Finite (f '' s) := finite_coe_iff.mpr h_fin
  have : Infinite s := infinite_coe_iff.mpr h_inf
  have h := not_injective_infinite_finite
            ((f '' s).codRestrict (s.domRestrict f) fun x => ⟨x, x.property, rfl⟩)
  contrapose h
  rwa [injective_codRestrict, ← injOn_iff_injective]

/--
theorem `finite_range_findGreatest` / 定理 `finite_range_findGreatest`

English:
theorem finite_range_findGreatest
  given: {P : α -> Nat -> Prop} [forall x, DecidablePred (P x)] {b : Nat}
  proof: (finite_le_nat b).subset range_subset_iff.2 fun _ => Nat.findGreatest_le _

中文:
定理 finite_range_findGreatest
  条件: {P : α -> 自然数 -> 命题} [对任意 x, DecidablePred (P x)] {b : 自然数}
  证明: (finite_le_nat b).subset range_subset_iff.2 fun _ => Nat.findGreatest_le _

Depends on / 依赖: Nat.findGreatest_le, findGreatest_le, finite_le_nat, range_subset_iff, subset
-/
theorem finite_range_findGreatest {P : α -> Nat -> Prop} [forall x, DecidablePred (P x)] {b : Nat} :
    (range fun x => Nat.findGreatest (P x) b).Finite :=
(finite_le_nat b).subset range_subset_iff.2 fun _ => Nat.findGreatest_le _

end Set

namespace Finset

/--
lemma `exists_card_eq` / 引理 `exists_card_eq`

English:
lemma exists_card_eq
  given: [Infinite α]
  statement: forall n : Nat, exists s : Finset α, s.card = n
  proof: exists_card_eq n
    obtain ⟨a, ha⟩ := s.exists_notMem
    exact ⟨insert a s, card_insert_of_notMem ha⟩

中文:
引理 存在_card_eq
  条件: [无限 α]
  结论: 对任意 n : 自然数, 存在 s : 有限集 α, s.card = n
  证明: exists_card_eq n
    obtain ⟨a, ha⟩ := s.exists_notMem
    exact ⟨insert a s, card_insert_of_notMem ha⟩

Depends on / 依赖: exists_card_eq
-/
lemma exists_card_eq [Infinite α] : forall n : Nat, exists s : Finset α, s.card = n
  | 0 => ⟨∅, card_empty⟩
  | n + 1 => by
    classical
    obtain ⟨s, rfl⟩ := exists_card_eq n
    obtain ⟨a, ha⟩ := s.exists_notMem
    exact ⟨insert a s, card_insert_of_notMem ha⟩

/--
lemma `exists_subset_injOn_image_eq_of_surjOn` / 引理 `exists_subset_injOn_image_eq_of_surjOn`

English:
lemma exists_subset_injOn_image_eq_of_surjOn
  statement: [DecidableEq β] {f : α -> β}
  proof: by
  obtain ⟨u, hus, hf, himg⟩ := hfs.exists_subset_injOn_image_eq
  refine ⟨(Finite.of_finite_image (by simp [himg]) hf).toFinset, by simpa, by simpa, ?_⟩
  simpa [← Finset.coe_inj]

中文:
引理 存在_subset_injOn_image_eq_of_surjOn
  结论: [DecidableEq β] {f : α -> β}
  证明: by
  obtain ⟨u, hus, hf, himg⟩ := hfs.exists_subset_injOn_image_eq
  refine ⟨(Finite.of_finite_image (by simp [himg]) hf).toFinset, by simpa, by simpa, ?_⟩
  simpa [← Finset.coe_inj]

Depends on / 依赖: Finite, Finite.of_finite_image, Finset, Finset.coe_inj, coe_inj, exists_subset_injOn_image_eq, hfs.exists_subset_injOn_image_eq, of_finite_image, toFinset
-/
lemma exists_subset_injOn_image_eq_of_surjOn [DecidableEq β] {f : α -> β}
    (s : Set α) (t : Finset β) (hfs : s.SurjOn f t) :
    exists u : Finset α, ↑u subseteq s ∧ Set.InjOn f u ∧ u.image f = t := by
  obtain ⟨u, hus, hf, himg⟩ := hfs.exists_subset_injOn_image_eq
  refine ⟨(Finite.of_finite_image (by simp [himg]) hf).toFinset, by simpa, by simpa, ?_⟩
  simpa [← Finset.coe_inj]

end Finset

section LinearOrder
variable [LinearOrder α] {s : Set α}

/--
lemma `Finite.of_forall_not_lt_lt` / 引理 `Finite.of_forall_not_lt_lt`

English:
lemma Finite.of_forall_not_lt_lt
  given: (h : forall ⦃x y z : α⦄, x < y -> y < z -> False)
  statement: Finite α
  proof: by
  nontriviality α
  rcases exists_pair_ne α with ⟨x, y, hne⟩
  refine @Finite.of_fintype α ⟨{x, y}, fun z => ?_⟩
  simpa [hne] using eq_or_eq_or_eq_of_forall_not_lt_lt h z x y

中文:
引理 有限.of_对任意_not_lt_lt
  条件: (h : 对任意 ⦃x y z : α⦄, x < y -> y < z -> 假)
  结论: 有限 α
  证明: by
  nontriviality α
  rcases exists_pair_ne α with ⟨x, y, hne⟩
  refine @Finite.of_fintype α ⟨{x, y}, fun z => ?_⟩
  simpa [hne] using eq_or_eq_or_eq_of_forall_not_lt_lt h z x y

Depends on / 依赖: Finite, Finite.of_fintype, eq_or_eq_or_eq_of_forall_not_lt_lt, exists_pair_ne, nontriviality, of_fintype
-/
lemma Finite.of_forall_not_lt_lt (h : forall ⦃x y z : α⦄, x < y -> y < z -> False) : Finite α := by
  nontriviality α
  rcases exists_pair_ne α with ⟨x, y, hne⟩
  refine @Finite.of_fintype α ⟨{x, y}, fun z => ?_⟩
  simpa [hne] using eq_or_eq_or_eq_of_forall_not_lt_lt h z x y

/--
lemma `Set.finite_of_forall_not_lt_lt` / 引理 `Set.finite_of_forall_not_lt_lt`

English:
lemma Set.finite_of_forall_not_lt_lt
  given: (h : forall x in s, forall y in s, forall z in s, x < y -> y < z -> False)
  proof: @Set.toFinite _ s Finite.of_forall_not_lt_lt by simpa only [SetCoe.forall'] using! h

中文:
引理 集合.finite_of_对任意_not_lt_lt
  条件: (h : 对任意 x in s, 对任意 y in s, 对任意 z in s, x < y -> y < z -> 假)
  证明: @Set.toFinite _ s Finite.of_forall_not_lt_lt by simpa only [SetCoe.forall'] using! h

Depends on / 依赖: Finite, Finite.of_forall_not_lt_lt, Set.toFinite, SetCoe, SetCoe.forall, of_forall_not_lt_lt, toFinite
-/
lemma Set.finite_of_forall_not_lt_lt (h : forall x in s, forall y in s, forall z in s, x < y -> y < z -> False) :
    Set.Finite s :=
@Set.toFinite _ s Finite.of_forall_not_lt_lt by simpa only [SetCoe.forall'] using! h

end LinearOrder
