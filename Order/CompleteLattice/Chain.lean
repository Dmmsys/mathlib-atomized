/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Preorder.Chain

/-!
# Hausdorff's maximality principle

This file proves Hausdorff's maximality principle.

## Main declarations

* `maxChain_spec`: Hausdorff's Maximality Principle.

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/

@[expose] public section

open Set

variable {α : Type*} {r : α -> α -> Prop} {c c₁ c₂ s t : Set α} {a b x y : α}

/--
Inductive type `ChainClosure` / 归纳类型 `ChainClosure`

English:
inductive ChainClosure
  parameters: (r : α -> α -> Prop)
  constructors (2):
    - succ: forall {s}, ChainClosure r s -> ChainClosure r (SuccChain r s)
    - union: forall {s}, (forall a in s, ChainClosure r a) -> ChainClosure r (⋃₀ s)

中文:
归纳类型 ChainClosure
  参数: (r : α -> α -> 命题)
  构造子 (2 个):
    - succ: 对任意 {s}, ChainClosure r s -> ChainClosure r (SuccChain r s)
    - union: 对任意 {s}, (对任意 a in s, ChainClosure r a) -> ChainClosure r (⋃₀ s)
-/
inductive ChainClosure (r : α -> α -> Prop) : Set α -> Prop
  | succ : forall {s}, ChainClosure r s -> ChainClosure r (SuccChain r s)
  | union : forall {s}, (forall a in s, ChainClosure r a) -> ChainClosure r (⋃₀ s)

/--
Definition of `maxChain` / `maxChain` 的定义

English:
definition maxChain
  signature: (r : α -> α -> Prop)
  body: ⋃₀ Set.ofPred (ChainClosure r)

中文:
定义 maxChain
  签名: (r : α -> α -> 命题)
  定义体: ⋃₀ Set.ofPred (ChainClosure r)

Depends on / 依赖: ChainClosure, Set.ofPred, ofPred
-/
def maxChain (r : α -> α -> Prop) : Set α := ⋃₀ Set.ofPred (ChainClosure r)

/--
lemma `chainClosure_empty` / 引理 `chainClosure_empty`

English:
lemma chainClosure_empty
  statement: ChainClosure r ∅
  proof: by
  have : ChainClosure r (⋃₀ ∅) := ChainClosure.union fun a h => (notMem_empty _ h).elim
  simpa using this

中文:
引理 chainClosure_empty
  结论: ChainClosure r ∅
  证明: by
  have : ChainClosure r (⋃₀ ∅) := ChainClosure.union fun a h => (notMem_empty _ h).elim
  simpa using this

Depends on / 依赖: ChainClosure, ChainClosure.union, notMem_empty
-/
lemma chainClosure_empty : ChainClosure r ∅ := by
  have : ChainClosure r (⋃₀ ∅) := ChainClosure.union fun a h => (notMem_empty _ h).elim
  simpa using this

/--
lemma `chainClosure_maxChain` / 引理 `chainClosure_maxChain`

English:
lemma chainClosure_maxChain
  statement: ChainClosure r (maxChain r)
  proof: ChainClosure.union fun _ => id

中文:
引理 chainClosure_maxChain
  结论: ChainClosure r (maxChain r)
  证明: ChainClosure.union fun _ => id

Depends on / 依赖: ChainClosure, ChainClosure.union
-/
lemma chainClosure_maxChain : ChainClosure r (maxChain r) :=
  ChainClosure.union fun _ => id

/--
lemma `chainClosure_succ_total_aux` / 引理 `chainClosure_succ_total_aux`

English:
lemma chainClosure_succ_total_aux
  statement: (hc₁ : ChainClosure r c₁)
  proof: by
  induction hc₁ with
  | @succ c₃ hc₃ ih =>
    obtain ih | ih := ih
    · exact Or.inl (ih.trans subset_succChain)
    · exact (h hc₃ ih).imp_left fun (h : c₂ = c₃) => h ▸ Subset.rfl
  | union _ ih =>
    refine or_iff_not_imp_left.2 fun hn => sUnion_subset fun a ha => ?_
exact (ih a ha).resolve

中文:
引理 chainClosure_succ_total_aux
  结论: (hc₁ : ChainClosure r c₁)
  证明: by
  induction hc₁ with
  | @succ c₃ hc₃ ih =>
    obtain ih | ih := ih
    · exact Or.inl (ih.trans subset_succChain)
    · exact (h hc₃ ih).imp_left fun (h : c₂ = c₃) => h ▸ Subset.rfl
  | union _ ih =>
    refine or_iff_not_imp_left.2 fun hn => sUnion_subset fun a ha => ?_
exact (ih a ha).resolve
-/
private lemma chainClosure_succ_total_aux (hc₁ : ChainClosure r c₁)
    (h : forall ⦃c₃⦄, ChainClosure r c₃ -> c₃ subseteq c₂ -> c₂ = c₃ ∨ SuccChain r c₃ subseteq c₂) :
    SuccChain r c₂ subseteq c₁ ∨ c₁ subseteq c₂ := by
  induction hc₁ with
  | @succ c₃ hc₃ ih =>
    obtain ih | ih := ih
    · exact Or.inl (ih.trans subset_succChain)
    · exact (h hc₃ ih).imp_left fun (h : c₂ = c₃) => h ▸ Subset.rfl
  | union _ ih =>
    refine or_iff_not_imp_left.2 fun hn => sUnion_subset fun a ha => ?_
exact (ih a ha).resolve_left fun h => hn h.trans subset_sUnion_of_mem ha

/--
lemma `chainClosure_succ_total` / 引理 `chainClosure_succ_total`

English:
lemma chainClosure_succ_total
  statement: (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
  proof: by
  induction hc₂ generalizing c₁ hc₁ with
  | succ _ ih =>
    refine ((chainClosure_succ_total_aux hc₁) fun c₁ => ih).imp h.antisymm' fun h₁ => ?_
    obtain rfl | h₂ := ih hc₁ h₁
    · exact Subset.rfl
    · exact h₂.trans subset_succChain
  | union _ ih =>
    apply Or.imp_left h.antisymm'
    

中文:
引理 chainClosure_succ_total
  结论: (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
  证明: by
  induction hc₂ generalizing c₁ hc₁ with
  | succ _ ih =>
    refine ((chainClosure_succ_total_aux hc₁) fun c₁ => ih).imp h.antisymm' fun h₁ => ?_
    obtain rfl | h₂ := ih hc₁ h₁
    · exact Subset.rfl
    · exact h₂.trans subset_succChain
  | union _ ih =>
    apply Or.imp_left h.antisymm'
    
-/
private lemma chainClosure_succ_total (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
    (h : c₁ subseteq c₂) : c₂ = c₁ ∨ SuccChain r c₁ subseteq c₂ := by
  induction hc₂ generalizing c₁ hc₁ with
  | succ _ ih =>
    refine ((chainClosure_succ_total_aux hc₁) fun c₁ => ih).imp h.antisymm' fun h₁ => ?_
    obtain rfl | h₂ := ih hc₁ h₁
    · exact Subset.rfl
    · exact h₂.trans subset_succChain
  | union _ ih =>
    apply Or.imp_left h.antisymm'
    apply by_contradiction
    simp only [sUnion_subset_iff, not_or, not_forall, exists_prop, and_imp, forall_exists_index]
    intro c₃ hc₃ h₁ h₂
    obtain h | h := chainClosure_succ_total_aux hc₁ fun c₄ => ih _ hc₃
    · exact h₁ (subset_succChain.trans h)
    obtain h' | h' := ih c₃ hc₃ hc₁ h
    · exact h₁ h'.subset
    · exact h₂ (h'.trans <| subset_sUnion_of_mem hc₃)

/--
lemma `ChainClosure.total` / 引理 `ChainClosure.total`

English:
lemma ChainClosure.total
  given: (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
  proof: ((chainClosure_succ_total_aux hc₂) fun _ hc₃ => chainClosure_succ_total hc₃ hc₁).imp_left
    subset_succChain.trans

中文:
引理 ChainClosure.total
  条件: (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
  证明: ((chainClosure_succ_total_aux hc₂) fun _ hc₃ => chainClosure_succ_total hc₃ hc₁).imp_left
    subset_succChain.trans

Depends on / 依赖: chainClosure_succ_total, chainClosure_succ_total_aux, imp_left, subset_succChain, subset_succChain.trans
-/
lemma ChainClosure.total (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂) :
    c₁ subseteq c₂ ∨ c₂ subseteq c₁ :=
  ((chainClosure_succ_total_aux hc₂) fun _ hc₃ => chainClosure_succ_total hc₃ hc₁).imp_left
    subset_succChain.trans

/--
lemma `ChainClosure.succ_fixpoint` / 引理 `ChainClosure.succ_fixpoint`

English:
lemma ChainClosure.succ_fixpoint
  statement: (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
  proof: by
  induction hc₁ with
  | succ hc₁ h => exact (chainClosure_succ_total hc₁ hc₂ h).elim (fun h => h ▸ hc.subset) id
  | union _ ih => exact sUnion_subset ih

中文:
引理 ChainClosure.succ_fixpoint
  结论: (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
  证明: by
  induction hc₁ with
  | succ hc₁ h => exact (chainClosure_succ_total hc₁ hc₂ h).elim (fun h => h ▸ hc.subset) id
  | union _ ih => exact sUnion_subset ih

Depends on / 依赖: chainClosure_succ_total, hc.subset, sUnion_subset, subset
-/
lemma ChainClosure.succ_fixpoint (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
    (hc : SuccChain r c₂ = c₂) : c₁ subseteq c₂ := by
  induction hc₁ with
  | succ hc₁ h => exact (chainClosure_succ_total hc₁ hc₂ h).elim (fun h => h ▸ hc.subset) id
  | union _ ih => exact sUnion_subset ih

/--
lemma `ChainClosure.succ_fixpoint_iff` / 引理 `ChainClosure.succ_fixpoint_iff`

English:
lemma ChainClosure.succ_fixpoint_iff
  given: (hc : ChainClosure r c)
  proof: ⟨fun h => (subset_sUnion_of_mem hc).antisymm chainClosure_maxChain.succ_fixpoint hc h,
fun h => subset_succChain.antisymm' (subset_sUnion_of_mem hc.succ).trans h.symm.subset⟩

中文:
引理 ChainClosure.succ_fixpoint_iff
  条件: (hc : ChainClosure r c)
  证明: ⟨fun h => (subset_sUnion_of_mem hc).antisymm chainClosure_maxChain.succ_fixpoint hc h,
fun h => subset_succChain.antisymm' (subset_sUnion_of_mem hc.succ).trans h.symm.subset⟩

Depends on / 依赖: antisymm, chainClosure_maxChain, chainClosure_maxChain.succ_fixpoint, h.symm.subset, hc.succ, subset, subset_sUnion_of_mem, subset_succChain, subset_succChain.antisymm, succ_fixpoint
-/
lemma ChainClosure.succ_fixpoint_iff (hc : ChainClosure r c) :
    SuccChain r c = c ↔ c = maxChain r :=
⟨fun h => (subset_sUnion_of_mem hc).antisymm chainClosure_maxChain.succ_fixpoint hc h,
fun h => subset_succChain.antisymm' (subset_sUnion_of_mem hc.succ).trans h.symm.subset⟩

/--
lemma `ChainClosure.isChain` / 引理 `ChainClosure.isChain`

English:
lemma ChainClosure.isChain
  given: (hc : ChainClosure r c)
  statement: IsChain r c
  proof: by
  induction hc with
  | succ _ h => exact h.succ
  | union hs h =>
    exact fun c₁ ⟨t₁, ht₁, (hc₁ : c₁ in t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ in t₂)⟩ hneq =>
      ((hs _ ht₁).total <| hs _ ht₂).elim (fun ht => h t₂ ht₂ (ht hc₁) hc₂ hneq) fun ht =>
        h t₁ ht₁ hc₁ (ht hc₂) hneq

中文:
引理 ChainClosure.isChain
  条件: (hc : ChainClosure r c)
  结论: IsChain r c
  证明: by
  induction hc with
  | succ _ h => exact h.succ
  | union hs h =>
    exact fun c₁ ⟨t₁, ht₁, (hc₁ : c₁ in t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ in t₂)⟩ hneq =>
      ((hs _ ht₁).total <| hs _ ht₂).elim (fun ht => h t₂ ht₂ (ht hc₁) hc₂ hneq) fun ht =>
        h t₁ ht₁ hc₁ (ht hc₂) hneq

Depends on / 依赖: h.succ
-/
lemma ChainClosure.isChain (hc : ChainClosure r c) : IsChain r c := by
  induction hc with
  | succ _ h => exact h.succ
  | union hs h =>
    exact fun c₁ ⟨t₁, ht₁, (hc₁ : c₁ in t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ in t₂)⟩ hneq =>
      ((hs _ ht₁).total <| hs _ ht₂).elim (fun ht => h t₂ ht₂ (ht hc₁) hc₂ hneq) fun ht =>
        h t₁ ht₁ hc₁ (ht hc₂) hneq

/--
theorem `maxChain_spec` / 定理 `maxChain_spec`

English:
theorem maxChain_spec
  statement: IsMaxChain r (maxChain r)
  proof: by_contradiction fun h =>
    let ⟨_, H⟩ := chainClosure_maxChain.isChain.superChain_succChain h
    H.ne (chainClosure_maxChain.succ_fixpoint_iff.mpr rfl).symm

中文:
定理 maxChain_spec
  结论: IsMaxChain r (maxChain r)
  证明: by_contradiction fun h =>
    let ⟨_, H⟩ := chainClosure_maxChain.isChain.superChain_succChain h
    H.ne (chainClosure_maxChain.succ_fixpoint_iff.mpr rfl).symm

Depends on / 依赖: H.ne, by_contradiction, chainClosure_maxChain, chainClosure_maxChain.isChain.superChain_succChain, chainClosure_maxChain.succ_fixpoint_iff.mpr, isChain, succ_fixpoint_iff, superChain_succChain
-/
theorem maxChain_spec : IsMaxChain r (maxChain r) :=
  by_contradiction fun h =>
    let ⟨_, H⟩ := chainClosure_maxChain.isChain.superChain_succChain h
    H.ne (chainClosure_maxChain.succ_fixpoint_iff.mpr rfl).symm
