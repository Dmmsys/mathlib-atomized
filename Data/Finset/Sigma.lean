/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Set.Sigma
public import Mathlib.Order.CompleteLattice.Finset

/-!
# Finite sets in a sigma type

This file defines a few `Finset` constructions on `Σ i, α i`.

## Main declarations

* `Finset.sigma`: Given a finset `s` in `ι` and finsets `t i` in each `α i`, `s.sigma t` is the
  finset of the dependent sum `Σ i, α i`
* `Finset.sigmaLift`: Lifts maps `α i → β i → Finset (γ i)` to a map
  `Σ i, α i → Σ i, β i → Finset (Σ i, γ i)`.

## TODO

`Finset.sigmaLift` can be generalized to any alternative functor. But to make the generalization
worth it, we must first refactor the functor library so that the `alternative` instance for `Finset`
is computable and universe-polymorphic.
-/

@[expose] public section


open Function Multiset

variable {ι : Type*}

namespace Finset

section Sigma

variable {α : ι -> Type*} {β : Type*} (s s₁ s₂ : Finset ι) (t t₁ t₂ : forall i, Finset (α i))

/--
Definition of `sigma` / `sigma` 的定义

English:
definition sigma
  signature: : Finset (Σ i, α i)
  body: ⟨_, s.nodup.sigma fun i => (t i).nodup⟩

中文:
定义 sigma
  签名: : Finset (Σ i, α i)
  定义体: ⟨_, s.nodup.sigma fun i => (t i).nodup⟩
-/
protected def sigma : Finset (Σ i, α i) :=
  ⟨_, s.nodup.sigma fun i => (t i).nodup⟩

variable {s s₁ s₂ t t₁ t₂}

@[simp, grind =]
/--
theorem `mem_sigma` / 定理 `mem_sigma`

English:
theorem mem_sigma
  given: {a : Σ i, α i}
  statement: a in s.sigma t ↔ a.1 in s ∧ a.2 in t a.1
  proof: Multiset.mem_sigma

@[simp, norm_cast]

中文:
定理 mem_sigma
  条件: {a : Σ i, α i}
  结论: a in s.sigma t ↔ a.1 in s ∧ a.2 in t a.1
  证明: Multiset.mem_sigma

@[simp, norm_cast]

Depends on / 依赖: Multiset, Multiset.mem_sigma, mem_sigma
-/
theorem mem_sigma {a : Σ i, α i} : a in s.sigma t ↔ a.1 in s ∧ a.2 in t a.1 :=
  Multiset.mem_sigma

@[simp, norm_cast]
/--
theorem `coe_sigma` / 定理 `coe_sigma`

English:
theorem coe_sigma
  given: (s : Finset ι) (t : forall i, Finset (α i))
  proof: Set.ext fun _ => mem_sigma

@[simp]

中文:
定理 coe_sigma
  条件: (s : Finset ι) (t : 对任意 i, Finset (α i))
  证明: Set.ext fun _ => mem_sigma

@[simp]

Depends on / 依赖: Set.ext, mem_sigma
-/
theorem coe_sigma (s : Finset ι) (t : forall i, Finset (α i)) :
    (s.sigma t : Set (Σ i, α i)) = (s : Set ι).sigma fun i => (t i : Set (α i)) :=
  Set.ext fun _ => mem_sigma

@[simp]
/--
theorem `sigma_nonempty` / 定理 `sigma_nonempty`

English:
theorem sigma_nonempty
  statement: (s.sigma t).Nonempty ↔ exists i in s, (t i).Nonempty
  proof: by simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.sigma_nonempty_of_exists_nonempty⟩ := sigma_nonempty

@[simp]

中文:
定理 sigma_nonempty
  结论: (s.sigma t).Nonempty ↔ 存在 i in s, (t i).Nonempty
  证明: by simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.sigma_nonempty_of_exists_nonempty⟩ := sigma_nonempty

@[simp]

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty
-/
theorem sigma_nonempty : (s.sigma t).Nonempty ↔ exists i in s, (t i).Nonempty := by simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.sigma_nonempty_of_exists_nonempty⟩ := sigma_nonempty

@[simp]
/--
theorem `sigma_eq_empty` / 定理 `sigma_eq_empty`

English:
theorem sigma_eq_empty
  statement: s.sigma t = ∅ ↔ forall i in s, t i = ∅
  proof: by
  contrapose!; exact sigma_nonempty

@[gcongr, mono]

中文:
定理 sigma_eq_empty
  结论: s.sigma t = ∅ ↔ 对任意 i in s, t i = ∅
  证明: by
  contrapose!; exact sigma_nonempty

@[gcongr, mono]

Depends on / 依赖: contrapose, sigma_nonempty
-/
theorem sigma_eq_empty : s.sigma t = ∅ ↔ forall i in s, t i = ∅ := by
  contrapose!; exact sigma_nonempty

@[gcongr, mono]
/--
theorem `sigma_mono` / 定理 `sigma_mono`

English:
theorem sigma_mono
  given: (hs : s₁ subseteq s₂) (ht : forall i, t₁ i subseteq t₂ i)
  statement: s₁.sigma t₁ subseteq s₂.sigma t₂
  proof: fun ⟨i, _⟩ h =>
  let ⟨hi, ha⟩ := mem_sigma.1 h
  mem_sigma.2 ⟨hs hi, ht i ha⟩

中文:
定理 sigma_mono
  条件: (hs : s₁ subseteq s₂) (ht : 对任意 i, t₁ i subseteq t₂ i)
  结论: s₁.sigma t₁ subseteq s₂.sigma t₂
  证明: fun ⟨i, _⟩ h =>
  let ⟨hi, ha⟩ := mem_sigma.1 h
  mem_sigma.2 ⟨hs hi, ht i ha⟩

Depends on / 依赖: mem_sigma
-/
theorem sigma_mono (hs : s₁ subseteq s₂) (ht : forall i, t₁ i subseteq t₂ i) : s₁.sigma t₁ subseteq s₂.sigma t₂ :=
  fun ⟨i, _⟩ h =>
  let ⟨hi, ha⟩ := mem_sigma.1 h
  mem_sigma.2 ⟨hs hi, ht i ha⟩

/--
theorem `pairwiseDisjoint_map_sigmaMk` / 定理 `pairwiseDisjoint_map_sigmaMk`

English:
theorem pairwiseDisjoint_map_sigmaMk
  proof: by
  intro i _ j _ hij
  rw [Function.onFun]; rw [disjoint_left]
  simp_rw [mem_map, Function.Embedding.sigmaMk_apply]
  rintro _ ⟨y, _, rfl⟩ ⟨z, _, hz'⟩
  exact hij (congr_arg Sigma.fst hz'.symm)

@[simp]

中文:
定理 pairwiseDisjoint_map_sigmaMk
  证明: by
  intro i _ j _ hij
  rw [Function.onFun]; rw [disjoint_left]
  simp_rw [mem_map, Function.Embedding.sigmaMk_apply]
  rintro _ ⟨y, _, rfl⟩ ⟨z, _, hz'⟩
  exact hij (congr_arg Sigma.fst hz'.symm)

@[simp]

Depends on / 依赖: Embedding, Function, Function.Embedding.sigmaMk_apply, Function.onFun, Sigma.fst, congr_arg, disjoint_left, mem_map, sigmaMk_apply, simp_rw
-/
theorem pairwiseDisjoint_map_sigmaMk :
    (s : Set ι).PairwiseDisjoint fun i => (t i).map (Embedding.sigmaMk i) := by
  intro i _ j _ hij
  rw [Function.onFun]; rw [disjoint_left]
  simp_rw [mem_map, Function.Embedding.sigmaMk_apply]
  rintro _ ⟨y, _, rfl⟩ ⟨z, _, hz'⟩
  exact hij (congr_arg Sigma.fst hz'.symm)

@[simp]
/--
theorem `disjiUnion_map_sigma_mk` / 定理 `disjiUnion_map_sigma_mk`

English:
theorem disjiUnion_map_sigma_mk
  proof: rfl

中文:
定理 disjiUnion_map_sigma_mk
  证明: rfl
-/
theorem disjiUnion_map_sigma_mk :
    s.disjiUnion (fun i => (t i).map (Embedding.sigmaMk i)) pairwiseDisjoint_map_sigmaMk =
      s.sigma t :=
  rfl

/--
theorem `sigma_eq_biUnion` / 定理 `sigma_eq_biUnion`

English:
theorem sigma_eq_biUnion
  given: [DecidableEq (Σ i, α i)] (s : Finset ι) (t : forall i, Finset (α i))
  proof: by
  ext ⟨x, y⟩
  simp [and_left_comm]

中文:
定理 sigma_eq_biUnion
  条件: [DecidableEq (Σ i, α i)] (s : Finset ι) (t : 对任意 i, Finset (α i))
  证明: by
  ext ⟨x, y⟩
  simp [and_left_comm]

Depends on / 依赖: and_left_comm
-/
theorem sigma_eq_biUnion [DecidableEq (Σ i, α i)] (s : Finset ι) (t : forall i, Finset (α i)) :
s.sigma t = s.biUnion fun i => (t i).map Embedding.sigmaMk i := by
  ext ⟨x, y⟩
  simp [and_left_comm]

/--
lemma `filter_sigma` / 引理 `filter_sigma`

English:
lemma filter_sigma
  statement: (s : Finset ι) (t : forall i, Finset (α i)) (p : (i : ι) × α i -> Prop)
  proof: by
  ext ⟨i, a⟩
  simp [Finset.mem_filter, Finset.mem_sigma, and_assoc]

中文:
引理 filter_sigma
  结论: (s : Finset ι) (t : 对任意 i, Finset (α i)) (p : (i : ι) × α i -> 命题)
  证明: by
  ext ⟨i, a⟩
  simp [Finset.mem_filter, Finset.mem_sigma, and_assoc]

Depends on / 依赖: Finset, Finset.mem_filter, Finset.mem_sigma, and_assoc, mem_filter, mem_sigma
-/
lemma filter_sigma (s : Finset ι) (t : forall i, Finset (α i)) (p : (i : ι) × α i -> Prop)
    [DecidablePred p] : (s.sigma t).filter p = s.sigma fun i => (t i).filter fun x => p ⟨i, x⟩ := by
  ext ⟨i, a⟩
  simp [Finset.mem_filter, Finset.mem_sigma, and_assoc]

/--
lemma `filter_sigma'` / 引理 `filter_sigma'`

English:
lemma filter_sigma'
  statement: (s : Finset ι) (t : forall i, Finset (α i)) (p : (i : ι) -> α i -> Prop)
  proof: by
  simp [filter_sigma]

中文:
引理 filter_sigma'
  结论: (s : Finset ι) (t : 对任意 i, Finset (α i)) (p : (i : ι) -> α i -> 命题)
  证明: by
  simp [filter_sigma]

Depends on / 依赖: filter_sigma
-/
lemma filter_sigma' (s : Finset ι) (t : forall i, Finset (α i)) (p : (i : ι) -> α i -> Prop)
    [forall i, DecidablePred (p i)] :
    (s.sigma t).filter (fun x => p x.fst x.snd) = s.sigma fun i => (t i).filter (p i) := by
  simp [filter_sigma]

variable (s t) (f : (Σ i, α i) -> β)

/--
theorem `sup_sigma` / 定理 `sup_sigma`

English:
theorem sup_sigma
  given: [SemilatticeSup β] [OrderBot β]
  proof: by
  simp only [le_antisymm_iff, Finset.sup_le_iff, mem_sigma, and_imp, Sigma.forall]
  exact
⟨fun i a hi ha => (le_sup hi).trans' le_sup (f := fun a => f ⟨i, a⟩) ha, fun i hi a ha =>
le_sup mem_sigma.2 ⟨hi, ha⟩⟩

中文:
定理 sup_sigma
  条件: [SemilatticeSup β] [OrderBot β]
  证明: by
  simp only [le_antisymm_iff, Finset.sup_le_iff, mem_sigma, and_imp, Sigma.forall]
  exact
⟨fun i a hi ha => (le_sup hi).trans' le_sup (f := fun a => f ⟨i, a⟩) ha, fun i hi a ha =>
le_sup mem_sigma.2 ⟨hi, ha⟩⟩

Depends on / 依赖: Finset, Finset.sup_le_iff, Sigma.forall, and_imp, le_antisymm_iff, le_sup, mem_sigma, sup_le_iff
-/
theorem sup_sigma [SemilatticeSup β] [OrderBot β] :
    (s.sigma t).sup f = s.sup fun i => (t i).sup fun b => f ⟨i, b⟩ := by
  simp only [le_antisymm_iff, Finset.sup_le_iff, mem_sigma, and_imp, Sigma.forall]
  exact
⟨fun i a hi ha => (le_sup hi).trans' le_sup (f := fun a => f ⟨i, a⟩) ha, fun i hi a ha =>
le_sup mem_sigma.2 ⟨hi, ha⟩⟩

/--
theorem `inf_sigma` / 定理 `inf_sigma`

English:
theorem inf_sigma
  given: [SemilatticeInf β] [OrderTop β]
  proof: @sup_sigma _ _ βᵒᵈ _ _ _ _ _

中文:
定理 inf_sigma
  条件: [SemilatticeInf β] [OrderTop β]
  证明: @sup_sigma _ _ βᵒᵈ _ _ _ _ _

Depends on / 依赖: sup_sigma
-/
theorem inf_sigma [SemilatticeInf β] [OrderTop β] :
    (s.sigma t).inf f = s.inf fun i => (t i).inf fun b => f ⟨i, b⟩ :=
  @sup_sigma _ _ βᵒᵈ _ _ _ _ _

/--
theorem `_root_.biSup_finsetSigma` / 定理 `_root_.biSup_finsetSigma`

English:
theorem _root_.biSup_finsetSigma
  statement: [CompleteLattice β] (s : Finset ι) (t : forall i, Finset (α i))
  proof: by
  simp_rw [← Finset.iSup_coe, Finset.coe_sigma, biSup_sigma]

中文:
定理 _root_.biSup_finsetSigma
  结论: [CompleteLattice β] (s : Finset ι) (t : 对任意 i, Finset (α i))
  证明: by
  simp_rw [← Finset.iSup_coe, Finset.coe_sigma, biSup_sigma]

Depends on / 依赖: Finset, Finset.coe_sigma, Finset.iSup_coe, biSup_sigma, coe_sigma, iSup_coe, simp_rw
-/
theorem _root_.biSup_finsetSigma [CompleteLattice β] (s : Finset ι) (t : forall i, Finset (α i))
    (f : Sigma α -> β) : ⨆ ij in s.sigma t, f ij = ⨆ (i in s) (j in t i), f ⟨i, j⟩ := by
  simp_rw [← Finset.iSup_coe, Finset.coe_sigma, biSup_sigma]

/--
theorem `_root_.biSup_finsetSigma'` / 定理 `_root_.biSup_finsetSigma'`

English:
theorem _root_.biSup_finsetSigma'
  statement: [CompleteLattice β] (s : Finset ι) (t : forall i, Finset (α i))
  proof: Eq.symm (biSup_finsetSigma _ _ _)

中文:
定理 _root_.biSup_finsetSigma'
  结论: [CompleteLattice β] (s : Finset ι) (t : 对任意 i, Finset (α i))
  证明: Eq.symm (biSup_finsetSigma _ _ _)

Depends on / 依赖: Eq.symm, biSup_finsetSigma
-/
theorem _root_.biSup_finsetSigma' [CompleteLattice β] (s : Finset ι) (t : forall i, Finset (α i))
    (f : forall i, α i -> β) : ⨆ (i in s) (j in t i), f i j = ⨆ ij in s.sigma t, f ij.fst ij.snd :=
  Eq.symm (biSup_finsetSigma _ _ _)

/--
theorem `_root_.biInf_finsetSigma` / 定理 `_root_.biInf_finsetSigma`

English:
theorem _root_.biInf_finsetSigma
  statement: [CompleteLattice β] (s : Finset ι) (t : forall i, Finset (α i))
  proof: biSup_finsetSigma (β := βᵒᵈ) _ _ _

中文:
定理 _root_.biInf_finsetSigma
  结论: [CompleteLattice β] (s : Finset ι) (t : 对任意 i, Finset (α i))
  证明: biSup_finsetSigma (β := βᵒᵈ) _ _ _

Depends on / 依赖: biSup_finsetSigma
-/
theorem _root_.biInf_finsetSigma [CompleteLattice β] (s : Finset ι) (t : forall i, Finset (α i))
    (f : Sigma α -> β) : ⨅ ij in s.sigma t, f ij = ⨅ (i in s) (j in t i), f ⟨i, j⟩ :=
  biSup_finsetSigma (β := βᵒᵈ) _ _ _

/--
theorem `_root_.biInf_finsetSigma'` / 定理 `_root_.biInf_finsetSigma'`

English:
theorem _root_.biInf_finsetSigma'
  statement: [CompleteLattice β] (s : Finset ι) (t : forall i, Finset (α i))
  proof: Eq.symm (biInf_finsetSigma _ _ _)

中文:
定理 _root_.biInf_finsetSigma'
  结论: [CompleteLattice β] (s : Finset ι) (t : 对任意 i, Finset (α i))
  证明: Eq.symm (biInf_finsetSigma _ _ _)

Depends on / 依赖: Eq.symm, biInf_finsetSigma
-/
theorem _root_.biInf_finsetSigma' [CompleteLattice β] (s : Finset ι) (t : forall i, Finset (α i))
    (f : forall i, α i -> β) : ⨅ (i in s) (j in t i), f i j = ⨅ ij in s.sigma t, f ij.fst ij.snd :=
  Eq.symm (biInf_finsetSigma _ _ _)

/--
theorem `_root_.Set.biUnion_finsetSigma` / 定理 `_root_.Set.biUnion_finsetSigma`

English:
theorem _root_.Set.biUnion_finsetSigma
  statement: (s : Finset ι) (t : forall i, Finset (α i))
  proof: biSup_finsetSigma _ _ _

中文:
定理 _root_.Set.biUnion_finsetSigma
  结论: (s : Finset ι) (t : 对任意 i, Finset (α i))
  证明: biSup_finsetSigma _ _ _

Depends on / 依赖: biSup_finsetSigma
-/
theorem _root_.Set.biUnion_finsetSigma (s : Finset ι) (t : forall i, Finset (α i))
    (f : Sigma α -> Set β) : ⋃ ij in s.sigma t, f ij = ⋃ i in s, ⋃ j in t i, f ⟨i, j⟩ :=
  biSup_finsetSigma _ _ _

/--
theorem `_root_.Set.biUnion_finsetSigma'` / 定理 `_root_.Set.biUnion_finsetSigma'`

English:
theorem _root_.Set.biUnion_finsetSigma'
  statement: (s : Finset ι) (t : forall i, Finset (α i))
  proof: biSup_finsetSigma' _ _ _

中文:
定理 _root_.Set.biUnion_finsetSigma'
  结论: (s : Finset ι) (t : 对任意 i, Finset (α i))
  证明: biSup_finsetSigma' _ _ _

Depends on / 依赖: biSup_finsetSigma
-/
theorem _root_.Set.biUnion_finsetSigma' (s : Finset ι) (t : forall i, Finset (α i))
    (f : forall i, α i -> Set β) : ⋃ i in s, ⋃ j in t i, f i j = ⋃ ij in s.sigma t, f ij.fst ij.snd :=
  biSup_finsetSigma' _ _ _

/--
theorem `_root_.Set.biInter_finsetSigma` / 定理 `_root_.Set.biInter_finsetSigma`

English:
theorem _root_.Set.biInter_finsetSigma
  statement: (s : Finset ι) (t : forall i, Finset (α i))
  proof: biInf_finsetSigma _ _ _

中文:
定理 _root_.Set.biInter_finsetSigma
  结论: (s : Finset ι) (t : 对任意 i, Finset (α i))
  证明: biInf_finsetSigma _ _ _

Depends on / 依赖: biInf_finsetSigma
-/
theorem _root_.Set.biInter_finsetSigma (s : Finset ι) (t : forall i, Finset (α i))
    (f : Sigma α -> Set β) : ⋂ ij in s.sigma t, f ij = ⋂ i in s, ⋂ j in t i, f ⟨i, j⟩ :=
  biInf_finsetSigma _ _ _

/--
theorem `_root_.Set.biInter_finsetSigma'` / 定理 `_root_.Set.biInter_finsetSigma'`

English:
theorem _root_.Set.biInter_finsetSigma'
  statement: (s : Finset ι) (t : forall i, Finset (α i))
  proof: biInf_finsetSigma' _ _ _

中文:
定理 _root_.Set.biInter_finsetSigma'
  结论: (s : Finset ι) (t : 对任意 i, Finset (α i))
  证明: biInf_finsetSigma' _ _ _

Depends on / 依赖: biInf_finsetSigma
-/
theorem _root_.Set.biInter_finsetSigma' (s : Finset ι) (t : forall i, Finset (α i))
    (f : forall i, α i -> Set β) : ⋂ i in s, ⋂ j in t i, f i j = ⋂ ij in s.sigma t, f ij.1 ij.2 :=
  biInf_finsetSigma' _ _ _

end Sigma

section SigmaLift

variable {α β γ : ι -> Type*} [DecidableEq ι]

/--
Definition of `sigmaLift` / `sigmaLift` 的定义

English:
definition sigmaLift
  signature: (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) (a : Sigma α) (b : Sigma β)
  body: dite (a.1 = b.1) (fun h => (f (h ▸ a.2) b.2).map <| Embedding.sigmaMk _) fun _ => ∅

中文:
定义 sigmaLift
  签名: (f : 对任意 ⦃i⦄, α i -> β i -> Finset (γ i)) (a : Sigma α) (b : Sigma β)
  定义体: dite (a.1 = b.1) (fun h => (f (h ▸ a.2) b.2).map <| Embedding.sigmaMk _) fun _ => ∅

Depends on / 依赖: Embedding, Embedding.sigmaMk, sigmaMk
-/
def sigmaLift (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) (a : Sigma α) (b : Sigma β) :
    Finset (Sigma γ) :=
  dite (a.1 = b.1) (fun h => (f (h ▸ a.2) b.2).map <| Embedding.sigmaMk _) fun _ => ∅

/--
theorem `mem_sigmaLift` / 定理 `mem_sigmaLift`

English:
theorem mem_sigmaLift
  statement: (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) (a : Sigma α) (b : Sigma β)
  proof: by
  obtain ⟨⟨i, a⟩, j, b⟩ := a, b
  obtain rfl | h := Decidable.eq_or_ne i j
  · constructor
    · simp_rw [sigmaLift]
      simp only [dite_eq_ite, ite_true, mem_map, Embedding.sigmaMk_apply, forall_exists_index,
        and_imp]
      rintro x hx rfl
      exact ⟨rfl, rfl, hx⟩
    · rintro ⟨⟨⟩, ⟨

中文:
定理 mem_sigmaLift
  结论: (f : 对任意 ⦃i⦄, α i -> β i -> Finset (γ i)) (a : Sigma α) (b : Sigma β)
  证明: by
  obtain ⟨⟨i, a⟩, j, b⟩ := a, b
  obtain rfl | h := Decidable.eq_or_ne i j
  · constructor
    · simp_rw [sigmaLift]
      simp only [dite_eq_ite, ite_true, mem_map, Embedding.sigmaMk_apply, forall_exists_index,
        and_imp]
      rintro x hx rfl
      exact ⟨rfl, rfl, hx⟩
    · rintro ⟨⟨⟩, ⟨

Depends on / 依赖: Decidable, Decidable.eq_or_ne, Embedding, Embedding.sigmaMk_apply, and_imp, dif_neg, dif_pos, dite_eq_ite, eq_or_ne, forall_exists_index, iff_of_false, ite_true, mem_map, notMem_empty, sigmaLift, sigmaMk_apply, simp_rw
-/
theorem mem_sigmaLift (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) (a : Sigma α) (b : Sigma β)
    (x : Sigma γ) :
    x in sigmaLift f a b ↔ exists (ha : a.1 = x.1) (hb : b.1 = x.1), x.2 in f (ha ▸ a.2) (hb ▸ b.2) := by
  obtain ⟨⟨i, a⟩, j, b⟩ := a, b
  obtain rfl | h := Decidable.eq_or_ne i j
  · constructor
    · simp_rw [sigmaLift]
      simp only [dite_eq_ite, ite_true, mem_map, Embedding.sigmaMk_apply, forall_exists_index,
        and_imp]
      rintro x hx rfl
      exact ⟨rfl, rfl, hx⟩
    · rintro ⟨⟨⟩, ⟨⟩, hx⟩
      rw [sigmaLift]; rw [dif_pos rfl]; rw [mem_map]
      exact ⟨_, hx, by simp⟩
  · rw [sigmaLift, dif_neg h]
    refine iff_of_false (notMem_empty _) ?_
    rintro ⟨⟨⟩, ⟨⟩, _⟩
    exact h rfl

/--
theorem `mk_mem_sigmaLift` / 定理 `mk_mem_sigmaLift`

English:
theorem mk_mem_sigmaLift
  statement: (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) (i : ι) (a : α i) (b : β i)
  proof: by
  rw [sigmaLift]; rw [dif_pos rfl]; rw [mem_map]
  refine ⟨?_, fun hx => ⟨_, hx, rfl⟩⟩
  rintro ⟨x, hx, _, rfl⟩
  exact hx

中文:
定理 mk_mem_sigmaLift
  结论: (f : 对任意 ⦃i⦄, α i -> β i -> Finset (γ i)) (i : ι) (a : α i) (b : β i)
  证明: by
  rw [sigmaLift]; rw [dif_pos rfl]; rw [mem_map]
  refine ⟨?_, fun hx => ⟨_, hx, rfl⟩⟩
  rintro ⟨x, hx, _, rfl⟩
  exact hx

Depends on / 依赖: dif_pos, mem_map, sigmaLift
-/
theorem mk_mem_sigmaLift (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) (i : ι) (a : α i) (b : β i)
    (x : γ i) : (⟨i, x⟩ : Sigma γ) in sigmaLift f ⟨i, a⟩ ⟨i, b⟩ ↔ x in f a b := by
  rw [sigmaLift]; rw [dif_pos rfl]; rw [mem_map]
  refine ⟨?_, fun hx => ⟨_, hx, rfl⟩⟩
  rintro ⟨x, hx, _, rfl⟩
  exact hx

/--
theorem `notMem_sigmaLift_of_ne_left` / 定理 `notMem_sigmaLift_of_ne_left`

English:
theorem notMem_sigmaLift_of_ne_left
  statement: (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) (a : Sigma α)
  proof: by
  rw [mem_sigmaLift]
  exact fun H => h H.fst

中文:
定理 notMem_sigmaLift_of_ne_left
  结论: (f : 对任意 ⦃i⦄, α i -> β i -> Finset (γ i)) (a : Sigma α)
  证明: by
  rw [mem_sigmaLift]
  exact fun H => h H.fst

Depends on / 依赖: H.fst, mem_sigmaLift
-/
theorem notMem_sigmaLift_of_ne_left (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) (a : Sigma α)
    (b : Sigma β) (x : Sigma γ) (h : a.1 != x.1) : x ∉ sigmaLift f a b := by
  rw [mem_sigmaLift]
  exact fun H => h H.fst

/--
theorem `notMem_sigmaLift_of_ne_right` / 定理 `notMem_sigmaLift_of_ne_right`

English:
theorem notMem_sigmaLift_of_ne_right
  statement: (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) {a : Sigma α}
  proof: by
  rw [mem_sigmaLift]
  exact fun H => h H.snd.fst

中文:
定理 notMem_sigmaLift_of_ne_right
  结论: (f : 对任意 ⦃i⦄, α i -> β i -> Finset (γ i)) {a : Sigma α}
  证明: by
  rw [mem_sigmaLift]
  exact fun H => h H.snd.fst

Depends on / 依赖: H.snd.fst, mem_sigmaLift
-/
theorem notMem_sigmaLift_of_ne_right (f : forall ⦃i⦄, α i -> β i -> Finset (γ i)) {a : Sigma α}
    (b : Sigma β) {x : Sigma γ} (h : b.1 != x.1) : x ∉ sigmaLift f a b := by
  rw [mem_sigmaLift]
  exact fun H => h H.snd.fst

variable {f g : forall ⦃i⦄, α i -> β i -> Finset (γ i)} {a : Σ i, α i} {b : Σ i, β i}

/--
theorem `sigmaLift_nonempty` / 定理 `sigmaLift_nonempty`

English:
theorem sigmaLift_nonempty
  proof: by
  simp_rw [nonempty_iff_ne_empty, sigmaLift]
  split_ifs with h <;> simp [h]

中文:
定理 sigmaLift_nonempty
  证明: by
  simp_rw [nonempty_iff_ne_empty, sigmaLift]
  split_ifs with h <;> simp [h]

Depends on / 依赖: nonempty_iff_ne_empty, sigmaLift, simp_rw, split_ifs
-/
theorem sigmaLift_nonempty :
    (sigmaLift f a b).Nonempty ↔ exists h : a.1 = b.1, (f (h ▸ a.2) b.2).Nonempty := by
  simp_rw [nonempty_iff_ne_empty, sigmaLift]
  split_ifs with h <;> simp [h]

/--
theorem `sigmaLift_eq_empty` / 定理 `sigmaLift_eq_empty`

English:
theorem sigmaLift_eq_empty
  statement: sigmaLift f a b = ∅ ↔ forall h : a.1 = b.1, f (h ▸ a.2) b.2 = ∅
  proof: by
  simp_rw [sigmaLift]
  split_ifs with h
  · simp [h]
  · simp [h]

中文:
定理 sigmaLift_eq_empty
  结论: sigmaLift f a b = ∅ ↔ 对任意 h : a.1 = b.1, f (h ▸ a.2) b.2 = ∅
  证明: by
  simp_rw [sigmaLift]
  split_ifs with h
  · simp [h]
  · simp [h]

Depends on / 依赖: sigmaLift, simp_rw, split_ifs
-/
theorem sigmaLift_eq_empty : sigmaLift f a b = ∅ ↔ forall h : a.1 = b.1, f (h ▸ a.2) b.2 = ∅ := by
  simp_rw [sigmaLift]
  split_ifs with h
  · simp [h]
  · simp [h]

/--
theorem `sigmaLift_mono` / 定理 `sigmaLift_mono`

English:
theorem sigmaLift_mono
  proof: by
  rintro x hx
  rw [mem_sigmaLift] at hx ⊢
  obtain ⟨ha, hb, hx⟩ := hx
  exact ⟨ha, hb, h hx⟩

中文:
定理 sigmaLift_mono
  证明: by
  rintro x hx
  rw [mem_sigmaLift] at hx ⊢
  obtain ⟨ha, hb, hx⟩ := hx
  exact ⟨ha, hb, h hx⟩

Depends on / 依赖: mem_sigmaLift
-/
theorem sigmaLift_mono
    (h : forall ⦃i⦄ ⦃a : α i⦄ ⦃b : β i⦄, f a b subseteq g a b) (a : Σ i, α i) (b : Σ i, β i) :
    sigmaLift f a b subseteq sigmaLift g a b := by
  rintro x hx
  rw [mem_sigmaLift] at hx ⊢
  obtain ⟨ha, hb, hx⟩ := hx
  exact ⟨ha, hb, h hx⟩

variable (f a b)

/--
theorem `card_sigmaLift` / 定理 `card_sigmaLift`

English:
theorem card_sigmaLift
  proof: by
  simp_rw [sigmaLift]
  split_ifs with h <;> simp

中文:
定理 card_sigmaLift
  证明: by
  simp_rw [sigmaLift]
  split_ifs with h <;> simp

Depends on / 依赖: sigmaLift, simp_rw, split_ifs
-/
theorem card_sigmaLift :
    (sigmaLift f a b).card = dite (a.1 = b.1) (fun h => (f (h ▸ a.2) b.2).card) fun _ => 0 := by
  simp_rw [sigmaLift]
  split_ifs with h <;> simp

end SigmaLift

end Finset
