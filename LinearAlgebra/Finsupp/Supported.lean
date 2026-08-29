/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# `Finsupp`s supported on a given submodule

* `Finsupp.restrictDom`: `Finsupp.filter` as a linear map to `Finsupp.supported s`;
  `Finsupp.supported R R s` and codomain `Submodule.span R (v '' s)`;
* `Finsupp.supportedEquivFinsupp`: a linear equivalence between the functions `α →₀ M` supported
  on `s` and the functions `s →₀ M`;
* `Finsupp.domLCongr`: a `LinearEquiv` version of `Finsupp.domCongr`;
* `Finsupp.congr`: if the sets `s` and `t` are equivalent, then `supported M R s` is equivalent to
  `supported M R t`;

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

variable (M R)

/--
Definition of `supported` / `supported` 的定义

English:
definition supported
  signature: (s : Set α)
  body: { p | ↑p.support subseteq s }
  add_mem' {p q} hp hq := by
    classical
    refine Subset.trans (Subset.trans (Finset.coe_subset.2 support_add) ?_) (union_subset hp hq)
    rw [Finset.coe_union]
  zero_mem' := by
    simp only [subset_def, Finset.mem_coe, Set.mem_ofPred_eq, mem_support_iff, zero_ap

中文:
定义 supported
  签名: (s : Set α)
  定义体: { p | ↑p.support subseteq s }
  add_mem' {p q} hp hq := by
    classical
    refine Subset.trans (Subset.trans (Finset.coe_subset.2 support_add) ?_) (union_subset hp hq)
    rw [Finset.coe_union]
  zero_mem' := by
    simp only [subset_def, Finset.mem_coe, Set.mem_ofPred_eq, mem_support_iff, zero_ap

Depends on / 依赖: p.support, subseteq, support
-/
def supported (s : Set α) : Submodule R (α ->₀ M) where
  carrier := { p | ↑p.support subseteq s }
  add_mem' {p q} hp hq := by
    classical
    refine Subset.trans (Subset.trans (Finset.coe_subset.2 support_add) ?_) (union_subset hp hq)
    rw [Finset.coe_union]
  zero_mem' := by
    simp only [subset_def, Finset.mem_coe, Set.mem_ofPred_eq, mem_support_iff, zero_apply]
    intro h ha
    exact (ha rfl).elim
  smul_mem' _ _ hp := Subset.trans (Finset.coe_subset.2 support_smul) hp

variable {M}

/--
theorem `mem_supported` / 定理 `mem_supported`

English:
theorem mem_supported
  given: {s : Set α} (p : α ->₀ M)
  statement: p in supported M R s ↔ ↑p.support subseteq s
  proof: Iff.rfl

中文:
定理 mem_supported
  条件: {s : Set α} (p : α ->₀ M)
  结论: p in supported M R s ↔ ↑p.support subseteq s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_supported {s : Set α} (p : α ->₀ M) : p in supported M R s ↔ ↑p.support subseteq s :=
  Iff.rfl

/--
theorem `mem_supported'` / 定理 `mem_supported'`

English:
theorem mem_supported'
  given: {s : Set α} (p : α ->₀ M)
  proof: by
  simp [mem_supported, Set.subset_def, not_imp_comm]

中文:
定理 mem_supported'
  条件: {s : Set α} (p : α ->₀ M)
  证明: by
  simp [mem_supported, Set.subset_def, not_imp_comm]

Depends on / 依赖: Set.subset_def, mem_supported, not_imp_comm, subset_def
-/
theorem mem_supported' {s : Set α} (p : α ->₀ M) :
    p in supported M R s ↔ forall x ∉ s, p x = 0 := by
  simp [mem_supported, Set.subset_def, not_imp_comm]

/--
theorem `mem_supported_support` / 定理 `mem_supported_support`

English:
theorem mem_supported_support
  given: (p : α ->₀ M)
  statement: p in Finsupp.supported M R (p.support : Set α)
  proof: by
  rw [Finsupp.mem_supported]

中文:
定理 mem_supported_support
  条件: (p : α ->₀ M)
  结论: p in Finsupp.supported M R (p.support : Set α)
  证明: by
  rw [Finsupp.mem_supported]

Depends on / 依赖: Finsupp, Finsupp.mem_supported, mem_supported
-/
theorem mem_supported_support (p : α ->₀ M) : p in Finsupp.supported M R (p.support : Set α) := by
  rw [Finsupp.mem_supported]

/--
theorem `single_mem_supported` / 定理 `single_mem_supported`

English:
theorem single_mem_supported
  given: {s : Set α} {a : α} (b : M) (h : a in s)
  proof: Set.Subset.trans support_single_subset (Finset.singleton_subset_set_iff.2 h)

中文:
定理 single_mem_supported
  条件: {s : Set α} {a : α} (b : M) (h : a in s)
  证明: Set.Subset.trans support_single_subset (Finset.singleton_subset_set_iff.2 h)

Depends on / 依赖: Finset, Finset.singleton_subset_set_iff, Set.Subset.trans, Subset, singleton_subset_set_iff, support_single_subset
-/
theorem single_mem_supported {s : Set α} {a : α} (b : M) (h : a in s) :
    single a b in supported M R s :=
  Set.Subset.trans support_single_subset (Finset.singleton_subset_set_iff.2 h)

/--
theorem `supported_eq_span_single` / 定理 `supported_eq_span_single`

English:
theorem supported_eq_span_single
  given: (s : Set α)
  proof: by
  refine (span_eq_of_le _ ?_ (SetLike.le_def.2 fun l hl => ?_)).symm
  · rintro _ ⟨_, hp, rfl⟩
    exact single_mem_supported R 1 hp
  · rw [← l.sum_single]
    refine sum_mem fun i il => ?_
    rw [show single i (l i) = l i • single i 1 by simp]
    exact smul_mem _ (l i) (subset_span (mem_image

中文:
定理 supported_eq_span_single
  条件: (s : Set α)
  证明: by
  refine (span_eq_of_le _ ?_ (SetLike.le_def.2 fun l hl => ?_)).symm
  · rintro _ ⟨_, hp, rfl⟩
    exact single_mem_supported R 1 hp
  · rw [← l.sum_single]
    refine sum_mem fun i il => ?_
    rw [show single i (l i) = l i • single i 1 by simp]
    exact smul_mem _ (l i) (subset_span (mem_image

Depends on / 依赖: SetLike, SetLike.le_def, l.sum_single, le_def, mem_image_of_mem, single, single_mem_supported, smul_mem, span_eq_of_le, subset_span, sum_mem, sum_single
-/
theorem supported_eq_span_single (s : Set α) :
    supported R R s = span R ((fun i => single i 1) '' s) := by
  refine (span_eq_of_le _ ?_ (SetLike.le_def.2 fun l hl => ?_)).symm
  · rintro _ ⟨_, hp, rfl⟩
    exact single_mem_supported R 1 hp
  · rw [← l.sum_single]
    refine sum_mem fun i il => ?_
    rw [show single i (l i) = l i • single i 1 by simp]
    exact smul_mem _ (l i) (subset_span (mem_image_of_mem _ (hl il)))

/--
lemma `single_mem_span_single` / 引理 `single_mem_span_single`

English:
lemma single_mem_span_single
  given: [Nontrivial R] {a : α} {s : Set α}
  proof: by
refine ⟨fun h => ?_, fun h => Submodule.subset_span Set.mem_image_of_mem _ h⟩
  rw [← Finsupp.supported_eq_span_single]; rw [Finsupp.mem_supported]; rw [Finsupp.support_single _ (one_ne_zero' R)] at h
  simpa using h

中文:
引理 single_mem_span_single
  条件: [Nontrivial R] {a : α} {s : Set α}
  证明: by
refine ⟨fun h => ?_, fun h => Submodule.subset_span Set.mem_image_of_mem _ h⟩
  rw [← Finsupp.supported_eq_span_single]; rw [Finsupp.mem_supported]; rw [Finsupp.support_single _ (one_ne_zero' R)] at h
  simpa using h

Depends on / 依赖: Finsupp, Finsupp.mem_supported, Finsupp.support_single, Finsupp.supported_eq_span_single, Set.mem_image_of_mem, Submodule, Submodule.subset_span, mem_image_of_mem, mem_supported, one_ne_zero, subset_span, support_single, supported_eq_span_single
-/
lemma single_mem_span_single [Nontrivial R] {a : α} {s : Set α} :
    single a 1 in Submodule.span R ((single · (1 : R)) '' s) ↔ a in s := by
refine ⟨fun h => ?_, fun h => Submodule.subset_span Set.mem_image_of_mem _ h⟩
  rw [← Finsupp.supported_eq_span_single]; rw [Finsupp.mem_supported]; rw [Finsupp.support_single _ (one_ne_zero' R)] at h
  simpa using h

/--
theorem `span_le_supported_biUnion_support` / 定理 `span_le_supported_biUnion_support`

English:
theorem span_le_supported_biUnion_support
  given: (s : Set (α ->₀ M))
  proof: span_le.mpr fun _ h => subset_biUnion_of_mem h (u := (SetLike.coe ·.support))

中文:
定理 span_le_supported_biUnion_support
  条件: (s : Set (α ->₀ M))
  证明: span_le.mpr fun _ h => subset_biUnion_of_mem h (u := (SetLike.coe ·.support))

Depends on / 依赖: SetLike, SetLike.coe, span_le, span_le.mpr, subset_biUnion_of_mem, support
-/
theorem span_le_supported_biUnion_support (s : Set (α ->₀ M)) :
    span R s <= supported M R (⋃ x in s, x.support) :=
  span_le.mpr fun _ h => subset_biUnion_of_mem h (u := (SetLike.coe ·.support))

variable (M)

/--
Definition of `restrictDom` / `restrictDom` 的定义

English:
definition restrictDom
  signature: (s : Set α) [DecidablePred (· in s)]
  body: LinearMap.codRestrict _
    { toFun := filter (· in s)
      map_add' := fun _ _ => filter_add
      map_smul' := fun _ _ => filter_smul } fun l =>
    (mem_supported' _ _).2 fun _ => filter_apply_neg (· in s) l

中文:
定义 restrictDom
  签名: (s : Set α) [DecidablePred (· in s)]
  定义体: LinearMap.codRestrict _
    { toFun := filter (· in s)
      map_add' := fun _ _ => filter_add
      map_smul' := fun _ _ => filter_smul } fun l =>
    (mem_supported' _ _).2 fun _ => filter_apply_neg (· in s) l

Depends on / 依赖: LinearMap, LinearMap.codRestrict, codRestrict, filter, filter_add, filter_apply_neg, filter_smul, map_add, map_smul, mem_supported
-/
def restrictDom (s : Set α) [DecidablePred (· in s)] : (α ->₀ M) ->ₗ[R] supported M R s :=
  LinearMap.codRestrict _
    { toFun := filter (· in s)
      map_add' := fun _ _ => filter_add
      map_smul' := fun _ _ => filter_smul } fun l =>
    (mem_supported' _ _).2 fun _ => filter_apply_neg (· in s) l

variable {M R}

section

@[simp]
/--
theorem `restrictDom_apply` / 定理 `restrictDom_apply`

English:
theorem restrictDom_apply
  given: (s : Set α) (l : α ->₀ M) [DecidablePred (· in s)]
  proof: rfl

中文:
定理 restrictDom_apply
  条件: (s : Set α) (l : α ->₀ M) [DecidablePred (· in s)]
  证明: rfl
-/
theorem restrictDom_apply (s : Set α) (l : α ->₀ M) [DecidablePred (· in s)] :
    (restrictDom M R s l : α ->₀ M) = Finsupp.filter (· in s) l := rfl

end

/--
theorem `restrictDom_comp_subtype` / 定理 `restrictDom_comp_subtype`

English:
theorem restrictDom_comp_subtype
  given: (s : Set α) [DecidablePred (· in s)]
  proof: by
  ext l a
  by_cases h : a in s
  · simp [h]
  simpa [h] using ((mem_supported' R l.1).1 l.2 a h).symm

中文:
定理 restrictDom_comp_subtype
  条件: (s : Set α) [DecidablePred (· in s)]
  证明: by
  ext l a
  by_cases h : a in s
  · simp [h]
  simpa [h] using ((mem_supported' R l.1).1 l.2 a h).symm

Depends on / 依赖: mem_supported
-/
theorem restrictDom_comp_subtype (s : Set α) [DecidablePred (· in s)] :
    (restrictDom M R s).comp (Submodule.subtype _) = LinearMap.id := by
  ext l a
  by_cases h : a in s
  · simp [h]
  simpa [h] using ((mem_supported' R l.1).1 l.2 a h).symm

/--
theorem `range_restrictDom` / 定理 `range_restrictDom`

English:
theorem range_restrictDom
  given: (s : Set α) [DecidablePred (· in s)]
  proof: range_eq_top.2
Function.RightInverse.surjective LinearMap.congr_fun (restrictDom_comp_subtype s)

中文:
定理 range_restrictDom
  条件: (s : Set α) [DecidablePred (· in s)]
  证明: range_eq_top.2
Function.RightInverse.surjective LinearMap.congr_fun (restrictDom_comp_subtype s)

Depends on / 依赖: Function, Function.RightInverse.surjective, LinearMap, LinearMap.congr_fun, RightInverse, congr_fun, range_eq_top, restrictDom_comp_subtype, surjective
-/
theorem range_restrictDom (s : Set α) [DecidablePred (· in s)] :
    LinearMap.range (restrictDom M R s) = ⊤ :=
range_eq_top.2
Function.RightInverse.surjective LinearMap.congr_fun (restrictDom_comp_subtype s)

/--
theorem `supported_mono` / 定理 `supported_mono`

English:
theorem supported_mono
  given: {s t : Set α} (st : s subseteq t)
  statement: supported M R s <= supported M R t
  proof: fun _ h =>
  Set.Subset.trans h st

@[simp]

中文:
定理 supported_mono
  条件: {s t : Set α} (st : s subseteq t)
  结论: supported M R s <= supported M R t
  证明: fun _ h =>
  Set.Subset.trans h st

@[simp]
-/
theorem supported_mono {s t : Set α} (st : s subseteq t) : supported M R s <= supported M R t := fun _ h =>
  Set.Subset.trans h st

@[simp]
/--
theorem `supported_empty` / 定理 `supported_empty`

English:
theorem supported_empty
  statement: supported M R (∅ : Set α) = ⊥
  proof: eq_bot_iff.2 fun l h => (Submodule.mem_bot R).2 by ext; simp_all [mem_supported']

@[simp]

中文:
定理 supported_empty
  结论: supported M R (∅ : Set α) = ⊥
  证明: eq_bot_iff.2 fun l h => (Submodule.mem_bot R).2 by ext; simp_all [mem_supported']

@[simp]

Depends on / 依赖: Submodule, Submodule.mem_bot, eq_bot_iff, mem_bot, mem_supported
-/
theorem supported_empty : supported M R (∅ : Set α) = ⊥ :=
eq_bot_iff.2 fun l h => (Submodule.mem_bot R).2 by ext; simp_all [mem_supported']

@[simp]
/--
theorem `supported_univ` / 定理 `supported_univ`

English:
theorem supported_univ
  statement: supported M R (Set.univ : Set α) = ⊤
  proof: eq_top_iff.2 fun _ _ => Set.subset_univ _

中文:
定理 supported_univ
  结论: supported M R (Set.univ : Set α) = ⊤
  证明: eq_top_iff.2 fun _ _ => Set.subset_univ _

Depends on / 依赖: Set.subset_univ, eq_top_iff, subset_univ
-/
theorem supported_univ : supported M R (Set.univ : Set α) = ⊤ :=
  eq_top_iff.2 fun _ _ => Set.subset_univ _

/--
theorem `supported_iUnion` / 定理 `supported_iUnion`

English:
theorem supported_iUnion
  given: {δ : Type*} (s : δ -> Set α)
  proof: by
  refine le_antisymm ?_ (iSup_le fun i => supported_mono <| Set.subset_iUnion _ _)
  have := Classical.decPred fun x => x in ⋃ i, s i
  suffices
    LinearMap.range ((Submodule.subtype _).comp (restrictDom M R (⋃ i, s i))) <=
      ⨆ i, supported M R (s i) by
    rwa [LinearMap.range_comp, range_

中文:
定理 supported_iUnion
  条件: {δ : 类型} (s : δ -> Set α)
  证明: by
  refine le_antisymm ?_ (iSup_le fun i => supported_mono <| Set.subset_iUnion _ _)
  have := Classical.decPred fun x => x in ⋃ i, s i
  suffices
    LinearMap.range ((Submodule.subtype _).comp (restrictDom M R (⋃ i, s i))) <=
      ⨆ i, supported M R (s i) by
    rwa [LinearMap.range_comp, range_

Depends on / 依赖: Classical, Classical.decPred, Finsupp, Finsupp.induction, LinearMap, LinearMap.range, LinearMap.range_comp, Set.subset_iUnion, Submodule, Submodule.map_top, Submodule.subtype, add_mem, decPred, eq_top_iff, iSup_le, le_antisymm, map_top, range_comp, range_le_iff_comap, range_restrictDom
-/
theorem supported_iUnion {δ : Type*} (s : δ -> Set α) :
    supported M R (⋃ i, s i) = ⨆ i, supported M R (s i) := by
  refine le_antisymm ?_ (iSup_le fun i => supported_mono <| Set.subset_iUnion _ _)
  have := Classical.decPred fun x => x in ⋃ i, s i
  suffices
    LinearMap.range ((Submodule.subtype _).comp (restrictDom M R (⋃ i, s i))) <=
      ⨆ i, supported M R (s i) by
    rwa [LinearMap.range_comp, range_restrictDom, Submodule.map_top, range_subtype] at this
  rw [range_le_iff_comap]; rw [eq_top_iff]
  rintro l ⟨⟩
  induction l using Finsupp.induction with
  | zero => exact zero_mem _
  | single_add x a l _ _ ih =>
    refine add_mem ?_ ih
    by_cases h : exists i, x in s i
    · simp only [mem_comap, coe_comp, coe_subtype, Function.comp_apply, restrictDom_apply,
        mem_iUnion, h, filter_single_of_pos]
      obtain ⟨i, hi⟩ := h
      exact le_iSup (fun i => supported M R (s i)) i (single_mem_supported R _ hi)
    · simp [h]

/--
theorem `supported_union` / 定理 `supported_union`

English:
theorem supported_union
  given: (s t : Set α)
  proof: by
  rw [Set.union_eq_iUnion]; rw [supported_iUnion]; rw [iSup_bool_eq]; rw [cond_true]; rw [cond_false]

中文:
定理 supported_union
  条件: (s t : Set α)
  证明: by
  rw [Set.union_eq_iUnion]; rw [supported_iUnion]; rw [iSup_bool_eq]; rw [cond_true]; rw [cond_false]

Depends on / 依赖: Set.union_eq_iUnion, cond_false, cond_true, iSup_bool_eq, supported_iUnion, union_eq_iUnion
-/
theorem supported_union (s t : Set α) :
    supported M R (s union t) = supported M R s ⊔ supported M R t := by
  rw [Set.union_eq_iUnion]; rw [supported_iUnion]; rw [iSup_bool_eq]; rw [cond_true]; rw [cond_false]

/--
theorem `supported_iInter` / 定理 `supported_iInter`

English:
theorem supported_iInter
  given: {ι : Type*} (s : ι -> Set α)
  proof: Submodule.ext fun x => by simp [mem_supported, subset_iInter_iff]

中文:
定理 supported_iInter
  条件: {ι : 类型} (s : ι -> Set α)
  证明: Submodule.ext fun x => by simp [mem_supported, subset_iInter_iff]

Depends on / 依赖: Submodule, Submodule.ext, mem_supported, subset_iInter_iff
-/
theorem supported_iInter {ι : Type*} (s : ι -> Set α) :
    supported M R (⋂ i, s i) = ⨅ i, supported M R (s i) :=
  Submodule.ext fun x => by simp [mem_supported, subset_iInter_iff]

/--
theorem `supported_inter` / 定理 `supported_inter`

English:
theorem supported_inter
  given: (s t : Set α)
  proof: by
  rw [Set.inter_eq_iInter]; rw [supported_iInter]; rw [iInf_bool_eq]; rfl

中文:
定理 supported_inter
  条件: (s t : Set α)
  证明: by
  rw [Set.inter_eq_iInter]; rw [supported_iInter]; rw [iInf_bool_eq]; rfl

Depends on / 依赖: Set.inter_eq_iInter, iInf_bool_eq, inter_eq_iInter, supported_iInter
-/
theorem supported_inter (s t : Set α) :
    supported M R (s inter t) = supported M R s ⊓ supported M R t := by
  rw [Set.inter_eq_iInter]; rw [supported_iInter]; rw [iInf_bool_eq]; rfl

/--
theorem `disjoint_supported_supported` / 定理 `disjoint_supported_supported`

English:
theorem disjoint_supported_supported
  given: {s t : Set α} (h : Disjoint s t)
  proof: disjoint_iff.2 by rw [← supported_inter, disjoint_iff_inter_eq_empty.1 h, supported_empty]

中文:
定理 disjoint_supported_supported
  条件: {s t : Set α} (h : Disjoint s t)
  证明: disjoint_iff.2 by rw [← supported_inter, disjoint_iff_inter_eq_empty.1 h, supported_empty]

Depends on / 依赖: disjoint_iff, disjoint_iff_inter_eq_empty, supported_empty, supported_inter
-/
theorem disjoint_supported_supported {s t : Set α} (h : Disjoint s t) :
    Disjoint (supported M R s) (supported M R t) :=
disjoint_iff.2 by rw [← supported_inter, disjoint_iff_inter_eq_empty.1 h, supported_empty]

/--
theorem `disjoint_supported_supported_iff` / 定理 `disjoint_supported_supported_iff`

English:
theorem disjoint_supported_supported_iff
  given: [Nontrivial M] {s t : Set α}
  proof: by
  refine ⟨fun h => Set.disjoint_left.mpr fun x hx1 hx2 => ?_, disjoint_supported_supported⟩
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  have := h.le_bot ⟨single_mem_supported R y hx1, single_mem_supported R y hx2⟩
  rw [mem_bot]; rw [single_eq_zero] at this
  exact hy this

中文:
定理 disjoint_supported_supported_iff
  条件: [Nontrivial M] {s t : Set α}
  证明: by
  refine ⟨fun h => Set.disjoint_left.mpr fun x hx1 hx2 => ?_, disjoint_supported_supported⟩
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  have := h.le_bot ⟨single_mem_supported R y hx1, single_mem_supported R y hx2⟩
  rw [mem_bot]; rw [single_eq_zero] at this
  exact hy this

Depends on / 依赖: Set.disjoint_left.mpr, disjoint_left, disjoint_supported_supported, exists_ne, h.le_bot, le_bot, mem_bot, single_eq_zero, single_mem_supported
-/
theorem disjoint_supported_supported_iff [Nontrivial M] {s t : Set α} :
    Disjoint (supported M R s) (supported M R t) ↔ Disjoint s t := by
  refine ⟨fun h => Set.disjoint_left.mpr fun x hx1 hx2 => ?_, disjoint_supported_supported⟩
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  have := h.le_bot ⟨single_mem_supported R y hx1, single_mem_supported R y hx2⟩
  rw [mem_bot]; rw [single_eq_zero] at this
  exact hy this

/--
lemma `codisjoint_supported_supported` / 引理 `codisjoint_supported_supported`

English:
lemma codisjoint_supported_supported
  given: {s t : Set α} (h : Codisjoint s t)
  proof: by
  rw [codisjoint_iff]; rw [eq_top_iff]; rw [← supported_union]; rw [show s union t = .univ from codisjoint_iff.mp h]; rw [supported_univ]

中文:
引理 codisjoint_supported_supported
  条件: {s t : Set α} (h : Codisjoint s t)
  证明: by
  rw [codisjoint_iff]; rw [eq_top_iff]; rw [← supported_union]; rw [show s union t = .univ from codisjoint_iff.mp h]; rw [supported_univ]

Depends on / 依赖: codisjoint_iff, codisjoint_iff.mp, eq_top_iff, supported_union, supported_univ
-/
lemma codisjoint_supported_supported {s t : Set α} (h : Codisjoint s t) :
    Codisjoint (supported M R s) (supported M R t) := by
  rw [codisjoint_iff]; rw [eq_top_iff]; rw [← supported_union]; rw [show s union t = .univ from codisjoint_iff.mp h]; rw [supported_univ]

/--
lemma `codisjoint_supported_supported_iff` / 引理 `codisjoint_supported_supported_iff`

English:
lemma codisjoint_supported_supported_iff
  given: [Nontrivial M] {s t : Set α}
  proof: by
  refine ⟨fun h => codisjoint_iff.mpr (eq_top_iff.mpr fun a => ?_), codisjoint_supported_supported⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  rw [codisjoint_iff]; rw [← supported_union]; rw [eq_top_iff'] at h
  simpa [Finsupp.mem_supported, Finsupp.support_single _ hx] using h (Finsupp.single a x)


中文:
引理 codisjoint_supported_supported_iff
  条件: [Nontrivial M] {s t : Set α}
  证明: by
  refine ⟨fun h => codisjoint_iff.mpr (eq_top_iff.mpr fun a => ?_), codisjoint_supported_supported⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  rw [codisjoint_iff]; rw [← supported_union]; rw [eq_top_iff'] at h
  simpa [Finsupp.mem_supported, Finsupp.support_single _ hx] using h (Finsupp.single a x)


Depends on / 依赖: Finsupp, Finsupp.mem_supported, Finsupp.single, Finsupp.support_single, codisjoint_iff, codisjoint_iff.mpr, codisjoint_supported_supported, eq_top_iff, eq_top_iff.mpr, exists_ne, mem_supported, single, support_single, supported_union
-/
lemma codisjoint_supported_supported_iff [Nontrivial M] {s t : Set α} :
    Codisjoint (supported M R s) (supported M R t) ↔ Codisjoint s t := by
  refine ⟨fun h => codisjoint_iff.mpr (eq_top_iff.mpr fun a => ?_), codisjoint_supported_supported⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  rw [codisjoint_iff]; rw [← supported_union]; rw [eq_top_iff'] at h
  simpa [Finsupp.mem_supported, Finsupp.support_single _ hx] using h (Finsupp.single a x)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `supportedEquivFinsupp` / `supportedEquivFinsupp` 的定义

English:
definition supportedEquivFinsupp
  signature: (s : Set α)
  body: by
  let F : supported M R s ≃ (s ->₀ M) := restrictSupportEquiv s M
  refine F.toLinearEquiv ?_
  have :
    (F : supported M R s -> ↥s ->₀ M) =
      (lsubtypeDomain s : (α ->₀ M) ->ₗ[R] s ->₀ M).comp (Submodule.subtype (supported M R s)) :=
    rfl
  rw [this]
  exact LinearMap.isLinear _

中文:
定义 supportedEquivFinsupp
  签名: (s : Set α)
  定义体: by
  let F : supported M R s ≃ (s ->₀ M) := restrictSupportEquiv s M
  refine F.toLinearEquiv ?_
  have :
    (F : supported M R s -> ↥s ->₀ M) =
      (lsubtypeDomain s : (α ->₀ M) ->ₗ[R] s ->₀ M).comp (Submodule.subtype (supported M R s)) :=
    rfl
  rw [this]
  exact LinearMap.isLinear _
-/
@[simps!] def supportedEquivFinsupp (s : Set α) : supported M R s ≃ₗ[R] s ->₀ M := by
  let F : supported M R s ≃ (s ->₀ M) := restrictSupportEquiv s M
  refine F.toLinearEquiv ?_
  have :
    (F : supported M R s -> ↥s ->₀ M) =
      (lsubtypeDomain s : (α ->₀ M) ->ₗ[R] s ->₀ M).comp (Submodule.subtype (supported M R s)) :=
    rfl
  rw [this]
  exact LinearMap.isLinear _

/--
theorem `supportedEquivFinsupp_symm_apply_coe` / 定理 `supportedEquivFinsupp_symm_apply_coe`

English:
theorem supportedEquivFinsupp_symm_apply_coe
  statement: (s : Set α) [DecidablePred (· in s)]
  proof: by
  convert! restrictSupportEquiv_symm_apply_coe ..

中文:
定理 supportedEquivFinsupp_symm_apply_coe
  结论: (s : Set α) [DecidablePred (· in s)]
  证明: by
  convert! restrictSupportEquiv_symm_apply_coe ..
-/
@[simp] theorem supportedEquivFinsupp_symm_apply_coe (s : Set α) [DecidablePred (· in s)]
    (f : s ->₀ M) : (supportedEquivFinsupp (R := R) s).symm f = f.extendDomain := by
  convert! restrictSupportEquiv_symm_apply_coe ..

/--
theorem `supportedEquivFinsupp_symm_single` / 定理 `supportedEquivFinsupp_symm_single`

English:
theorem supportedEquivFinsupp_symm_single
  given: (s : Set α) (i : s) (a : M)
  proof: by
  classical simp

中文:
定理 supportedEquivFinsupp_symm_single
  条件: (s : Set α) (i : s) (a : M)
  证明: by
  classical simp
-/
@[simp] theorem supportedEquivFinsupp_symm_single (s : Set α) (i : s) (a : M) :
    ((supportedEquivFinsupp (R := R) s).symm (single i a) : α ->₀ M) = single ↑i a := by
  classical simp

section LMapDomain

variable {α' : Type*} {α'' : Type*} (M R)

/--
theorem `supported_comap_lmapDomain` / 定理 `supported_comap_lmapDomain`

English:
theorem supported_comap_lmapDomain
  given: (f : α -> α') (s : Set α')
  proof: by
  classical
  intro l (hl : (l.support : Set α) subseteq f ⁻¹' s)
  change ↑(mapDomain f l).support subseteq s
  rw [← Set.image_subset_iff]; rw [← Finset.coe_image] at hl
  exact Set.Subset.trans mapDomain_support hl

中文:
定理 supported_comap_lmapDomain
  条件: (f : α -> α') (s : Set α')
  证明: by
  classical
  intro l (hl : (l.support : Set α) subseteq f ⁻¹' s)
  change ↑(mapDomain f l).support subseteq s
  rw [← Set.image_subset_iff]; rw [← Finset.coe_image] at hl
  exact Set.Subset.trans mapDomain_support hl

Depends on / 依赖: Finset, Finset.coe_image, Set.Subset.trans, Set.image_subset_iff, Subset, classical, coe_image, image_subset_iff, l.support, mapDomain, mapDomain_support, subseteq, support
-/
theorem supported_comap_lmapDomain (f : α -> α') (s : Set α') :
    supported M R (f ⁻¹' s) <= (supported M R s).comap (lmapDomain M R f) := by
  classical
  intro l (hl : (l.support : Set α) subseteq f ⁻¹' s)
  change ↑(mapDomain f l).support subseteq s
  rw [← Set.image_subset_iff]; rw [← Finset.coe_image] at hl
  exact Set.Subset.trans mapDomain_support hl

/--
theorem `lmapDomain_supported` / 定理 `lmapDomain_supported`

English:
theorem lmapDomain_supported
  given: (f : α -> α') (s : Set α)
  proof: by
  classical
  cases isEmpty_or_nonempty α
  · simp [s.eq_empty_of_isEmpty]
  refine
    le_antisymm
      (map_le_iff_le_comap.2 <|
        le_trans (supported_mono <| Set.subset_preimage_image _ _)
          (supported_comap_lmapDomain M R _ _))
      ?_
  intro l hl
  refine ⟨(lmapDomain M R (F

中文:
定理 lmapDomain_supported
  条件: (f : α -> α') (s : Set α)
  证明: by
  classical
  cases isEmpty_or_nonempty α
  · simp [s.eq_empty_of_isEmpty]
  refine
    le_antisymm
      (map_le_iff_le_comap.2 <|
        le_trans (supported_mono <| Set.subset_preimage_image _ _)
          (supported_comap_lmapDomain M R _ _))
      ?_
  intro l hl
  refine ⟨(lmapDomain M R (F

Depends on / 依赖: Finset, Finset.mem_image, Function, Function.invFunOn, Function.invFunOn_mem, LinearMap, LinearMap.comp_apply, Set.subset_preimage_image, classical, comp_apply, eq_empty_of_isEmpty, invFunOn, invFunOn_mem, isEmpty_or_nonempty, le_antisymm, le_trans, lmapDomain, lmapDomain_comp, mapDomain_support, map_le_iff_le_comap
-/
theorem lmapDomain_supported (f : α -> α') (s : Set α) :
    (supported M R s).map (lmapDomain M R f) = supported M R (f '' s) := by
  classical
  cases isEmpty_or_nonempty α
  · simp [s.eq_empty_of_isEmpty]
  refine
    le_antisymm
      (map_le_iff_le_comap.2 <|
        le_trans (supported_mono <| Set.subset_preimage_image _ _)
          (supported_comap_lmapDomain M R _ _))
      ?_
  intro l hl
  refine ⟨(lmapDomain M R (Function.invFunOn f s) : (α' ->₀ M) ->ₗ[R] α ->₀ M) l, fun x hx => ?_, ?_⟩
  · rcases Finset.mem_image.1 (mapDomain_support hx) with ⟨c, hc, rfl⟩
    exact Function.invFunOn_mem (by simpa using hl hc)
  · rw [← LinearMap.comp_apply, ← lmapDomain_comp]
    refine (mapDomain_congr fun c hc => ?_).trans mapDomain_id
    exact Function.invFunOn_eq (by simpa using hl hc)

/--
theorem `lmapDomain_disjoint_ker` / 定理 `lmapDomain_disjoint_ker`

English:
theorem lmapDomain_disjoint_ker
  statement: (f : α -> α') {s : Set α}
  proof: by
  rw [disjoint_iff_inf_le]
  rintro l ⟨h₁, h₂⟩
  rw [SetLike.mem_coe]; rw [mem_ker]; rw [lmapDomain_apply]; rw [mapDomain] at h₂
  simp only [mem_bot]; ext x
  have := Classical.decPred fun x => x in s
  by_cases xs : x in s
  · have : Finsupp.sum l (fun a => Finsupp.single (f a)) (f x) = 0 := by

中文:
定理 lmapDomain_disjoint_ker
  结论: (f : α -> α') {s : Set α}
  证明: by
  rw [disjoint_iff_inf_le]
  rintro l ⟨h₁, h₂⟩
  rw [SetLike.mem_coe]; rw [mem_ker]; rw [lmapDomain_apply]; rw [mapDomain] at h₂
  simp only [mem_bot]; ext x
  have := Classical.decPred fun x => x in s
  by_cases xs : x in s
  · have : Finsupp.sum l (fun a => Finsupp.single (f a)) (f x) = 0 := by

Depends on / 依赖: Classical, Classical.decPred, Finsupp, Finsupp.single, Finsupp.sum, Finsupp.sum_apply, Finsupp.sum_eq_single, SetLike, SetLike.mem_coe, decPred, disjoint_iff_inf_le, lmapDomain_apply, mapDomain, mem_bot, mem_coe, mem_ker, mem_support_iff, mem_supported, single, single_eq_same
-/
theorem lmapDomain_disjoint_ker (f : α -> α') {s : Set α}
    (H : forall a in s, forall b in s, f a = f b -> a = b) :
    Disjoint (supported M R s) (ker (lmapDomain M R f)) := by
  rw [disjoint_iff_inf_le]
  rintro l ⟨h₁, h₂⟩
  rw [SetLike.mem_coe]; rw [mem_ker]; rw [lmapDomain_apply]; rw [mapDomain] at h₂
  simp only [mem_bot]; ext x
  have := Classical.decPred fun x => x in s
  by_cases xs : x in s
  · have : Finsupp.sum l (fun a => Finsupp.single (f a)) (f x) = 0 := by
      rw [h₂]
      rfl
    rw [Finsupp.sum_apply]; rw [Finsupp.sum_eq_single x]; rw [single_eq_same] at this
    · simpa
    · intro y hy xy
      simp only [SetLike.mem_coe, mem_supported, subset_def, mem_support_iff] at h₁
      simp [mt (H _ (h₁ _ hy) _ xs) xy]
    · simp +contextual
  · by_contra h
    exact xs (h₁ <| Finsupp.mem_support_iff.2 h)

end LMapDomain

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: {α' : Type*} (s : Set α) (t : Set α') (e : s ≃ t)
  body: by
  haveI := Classical.decPred fun x => x in s
  haveI := Classical.decPred fun x => x in t
  exact Finsupp.supportedEquivFinsupp s ≪≫ₗ
    (Finsupp.domLCongr e ≪≫ₗ (Finsupp.supportedEquivFinsupp t).symm)

中文:
定义 congr
  签名: {α' : 类型} (s : Set α) (t : Set α') (e : s ≃ t)
  定义体: by
  haveI := Classical.decPred fun x => x in s
  haveI := Classical.decPred fun x => x in t
  exact Finsupp.supportedEquivFinsupp s ≪≫ₗ
    (Finsupp.domLCongr e ≪≫ₗ (Finsupp.supportedEquivFinsupp t).symm)

Depends on / 依赖: Classical, Classical.decPred, Finsupp, Finsupp.domLCongr, Finsupp.supportedEquivFinsupp, decPred, domLCongr, supportedEquivFinsupp
-/
noncomputable def congr {α' : Type*} (s : Set α) (t : Set α') (e : s ≃ t) :
    supported M R s ≃ₗ[R] supported M R t := by
  haveI := Classical.decPred fun x => x in s
  haveI := Classical.decPred fun x => x in t
  exact Finsupp.supportedEquivFinsupp s ≪≫ₗ
    (Finsupp.domLCongr e ≪≫ₗ (Finsupp.supportedEquivFinsupp t).symm)

end Finsupp
