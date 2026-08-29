/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.Topology.Perfect
public import Mathlib.Tactic.Peel

/-!
# Derived set

This file defines the derived set of a set, the set of all `AccPt`s of its principal filter,
and proves some properties of it.

-/

@[expose] public section

open Filter Topology

variable {X : Type*} [TopologicalSpace X]

/--
theorem `AccPt.map` / 定理 `AccPt.map`

English:
theorem AccPt.map
  statement: {β : Type*} [TopologicalSpace β] {F : Filter X} {x : X}
  proof: by
.mono apply map_neBot (m := f) (hf := h)
  rw [Filter.map_inf hf2]
  gcongr
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hf1.continuousWithinAt
  simpa [hf2.eq_iff] using! eventually_mem_nhdsWithin

中文:
定理 聚点.map
  结论: {β : 类型} [拓扑空间 β] {F : 滤子 X} {x : X}
  证明: by
.mono apply map_neBot (m := f) (hf := h)
  rw [Filter.map_inf hf2]
  gcongr
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hf1.continuousWithinAt
  simpa [hf2.eq_iff] using! eventually_mem_nhdsWithin

Depends on / 依赖: Filter, Filter.map_inf, continuousWithinAt, eq_iff, eventually_mem_nhdsWithin, hf1.continuousWithinAt, hf2.eq_iff, map_inf, map_neBot, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
-/
theorem AccPt.map {β : Type*} [TopologicalSpace β] {F : Filter X} {x : X}
    (h : AccPt x F) {f : X -> β} (hf1 : ContinuousAt f x) (hf2 : Function.Injective f) :
    AccPt (f x) (map f F) := by
.mono apply map_neBot (m := f) (hf := h)
  rw [Filter.map_inf hf2]
  gcongr
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hf1.continuousWithinAt
  simpa [hf2.eq_iff] using! eventually_mem_nhdsWithin

/--
Definition of `derivedSet` / `derivedSet` 的定义

English:
definition derivedSet
  signature: (A : Set X)
  body: {x | AccPt x (𝓟 A)}

@[simp]

中文:
定义 derivedSet
  签名: (A : 集合 X)
  定义体: {x | AccPt x (𝓟 A)}

@[simp]
-/
def derivedSet (A : Set X) : Set X := {x | AccPt x (𝓟 A)}

@[simp]
/--
lemma `mem_derivedSet` / 引理 `mem_derivedSet`

English:
lemma mem_derivedSet
  given: {A : Set X} {x : X}
  statement: x in derivedSet A ↔ AccPt x (𝓟 A)
  proof: Iff.rfl

中文:
引理 mem_derivedSet
  条件: {A : 集合 X} {x : X}
  结论: x in derivedSet A ↔ 聚点 x (𝓟 A)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_derivedSet {A : Set X} {x : X} : x in derivedSet A ↔ AccPt x (𝓟 A) := Iff.rfl

/--
lemma `derivedSet_union` / 引理 `derivedSet_union`

English:
lemma derivedSet_union
  given: (A B : Set X)
  statement: derivedSet (A union B) = derivedSet A union derivedSet B
  proof: by
  ext x
  simp [derivedSet, ← sup_principal, accPt_sup]

中文:
引理 derivedSet_union
  条件: (A B : 集合 X)
  结论: derivedSet (A union B) = derivedSet A union derivedSet B
  证明: by
  ext x
  simp [derivedSet, ← sup_principal, accPt_sup]

Depends on / 依赖: accPt_sup, derivedSet, sup_principal
-/
lemma derivedSet_union (A B : Set X) : derivedSet (A union B) = derivedSet A union derivedSet B := by
  ext x
  simp [derivedSet, ← sup_principal, accPt_sup]

/--
lemma `derivedSet_mono` / 引理 `derivedSet_mono`

English:
lemma derivedSet_mono
  given: (A B : Set X) (h : A subseteq B)
  statement: derivedSet A subseteq derivedSet B
  proof: fun _ hx => hx.mono le_principal_iff.mpr mem_principal.mpr h

中文:
引理 derivedSet_mono
  条件: (A B : 集合 X) (h : A subseteq B)
  结论: derivedSet A subseteq derivedSet B
  证明: fun _ hx => hx.mono le_principal_iff.mpr mem_principal.mpr h

Depends on / 依赖: hx.mono, le_principal_iff, le_principal_iff.mpr, mem_principal, mem_principal.mpr
-/
lemma derivedSet_mono (A B : Set X) (h : A subseteq B) : derivedSet A subseteq derivedSet B :=
fun _ hx => hx.mono le_principal_iff.mpr mem_principal.mpr h

/--
Definition of `relDerivedSet` / `relDerivedSet` 的定义

English:
definition relDerivedSet
  signature: : Set X ->o Set X where
  body: derivedSet s inter s
  monotone' s t h := Set.inter_subset_inter (derivedSet_mono s t h) h

中文:
定义 relDerivedSet
  签名: : 集合 X ->o 集合 X where
  定义体: derivedSet s inter s
  monotone' s t h := Set.inter_subset_inter (derivedSet_mono s t h) h

Depends on / 依赖: derivedSet
-/
def relDerivedSet : Set X ->o Set X where
  toFun s := derivedSet s inter s
  monotone' s t h := Set.inter_subset_inter (derivedSet_mono s t h) h

/--
lemma `relDerivedSet_apply` / 引理 `relDerivedSet_apply`

English:
lemma relDerivedSet_apply
  given: (A : Set X)
  statement: relDerivedSet A = derivedSet A inter A
  proof: rfl

中文:
引理 relDerivedSet_apply
  条件: (A : 集合 X)
  结论: relDerivedSet A = derivedSet A inter A
  证明: rfl
-/
@[simp] lemma relDerivedSet_apply (A : Set X) : relDerivedSet A = derivedSet A inter A := rfl

/--
lemma `relDerivedSet_subset` / 引理 `relDerivedSet_subset`

English:
lemma relDerivedSet_subset
  given: {A : Set X}
  statement: relDerivedSet A subseteq A
  proof: Set.inter_subset_right

中文:
引理 relDerivedSet_subset
  条件: {A : 集合 X}
  结论: relDerivedSet A subseteq A
  证明: Set.inter_subset_right

Depends on / 依赖: Set.inter_subset_right, inter_subset_right
-/
lemma relDerivedSet_subset {A : Set X} : relDerivedSet A subseteq A :=
  Set.inter_subset_right

/--
theorem `Continuous.image_derivedSet` / 定理 `Continuous.image_derivedSet`

English:
theorem Continuous.image_derivedSet
  statement: {β : Type*} [TopologicalSpace β] {A : Set X} {f : X -> β}
  proof: by
  intro x hx
  simp only [Set.mem_image, mem_derivedSet] at hx
  obtain ⟨y, hy1, rfl⟩ := hx
  convert! hy1.map hf1.continuousAt hf2
  simp

中文:
定理 连续.image_derivedSet
  结论: {β : 类型} [拓扑空间 β] {A : 集合 X} {f : X -> β}
  证明: by
  intro x hx
  simp only [Set.mem_image, mem_derivedSet] at hx
  obtain ⟨y, hy1, rfl⟩ := hx
  convert! hy1.map hf1.continuousAt hf2
  simp

Depends on / 依赖: Set.mem_image, continuousAt, convert, hf1.continuousAt, hy1.map, mem_derivedSet, mem_image
-/
theorem Continuous.image_derivedSet {β : Type*} [TopologicalSpace β] {A : Set X} {f : X -> β}
    (hf1 : Continuous f) (hf2 : Function.Injective f) :
    f '' derivedSet A subseteq derivedSet (f '' A) := by
  intro x hx
  simp only [Set.mem_image, mem_derivedSet] at hx
  obtain ⟨y, hy1, rfl⟩ := hx
  convert! hy1.map hf1.continuousAt hf2
  simp

/--
lemma `derivedSet_subset_closure` / 引理 `derivedSet_subset_closure`

English:
lemma derivedSet_subset_closure
  given: (A : Set X)
  statement: derivedSet A subseteq closure A
  proof: fun _ hx => mem_closure_iff_clusterPt.mpr hx.clusterPt

中文:
引理 derivedSet_subset_closure
  条件: (A : 集合 X)
  结论: derivedSet A subseteq closure A
  证明: fun _ hx => mem_closure_iff_clusterPt.mpr hx.clusterPt

Depends on / 依赖: clusterPt, hx.clusterPt, mem_closure_iff_clusterPt, mem_closure_iff_clusterPt.mpr
-/
lemma derivedSet_subset_closure (A : Set X) : derivedSet A subseteq closure A :=
  fun _ hx => mem_closure_iff_clusterPt.mpr hx.clusterPt

/--
lemma `isClosed_iff_derivedSet_subset` / 引理 `isClosed_iff_derivedSet_subset`

English:
lemma isClosed_iff_derivedSet_subset
  given: (A : Set X)
  statement: IsClosed A ↔ derivedSet A subseteq A where
  proof: derivedSet_subset_closure A
  mpr h := by
    rw [isClosed_iff_clusterPt]
    intro a ha
    by_contra! nh
    have : A = A \ {a} := by simp [nh]
    rw [this]; rw [← accPt_principal_iff_clusterPt] at ha
    exact nh (h ha)

中文:
引理 isClosed_iff_derivedSet_subset
  条件: (A : 集合 X)
  结论: 是闭集 A ↔ derivedSet A subseteq A where
  证明: derivedSet_subset_closure A
  mpr h := by
    rw [isClosed_iff_clusterPt]
    intro a ha
    by_contra! nh
    have : A = A \ {a} := by simp [nh]
    rw [this]; rw [← accPt_principal_iff_clusterPt] at ha
    exact nh (h ha)

Depends on / 依赖: derivedSet_subset_closure
-/
lemma isClosed_iff_derivedSet_subset (A : Set X) : IsClosed A ↔ derivedSet A subseteq A where
.trans h.closure_subset mp h := derivedSet_subset_closure A
  mpr h := by
    rw [isClosed_iff_clusterPt]
    intro a ha
    by_contra! nh
    have : A = A \ {a} := by simp [nh]
    rw [this]; rw [← accPt_principal_iff_clusterPt] at ha
    exact nh (h ha)

/--
lemma `IsClosed.relDerivedSet_eq` / 引理 `IsClosed.relDerivedSet_eq`

English:
lemma IsClosed.relDerivedSet_eq
  given: {A : Set X} (hA : IsClosed A)
  proof: by
  simpa using (isClosed_iff_derivedSet_subset A).mp hA

中文:
引理 是闭集.relDerivedSet_eq
  条件: {A : 集合 X} (hA : 是闭集 A)
  证明: by
  simpa using (isClosed_iff_derivedSet_subset A).mp hA

Depends on / 依赖: isClosed_iff_derivedSet_subset
-/
lemma IsClosed.relDerivedSet_eq {A : Set X} (hA : IsClosed A) :
    relDerivedSet A = derivedSet A := by
  simpa using (isClosed_iff_derivedSet_subset A).mp hA

/--
lemma `closure_eq_self_union_derivedSet` / 引理 `closure_eq_self_union_derivedSet`

English:
lemma closure_eq_self_union_derivedSet
  given: (A : Set X)
  statement: closure A = A union derivedSet A
  proof: by
  ext
  simp [closure_eq_cluster_pts, clusterPt_principal]

中文:
引理 closure_eq_self_union_derivedSet
  条件: (A : 集合 X)
  结论: closure A = A union derivedSet A
  证明: by
  ext
  simp [closure_eq_cluster_pts, clusterPt_principal]

Depends on / 依赖: closure_eq_cluster_pts, clusterPt_principal
-/
lemma closure_eq_self_union_derivedSet (A : Set X) : closure A = A union derivedSet A := by
  ext
  simp [closure_eq_cluster_pts, clusterPt_principal]

/--
lemma `derivedSet_closure` / 引理 `derivedSet_closure`

English:
lemma derivedSet_closure
  given: [T1Space X] (A : Set X)
  statement: derivedSet (closure A) = derivedSet A
  proof: by
  refine le_antisymm (fun x hx => ?_) (derivedSet_mono _ _ subset_closure)
  rw [mem_derivedSet]; rw [AccPt]; rw [(nhdsWithin_basis_open x {x}ᶜ).inf_principal_neBot_iff] at hx ⊢
  peel hx with u hu _
  obtain ⟨-, hu_open⟩ := hu
  exact mem_closure_iff.mp this.some_mem.2 (u inter {x}ᶜ) (hu_open.in

中文:
引理 derivedSet_closure
  条件: [T1空间 X] (A : 集合 X)
  结论: derivedSet (closure A) = derivedSet A
  证明: by
  refine le_antisymm (fun x hx => ?_) (derivedSet_mono _ _ subset_closure)
  rw [mem_derivedSet]; rw [AccPt]; rw [(nhdsWithin_basis_open x {x}ᶜ).inf_principal_neBot_iff] at hx ⊢
  peel hx with u hu _
  obtain ⟨-, hu_open⟩ := hu
  exact mem_closure_iff.mp this.some_mem.2 (u inter {x}ᶜ) (hu_open.in

Depends on / 依赖: derivedSet_mono, hu_open, hu_open.inter, inf_principal_neBot_iff, isOpen_compl_singleton, le_antisymm, mem_closure_iff, mem_closure_iff.mp, mem_derivedSet, nhdsWithin_basis_open, some_mem, subset_closure, this.some_mem
-/
lemma derivedSet_closure [T1Space X] (A : Set X) : derivedSet (closure A) = derivedSet A := by
  refine le_antisymm (fun x hx => ?_) (derivedSet_mono _ _ subset_closure)
  rw [mem_derivedSet]; rw [AccPt]; rw [(nhdsWithin_basis_open x {x}ᶜ).inf_principal_neBot_iff] at hx ⊢
  peel hx with u hu _
  obtain ⟨-, hu_open⟩ := hu
  exact mem_closure_iff.mp this.some_mem.2 (u inter {x}ᶜ) (hu_open.inter isOpen_compl_singleton)
    this.some_mem.1

@[simp]
/--
lemma `isClosed_derivedSet` / 引理 `isClosed_derivedSet`

English:
lemma isClosed_derivedSet
  given: [T1Space X] (A : Set X)
  statement: IsClosed (derivedSet A)
  proof: by
  rw [← derivedSet_closure]; rw [isClosed_iff_derivedSet_subset]
  apply derivedSet_mono
  simp [← isClosed_iff_derivedSet_subset]

中文:
引理 isClosed_derivedSet
  条件: [T1空间 X] (A : 集合 X)
  结论: 是闭集 (derivedSet A)
  证明: by
  rw [← derivedSet_closure]; rw [isClosed_iff_derivedSet_subset]
  apply derivedSet_mono
  simp [← isClosed_iff_derivedSet_subset]

Depends on / 依赖: derivedSet_closure, derivedSet_mono, isClosed_iff_derivedSet_subset
-/
lemma isClosed_derivedSet [T1Space X] (A : Set X) : IsClosed (derivedSet A) := by
  rw [← derivedSet_closure]; rw [isClosed_iff_derivedSet_subset]
  apply derivedSet_mono
  simp [← isClosed_iff_derivedSet_subset]

/--
lemma `preperfect_iff_subset_derivedSet` / 引理 `preperfect_iff_subset_derivedSet`

English:
lemma preperfect_iff_subset_derivedSet
  given: {U : Set X}
  statement: Preperfect U ↔ U subseteq derivedSet U
  proof: Iff.rfl

中文:
引理 preperfect_iff_subset_derivedSet
  条件: {U : 集合 X}
  结论: Preperfect U ↔ U subseteq derivedSet U
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma preperfect_iff_subset_derivedSet {U : Set X} : Preperfect U ↔ U subseteq derivedSet U :=
  Iff.rfl

/--
lemma `preperfect_iff_eq_relDerivedSet` / 引理 `preperfect_iff_eq_relDerivedSet`

English:
lemma preperfect_iff_eq_relDerivedSet
  given: {U : Set X}
  statement: Preperfect U ↔ U = relDerivedSet U
  proof: by
  simp [preperfect_iff_subset_derivedSet]

中文:
引理 preperfect_iff_eq_relDerivedSet
  条件: {U : 集合 X}
  结论: Preperfect U ↔ U = relDerivedSet U
  证明: by
  simp [preperfect_iff_subset_derivedSet]

Depends on / 依赖: preperfect_iff_subset_derivedSet
-/
lemma preperfect_iff_eq_relDerivedSet {U : Set X} : Preperfect U ↔ U = relDerivedSet U := by
  simp [preperfect_iff_subset_derivedSet]

/--
lemma `perfect_iff_eq_derivedSet` / 引理 `perfect_iff_eq_derivedSet`

English:
lemma perfect_iff_eq_derivedSet
  given: {U : Set X}
  statement: Perfect U ↔ U = derivedSet U
  proof: by
  rw [perfect_def]; rw [isClosed_iff_derivedSet_subset]; rw [preperfect_iff_subset_derivedSet]; rw [← subset_antisymm_iff]; rw [eq_comm]

中文:
引理 perfect_iff_eq_derivedSet
  条件: {U : 集合 X}
  结论: 完美 U ↔ U = derivedSet U
  证明: by
  rw [perfect_def]; rw [isClosed_iff_derivedSet_subset]; rw [preperfect_iff_subset_derivedSet]; rw [← subset_antisymm_iff]; rw [eq_comm]

Depends on / 依赖: eq_comm, isClosed_iff_derivedSet_subset, perfect_def, preperfect_iff_subset_derivedSet, subset_antisymm_iff
-/
lemma perfect_iff_eq_derivedSet {U : Set X} : Perfect U ↔ U = derivedSet U := by
  rw [perfect_def]; rw [isClosed_iff_derivedSet_subset]; rw [preperfect_iff_subset_derivedSet]; rw [← subset_antisymm_iff]; rw [eq_comm]

/--
lemma `IsPreconnected.inter_derivedSet_nonempty` / 引理 `IsPreconnected.inter_derivedSet_nonempty`

English:
lemma IsPreconnected.inter_derivedSet_nonempty
  statement: [T1Space X] {U : Set X} (hs : IsPreconnected U)
  proof: by
  by_cases hu : U.Nontrivial
  · apply isPreconnected_closed_iff.mp hs
    · simp
    · simp
    · trans derivedSet U
      · apply hs.preperfect_of_nontrivial hu
      · rw [← derivedSet_union]
        exact derivedSet_mono _ _ h
    · exact ha
    · exact hb
  · obtain ⟨x, hx⟩ := ha.left.exists

中文:
引理 是预连通.inter_derivedSet_nonempty
  结论: [T1空间 X] {U : 集合 X} (hs : 是预连通 U)
  证明: by
  by_cases hu : U.Nontrivial
  · apply isPreconnected_closed_iff.mp hs
    · simp
    · simp
    · trans derivedSet U
      · apply hs.preperfect_of_nontrivial hu
      · rw [← derivedSet_union]
        exact derivedSet_mono _ _ h
    · exact ha
    · exact hb
  · obtain ⟨x, hx⟩ := ha.left.exists

Depends on / 依赖: Nontrivial, U.Nontrivial, derivedSet, derivedSet_mono, derivedSet_union, exists_eq_singleton_or_nontrivial, ha.left.exists_eq_singleton_or_nontrivial.resolve_right, hs.preperfect_of_nontrivial, isPreconnected_closed_iff, isPreconnected_closed_iff.mp, preperfect_of_nontrivial, resolve_right
-/
lemma IsPreconnected.inter_derivedSet_nonempty [T1Space X] {U : Set X} (hs : IsPreconnected U)
    (a b : Set X) (h : U subseteq a union b) (ha : (U inter derivedSet a).Nonempty)
    (hb : (U inter derivedSet b).Nonempty) : (U inter (derivedSet a inter derivedSet b)).Nonempty := by
  by_cases hu : U.Nontrivial
  · apply isPreconnected_closed_iff.mp hs
    · simp
    · simp
    · trans derivedSet U
      · apply hs.preperfect_of_nontrivial hu
      · rw [← derivedSet_union]
        exact derivedSet_mono _ _ h
    · exact ha
    · exact hb
  · obtain ⟨x, hx⟩ := ha.left.exists_eq_singleton_or_nontrivial.resolve_right hu
    simp_all
