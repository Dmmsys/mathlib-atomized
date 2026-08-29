/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/
module

public import Mathlib.Topology.Neighborhoods

/-!
# Neighborhoods of a set

In this file we define the filter `𝓝ˢ s` or `nhdsSet s` consisting of all neighborhoods of a set
`s`.

## Main Properties

There are a couple different notions equivalent to `s ∈ 𝓝ˢ t`:
* `s ⊆ interior t` using `subset_interior_iff_mem_nhdsSet`
* `∀ x : X, x ∈ t → s ∈ 𝓝 x` using `mem_nhdsSet_iff_forall`
* `∃ U : Set X, IsOpen U ∧ t ⊆ U ∧ U ⊆ s` using `mem_nhdsSet_iff_exists`

Furthermore, we have the following results:
* `monotone_nhdsSet`: `𝓝ˢ` is monotone
* In T₁-spaces, `𝓝ˢ` is strictly monotone and hence injective:
  `strict_mono_nhdsSet`/`injective_nhdsSet`. These results are in
  `Mathlib/Topology/Separation/Basic.lean`.
-/

public section

open Set Filter Topology

variable {α X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Filter X}
  {s t s₁ s₂ t₁ t₂ : Set X} {x : X}

/--
theorem `nhdsSet_diagonal` / 定理 `nhdsSet_diagonal`

English:
theorem nhdsSet_diagonal
  given: (X) [TopologicalSpace (X × X)]
  proof: by
  rw [nhdsSet]; rw [← range_diag]; rw [← range_comp]
  rfl

中文:
定理 nhdsSet_diagonal
  条件: (X) [拓扑空间 (X × X)]
  证明: by
  rw [nhdsSet]; rw [← range_diag]; rw [← range_comp]
  rfl

Depends on / 依赖: nhdsSet, range_comp, range_diag
-/
theorem nhdsSet_diagonal (X) [TopologicalSpace (X × X)] :
    𝓝ˢ (diagonal X) = ⨆ (x : X), 𝓝 (x, x) := by
  rw [nhdsSet]; rw [← range_diag]; rw [← range_comp]
  rfl

/--
theorem `mem_nhdsSet_iff_forall` / 定理 `mem_nhdsSet_iff_forall`

English:
theorem mem_nhdsSet_iff_forall
  statement: s in 𝓝ˢ t ↔ forall x : X, x in t -> s in 𝓝 x
  proof: by
  simp_rw [nhdsSet, Filter.mem_sSup, forall_mem_image]

中文:
定理 mem_nhdsSet_iff_对任意
  结论: s in 𝓝ˢ t ↔ 对任意 x : X, x in t -> s in 𝓝 x
  证明: by
  simp_rw [nhdsSet, Filter.mem_sSup, forall_mem_image]

Depends on / 依赖: Filter, Filter.mem_sSup, forall_mem_image, mem_sSup, nhdsSet, simp_rw
-/
theorem mem_nhdsSet_iff_forall : s in 𝓝ˢ t ↔ forall x : X, x in t -> s in 𝓝 x := by
  simp_rw [nhdsSet, Filter.mem_sSup, forall_mem_image]

/--
lemma `nhdsSet_le` / 引理 `nhdsSet_le`

English:
lemma nhdsSet_le
  statement: 𝓝ˢ s <= f ↔ forall x in s, 𝓝 x <= f
  proof: by simp [nhdsSet]

中文:
引理 nhdsSet_le
  结论: 𝓝ˢ s <= f ↔ 对任意 x in s, 𝓝 x <= f
  证明: by simp [nhdsSet]

Depends on / 依赖: nhdsSet
-/
lemma nhdsSet_le : 𝓝ˢ s <= f ↔ forall x in s, 𝓝 x <= f := by simp [nhdsSet]

/--
theorem `bUnion_mem_nhdsSet` / 定理 `bUnion_mem_nhdsSet`

English:
theorem bUnion_mem_nhdsSet
  given: {t : X -> Set X} (h : forall x in s, t x in 𝓝 x)
  statement: (⋃ x in s, t x) in 𝓝ˢ s
  proof: mem_nhdsSet_iff_forall.2 fun x hx => mem_of_superset (h x hx)
    subset_iUnion₂ (s := fun x _ => t x) x hx

中文:
定理 bUnion_mem_nhdsSet
  条件: {t : X -> 集合 X} (h : 对任意 x in s, t x in 𝓝 x)
  结论: (⋃ x in s, t x) in 𝓝ˢ s
  证明: mem_nhdsSet_iff_forall.2 fun x hx => mem_of_superset (h x hx)
    subset_iUnion₂ (s := fun x _ => t x) x hx

Depends on / 依赖: mem_nhdsSet_iff_forall, mem_of_superset
-/
theorem bUnion_mem_nhdsSet {t : X -> Set X} (h : forall x in s, t x in 𝓝 x) : (⋃ x in s, t x) in 𝓝ˢ s :=
mem_nhdsSet_iff_forall.2 fun x hx => mem_of_superset (h x hx)
    subset_iUnion₂ (s := fun x _ => t x) x hx

/--
theorem `subset_interior_iff_mem_nhdsSet` / 定理 `subset_interior_iff_mem_nhdsSet`

English:
theorem subset_interior_iff_mem_nhdsSet
  statement: s subseteq interior t ↔ t in 𝓝ˢ s
  proof: by
  simp_rw [mem_nhdsSet_iff_forall, subset_interior_iff_nhds]

中文:
定理 subset_interior_iff_mem_nhdsSet
  结论: s subseteq interior t ↔ t in 𝓝ˢ s
  证明: by
  simp_rw [mem_nhdsSet_iff_forall, subset_interior_iff_nhds]

Depends on / 依赖: mem_nhdsSet_iff_forall, simp_rw, subset_interior_iff_nhds
-/
theorem subset_interior_iff_mem_nhdsSet : s subseteq interior t ↔ t in 𝓝ˢ s := by
  simp_rw [mem_nhdsSet_iff_forall, subset_interior_iff_nhds]

/--
theorem `disjoint_principal_nhdsSet` / 定理 `disjoint_principal_nhdsSet`

English:
theorem disjoint_principal_nhdsSet
  statement: Disjoint (𝓟 s) (𝓝ˢ t) ↔ Disjoint (closure s) t
  proof: by
  rw [disjoint_principal_left]; rw [← subset_interior_iff_mem_nhdsSet]; rw [interior_compl]; rw [subset_compl_iff_disjoint_left]

中文:
定理 disjoint_principal_nhdsSet
  结论: Disjoint (𝓟 s) (𝓝ˢ t) ↔ Disjoint (closure s) t
  证明: by
  rw [disjoint_principal_left]; rw [← subset_interior_iff_mem_nhdsSet]; rw [interior_compl]; rw [subset_compl_iff_disjoint_left]

Depends on / 依赖: disjoint_principal_left, interior_compl, subset_compl_iff_disjoint_left, subset_interior_iff_mem_nhdsSet
-/
theorem disjoint_principal_nhdsSet : Disjoint (𝓟 s) (𝓝ˢ t) ↔ Disjoint (closure s) t := by
  rw [disjoint_principal_left]; rw [← subset_interior_iff_mem_nhdsSet]; rw [interior_compl]; rw [subset_compl_iff_disjoint_left]

/--
theorem `disjoint_nhdsSet_principal` / 定理 `disjoint_nhdsSet_principal`

English:
theorem disjoint_nhdsSet_principal
  statement: Disjoint (𝓝ˢ s) (𝓟 t) ↔ Disjoint s (closure t)
  proof: by
  rw [disjoint_comm]; rw [disjoint_principal_nhdsSet]; rw [disjoint_comm]

中文:
定理 disjoint_nhdsSet_principal
  结论: Disjoint (𝓝ˢ s) (𝓟 t) ↔ Disjoint s (closure t)
  证明: by
  rw [disjoint_comm]; rw [disjoint_principal_nhdsSet]; rw [disjoint_comm]

Depends on / 依赖: disjoint_comm, disjoint_principal_nhdsSet
-/
theorem disjoint_nhdsSet_principal : Disjoint (𝓝ˢ s) (𝓟 t) ↔ Disjoint s (closure t) := by
  rw [disjoint_comm]; rw [disjoint_principal_nhdsSet]; rw [disjoint_comm]

/--
theorem `mem_nhdsSet_iff_exists` / 定理 `mem_nhdsSet_iff_exists`

English:
theorem mem_nhdsSet_iff_exists
  statement: s in 𝓝ˢ t ↔ exists U : Set X, IsOpen U ∧ t subseteq U ∧ U subseteq s
  proof: by
  rw [← subset_interior_iff_mem_nhdsSet]; rw [subset_interior_iff]

中文:
定理 mem_nhdsSet_iff_存在
  结论: s in 𝓝ˢ t ↔ 存在 U : 集合 X, 是开集 U ∧ t subseteq U ∧ U subseteq s
  证明: by
  rw [← subset_interior_iff_mem_nhdsSet]; rw [subset_interior_iff]

Depends on / 依赖: subset_interior_iff, subset_interior_iff_mem_nhdsSet
-/
theorem mem_nhdsSet_iff_exists : s in 𝓝ˢ t ↔ exists U : Set X, IsOpen U ∧ t subseteq U ∧ U subseteq s := by
  rw [← subset_interior_iff_mem_nhdsSet]; rw [subset_interior_iff]

/--
theorem `eventually_nhdsSet_iff_exists` / 定理 `eventually_nhdsSet_iff_exists`

English:
theorem eventually_nhdsSet_iff_exists
  given: {p : X -> Prop}
  proof: mem_nhdsSet_iff_exists

中文:
定理 eventually_nhdsSet_iff_存在
  条件: {p : X -> 命题}
  证明: mem_nhdsSet_iff_exists

Depends on / 依赖: mem_nhdsSet_iff_exists
-/
theorem eventually_nhdsSet_iff_exists {p : X -> Prop} :
    (forallᶠ x in 𝓝ˢ s, p x) ↔ exists t, IsOpen t ∧ s subseteq t ∧ forall x, x in t -> p x :=
  mem_nhdsSet_iff_exists

/--
theorem `eventually_nhdsSet_iff_forall` / 定理 `eventually_nhdsSet_iff_forall`

English:
theorem eventually_nhdsSet_iff_forall
  given: {p : X -> Prop}
  proof: mem_nhdsSet_iff_forall

中文:
定理 eventually_nhdsSet_iff_对任意
  条件: {p : X -> 命题}
  证明: mem_nhdsSet_iff_forall

Depends on / 依赖: mem_nhdsSet_iff_forall
-/
theorem eventually_nhdsSet_iff_forall {p : X -> Prop} :
    (forallᶠ x in 𝓝ˢ s, p x) ↔ forall x, x in s -> forallᶠ y in 𝓝 x, p y :=
  mem_nhdsSet_iff_forall

/--
theorem `hasBasis_nhdsSet` / 定理 `hasBasis_nhdsSet`

English:
theorem hasBasis_nhdsSet
  given: (s : Set X)
  statement: (𝓝ˢ s).HasBasis (fun U => IsOpen U ∧ s subseteq U) fun U => U
  proof: ⟨fun t => by simp [mem_nhdsSet_iff_exists, and_assoc]⟩

@[simp]

中文:
定理 hasBasis_nhdsSet
  条件: (s : 集合 X)
  结论: (𝓝ˢ s).有基 (fun U => 是开集 U ∧ s subseteq U) fun U => U
  证明: ⟨fun t => by simp [mem_nhdsSet_iff_exists, and_assoc]⟩

@[simp]

Depends on / 依赖: and_assoc, mem_nhdsSet_iff_exists
-/
theorem hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U => IsOpen U ∧ s subseteq U) fun U => U :=
  ⟨fun t => by simp [mem_nhdsSet_iff_exists, and_assoc]⟩

@[simp]
/--
lemma `lift'_nhdsSet_interior` / 引理 `lift'_nhdsSet_interior`

English:
lemma lift'_nhdsSet_interior
  given: (s : Set X)
  statement: (𝓝ˢ s).lift' interior = 𝓝ˢ s
  proof: (hasBasis_nhdsSet s).lift'_interior_eq_self fun _ => And.left

中文:
引理 lift'_nhdsSet_interior
  条件: (s : 集合 X)
  结论: (𝓝ˢ s).lift' interior = 𝓝ˢ s
  证明: (hasBasis_nhdsSet s).lift'_interior_eq_self fun _ => And.left
-/
lemma lift'_nhdsSet_interior (s : Set X) : (𝓝ˢ s).lift' interior = 𝓝ˢ s :=
  (hasBasis_nhdsSet s).lift'_interior_eq_self fun _ => And.left

/--
lemma `Filter.HasBasis.nhdsSet_interior` / 引理 `Filter.HasBasis.nhdsSet_interior`

English:
lemma Filter.HasBasis.nhdsSet_interior
  statement: {ι : Sort*} {p : ι -> Prop} {s : ι -> Set X} {t : Set X}
  proof: lift'_nhdsSet_interior t ▸ h.lift'_interior

中文:
引理 滤子.有基.nhdsSet_interior
  结论: {ι : 类型层*} {p : ι -> 命题} {s : ι -> 集合 X} {t : 集合 X}
  证明: lift'_nhdsSet_interior t ▸ h.lift'_interior

Depends on / 依赖: _interior, _nhdsSet_interior, h.lift
-/
lemma Filter.HasBasis.nhdsSet_interior {ι : Sort*} {p : ι -> Prop} {s : ι -> Set X} {t : Set X}
    (h : (𝓝ˢ t).HasBasis p s) : (𝓝ˢ t).HasBasis p (interior <| s ·) :=
  lift'_nhdsSet_interior t ▸ h.lift'_interior

/--
theorem `IsOpen.mem_nhdsSet` / 定理 `IsOpen.mem_nhdsSet`

English:
theorem IsOpen.mem_nhdsSet
  given: (hU : IsOpen s)
  statement: s in 𝓝ˢ t ↔ t subseteq s
  proof: by
  rw [← subset_interior_iff_mem_nhdsSet]; rw [hU.interior_eq]

中文:
定理 是开集.mem_nhdsSet
  条件: (hU : 是开集 s)
  结论: s in 𝓝ˢ t ↔ t subseteq s
  证明: by
  rw [← subset_interior_iff_mem_nhdsSet]; rw [hU.interior_eq]

Depends on / 依赖: hU.interior_eq, interior_eq, subset_interior_iff_mem_nhdsSet
-/
theorem IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t subseteq s := by
  rw [← subset_interior_iff_mem_nhdsSet]; rw [hU.interior_eq]

/--
theorem `IsOpen.mem_nhdsSet_self` / 定理 `IsOpen.mem_nhdsSet_self`

English:
theorem IsOpen.mem_nhdsSet_self
  given: (ho : IsOpen s)
  statement: s in 𝓝ˢ s
  proof: ho.mem_nhdsSet.mpr Subset.rfl

中文:
定理 是开集.mem_nhdsSet_self
  条件: (ho : 是开集 s)
  结论: s in 𝓝ˢ s
  证明: ho.mem_nhdsSet.mpr Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, ho.mem_nhdsSet.mpr, mem_nhdsSet
-/
theorem IsOpen.mem_nhdsSet_self (ho : IsOpen s) : s in 𝓝ˢ s := ho.mem_nhdsSet.mpr Subset.rfl

/--
theorem `principal_le_nhdsSet` / 定理 `principal_le_nhdsSet`

English:
theorem principal_le_nhdsSet
  statement: 𝓟 s <= 𝓝ˢ s
  proof: fun _s hs =>
  (subset_interior_iff_mem_nhdsSet.mpr hs).trans interior_subset

中文:
定理 principal_le_nhdsSet
  结论: 𝓟 s <= 𝓝ˢ s
  证明: fun _s hs =>
  (subset_interior_iff_mem_nhdsSet.mpr hs).trans interior_subset
-/
theorem principal_le_nhdsSet : 𝓟 s <= 𝓝ˢ s := fun _s hs =>
  (subset_interior_iff_mem_nhdsSet.mpr hs).trans interior_subset

/--
theorem `subset_of_mem_nhdsSet` / 定理 `subset_of_mem_nhdsSet`

English:
theorem subset_of_mem_nhdsSet
  given: (h : t in 𝓝ˢ s)
  statement: s subseteq t
  proof: principal_le_nhdsSet h

中文:
定理 subset_of_mem_nhdsSet
  条件: (h : t in 𝓝ˢ s)
  结论: s subseteq t
  证明: principal_le_nhdsSet h

Depends on / 依赖: principal_le_nhdsSet
-/
theorem subset_of_mem_nhdsSet (h : t in 𝓝ˢ s) : s subseteq t := principal_le_nhdsSet h

/--
theorem `Filter.Eventually.self_of_nhdsSet` / 定理 `Filter.Eventually.self_of_nhdsSet`

English:
theorem Filter.Eventually.self_of_nhdsSet
  given: {p : X -> Prop} (h : forallᶠ x in 𝓝ˢ s, p x)
  statement: forall x in s, p x
  proof: principal_le_nhdsSet h

nonrec theorem Filter.EventuallyEq.self_of_nhdsSet {Y} {f g : X -> Y} (h : f =ᶠ[𝓝ˢ s] g) :
    EqOn f g s :=
  h.self_of_nhdsSet

@[simp]

中文:
定理 滤子.Eventually.self_of_nhdsSet
  条件: {p : X -> 命题} (h : 对任意ᶠ x in 𝓝ˢ s, p x)
  结论: 对任意 x in s, p x
  证明: principal_le_nhdsSet h

nonrec theorem Filter.EventuallyEq.self_of_nhdsSet {Y} {f g : X -> Y} (h : f =ᶠ[𝓝ˢ s] g) :
    EqOn f g s :=
  h.self_of_nhdsSet

@[simp]

Depends on / 依赖: principal_le_nhdsSet
-/
theorem Filter.Eventually.self_of_nhdsSet {p : X -> Prop} (h : forallᶠ x in 𝓝ˢ s, p x) : forall x in s, p x :=
  principal_le_nhdsSet h

nonrec theorem Filter.EventuallyEq.self_of_nhdsSet {Y} {f g : X -> Y} (h : f =ᶠ[𝓝ˢ s] g) :
    EqOn f g s :=
  h.self_of_nhdsSet

@[simp]
/--
theorem `nhdsSet_eq_principal_iff` / 定理 `nhdsSet_eq_principal_iff`

English:
theorem nhdsSet_eq_principal_iff
  statement: 𝓝ˢ s = 𝓟 s ↔ IsOpen s
  proof: by
  rw [← principal_le_nhdsSet.ge_iff_eq']; rw [le_principal_iff]; rw [mem_nhdsSet_iff_forall]; rw [isOpen_iff_mem_nhds]

alias ⟨_, IsOpen.nhdsSet_eq⟩ := nhdsSet_eq_principal_iff

@[simp]

中文:
定理 nhdsSet_eq_principal_iff
  结论: 𝓝ˢ s = 𝓟 s ↔ 是开集 s
  证明: by
  rw [← principal_le_nhdsSet.ge_iff_eq']; rw [le_principal_iff]; rw [mem_nhdsSet_iff_forall]; rw [isOpen_iff_mem_nhds]

alias ⟨_, IsOpen.nhdsSet_eq⟩ := nhdsSet_eq_principal_iff

@[simp]

Depends on / 依赖: ge_iff_eq, isOpen_iff_mem_nhds, le_principal_iff, mem_nhdsSet_iff_forall, principal_le_nhdsSet, principal_le_nhdsSet.ge_iff_eq
-/
theorem nhdsSet_eq_principal_iff : 𝓝ˢ s = 𝓟 s ↔ IsOpen s := by
  rw [← principal_le_nhdsSet.ge_iff_eq']; rw [le_principal_iff]; rw [mem_nhdsSet_iff_forall]; rw [isOpen_iff_mem_nhds]

alias ⟨_, IsOpen.nhdsSet_eq⟩ := nhdsSet_eq_principal_iff

@[simp]
/--
theorem `nhdsSet_interior` / 定理 `nhdsSet_interior`

English:
theorem nhdsSet_interior
  statement: 𝓝ˢ (interior s) = 𝓟 (interior s)
  proof: isOpen_interior.nhdsSet_eq

@[simp]

中文:
定理 nhdsSet_interior
  结论: 𝓝ˢ (interior s) = 𝓟 (interior s)
  证明: isOpen_interior.nhdsSet_eq

@[simp]

Depends on / 依赖: isOpen_interior, isOpen_interior.nhdsSet_eq, nhdsSet_eq
-/
theorem nhdsSet_interior : 𝓝ˢ (interior s) = 𝓟 (interior s) :=
  isOpen_interior.nhdsSet_eq

@[simp]
/--
theorem `nhdsSet_singleton` / 定理 `nhdsSet_singleton`

English:
theorem nhdsSet_singleton
  statement: 𝓝ˢ {x} = 𝓝 x
  proof: by simp [nhdsSet]

中文:
定理 nhdsSet_singleton
  结论: 𝓝ˢ {x} = 𝓝 x
  证明: by simp [nhdsSet]

Depends on / 依赖: nhdsSet
-/
theorem nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x := by simp [nhdsSet]

/--
theorem `mem_nhdsSet_interior` / 定理 `mem_nhdsSet_interior`

English:
theorem mem_nhdsSet_interior
  statement: s in 𝓝ˢ (interior s)
  proof: subset_interior_iff_mem_nhdsSet.mp Subset.rfl

@[simp]

中文:
定理 mem_nhdsSet_interior
  结论: s in 𝓝ˢ (interior s)
  证明: subset_interior_iff_mem_nhdsSet.mp Subset.rfl

@[simp]

Depends on / 依赖: Subset, Subset.rfl, subset_interior_iff_mem_nhdsSet, subset_interior_iff_mem_nhdsSet.mp
-/
theorem mem_nhdsSet_interior : s in 𝓝ˢ (interior s) :=
  subset_interior_iff_mem_nhdsSet.mp Subset.rfl

@[simp]
/--
theorem `nhdsSet_empty` / 定理 `nhdsSet_empty`

English:
theorem nhdsSet_empty
  statement: 𝓝ˢ (∅ : Set X) = ⊥
  proof: by rw [isOpen_empty.nhdsSet_eq, principal_empty]

中文:
定理 nhdsSet_empty
  结论: 𝓝ˢ (∅ : 集合 X) = ⊥
  证明: by rw [isOpen_empty.nhdsSet_eq, principal_empty]

Depends on / 依赖: isOpen_empty, isOpen_empty.nhdsSet_eq, nhdsSet_eq, principal_empty
-/
theorem nhdsSet_empty : 𝓝ˢ (∅ : Set X) = ⊥ := by rw [isOpen_empty.nhdsSet_eq, principal_empty]

/--
theorem `mem_nhdsSet_empty` / 定理 `mem_nhdsSet_empty`

English:
theorem mem_nhdsSet_empty
  statement: s in 𝓝ˢ (∅ : Set X)
  proof: by simp

@[simp]

中文:
定理 mem_nhdsSet_empty
  结论: s in 𝓝ˢ (∅ : 集合 X)
  证明: by simp

@[simp]
-/
theorem mem_nhdsSet_empty : s in 𝓝ˢ (∅ : Set X) := by simp

@[simp]
/--
lemma `nhdsSet_eq_bot_iff` / 引理 `nhdsSet_eq_bot_iff`

English:
lemma nhdsSet_eq_bot_iff
  given: {α : Type*} [TopologicalSpace α] {s : Set α}
  proof: by simp [← empty_mem_iff_bot, mem_nhdsSet_iff_forall, eq_empty_iff_forall_notMem]
  mpr := by simp +contextual

中文:
引理 nhdsSet_eq_bot_iff
  条件: {α : 类型} [拓扑空间 α] {s : 集合 α}
  证明: by simp [← empty_mem_iff_bot, mem_nhdsSet_iff_forall, eq_empty_iff_forall_notMem]
  mpr := by simp +contextual

Depends on / 依赖: contextual, empty_mem_iff_bot, eq_empty_iff_forall_notMem, mem_nhdsSet_iff_forall
-/
lemma nhdsSet_eq_bot_iff {α : Type*} [TopologicalSpace α] {s : Set α} :
    𝓝ˢ s = ⊥ ↔ s = ∅ where
  mp := by simp [← empty_mem_iff_bot, mem_nhdsSet_iff_forall, eq_empty_iff_forall_notMem]
  mpr := by simp +contextual

/--
lemma `nhdsSet_neBot_iff` / 引理 `nhdsSet_neBot_iff`

English:
lemma nhdsSet_neBot_iff
  given: {α : Type*} [TopologicalSpace α] {s : Set α}
  proof: not_iff_not.mp by simp [not_nonempty_iff_eq_empty]

alias ⟨Set.Nonempty.nhdsSet_neBot, _⟩ := nhdsSet_neBot_iff

@[simp]

中文:
引理 nhdsSet_neBot_iff
  条件: {α : 类型} [拓扑空间 α] {s : 集合 α}
  证明: not_iff_not.mp by simp [not_nonempty_iff_eq_empty]

alias ⟨Set.Nonempty.nhdsSet_neBot, _⟩ := nhdsSet_neBot_iff

@[simp]

Depends on / 依赖: not_iff_not, not_iff_not.mp, not_nonempty_iff_eq_empty
-/
lemma nhdsSet_neBot_iff {α : Type*} [TopologicalSpace α] {s : Set α} :
    (𝓝ˢ s).NeBot ↔ s.Nonempty :=
not_iff_not.mp by simp [not_nonempty_iff_eq_empty]

alias ⟨Set.Nonempty.nhdsSet_neBot, _⟩ := nhdsSet_neBot_iff

@[simp]
/--
theorem `nhdsSet_univ` / 定理 `nhdsSet_univ`

English:
theorem nhdsSet_univ
  statement: 𝓝ˢ (univ : Set X) = ⊤
  proof: by rw [isOpen_univ.nhdsSet_eq, principal_univ]

@[gcongr, mono]

中文:
定理 nhdsSet_univ
  结论: 𝓝ˢ (univ : 集合 X) = ⊤
  证明: by rw [isOpen_univ.nhdsSet_eq, principal_univ]

@[gcongr, mono]

Depends on / 依赖: isOpen_univ, isOpen_univ.nhdsSet_eq, nhdsSet_eq, principal_univ
-/
theorem nhdsSet_univ : 𝓝ˢ (univ : Set X) = ⊤ := by rw [isOpen_univ.nhdsSet_eq, principal_univ]

@[gcongr, mono]
/--
theorem `nhdsSet_mono` / 定理 `nhdsSet_mono`

English:
theorem nhdsSet_mono
  given: (h : s subseteq t)
  statement: 𝓝ˢ s <= 𝓝ˢ t
  proof: sSup_le_sSup image_mono h

中文:
定理 nhdsSet_mono
  条件: (h : s subseteq t)
  结论: 𝓝ˢ s <= 𝓝ˢ t
  证明: sSup_le_sSup image_mono h

Depends on / 依赖: image_mono, sSup_le_sSup
-/
theorem nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t :=
sSup_le_sSup image_mono h

/--
theorem `monotone_nhdsSet` / 定理 `monotone_nhdsSet`

English:
theorem monotone_nhdsSet
  statement: Monotone (𝓝ˢ : Set X -> Filter X)
  proof: fun _ _ => nhdsSet_mono

中文:
定理 monotone_nhdsSet
  结论: 递增 (𝓝ˢ : 集合 X -> 滤子 X)
  证明: fun _ _ => nhdsSet_mono

Depends on / 依赖: nhdsSet_mono
-/
theorem monotone_nhdsSet : Monotone (𝓝ˢ : Set X -> Filter X) := fun _ _ => nhdsSet_mono

/--
theorem `nhds_le_nhdsSet` / 定理 `nhds_le_nhdsSet`

English:
theorem nhds_le_nhdsSet
  given: (h : x in s)
  statement: 𝓝 x <= 𝓝ˢ s
  proof: le_sSup mem_image_of_mem _ h

中文:
定理 nhds_le_nhdsSet
  条件: (h : x in s)
  结论: 𝓝 x <= 𝓝ˢ s
  证明: le_sSup mem_image_of_mem _ h

Depends on / 依赖: le_sSup, mem_image_of_mem
-/
theorem nhds_le_nhdsSet (h : x in s) : 𝓝 x <= 𝓝ˢ s :=
le_sSup mem_image_of_mem _ h

/--
theorem `tendsto_nhdsSet_of_tendsto_nhds` / 定理 `tendsto_nhdsSet_of_tendsto_nhds`

English:
theorem tendsto_nhdsSet_of_tendsto_nhds
  statement: {f : α -> X} {l : Filter α} {x : X} (hx : x in s)
  proof: hf.trans (nhds_le_nhdsSet hx)

@[simp]

中文:
定理 tendsto_nhdsSet_of_tendsto_nhds
  结论: {f : α -> X} {l : 滤子 α} {x : X} (hx : x in s)
  证明: hf.trans (nhds_le_nhdsSet hx)

@[simp]

Depends on / 依赖: hf.trans, nhds_le_nhdsSet
-/
theorem tendsto_nhdsSet_of_tendsto_nhds {f : α -> X} {l : Filter α} {x : X} (hx : x in s)
    (hf : Tendsto f l (𝓝 x)) :
    Tendsto f l (𝓝ˢ s) :=
  hf.trans (nhds_le_nhdsSet hx)

@[simp]
/--
theorem `nhdsSet_union` / 定理 `nhdsSet_union`

English:
theorem nhdsSet_union
  given: (s t : Set X)
  statement: 𝓝ˢ (s union t) = 𝓝ˢ s ⊔ 𝓝ˢ t
  proof: by
  simp only [nhdsSet, image_union, sSup_union]

中文:
定理 nhdsSet_union
  条件: (s t : 集合 X)
  结论: 𝓝ˢ (s union t) = 𝓝ˢ s ⊔ 𝓝ˢ t
  证明: by
  simp only [nhdsSet, image_union, sSup_union]

Depends on / 依赖: image_union, nhdsSet, sSup_union
-/
theorem nhdsSet_union (s t : Set X) : 𝓝ˢ (s union t) = 𝓝ˢ s ⊔ 𝓝ˢ t := by
  simp only [nhdsSet, image_union, sSup_union]

/--
theorem `union_mem_nhdsSet` / 定理 `union_mem_nhdsSet`

English:
theorem union_mem_nhdsSet
  given: (h₁ : s₁ in 𝓝ˢ t₁) (h₂ : s₂ in 𝓝ˢ t₂)
  statement: s₁ union s₂ in 𝓝ˢ (t₁ union t₂)
  proof: by
  rw [nhdsSet_union]
  exact union_mem_sup h₁ h₂

@[simp]

中文:
定理 union_mem_nhdsSet
  条件: (h₁ : s₁ in 𝓝ˢ t₁) (h₂ : s₂ in 𝓝ˢ t₂)
  结论: s₁ union s₂ in 𝓝ˢ (t₁ union t₂)
  证明: by
  rw [nhdsSet_union]
  exact union_mem_sup h₁ h₂

@[simp]

Depends on / 依赖: nhdsSet_union, union_mem_sup
-/
theorem union_mem_nhdsSet (h₁ : s₁ in 𝓝ˢ t₁) (h₂ : s₂ in 𝓝ˢ t₂) : s₁ union s₂ in 𝓝ˢ (t₁ union t₂) := by
  rw [nhdsSet_union]
  exact union_mem_sup h₁ h₂

@[simp]
/--
theorem `nhdsSet_insert` / 定理 `nhdsSet_insert`

English:
theorem nhdsSet_insert
  given: (x : X) (s : Set X)
  statement: 𝓝ˢ (insert x s) = 𝓝 x ⊔ 𝓝ˢ s
  proof: by
  rw [insert_eq]; rw [nhdsSet_union]; rw [nhdsSet_singleton]

中文:
定理 nhdsSet_insert
  条件: (x : X) (s : 集合 X)
  结论: 𝓝ˢ (insert x s) = 𝓝 x ⊔ 𝓝ˢ s
  证明: by
  rw [insert_eq]; rw [nhdsSet_union]; rw [nhdsSet_singleton]

Depends on / 依赖: insert_eq, nhdsSet_singleton, nhdsSet_union
-/
theorem nhdsSet_insert (x : X) (s : Set X) : 𝓝ˢ (insert x s) = 𝓝 x ⊔ 𝓝ˢ s := by
  rw [insert_eq]; rw [nhdsSet_union]; rw [nhdsSet_singleton]

/--
theorem `nhdsSet_inter_le` / 定理 `nhdsSet_inter_le`

English:
theorem nhdsSet_inter_le
  given: (s t : Set X)
  statement: 𝓝ˢ (s inter t) <= 𝓝ˢ s ⊓ 𝓝ˢ t
  proof: (monotone_nhdsSet (X := X)).map_inf_le s t

中文:
定理 nhdsSet_inter_le
  条件: (s t : 集合 X)
  结论: 𝓝ˢ (s inter t) <= 𝓝ˢ s ⊓ 𝓝ˢ t
  证明: (monotone_nhdsSet (X := X)).map_inf_le s t

Depends on / 依赖: map_inf_le, monotone_nhdsSet
-/
theorem nhdsSet_inter_le (s t : Set X) : 𝓝ˢ (s inter t) <= 𝓝ˢ s ⊓ 𝓝ˢ t :=
  (monotone_nhdsSet (X := X)).map_inf_le s t

/--
theorem `nhdsSet_iInter_le` / 定理 `nhdsSet_iInter_le`

English:
theorem nhdsSet_iInter_le
  given: {ι : Sort*} (s : ι -> Set X)
  statement: 𝓝ˢ (⋂ i, s i) <= ⨅ i, 𝓝ˢ (s i)
  proof: (monotone_nhdsSet (X := X)).map_iInf_le

中文:
定理 nhdsSet_i整数er_le
  条件: {ι : 类型层*} (s : ι -> 集合 X)
  结论: 𝓝ˢ (⋂ i, s i) <= ⨅ i, 𝓝ˢ (s i)
  证明: (monotone_nhdsSet (X := X)).map_iInf_le

Depends on / 依赖: map_iInf_le, monotone_nhdsSet
-/
theorem nhdsSet_iInter_le {ι : Sort*} (s : ι -> Set X) : 𝓝ˢ (⋂ i, s i) <= ⨅ i, 𝓝ˢ (s i) :=
  (monotone_nhdsSet (X := X)).map_iInf_le

/--
theorem `nhdsSet_sInter_le` / 定理 `nhdsSet_sInter_le`

English:
theorem nhdsSet_sInter_le
  given: (s : Set (Set X))
  statement: 𝓝ˢ (⋂₀ s) <= ⨅ x in s, 𝓝ˢ x
  proof: (monotone_nhdsSet (X := X)).map_sInf_le

中文:
定理 nhdsSet_s整数er_le
  条件: (s : 集合 (集合 X))
  结论: 𝓝ˢ (⋂₀ s) <= ⨅ x in s, 𝓝ˢ x
  证明: (monotone_nhdsSet (X := X)).map_sInf_le

Depends on / 依赖: map_sInf_le, monotone_nhdsSet
-/
theorem nhdsSet_sInter_le (s : Set (Set X)) : 𝓝ˢ (⋂₀ s) <= ⨅ x in s, 𝓝ˢ x :=
  (monotone_nhdsSet (X := X)).map_sInf_le

variable (s) in
/--
theorem `IsClosed.nhdsSet_le_sup` / 定理 `IsClosed.nhdsSet_le_sup`

English:
theorem IsClosed.nhdsSet_le_sup
  given: (h : IsClosed t)
  statement: 𝓝ˢ s <= 𝓝ˢ (s inter t) ⊔ 𝓟 (tᶜ)
  proof: calc
    𝓝ˢ s = 𝓝ˢ (s inter t union s inter tᶜ) := by rw [Set.inter_union_compl s t]
    _ = 𝓝ˢ (s inter t) ⊔ 𝓝ˢ (s inter tᶜ) := by rw [nhdsSet_union]
    _ <= 𝓝ˢ (s inter t) ⊔ 𝓝ˢ (tᶜ) := by nth_grw 2 [inter_subset_right]
    _ = 𝓝ˢ (s inter t) ⊔ 𝓟 (tᶜ) := by rw [h.isOpen_compl.nhdsSet_eq]

中文:
定理 是闭集.nhdsSet_le_sup
  条件: (h : 是闭集 t)
  结论: 𝓝ˢ s <= 𝓝ˢ (s inter t) ⊔ 𝓟 (tᶜ)
  证明: calc
    𝓝ˢ s = 𝓝ˢ (s inter t union s inter tᶜ) := by rw [Set.inter_union_compl s t]
    _ = 𝓝ˢ (s inter t) ⊔ 𝓝ˢ (s inter tᶜ) := by rw [nhdsSet_union]
    _ <= 𝓝ˢ (s inter t) ⊔ 𝓝ˢ (tᶜ) := by nth_grw 2 [inter_subset_right]
    _ = 𝓝ˢ (s inter t) ⊔ 𝓟 (tᶜ) := by rw [h.isOpen_compl.nhdsSet_eq]

Depends on / 依赖: Set.inter_union_compl, h.isOpen_compl.nhdsSet_eq, inter_subset_right, inter_union_compl, isOpen_compl, nhdsSet_eq, nhdsSet_union, nth_grw
-/
theorem IsClosed.nhdsSet_le_sup (h : IsClosed t) : 𝓝ˢ s <= 𝓝ˢ (s inter t) ⊔ 𝓟 (tᶜ) :=
  calc
    𝓝ˢ s = 𝓝ˢ (s inter t union s inter tᶜ) := by rw [Set.inter_union_compl s t]
    _ = 𝓝ˢ (s inter t) ⊔ 𝓝ˢ (s inter tᶜ) := by rw [nhdsSet_union]
    _ <= 𝓝ˢ (s inter t) ⊔ 𝓝ˢ (tᶜ) := by nth_grw 2 [inter_subset_right]
    _ = 𝓝ˢ (s inter t) ⊔ 𝓟 (tᶜ) := by rw [h.isOpen_compl.nhdsSet_eq]

variable (s) in
/--
theorem `IsClosed.nhdsSet_le_sup'` / 定理 `IsClosed.nhdsSet_le_sup'`

English:
theorem IsClosed.nhdsSet_le_sup'
  given: (h : IsClosed t)
  proof: by rw [Set.inter_comm]; exact h.nhdsSet_le_sup s

中文:
定理 是闭集.nhdsSet_le_sup'
  条件: (h : 是闭集 t)
  证明: by rw [Set.inter_comm]; exact h.nhdsSet_le_sup s

Depends on / 依赖: Set.inter_comm, h.nhdsSet_le_sup, inter_comm, nhdsSet_le_sup
-/
theorem IsClosed.nhdsSet_le_sup' (h : IsClosed t) :
    𝓝ˢ s <= 𝓝ˢ (t inter s) ⊔ 𝓟 (tᶜ) := by rw [Set.inter_comm]; exact h.nhdsSet_le_sup s

/--
theorem `Filter.Eventually.eventually_nhdsSet` / 定理 `Filter.Eventually.eventually_nhdsSet`

English:
theorem Filter.Eventually.eventually_nhdsSet
  given: {p : X -> Prop} (h : forallᶠ y in 𝓝ˢ s, p y)
  proof: eventually_nhdsSet_iff_forall.mpr fun x x_in =>
    (eventually_nhdsSet_iff_forall.mp h x x_in).eventually_nhds

中文:
定理 滤子.Eventually.eventually_nhdsSet
  条件: {p : X -> 命题} (h : 对任意ᶠ y in 𝓝ˢ s, p y)
  证明: eventually_nhdsSet_iff_forall.mpr fun x x_in =>
    (eventually_nhdsSet_iff_forall.mp h x x_in).eventually_nhds

Depends on / 依赖: eventually_nhds, eventually_nhdsSet_iff_forall, eventually_nhdsSet_iff_forall.mp, eventually_nhdsSet_iff_forall.mpr, x_in
-/
theorem Filter.Eventually.eventually_nhdsSet {p : X -> Prop} (h : forallᶠ y in 𝓝ˢ s, p y) :
    forallᶠ y in 𝓝ˢ s, forallᶠ x in 𝓝 y, p x :=
  eventually_nhdsSet_iff_forall.mpr fun x x_in =>
    (eventually_nhdsSet_iff_forall.mp h x x_in).eventually_nhds

/--
theorem `Filter.Eventually.union_nhdsSet` / 定理 `Filter.Eventually.union_nhdsSet`

English:
theorem Filter.Eventually.union_nhdsSet
  given: {p : X -> Prop}
  proof: by
  rw [nhdsSet_union]; rw [eventually_sup]

中文:
定理 滤子.Eventually.union_nhdsSet
  条件: {p : X -> 命题}
  证明: by
  rw [nhdsSet_union]; rw [eventually_sup]

Depends on / 依赖: eventually_sup, nhdsSet_union
-/
theorem Filter.Eventually.union_nhdsSet {p : X -> Prop} :
    (forallᶠ x in 𝓝ˢ (s union t), p x) ↔ (forallᶠ x in 𝓝ˢ s, p x) ∧ forallᶠ x in 𝓝ˢ t, p x := by
  rw [nhdsSet_union]; rw [eventually_sup]

/--
theorem `Filter.Eventually.union` / 定理 `Filter.Eventually.union`

English:
theorem Filter.Eventually.union
  given: {p : X -> Prop} (hs : forallᶠ x in 𝓝ˢ s, p x) (ht : forallᶠ x in 𝓝ˢ t, p x)
  proof: Filter.Eventually.union_nhdsSet.mpr ⟨hs, ht⟩

中文:
定理 滤子.Eventually.union
  条件: {p : X -> 命题} (hs : 对任意ᶠ x in 𝓝ˢ s, p x) (ht : 对任意ᶠ x in 𝓝ˢ t, p x)
  证明: Filter.Eventually.union_nhdsSet.mpr ⟨hs, ht⟩

Depends on / 依赖: Eventually, Filter, Filter.Eventually.union_nhdsSet.mpr, union_nhdsSet
-/
theorem Filter.Eventually.union {p : X -> Prop} (hs : forallᶠ x in 𝓝ˢ s, p x) (ht : forallᶠ x in 𝓝ˢ t, p x) :
    forallᶠ x in 𝓝ˢ (s union t), p x :=
  Filter.Eventually.union_nhdsSet.mpr ⟨hs, ht⟩

/--
theorem `nhdsSet_iUnion` / 定理 `nhdsSet_iUnion`

English:
theorem nhdsSet_iUnion
  given: {ι : Sort*} (s : ι -> Set X)
  statement: 𝓝ˢ (⋃ i, s i) = ⨆ i, 𝓝ˢ (s i)
  proof: by
  simp only [nhdsSet, image_iUnion, sSup_iUnion (β := Filter X)]

中文:
定理 nhdsSet_iUnion
  条件: {ι : 类型层*} (s : ι -> 集合 X)
  结论: 𝓝ˢ (⋃ i, s i) = ⨆ i, 𝓝ˢ (s i)
  证明: by
  simp only [nhdsSet, image_iUnion, sSup_iUnion (β := Filter X)]

Depends on / 依赖: Filter, image_iUnion, nhdsSet, sSup_iUnion
-/
theorem nhdsSet_iUnion {ι : Sort*} (s : ι -> Set X) : 𝓝ˢ (⋃ i, s i) = ⨆ i, 𝓝ˢ (s i) := by
  simp only [nhdsSet, image_iUnion, sSup_iUnion (β := Filter X)]

/--
theorem `eventually_nhdsSet_iUnion₂` / 定理 `eventually_nhdsSet_iUnion₂`

English:
theorem eventually_nhdsSet_iUnion₂
  given: {ι : Sort*} {p : ι -> Prop} {s : ι -> Set X} {P : X -> Prop}
  proof: by
  simp only [nhdsSet_iUnion, eventually_iSup]

中文:
定理 eventually_nhdsSet_iUnion₂
  条件: {ι : 类型层*} {p : ι -> 命题} {s : ι -> 集合 X} {P : X -> 命题}
  证明: by
  simp only [nhdsSet_iUnion, eventually_iSup]

Depends on / 依赖: eventually_iSup, nhdsSet_iUnion
-/
theorem eventually_nhdsSet_iUnion₂ {ι : Sort*} {p : ι -> Prop} {s : ι -> Set X} {P : X -> Prop} :
    (forallᶠ x in 𝓝ˢ (⋃ (i) (_ : p i), s i), P x) ↔ forall i, p i -> forallᶠ x in 𝓝ˢ (s i), P x := by
  simp only [nhdsSet_iUnion, eventually_iSup]

/--
theorem `eventually_nhdsSet_iUnion` / 定理 `eventually_nhdsSet_iUnion`

English:
theorem eventually_nhdsSet_iUnion
  given: {ι : Sort*} {s : ι -> Set X} {P : X -> Prop}
  proof: by
  simp only [nhdsSet_iUnion, eventually_iSup]

中文:
定理 eventually_nhdsSet_iUnion
  条件: {ι : 类型层*} {s : ι -> 集合 X} {P : X -> 命题}
  证明: by
  simp only [nhdsSet_iUnion, eventually_iSup]

Depends on / 依赖: eventually_iSup, nhdsSet_iUnion
-/
theorem eventually_nhdsSet_iUnion {ι : Sort*} {s : ι -> Set X} {P : X -> Prop} :
    (forallᶠ x in 𝓝ˢ (⋃ i, s i), P x) ↔ forall i, forallᶠ x in 𝓝ˢ (s i), P x := by
  simp only [nhdsSet_iUnion, eventually_iSup]
