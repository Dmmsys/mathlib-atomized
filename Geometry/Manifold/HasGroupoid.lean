/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Charted spaces with a given structure groupoid
-/

@[expose] public section

noncomputable section

open TopologicalSpace Topology

universe u

variable {H : Type u} {H' : Type*} {M : Type*} {M' : Type*} {M'' : Type*}

open Set OpenPartialHomeomorph Manifold

section HasGroupoid

variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

/--
Definition of `HasGroupoid` / `HasGroupoid` 的定义

English:
class HasGroupoid
  parameters: {H : Type*} [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
  axioms and operations (1):
    - compatible : forall {e e' : OpenPartialHomeomorph M H}, e in atlas H M -> e' in atlas H M -> e.symm ≫ₕ e' in G

中文:
类 有群胚
  参数: {H : 类型} [拓扑空间 H] (M : 类型) [拓扑空间 M]
  公理与运算 (1 个):
    - compatible : 对任意 {e e' : OpenPartialHomeomorph M H}, e in atlas H M -> e' in atlas H M -> e.symm ≫ₕ e' in G
-/
class HasGroupoid {H : Type*} [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (G : StructureGroupoid H) : Prop where
  compatible :
    forall {e e' : OpenPartialHomeomorph M H}, e in atlas H M -> e' in atlas H M -> e.symm ≫ₕ e' in G

/--
theorem `StructureGroupoid.compatible` / 定理 `StructureGroupoid.compatible`

English:
theorem StructureGroupoid.compatible
  statement: {H : Type*} [TopologicalSpace H] (G : StructureGroupoid H)
  proof: HasGroupoid.compatible he he'

中文:
定理 StructureGroupoid.compatible
  结论: {H : 类型} [拓扑空间 H] (G : StructureGroupoid H)
  证明: HasGroupoid.compatible he he'

Depends on / 依赖: HasGroupoid, HasGroupoid.compatible, compatible
-/
theorem StructureGroupoid.compatible {H : Type*} [TopologicalSpace H] (G : StructureGroupoid H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G]
    {e e' : OpenPartialHomeomorph M H} (he : e in atlas H M) (he' : e' in atlas H M) :
    e.symm ≫ₕ e' in G :=
  HasGroupoid.compatible he he'

/--
theorem `hasGroupoid_of_le` / 定理 `hasGroupoid_of_le`

English:
theorem hasGroupoid_of_le
  given: {G₁ G₂ : StructureGroupoid H} (h : HasGroupoid M G₁) (hle : G₁ <= G₂)
  proof: ⟨fun he he' => hle (h.compatible he he')⟩

中文:
定理 hasGroupoid_of_le
  条件: {G₁ G₂ : StructureGroupoid H} (h : 有群胚 M G₁) (hle : G₁ <= G₂)
  证明: ⟨fun he he' => hle (h.compatible he he')⟩

Depends on / 依赖: compatible, h.compatible
-/
theorem hasGroupoid_of_le {G₁ G₂ : StructureGroupoid H} (h : HasGroupoid M G₁) (hle : G₁ <= G₂) :
    HasGroupoid M G₂ :=
  ⟨fun he he' => hle (h.compatible he he')⟩

/--
theorem `hasGroupoid_inf_iff` / 定理 `hasGroupoid_inf_iff`

English:
theorem hasGroupoid_inf_iff
  given: {G₁ G₂ : StructureGroupoid H}
  statement: HasGroupoid M (G₁ ⊓ G₂) ↔
  proof: ⟨(fun h => ⟨hasGroupoid_of_le h inf_le_left, hasGroupoid_of_le h inf_le_right⟩),
  fun ⟨h1, h2⟩ => { compatible := fun he he' => ⟨h1.compatible he he', h2.compatible he he'⟩ }⟩

中文:
定理 hasGroupoid_inf_iff
  条件: {G₁ G₂ : StructureGroupoid H}
  结论: 有群胚 M (G₁ ⊓ G₂) ↔
  证明: ⟨(fun h => ⟨hasGroupoid_of_le h inf_le_left, hasGroupoid_of_le h inf_le_right⟩),
  fun ⟨h1, h2⟩ => { compatible := fun he he' => ⟨h1.compatible he he', h2.compatible he he'⟩ }⟩

Depends on / 依赖: compatible, h1.compatible, h2.compatible, hasGroupoid_of_le, inf_le_left, inf_le_right
-/
theorem hasGroupoid_inf_iff {G₁ G₂ : StructureGroupoid H} : HasGroupoid M (G₁ ⊓ G₂) ↔
    HasGroupoid M G₁ ∧ HasGroupoid M G₂ :=
  ⟨(fun h => ⟨hasGroupoid_of_le h inf_le_left, hasGroupoid_of_le h inf_le_right⟩),
  fun ⟨h1, h2⟩ => { compatible := fun he he' => ⟨h1.compatible he he', h2.compatible he he'⟩ }⟩

/--
theorem `hasGroupoid_of_pregroupoid` / 定理 `hasGroupoid_of_pregroupoid`

English:
theorem hasGroupoid_of_pregroupoid
  statement: (PG : Pregroupoid H) (h : forall {e e' : OpenPartialHomeomorph M H},
  proof: ⟨fun he he' => mem_groupoid_of_pregroupoid.mpr ⟨h he he', h he' he⟩⟩

中文:
定理 hasGroupoid_of_pregroupoid
  结论: (PG : Pregroupoid H) (h : 对任意 {e e' : OpenPartialHomeomorph M H},
  证明: ⟨fun he he' => mem_groupoid_of_pregroupoid.mpr ⟨h he he', h he' he⟩⟩

Depends on / 依赖: mem_groupoid_of_pregroupoid, mem_groupoid_of_pregroupoid.mpr
-/
theorem hasGroupoid_of_pregroupoid (PG : Pregroupoid H) (h : forall {e e' : OpenPartialHomeomorph M H},
    e in atlas H M -> e' in atlas H M -> PG.property (e.symm ≫ₕ e') (e.symm ≫ₕ e').source) :
    HasGroupoid M PG.groupoid :=
  ⟨fun he he' => mem_groupoid_of_pregroupoid.mpr ⟨h he he', h he' he⟩⟩

/--
Instance `hasGroupoid_model_space` / 实例 `hasGroupoid_model_space`

English:
instance hasGroupoid_model_space
  signature: (H : Type*) [TopologicalSpace H] (G : StructureGroupoid H)
  body: by
    rw [chartedSpaceSelf_atlas] at he he'
    simp [he, he', StructureGroupoid.id_mem]

中文:
实例 hasGroupoid_model_space
  签名: (H : 类型) [拓扑空间 H] (G : StructureGroupoid H)
  定义体: by
    rw [chartedSpaceSelf_atlas] at he he'
    simp [he, he', StructureGroupoid.id_mem]

Depends on / 依赖: StructureGroupoid, StructureGroupoid.id_mem, chartedSpaceSelf_atlas, id_mem
-/
instance hasGroupoid_model_space (H : Type*) [TopologicalSpace H] (G : StructureGroupoid H) :
    HasGroupoid H G where
  compatible {e e'} he he' := by
    rw [chartedSpaceSelf_atlas] at he he'
    simp [he, he', StructureGroupoid.id_mem]

/--
Instance `hasGroupoid_continuousGroupoid` / 实例 `hasGroupoid_continuousGroupoid`

English:
instance hasGroupoid_continuousGroupoid
  signature: : HasGroupoid M (continuousGroupoid H)
  body: by
  refine ⟨fun _ _ => ?_⟩
  rw [continuousGroupoid]; rw [mem_groupoid_of_pregroupoid]
  simp only [and_self_iff]

中文:
实例 hasGroupoid_continuousGroupoid
  签名: : 有群胚 M (continuousGroupoid H)
  定义体: by
  refine ⟨fun _ _ => ?_⟩
  rw [continuousGroupoid]; rw [mem_groupoid_of_pregroupoid]
  simp only [and_self_iff]

Depends on / 依赖: and_self_iff, continuousGroupoid, mem_groupoid_of_pregroupoid
-/
instance hasGroupoid_continuousGroupoid : HasGroupoid M (continuousGroupoid H) := by
  refine ⟨fun _ _ => ?_⟩
  rw [continuousGroupoid]; rw [mem_groupoid_of_pregroupoid]
  simp only [and_self_iff]

/--
theorem `StructureGroupoid.trans_restricted` / 定理 `StructureGroupoid.trans_restricted`

English:
theorem StructureGroupoid.trans_restricted
  statement: {e e' : OpenPartialHomeomorph M H}
  proof: G.mem_of_eqOnSource (closedUnderRestriction' (G.compatible he he')
    (e.isOpen_inter_preimage_symm s.2)) (e.subtypeRestr_symm_trans_subtypeRestr hs e')

中文:
定理 StructureGroupoid.trans_restricted
  结论: {e e' : OpenPartialHomeomorph M H}
  证明: G.mem_of_eqOnSource (closedUnderRestriction' (G.compatible he he')
    (e.isOpen_inter_preimage_symm s.2)) (e.subtypeRestr_symm_trans_subtypeRestr hs e')

Depends on / 依赖: G.compatible, G.mem_of_eqOnSource, closedUnderRestriction, compatible, e.isOpen_inter_preimage_symm, e.subtypeRestr_symm_trans_subtypeRestr, isOpen_inter_preimage_symm, mem_of_eqOnSource, subtypeRestr_symm_trans_subtypeRestr
-/
theorem StructureGroupoid.trans_restricted {e e' : OpenPartialHomeomorph M H}
    {G : StructureGroupoid H} (he : e in atlas H M) (he' : e' in atlas H M)
    [HasGroupoid M G] [ClosedUnderRestriction G] {s : Opens M} (hs : Nonempty s) :
    (e.subtypeRestr hs).symm ≫ₕ e'.subtypeRestr hs in G :=
  G.mem_of_eqOnSource (closedUnderRestriction' (G.compatible he he')
    (e.isOpen_inter_preimage_symm s.2)) (e.subtypeRestr_symm_trans_subtypeRestr hs e')

section MaximalAtlas

variable (G : StructureGroupoid H)

variable (M) in
/--
Definition of `StructureGroupoid.maximalAtlas` / `StructureGroupoid.maximalAtlas` 的定义

English:
definition StructureGroupoid.maximalAtlas
  signature: : Set (OpenPartialHomeomorph M H)
  body: { e | forall e' in atlas H M, e.symm ≫ₕ e' in G ∧ e'.symm ≫ₕ e in G }

中文:
定义 StructureGroupoid.maximalAtlas
  签名: : 集合 (OpenPartialHomeomorph M H)
  定义体: { e | forall e' in atlas H M, e.symm ≫ₕ e' in G ∧ e'.symm ≫ₕ e in G }

Depends on / 依赖: e.symm
-/
def StructureGroupoid.maximalAtlas : Set (OpenPartialHomeomorph M H) :=
  { e | forall e' in atlas H M, e.symm ≫ₕ e' in G ∧ e'.symm ≫ₕ e in G }

/--
theorem `StructureGroupoid.subset_maximalAtlas` / 定理 `StructureGroupoid.subset_maximalAtlas`

English:
theorem StructureGroupoid.subset_maximalAtlas
  given: [HasGroupoid M G]
  statement: atlas H M subseteq G.maximalAtlas M
  proof: fun _ he _ he' => ⟨G.compatible he he', G.compatible he' he⟩

中文:
定理 StructureGroupoid.subset_maximalAtlas
  条件: [有群胚 M G]
  结论: atlas H M subseteq G.maximalAtlas M
  证明: fun _ he _ he' => ⟨G.compatible he he', G.compatible he' he⟩

Depends on / 依赖: G.compatible, compatible
-/
theorem StructureGroupoid.subset_maximalAtlas [HasGroupoid M G] : atlas H M subseteq G.maximalAtlas M :=
  fun _ he _ he' => ⟨G.compatible he he', G.compatible he' he⟩

/--
theorem `StructureGroupoid.chart_mem_maximalAtlas` / 定理 `StructureGroupoid.chart_mem_maximalAtlas`

English:
theorem StructureGroupoid.chart_mem_maximalAtlas
  given: [HasGroupoid M G] (x : M)
  proof: G.subset_maximalAtlas (chart_mem_atlas H x)

中文:
定理 StructureGroupoid.chart_mem_maximalAtlas
  条件: [有群胚 M G] (x : M)
  证明: G.subset_maximalAtlas (chart_mem_atlas H x)

Depends on / 依赖: G.subset_maximalAtlas, chart_mem_atlas, subset_maximalAtlas
-/
theorem StructureGroupoid.chart_mem_maximalAtlas [HasGroupoid M G] (x : M) :
    chartAt H x in G.maximalAtlas M :=
  G.subset_maximalAtlas (chart_mem_atlas H x)

variable {G}

/--
theorem `mem_maximalAtlas_iff` / 定理 `mem_maximalAtlas_iff`

English:
theorem mem_maximalAtlas_iff
  given: {e : OpenPartialHomeomorph M H}
  proof: Iff.rfl

中文:
定理 mem_maximalAtlas_iff
  条件: {e : OpenPartialHomeomorph M H}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_maximalAtlas_iff {e : OpenPartialHomeomorph M H} :
    e in G.maximalAtlas M ↔ forall e' in atlas H M, e.symm ≫ₕ e' in G ∧ e'.symm ≫ₕ e in G :=
  Iff.rfl

/--
theorem `StructureGroupoid.compatible_of_mem_maximalAtlas_right` / 定理 `StructureGroupoid.compatible_of_mem_maximalAtlas_right`

English:
theorem StructureGroupoid.compatible_of_mem_maximalAtlas_right
  proof: (he' _ (ChartedSpace.chart_mem_atlas x)).2

中文:
定理 StructureGroupoid.compatible_of_mem_maximalAtlas_right
  证明: (he' _ (ChartedSpace.chart_mem_atlas x)).2

Depends on / 依赖: ChartedSpace, ChartedSpace.chart_mem_atlas, chart_mem_atlas
-/
theorem StructureGroupoid.compatible_of_mem_maximalAtlas_right
    {e' : OpenPartialHomeomorph M H} {x : M}
    (he' : e' in G.maximalAtlas M) : (chartAt H x).symm ≫ₕ e' in G :=
  (he' _ (ChartedSpace.chart_mem_atlas x)).2

/--
theorem `StructureGroupoid.compatible_of_mem_maximalAtlas_left` / 定理 `StructureGroupoid.compatible_of_mem_maximalAtlas_left`

English:
theorem StructureGroupoid.compatible_of_mem_maximalAtlas_left
  proof: (he' _ (ChartedSpace.chart_mem_atlas x)).1

中文:
定理 StructureGroupoid.compatible_of_mem_maximalAtlas_left
  证明: (he' _ (ChartedSpace.chart_mem_atlas x)).1

Depends on / 依赖: ChartedSpace, ChartedSpace.chart_mem_atlas, chart_mem_atlas
-/
theorem StructureGroupoid.compatible_of_mem_maximalAtlas_left
    {e' : OpenPartialHomeomorph M H} {x : M}
    (he' : e' in G.maximalAtlas M) : e'.symm ≫ₕ chartAt H x in G :=
  (he' _ (ChartedSpace.chart_mem_atlas x)).1

/--
theorem `StructureGroupoid.compatible_of_mem_maximalAtlas` / 定理 `StructureGroupoid.compatible_of_mem_maximalAtlas`

English:
theorem StructureGroupoid.compatible_of_mem_maximalAtlas
  statement: {e e' : OpenPartialHomeomorph M H}
  proof: by
  refine G.locality fun x hx => ?_
  set f := chartAt (H := H) (e.symm x)
  let s := e.target inter e.symm ⁻¹' f.source
  have hs : IsOpen s := by
    apply e.symm.continuousOn_toFun.isOpen_inter_preimage <;> apply open_source
  have xs : x in s := by
    simp only [s, f, mem_inter_iff, mem_preimage, mem_chart_source, and_true]
    exact ((mem_inter_iff _ _ _).1 hx).1
  refine ⟨s, hs, xs, ?_⟩
  have A : e.symm ≫ₕ f in G := (mem_maximalAtlas_iff.1 he f (chart_mem_atlas _ _)).1
  have B : f.symm ≫ₕ e' in G := (mem_maximalAtlas_iff.1 he' f (chart_mem_atlas _ _)).2
  have C : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' in G := G.trans A B
  have D : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' ≈ (e.symm ≫ₕ e').restr s := calc
    (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' = e.symm ≫ₕ (f ≫ₕ f.symm) ≫ₕ e' := by simp only [trans_assoc]
    _ ≈ e.symm ≫ₕ ofSet f.source f.open_source ≫ₕ e' :=
      EqOnSource.trans' (refl _) (EqOnSource.trans' (self_trans_symm _) (refl _))
    _ ≈ (e.symm ≫ₕ ofSet f.source f.open_source) ≫ₕ e' := by rw [trans_assoc]
    _ ≈ e.symm.restr s ≫ₕ e' := by rw [trans_of_set']; apply refl
    _ ≈ (e.symm ≫ₕ e').restr s := by rw [restr_trans]
  exact G.mem_of_eqOnSource C (Setoid.symm D)

中文:
定理 StructureGroupoid.compatible_of_mem_maximalAtlas
  结论: {e e' : OpenPartialHomeomorph M H}
  证明: by
  refine G.locality fun x hx => ?_
  set f := chartAt (H := H) (e.symm x)
  let s := e.target inter e.symm ⁻¹' f.source
  have hs : IsOpen s := by
    apply e.symm.continuousOn_toFun.isOpen_inter_preimage <;> apply open_source
  have xs : x in s := by
    simp only [s, f, mem_inter_iff, mem_preimage, mem_chart_source, and_true]
    exact ((mem_inter_iff _ _ _).1 hx).1
  refine ⟨s, hs, xs, ?_⟩
  have A : e.symm ≫ₕ f in G := (mem_maximalAtlas_iff.1 he f (chart_mem_atlas _ _)).1
  have B : f.symm ≫ₕ e' in G := (mem_maximalAtlas_iff.1 he' f (chart_mem_atlas _ _)).2
  have C : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' in G := G.trans A B
  have D : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' ≈ (e.symm ≫ₕ e').restr s := calc
    (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' = e.symm ≫ₕ (f ≫ₕ f.symm) ≫ₕ e' := by simp only [trans_assoc]
    _ ≈ e.symm ≫ₕ ofSet f.source f.open_source ≫ₕ e' :=
      EqOnSource.trans' (refl _) (EqOnSource.trans' (self_trans_symm _) (refl _))
    _ ≈ (e.symm ≫ₕ ofSet f.source f.open_source) ≫ₕ e' := by rw [trans_assoc]
    _ ≈ e.symm.restr s ≫ₕ e' := by rw [trans_of_set']; apply refl
    _ ≈ (e.symm ≫ₕ e').restr s := by rw [restr_trans]
  exact G.mem_of_eqOnSource C (Setoid.symm D)

Depends on / 依赖: G.locality, IsOpen, and_true, chartAt, chart_mem_atlas, continuousOn_toFun, e.symm, e.symm.continuousOn_toFun.isOpen_inter_preimage, e.target, f.source, f.symm, isOpen_inter_preimage, locality, mem_chart_source, mem_inter_iff, mem_maximal, mem_maximalAtlas_iff, mem_preimage, open_source, source
-/
theorem StructureGroupoid.compatible_of_mem_maximalAtlas {e e' : OpenPartialHomeomorph M H}
    (he : e in G.maximalAtlas M) (he' : e' in G.maximalAtlas M) : e.symm ≫ₕ e' in G := by
  refine G.locality fun x hx => ?_
  set f := chartAt (H := H) (e.symm x)
  let s := e.target inter e.symm ⁻¹' f.source
  have hs : IsOpen s := by
    apply e.symm.continuousOn_toFun.isOpen_inter_preimage <;> apply open_source
  have xs : x in s := by
    simp only [s, f, mem_inter_iff, mem_preimage, mem_chart_source, and_true]
    exact ((mem_inter_iff _ _ _).1 hx).1
  refine ⟨s, hs, xs, ?_⟩
  have A : e.symm ≫ₕ f in G := (mem_maximalAtlas_iff.1 he f (chart_mem_atlas _ _)).1
  have B : f.symm ≫ₕ e' in G := (mem_maximalAtlas_iff.1 he' f (chart_mem_atlas _ _)).2
  have C : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' in G := G.trans A B
  have D : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' ≈ (e.symm ≫ₕ e').restr s := calc
    (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' = e.symm ≫ₕ (f ≫ₕ f.symm) ≫ₕ e' := by simp only [trans_assoc]
    _ ≈ e.symm ≫ₕ ofSet f.source f.open_source ≫ₕ e' :=
      EqOnSource.trans' (refl _) (EqOnSource.trans' (self_trans_symm _) (refl _))
    _ ≈ (e.symm ≫ₕ ofSet f.source f.open_source) ≫ₕ e' := by rw [trans_assoc]
    _ ≈ e.symm.restr s ≫ₕ e' := by rw [trans_of_set']; apply refl
    _ ≈ (e.symm ≫ₕ e').restr s := by rw [restr_trans]
  exact G.mem_of_eqOnSource C (Setoid.symm D)

open OpenPartialHomeomorph in
/--
lemma `StructureGroupoid.mem_maximalAtlas_of_eqOnSource` / 引理 `StructureGroupoid.mem_maximalAtlas_of_eqOnSource`

English:
lemma StructureGroupoid.mem_maximalAtlas_of_eqOnSource
  statement: {e e' : OpenPartialHomeomorph M H}
  proof: by
  intro e'' he''
  obtain ⟨l, r⟩ := mem_maximalAtlas_iff.mp he e'' he''
  exact ⟨G.mem_of_eqOnSource l (EqOnSource.trans' (EqOnSource.symm' h) (e''.eqOnSource_refl)),
         G.mem_of_eqOnSource r (EqOnSource.trans' (e''.symm).eqOnSource_refl h)⟩

中文:
引理 StructureGroupoid.mem_maximalAtlas_of_eqOnSource
  结论: {e e' : OpenPartialHomeomorph M H}
  证明: by
  intro e'' he''
  obtain ⟨l, r⟩ := mem_maximalAtlas_iff.mp he e'' he''
  exact ⟨G.mem_of_eqOnSource l (EqOnSource.trans' (EqOnSource.symm' h) (e''.eqOnSource_refl)),
         G.mem_of_eqOnSource r (EqOnSource.trans' (e''.symm).eqOnSource_refl h)⟩

Depends on / 依赖: EqOnSource, EqOnSource.symm, EqOnSource.trans, G.mem_of_eqOnSource, eqOnSource_refl, mem_maximalAtlas_iff, mem_maximalAtlas_iff.mp, mem_of_eqOnSource
-/
lemma StructureGroupoid.mem_maximalAtlas_of_eqOnSource {e e' : OpenPartialHomeomorph M H}
    (h : e' ≈ e) (he : e in G.maximalAtlas M) : e' in G.maximalAtlas M := by
  intro e'' he''
  obtain ⟨l, r⟩ := mem_maximalAtlas_iff.mp he e'' he''
  exact ⟨G.mem_of_eqOnSource l (EqOnSource.trans' (EqOnSource.symm' h) (e''.eqOnSource_refl)),
         G.mem_of_eqOnSource r (EqOnSource.trans' (e''.symm).eqOnSource_refl h)⟩

variable (G)

/--
theorem `StructureGroupoid.id_mem_maximalAtlas` / 定理 `StructureGroupoid.id_mem_maximalAtlas`

English:
theorem StructureGroupoid.id_mem_maximalAtlas
  statement: OpenPartialHomeomorph.refl H in G.maximalAtlas H
  proof: G.subset_maximalAtlas by simp

中文:
定理 StructureGroupoid.id_mem_maximalAtlas
  结论: OpenPartialHomeomorph.refl H in G.maximalAtlas H
  证明: G.subset_maximalAtlas by simp

Depends on / 依赖: G.subset_maximalAtlas, subset_maximalAtlas
-/
theorem StructureGroupoid.id_mem_maximalAtlas : OpenPartialHomeomorph.refl H in G.maximalAtlas H :=
G.subset_maximalAtlas by simp

/--
theorem `StructureGroupoid.mem_maximalAtlas_of_mem_groupoid` / 定理 `StructureGroupoid.mem_maximalAtlas_of_mem_groupoid`

English:
theorem StructureGroupoid.mem_maximalAtlas_of_mem_groupoid
  statement: {f : OpenPartialHomeomorph H H}
  proof: by
  rintro e (rfl : e = OpenPartialHomeomorph.refl H)
  exact ⟨G.trans (G.symm hf) G.id_mem, G.trans (G.symm G.id_mem) hf⟩

中文:
定理 StructureGroupoid.mem_maximalAtlas_of_mem_groupoid
  结论: {f : OpenPartialHomeomorph H H}
  证明: by
  rintro e (rfl : e = OpenPartialHomeomorph.refl H)
  exact ⟨G.trans (G.symm hf) G.id_mem, G.trans (G.symm G.id_mem) hf⟩

Depends on / 依赖: G.id_mem, G.symm, G.trans, OpenPartialHomeomorph, OpenPartialHomeomorph.refl, id_mem
-/
theorem StructureGroupoid.mem_maximalAtlas_of_mem_groupoid {f : OpenPartialHomeomorph H H}
    (hf : f in G) : f in G.maximalAtlas H := by
  rintro e (rfl : e = OpenPartialHomeomorph.refl H)
  exact ⟨G.trans (G.symm hf) G.id_mem, G.trans (G.symm G.id_mem) hf⟩

/--
theorem `StructureGroupoid.maximalAtlas_mono` / 定理 `StructureGroupoid.maximalAtlas_mono`

English:
theorem StructureGroupoid.maximalAtlas_mono
  given: {G G' : StructureGroupoid H} (h : G <= G')
  proof: fun _ he e' he' => ⟨h (he e' he').1, h (he e' he').2⟩

中文:
定理 StructureGroupoid.maximalAtlas_mono
  条件: {G G' : StructureGroupoid H} (h : G <= G')
  证明: fun _ he e' he' => ⟨h (he e' he').1, h (he e' he').2⟩
-/
theorem StructureGroupoid.maximalAtlas_mono {G G' : StructureGroupoid H} (h : G <= G') :
    G.maximalAtlas M subseteq G'.maximalAtlas M :=
  fun _ he e' he' => ⟨h (he e' he').1, h (he e' he').2⟩

/--
theorem `restr_mem_maximalAtlas_aux1` / 定理 `restr_mem_maximalAtlas_aux1`

English:
theorem restr_mem_maximalAtlas_aux1
  statement: [ClosedUnderRestriction G]
  proof: by
  have hs'' : IsOpen (e '' (e.source inter s)) := by
    rw [isOpen_image_iff_of_subset_source _ inter_subset_left]
    exact e.open_source.inter hs
  have : (e.restr (e.source inter s)).symm ≫ₕ e' in G := by
    apply G.mem_of_eqOnSource (closedUnderRestriction' (he e' he').1 hs'')
    exact e.restr_symm_trans (e.open_source.inter hs) hs'' inter_subset_left
  refine G.mem_of_eqOnSource this ?_
  exact EqOnSource.trans' (Setoid.symm e.restr_inter_source).symm' (eqOnSource_refl e')

中文:
定理 restr_mem_maximalAtlas_aux1
  结论: [ClosedUnderRestriction G]
  证明: by
  have hs'' : IsOpen (e '' (e.source inter s)) := by
    rw [isOpen_image_iff_of_subset_source _ inter_subset_left]
    exact e.open_source.inter hs
  have : (e.restr (e.source inter s)).symm ≫ₕ e' in G := by
    apply G.mem_of_eqOnSource (closedUnderRestriction' (he e' he').1 hs'')
    exact e.restr_symm_trans (e.open_source.inter hs) hs'' inter_subset_left
  refine G.mem_of_eqOnSource this ?_
  exact EqOnSource.trans' (Setoid.symm e.restr_inter_source).symm' (eqOnSource_refl e')
-/
private theorem restr_mem_maximalAtlas_aux1 [ClosedUnderRestriction G]
    {e e' : OpenPartialHomeomorph M H} (he : e in G.maximalAtlas M) (he' : e' in atlas H M)
    {s : Set M} (hs : IsOpen s) :
    (e.restr s).symm ≫ₕ e' in G := by
  have hs'' : IsOpen (e '' (e.source inter s)) := by
    rw [isOpen_image_iff_of_subset_source _ inter_subset_left]
    exact e.open_source.inter hs
  have : (e.restr (e.source inter s)).symm ≫ₕ e' in G := by
    apply G.mem_of_eqOnSource (closedUnderRestriction' (he e' he').1 hs'')
    exact e.restr_symm_trans (e.open_source.inter hs) hs'' inter_subset_left
  refine G.mem_of_eqOnSource this ?_
  exact EqOnSource.trans' (Setoid.symm e.restr_inter_source).symm' (eqOnSource_refl e')

/--
theorem `restr_mem_maximalAtlas_aux2` / 定理 `restr_mem_maximalAtlas_aux2`

English:
theorem restr_mem_maximalAtlas_aux2
  statement: [ClosedUnderRestriction G]
  proof: by
  have hs'' : IsOpen (e' '' (e'.source inter s)) := by
    rw [isOpen_image_iff_of_subset_source e' inter_subset_left]
    exact e'.open_source.inter hs
  have ht : IsOpen (e'.target inter e'.symm ⁻¹' s) := by
    rw [← image_source_inter_eq']
    exact isOpen_image_source_inter e' hs
  exact G.mem_of_eqOnSource (closedUnderRestriction' (he e' he').2 ht) (e.symm_trans_restr e' hs)

中文:
定理 restr_mem_maximalAtlas_aux2
  结论: [ClosedUnderRestriction G]
  证明: by
  have hs'' : IsOpen (e' '' (e'.source inter s)) := by
    rw [isOpen_image_iff_of_subset_source e' inter_subset_left]
    exact e'.open_source.inter hs
  have ht : IsOpen (e'.target inter e'.symm ⁻¹' s) := by
    rw [← image_source_inter_eq']
    exact isOpen_image_source_inter e' hs
  exact G.mem_of_eqOnSource (closedUnderRestriction' (he e' he').2 ht) (e.symm_trans_restr e' hs)
-/
private theorem restr_mem_maximalAtlas_aux2 [ClosedUnderRestriction G]
    {e e' : OpenPartialHomeomorph M H} (he : e in G.maximalAtlas M) (he' : e' in atlas H M)
    {s : Set M} (hs : IsOpen s) :
    e'.symm ≫ₕ e.restr s in G := by
  have hs'' : IsOpen (e' '' (e'.source inter s)) := by
    rw [isOpen_image_iff_of_subset_source e' inter_subset_left]
    exact e'.open_source.inter hs
  have ht : IsOpen (e'.target inter e'.symm ⁻¹' s) := by
    rw [← image_source_inter_eq']
    exact isOpen_image_source_inter e' hs
  exact G.mem_of_eqOnSource (closedUnderRestriction' (he e' he').2 ht) (e.symm_trans_restr e' hs)

/--
theorem `restr_mem_maximalAtlas` / 定理 `restr_mem_maximalAtlas`

English:
theorem restr_mem_maximalAtlas
  statement: [ClosedUnderRestriction G]
  proof: fun _e' he' => ⟨restr_mem_maximalAtlas_aux1 G he he' hs, restr_mem_maximalAtlas_aux2 G he he' hs⟩

中文:
定理 restr_mem_maximalAtlas
  结论: [ClosedUnderRestriction G]
  证明: fun _e' he' => ⟨restr_mem_maximalAtlas_aux1 G he he' hs, restr_mem_maximalAtlas_aux2 G he he' hs⟩

Depends on / 依赖: restr_mem_maximalAtlas_aux1, restr_mem_maximalAtlas_aux2
-/
theorem restr_mem_maximalAtlas [ClosedUnderRestriction G]
    {e : OpenPartialHomeomorph M H} (he : e in G.maximalAtlas M) {s : Set M} (hs : IsOpen s) :
    e.restr s in G.maximalAtlas M :=
  fun _e' he' => ⟨restr_mem_maximalAtlas_aux1 G he he' hs, restr_mem_maximalAtlas_aux2 G he he' hs⟩

end MaximalAtlas

section Singleton

variable {α : Type*} [TopologicalSpace α]

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph α H)

/-- If a single open partial homeomorphism `e` from a space `α` into `H` has source covering the
whole space `α`, then that open partial homeomorphism induces an `H`-charted space structure on `α`.
(This condition is equivalent to `e` being an open embedding of `α` into `H`; see
`IsOpenEmbedding.singletonChartedSpace`.) -/
@[instance_reducible]
/--
Definition of `singletonChartedSpace` / `singletonChartedSpace` 的定义

English:
definition singletonChartedSpace
  signature: (h : e.source = Set.univ)
  body: {e}
  chartAt _ := e
  mem_chart_source _ := by rw [h]; apply mem_univ
  chart_mem_atlas _ := by tauto

@[simp, mfld_simps]

中文:
定义 singletonChartedSpace
  签名: (h : e.source = 集合.univ)
  定义体: {e}
  chartAt _ := e
  mem_chart_source _ := by rw [h]; apply mem_univ
  chart_mem_atlas _ := by tauto

@[simp, mfld_simps]
-/
def singletonChartedSpace (h : e.source = Set.univ) : ChartedSpace H α where
  atlas := {e}
  chartAt _ := e
  mem_chart_source _ := by rw [h]; apply mem_univ
  chart_mem_atlas _ := by tauto

@[simp, mfld_simps]
/--
theorem `singletonChartedSpace_chartAt_eq` / 定理 `singletonChartedSpace_chartAt_eq`

English:
theorem singletonChartedSpace_chartAt_eq
  given: (h : e.source = Set.univ) {x : α}
  proof: rfl

中文:
定理 singletonChartedSpace_chartAt_eq
  条件: (h : e.source = 集合.univ) {x : α}
  证明: rfl
-/
theorem singletonChartedSpace_chartAt_eq (h : e.source = Set.univ) {x : α} :
    @chartAt H _ α _ (e.singletonChartedSpace h) x = e :=
  rfl

/--
theorem `singletonChartedSpace_chartAt_source` / 定理 `singletonChartedSpace_chartAt_source`

English:
theorem singletonChartedSpace_chartAt_source
  given: (h : e.source = Set.univ) {x : α}
  proof: h

中文:
定理 singletonChartedSpace_chartAt_source
  条件: (h : e.source = 集合.univ) {x : α}
  证明: h
-/
theorem singletonChartedSpace_chartAt_source (h : e.source = Set.univ) {x : α} :
    (@chartAt H _ α _ (e.singletonChartedSpace h) x).source = Set.univ :=
  h

/--
theorem `singletonChartedSpace_mem_atlas_eq` / 定理 `singletonChartedSpace_mem_atlas_eq`

English:
theorem singletonChartedSpace_mem_atlas_eq
  statement: (h : e.source = Set.univ)
  proof: h'

中文:
定理 singletonChartedSpace_mem_atlas_eq
  结论: (h : e.source = 集合.univ)
  证明: h'
-/
theorem singletonChartedSpace_mem_atlas_eq (h : e.source = Set.univ)
    (e' : OpenPartialHomeomorph α H) (h' : e' in (e.singletonChartedSpace h).atlas) : e' = e :=
  h'

/--
theorem `singleton_hasGroupoid` / 定理 `singleton_hasGroupoid`

English:
theorem singleton_hasGroupoid
  statement: (h : e.source = Set.univ) (G : StructureGroupoid H)
  proof: { __ := e.singletonChartedSpace h
    compatible := by
      intro e' e'' he' he''
      rw [e.singletonChartedSpace_mem_atlas_eq h e' he']; rw [e.singletonChartedSpace_mem_atlas_eq h e'' he'']
      refine G.mem_of_eqOnSource ?_ e.symm_trans_self
      have hle : idRestrGroupoid <= G := (closedUnderRestriction_iff_id_le G).mp (by assumption)
      exact StructureGroupoid.le_iff.mp hle _ (idRestrGroupoid_mem _) }

中文:
定理 singleton_hasGroupoid
  结论: (h : e.source = 集合.univ) (G : StructureGroupoid H)
  证明: { __ := e.singletonChartedSpace h
    compatible := by
      intro e' e'' he' he''
      rw [e.singletonChartedSpace_mem_atlas_eq h e' he']; rw [e.singletonChartedSpace_mem_atlas_eq h e'' he'']
      refine G.mem_of_eqOnSource ?_ e.symm_trans_self
      have hle : idRestrGroupoid <= G := (closedUnderRestriction_iff_id_le G).mp (by assumption)
      exact StructureGroupoid.le_iff.mp hle _ (idRestrGroupoid_mem _) }

Depends on / 依赖: G.mem_of_eqOnSource, StructureGroupoid, StructureGroupoid.le_iff.mp, closedUnderRestriction_iff_id_le, compatible, e.singletonChartedSpace, e.singletonChartedSpace_mem_atlas_eq, e.symm_trans_self, idRestrGroupoid, idRestrGroupoid_mem, le_iff, mem_of_eqOnSource, singletonChartedSpace, singletonChartedSpace_mem_atlas_eq, symm_trans_self
-/
theorem singleton_hasGroupoid (h : e.source = Set.univ) (G : StructureGroupoid H)
    [ClosedUnderRestriction G] : @HasGroupoid _ _ _ _ (e.singletonChartedSpace h) G :=
  { __ := e.singletonChartedSpace h
    compatible := by
      intro e' e'' he' he''
      rw [e.singletonChartedSpace_mem_atlas_eq h e' he']; rw [e.singletonChartedSpace_mem_atlas_eq h e'' he'']
      refine G.mem_of_eqOnSource ?_ e.symm_trans_self
      have hle : idRestrGroupoid <= G := (closedUnderRestriction_iff_id_le G).mp (by assumption)
      exact StructureGroupoid.le_iff.mp hle _ (idRestrGroupoid_mem _) }

end OpenPartialHomeomorph

namespace Topology.IsOpenEmbedding

variable [Nonempty α]

/-- An open embedding of `α` into `H` induces an `H`-charted space structure on `α`.
See `OpenPartialHomeomorph.singletonChartedSpace`. -/
@[instance_reducible]
/--
Definition of `singletonChartedSpace` / `singletonChartedSpace` 的定义

English:
definition singletonChartedSpace
  signature: {f : α -> H} (h : IsOpenEmbedding f)
  body: (h.toOpenPartialHomeomorph f).singletonChartedSpace (toOpenPartialHomeomorph_source _ _)

中文:
定义 singletonChartedSpace
  签名: {f : α -> H} (h : 是开嵌入 f)
  定义体: (h.toOpenPartialHomeomorph f).singletonChartedSpace (toOpenPartialHomeomorph_source _ _)

Depends on / 依赖: h.toOpenPartialHomeomorph, singletonChartedSpace, toOpenPartialHomeomorph, toOpenPartialHomeomorph_source
-/
def singletonChartedSpace {f : α -> H} (h : IsOpenEmbedding f) : ChartedSpace H α :=
  (h.toOpenPartialHomeomorph f).singletonChartedSpace (toOpenPartialHomeomorph_source _ _)

/--
theorem `singletonChartedSpace_chartAt_eq` / 定理 `singletonChartedSpace_chartAt_eq`

English:
theorem singletonChartedSpace_chartAt_eq
  given: {f : α -> H} (h : IsOpenEmbedding f) {x : α}
  proof: rfl

中文:
定理 singletonChartedSpace_chartAt_eq
  条件: {f : α -> H} (h : 是开嵌入 f) {x : α}
  证明: rfl
-/
theorem singletonChartedSpace_chartAt_eq {f : α -> H} (h : IsOpenEmbedding f) {x : α} :
    ⇑(@chartAt H _ α _ h.singletonChartedSpace x) = f :=
  rfl

/--
theorem `singleton_hasGroupoid` / 定理 `singleton_hasGroupoid`

English:
theorem singleton_hasGroupoid
  statement: {f : α -> H} (h : IsOpenEmbedding f) (G : StructureGroupoid H)
  proof: (h.toOpenPartialHomeomorph f).singleton_hasGroupoid (toOpenPartialHomeomorph_source _ _) G

中文:
定理 singleton_hasGroupoid
  结论: {f : α -> H} (h : 是开嵌入 f) (G : StructureGroupoid H)
  证明: (h.toOpenPartialHomeomorph f).singleton_hasGroupoid (toOpenPartialHomeomorph_source _ _) G

Depends on / 依赖: h.toOpenPartialHomeomorph, singleton_hasGroupoid, toOpenPartialHomeomorph, toOpenPartialHomeomorph_source
-/
theorem singleton_hasGroupoid {f : α -> H} (h : IsOpenEmbedding f) (G : StructureGroupoid H)
    [ClosedUnderRestriction G] : @HasGroupoid _ _ _ _ h.singletonChartedSpace G :=
  (h.toOpenPartialHomeomorph f).singleton_hasGroupoid (toOpenPartialHomeomorph_source _ _) G

end Topology.IsOpenEmbedding

end Singleton

namespace TopologicalSpace.Opens

open TopologicalSpace

variable (G : StructureGroupoid H) [HasGroupoid M G]
variable (s : Opens M)

/--
Instance `instChartedSpace` / 实例 `instChartedSpace`

English:
instance instChartedSpace
  signature: : ChartedSpace H s where
  body: ⋃ x : s, {(chartAt H x.1).subtypeRestr ⟨x⟩}
  chartAt x := (chartAt H x.1).subtypeRestr ⟨x⟩
  mem_chart_source x := ⟨trivial, mem_chart_source H x.1⟩
  chart_mem_atlas x := by
    simp only [mem_iUnion, mem_singleton_iff]
    use x

中文:
实例 instChartedSpace
  签名: : Charted空间 H s where
  定义体: ⋃ x : s, {(chartAt H x.1).subtypeRestr ⟨x⟩}
  chartAt x := (chartAt H x.1).subtypeRestr ⟨x⟩
  mem_chart_source x := ⟨trivial, mem_chart_source H x.1⟩
  chart_mem_atlas x := by
    simp only [mem_iUnion, mem_singleton_iff]
    use x
-/
protected instance instChartedSpace : ChartedSpace H s where
  atlas := ⋃ x : s, {(chartAt H x.1).subtypeRestr ⟨x⟩}
  chartAt x := (chartAt H x.1).subtypeRestr ⟨x⟩
  mem_chart_source x := ⟨trivial, mem_chart_source H x.1⟩
  chart_mem_atlas x := by
    simp only [mem_iUnion, mem_singleton_iff]
    use x

/--
lemma `chartAt_eq` / 引理 `chartAt_eq`

English:
lemma chartAt_eq
  given: {s : Opens M} {x : s}
  statement: chartAt H x = (chartAt H x.1).subtypeRestr ⟨x⟩
  proof: rfl

中文:
引理 chartAt_eq
  条件: {s : Opens M} {x : s}
  结论: chartAt H x = (chartAt H x.1).subtypeRestr ⟨x⟩
  证明: rfl
-/
lemma chartAt_eq {s : Opens M} {x : s} : chartAt H x = (chartAt H x.1).subtypeRestr ⟨x⟩ := rfl

/--
lemma `chart_eq` / 引理 `chart_eq`

English:
lemma chart_eq
  statement: {s : Opens M} (hs : Nonempty s) {e : OpenPartialHomeomorph s H}
  proof: by
  rcases he with ⟨xset, ⟨x, hx⟩, he⟩
  exact ⟨x, mem_singleton_iff.mp (by convert! he)⟩

中文:
引理 chart_eq
  结论: {s : Opens M} (hs : 非空 s) {e : OpenPartialHomeomorph s H}
  证明: by
  rcases he with ⟨xset, ⟨x, hx⟩, he⟩
  exact ⟨x, mem_singleton_iff.mp (by convert! he)⟩

Depends on / 依赖: convert, mem_singleton_iff, mem_singleton_iff.mp
-/
lemma chart_eq {s : Opens M} (hs : Nonempty s) {e : OpenPartialHomeomorph s H}
    (he : e in atlas H s) : exists x : s, e = (chartAt H (x : M)).subtypeRestr hs := by
  rcases he with ⟨xset, ⟨x, hx⟩, he⟩
  exact ⟨x, mem_singleton_iff.mp (by convert! he)⟩

-- XXX: can I unify this with `chart_eq`?
/--
lemma `chart_eq'` / 引理 `chart_eq'`

English:
lemma chart_eq'
  statement: {t : Opens H} (ht : Nonempty t) {e' : OpenPartialHomeomorph t H}
  proof: chart_eq ht he'

中文:
引理 chart_eq'
  结论: {t : Opens H} (ht : 非空 t) {e' : OpenPartialHomeomorph t H}
  证明: chart_eq ht he'

Depends on / 依赖: chart_eq
-/
lemma chart_eq' {t : Opens H} (ht : Nonempty t) {e' : OpenPartialHomeomorph t H}
    (he' : e' in atlas H t) : exists x : t, e' = (chartAt H ↑x).subtypeRestr ht :=
  chart_eq ht he'

/--
Instance `instHasGroupoid` / 实例 `instHasGroupoid`

English:
instance instHasGroupoid
  signature: [ClosedUnderRestriction G]
  body: by
    rintro e e' ⟨_, ⟨x, hc⟩, he⟩ ⟨_, ⟨x', hc'⟩, he'⟩
    rw [hc.symm]; rw [mem_singleton_iff] at he
    rw [hc'.symm]; rw [mem_singleton_iff] at he'
    rw [he]; rw [he']
    refine G.mem_of_eqOnSource ?_
      (subtypeRestr_symm_trans_subtypeRestr (s := s) _ (chartAt H x) (chartAt H x'))
    apply closedUnderRestriction'
    · exact G.compatible (chart_mem_atlas _ _) (chart_mem_atlas _ _)
    · exact isOpen_inter_preimage_symm (chartAt _ _) s.2

中文:
实例 instHasGroupoid
  签名: [ClosedUnderRestriction G]
  定义体: by
    rintro e e' ⟨_, ⟨x, hc⟩, he⟩ ⟨_, ⟨x', hc'⟩, he'⟩
    rw [hc.symm]; rw [mem_singleton_iff] at he
    rw [hc'.symm]; rw [mem_singleton_iff] at he'
    rw [he]; rw [he']
    refine G.mem_of_eqOnSource ?_
      (subtypeRestr_symm_trans_subtypeRestr (s := s) _ (chartAt H x) (chartAt H x'))
    apply closedUnderRestriction'
    · exact G.compatible (chart_mem_atlas _ _) (chart_mem_atlas _ _)
    · exact isOpen_inter_preimage_symm (chartAt _ _) s.2
-/
protected instance instHasGroupoid [ClosedUnderRestriction G] : HasGroupoid s G where
  compatible := by
    rintro e e' ⟨_, ⟨x, hc⟩, he⟩ ⟨_, ⟨x', hc'⟩, he'⟩
    rw [hc.symm]; rw [mem_singleton_iff] at he
    rw [hc'.symm]; rw [mem_singleton_iff] at he'
    rw [he]; rw [he']
    refine G.mem_of_eqOnSource ?_
      (subtypeRestr_symm_trans_subtypeRestr (s := s) _ (chartAt H x) (chartAt H x'))
    apply closedUnderRestriction'
    · exact G.compatible (chart_mem_atlas _ _) (chart_mem_atlas _ _)
    · exact isOpen_inter_preimage_symm (chartAt _ _) s.2

/--
theorem `chartAt_subtype_val_symm_eventuallyEq` / 定理 `chartAt_subtype_val_symm_eventuallyEq`

English:
theorem chartAt_subtype_val_symm_eventuallyEq
  given: (U : Opens M) {x : U}
  proof: by
  set e := chartAt H x.val
  have heUx_nhds : (e.subtypeRestr ⟨x⟩).target in 𝓝 (e x) := by
    apply (e.subtypeRestr ⟨x⟩).open_target.mem_nhds
    exact e.map_subtype_source ⟨x⟩ (mem_chart_source _ _)
  exact Filter.eventuallyEq_of_mem heUx_nhds (e.subtypeRestr_symm_eqOn ⟨x⟩)

中文:
定理 chartAt_subtype_val_symm_eventuallyEq
  条件: (U : Opens M) {x : U}
  证明: by
  set e := chartAt H x.val
  have heUx_nhds : (e.subtypeRestr ⟨x⟩).target in 𝓝 (e x) := by
    apply (e.subtypeRestr ⟨x⟩).open_target.mem_nhds
    exact e.map_subtype_source ⟨x⟩ (mem_chart_source _ _)
  exact Filter.eventuallyEq_of_mem heUx_nhds (e.subtypeRestr_symm_eqOn ⟨x⟩)

Depends on / 依赖: Filter, Filter.eventuallyEq_of_mem, chartAt, e.map_subtype_source, e.subtypeRestr, e.subtypeRestr_symm_eqOn, eventuallyEq_of_mem, heUx_nhds, map_subtype_source, mem_chart_source, mem_nhds, open_target, open_target.mem_nhds, subtypeRestr, subtypeRestr_symm_eqOn, target, x.val
-/
theorem chartAt_subtype_val_symm_eventuallyEq (U : Opens M) {x : U} :
    (chartAt H x.val).symm =ᶠ[𝓝 (chartAt H x.val x.val)] Subtype.val ∘ (chartAt H x).symm := by
  set e := chartAt H x.val
  have heUx_nhds : (e.subtypeRestr ⟨x⟩).target in 𝓝 (e x) := by
    apply (e.subtypeRestr ⟨x⟩).open_target.mem_nhds
    exact e.map_subtype_source ⟨x⟩ (mem_chart_source _ _)
  exact Filter.eventuallyEq_of_mem heUx_nhds (e.subtypeRestr_symm_eqOn ⟨x⟩)

/--
theorem `chartAt_inclusion_symm_eventuallyEq` / 定理 `chartAt_inclusion_symm_eventuallyEq`

English:
theorem chartAt_inclusion_symm_eventuallyEq
  given: {U V : Opens M} (hUV : U <= V) {x : U}
  proof: by
  set e := chartAt H (x : M)
  have heUx_nhds : (e.subtypeRestr ⟨x⟩).target in 𝓝 (e x) := by
    apply (e.subtypeRestr ⟨x⟩).open_target.mem_nhds
    exact e.map_subtype_source ⟨x⟩ (mem_chart_source _ _)
exact Filter.eventuallyEq_of_mem heUx_nhds e.subtypeRestr_symm_eqOn_of_le ⟨x⟩
    ⟨Opens.inclusion hUV x⟩ hUV

中文:
定理 chartAt_inclusion_symm_eventuallyEq
  条件: {U V : Opens M} (hUV : U <= V) {x : U}
  证明: by
  set e := chartAt H (x : M)
  have heUx_nhds : (e.subtypeRestr ⟨x⟩).target in 𝓝 (e x) := by
    apply (e.subtypeRestr ⟨x⟩).open_target.mem_nhds
    exact e.map_subtype_source ⟨x⟩ (mem_chart_source _ _)
exact Filter.eventuallyEq_of_mem heUx_nhds e.subtypeRestr_symm_eqOn_of_le ⟨x⟩
    ⟨Opens.inclusion hUV x⟩ hUV

Depends on / 依赖: Filter, Filter.eventuallyEq_of_mem, Opens.inclusion, chartAt, e.map_subtype_source, e.subtypeRestr, e.subtypeRestr_symm_eqOn_of_le, eventuallyEq_of_mem, heUx_nhds, inclusion, map_subtype_source, mem_chart_source, mem_nhds, open_target, open_target.mem_nhds, subtypeRestr, subtypeRestr_symm_eqOn_of_le, target
-/
theorem chartAt_inclusion_symm_eventuallyEq {U V : Opens M} (hUV : U <= V) {x : U} :
    (chartAt H (Opens.inclusion hUV x)).symm
    =ᶠ[𝓝 (chartAt H (Opens.inclusion hUV x) (Set.inclusion hUV x))]
    Opens.inclusion hUV ∘ (chartAt H x).symm := by
  set e := chartAt H (x : M)
  have heUx_nhds : (e.subtypeRestr ⟨x⟩).target in 𝓝 (e x) := by
    apply (e.subtypeRestr ⟨x⟩).open_target.mem_nhds
    exact e.map_subtype_source ⟨x⟩ (mem_chart_source _ _)
exact Filter.eventuallyEq_of_mem heUx_nhds e.subtypeRestr_symm_eqOn_of_le ⟨x⟩
    ⟨Opens.inclusion hUV x⟩ hUV
end TopologicalSpace.Opens

/--
lemma `StructureGroupoid.subtypeRestr_mem_maximalAtlas` / 引理 `StructureGroupoid.subtypeRestr_mem_maximalAtlas`

English:
lemma StructureGroupoid.subtypeRestr_mem_maximalAtlas
  statement: {e : OpenPartialHomeomorph M H}
  proof: by
  intro e' he'
  -- `e'` is the restriction of some chart of `M` at `x`,
  obtain ⟨x, this⟩ := Opens.chart_eq hs he'
  rw [this]
  -- The transition functions between the unrestricted charts lie in the groupoid,
  -- the transition functions of the restriction are the restriction of the transition function.
  exact ⟨G.trans_restricted he (chart_mem_atlas H (x : M)) hs,
         G.trans_restricted (chart_mem_atlas H (x : M)) he hs⟩

中文:
引理 StructureGroupoid.subtypeRestr_mem_maximalAtlas
  结论: {e : OpenPartialHomeomorph M H}
  证明: by
  intro e' he'
  -- `e'` is the restriction of some chart of `M` at `x`,
  obtain ⟨x, this⟩ := Opens.chart_eq hs he'
  rw [this]
  -- The transition functions between the unrestricted charts lie in the groupoid,
  -- the transition functions of the restriction are the restriction of the transition function.
  exact ⟨G.trans_restricted he (chart_mem_atlas H (x : M)) hs,
         G.trans_restricted (chart_mem_atlas H (x : M)) he hs⟩
-/
lemma StructureGroupoid.subtypeRestr_mem_maximalAtlas {e : OpenPartialHomeomorph M H}
    (he : e in atlas H M) {s : Opens M} (hs : Nonempty s) {G : StructureGroupoid H} [HasGroupoid M G]
    [ClosedUnderRestriction G] : e.subtypeRestr hs in G.maximalAtlas s := by
  intro e' he'
  -- `e'` is the restriction of some chart of `M` at `x`,
  obtain ⟨x, this⟩ := Opens.chart_eq hs he'
  rw [this]
  -- The transition functions between the unrestricted charts lie in the groupoid,
  -- the transition functions of the restriction are the restriction of the transition function.
  exact ⟨G.trans_restricted he (chart_mem_atlas H (x : M)) hs,
         G.trans_restricted (chart_mem_atlas H (x : M)) he hs⟩

/-! ### Structomorphisms -/

/--
Definition of `Structomorph` / `Structomorph` 的定义

English:
structure Structomorph
  parameters: (G : StructureGroupoid H) (M : Type*) (M' : Type*) [TopologicalSpace M]
  extends: Homeomorph M M'
  axioms and operations (1):
    - mem_groupoid : forall c : OpenPartialHomeomorph M H, forall c' : OpenPartialHomeomorph M' H, c in atlas H M -> c' in atlas H M' -> c.symm ≫ₕ toHomeomorph.toOpenPartialHomeomorph ≫ₕ c' in G

中文:
结构 Structomorph
  参数: (G : StructureGroupoid H) (M : 类型) (M' : 类型) [拓扑空间 M]
  继承: 同胚 M M'
  公理与运算 (1 个):
    - mem_groupoid : 对任意 c : OpenPartialHomeomorph M H, 对任意 c' : OpenPartialHomeomorph M' H, c in atlas H M -> c' in atlas H M' -> c.symm ≫ₕ toHomeomorph.toOpenPartialHomeomorph ≫ₕ c' in G
-/
structure Structomorph (G : StructureGroupoid H) (M : Type*) (M' : Type*) [TopologicalSpace M]
  [TopologicalSpace M'] [ChartedSpace H M] [ChartedSpace H M'] extends Homeomorph M M' where
  mem_groupoid : forall c : OpenPartialHomeomorph M H, forall c' : OpenPartialHomeomorph M' H, c in atlas H M ->
    c' in atlas H M' -> c.symm ≫ₕ toHomeomorph.toOpenPartialHomeomorph ≫ₕ c' in G

variable [TopologicalSpace M'] [TopologicalSpace M''] {G : StructureGroupoid H} [ChartedSpace H M']
  [ChartedSpace H M'']

/--
Definition of `Structomorph.refl` / `Structomorph.refl` 的定义

English:
definition Structomorph.refl
  signature: (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G]
  body: { Homeomorph.refl M with
    mem_groupoid := fun c c' hc hc' => by
      change OpenPartialHomeomorph.symm c ≫ₕ OpenPartialHomeomorph.refl M ≫ₕ c' in G
      rw [OpenPartialHomeomorph.refl_trans]
      exact G.compatible hc hc' }

中文:
定义 Structomorph.refl
  签名: (M : 类型) [拓扑空间 M] [Charted空间 H M] [有群胚 M G]
  定义体: { Homeomorph.refl M with
    mem_groupoid := fun c c' hc hc' => by
      change OpenPartialHomeomorph.symm c ≫ₕ OpenPartialHomeomorph.refl M ≫ₕ c' in G
      rw [OpenPartialHomeomorph.refl_trans]
      exact G.compatible hc hc' }

Depends on / 依赖: G.compatible, Homeomorph, Homeomorph.refl, OpenPartialHomeomorph, OpenPartialHomeomorph.refl, OpenPartialHomeomorph.refl_trans, OpenPartialHomeomorph.symm, compatible, mem_groupoid, refl_trans
-/
def Structomorph.refl (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G] :
    Structomorph G M M :=
  { Homeomorph.refl M with
    mem_groupoid := fun c c' hc hc' => by
      change OpenPartialHomeomorph.symm c ≫ₕ OpenPartialHomeomorph.refl M ≫ₕ c' in G
      rw [OpenPartialHomeomorph.refl_trans]
      exact G.compatible hc hc' }

/--
Definition of `Structomorph.symm` / `Structomorph.symm` 的定义

English:
definition Structomorph.symm
  signature: (e : Structomorph G M M')
  body: { e.toHomeomorph.symm with
    mem_groupoid := by
      intro c c' hc hc'
      have : (c'.symm ≫ₕ e.toHomeomorph.toOpenPartialHomeomorph ≫ₕ c).symm in G :=
        G.symm (e.mem_groupoid c' c hc' hc)
      rwa [trans_symm_eq_symm_trans_symm, trans_symm_eq_symm_trans_symm, symm_symm, trans_assoc]
        at this }

中文:
定义 Structomorph.symm
  签名: (e : Structomorph G M M')
  定义体: { e.toHomeomorph.symm with
    mem_groupoid := by
      intro c c' hc hc'
      have : (c'.symm ≫ₕ e.toHomeomorph.toOpenPartialHomeomorph ≫ₕ c).symm in G :=
        G.symm (e.mem_groupoid c' c hc' hc)
      rwa [trans_symm_eq_symm_trans_symm, trans_symm_eq_symm_trans_symm, symm_symm, trans_assoc]
        at this }

Depends on / 依赖: G.symm, e.mem_groupoid, e.toHomeomorph.symm, e.toHomeomorph.toOpenPartialHomeomorph, mem_groupoid, symm_symm, toHomeomorph, toOpenPartialHomeomorph, trans_assoc, trans_symm_eq_symm_trans_symm
-/
def Structomorph.symm (e : Structomorph G M M') : Structomorph G M' M :=
  { e.toHomeomorph.symm with
    mem_groupoid := by
      intro c c' hc hc'
      have : (c'.symm ≫ₕ e.toHomeomorph.toOpenPartialHomeomorph ≫ₕ c).symm in G :=
        G.symm (e.mem_groupoid c' c hc' hc)
      rwa [trans_symm_eq_symm_trans_symm, trans_symm_eq_symm_trans_symm, symm_symm, trans_assoc]
        at this }

/--
Definition of `Structomorph.trans` / `Structomorph.trans` 的定义

English:
definition Structomorph.trans
  signature: (e : Structomorph G M M') (e' : Structomorph G M' M'')
  body: { Homeomorph.trans e.toHomeomorph e'.toHomeomorph with
    mem_groupoid := by
      /- Let c and c' be two charts in M and M''. We want to show that e' ∘ e is smooth in these
      charts, around any point x. For this, let y = e (c⁻¹ x), and consider a chart g around y.
      Then g ∘ e ∘ c⁻¹ and c' ∘ e' ∘ g⁻¹ are both smooth as e and e' are structomorphisms, so
      their composition is smooth, and it coincides with c' ∘ e' ∘ e ∘ c⁻¹ around x. -/
      intro c c' hc hc'
      refine G.locality fun x hx => ?_
      let f₁ := e.toHomeomorph.toOpenPartialHomeomorph
      let f₂ := e'.toHomeomorph.toOpenPartialHomeomorph
      let f := (e.toHomeomorph.trans e'.toHomeomorph).toOpenPartialHomeomorph
      have feq : f = f₁ ≫ₕ f₂ := Homeomorph.trans_toOpenPartialHomeomorph _ _
      -- define the atlas g around y
      let y := (c.symm ≫ₕ f₁) x
      let g := chartAt (H := H) y
      have hg₁ := chart_mem_atlas (H := H) y
      have hg₂ := mem_chart_source (H := H) y
      let s := (c.symm ≫ₕ f₁).source inter c.symm ≫ₕ f₁ ⁻¹' g.source
      have open_s : IsOpen s := by
        apply (c.symm ≫ₕ f₁).continuousOn_toFun.isOpen_inter_preimage <;> apply open_source
      have : x in s := by
        constructor
        · simp only [f₁, trans_source, preimage_univ, inter_univ,
            Homeomorph.toOpenPartialHomeomorph_source]
          rw [trans_source] at hx
          exact hx.1
        · exact hg₂
      refine ⟨s, open_s, this, ?_⟩
      let F₁ := (c.symm ≫ₕ f₁ ≫ₕ g) ≫ₕ g.symm ≫ₕ f₂ ≫ₕ c'
      have A : F₁ in G := G.trans (e.mem_groupoid c g hc hg₁) (e'.mem_groupoid g c' hg₁ hc')
      let F₂ := (c.symm ≫ₕ f ≫ₕ c').restr s
      have : F₁ ≈ F₂ := calc
        F₁ ≈ c.symm ≫ₕ f₁ ≫ₕ (g ≫ₕ g.symm) ≫ₕ f₂ ≫ₕ c' := by
            simp only [F₁, trans_assoc, _root_.refl]
        _ ≈ c.symm ≫ₕ f₁ ≫ₕ ofSet g.source g.open_source ≫ₕ f₂ ≫ₕ c' :=
          EqOnSource.trans' (_root_.refl _) (EqOnSource.trans' (_root_.refl _)
            (EqOnSource.trans' (self_trans_symm g) (_root_.refl _)))
        _ ≈ ((c.symm ≫ₕ f₁) ≫ₕ ofSet g.source g.open_source) ≫ₕ f₂ ≫ₕ c' := by
          simp only [trans_assoc, _root_.refl]
        _ ≈ (c.symm ≫ₕ f₁).restr s ≫ₕ f₂ ≫ₕ c' := by rw [trans_of_set']
        _ ≈ ((c.symm ≫ₕ f₁) ≫ₕ f₂ ≫ₕ c').restr s := by rw [restr_trans]
        _ ≈ (c.symm ≫ₕ (f₁ ≫ₕ f₂) ≫ₕ c').restr s := by
          simp only [trans_assoc, _root_.refl]
        _ ≈ F₂ := by simp only [F₂, feq, _root_.refl]
      have : F₂ in G := G.mem_of_eqOnSource A (Setoid.symm this)
      exact this }

中文:
定义 Structomorph.trans
  签名: (e : Structomorph G M M') (e' : Structomorph G M' M'')
  定义体: { Homeomorph.trans e.toHomeomorph e'.toHomeomorph with
    mem_groupoid := by
      /- Let c and c' be two charts in M and M''. We want to show that e' ∘ e is smooth in these
      charts, around any point x. For this, let y = e (c⁻¹ x), and consider a chart g around y.
      Then g ∘ e ∘ c⁻¹ and c' ∘ e' ∘ g⁻¹ are both smooth as e and e' are structomorphisms, so
      their composition is smooth, and it coincides with c' ∘ e' ∘ e ∘ c⁻¹ around x. -/
      intro c c' hc hc'
      refine G.locality fun x hx => ?_
      let f₁ := e.toHomeomorph.toOpenPartialHomeomorph
      let f₂ := e'.toHomeomorph.toOpenPartialHomeomorph
      let f := (e.toHomeomorph.trans e'.toHomeomorph).toOpenPartialHomeomorph
      have feq : f = f₁ ≫ₕ f₂ := Homeomorph.trans_toOpenPartialHomeomorph _ _
      -- define the atlas g around y
      let y := (c.symm ≫ₕ f₁) x
      let g := chartAt (H := H) y
      have hg₁ := chart_mem_atlas (H := H) y
      have hg₂ := mem_chart_source (H := H) y
      let s := (c.symm ≫ₕ f₁).source inter c.symm ≫ₕ f₁ ⁻¹' g.source
      have open_s : IsOpen s := by
        apply (c.symm ≫ₕ f₁).continuousOn_toFun.isOpen_inter_preimage <;> apply open_source
      have : x in s := by
        constructor
        · simp only [f₁, trans_source, preimage_univ, inter_univ,
            Homeomorph.toOpenPartialHomeomorph_source]
          rw [trans_source] at hx
          exact hx.1
        · exact hg₂
      refine ⟨s, open_s, this, ?_⟩
      let F₁ := (c.symm ≫ₕ f₁ ≫ₕ g) ≫ₕ g.symm ≫ₕ f₂ ≫ₕ c'
      have A : F₁ in G := G.trans (e.mem_groupoid c g hc hg₁) (e'.mem_groupoid g c' hg₁ hc')
      let F₂ := (c.symm ≫ₕ f ≫ₕ c').restr s
      have : F₁ ≈ F₂ := calc
        F₁ ≈ c.symm ≫ₕ f₁ ≫ₕ (g ≫ₕ g.symm) ≫ₕ f₂ ≫ₕ c' := by
            simp only [F₁, trans_assoc, _root_.refl]
        _ ≈ c.symm ≫ₕ f₁ ≫ₕ ofSet g.source g.open_source ≫ₕ f₂ ≫ₕ c' :=
          EqOnSource.trans' (_root_.refl _) (EqOnSource.trans' (_root_.refl _)
            (EqOnSource.trans' (self_trans_symm g) (_root_.refl _)))
        _ ≈ ((c.symm ≫ₕ f₁) ≫ₕ ofSet g.source g.open_source) ≫ₕ f₂ ≫ₕ c' := by
          simp only [trans_assoc, _root_.refl]
        _ ≈ (c.symm ≫ₕ f₁).restr s ≫ₕ f₂ ≫ₕ c' := by rw [trans_of_set']
        _ ≈ ((c.symm ≫ₕ f₁) ≫ₕ f₂ ≫ₕ c').restr s := by rw [restr_trans]
        _ ≈ (c.symm ≫ₕ (f₁ ≫ₕ f₂) ≫ₕ c').restr s := by
          simp only [trans_assoc, _root_.refl]
        _ ≈ F₂ := by simp only [F₂, feq, _root_.refl]
      have : F₂ in G := G.mem_of_eqOnSource A (Setoid.symm this)
      exact this }

Depends on / 依赖: CommSemiring, Homeomorph, Homeomorph.trans, Semiring, StrongRankCondition, e.toHomeomorph, mem_groupoid, toHomeomorph
-/
def Structomorph.trans (e : Structomorph G M M') (e' : Structomorph G M' M'') :
    Structomorph G M M'' :=
  { Homeomorph.trans e.toHomeomorph e'.toHomeomorph with
    mem_groupoid := by
      /- Let c and c' be two charts in M and M''. We want to show that e' ∘ e is smooth in these
      charts, around any point x. For this, let y = e (c⁻¹ x), and consider a chart g around y.
      Then g ∘ e ∘ c⁻¹ and c' ∘ e' ∘ g⁻¹ are both smooth as e and e' are structomorphisms, so
      their composition is smooth, and it coincides with c' ∘ e' ∘ e ∘ c⁻¹ around x. -/
      intro c c' hc hc'
      refine G.locality fun x hx => ?_
      let f₁ := e.toHomeomorph.toOpenPartialHomeomorph
      let f₂ := e'.toHomeomorph.toOpenPartialHomeomorph
      let f := (e.toHomeomorph.trans e'.toHomeomorph).toOpenPartialHomeomorph
      have feq : f = f₁ ≫ₕ f₂ := Homeomorph.trans_toOpenPartialHomeomorph _ _
      -- define the atlas g around y
      let y := (c.symm ≫ₕ f₁) x
      let g := chartAt (H := H) y
      have hg₁ := chart_mem_atlas (H := H) y
      have hg₂ := mem_chart_source (H := H) y
      let s := (c.symm ≫ₕ f₁).source inter c.symm ≫ₕ f₁ ⁻¹' g.source
      have open_s : IsOpen s := by
        apply (c.symm ≫ₕ f₁).continuousOn_toFun.isOpen_inter_preimage <;> apply open_source
      have : x in s := by
        constructor
        · simp only [f₁, trans_source, preimage_univ, inter_univ,
            Homeomorph.toOpenPartialHomeomorph_source]
          rw [trans_source] at hx
          exact hx.1
        · exact hg₂
      refine ⟨s, open_s, this, ?_⟩
      let F₁ := (c.symm ≫ₕ f₁ ≫ₕ g) ≫ₕ g.symm ≫ₕ f₂ ≫ₕ c'
      have A : F₁ in G := G.trans (e.mem_groupoid c g hc hg₁) (e'.mem_groupoid g c' hg₁ hc')
      let F₂ := (c.symm ≫ₕ f ≫ₕ c').restr s
      have : F₁ ≈ F₂ := calc
        F₁ ≈ c.symm ≫ₕ f₁ ≫ₕ (g ≫ₕ g.symm) ≫ₕ f₂ ≫ₕ c' := by
            simp only [F₁, trans_assoc, _root_.refl]
        _ ≈ c.symm ≫ₕ f₁ ≫ₕ ofSet g.source g.open_source ≫ₕ f₂ ≫ₕ c' :=
          EqOnSource.trans' (_root_.refl _) (EqOnSource.trans' (_root_.refl _)
            (EqOnSource.trans' (self_trans_symm g) (_root_.refl _)))
        _ ≈ ((c.symm ≫ₕ f₁) ≫ₕ ofSet g.source g.open_source) ≫ₕ f₂ ≫ₕ c' := by
          simp only [trans_assoc, _root_.refl]
        _ ≈ (c.symm ≫ₕ f₁).restr s ≫ₕ f₂ ≫ₕ c' := by rw [trans_of_set']
        _ ≈ ((c.symm ≫ₕ f₁) ≫ₕ f₂ ≫ₕ c').restr s := by rw [restr_trans]
        _ ≈ (c.symm ≫ₕ (f₁ ≫ₕ f₂) ≫ₕ c').restr s := by
          simp only [trans_assoc, _root_.refl]
        _ ≈ F₂ := by simp only [F₂, feq, _root_.refl]
      have : F₂ in G := G.mem_of_eqOnSource A (Setoid.symm this)
      exact this }

/--
theorem `StructureGroupoid.restriction_mem_maximalAtlas_subtype` / 定理 `StructureGroupoid.restriction_mem_maximalAtlas_subtype`

English:
theorem StructureGroupoid.restriction_mem_maximalAtlas_subtype
  proof: { carrier := e.source, is_open' := e.open_source : Opens M }
    let t := { carrier := e.target, is_open' := e.open_target : Opens H }
    forall c' in atlas H t,
      e.toHomeomorphSourceTarget.toOpenPartialHomeomorph ≫ₕ c' in G.maximalAtlas s := by
  intro s t c' hc'
  have : Nonempty t := nonempty_coe_sort.mpr (e.mapsTo.nonempty (nonempty_coe_sort.mp hs))
  obtain ⟨x, hc'⟩ := Opens.chart_eq this hc'
  -- As H has only one chart, `chartAt H x` is the identity: i.e., `c'` is the inclusion.
  rw [hc']; rw [(chartAt_self_eq)]
  -- Our expression equals this chart, at least on its source.
  rw [OpenPartialHomeomorph.subtypeRestr_def]; rw [OpenPartialHomeomorph.trans_refl]
  let goal :=
    e.toHomeomorphSourceTarget.toOpenPartialHomeomorph ≫ₕ (t.openPartialHomeomorphSubtypeCoe this)
  have : goal ≈ e.subtypeRestr (s := s) hs :=
    (goal.eqOnSource_iff (e.subtypeRestr (s := s) hs)).mpr
      ⟨by
        simp only [trans_toPartialEquiv, PartialEquiv.trans_source,
          Homeomorph.toOpenPartialHomeomorph_source, toFun_eq_coe,
          Homeomorph.toOpenPartialHomeomorph_apply, Opens.openPartialHomeomorphSubtypeCoe_source,
          preimage_univ, inter_self, subtypeRestr_source, goal, s]
.symm, by intro _ _; rfl⟩ exact Subtype.coe_preimage_self _
  exact G.mem_maximalAtlas_of_eqOnSource (M := s) this (G.subtypeRestr_mem_maximalAtlas he hs)

中文:
定理 StructureGroupoid.restriction_mem_maximalAtlas_subtype
  证明: { carrier := e.source, is_open' := e.open_source : Opens M }
    let t := { carrier := e.target, is_open' := e.open_target : Opens H }
    forall c' in atlas H t,
      e.toHomeomorphSourceTarget.toOpenPartialHomeomorph ≫ₕ c' in G.maximalAtlas s := by
  intro s t c' hc'
  have : Nonempty t := nonempty_coe_sort.mpr (e.mapsTo.nonempty (nonempty_coe_sort.mp hs))
  obtain ⟨x, hc'⟩ := Opens.chart_eq this hc'
  -- As H has only one chart, `chartAt H x` is the identity: i.e., `c'` is the inclusion.
  rw [hc']; rw [(chartAt_self_eq)]
  -- Our expression equals this chart, at least on its source.
  rw [OpenPartialHomeomorph.subtypeRestr_def]; rw [OpenPartialHomeomorph.trans_refl]
  let goal :=
    e.toHomeomorphSourceTarget.toOpenPartialHomeomorph ≫ₕ (t.openPartialHomeomorphSubtypeCoe this)
  have : goal ≈ e.subtypeRestr (s := s) hs :=
    (goal.eqOnSource_iff (e.subtypeRestr (s := s) hs)).mpr
      ⟨by
        simp only [trans_toPartialEquiv, PartialEquiv.trans_source,
          Homeomorph.toOpenPartialHomeomorph_source, toFun_eq_coe,
          Homeomorph.toOpenPartialHomeomorph_apply, Opens.openPartialHomeomorphSubtypeCoe_source,
          preimage_univ, inter_self, subtypeRestr_source, goal, s]
.symm, by intro _ _; rfl⟩ exact Subtype.coe_preimage_self _
  exact G.mem_maximalAtlas_of_eqOnSource (M := s) this (G.subtypeRestr_mem_maximalAtlas he hs)

Depends on / 依赖: carrier, e.open_source, e.source, is_open, open_source, source
-/
theorem StructureGroupoid.restriction_mem_maximalAtlas_subtype
    {e : OpenPartialHomeomorph M H} (he : e in atlas H M)
    (hs : Nonempty e.source) [HasGroupoid M G] [ClosedUnderRestriction G] :
    let s := { carrier := e.source, is_open' := e.open_source : Opens M }
    let t := { carrier := e.target, is_open' := e.open_target : Opens H }
    forall c' in atlas H t,
      e.toHomeomorphSourceTarget.toOpenPartialHomeomorph ≫ₕ c' in G.maximalAtlas s := by
  intro s t c' hc'
  have : Nonempty t := nonempty_coe_sort.mpr (e.mapsTo.nonempty (nonempty_coe_sort.mp hs))
  obtain ⟨x, hc'⟩ := Opens.chart_eq this hc'
  -- As H has only one chart, `chartAt H x` is the identity: i.e., `c'` is the inclusion.
  rw [hc']; rw [(chartAt_self_eq)]
  -- Our expression equals this chart, at least on its source.
  rw [OpenPartialHomeomorph.subtypeRestr_def]; rw [OpenPartialHomeomorph.trans_refl]
  let goal :=
    e.toHomeomorphSourceTarget.toOpenPartialHomeomorph ≫ₕ (t.openPartialHomeomorphSubtypeCoe this)
  have : goal ≈ e.subtypeRestr (s := s) hs :=
    (goal.eqOnSource_iff (e.subtypeRestr (s := s) hs)).mpr
      ⟨by
        simp only [trans_toPartialEquiv, PartialEquiv.trans_source,
          Homeomorph.toOpenPartialHomeomorph_source, toFun_eq_coe,
          Homeomorph.toOpenPartialHomeomorph_apply, Opens.openPartialHomeomorphSubtypeCoe_source,
          preimage_univ, inter_self, subtypeRestr_source, goal, s]
.symm, by intro _ _; rfl⟩ exact Subtype.coe_preimage_self _
  exact G.mem_maximalAtlas_of_eqOnSource (M := s) this (G.subtypeRestr_mem_maximalAtlas he hs)

/--
Definition of `OpenPartialHomeomorph.toStructomorph` / `OpenPartialHomeomorph.toStructomorph` 的定义

English:
definition OpenPartialHomeomorph.toStructomorph
  signature: {e : OpenPartialHomeomorph M H} (he : e in atlas H M)
  body: { carrier := e.source, is_open' := e.open_source }
    let t : Opens H := { carrier := e.target, is_open' := e.open_target }
    Structomorph G s t := by
  intro s t
  by_cases! h : Nonempty e.source
  · exact { e.toHomeomorphSourceTarget with
      mem_groupoid :=
        -- The atlas of H on itself has only one chart, hence c' is the inclusion.
        -- Then, compatibility of `G` *almost* yields our claim --- except that `e` is a chart
        -- on `M` and `c` is one on `s`: we need to show that restricting `e` to `s` and composing
        -- with `c'` yields a chart in the maximal atlas of `s`.
        fun c c' hc hc' => G.compatible_of_mem_maximalAtlas (G.subset_maximalAtlas hc)
          (G.restriction_mem_maximalAtlas_subtype he h c' hc') }
  · have : IsEmpty t := isEmpty_coe_sort.mpr
      (by convert! e.image_source_eq_target ▸ image_eq_empty.mpr (isEmpty_coe_sort.mp h))
    exact { Homeomorph.empty with
      -- `c'` cannot exist: it would be the restriction of `chartAt H x` at some `x ∈ t`.
      mem_groupoid := fun _ c' _ ⟨_, ⟨x, _⟩, _⟩ => (this.false x).elim }

中文:
定义 OpenPartialHomeomorph.toStructomorph
  签名: {e : OpenPartialHomeomorph M H} (he : e in atlas H M)
  定义体: { carrier := e.source, is_open' := e.open_source }
    let t : Opens H := { carrier := e.target, is_open' := e.open_target }
    Structomorph G s t := by
  intro s t
  by_cases! h : Nonempty e.source
  · exact { e.toHomeomorphSourceTarget with
      mem_groupoid :=
        -- The atlas of H on itself has only one chart, hence c' is the inclusion.
        -- Then, compatibility of `G` *almost* yields our claim --- except that `e` is a chart
        -- on `M` and `c` is one on `s`: we need to show that restricting `e` to `s` and composing
        -- with `c'` yields a chart in the maximal atlas of `s`.
        fun c c' hc hc' => G.compatible_of_mem_maximalAtlas (G.subset_maximalAtlas hc)
          (G.restriction_mem_maximalAtlas_subtype he h c' hc') }
  · have : IsEmpty t := isEmpty_coe_sort.mpr
      (by convert! e.image_source_eq_target ▸ image_eq_empty.mpr (isEmpty_coe_sort.mp h))
    exact { Homeomorph.empty with
      -- `c'` cannot exist: it would be the restriction of `chartAt H x` at some `x ∈ t`.
      mem_groupoid := fun _ c' _ ⟨_, ⟨x, _⟩, _⟩ => (this.false x).elim }

Depends on / 依赖: carrier, e.open_source, e.source, is_open, open_source, source
-/
def OpenPartialHomeomorph.toStructomorph {e : OpenPartialHomeomorph M H} (he : e in atlas H M)
    [HasGroupoid M G] [ClosedUnderRestriction G] :
    let s : Opens M := { carrier := e.source, is_open' := e.open_source }
    let t : Opens H := { carrier := e.target, is_open' := e.open_target }
    Structomorph G s t := by
  intro s t
  by_cases! h : Nonempty e.source
  · exact { e.toHomeomorphSourceTarget with
      mem_groupoid :=
        -- The atlas of H on itself has only one chart, hence c' is the inclusion.
        -- Then, compatibility of `G` *almost* yields our claim --- except that `e` is a chart
        -- on `M` and `c` is one on `s`: we need to show that restricting `e` to `s` and composing
        -- with `c'` yields a chart in the maximal atlas of `s`.
        fun c c' hc hc' => G.compatible_of_mem_maximalAtlas (G.subset_maximalAtlas hc)
          (G.restriction_mem_maximalAtlas_subtype he h c' hc') }
  · have : IsEmpty t := isEmpty_coe_sort.mpr
      (by convert! e.image_source_eq_target ▸ image_eq_empty.mpr (isEmpty_coe_sort.mp h))
    exact { Homeomorph.empty with
      -- `c'` cannot exist: it would be the restriction of `chartAt H x` at some `x ∈ t`.
      mem_groupoid := fun _ c' _ ⟨_, ⟨x, _⟩, _⟩ => (this.false x).elim }

end HasGroupoid
