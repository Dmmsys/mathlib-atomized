/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Patrick Massot
-/
module

public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Separation
public import Mathlib.Topology.DenseEmbedding

/-!
# Uniform embeddings of uniform spaces.

Extension of uniform continuous functions.
-/

@[expose] public section


open Filter Function Set Uniformity Topology
open scoped SetRel

section

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w} [UniformSpace α] [UniformSpace β] [UniformSpace γ]
  {f : α -> β}


/--
lemma `isUniformInducing_iff_uniformSpace` / 引理 `isUniformInducing_iff_uniformSpace`

English:
lemma isUniformInducing_iff_uniformSpace
  given: {f : α -> β}
  proof: by
  rw [isUniformInducing_iff]; rw [UniformSpace.ext_iff]; rw [Filter.ext_iff]
  rfl

protected alias ⟨IsUniformInducing.comap_uniformSpace, _⟩ := isUniformInducing_iff_uniformSpace

中文:
引理 isUniformInducing_iff_uniformSpace
  条件: {f : α -> β}
  证明: by
  rw [isUniformInducing_iff]; rw [UniformSpace.ext_iff]; rw [Filter.ext_iff]
  rfl

protected alias ⟨IsUniformInducing.comap_uniformSpace, _⟩ := isUniformInducing_iff_uniformSpace

Depends on / 依赖: Filter, Filter.ext_iff, UniformSpace, UniformSpace.ext_iff, ext_iff, isUniformInducing_iff
-/
lemma isUniformInducing_iff_uniformSpace {f : α -> β} :
    IsUniformInducing f ↔ ‹UniformSpace β›.comap f = ‹UniformSpace α› := by
  rw [isUniformInducing_iff]; rw [UniformSpace.ext_iff]; rw [Filter.ext_iff]
  rfl

protected alias ⟨IsUniformInducing.comap_uniformSpace, _⟩ := isUniformInducing_iff_uniformSpace

/--
lemma `isUniformInducing_iff'` / 引理 `isUniformInducing_iff'`

English:
lemma isUniformInducing_iff'
  given: {f : α -> β}
  proof: by
  rw [isUniformInducing_iff]; rw [UniformContinuous]; rw [tendsto_iff_comap]; rw [le_antisymm_iff]; rw [and_comm]; rfl

中文:
引理 isUniformInducing_iff'
  条件: {f : α -> β}
  证明: by
  rw [isUniformInducing_iff]; rw [UniformContinuous]; rw [tendsto_iff_comap]; rw [le_antisymm_iff]; rw [and_comm]; rfl

Depends on / 依赖: UniformContinuous, and_comm, isUniformInducing_iff, le_antisymm_iff, tendsto_iff_comap
-/
lemma isUniformInducing_iff' {f : α -> β} :
    IsUniformInducing f ↔ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) <= 𝓤 α := by
  rw [isUniformInducing_iff]; rw [UniformContinuous]; rw [tendsto_iff_comap]; rw [le_antisymm_iff]; rw [and_comm]; rfl

/--
lemma `Filter.HasBasis.isUniformInducing_iff` / 引理 `Filter.HasBasis.isUniformInducing_iff`

English:
lemma Filter.HasBasis.isUniformInducing_iff
  statement: {ι ι'} {p : ι -> Prop} {p' : ι' -> Prop} {s s'}
  proof: by
  simp [isUniformInducing_iff', h.uniformContinuous_iff h', (h'.comap _).le_basis_iff h, subset_def]

中文:
引理 Filter.HasBasis.isUniformInducing_iff
  结论: {ι ι'} {p : ι -> 命题} {p' : ι' -> 命题} {s s'}
  证明: by
  simp [isUniformInducing_iff', h.uniformContinuous_iff h', (h'.comap _).le_basis_iff h, subset_def]
-/
protected lemma Filter.HasBasis.isUniformInducing_iff {ι ι'} {p : ι -> Prop} {p' : ι' -> Prop} {s s'}
    (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α -> β} :
    IsUniformInducing f ↔
      (forall i, p' i -> exists j, p j ∧ forall x y, (x, y) in s j -> (f x, f y) in s' i) ∧
        (forall j, p j -> exists i, p' i ∧ forall x y, (f x, f y) in s' i -> (x, y) in s j) := by
  simp [isUniformInducing_iff', h.uniformContinuous_iff h', (h'.comap _).le_basis_iff h, subset_def]

/--
theorem `IsUniformInducing.mk'` / 定理 `IsUniformInducing.mk'`

English:
theorem IsUniformInducing.mk'
  statement: {f : α -> β}
  proof: ⟨by simp [eq_comm, Filter.ext_iff, subset_def, h]⟩

中文:
定理 IsUniformInducing.mk'
  结论: {f : α -> β}
  证明: ⟨by simp [eq_comm, Filter.ext_iff, subset_def, h]⟩

Depends on / 依赖: Filter, Filter.ext_iff, eq_comm, ext_iff, subset_def
-/
theorem IsUniformInducing.mk' {f : α -> β}
    (h : forall s, s in 𝓤 α ↔ exists t in 𝓤 β, forall x y : α, (f x, f y) in t -> (x, y) in s) : IsUniformInducing f :=
  ⟨by simp [eq_comm, Filter.ext_iff, subset_def, h]⟩

/--
theorem `IsUniformInducing.id` / 定理 `IsUniformInducing.id`

English:
theorem IsUniformInducing.id
  statement: IsUniformInducing (@id α)
  proof: ⟨by rw [← Prod.map_def, Prod.map_id, comap_id]⟩

中文:
定理 IsUniformInducing.id
  结论: IsUniformInducing (@id α)
  证明: ⟨by rw [← Prod.map_def, Prod.map_id, comap_id]⟩

Depends on / 依赖: Prod.map_def, Prod.map_id, comap_id, map_def, map_id
-/
theorem IsUniformInducing.id : IsUniformInducing (@id α) :=
  ⟨by rw [← Prod.map_def, Prod.map_id, comap_id]⟩

/--
theorem `IsUniformInducing.comp` / 定理 `IsUniformInducing.comp`

English:
theorem IsUniformInducing.comp
  statement: {g : β -> γ} (hg : IsUniformInducing g) {f : α -> β}
  proof: ⟨by rw [← hf.1, ← hg.1, comap_comap]; rfl⟩

中文:
定理 IsUniformInducing.comp
  结论: {g : β -> γ} (hg : IsUniformInducing g) {f : α -> β}
  证明: ⟨by rw [← hf.1, ← hg.1, comap_comap]; rfl⟩

Depends on / 依赖: comap_comap
-/
theorem IsUniformInducing.comp {g : β -> γ} (hg : IsUniformInducing g) {f : α -> β}
    (hf : IsUniformInducing f) : IsUniformInducing (g ∘ f) :=
  ⟨by rw [← hf.1, ← hg.1, comap_comap]; rfl⟩

/--
theorem `IsUniformInducing.of_comp_iff` / 定理 `IsUniformInducing.of_comp_iff`

English:
theorem IsUniformInducing.of_comp_iff
  given: {g : β -> γ} (hg : IsUniformInducing g) {f : α -> β}
  proof: by
  refine ⟨fun h => ?_, hg.comp⟩
  rw [isUniformInducing_iff]; rw [← hg.comap_uniformity]; rw [comap_comap]; rw [← h.comap_uniformity]; rw [Function.comp_def]; rw [Function.comp_def]

中文:
定理 IsUniformInducing.of_comp_iff
  条件: {g : β -> γ} (hg : IsUniformInducing g) {f : α -> β}
  证明: by
  refine ⟨fun h => ?_, hg.comp⟩
  rw [isUniformInducing_iff]; rw [← hg.comap_uniformity]; rw [comap_comap]; rw [← h.comap_uniformity]; rw [Function.comp_def]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comap_comap, comap_uniformity, comp_def, h.comap_uniformity, hg.comap_uniformity, hg.comp, isUniformInducing_iff
-/
theorem IsUniformInducing.of_comp_iff {g : β -> γ} (hg : IsUniformInducing g) {f : α -> β} :
    IsUniformInducing (g ∘ f) ↔ IsUniformInducing f := by
  refine ⟨fun h => ?_, hg.comp⟩
  rw [isUniformInducing_iff]; rw [← hg.comap_uniformity]; rw [comap_comap]; rw [← h.comap_uniformity]; rw [Function.comp_def]; rw [Function.comp_def]

/--
theorem `IsUniformInducing.basis_uniformity` / 定理 `IsUniformInducing.basis_uniformity`

English:
theorem IsUniformInducing.basis_uniformity
  statement: {f : α -> β} (hf : IsUniformInducing f) {ι : Sort*}
  proof: hf.1 ▸ H.comap _

中文:
定理 IsUniformInducing.basis_uniformity
  结论: {f : α -> β} (hf : IsUniformInducing f) {ι : Sort*}
  证明: hf.1 ▸ H.comap _

Depends on / 依赖: H.comap
-/
theorem IsUniformInducing.basis_uniformity {f : α -> β} (hf : IsUniformInducing f) {ι : Sort*}
    {p : ι -> Prop} {s : ι -> Set (β × β)} (H : (𝓤 β).HasBasis p s) :
    (𝓤 α).HasBasis p fun i => Prod.map f f ⁻¹' s i :=
  hf.1 ▸ H.comap _

/--
theorem `IsUniformInducing.cauchy_map_iff` / 定理 `IsUniformInducing.cauchy_map_iff`

English:
theorem IsUniformInducing.cauchy_map_iff
  given: {f : α -> β} (hf : IsUniformInducing f) {F : Filter α}
  proof: by
  simp only [Cauchy, map_neBot_iff, prod_map_map_eq, map_le_iff_le_comap, ← hf.comap_uniformity]

中文:
定理 IsUniformInducing.cauchy_map_iff
  条件: {f : α -> β} (hf : IsUniformInducing f) {F : Filter α}
  证明: by
  simp only [Cauchy, map_neBot_iff, prod_map_map_eq, map_le_iff_le_comap, ← hf.comap_uniformity]

Depends on / 依赖: Cauchy, comap_uniformity, hf.comap_uniformity, map_le_iff_le_comap, map_neBot_iff, prod_map_map_eq
-/
theorem IsUniformInducing.cauchy_map_iff {f : α -> β} (hf : IsUniformInducing f) {F : Filter α} :
    Cauchy (map f F) ↔ Cauchy F := by
  simp only [Cauchy, map_neBot_iff, prod_map_map_eq, map_le_iff_le_comap, ← hf.comap_uniformity]

/--
theorem `IsUniformInducing.of_comp` / 定理 `IsUniformInducing.of_comp`

English:
theorem IsUniformInducing.of_comp
  statement: {f : α -> β} {g : β -> γ} (hf : UniformContinuous f)
  proof: by
  refine ⟨le_antisymm ?_ hf.le_comap⟩
  rw [← hgf.1]; rw [← Prod.map_def]; rw [← Prod.map_def]; rw [← Prod.map_comp_map f f g g]; rw [← comap_comap]
  exact comap_mono hg.le_comap

中文:
定理 IsUniformInducing.of_comp
  结论: {f : α -> β} {g : β -> γ} (hf : UniformContinuous f)
  证明: by
  refine ⟨le_antisymm ?_ hf.le_comap⟩
  rw [← hgf.1]; rw [← Prod.map_def]; rw [← Prod.map_def]; rw [← Prod.map_comp_map f f g g]; rw [← comap_comap]
  exact comap_mono hg.le_comap

Depends on / 依赖: Prod.map_comp_map, Prod.map_def, comap_comap, comap_mono, hf.le_comap, hg.le_comap, le_antisymm, le_comap, map_comp_map, map_def
-/
theorem IsUniformInducing.of_comp {f : α -> β} {g : β -> γ} (hf : UniformContinuous f)
    (hg : UniformContinuous g) (hgf : IsUniformInducing (g ∘ f)) : IsUniformInducing f := by
  refine ⟨le_antisymm ?_ hf.le_comap⟩
  rw [← hgf.1]; rw [← Prod.map_def]; rw [← Prod.map_def]; rw [← Prod.map_comp_map f f g g]; rw [← comap_comap]
  exact comap_mono hg.le_comap

/--
theorem `IsUniformInducing.uniformContinuous` / 定理 `IsUniformInducing.uniformContinuous`

English:
theorem IsUniformInducing.uniformContinuous
  given: {f : α -> β} (hf : IsUniformInducing f)
  proof: (isUniformInducing_iff'.1 hf).1

中文:
定理 IsUniformInducing.uniformContinuous
  条件: {f : α -> β} (hf : IsUniformInducing f)
  证明: (isUniformInducing_iff'.1 hf).1

Depends on / 依赖: isUniformInducing_iff
-/
theorem IsUniformInducing.uniformContinuous {f : α -> β} (hf : IsUniformInducing f) :
    UniformContinuous f := (isUniformInducing_iff'.1 hf).1

/--
theorem `IsUniformInducing.uniformContinuous_iff` / 定理 `IsUniformInducing.uniformContinuous_iff`

English:
theorem IsUniformInducing.uniformContinuous_iff
  given: {f : α -> β} {g : β -> γ} (hg : IsUniformInducing g)
  proof: by
  dsimp only [UniformContinuous, Tendsto]
  simp only [← hg.comap_uniformity, ← map_le_iff_le_comap, Filter.map_map, Function.comp_def]

@[deprecated (since := "2026-03-17")]
alias IsUniformInducing.isUniformInducing_comp_iff := IsUniformInducing.of_comp_iff

中文:
定理 IsUniformInducing.uniformContinuous_iff
  条件: {f : α -> β} {g : β -> γ} (hg : IsUniformInducing g)
  证明: by
  dsimp only [UniformContinuous, Tendsto]
  simp only [← hg.comap_uniformity, ← map_le_iff_le_comap, Filter.map_map, Function.comp_def]

@[deprecated (since := "2026-03-17")]
alias IsUniformInducing.isUniformInducing_comp_iff := IsUniformInducing.of_comp_iff

Depends on / 依赖: Filter, Filter.map_map, Function, Function.comp_def, Tendsto, UniformContinuous, comap_uniformity, comp_def, hg.comap_uniformity, map_le_iff_le_comap, map_map
-/
theorem IsUniformInducing.uniformContinuous_iff {f : α -> β} {g : β -> γ} (hg : IsUniformInducing g) :
    UniformContinuous f ↔ UniformContinuous (g ∘ f) := by
  dsimp only [UniformContinuous, Tendsto]
  simp only [← hg.comap_uniformity, ← map_le_iff_le_comap, Filter.map_map, Function.comp_def]

@[deprecated (since := "2026-03-17")]
alias IsUniformInducing.isUniformInducing_comp_iff := IsUniformInducing.of_comp_iff

/--
theorem `IsUniformInducing.uniformContinuousOn_iff` / 定理 `IsUniformInducing.uniformContinuousOn_iff`

English:
theorem IsUniformInducing.uniformContinuousOn_iff
  statement: {f : α -> β} {g : β -> γ} {S : Set α}
  proof: by
  dsimp only [UniformContinuousOn, Tendsto]
  rw [← hg.comap_uniformity]; rw [← map_le_iff_le_comap]; rw [Filter.map_map]; rw [comp_def]; rw [comp_def]

中文:
定理 IsUniformInducing.uniformContinuousOn_iff
  结论: {f : α -> β} {g : β -> γ} {S : Set α}
  证明: by
  dsimp only [UniformContinuousOn, Tendsto]
  rw [← hg.comap_uniformity]; rw [← map_le_iff_le_comap]; rw [Filter.map_map]; rw [comp_def]; rw [comp_def]

Depends on / 依赖: Filter, Filter.map_map, Tendsto, UniformContinuousOn, comap_uniformity, comp_def, hg.comap_uniformity, map_le_iff_le_comap, map_map
-/
theorem IsUniformInducing.uniformContinuousOn_iff {f : α -> β} {g : β -> γ} {S : Set α}
    (hg : IsUniformInducing g) :
    UniformContinuousOn f S ↔ UniformContinuousOn (g ∘ f) S := by
  dsimp only [UniformContinuousOn, Tendsto]
  rw [← hg.comap_uniformity]; rw [← map_le_iff_le_comap]; rw [Filter.map_map]; rw [comp_def]; rw [comp_def]

/--
theorem `IsUniformInducing.isInducing` / 定理 `IsUniformInducing.isInducing`

English:
theorem IsUniformInducing.isInducing
  given: {f : α -> β} (h : IsUniformInducing f)
  statement: IsInducing f
  proof: by
  obtain rfl := h.comap_uniformSpace
  exact .induced f

中文:
定理 IsUniformInducing.isInducing
  条件: {f : α -> β} (h : IsUniformInducing f)
  结论: IsInducing f
  证明: by
  obtain rfl := h.comap_uniformSpace
  exact .induced f

Depends on / 依赖: comap_uniformSpace, h.comap_uniformSpace, induced
-/
theorem IsUniformInducing.isInducing {f : α -> β} (h : IsUniformInducing f) : IsInducing f := by
  obtain rfl := h.comap_uniformSpace
  exact .induced f

/--
theorem `IsUniformInducing.prod` / 定理 `IsUniformInducing.prod`

English:
theorem IsUniformInducing.prod
  statement: {α' : Type*} {β' : Type*} [UniformSpace α'] [UniformSpace β']
  proof: ⟨by simp [Function.comp_def, uniformity_prod, ← h₁.1, ← h₂.1, comap_inf, comap_comap]⟩

中文:
定理 IsUniformInducing.prod
  结论: {α' : 类型} {β' : 类型} [UniformSpace α'] [UniformSpace β']
  证明: ⟨by simp [Function.comp_def, uniformity_prod, ← h₁.1, ← h₂.1, comap_inf, comap_comap]⟩

Depends on / 依赖: Function, Function.comp_def, comap_comap, comap_inf, comp_def, uniformity_prod
-/
theorem IsUniformInducing.prod {α' : Type*} {β' : Type*} [UniformSpace α'] [UniformSpace β']
    {e₁ : α -> α'} {e₂ : β -> β'} (h₁ : IsUniformInducing e₁) (h₂ : IsUniformInducing e₂) :
    IsUniformInducing fun p : α × β => (e₁ p.1, e₂ p.2) :=
  ⟨by simp [Function.comp_def, uniformity_prod, ← h₁.1, ← h₂.1, comap_inf, comap_comap]⟩

/--
lemma `IsUniformInducing.isDenseInducing` / 引理 `IsUniformInducing.isDenseInducing`

English:
lemma IsUniformInducing.isDenseInducing
  given: (h : IsUniformInducing f) (hd : DenseRange f)
  proof: h.isInducing
  dense := hd

中文:
引理 IsUniformInducing.isDenseInducing
  条件: (h : IsUniformInducing f) (hd : DenseRange f)
  证明: h.isInducing
  dense := hd

Depends on / 依赖: h.isInducing, isInducing
-/
lemma IsUniformInducing.isDenseInducing (h : IsUniformInducing f) (hd : DenseRange f) :
    IsDenseInducing f where
  toIsInducing := h.isInducing
  dense := hd

/--
lemma `SeparationQuotient.isUniformInducing_mk` / 引理 `SeparationQuotient.isUniformInducing_mk`

English:
lemma SeparationQuotient.isUniformInducing_mk
  proof: ⟨comap_mk_uniformity⟩

中文:
引理 SeparationQuotient.isUniformInducing_mk
  证明: ⟨comap_mk_uniformity⟩

Depends on / 依赖: comap_mk_uniformity
-/
lemma SeparationQuotient.isUniformInducing_mk :
    IsUniformInducing (mk : α -> SeparationQuotient α) :=
  ⟨comap_mk_uniformity⟩

/--
theorem `IsUniformInducing.injective` / 定理 `IsUniformInducing.injective`

English:
theorem IsUniformInducing.injective
  given: [T0Space α] {f : α -> β} (h : IsUniformInducing f)
  proof: h.isInducing.injective

中文:
定理 IsUniformInducing.injective
  条件: [T0Space α] {f : α -> β} (h : IsUniformInducing f)
  证明: h.isInducing.injective
-/
protected theorem IsUniformInducing.injective [T0Space α] {f : α -> β} (h : IsUniformInducing f) :
    Injective f :=
  h.isInducing.injective


/--
theorem `isUniformEmbedding_iff'` / 定理 `isUniformEmbedding_iff'`

English:
theorem isUniformEmbedding_iff'
  given: {f : α -> β}
  proof: by
  rw [isUniformEmbedding_iff]; rw [and_comm]; rw [isUniformInducing_iff']

中文:
定理 isUniformEmbedding_iff'
  条件: {f : α -> β}
  证明: by
  rw [isUniformEmbedding_iff]; rw [and_comm]; rw [isUniformInducing_iff']

Depends on / 依赖: and_comm, isUniformEmbedding_iff, isUniformInducing_iff
-/
theorem isUniformEmbedding_iff' {f : α -> β} :
    IsUniformEmbedding f ↔
      Injective f ∧ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) <= 𝓤 α := by
  rw [isUniformEmbedding_iff]; rw [and_comm]; rw [isUniformInducing_iff']

/--
theorem `Filter.HasBasis.isUniformEmbedding_iff'` / 定理 `Filter.HasBasis.isUniformEmbedding_iff'`

English:
theorem Filter.HasBasis.isUniformEmbedding_iff'
  statement: {ι ι'} {p : ι -> Prop} {p' : ι' -> Prop} {s s'}
  proof: by
  rw [isUniformEmbedding_iff]; rw [and_comm]; rw [h.isUniformInducing_iff h']

中文:
定理 Filter.HasBasis.isUniformEmbedding_iff'
  结论: {ι ι'} {p : ι -> 命题} {p' : ι' -> 命题} {s s'}
  证明: by
  rw [isUniformEmbedding_iff]; rw [and_comm]; rw [h.isUniformInducing_iff h']

Depends on / 依赖: and_comm, h.isUniformInducing_iff, isUniformEmbedding_iff, isUniformInducing_iff
-/
theorem Filter.HasBasis.isUniformEmbedding_iff' {ι ι'} {p : ι -> Prop} {p' : ι' -> Prop} {s s'}
    (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α -> β} :
    IsUniformEmbedding f ↔ Injective f ∧
      (forall i, p' i -> exists j, p j ∧ forall x y, (x, y) in s j -> (f x, f y) in s' i) ∧
        (forall j, p j -> exists i, p' i ∧ forall x y, (f x, f y) in s' i -> (x, y) in s j) := by
  rw [isUniformEmbedding_iff]; rw [and_comm]; rw [h.isUniformInducing_iff h']

/--
theorem `Filter.HasBasis.isUniformEmbedding_iff` / 定理 `Filter.HasBasis.isUniformEmbedding_iff`

English:
theorem Filter.HasBasis.isUniformEmbedding_iff
  statement: {ι ι'} {p : ι -> Prop} {p' : ι' -> Prop} {s s'}
  proof: by
  simp only [h.isUniformEmbedding_iff' h', h.uniformContinuous_iff h']

中文:
定理 Filter.HasBasis.isUniformEmbedding_iff
  结论: {ι ι'} {p : ι -> 命题} {p' : ι' -> 命题} {s s'}
  证明: by
  simp only [h.isUniformEmbedding_iff' h', h.uniformContinuous_iff h']

Depends on / 依赖: h.isUniformEmbedding_iff, h.uniformContinuous_iff, isUniformEmbedding_iff, uniformContinuous_iff
-/
theorem Filter.HasBasis.isUniformEmbedding_iff {ι ι'} {p : ι -> Prop} {p' : ι' -> Prop} {s s'}
    (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α -> β} :
    IsUniformEmbedding f ↔ Injective f ∧ UniformContinuous f ∧
      (forall j, p j -> exists i, p' i ∧ forall x y, (f x, f y) in s' i -> (x, y) in s j) := by
  simp only [h.isUniformEmbedding_iff' h', h.uniformContinuous_iff h']

/--
theorem `isUniformEmbedding_subtype_val` / 定理 `isUniformEmbedding_subtype_val`

English:
theorem isUniformEmbedding_subtype_val
  given: {p : α -> Prop}
  proof: { comap_uniformity := rfl
    injective := Subtype.val_injective }

中文:
定理 isUniformEmbedding_subtype_val
  条件: {p : α -> 命题}
  证明: { comap_uniformity := rfl
    injective := Subtype.val_injective }

Depends on / 依赖: Subtype, Subtype.val_injective, comap_uniformity, injective, val_injective
-/
theorem isUniformEmbedding_subtype_val {p : α -> Prop} :
    IsUniformEmbedding (Subtype.val : Subtype p -> α) :=
  { comap_uniformity := rfl
    injective := Subtype.val_injective }

/--
theorem `isUniformEmbedding_set_inclusion` / 定理 `isUniformEmbedding_set_inclusion`

English:
theorem isUniformEmbedding_set_inclusion
  given: {s t : Set α} (hst : s subseteq t)
  proof: by rw [uniformity_subtype, uniformity_subtype, comap_comap]; rfl
  injective := inclusion_injective hst

中文:
定理 isUniformEmbedding_set_inclusion
  条件: {s t : Set α} (hst : s subseteq t)
  证明: by rw [uniformity_subtype, uniformity_subtype, comap_comap]; rfl
  injective := inclusion_injective hst

Depends on / 依赖: comap_comap, inclusion_injective, injective, uniformity_subtype
-/
theorem isUniformEmbedding_set_inclusion {s t : Set α} (hst : s subseteq t) :
    IsUniformEmbedding (inclusion hst) where
  comap_uniformity := by rw [uniformity_subtype, uniformity_subtype, comap_comap]; rfl
  injective := inclusion_injective hst

/--
theorem `IsUniformEmbedding.comp` / 定理 `IsUniformEmbedding.comp`

English:
theorem IsUniformEmbedding.comp
  statement: {g : β -> γ} (hg : IsUniformEmbedding g) {f : α -> β}
  proof: hg.isUniformInducing.comp hf.isUniformInducing
  injective := hg.injective.comp hf.injective

中文:
定理 IsUniformEmbedding.comp
  结论: {g : β -> γ} (hg : IsUniformEmbedding g) {f : α -> β}
  证明: hg.isUniformInducing.comp hf.isUniformInducing
  injective := hg.injective.comp hf.injective

Depends on / 依赖: hf.isUniformInducing, hg.isUniformInducing.comp, isUniformInducing
-/
theorem IsUniformEmbedding.comp {g : β -> γ} (hg : IsUniformEmbedding g) {f : α -> β}
    (hf : IsUniformEmbedding f) : IsUniformEmbedding (g ∘ f) where
  toIsUniformInducing := hg.isUniformInducing.comp hf.isUniformInducing
  injective := hg.injective.comp hf.injective

/--
theorem `IsUniformEmbedding.of_comp_iff` / 定理 `IsUniformEmbedding.of_comp_iff`

English:
theorem IsUniformEmbedding.of_comp_iff
  given: {g : β -> γ} (hg : IsUniformEmbedding g) {f : α -> β}
  proof: by
  simp_rw [isUniformEmbedding_iff, hg.isUniformInducing.of_comp_iff, hg.injective.of_comp_iff f]

中文:
定理 IsUniformEmbedding.of_comp_iff
  条件: {g : β -> γ} (hg : IsUniformEmbedding g) {f : α -> β}
  证明: by
  simp_rw [isUniformEmbedding_iff, hg.isUniformInducing.of_comp_iff, hg.injective.of_comp_iff f]

Depends on / 依赖: hg.injective.of_comp_iff, hg.isUniformInducing.of_comp_iff, injective, isUniformEmbedding_iff, isUniformInducing, of_comp_iff, simp_rw
-/
theorem IsUniformEmbedding.of_comp_iff {g : β -> γ} (hg : IsUniformEmbedding g) {f : α -> β} :
    IsUniformEmbedding (g ∘ f) ↔ IsUniformEmbedding f := by
  simp_rw [isUniformEmbedding_iff, hg.isUniformInducing.of_comp_iff, hg.injective.of_comp_iff f]

/--
theorem `IsUniformEmbedding.of_comp` / 定理 `IsUniformEmbedding.of_comp`

English:
theorem IsUniformEmbedding.of_comp
  statement: {f : α -> β} {g : β -> γ} (hf : UniformContinuous f)
  proof: ⟨.of_comp hf hg hgf.isUniformInducing, .of_comp hgf.injective⟩

中文:
定理 IsUniformEmbedding.of_comp
  结论: {f : α -> β} {g : β -> γ} (hf : UniformContinuous f)
  证明: ⟨.of_comp hf hg hgf.isUniformInducing, .of_comp hgf.injective⟩

Depends on / 依赖: hgf.injective, hgf.isUniformInducing, injective, isUniformInducing, of_comp
-/
theorem IsUniformEmbedding.of_comp {f : α -> β} {g : β -> γ} (hf : UniformContinuous f)
    (hg : UniformContinuous g) (hgf : IsUniformEmbedding (g ∘ f)) : IsUniformEmbedding f :=
  ⟨.of_comp hf hg hgf.isUniformInducing, .of_comp hgf.injective⟩

/--
theorem `Equiv.isUniformEmbedding` / 定理 `Equiv.isUniformEmbedding`

English:
theorem Equiv.isUniformEmbedding
  statement: {α β : Type*} [UniformSpace α] [UniformSpace β] (f : α ≃ β)
  proof: isUniformEmbedding_iff'.2 ⟨f.injective, h₁, by rwa [← Equiv.prodCongr_apply, ← map_equiv_symm]⟩

中文:
定理 Equiv.isUniformEmbedding
  结论: {α β : 类型} [UniformSpace α] [UniformSpace β] (f : α ≃ β)
  证明: isUniformEmbedding_iff'.2 ⟨f.injective, h₁, by rwa [← Equiv.prodCongr_apply, ← map_equiv_symm]⟩

Depends on / 依赖: Equiv.prodCongr_apply, f.injective, injective, isUniformEmbedding_iff, map_equiv_symm, prodCongr_apply
-/
theorem Equiv.isUniformEmbedding {α β : Type*} [UniformSpace α] [UniformSpace β] (f : α ≃ β)
    (h₁ : UniformContinuous f) (h₂ : UniformContinuous f.symm) : IsUniformEmbedding f :=
  isUniformEmbedding_iff'.2 ⟨f.injective, h₁, by rwa [← Equiv.prodCongr_apply, ← map_equiv_symm]⟩

/--
theorem `isUniformEmbedding_inl` / 定理 `isUniformEmbedding_inl`

English:
theorem isUniformEmbedding_inl
  statement: IsUniformEmbedding (Sum.inl : α -> α oplus β)
  proof: isUniformEmbedding_iff'.2 ⟨Sum.inl_injective, uniformContinuous_inl, fun s hs =>
    ⟨Prod.map Sum.inl Sum.inl '' s union range (Prod.map Sum.inr Sum.inr),
      union_mem_sup (image_mem_map hs) range_mem_map,
      fun x h => by simpa [Prod.map_apply'] using h⟩⟩

中文:
定理 isUniformEmbedding_inl
  结论: IsUniformEmbedding (Sum.inl : α -> α oplus β)
  证明: isUniformEmbedding_iff'.2 ⟨Sum.inl_injective, uniformContinuous_inl, fun s hs =>
    ⟨Prod.map Sum.inl Sum.inl '' s union range (Prod.map Sum.inr Sum.inr),
      union_mem_sup (image_mem_map hs) range_mem_map,
      fun x h => by simpa [Prod.map_apply'] using h⟩⟩

Depends on / 依赖: Prod.map, Prod.map_apply, Sum.inl, Sum.inl_injective, Sum.inr, image_mem_map, inl_injective, isUniformEmbedding_iff, map_apply, range_mem_map, uniformContinuous_inl, union_mem_sup
-/
theorem isUniformEmbedding_inl : IsUniformEmbedding (Sum.inl : α -> α oplus β) :=
  isUniformEmbedding_iff'.2 ⟨Sum.inl_injective, uniformContinuous_inl, fun s hs =>
    ⟨Prod.map Sum.inl Sum.inl '' s union range (Prod.map Sum.inr Sum.inr),
      union_mem_sup (image_mem_map hs) range_mem_map,
      fun x h => by simpa [Prod.map_apply'] using h⟩⟩

/--
theorem `isUniformEmbedding_inr` / 定理 `isUniformEmbedding_inr`

English:
theorem isUniformEmbedding_inr
  statement: IsUniformEmbedding (Sum.inr : β -> α oplus β)
  proof: isUniformEmbedding_iff'.2 ⟨Sum.inr_injective, uniformContinuous_inr, fun s hs =>
    ⟨range (Prod.map Sum.inl Sum.inl) union Prod.map Sum.inr Sum.inr '' s,
      union_mem_sup range_mem_map (image_mem_map hs),
      fun x h => by simpa [Prod.map_apply'] using h⟩⟩

中文:
定理 isUniformEmbedding_inr
  结论: IsUniformEmbedding (Sum.inr : β -> α oplus β)
  证明: isUniformEmbedding_iff'.2 ⟨Sum.inr_injective, uniformContinuous_inr, fun s hs =>
    ⟨range (Prod.map Sum.inl Sum.inl) union Prod.map Sum.inr Sum.inr '' s,
      union_mem_sup range_mem_map (image_mem_map hs),
      fun x h => by simpa [Prod.map_apply'] using h⟩⟩

Depends on / 依赖: Prod.map, Prod.map_apply, Sum.inl, Sum.inr, Sum.inr_injective, image_mem_map, inr_injective, isUniformEmbedding_iff, map_apply, range_mem_map, uniformContinuous_inr, union_mem_sup
-/
theorem isUniformEmbedding_inr : IsUniformEmbedding (Sum.inr : β -> α oplus β) :=
  isUniformEmbedding_iff'.2 ⟨Sum.inr_injective, uniformContinuous_inr, fun s hs =>
    ⟨range (Prod.map Sum.inl Sum.inl) union Prod.map Sum.inr Sum.inr '' s,
      union_mem_sup range_mem_map (image_mem_map hs),
      fun x h => by simpa [Prod.map_apply'] using h⟩⟩

/--
theorem `IsUniformInducing.isUniformEmbedding` / 定理 `IsUniformInducing.isUniformEmbedding`

English:
theorem IsUniformInducing.isUniformEmbedding
  statement: [T0Space α] {f : α -> β}
  proof: ⟨hf, hf.isInducing.injective⟩

中文:
定理 IsUniformInducing.isUniformEmbedding
  结论: [T0Space α] {f : α -> β}
  证明: ⟨hf, hf.isInducing.injective⟩
-/
protected theorem IsUniformInducing.isUniformEmbedding [T0Space α] {f : α -> β}
    (hf : IsUniformInducing f) : IsUniformEmbedding f :=
  ⟨hf, hf.isInducing.injective⟩

/--
theorem `isUniformEmbedding_iff_isUniformInducing` / 定理 `isUniformEmbedding_iff_isUniformInducing`

English:
theorem isUniformEmbedding_iff_isUniformInducing
  given: [T0Space α] {f : α -> β}
  proof: ⟨IsUniformEmbedding.isUniformInducing, IsUniformInducing.isUniformEmbedding⟩

中文:
定理 isUniformEmbedding_iff_isUniformInducing
  条件: [T0Space α] {f : α -> β}
  证明: ⟨IsUniformEmbedding.isUniformInducing, IsUniformInducing.isUniformEmbedding⟩

Depends on / 依赖: IsUniformEmbedding, IsUniformEmbedding.isUniformInducing, IsUniformInducing, IsUniformInducing.isUniformEmbedding, isUniformEmbedding, isUniformInducing
-/
theorem isUniformEmbedding_iff_isUniformInducing [T0Space α] {f : α -> β} :
    IsUniformEmbedding f ↔ IsUniformInducing f :=
  ⟨IsUniformEmbedding.isUniformInducing, IsUniformInducing.isUniformEmbedding⟩

/--
theorem `comap_uniformity_of_spaced_out` / 定理 `comap_uniformity_of_spaced_out`

English:
theorem comap_uniformity_of_spaced_out
  statement: {α} {f : α -> β} {s : Set (β × β)} (hs : s in 𝓤 β)
  proof: by
  refine le_antisymm ?_ (@refl_le_uniformity α (UniformSpace.comap f _))
  calc
    comap (Prod.map f f) (𝓤 β) <= comap (Prod.map f f) (𝓟 s) := comap_mono (le_principal_iff.2 hs)
    _ = 𝓟 (Prod.map f f ⁻¹' s) := comap_principal
    _ <= 𝓟 SetRel.id := principal_mono.2 ?_
  rintro ⟨x, y⟩; simpa [

中文:
定理 comap_uniformity_of_spaced_out
  结论: {α} {f : α -> β} {s : Set (β × β)} (hs : s in 𝓤 β)
  证明: by
  refine le_antisymm ?_ (@refl_le_uniformity α (UniformSpace.comap f _))
  calc
    comap (Prod.map f f) (𝓤 β) <= comap (Prod.map f f) (𝓟 s) := comap_mono (le_principal_iff.2 hs)
    _ = 𝓟 (Prod.map f f ⁻¹' s) := comap_principal
    _ <= 𝓟 SetRel.id := principal_mono.2 ?_
  rintro ⟨x, y⟩; simpa [

Depends on / 依赖: Prod.map, SetRel, SetRel.id, UniformSpace, UniformSpace.comap, comap_mono, comap_principal, le_antisymm, le_principal_iff, not_imp_not, principal_mono, refl_le_uniformity
-/
theorem comap_uniformity_of_spaced_out {α} {f : α -> β} {s : Set (β × β)} (hs : s in 𝓤 β)
    (hf : Pairwise fun x y => (f x, f y) ∉ s) : comap (Prod.map f f) (𝓤 β) = 𝓟 SetRel.id := by
  refine le_antisymm ?_ (@refl_le_uniformity α (UniformSpace.comap f _))
  calc
    comap (Prod.map f f) (𝓤 β) <= comap (Prod.map f f) (𝓟 s) := comap_mono (le_principal_iff.2 hs)
    _ = 𝓟 (Prod.map f f ⁻¹' s) := comap_principal
    _ <= 𝓟 SetRel.id := principal_mono.2 ?_
  rintro ⟨x, y⟩; simpa [not_imp_not] using @hf x y

/--
theorem `isUniformEmbedding_of_spaced_out` / 定理 `isUniformEmbedding_of_spaced_out`

English:
theorem isUniformEmbedding_of_spaced_out
  statement: {α} {f : α -> β} {s : Set (β × β)} (hs : s in 𝓤 β)
  proof: by
  let _ : UniformSpace α := ⊥; have := discreteTopology_bot α
  exact IsUniformInducing.isUniformEmbedding ⟨comap_uniformity_of_spaced_out hs hf⟩

中文:
定理 isUniformEmbedding_of_spaced_out
  结论: {α} {f : α -> β} {s : Set (β × β)} (hs : s in 𝓤 β)
  证明: by
  let _ : UniformSpace α := ⊥; have := discreteTopology_bot α
  exact IsUniformInducing.isUniformEmbedding ⟨comap_uniformity_of_spaced_out hs hf⟩

Depends on / 依赖: IsUniformInducing, IsUniformInducing.isUniformEmbedding, UniformSpace, comap_uniformity_of_spaced_out, discreteTopology_bot, isUniformEmbedding
-/
theorem isUniformEmbedding_of_spaced_out {α} {f : α -> β} {s : Set (β × β)} (hs : s in 𝓤 β)
    (hf : Pairwise fun x y => (f x, f y) ∉ s) : @IsUniformEmbedding α β ⊥ ‹_› f := by
  let _ : UniformSpace α := ⊥; have := discreteTopology_bot α
  exact IsUniformInducing.isUniformEmbedding ⟨comap_uniformity_of_spaced_out hs hf⟩

/--
lemma `IsUniformEmbedding.isEmbedding` / 引理 `IsUniformEmbedding.isEmbedding`

English:
lemma IsUniformEmbedding.isEmbedding
  given: {f : α -> β} (h : IsUniformEmbedding f)
  proof: h.toIsUniformInducing.isInducing
  injective := h.injective

中文:
引理 IsUniformEmbedding.isEmbedding
  条件: {f : α -> β} (h : IsUniformEmbedding f)
  证明: h.toIsUniformInducing.isInducing
  injective := h.injective
-/
protected lemma IsUniformEmbedding.isEmbedding {f : α -> β} (h : IsUniformEmbedding f) :
    IsEmbedding f where
  toIsInducing := h.toIsUniformInducing.isInducing
  injective := h.injective

/--
theorem `IsUniformEmbedding.isDenseEmbedding` / 定理 `IsUniformEmbedding.isDenseEmbedding`

English:
theorem IsUniformEmbedding.isDenseEmbedding
  statement: {f : α -> β} (h : IsUniformEmbedding f)
  proof: { h.isEmbedding with dense := hd }

中文:
定理 IsUniformEmbedding.isDenseEmbedding
  结论: {f : α -> β} (h : IsUniformEmbedding f)
  证明: { h.isEmbedding with dense := hd }

Depends on / 依赖: h.isEmbedding, isEmbedding
-/
theorem IsUniformEmbedding.isDenseEmbedding {f : α -> β} (h : IsUniformEmbedding f)
    (hd : DenseRange f) : IsDenseEmbedding f :=
  { h.isEmbedding with dense := hd }

/--
theorem `isClosedEmbedding_of_spaced_out` / 定理 `isClosedEmbedding_of_spaced_out`

English:
theorem isClosedEmbedding_of_spaced_out
  statement: {α} [TopologicalSpace α] [DiscreteTopology α]
  proof: by
  rcases @DiscreteTopology.eq_bot α _ _ with rfl; let _ : UniformSpace α := ⊥
  exact
    { (isUniformEmbedding_of_spaced_out hs hf).isEmbedding with
      isClosed_range := isClosed_range_of_spaced_out hs hf }

中文:
定理 isClosedEmbedding_of_spaced_out
  结论: {α} [TopologicalSpace α] [DiscreteTopology α]
  证明: by
  rcases @DiscreteTopology.eq_bot α _ _ with rfl; let _ : UniformSpace α := ⊥
  exact
    { (isUniformEmbedding_of_spaced_out hs hf).isEmbedding with
      isClosed_range := isClosed_range_of_spaced_out hs hf }

Depends on / 依赖: DiscreteTopology, DiscreteTopology.eq_bot, UniformSpace, eq_bot, isClosed_range, isClosed_range_of_spaced_out, isEmbedding, isUniformEmbedding_of_spaced_out
-/
theorem isClosedEmbedding_of_spaced_out {α} [TopologicalSpace α] [DiscreteTopology α]
    [T0Space β] {f : α -> β} {s : Set (β × β)} (hs : s in 𝓤 β)
    (hf : Pairwise fun x y => (f x, f y) ∉ s) : IsClosedEmbedding f := by
  rcases @DiscreteTopology.eq_bot α _ _ with rfl; let _ : UniformSpace α := ⊥
  exact
    { (isUniformEmbedding_of_spaced_out hs hf).isEmbedding with
      isClosed_range := isClosed_range_of_spaced_out hs hf }

/--
theorem `closure_image_mem_nhds_of_isUniformInducing` / 定理 `closure_image_mem_nhds_of_isUniformInducing`

English:
theorem closure_image_mem_nhds_of_isUniformInducing
  statement: {s : Set (α × α)} {e : α -> β} (b : β)
  proof: by
  obtain ⟨U, ⟨hU, hUo, hsymm⟩, hs⟩ :
    exists U, (U in 𝓤 β ∧ IsOpen U ∧ SetRel.IsSymm U) ∧ Prod.map e e ⁻¹' U subseteq s := by
      rwa [← he₁.comap_uniformity, (uniformity_hasBasis_open_symmetric.comap _).mem_iff] at hs
  rcases he₂.dense.mem_nhds (UniformSpace.ball_mem_nhds b hU) with ⟨a, ha

中文:
定理 closure_image_mem_nhds_of_isUniformInducing
  结论: {s : Set (α × α)} {e : α -> β} (b : β)
  证明: by
  obtain ⟨U, ⟨hU, hUo, hsymm⟩, hs⟩ :
    exists U, (U in 𝓤 β ∧ IsOpen U ∧ SetRel.IsSymm U) ∧ Prod.map e e ⁻¹' U subseteq s := by
      rwa [← he₁.comap_uniformity, (uniformity_hasBasis_open_symmetric.comap _).mem_iff] at hs
  rcases he₂.dense.mem_nhds (UniformSpace.ball_mem_nhds b hU) with ⟨a, ha

Depends on / 依赖: IsOpen, IsSymm, Prod.map, SetRel, SetRel.IsSymm, UniformSpace, UniformSpace.ball, UniformSpace.ball_mem_nhds, UniformSpace.ball_mono, UniformSpace.isOpen_ball, ball_mem_nhds, ball_mono, closure_mono, comap_uniformity, dense.mem_nhds, ho.mem_nhds, image_mono, isOpen_ball, mem_iff, mem_nhds
-/
theorem closure_image_mem_nhds_of_isUniformInducing {s : Set (α × α)} {e : α -> β} (b : β)
    (he₁ : IsUniformInducing e) (he₂ : IsDenseInducing e) (hs : s in 𝓤 α) :
    exists a, closure (e '' { a' | (a, a') in s }) in 𝓝 b := by
  obtain ⟨U, ⟨hU, hUo, hsymm⟩, hs⟩ :
    exists U, (U in 𝓤 β ∧ IsOpen U ∧ SetRel.IsSymm U) ∧ Prod.map e e ⁻¹' U subseteq s := by
      rwa [← he₁.comap_uniformity, (uniformity_hasBasis_open_symmetric.comap _).mem_iff] at hs
  rcases he₂.dense.mem_nhds (UniformSpace.ball_mem_nhds b hU) with ⟨a, ha⟩
  refine ⟨a, mem_of_superset ?_ (closure_mono <| image_mono <| UniformSpace.ball_mono hs a)⟩
  have ho : IsOpen (UniformSpace.ball (e a) U) := UniformSpace.isOpen_ball (e a) hUo
  refine mem_of_superset (ho.mem_nhds <| UniformSpace.mem_ball_symmetry.2 ha) fun y hy => ?_
  refine mem_closure_iff_nhds.2 fun V hV => ?_
  rcases he₂.dense.mem_nhds (inter_mem hV (ho.mem_nhds hy)) with ⟨x, hxV, hxU⟩
  exact ⟨e x, hxV, mem_image_of_mem e hxU⟩

/--
theorem `isUniformEmbedding_subtypeEmb` / 定理 `isUniformEmbedding_subtypeEmb`

English:
theorem isUniformEmbedding_subtypeEmb
  statement: (p : α -> Prop) {e : α -> β} (ue : IsUniformEmbedding e)
  proof: { comap_uniformity := by
      simp [comap_comap, Function.comp_def, IsDenseEmbedding.subtypeEmb, uniformity_subtype,
        ue.comap_uniformity.symm]
    injective := (de.subtype p).injective }

中文:
定理 isUniformEmbedding_subtypeEmb
  结论: (p : α -> 命题) {e : α -> β} (ue : IsUniformEmbedding e)
  证明: { comap_uniformity := by
      simp [comap_comap, Function.comp_def, IsDenseEmbedding.subtypeEmb, uniformity_subtype,
        ue.comap_uniformity.symm]
    injective := (de.subtype p).injective }

Depends on / 依赖: Function, Function.comp_def, IsDenseEmbedding, IsDenseEmbedding.subtypeEmb, comap_comap, comap_uniformity, comp_def, de.subtype, injective, subtype, subtypeEmb, ue.comap_uniformity.symm, uniformity_subtype
-/
theorem isUniformEmbedding_subtypeEmb (p : α -> Prop) {e : α -> β} (ue : IsUniformEmbedding e)
    (de : IsDenseEmbedding e) : IsUniformEmbedding (IsDenseEmbedding.subtypeEmb p e) :=
  { comap_uniformity := by
      simp [comap_comap, Function.comp_def, IsDenseEmbedding.subtypeEmb, uniformity_subtype,
        ue.comap_uniformity.symm]
    injective := (de.subtype p).injective }

/--
theorem `IsUniformEmbedding.prod` / 定理 `IsUniformEmbedding.prod`

English:
theorem IsUniformEmbedding.prod
  statement: {α' : Type*} {β' : Type*} [UniformSpace α'] [UniformSpace β']
  proof: h₁.isUniformInducing.prod h₂.isUniformInducing
  injective := h₁.injective.prodMap h₂.injective

中文:
定理 IsUniformEmbedding.prod
  结论: {α' : 类型} {β' : 类型} [UniformSpace α'] [UniformSpace β']
  证明: h₁.isUniformInducing.prod h₂.isUniformInducing
  injective := h₁.injective.prodMap h₂.injective

Depends on / 依赖: isUniformInducing, isUniformInducing.prod
-/
theorem IsUniformEmbedding.prod {α' : Type*} {β' : Type*} [UniformSpace α'] [UniformSpace β']
    {e₁ : α -> α'} {e₂ : β -> β'} (h₁ : IsUniformEmbedding e₁) (h₂ : IsUniformEmbedding e₂) :
    IsUniformEmbedding fun p : α × β => (e₁ p.1, e₂ p.2) where
  toIsUniformInducing := h₁.isUniformInducing.prod h₂.isUniformInducing
  injective := h₁.injective.prodMap h₂.injective

/--
theorem `isComplete_image_iff` / 定理 `isComplete_image_iff`

English:
theorem isComplete_image_iff
  given: {m : α -> β} {s : Set α} (hm : IsUniformInducing m)
  proof: by
.filter_map_Iic have fact1 : SurjOn (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 <| m '' s) := surjOn_image ..
.filter_map_Iic have fact2 : MapsTo (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 <| m '' s) := mapsTo_image ..
  simp_rw [IsComplete, imp.swap (a := Cauchy _), ← mem_Iic (b := 𝓟 _), fact1.forall fact2,
    hm.cauch

中文:
定理 isComplete_image_iff
  条件: {m : α -> β} {s : Set α} (hm : IsUniformInducing m)
  证明: by
.filter_map_Iic have fact1 : SurjOn (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 <| m '' s) := surjOn_image ..
.filter_map_Iic have fact2 : MapsTo (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 <| m '' s) := mapsTo_image ..
  simp_rw [IsComplete, imp.swap (a := Cauchy _), ← mem_Iic (b := 𝓟 _), fact1.forall fact2,
    hm.cauch

Depends on / 依赖: Cauchy, IsComplete, MapsTo, SurjOn, cauchy_map_iff, exists_mem_image, fact1.forall, filter_map_Iic, hm.cauchy_map_iff, hm.isInducing.nhds_eq_comap, imp.swap, isInducing, map_le_iff_le_comap, mapsTo_image, mem_Iic, nhds_eq_comap, simp_rw, surjOn_image
-/
theorem isComplete_image_iff {m : α -> β} {s : Set α} (hm : IsUniformInducing m) :
    IsComplete (m '' s) ↔ IsComplete s := by
.filter_map_Iic have fact1 : SurjOn (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 <| m '' s) := surjOn_image ..
.filter_map_Iic have fact2 : MapsTo (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 <| m '' s) := mapsTo_image ..
  simp_rw [IsComplete, imp.swap (a := Cauchy _), ← mem_Iic (b := 𝓟 _), fact1.forall fact2,
    hm.cauchy_map_iff, exists_mem_image, map_le_iff_le_comap, hm.isInducing.nhds_eq_comap]

/--
theorem `IsUniformInducing.isComplete_iff` / 定理 `IsUniformInducing.isComplete_iff`

English:
theorem IsUniformInducing.isComplete_iff
  given: {f : α -> β} {s : Set α} (hf : IsUniformInducing f)
  proof: isComplete_image_iff hf

中文:
定理 IsUniformInducing.isComplete_iff
  条件: {f : α -> β} {s : Set α} (hf : IsUniformInducing f)
  证明: isComplete_image_iff hf

Depends on / 依赖: isComplete_image_iff
-/
theorem IsUniformInducing.isComplete_iff {f : α -> β} {s : Set α} (hf : IsUniformInducing f) :
    IsComplete (f '' s) ↔ IsComplete s := isComplete_image_iff hf

/--
theorem `IsUniformEmbedding.isComplete_iff` / 定理 `IsUniformEmbedding.isComplete_iff`

English:
theorem IsUniformEmbedding.isComplete_iff
  given: {f : α -> β} {s : Set α} (hf : IsUniformEmbedding f)
  proof: hf.isUniformInducing.isComplete_iff

中文:
定理 IsUniformEmbedding.isComplete_iff
  条件: {f : α -> β} {s : Set α} (hf : IsUniformEmbedding f)
  证明: hf.isUniformInducing.isComplete_iff

Depends on / 依赖: hf.isUniformInducing.isComplete_iff, isComplete_iff, isUniformInducing
-/
theorem IsUniformEmbedding.isComplete_iff {f : α -> β} {s : Set α} (hf : IsUniformEmbedding f) :
    IsComplete (f '' s) ↔ IsComplete s := hf.isUniformInducing.isComplete_iff

/--
theorem `Subtype.isComplete_iff` / 定理 `Subtype.isComplete_iff`

English:
theorem Subtype.isComplete_iff
  given: {p : α -> Prop} {s : Set { x // p x }}
  proof: isUniformEmbedding_subtype_val.isComplete_iff.symm

alias ⟨isComplete_of_complete_image, _⟩ := isComplete_image_iff

中文:
定理 Subtype.isComplete_iff
  条件: {p : α -> 命题} {s : Set { x // p x }}
  证明: isUniformEmbedding_subtype_val.isComplete_iff.symm

alias ⟨isComplete_of_complete_image, _⟩ := isComplete_image_iff

Depends on / 依赖: isComplete_iff, isUniformEmbedding_subtype_val, isUniformEmbedding_subtype_val.isComplete_iff.symm
-/
theorem Subtype.isComplete_iff {p : α -> Prop} {s : Set { x // p x }} :
    IsComplete s ↔ IsComplete ((↑) '' s : Set α) :=
  isUniformEmbedding_subtype_val.isComplete_iff.symm

alias ⟨isComplete_of_complete_image, _⟩ := isComplete_image_iff

/--
theorem `completeSpace_iff_isComplete_range` / 定理 `completeSpace_iff_isComplete_range`

English:
theorem completeSpace_iff_isComplete_range
  given: {f : α -> β} (hf : IsUniformInducing f)
  proof: by
  rw [completeSpace_iff_isComplete_univ]; rw [← isComplete_image_iff hf]; rw [image_univ]

alias ⟨_, IsUniformInducing.completeSpace⟩ := completeSpace_iff_isComplete_range

中文:
定理 completeSpace_iff_isComplete_range
  条件: {f : α -> β} (hf : IsUniformInducing f)
  证明: by
  rw [completeSpace_iff_isComplete_univ]; rw [← isComplete_image_iff hf]; rw [image_univ]

alias ⟨_, IsUniformInducing.completeSpace⟩ := completeSpace_iff_isComplete_range

Depends on / 依赖: completeSpace_iff_isComplete_univ, image_univ, isComplete_image_iff
-/
theorem completeSpace_iff_isComplete_range {f : α -> β} (hf : IsUniformInducing f) :
    CompleteSpace α ↔ IsComplete (range f) := by
  rw [completeSpace_iff_isComplete_univ]; rw [← isComplete_image_iff hf]; rw [image_univ]

alias ⟨_, IsUniformInducing.completeSpace⟩ := completeSpace_iff_isComplete_range

/--
lemma `IsUniformInducing.isComplete_range` / 引理 `IsUniformInducing.isComplete_range`

English:
lemma IsUniformInducing.isComplete_range
  given: [CompleteSpace α] (hf : IsUniformInducing f)
  proof: (completeSpace_iff_isComplete_range hf).1 ‹_›

中文:
引理 IsUniformInducing.isComplete_range
  条件: [CompleteSpace α] (hf : IsUniformInducing f)
  证明: (completeSpace_iff_isComplete_range hf).1 ‹_›

Depends on / 依赖: completeSpace_iff_isComplete_range
-/
lemma IsUniformInducing.isComplete_range [CompleteSpace α] (hf : IsUniformInducing f) :
    IsComplete (range f) :=
  (completeSpace_iff_isComplete_range hf).1 ‹_›

/--
theorem `IsUniformInducing.completeSpace_congr` / 定理 `IsUniformInducing.completeSpace_congr`

English:
theorem IsUniformInducing.completeSpace_congr
  statement: {f : α -> β} (hf : IsUniformInducing f)
  proof: by
  rw [completeSpace_iff_isComplete_range hf]; rw [hsurj.range_eq]; rw [completeSpace_iff_isComplete_univ]

中文:
定理 IsUniformInducing.completeSpace_congr
  结论: {f : α -> β} (hf : IsUniformInducing f)
  证明: by
  rw [completeSpace_iff_isComplete_range hf]; rw [hsurj.range_eq]; rw [completeSpace_iff_isComplete_univ]

Depends on / 依赖: completeSpace_iff_isComplete_range, completeSpace_iff_isComplete_univ, hsurj.range_eq, range_eq
-/
theorem IsUniformInducing.completeSpace_congr {f : α -> β} (hf : IsUniformInducing f)
    (hsurj : f.Surjective) : CompleteSpace α ↔ CompleteSpace β := by
  rw [completeSpace_iff_isComplete_range hf]; rw [hsurj.range_eq]; rw [completeSpace_iff_isComplete_univ]

/--
theorem `SeparationQuotient.completeSpace_iff` / 定理 `SeparationQuotient.completeSpace_iff`

English:
theorem SeparationQuotient.completeSpace_iff
  proof: .symm isUniformInducing_mk.completeSpace_congr surjective_mk

中文:
定理 SeparationQuotient.completeSpace_iff
  证明: .symm isUniformInducing_mk.completeSpace_congr surjective_mk

Depends on / 依赖: completeSpace_congr, isUniformInducing_mk, isUniformInducing_mk.completeSpace_congr, surjective_mk
-/
theorem SeparationQuotient.completeSpace_iff :
    CompleteSpace (SeparationQuotient α) ↔ CompleteSpace α :=
.symm isUniformInducing_mk.completeSpace_congr surjective_mk

/--
Instance `SeparationQuotient.instCompleteSpace` / 实例 `SeparationQuotient.instCompleteSpace`

English:
instance SeparationQuotient.instCompleteSpace
  signature: [CompleteSpace α]
  body: completeSpace_iff.2 ‹_›

中文:
实例 SeparationQuotient.instCompleteSpace
  签名: [CompleteSpace α]
  定义体: completeSpace_iff.2 ‹_›

Depends on / 依赖: completeSpace_iff
-/
instance SeparationQuotient.instCompleteSpace [CompleteSpace α] :
    CompleteSpace (SeparationQuotient α) :=
  completeSpace_iff.2 ‹_›

/--
theorem `completeSpace_congr` / 定理 `completeSpace_congr`

English:
theorem completeSpace_congr
  given: {e : α ≃ β} (he : IsUniformEmbedding e)
  proof: he.completeSpace_congr e.surjective

中文:
定理 completeSpace_congr
  条件: {e : α ≃ β} (he : IsUniformEmbedding e)
  证明: he.completeSpace_congr e.surjective

Depends on / 依赖: completeSpace_congr, e.surjective, he.completeSpace_congr, surjective
-/
theorem completeSpace_congr {e : α ≃ β} (he : IsUniformEmbedding e) :
    CompleteSpace α ↔ CompleteSpace β :=
  he.completeSpace_congr e.surjective

/--
theorem `completeSpace_coe_iff_isComplete` / 定理 `completeSpace_coe_iff_isComplete`

English:
theorem completeSpace_coe_iff_isComplete
  given: {s : Set α}
  statement: CompleteSpace s ↔ IsComplete s
  proof: by
  rw [completeSpace_iff_isComplete_range isUniformEmbedding_subtype_val.isUniformInducing]; rw [Subtype.range_coe]

alias ⟨_, IsComplete.completeSpace_coe⟩ := completeSpace_coe_iff_isComplete

中文:
定理 completeSpace_coe_iff_isComplete
  条件: {s : Set α}
  结论: CompleteSpace s ↔ IsComplete s
  证明: by
  rw [completeSpace_iff_isComplete_range isUniformEmbedding_subtype_val.isUniformInducing]; rw [Subtype.range_coe]

alias ⟨_, IsComplete.completeSpace_coe⟩ := completeSpace_coe_iff_isComplete

Depends on / 依赖: Subtype, Subtype.range_coe, completeSpace_iff_isComplete_range, isUniformEmbedding_subtype_val, isUniformEmbedding_subtype_val.isUniformInducing, isUniformInducing, range_coe
-/
theorem completeSpace_coe_iff_isComplete {s : Set α} : CompleteSpace s ↔ IsComplete s := by
  rw [completeSpace_iff_isComplete_range isUniformEmbedding_subtype_val.isUniformInducing]; rw [Subtype.range_coe]

alias ⟨_, IsComplete.completeSpace_coe⟩ := completeSpace_coe_iff_isComplete

/--
Instance `IsClosed.completeSpace_coe` / 实例 `IsClosed.completeSpace_coe`

English:
instance IsClosed.completeSpace_coe
  signature: [CompleteSpace α] {s : Set α} [hs : IsClosed s]
  body: hs.isComplete.completeSpace_coe

中文:
实例 IsClosed.completeSpace_coe
  签名: [CompleteSpace α] {s : Set α} [hs : IsClosed s]
  定义体: hs.isComplete.completeSpace_coe

Depends on / 依赖: completeSpace_coe, hs.isComplete.completeSpace_coe, isComplete
-/
instance IsClosed.completeSpace_coe [CompleteSpace α] {s : Set α} [hs : IsClosed s] :
    CompleteSpace s := hs.isComplete.completeSpace_coe

/--
theorem `completeSpace_ulift_iff` / 定理 `completeSpace_ulift_iff`

English:
theorem completeSpace_ulift_iff
  statement: CompleteSpace (ULift α) ↔ CompleteSpace α
  proof: IsUniformInducing.completeSpace_congr ⟨rfl⟩ ULift.down_surjective

中文:
定理 completeSpace_ulift_iff
  结论: CompleteSpace (ULift α) ↔ CompleteSpace α
  证明: IsUniformInducing.completeSpace_congr ⟨rfl⟩ ULift.down_surjective

Depends on / 依赖: IsUniformInducing, IsUniformInducing.completeSpace_congr, ULift.down_surjective, completeSpace_congr, down_surjective
-/
theorem completeSpace_ulift_iff : CompleteSpace (ULift α) ↔ CompleteSpace α :=
  IsUniformInducing.completeSpace_congr ⟨rfl⟩ ULift.down_surjective

/--
Instance `ULift.instCompleteSpace` / 实例 `ULift.instCompleteSpace`

English:
instance ULift.instCompleteSpace
  signature: [CompleteSpace α]
  body: completeSpace_ulift_iff.2 ‹_›

中文:
实例 ULift.instCompleteSpace
  签名: [CompleteSpace α]
  定义体: completeSpace_ulift_iff.2 ‹_›

Depends on / 依赖: completeSpace_ulift_iff
-/
instance ULift.instCompleteSpace [CompleteSpace α] : CompleteSpace (ULift α) :=
  completeSpace_ulift_iff.2 ‹_›

/--
theorem `completeSpace_extension` / 定理 `completeSpace_extension`

English:
theorem completeSpace_extension
  statement: {m : β -> α} (hm : IsUniformInducing m) (dense : DenseRange m)
  proof: ⟨fun {f : Filter α} (hf : Cauchy f) =>
    let p : Set (α × α) -> Set α -> Set α := fun s t => { y : α | exists x : α, x in t ∧ (x, y) in s }
    let g := (𝓤 α).lift fun s => f.lift' (p s)
    have mp₀ : Monotone p := fun _ _ h _ _ ⟨x, xs, xa⟩ => ⟨x, xs, h xa⟩
    have mp₁ : forall {s}, Monotone (p 

中文:
定理 completeSpace_extension
  结论: {m : β -> α} (hm : IsUniformInducing m) (dense : DenseRange m)
  证明: ⟨fun {f : Filter α} (hf : Cauchy f) =>
    let p : Set (α × α) -> Set α -> Set α := fun s t => { y : α | exists x : α, x in t ∧ (x, y) in s }
    let g := (𝓤 α).lift fun s => f.lift' (p s)
    have mp₀ : Monotone p := fun _ _ h _ _ ⟨x, xs, xa⟩ => ⟨x, xs, h xa⟩
    have mp₁ : forall {s}, Monotone (p 

Depends on / 依赖: Cauchy, Filter, Monotone, f.lift, hf.left.mo, le_principal_iff, le_principal_iff.mpr, mem_of_superset, refl_mem_uniformity
-/
theorem completeSpace_extension {m : β -> α} (hm : IsUniformInducing m) (dense : DenseRange m)
    (h : forall f : Filter β, Cauchy f -> exists x : α, map m f <= 𝓝 x) : CompleteSpace α :=
  ⟨fun {f : Filter α} (hf : Cauchy f) =>
    let p : Set (α × α) -> Set α -> Set α := fun s t => { y : α | exists x : α, x in t ∧ (x, y) in s }
    let g := (𝓤 α).lift fun s => f.lift' (p s)
    have mp₀ : Monotone p := fun _ _ h _ _ ⟨x, xs, xa⟩ => ⟨x, xs, h xa⟩
    have mp₁ : forall {s}, Monotone (p s) := fun h _ ⟨y, ya, yxs⟩ => ⟨y, h ya, yxs⟩
    have : f <= g := le_iInf₂ fun _ hs => le_iInf₂ fun _ ht =>
le_principal_iff.mpr mem_of_superset ht fun x hx => ⟨x, hx, refl_mem_uniformity hs⟩
    have : NeBot g := hf.left.mono this
    have : NeBot (comap m g) :=
      comap_neBot fun _ ht =>
        let ⟨t', ht', ht_mem⟩ := (mem_lift_sets <| monotone_lift' monotone_const mp₀).mp ht
        let ⟨_, ht'', ht'_sub⟩ := (mem_lift'_sets mp₁).mp ht_mem
        let ⟨x, hx⟩ := hf.left.nonempty_of_mem ht''
        have h₀ : NeBot (𝓝[range m] x) := dense.nhdsWithin_neBot x
        have h₁ : { y | (x, y) in t' } in 𝓝[range m] x :=
@mem_inf_of_left α (𝓝 x) (𝓟 (range m)) _ mem_nhds_left x ht'
        have h₂ : range m in 𝓝[range m] x :=
@mem_inf_of_right α (𝓝 x) (𝓟 (range m)) _ Subset.refl _
        have : { y | (x, y) in t' } inter range m in 𝓝[range m] x := @inter_mem α (𝓝[range m] x) _ _ h₁ h₂
        let ⟨_, xyt', b, b_eq⟩ := h₀.nonempty_of_mem this
        ⟨b, b_eq.symm ▸ ht'_sub ⟨x, hx, xyt'⟩⟩
    have : Cauchy g :=
      ⟨‹NeBot g›, fun _ hs =>
        let ⟨s₁, hs₁, comp_s₁⟩ := comp_mem_uniformity_sets hs
        let ⟨s₂, hs₂, comp_s₂⟩ := comp_mem_uniformity_sets hs₁
        let ⟨t, ht, (prod_t : t ×ˢ t subseteq s₂)⟩ := mem_prod_same_iff.mp (hf.right hs₂)
        have hg₁ : p (preimage Prod.swap s₁) t in g :=
mem_lift (symm_le_uniformity hs₁) @mem_lift' α α f _ t ht
have hg₂ : p s₂ t in g := mem_lift hs₂ @mem_lift' α α f _ t ht
        have hg : p (Prod.swap ⁻¹' s₁) t ×ˢ p s₂ t in g ×ˢ g := @prod_mem_prod α α _ _ g g hg₁ hg₂
        (g ×ˢ g).sets_of_superset hg fun ⟨_, _⟩ ⟨⟨c₁, c₁t, hc₁⟩, ⟨c₂, c₂t, hc₂⟩⟩ =>
          have : (c₁, c₂) in t ×ˢ t := ⟨c₁t, c₂t⟩
comp_s₁ SetRel.prodMk_mem_comp hc₁ comp_s₂
            SetRel.prodMk_mem_comp (prod_t this) hc₂⟩
    have : Cauchy (Filter.comap m g) := ‹Cauchy g›.comap' (le_of_eq hm.comap_uniformity) ‹_›
    let ⟨x, (hx : map m (Filter.comap m g) <= 𝓝 x)⟩ := h _ this
    have : ClusterPt x (map m (Filter.comap m g)) :=
      (le_nhds_iff_adhp_of_cauchy (this.map hm.uniformContinuous)).mp hx
    have : ClusterPt x g := this.mono map_comap_le
    ⟨x,
      calc
        f <= g := by assumption
        _ <= 𝓝 x := le_nhds_of_cauchy_adhp ‹Cauchy g› this
        ⟩⟩

/--
lemma `Filter.totallyBounded_map_iff` / 引理 `Filter.totallyBounded_map_iff`

English:
lemma Filter.totallyBounded_map_iff
  given: {f : α -> β} {F : Filter α} (hf : IsUniformInducing f)
  proof: by
  refine ⟨fun hs => ?_, fun h => h.map hf.uniformContinuous⟩
  simp_rw [(hf.basis_uniformity (basis_sets _)).filter_totallyBounded_iff]
  intro t ht
  rcases exists_subset_image_finite_and.1 (hs.exists_subset_of_mem (F.image_mem_map F.univ_mem) ht)
    with ⟨u, -, hfin, h⟩
  use u, hfin
  simp_rw

中文:
引理 Filter.totallyBounded_map_iff
  条件: {f : α -> β} {F : Filter α} (hf : IsUniformInducing f)
  证明: by
  refine ⟨fun hs => ?_, fun h => h.map hf.uniformContinuous⟩
  simp_rw [(hf.basis_uniformity (basis_sets _)).filter_totallyBounded_iff]
  intro t ht
  rcases exists_subset_image_finite_and.1 (hs.exists_subset_of_mem (F.image_mem_map F.univ_mem) ht)
    with ⟨u, -, hfin, h⟩
  use u, hfin
  simp_rw

Depends on / 依赖: F.image_mem_map, F.univ_mem, SetRel, SetRel.preimage, basis_sets, basis_uniformity, exists_mem_image, exists_subset_image_finite_and, exists_subset_of_mem, filter_totallyBounded_iff, h.map, hf.basis_uniformity, hf.uniformContinuous, hs.exists_subset_of_mem, image_mem_map, preimage, simp_rw, uniformContinuous, univ_mem
-/
lemma Filter.totallyBounded_map_iff {f : α -> β} {F : Filter α} (hf : IsUniformInducing f) :
    (F.map f).TotallyBounded ↔ F.TotallyBounded := by
  refine ⟨fun hs => ?_, fun h => h.map hf.uniformContinuous⟩
  simp_rw [(hf.basis_uniformity (basis_sets _)).filter_totallyBounded_iff]
  intro t ht
  rcases exists_subset_image_finite_and.1 (hs.exists_subset_of_mem (F.image_mem_map F.univ_mem) ht)
    with ⟨u, -, hfin, h⟩
  use u, hfin
  simp_rw [SetRel.preimage, exists_mem_image] at h
  exact h

/--
lemma `totallyBounded_image_iff` / 引理 `totallyBounded_image_iff`

English:
lemma totallyBounded_image_iff
  given: {f : α -> β} {s : Set α} (hf : IsUniformInducing f)
  proof: by
  simp_rw [← totallyBounded_principal_iff, ← map_principal, totallyBounded_map_iff hf]

中文:
引理 totallyBounded_image_iff
  条件: {f : α -> β} {s : Set α} (hf : IsUniformInducing f)
  证明: by
  simp_rw [← totallyBounded_principal_iff, ← map_principal, totallyBounded_map_iff hf]

Depends on / 依赖: map_principal, simp_rw, totallyBounded_map_iff, totallyBounded_principal_iff
-/
lemma totallyBounded_image_iff {f : α -> β} {s : Set α} (hf : IsUniformInducing f) :
    TotallyBounded (f '' s) ↔ TotallyBounded s := by
  simp_rw [← totallyBounded_principal_iff, ← map_principal, totallyBounded_map_iff hf]

/--
theorem `totallyBounded_preimage` / 定理 `totallyBounded_preimage`

English:
theorem totallyBounded_preimage
  statement: {f : α -> β} {s : Set β} (hf : IsUniformInducing f)
  proof: (totallyBounded_image_iff hf).1 hs.subset image_preimage_subset ..

中文:
定理 totallyBounded_preimage
  结论: {f : α -> β} {s : Set β} (hf : IsUniformInducing f)
  证明: (totallyBounded_image_iff hf).1 hs.subset image_preimage_subset ..

Depends on / 依赖: hs.subset, image_preimage_subset, subset, totallyBounded_image_iff
-/
theorem totallyBounded_preimage {f : α -> β} {s : Set β} (hf : IsUniformInducing f)
    (hs : TotallyBounded s) : TotallyBounded (f ⁻¹' s) :=
(totallyBounded_image_iff hf).1 hs.subset image_preimage_subset ..

/--
theorem `Filter.totallyBounded_comap` / 定理 `Filter.totallyBounded_comap`

English:
theorem Filter.totallyBounded_comap
  statement: {f : α -> β} {F : Filter β} (hf : IsUniformInducing f)
  proof: (totallyBounded_map_iff hf).1 hF.mono map_comap_le

中文:
定理 Filter.totallyBounded_comap
  结论: {f : α -> β} {F : Filter β} (hf : IsUniformInducing f)
  证明: (totallyBounded_map_iff hf).1 hF.mono map_comap_le

Depends on / 依赖: hF.mono, map_comap_le, totallyBounded_map_iff
-/
theorem Filter.totallyBounded_comap {f : α -> β} {F : Filter β} (hf : IsUniformInducing f)
    (hF : F.TotallyBounded) : (F.comap f).TotallyBounded :=
(totallyBounded_map_iff hf).1 hF.mono map_comap_le

/--
Instance `CompleteSpace.sum` / 实例 `CompleteSpace.sum`

English:
instance CompleteSpace.sum
  signature: [CompleteSpace α] [CompleteSpace β]
  body: by
  rw [completeSpace_iff_isComplete_univ]; rw [← range_inl_union_range_inr]
  exact isUniformEmbedding_inl.isUniformInducing.isComplete_range.union
    isUniformEmbedding_inr.isUniformInducing.isComplete_range

中文:
实例 CompleteSpace.sum
  签名: [CompleteSpace α] [CompleteSpace β]
  定义体: by
  rw [completeSpace_iff_isComplete_univ]; rw [← range_inl_union_range_inr]
  exact isUniformEmbedding_inl.isUniformInducing.isComplete_range.union
    isUniformEmbedding_inr.isUniformInducing.isComplete_range

Depends on / 依赖: completeSpace_iff_isComplete_univ, isComplete_range, isUniformEmbedding_inl, isUniformEmbedding_inl.isUniformInducing.isComplete_range.union, isUniformEmbedding_inr, isUniformEmbedding_inr.isUniformInducing.isComplete_range, isUniformInducing, range_inl_union_range_inr
-/
instance CompleteSpace.sum [CompleteSpace α] [CompleteSpace β] : CompleteSpace (α oplus β) := by
  rw [completeSpace_iff_isComplete_univ]; rw [← range_inl_union_range_inr]
  exact isUniformEmbedding_inl.isUniformInducing.isComplete_range.union
    isUniformEmbedding_inr.isUniformInducing.isComplete_range

/--
theorem `IsUniformEmbedding.discreteUniformity` / 定理 `IsUniformEmbedding.discreteUniformity`

English:
theorem IsUniformEmbedding.discreteUniformity
  statement: [DiscreteUniformity β] {f : α -> β}
  proof: by
  simp_rw [discreteUniformity_iff_eq_principal_setRelId, ← hf.comap_uniformity,
    DiscreteUniformity.eq_principal_setRelId, comap_principal, SetRel.id, preimage_ofPred_eq,
    hf.injective.eq_iff]

中文:
定理 IsUniformEmbedding.discreteUniformity
  结论: [DiscreteUniformity β] {f : α -> β}
  证明: by
  simp_rw [discreteUniformity_iff_eq_principal_setRelId, ← hf.comap_uniformity,
    DiscreteUniformity.eq_principal_setRelId, comap_principal, SetRel.id, preimage_ofPred_eq,
    hf.injective.eq_iff]

Depends on / 依赖: DiscreteUniformity, DiscreteUniformity.eq_principal_setRelId, SetRel, SetRel.id, comap_principal, comap_uniformity, discreteUniformity_iff_eq_principal_setRelId, eq_iff, eq_principal_setRelId, hf.comap_uniformity, hf.injective.eq_iff, injective, preimage_ofPred_eq, simp_rw
-/
theorem IsUniformEmbedding.discreteUniformity [DiscreteUniformity β] {f : α -> β}
    (hf : IsUniformEmbedding f) : DiscreteUniformity α := by
  simp_rw [discreteUniformity_iff_eq_principal_setRelId, ← hf.comap_uniformity,
    DiscreteUniformity.eq_principal_setRelId, comap_principal, SetRel.id, preimage_ofPred_eq,
    hf.injective.eq_iff]

end

/--
theorem `isUniformEmbedding_comap` / 定理 `isUniformEmbedding_comap`

English:
theorem isUniformEmbedding_comap
  statement: {α : Type*} {β : Type*} {f : α -> β} [u : UniformSpace β]
  proof: @IsUniformEmbedding.mk _ _ (UniformSpace.comap f u) _ _
    (@IsUniformInducing.mk _ _ (UniformSpace.comap f u) _ _ rfl) hf

中文:
定理 isUniformEmbedding_comap
  结论: {α : 类型} {β : 类型} {f : α -> β} [u : UniformSpace β]
  证明: @IsUniformEmbedding.mk _ _ (UniformSpace.comap f u) _ _
    (@IsUniformInducing.mk _ _ (UniformSpace.comap f u) _ _ rfl) hf

Depends on / 依赖: IsUniformEmbedding, IsUniformEmbedding.mk, IsUniformInducing, IsUniformInducing.mk, UniformSpace, UniformSpace.comap
-/
theorem isUniformEmbedding_comap {α : Type*} {β : Type*} {f : α -> β} [u : UniformSpace β]
    (hf : Function.Injective f) : @IsUniformEmbedding α β (UniformSpace.comap f u) u f :=
  @IsUniformEmbedding.mk _ _ (UniformSpace.comap f u) _ _
    (@IsUniformInducing.mk _ _ (UniformSpace.comap f u) _ _ rfl) hf

/-- Pull back a uniform space structure by an embedding, adjusting the new uniform structure to
make sure that its topology is defeq to the original one. -/
@[instance_reducible]
/--
Definition of `Topology.IsEmbedding.comapUniformSpace` / `Topology.IsEmbedding.comapUniformSpace` 的定义

English:
definition Topology.IsEmbedding.comapUniformSpace
  signature: {α β} [TopologicalSpace α] [u : UniformSpace β]
  body: (u.comap f).replaceTopology h.eq_induced

中文:
定义 Topology.IsEmbedding.comapUniformSpace
  签名: {α β} [TopologicalSpace α] [u : UniformSpace β]
  定义体: (u.comap f).replaceTopology h.eq_induced

Depends on / 依赖: eq_induced, h.eq_induced, replaceTopology, u.comap
-/
def Topology.IsEmbedding.comapUniformSpace {α β} [TopologicalSpace α] [u : UniformSpace β]
    (f : α -> β) (h : IsEmbedding f) : UniformSpace α :=
  (u.comap f).replaceTopology h.eq_induced

/--
theorem `Embedding.to_isUniformEmbedding` / 定理 `Embedding.to_isUniformEmbedding`

English:
theorem Embedding.to_isUniformEmbedding
  statement: {α β} [TopologicalSpace α] [u : UniformSpace β] (f : α -> β)
  proof: let _ := h.comapUniformSpace f
  { comap_uniformity := rfl
    injective := h.injective }

中文:
定理 Embedding.to_isUniformEmbedding
  结论: {α β} [TopologicalSpace α] [u : UniformSpace β] (f : α -> β)
  证明: let _ := h.comapUniformSpace f
  { comap_uniformity := rfl
    injective := h.injective }

Depends on / 依赖: comapUniformSpace, comap_uniformity, h.comapUniformSpace, h.injective, injective
-/
theorem Embedding.to_isUniformEmbedding {α β} [TopologicalSpace α] [u : UniformSpace β] (f : α -> β)
    (h : IsEmbedding f) : @IsUniformEmbedding α β (h.comapUniformSpace f) u f :=
  let _ := h.comapUniformSpace f
  { comap_uniformity := rfl
    injective := h.injective }

section UniformExtension

variable {α : Type*} {β : Type*} {γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ]
  {e : β -> α} (h_e : IsUniformInducing e) (h_dense : DenseRange e) {f : β -> γ}
  (h_f : UniformContinuous f)

local notation "ψ" => IsDenseInducing.extend (IsUniformInducing.isDenseInducing h_e h_dense) f

include h_e h_dense h_f in
/--
theorem `uniformly_extend_exists` / 定理 `uniformly_extend_exists`

English:
theorem uniformly_extend_exists
  given: [CompleteSpace γ] (a : α)
  statement: exists c, Tendsto f (comap e (𝓝 a)) (𝓝 c)
  proof: let de := h_e.isDenseInducing h_dense
  have : Cauchy (𝓝 a) := cauchy_nhds
  have : Cauchy (comap e (𝓝 a)) :=
    this.comap' (le_of_eq h_e.comap_uniformity) (de.comap_nhds_neBot _)
  have : Cauchy (map f (comap e (𝓝 a))) := this.map h_f
  CompleteSpace.complete this

中文:
定理 uniformly_extend_exists
  条件: [CompleteSpace γ] (a : α)
  结论: 存在 c, Tendsto f (comap e (𝓝 a)) (𝓝 c)
  证明: let de := h_e.isDenseInducing h_dense
  have : Cauchy (𝓝 a) := cauchy_nhds
  have : Cauchy (comap e (𝓝 a)) :=
    this.comap' (le_of_eq h_e.comap_uniformity) (de.comap_nhds_neBot _)
  have : Cauchy (map f (comap e (𝓝 a))) := this.map h_f
  CompleteSpace.complete this

Depends on / 依赖: Cauchy, CompleteSpace, CompleteSpace.complete, cauchy_nhds, comap_nhds_neBot, comap_uniformity, complete, de.comap_nhds_neBot, h_dense, h_e.comap_uniformity, h_e.isDenseInducing, isDenseInducing, le_of_eq, this.comap, this.map
-/
theorem uniformly_extend_exists [CompleteSpace γ] (a : α) : exists c, Tendsto f (comap e (𝓝 a)) (𝓝 c) :=
  let de := h_e.isDenseInducing h_dense
  have : Cauchy (𝓝 a) := cauchy_nhds
  have : Cauchy (comap e (𝓝 a)) :=
    this.comap' (le_of_eq h_e.comap_uniformity) (de.comap_nhds_neBot _)
  have : Cauchy (map f (comap e (𝓝 a))) := this.map h_f
  CompleteSpace.complete this

/--
theorem `uniform_extend_subtype` / 定理 `uniform_extend_subtype`

English:
theorem uniform_extend_subtype
  statement: [CompleteSpace γ] {p : α -> Prop} {e : α -> β} {f : α -> γ} {b : β}
  proof: by
  have de : IsDenseEmbedding e := he.isDenseEmbedding hd
  have de' : IsDenseEmbedding (IsDenseEmbedding.subtypeEmb p e) := de.subtype p
  have ue' : IsUniformEmbedding (IsDenseEmbedding.subtypeEmb p e) :=
    isUniformEmbedding_subtypeEmb _ he de
  have : b in closure (e '' { x | p x }) :=
    (

中文:
定理 uniform_extend_subtype
  结论: [CompleteSpace γ] {p : α -> 命题} {e : α -> β} {f : α -> γ} {b : β}
  证明: by
  have de : IsDenseEmbedding e := he.isDenseEmbedding hd
  have de' : IsDenseEmbedding (IsDenseEmbedding.subtypeEmb p e) := de.subtype p
  have ue' : IsUniformEmbedding (IsDenseEmbedding.subtypeEmb p e) :=
    isUniformEmbedding_subtypeEmb _ he de
  have : b in closure (e '' { x | p x }) :=
    (

Depends on / 依赖: IsDenseEmbedding, IsDenseEmbedding.subtypeEmb, IsUniformEmbedding, Subtype, Subtype.val, Tendsto, closure, closure_mono, de.subtype, he.isDenseEmbedding, isDenseEmbedding, isUniformEmbedding_subtypeEmb, isUniformInducing, mem_of_mem_nhds, monotone_image, replace, subtype, subtypeEmb, uniformly_extend_exists
-/
theorem uniform_extend_subtype [CompleteSpace γ] {p : α -> Prop} {e : α -> β} {f : α -> γ} {b : β}
    {s : Set α} (hf : UniformContinuous fun x : Subtype p => f x.val) (he : IsUniformEmbedding e)
    (hd : forall x : β, x in closure (range e)) (hb : closure (e '' s) in 𝓝 b) (hs : IsClosed s)
    (hp : forall x in s, p x) : exists c, Tendsto f (comap e (𝓝 b)) (𝓝 c) := by
  have de : IsDenseEmbedding e := he.isDenseEmbedding hd
  have de' : IsDenseEmbedding (IsDenseEmbedding.subtypeEmb p e) := de.subtype p
  have ue' : IsUniformEmbedding (IsDenseEmbedding.subtypeEmb p e) :=
    isUniformEmbedding_subtypeEmb _ he de
  have : b in closure (e '' { x | p x }) :=
    (closure_mono <| monotone_image <| hp) (mem_of_mem_nhds hb)
  let ⟨c, hc⟩ := uniformly_extend_exists ue'.isUniformInducing de'.dense hf ⟨b, this⟩
  replace hc : Tendsto (f ∘ Subtype.val (p := p)) (((𝓝 b).comap e).comap Subtype.val) (𝓝 c) := by
    simpa only [nhds_subtype_eq_comap, comap_comap, IsDenseEmbedding.subtypeEmb_coe] using! hc
  refine ⟨c, (tendsto_comap'_iff ?_).1 hc⟩
  rw [Subtype.range_coe_subtype]
  exact ⟨_, hb, by rwa [← de.isInducing.closure_eq_preimage_closure_image, hs.closure_eq]⟩

include h_e h_f in
/--
theorem `uniformly_extend_spec` / 定理 `uniformly_extend_spec`

English:
theorem uniformly_extend_spec
  given: [CompleteSpace γ] (a : α)
  statement: Tendsto f (comap e (𝓝 a)) (𝓝 (ψ a))
  proof: by
  simpa only [IsDenseInducing.extend] using
    tendsto_nhds_limUnder (uniformly_extend_exists h_e ‹_› h_f _)

include h_f in

中文:
定理 uniformly_extend_spec
  条件: [CompleteSpace γ] (a : α)
  结论: Tendsto f (comap e (𝓝 a)) (𝓝 (ψ a))
  证明: by
  simpa only [IsDenseInducing.extend] using
    tendsto_nhds_limUnder (uniformly_extend_exists h_e ‹_› h_f _)

include h_f in

Depends on / 依赖: IsDenseInducing, IsDenseInducing.extend, extend, tendsto_nhds_limUnder, uniformly_extend_exists
-/
theorem uniformly_extend_spec [CompleteSpace γ] (a : α) : Tendsto f (comap e (𝓝 a)) (𝓝 (ψ a)) := by
  simpa only [IsDenseInducing.extend] using
    tendsto_nhds_limUnder (uniformly_extend_exists h_e ‹_› h_f _)

include h_f in
/--
theorem `uniformContinuous_uniformly_extend` / 定理 `uniformContinuous_uniformly_extend`

English:
theorem uniformContinuous_uniformly_extend
  given: [CompleteSpace γ]
  statement: UniformContinuous ψ
  proof: fun d hd =>
  let ⟨s, hs, hs_comp⟩ := comp3_mem_uniformity hd
  have h_pnt : forall {a m}, m in 𝓝 a -> exists c in f '' e ⁻¹' m, (c, ψ a) in s ∧ (ψ a, c) in s :=
    fun {a m} hm =>
    have nb : NeBot (map f (comap e (𝓝 a))) :=
      ((h_e.isDenseInducing h_dense).comap_nhds_neBot _).map _
    have

中文:
定理 uniformContinuous_uniformly_extend
  条件: [CompleteSpace γ]
  结论: UniformContinuous ψ
  证明: fun d hd =>
  let ⟨s, hs, hs_comp⟩ := comp3_mem_uniformity hd
  have h_pnt : forall {a m}, m in 𝓝 a -> exists c in f '' e ⁻¹' m, (c, ψ a) in s ∧ (ψ a, c) in s :=
    fun {a m} hm =>
    have nb : NeBot (map f (comap e (𝓝 a))) :=
      ((h_e.isDenseInducing h_dense).comap_nhds_neBot _).map _
    have
-/
theorem uniformContinuous_uniformly_extend [CompleteSpace γ] : UniformContinuous ψ := fun d hd =>
  let ⟨s, hs, hs_comp⟩ := comp3_mem_uniformity hd
  have h_pnt : forall {a m}, m in 𝓝 a -> exists c in f '' e ⁻¹' m, (c, ψ a) in s ∧ (ψ a, c) in s :=
    fun {a m} hm =>
    have nb : NeBot (map f (comap e (𝓝 a))) :=
      ((h_e.isDenseInducing h_dense).comap_nhds_neBot _).map _
    have :
      f '' (e ⁻¹' m) inter ({ c | (c, ψ a) in s } inter { c | (ψ a, c) in s }) in map f (comap e (𝓝 a)) :=
      inter_mem (image_mem_map <| preimage_mem_comap <| hm)
        (uniformly_extend_spec h_e h_dense h_f _
          (inter_mem (mem_nhds_right _ hs) (mem_nhds_left _ hs)))
    nb.nonempty_of_mem this
  have : (Prod.map f f) ⁻¹' s in 𝓤 β := h_f hs
  have : (Prod.map f f) ⁻¹' s in comap (Prod.map e e) (𝓤 α) := by
    rwa [← h_e.comap_uniformity] at this
  let ⟨t, ht, ts⟩ := this
  show (Prod.map ψ ψ) ⁻¹' d in 𝓤 α from
    mem_of_superset (interior_mem_uniformity ht) fun ⟨x₁, x₂⟩ hx_t => by
      have : interior t in 𝓝 (x₁, x₂) := isOpen_interior.mem_nhds hx_t
      let ⟨m₁, hm₁, m₂, hm₂, (hm : m₁ ×ˢ m₂ subseteq interior t)⟩ := mem_nhds_prod_iff.mp this
      obtain ⟨_, ⟨a, ha₁, rfl⟩, _, ha₂⟩ := h_pnt hm₁
      obtain ⟨_, ⟨b, hb₁, rfl⟩, hb₂, _⟩ := h_pnt hm₂
      have : Prod.map f f (a, b) in s :=
ts mem_preimage.2 interior_subset (@hm (e a, e b) ⟨ha₁, hb₁⟩)
      exact hs_comp ⟨f a, ha₂, ⟨f b, this, hb₂⟩⟩

variable [T0Space γ]

include h_f in
/--
theorem `uniformly_extend_of_ind` / 定理 `uniformly_extend_of_ind`

English:
theorem uniformly_extend_of_ind
  given: (b : β)
  statement: ψ (e b) = f b
  proof: IsDenseInducing.extend_eq_at _ h_f.continuous.continuousAt

中文:
定理 uniformly_extend_of_ind
  条件: (b : β)
  结论: ψ (e b) = f b
  证明: IsDenseInducing.extend_eq_at _ h_f.continuous.continuousAt

Depends on / 依赖: IsDenseInducing, IsDenseInducing.extend_eq_at, continuous, continuousAt, extend_eq_at, h_f.continuous.continuousAt
-/
theorem uniformly_extend_of_ind (b : β) : ψ (e b) = f b :=
  IsDenseInducing.extend_eq_at _ h_f.continuous.continuousAt

/--
theorem `uniformly_extend_unique` / 定理 `uniformly_extend_unique`

English:
theorem uniformly_extend_unique
  given: {g : α -> γ} (hg : forall b, g (e b) = f b) (hc : Continuous g)
  statement: ψ = g
  proof: IsDenseInducing.extend_unique _ hg hc

中文:
定理 uniformly_extend_unique
  条件: {g : α -> γ} (hg : 对任意 b, g (e b) = f b) (hc : Continuous g)
  结论: ψ = g
  证明: IsDenseInducing.extend_unique _ hg hc

Depends on / 依赖: IsDenseInducing, IsDenseInducing.extend_unique, extend_unique
-/
theorem uniformly_extend_unique {g : α -> γ} (hg : forall b, g (e b) = f b) (hc : Continuous g) : ψ = g :=
  IsDenseInducing.extend_unique _ hg hc

end UniformExtension

section DenseExtension

variable {α β : Type*} [UniformSpace α] [UniformSpace β]

/--
theorem `isUniformInducing_val` / 定理 `isUniformInducing_val`

English:
theorem isUniformInducing_val
  given: (s : Set α)
  proof: ⟨uniformity_setCoe⟩

@[simp]

中文:
定理 isUniformInducing_val
  条件: (s : Set α)
  证明: ⟨uniformity_setCoe⟩

@[simp]

Depends on / 依赖: uniformity_setCoe
-/
theorem isUniformInducing_val (s : Set α) :
    IsUniformInducing ((↑) : s -> α) := ⟨uniformity_setCoe⟩

@[simp]
/--
theorem `uniformContinuous_rangeFactorization_iff` / 定理 `uniformContinuous_rangeFactorization_iff`

English:
theorem uniformContinuous_rangeFactorization_iff
  given: {f : α -> β}
  proof: (isUniformInducing_val _).uniformContinuous_iff

中文:
定理 uniformContinuous_rangeFactorization_iff
  条件: {f : α -> β}
  证明: (isUniformInducing_val _).uniformContinuous_iff

Depends on / 依赖: isUniformInducing_val, uniformContinuous_iff
-/
theorem uniformContinuous_rangeFactorization_iff {f : α -> β} :
    UniformContinuous (rangeFactorization f) ↔ UniformContinuous f :=
  (isUniformInducing_val _).uniformContinuous_iff

/--
theorem `UniformContinuous.rangeFactorization` / 定理 `UniformContinuous.rangeFactorization`

English:
theorem UniformContinuous.rangeFactorization
  given: {f : α -> β} (hf : UniformContinuous f)
  proof: uniformContinuous_rangeFactorization_iff.mpr hf

@[simp]

中文:
定理 UniformContinuous.rangeFactorization
  条件: {f : α -> β} (hf : UniformContinuous f)
  证明: uniformContinuous_rangeFactorization_iff.mpr hf

@[simp]

Depends on / 依赖: uniformContinuous_rangeFactorization_iff, uniformContinuous_rangeFactorization_iff.mpr
-/
theorem UniformContinuous.rangeFactorization {f : α -> β} (hf : UniformContinuous f) :
    UniformContinuous (rangeFactorization f) :=
  uniformContinuous_rangeFactorization_iff.mpr hf

@[simp]
/--
theorem `isUniformInducing_rangeFactorization_iff` / 定理 `isUniformInducing_rangeFactorization_iff`

English:
theorem isUniformInducing_rangeFactorization_iff
  given: {f : α -> β}
  proof: (isUniformInducing_val (range f)).of_comp_iff.symm

中文:
定理 isUniformInducing_rangeFactorization_iff
  条件: {f : α -> β}
  证明: (isUniformInducing_val (range f)).of_comp_iff.symm

Depends on / 依赖: isUniformInducing_val, of_comp_iff, of_comp_iff.symm
-/
theorem isUniformInducing_rangeFactorization_iff {f : α -> β} :
    IsUniformInducing (rangeFactorization f) ↔ IsUniformInducing f :=
  (isUniformInducing_val (range f)).of_comp_iff.symm

/--
theorem `IsUniformInducing.rangeFactorization` / 定理 `IsUniformInducing.rangeFactorization`

English:
theorem IsUniformInducing.rangeFactorization
  given: {f : α -> β} (hf : IsUniformInducing f)
  proof: isUniformInducing_rangeFactorization_iff.2 hf

中文:
定理 IsUniformInducing.rangeFactorization
  条件: {f : α -> β} (hf : IsUniformInducing f)
  证明: isUniformInducing_rangeFactorization_iff.2 hf

Depends on / 依赖: isUniformInducing_rangeFactorization_iff
-/
theorem IsUniformInducing.rangeFactorization {f : α -> β} (hf : IsUniformInducing f) :
    IsUniformInducing (rangeFactorization f) :=
  isUniformInducing_rangeFactorization_iff.2 hf

namespace Dense

variable {s : Set α} {f : s -> β}

/--
theorem `extend_exists` / 定理 `extend_exists`

English:
theorem extend_exists
  given: [CompleteSpace β] (hs : Dense s) (hf : UniformContinuous f) (a : α)
  proof: uniformly_extend_exists (isUniformInducing_val s) hs.denseRange_val hf a

中文:
定理 extend_exists
  条件: [CompleteSpace β] (hs : Dense s) (hf : UniformContinuous f) (a : α)
  证明: uniformly_extend_exists (isUniformInducing_val s) hs.denseRange_val hf a

Depends on / 依赖: denseRange_val, hs.denseRange_val, isUniformInducing_val, uniformly_extend_exists
-/
theorem extend_exists [CompleteSpace β] (hs : Dense s) (hf : UniformContinuous f) (a : α) :
    exists b, Tendsto f (comap (↑) (𝓝 a)) (𝓝 b) :=
  uniformly_extend_exists (isUniformInducing_val s) hs.denseRange_val hf a

/--
theorem `extend_spec` / 定理 `extend_spec`

English:
theorem extend_spec
  given: [CompleteSpace β] (hs : Dense s) (hf : UniformContinuous f) (a : α)
  proof: uniformly_extend_spec (isUniformInducing_val s) hs.denseRange_val hf a

中文:
定理 extend_spec
  条件: [CompleteSpace β] (hs : Dense s) (hf : UniformContinuous f) (a : α)
  证明: uniformly_extend_spec (isUniformInducing_val s) hs.denseRange_val hf a

Depends on / 依赖: denseRange_val, hs.denseRange_val, isUniformInducing_val, uniformly_extend_spec
-/
theorem extend_spec [CompleteSpace β] (hs : Dense s) (hf : UniformContinuous f) (a : α) :
    Tendsto f (comap (↑) (𝓝 a)) (𝓝 (hs.extend f a)) :=
  uniformly_extend_spec (isUniformInducing_val s) hs.denseRange_val hf a

/--
theorem `uniformContinuous_extend` / 定理 `uniformContinuous_extend`

English:
theorem uniformContinuous_extend
  given: [CompleteSpace β] (hs : Dense s) (hf : UniformContinuous f)
  proof: uniformContinuous_uniformly_extend (isUniformInducing_val s) hs.denseRange_val hf

中文:
定理 uniformContinuous_extend
  条件: [CompleteSpace β] (hs : Dense s) (hf : UniformContinuous f)
  证明: uniformContinuous_uniformly_extend (isUniformInducing_val s) hs.denseRange_val hf

Depends on / 依赖: denseRange_val, hs.denseRange_val, isUniformInducing_val, uniformContinuous_uniformly_extend
-/
theorem uniformContinuous_extend [CompleteSpace β] (hs : Dense s) (hf : UniformContinuous f) :
    UniformContinuous (hs.extend f) :=
  uniformContinuous_uniformly_extend (isUniformInducing_val s) hs.denseRange_val hf

variable [T0Space β]

/--
theorem `extend_of_ind` / 定理 `extend_of_ind`

English:
theorem extend_of_ind
  given: (hs : Dense s) (hf : UniformContinuous f) (x : s)
  proof: IsDenseInducing.extend_eq_at _ hf.continuous.continuousAt

中文:
定理 extend_of_ind
  条件: (hs : Dense s) (hf : UniformContinuous f) (x : s)
  证明: IsDenseInducing.extend_eq_at _ hf.continuous.continuousAt

Depends on / 依赖: IsDenseInducing, IsDenseInducing.extend_eq_at, continuous, continuousAt, extend_eq_at, hf.continuous.continuousAt
-/
theorem extend_of_ind (hs : Dense s) (hf : UniformContinuous f) (x : s) :
    hs.extend f x = f x :=
  IsDenseInducing.extend_eq_at _ hf.continuous.continuousAt

end Dense

/--
lemma `IsDenseInducing.isUniformInducing_extend` / 引理 `IsDenseInducing.isUniformInducing_extend`

English:
lemma IsDenseInducing.isUniformInducing_extend
  statement: {γ : Type*} [UniformSpace γ]
  proof: by
  let sf := SeparationQuotient.mk ∘ f
  have : CompleteSpace (closure (range sf)) :=
    isClosed_closure.isComplete.completeSpace_coe
  let ff : α -> closure (range sf) := inclusion subset_closure ∘ rangeFactorization sf
  have hgu : IsUniformInducing ff :=
    (isUniformEmbedding_set_inclusion 

中文:
引理 IsDenseInducing.isUniformInducing_extend
  结论: {γ : 类型} [UniformSpace γ]
  证明: by
  let sf := SeparationQuotient.mk ∘ f
  have : CompleteSpace (closure (range sf)) :=
    isClosed_closure.isComplete.completeSpace_coe
  let ff : α -> closure (range sf) := inclusion subset_closure ∘ rangeFactorization sf
  have hgu : IsUniformInducing ff :=
    (isUniformEmbedding_set_inclusion 

Depends on / 依赖: CompleteSpace, DenseRange, IsUniformInducing, SeparationQuotient, SeparationQuotient.isUniformInducing_mk.comp, SeparationQuotient.mk, closure, completeSpace_coe, denseRange_inclusion_iff, inclusion, isClosed_closure, isClosed_closure.isComplete.completeSpace_coe, isComplete, isUniformEmbedding_set_inclusion, isUniformInducing, isUniformInducing.comp, isUniformInducing_mk, rangeFactorization, rangeFactorization_, subset_closure
-/
lemma IsDenseInducing.isUniformInducing_extend {γ : Type*} [UniformSpace γ]
    [CompleteSpace β] [CompleteSpace γ] {i : α -> β} {f : α -> γ}
    (hid : IsDenseInducing i) (hi : IsUniformInducing i) (h : IsUniformInducing f) :
    IsUniformInducing (hid.extend f) := by
  let sf := SeparationQuotient.mk ∘ f
  have : CompleteSpace (closure (range sf)) :=
    isClosed_closure.isComplete.completeSpace_coe
  let ff : α -> closure (range sf) := inclusion subset_closure ∘ rangeFactorization sf
  have hgu : IsUniformInducing ff :=
    (isUniformEmbedding_set_inclusion subset_closure).isUniformInducing.comp
      (SeparationQuotient.isUniformInducing_mk.comp h).rangeFactorization
  have hgd : DenseRange ff :=
    ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
      rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)
  have hg : IsDenseInducing ff := hgu.isDenseInducing hgd
  let fwd := hid.extend ff
  have hfwd : UniformContinuous fwd :=
    uniformContinuous_uniformly_extend hi hid.dense hgu.uniformContinuous
  have hg' : UniformContinuous (hg.extend i) :=
    uniformContinuous_uniformly_extend hgu hgd hi.uniformContinuous
  have key : SeparationQuotient.mk ∘ hg.extend i ∘ fwd = SeparationQuotient.mk := by
    ext x
    induction x using isClosed_property hid.dense
    · exact isClosed_eq (SeparationQuotient.continuous_mk.comp (hg'.comp hfwd).continuous)
        SeparationQuotient.continuous_mk
    · simpa [fwd, hid.extend_eq hgu.uniformContinuous.continuous]
        using hg.inseparable_extend hi.uniformContinuous.continuous.continuousAt
  have hfu : IsUniformInducing fwd := by
    refine IsUniformInducing.of_comp hfwd (SeparationQuotient.uniformContinuous_mk.comp hg') ?_
    rw [Function.comp_assoc]; rw [key]
    exact SeparationQuotient.isUniformInducing_mk
  have hrr : range (SeparationQuotient.mk ∘ hid.extend f) subseteq
      closure (range (SeparationQuotient.mk ∘ f)) := by
    refine ((SeparationQuotient.continuous_mk.comp (uniformContinuous_uniformly_extend hi hid.dense
      h.uniformContinuous).continuous).range_subset_closure_image_dense hid.dense).trans
      (closure_mono (subset_of_eq ?_))
    rw [← range_comp]
    apply congrArg range
    funext x
    simpa using (hid.inseparable_extend h.uniformContinuous.continuous.continuousAt)
  suffices Subtype.val ∘ fwd = SeparationQuotient.mk ∘ hid.extend f by
    rw [← SeparationQuotient.isUniformInducing_mk.of_comp_iff]; rw [← this]
    exact (isUniformInducing_val _).comp hfu
  rw [← coe_comp_rangeFactorization (SeparationQuotient.mk ∘ hid.extend f)]; rw [← val_comp_inclusion hrr]; rw [Function.comp_assoc]; rw [Subtype.val_injective.comp_left.eq_iff]
  refine hid.extend_unique ?_ ?_
  · simp [ff, hid.inseparable_extend h.uniformContinuous.continuous.continuousAt, sf]
  · exact (continuous_inclusion hrr).comp
      (SeparationQuotient.continuous_mk.comp (uniformContinuous_uniformly_extend hi hid.dense
        h.uniformContinuous).continuous).rangeFactorization

end DenseExtension
