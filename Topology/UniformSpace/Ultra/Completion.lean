/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Ultra.Basic
public import Mathlib.Topology.UniformSpace.Ultra.Constructions

/-!
# Completions of ultrametric (nonarchimedean) uniform spaces

## Main results

* `IsUltraUniformity.completion_iff`: a Hausdorff completion has a nonarchimedean uniformity
  iff the underlying space has a nonarchimedean uniformity.

-/

public section

variable {X Y : Type*} [UniformSpace X] [UniformSpace Y]

open Filter Set Topology Uniformity

/--
lemma `IsUniformInducing.isUltraUniformity` / 引理 `IsUniformInducing.isUltraUniformity`

English:
lemma IsUniformInducing.isUltraUniformity
  statement: [IsUltraUniformity Y] {f : X -> Y}
  proof: hf.comap_uniformSpace ▸ .comap inferInstance f

中文:
引理 是UniformInducing.isUltraUniformity
  结论: [是UltraUniformity Y] {f : X -> Y}
  证明: hf.comap_uniformSpace ▸ .comap inferInstance f

Depends on / 依赖: comap_uniformSpace, hf.comap_uniformSpace
-/
lemma IsUniformInducing.isUltraUniformity [IsUltraUniformity Y] {f : X -> Y}
    (hf : IsUniformInducing f) : IsUltraUniformity X :=
  hf.comap_uniformSpace ▸ .comap inferInstance f

/--
Instance `CauchyFilter.isSymm_gen` / 实例 `CauchyFilter.isSymm_gen`

English:
instance CauchyFilter.isSymm_gen
  signature: {s : SetRel X X} [s.IsSymm]
  body: by simp [CauchyFilter.gen, s.mem_filter_prod_comm]

中文:
实例 CauchyFilter.isSymm_gen
  签名: {s : SetRel X X} [s.是Symm]
  定义体: by simp [CauchyFilter.gen, s.mem_filter_prod_comm]

Depends on / 依赖: CauchyFilter, CauchyFilter.gen, mem_filter_prod_comm, s.mem_filter_prod_comm
-/
instance CauchyFilter.isSymm_gen {s : SetRel X X} [s.IsSymm] : (gen s).IsSymm where
  symm _ := by simp [CauchyFilter.gen, s.mem_filter_prod_comm]


/--
Instance `CauchyFilter.isTrans_gen` / 实例 `CauchyFilter.isTrans_gen`

English:
instance CauchyFilter.isTrans_gen
  signature: {s : SetRel X X} [s.IsTrans]
  body: IsTransitiveRel.mem_filter_prod_trans

中文:
实例 CauchyFilter.isTrans_gen
  签名: {s : SetRel X X} [s.是Trans]
  定义体: IsTransitiveRel.mem_filter_prod_trans

Depends on / 依赖: IsTransitiveRel, IsTransitiveRel.mem_filter_prod_trans, mem_filter_prod_trans
-/
instance CauchyFilter.isTrans_gen {s : SetRel X X} [s.IsTrans] : (gen s).IsTrans where
  trans _ _ _ := IsTransitiveRel.mem_filter_prod_trans

/--
Instance `IsUltraUniformity.cauchyFilter` / 实例 `IsUltraUniformity.cauchyFilter`

English:
instance IsUltraUniformity.cauchyFilter
  signature: [IsUltraUniformity X]
  body: by
  apply mk_of_hasBasis (CauchyFilter.basis_uniformity IsUltraUniformity.hasBasis)
  · exact fun _ ⟨_, hU, _⟩ => by simpa using CauchyFilter.isSymm_gen
  · exact fun _ ⟨_, _, hU⟩ => by simpa using CauchyFilter.isTrans_gen

中文:
实例 是UltraUniformity.cauchyFilter
  签名: [是UltraUniformity X]
  定义体: by
  apply mk_of_hasBasis (CauchyFilter.basis_uniformity IsUltraUniformity.hasBasis)
  · exact fun _ ⟨_, hU, _⟩ => by simpa using CauchyFilter.isSymm_gen
  · exact fun _ ⟨_, _, hU⟩ => by simpa using CauchyFilter.isTrans_gen

Depends on / 依赖: CauchyFilter, CauchyFilter.basis_uniformity, CauchyFilter.isSymm_gen, CauchyFilter.isTrans_gen, IsUltraUniformity, IsUltraUniformity.hasBasis, basis_uniformity, hasBasis, isSymm_gen, isTrans_gen, mk_of_hasBasis
-/
instance IsUltraUniformity.cauchyFilter [IsUltraUniformity X] :
    IsUltraUniformity (CauchyFilter X) := by
  apply mk_of_hasBasis (CauchyFilter.basis_uniformity IsUltraUniformity.hasBasis)
  · exact fun _ ⟨_, hU, _⟩ => by simpa using CauchyFilter.isSymm_gen
  · exact fun _ ⟨_, _, hU⟩ => by simpa using CauchyFilter.isTrans_gen

/--
lemma `IsUltraUniformity.cauchyFilter_iff` / 引理 `IsUltraUniformity.cauchyFilter_iff`

English:
lemma IsUltraUniformity.cauchyFilter_iff
  proof: ⟨fun _ => CauchyFilter.isUniformInducing_pureCauchy.isUltraUniformity,
   fun _ => inferInstance⟩

中文:
引理 是UltraUniformity.cauchyFilter_iff
  证明: ⟨fun _ => CauchyFilter.isUniformInducing_pureCauchy.isUltraUniformity,
   fun _ => inferInstance⟩
-/
@[simp] lemma IsUltraUniformity.cauchyFilter_iff :
    IsUltraUniformity (CauchyFilter X) ↔ IsUltraUniformity X :=
  ⟨fun _ => CauchyFilter.isUniformInducing_pureCauchy.isUltraUniformity,
   fun _ => inferInstance⟩

/--
Instance `IsUltraUniformity.separationQuotient` / 实例 `IsUltraUniformity.separationQuotient`

English:
instance IsUltraUniformity.separationQuotient
  signature: [IsUltraUniformity X]
  body: by
  have := IsUltraUniformity.hasBasis.map
    (Prod.map SeparationQuotient.mk (SeparationQuotient.mk (X := X)))
  rw [← SeparationQuotient.uniformity_eq] at this
  apply mk_of_hasBasis this
  · exact fun _ ⟨_, hU, _⟩ => by rw [id_eq]; infer_instance
  · rintro U ⟨hU', _, hU⟩
    constructor
    ri

中文:
实例 是UltraUniformity.separationQuotient
  签名: [是UltraUniformity X]
  定义体: by
  have := IsUltraUniformity.hasBasis.map
    (Prod.map SeparationQuotient.mk (SeparationQuotient.mk (X := X)))
  rw [← SeparationQuotient.uniformity_eq] at this
  apply mk_of_hasBasis this
  · exact fun _ ⟨_, hU, _⟩ => by rw [id_eq]; infer_instance
  · rintro U ⟨hU', _, hU⟩
    constructor
    ri

Depends on / 依赖: IsUltraUniformity, IsUltraUniformity.hasBasis.map, Prod.exists, Prod.map, Prod.map_apply, Prod.mk.injEq, SeparationQuotient, SeparationQuotient.mk, SeparationQuotient.uniformity_eq, Set.mem_image, and_imp, eq_comm, forall_exists_index, hasBasis, id_eq, infer_instance, map_apply, mem_image, mk_of_hasBasis, uniformity_eq
-/
instance IsUltraUniformity.separationQuotient [IsUltraUniformity X] :
    IsUltraUniformity (SeparationQuotient X) := by
  have := IsUltraUniformity.hasBasis.map
    (Prod.map SeparationQuotient.mk (SeparationQuotient.mk (X := X)))
  rw [← SeparationQuotient.uniformity_eq] at this
  apply mk_of_hasBasis this
  · exact fun _ ⟨_, hU, _⟩ => by rw [id_eq]; infer_instance
  · rintro U ⟨hU', _, hU⟩
    constructor
    rintro x y z
    simp only [id_eq, Set.mem_image, Prod.exists, Prod.map_apply, Prod.mk.injEq,
      forall_exists_index, and_imp]
    rintro a b hab rfl rfl c d hcd hc rfl
    have hbc : (b, c) in U := by
      rw [eq_comm]; rw [SeparationQuotient.mk_eq_mk]; rw [inseparable_iff_ker_uniformity]; rw [Filter.mem_ker] at hc
      exact hc _ hU'
    exact ⟨a, d, U.trans (U.trans hab hbc) hcd, by simp, by simp⟩

/--
lemma `IsUltraUniformity.separationQuotient_iff` / 引理 `IsUltraUniformity.separationQuotient_iff`

English:
lemma IsUltraUniformity.separationQuotient_iff
  proof: ⟨fun _ => SeparationQuotient.isUniformInducing_mk.isUltraUniformity,
   fun _ => inferInstance⟩

中文:
引理 是UltraUniformity.separationQuotient_iff
  证明: ⟨fun _ => SeparationQuotient.isUniformInducing_mk.isUltraUniformity,
   fun _ => inferInstance⟩
-/
@[simp] lemma IsUltraUniformity.separationQuotient_iff :
    IsUltraUniformity (SeparationQuotient X) ↔ IsUltraUniformity X :=
  ⟨fun _ => SeparationQuotient.isUniformInducing_mk.isUltraUniformity,
   fun _ => inferInstance⟩

/--
lemma `IsUltraUniformity.completion_iff` / 引理 `IsUltraUniformity.completion_iff`

English:
lemma IsUltraUniformity.completion_iff
  proof: by
  rw [iff_comm]; rw [← cauchyFilter_iff]; rw [← separationQuotient_iff]
  exact Iff.rfl

中文:
引理 是UltraUniformity.completion_iff
  证明: by
  rw [iff_comm]; rw [← cauchyFilter_iff]; rw [← separationQuotient_iff]
  exact Iff.rfl
-/
@[simp] lemma IsUltraUniformity.completion_iff :
    IsUltraUniformity (UniformSpace.Completion X) ↔ IsUltraUniformity X := by
  rw [iff_comm]; rw [← cauchyFilter_iff]; rw [← separationQuotient_iff]
  exact Iff.rfl

/--
Instance `IsUltraUniformity.completion` / 实例 `IsUltraUniformity.completion`

English:
instance IsUltraUniformity.completion
  signature: [IsUltraUniformity X]
  body: completion_iff.2 inferInstance

中文:
实例 是UltraUniformity.completion
  签名: [是UltraUniformity X]
  定义体: completion_iff.2 inferInstance

Depends on / 依赖: completion_iff
-/
instance IsUltraUniformity.completion [IsUltraUniformity X] :
    IsUltraUniformity (UniformSpace.Completion X) :=
  completion_iff.2 inferInstance
