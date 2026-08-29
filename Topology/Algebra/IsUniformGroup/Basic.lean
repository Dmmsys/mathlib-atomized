/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.UniformSpace.CompleteSeparated
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Tactic.Abel

/-!
# Uniform structure on topological groups

## Main results

* extension of ℤ-bilinear maps to complete groups (useful for ring completions)

* `QuotientGroup.completeSpace_left` and `QuotientAddGroup.completeSpace_left` guarantee that
  quotients of first countable topological groups by normal subgroups are themselves complete, for
  the left uniformity. We also give versions for the right uniformity. In particular,
  the quotient of a Banach space by a subspace is complete.
-/

@[expose] public section

noncomputable section

open Uniformity Topology Filter Pointwise

section IsUniformGroup

open Filter Set

variable {α : Type*} {β : Type*}

variable [UniformSpace α] [Group α] [IsUniformGroup α]

@[to_additive]
/--
theorem `isUniformEmbedding_translate_mul` / 定理 `isUniformEmbedding_translate_mul`

English:
theorem isUniformEmbedding_translate_mul
  given: (a : α)
  statement: IsUniformEmbedding fun x : α => x * a
  proof: { comap_uniformity := by
      nth_rw 1 [← uniformity_translate_mul a, comap_map]
      rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
      simp only [Prod.mk.injEq, mul_left_inj, imp_self]
    injective := mul_left_injective a }

中文:
定理 isUniformEmbedding_translate_mul
  条件: (a : α)
  结论: 是一致嵌入 fun x : α => x * a
  证明: { comap_uniformity := by
      nth_rw 1 [← uniformity_translate_mul a, comap_map]
      rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
      simp only [Prod.mk.injEq, mul_left_inj, imp_self]
    injective := mul_left_injective a }

Depends on / 依赖: Prod.mk.injEq, comap_map, comap_uniformity, imp_self, injective, mul_left_inj, mul_left_injective, nth_rw, uniformity_translate_mul
-/
theorem isUniformEmbedding_translate_mul (a : α) : IsUniformEmbedding fun x : α => x * a :=
  { comap_uniformity := by
      nth_rw 1 [← uniformity_translate_mul a, comap_map]
      rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
      simp only [Prod.mk.injEq, mul_left_inj, imp_self]
    injective := mul_left_injective a }

section Cauchy

namespace IsUniformGroup

variable {ι G : Type*} [Group G] [UniformSpace G] [IsUniformGroup G]

@[to_additive]
/--
lemma `cauchy_iff_tendsto` / 引理 `cauchy_iff_tendsto`

English:
lemma cauchy_iff_tendsto
  given: (𝓕 : Filter G)
  proof: by
  simp [Cauchy, uniformity_eq_comap_nhds_one_swapped, ← tendsto_iff_comap]

@[to_additive]

中文:
引理 cauchy_iff_tendsto
  条件: (𝓕 : 滤子 G)
  证明: by
  simp [Cauchy, uniformity_eq_comap_nhds_one_swapped, ← tendsto_iff_comap]

@[to_additive]

Depends on / 依赖: Cauchy, tendsto_iff_comap, uniformity_eq_comap_nhds_one_swapped
-/
lemma cauchy_iff_tendsto (𝓕 : Filter G) :
    Cauchy 𝓕 ↔ NeBot 𝓕 ∧ Tendsto (fun p => p.1 / p.2) (𝓕 ×ˢ 𝓕) (𝓝 1) := by
  simp [Cauchy, uniformity_eq_comap_nhds_one_swapped, ← tendsto_iff_comap]

@[to_additive]
/--
lemma `cauchy_iff_tendsto_swapped` / 引理 `cauchy_iff_tendsto_swapped`

English:
lemma cauchy_iff_tendsto_swapped
  given: (𝓕 : Filter G)
  proof: by
  simp [Cauchy, uniformity_eq_comap_nhds_one, ← tendsto_iff_comap]

@[to_additive]

中文:
引理 cauchy_iff_tendsto_swapped
  条件: (𝓕 : 滤子 G)
  证明: by
  simp [Cauchy, uniformity_eq_comap_nhds_one, ← tendsto_iff_comap]

@[to_additive]

Depends on / 依赖: Cauchy, tendsto_iff_comap, uniformity_eq_comap_nhds_one
-/
lemma cauchy_iff_tendsto_swapped (𝓕 : Filter G) :
    Cauchy 𝓕 ↔ NeBot 𝓕 ∧ Tendsto (fun p => p.2 / p.1) (𝓕 ×ˢ 𝓕) (𝓝 1) := by
  simp [Cauchy, uniformity_eq_comap_nhds_one, ← tendsto_iff_comap]

@[to_additive]
/--
lemma `cauchy_map_iff_tendsto` / 引理 `cauchy_map_iff_tendsto`

English:
lemma cauchy_map_iff_tendsto
  given: (𝓕 : Filter ι) (f : ι -> G)
  proof: by
  simp [cauchy_map_iff, uniformity_eq_comap_nhds_one_swapped, Function.comp_def]

@[to_additive]

中文:
引理 cauchy_map_iff_tendsto
  条件: (𝓕 : 滤子 ι) (f : ι -> G)
  证明: by
  simp [cauchy_map_iff, uniformity_eq_comap_nhds_one_swapped, Function.comp_def]

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, cauchy_map_iff, comp_def, uniformity_eq_comap_nhds_one_swapped
-/
lemma cauchy_map_iff_tendsto (𝓕 : Filter ι) (f : ι -> G) :
    Cauchy (map f 𝓕) ↔ NeBot 𝓕 ∧ Tendsto (fun p => f p.1 / f p.2) (𝓕 ×ˢ 𝓕) (𝓝 1) := by
  simp [cauchy_map_iff, uniformity_eq_comap_nhds_one_swapped, Function.comp_def]

@[to_additive]
/--
lemma `cauchy_map_iff_tendsto_swapped` / 引理 `cauchy_map_iff_tendsto_swapped`

English:
lemma cauchy_map_iff_tendsto_swapped
  given: (𝓕 : Filter ι) (f : ι -> G)
  proof: by
  simp [cauchy_map_iff, uniformity_eq_comap_nhds_one, Function.comp_def]

中文:
引理 cauchy_map_iff_tendsto_swapped
  条件: (𝓕 : 滤子 ι) (f : ι -> G)
  证明: by
  simp [cauchy_map_iff, uniformity_eq_comap_nhds_one, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, cauchy_map_iff, comp_def, uniformity_eq_comap_nhds_one
-/
lemma cauchy_map_iff_tendsto_swapped (𝓕 : Filter ι) (f : ι -> G) :
    Cauchy (map f 𝓕) ↔ NeBot 𝓕 ∧ Tendsto (fun p => f p.2 / f p.1) (𝓕 ×ˢ 𝓕) (𝓝 1) := by
  simp [cauchy_map_iff, uniformity_eq_comap_nhds_one, Function.comp_def]

end IsUniformGroup

end Cauchy

namespace IsRightUniformGroup

variable {G : Type*} [Group G] [UniformSpace G] [IsRightUniformGroup G]

/-- A locally compact right-uniform group is complete. -/
@[to_additive
/-- A locally compact right-uniform additive group is complete. -/]
/--
theorem `completeSpace_of_weaklyLocallyCompactSpace` / 定理 `completeSpace_of_weaklyLocallyCompactSpace`

English:
theorem completeSpace_of_weaklyLocallyCompactSpace
  proof: by
    open scoped RightActions in
    have : f.NeBot := hf.1
    obtain ⟨K, K_compact, K_mem⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds (1 : G)
    obtain ⟨x, hx⟩ : exists x, forallᶠ y in f, y / x in K := by
      rw [cauchy_iff_le]; rw [uniformity_eq_comap_nhds_one]; rw [← tendsto_iff_c

中文:
定理 completeSpace_of_weaklyLocallyCompactSpace
  证明: by
    open scoped RightActions in
    have : f.NeBot := hf.1
    obtain ⟨K, K_compact, K_mem⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds (1 : G)
    obtain ⟨x, hx⟩ : exists x, forallᶠ y in f, y / x in K := by
      rw [cauchy_iff_le]; rw [uniformity_eq_comap_nhds_one]; rw [← tendsto_iff_c

Depends on / 依赖: IsComplete, K_compact, K_mem, Kx_complete, MulOpposite, MulOpposite.op_inv, RightActions, WeaklyLocallyCompactSpace, WeaklyLocallyCompactSpace.exists_compact_mem_nhds, cauchy_iff_le, curry.exists, div_eq_mul_inv, eventually_mem, exists_compact_mem_nhds, f.NeBot, hf.eventually_mem, isComplete, mem_smul_set_iff_inv_smul_mem, op_inv, op_smul_eq_mul
-/
theorem completeSpace_of_weaklyLocallyCompactSpace
    [WeaklyLocallyCompactSpace G] : CompleteSpace G where
  complete {f} hf := by
    open scoped RightActions in
    have : f.NeBot := hf.1
    obtain ⟨K, K_compact, K_mem⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds (1 : G)
    obtain ⟨x, hx⟩ : exists x, forallᶠ y in f, y / x in K := by
      rw [cauchy_iff_le]; rw [uniformity_eq_comap_nhds_one]; rw [← tendsto_iff_comap] at hf
.curry.exists exact hf.eventually_mem K_mem
    simp_rw [div_eq_mul_inv, ← op_smul_eq_mul, MulOpposite.op_inv,
      ← mem_smul_set_iff_inv_smul_mem] at hx
.isComplete have Kx_complete : IsComplete (K <• x) := K_compact.smul _
    obtain ⟨l, -, hl⟩ := Kx_complete f hf (by simpa using hx)
    exact ⟨l, hl⟩

end IsRightUniformGroup

namespace Subgroup

@[to_additive]
/--
Instance `isUniformGroup` / 实例 `isUniformGroup`

English:
instance isUniformGroup
  signature: (S : Subgroup α)
  body: .comap S.subtype

中文:
实例 isUniformGroup
  签名: (S : 子群 α)
  定义体: .comap S.subtype

Depends on / 依赖: S.subtype, subtype
-/
instance isUniformGroup (S : Subgroup α) : IsUniformGroup S := .comap S.subtype

end Subgroup

@[to_additive]
/--
theorem `CauchySeq.mul` / 定理 `CauchySeq.mul`

English:
theorem CauchySeq.mul
  statement: {ι : Type*} [Preorder ι] {u v : ι -> α} (hu : CauchySeq u)
  proof: uniformContinuous_mul.comp_cauchySeq (hu.prodMk hv)

@[to_additive]

中文:
定理 CauchySeq.mul
  结论: {ι : 类型} [预序 ι] {u v : ι -> α} (hu : CauchySeq u)
  证明: uniformContinuous_mul.comp_cauchySeq (hu.prodMk hv)

@[to_additive]

Depends on / 依赖: comp_cauchySeq, hu.prodMk, prodMk, uniformContinuous_mul, uniformContinuous_mul.comp_cauchySeq
-/
theorem CauchySeq.mul {ι : Type*} [Preorder ι] {u v : ι -> α} (hu : CauchySeq u)
    (hv : CauchySeq v) : CauchySeq (u * v) :=
  uniformContinuous_mul.comp_cauchySeq (hu.prodMk hv)

@[to_additive]
/--
theorem `CauchySeq.mul_const` / 定理 `CauchySeq.mul_const`

English:
theorem CauchySeq.mul_const
  given: {ι : Type*} [Preorder ι] {u : ι -> α} {x : α} (hu : CauchySeq u)
  proof: (uniformContinuous_id.mul uniformContinuous_const).comp_cauchySeq hu

@[to_additive]

中文:
定理 CauchySeq.mul_const
  条件: {ι : 类型} [预序 ι] {u : ι -> α} {x : α} (hu : CauchySeq u)
  证明: (uniformContinuous_id.mul uniformContinuous_const).comp_cauchySeq hu

@[to_additive]

Depends on / 依赖: comp_cauchySeq, uniformContinuous_const, uniformContinuous_id, uniformContinuous_id.mul
-/
theorem CauchySeq.mul_const {ι : Type*} [Preorder ι] {u : ι -> α} {x : α} (hu : CauchySeq u) :
    CauchySeq fun n => u n * x :=
  (uniformContinuous_id.mul uniformContinuous_const).comp_cauchySeq hu

@[to_additive]
/--
theorem `CauchySeq.const_mul` / 定理 `CauchySeq.const_mul`

English:
theorem CauchySeq.const_mul
  given: {ι : Type*} [Preorder ι] {u : ι -> α} {x : α} (hu : CauchySeq u)
  proof: (uniformContinuous_const.mul uniformContinuous_id).comp_cauchySeq hu

@[to_additive]

中文:
定理 CauchySeq.const_mul
  条件: {ι : 类型} [预序 ι] {u : ι -> α} {x : α} (hu : CauchySeq u)
  证明: (uniformContinuous_const.mul uniformContinuous_id).comp_cauchySeq hu

@[to_additive]

Depends on / 依赖: comp_cauchySeq, uniformContinuous_const, uniformContinuous_const.mul, uniformContinuous_id
-/
theorem CauchySeq.const_mul {ι : Type*} [Preorder ι] {u : ι -> α} {x : α} (hu : CauchySeq u) :
    CauchySeq fun n => x * u n :=
  (uniformContinuous_const.mul uniformContinuous_id).comp_cauchySeq hu

@[to_additive]
/--
theorem `CauchySeq.inv` / 定理 `CauchySeq.inv`

English:
theorem CauchySeq.inv
  given: {ι : Type*} [Preorder ι] {u : ι -> α} (h : CauchySeq u)
  proof: uniformContinuous_inv.comp_cauchySeq h

@[to_additive]

中文:
定理 CauchySeq.inv
  条件: {ι : 类型} [预序 ι] {u : ι -> α} (h : CauchySeq u)
  证明: uniformContinuous_inv.comp_cauchySeq h

@[to_additive]

Depends on / 依赖: comp_cauchySeq, uniformContinuous_inv, uniformContinuous_inv.comp_cauchySeq
-/
theorem CauchySeq.inv {ι : Type*} [Preorder ι] {u : ι -> α} (h : CauchySeq u) :
    CauchySeq u⁻¹ :=
  uniformContinuous_inv.comp_cauchySeq h

@[to_additive]
/--
theorem `totallyBounded_iff_subset_finite_iUnion_nhds_one` / 定理 `totallyBounded_iff_subset_finite_iUnion_nhds_one`

English:
theorem totallyBounded_iff_subset_finite_iUnion_nhds_one
  given: {s : Set α}
  proof: (𝓝 (1 : α)).basis_sets.uniformity_of_nhds_one_inv_mul_swapped.totallyBounded_iff.trans by
    simp [← preimage_smul_inv, preimage]

@[to_additive]

中文:
定理 totallyBounded_iff_subset_finite_iUnion_nhds_one
  条件: {s : 集合 α}
  证明: (𝓝 (1 : α)).basis_sets.uniformity_of_nhds_one_inv_mul_swapped.totallyBounded_iff.trans by
    simp [← preimage_smul_inv, preimage]

@[to_additive]

Depends on / 依赖: basis_sets, basis_sets.uniformity_of_nhds_one_inv_mul_swapped.totallyBounded_iff.trans, preimage, preimage_smul_inv, totallyBounded_iff, uniformity_of_nhds_one_inv_mul_swapped
-/
theorem totallyBounded_iff_subset_finite_iUnion_nhds_one {s : Set α} :
    TotallyBounded s ↔ forall U in 𝓝 (1 : α), exists t : Set α, t.Finite ∧ s subseteq ⋃ y in t, y • U :=
(𝓝 (1 : α)).basis_sets.uniformity_of_nhds_one_inv_mul_swapped.totallyBounded_iff.trans by
    simp [← preimage_smul_inv, preimage]

@[to_additive]
/--
lemma `TotallyBounded.inv` / 引理 `TotallyBounded.inv`

English:
lemma TotallyBounded.inv
  given: {s : Set α} (hs : TotallyBounded s)
  statement: TotallyBounded s⁻¹
  proof: by
  simpa using hs.image uniformContinuous_inv

@[to_additive (attr := simp)]

中文:
引理 全有界.inv
  条件: {s : 集合 α} (hs : 全有界 s)
  结论: 全有界 s⁻¹
  证明: by
  simpa using hs.image uniformContinuous_inv

@[to_additive (attr := simp)]
-/
protected lemma TotallyBounded.inv {s : Set α} (hs : TotallyBounded s) : TotallyBounded s⁻¹ := by
  simpa using hs.image uniformContinuous_inv

@[to_additive (attr := simp)]
/--
lemma `totallyBounded_inv` / 引理 `totallyBounded_inv`

English:
lemma totallyBounded_inv
  given: {s : Set α}
  statement: TotallyBounded s⁻¹ ↔ TotallyBounded s where
  proof: by simpa using hs.inv
  mpr := .inv

中文:
引理 totallyBounded_inv
  条件: {s : 集合 α}
  结论: 全有界 s⁻¹ ↔ 全有界 s where
  证明: by simpa using hs.inv
  mpr := .inv

Depends on / 依赖: hs.inv
-/
lemma totallyBounded_inv {s : Set α} : TotallyBounded s⁻¹ ↔ TotallyBounded s where
  mp hs := by simpa using hs.inv
  mpr := .inv

section UniformConvergence

variable {ι : Type*} {l : Filter ι} {l' : Filter β} {f f' : ι -> β -> α} {g g' : β -> α} {s : Set β}

@[to_additive (attr := to_fun)]
/--
theorem `TendstoUniformlyOnFilter.mul` / 定理 `TendstoUniformlyOnFilter.mul`

English:
theorem TendstoUniformlyOnFilter.mul
  statement: (hf : TendstoUniformlyOnFilter f g l l')
  proof: fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformlyOnFilter (hf.prodMk hf')) u hu).diag_of_prod_left

@[to_additive (attr := to_fun)]

中文:
定理 TendstoUniformlyOnFilter.mul
  结论: (hf : TendstoUniformlyOnFilter f g l l')
  证明: fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformlyOnFilter (hf.prodMk hf')) u hu).diag_of_prod_left

@[to_additive (attr := to_fun)]

Depends on / 依赖: comp_tendstoUniformlyOnFilter, diag_of_prod_left, hf.prodMk, prodMk, uniformContinuous_mul, uniformContinuous_mul.comp_tendstoUniformlyOnFilter
-/
theorem TendstoUniformlyOnFilter.mul (hf : TendstoUniformlyOnFilter f g l l')
    (hf' : TendstoUniformlyOnFilter f' g' l l') : TendstoUniformlyOnFilter (f * f') (g * g') l l' :=
  fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformlyOnFilter (hf.prodMk hf')) u hu).diag_of_prod_left

@[to_additive (attr := to_fun)]
/--
theorem `TendstoUniformlyOnFilter.div` / 定理 `TendstoUniformlyOnFilter.div`

English:
theorem TendstoUniformlyOnFilter.div
  statement: (hf : TendstoUniformlyOnFilter f g l l')
  proof: fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformlyOnFilter (hf.prodMk hf')) u hu).diag_of_prod_left

@[to_additive (attr := to_fun)]

中文:
定理 TendstoUniformlyOnFilter.div
  结论: (hf : TendstoUniformlyOnFilter f g l l')
  证明: fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformlyOnFilter (hf.prodMk hf')) u hu).diag_of_prod_left

@[to_additive (attr := to_fun)]

Depends on / 依赖: comp_tendstoUniformlyOnFilter, diag_of_prod_left, hf.prodMk, prodMk, uniformContinuous_div, uniformContinuous_div.comp_tendstoUniformlyOnFilter
-/
theorem TendstoUniformlyOnFilter.div (hf : TendstoUniformlyOnFilter f g l l')
    (hf' : TendstoUniformlyOnFilter f' g' l l') : TendstoUniformlyOnFilter (f / f') (g / g') l l' :=
  fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformlyOnFilter (hf.prodMk hf')) u hu).diag_of_prod_left

@[to_additive (attr := to_fun)]
/--
theorem `TendstoUniformlyOnFilter.inv` / 定理 `TendstoUniformlyOnFilter.inv`

English:
theorem TendstoUniformlyOnFilter.inv
  given: (hf : TendstoUniformlyOnFilter f g l l')
  proof: fun u hu => uniformContinuous_inv.comp_tendstoUniformlyOnFilter hf u hu

@[to_additive (attr := to_fun)]

中文:
定理 TendstoUniformlyOnFilter.inv
  条件: (hf : TendstoUniformlyOnFilter f g l l')
  证明: fun u hu => uniformContinuous_inv.comp_tendstoUniformlyOnFilter hf u hu

@[to_additive (attr := to_fun)]

Depends on / 依赖: comp_tendstoUniformlyOnFilter, uniformContinuous_inv, uniformContinuous_inv.comp_tendstoUniformlyOnFilter
-/
theorem TendstoUniformlyOnFilter.inv (hf : TendstoUniformlyOnFilter f g l l') :
    TendstoUniformlyOnFilter (f⁻¹) (g⁻¹) l l' :=
  fun u hu => uniformContinuous_inv.comp_tendstoUniformlyOnFilter hf u hu

@[to_additive (attr := to_fun)]
/--
theorem `TendstoUniformlyOn.mul` / 定理 `TendstoUniformlyOn.mul`

English:
theorem TendstoUniformlyOn.mul
  statement: (hf : TendstoUniformlyOn f g l s)
  proof: fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformlyOn (hf.prodMk hf')) u hu).diag_of_prod

@[to_additive (attr := to_fun)]

中文:
定理 TendstoUniformlyOn.mul
  结论: (hf : TendstoUniformlyOn f g l s)
  证明: fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformlyOn (hf.prodMk hf')) u hu).diag_of_prod

@[to_additive (attr := to_fun)]
-/
theorem TendstoUniformlyOn.mul (hf : TendstoUniformlyOn f g l s)
    (hf' : TendstoUniformlyOn f' g' l s) : TendstoUniformlyOn (f * f') (g * g') l s := fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformlyOn (hf.prodMk hf')) u hu).diag_of_prod

@[to_additive (attr := to_fun)]
/--
theorem `TendstoUniformlyOn.div` / 定理 `TendstoUniformlyOn.div`

English:
theorem TendstoUniformlyOn.div
  statement: (hf : TendstoUniformlyOn f g l s)
  proof: fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformlyOn (hf.prodMk hf')) u hu).diag_of_prod

@[to_additive (attr := to_fun)]

中文:
定理 TendstoUniformlyOn.div
  结论: (hf : TendstoUniformlyOn f g l s)
  证明: fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformlyOn (hf.prodMk hf')) u hu).diag_of_prod

@[to_additive (attr := to_fun)]
-/
theorem TendstoUniformlyOn.div (hf : TendstoUniformlyOn f g l s)
    (hf' : TendstoUniformlyOn f' g' l s) : TendstoUniformlyOn (f / f') (g / g') l s := fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformlyOn (hf.prodMk hf')) u hu).diag_of_prod

@[to_additive (attr := to_fun)]
/--
theorem `TendstoUniformlyOn.inv` / 定理 `TendstoUniformlyOn.inv`

English:
theorem TendstoUniformlyOn.inv
  given: (hf : TendstoUniformlyOn f g l s)
  proof: fun u hu => uniformContinuous_inv.comp_tendstoUniformlyOn hf u hu

@[to_additive (attr := to_fun)]

中文:
定理 TendstoUniformlyOn.inv
  条件: (hf : TendstoUniformlyOn f g l s)
  证明: fun u hu => uniformContinuous_inv.comp_tendstoUniformlyOn hf u hu

@[to_additive (attr := to_fun)]

Depends on / 依赖: comp_tendstoUniformlyOn, uniformContinuous_inv, uniformContinuous_inv.comp_tendstoUniformlyOn
-/
theorem TendstoUniformlyOn.inv (hf : TendstoUniformlyOn f g l s) :
    TendstoUniformlyOn (f⁻¹) (g⁻¹) l s :=
  fun u hu => uniformContinuous_inv.comp_tendstoUniformlyOn hf u hu

@[to_additive (attr := to_fun)]
/--
theorem `TendstoUniformly.mul` / 定理 `TendstoUniformly.mul`

English:
theorem TendstoUniformly.mul
  given: (hf : TendstoUniformly f g l) (hf' : TendstoUniformly f' g' l)
  proof: fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformly (hf.prodMk hf')) u hu).diag_of_prod

@[to_additive (attr := to_fun)]

中文:
定理 TendstoUniformly.mul
  条件: (hf : TendstoUniformly f g l) (hf' : TendstoUniformly f' g' l)
  证明: fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformly (hf.prodMk hf')) u hu).diag_of_prod

@[to_additive (attr := to_fun)]
-/
theorem TendstoUniformly.mul (hf : TendstoUniformly f g l) (hf' : TendstoUniformly f' g' l) :
    TendstoUniformly (f * f') (g * g') l := fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformly (hf.prodMk hf')) u hu).diag_of_prod

@[to_additive (attr := to_fun)]
/--
theorem `TendstoUniformly.div` / 定理 `TendstoUniformly.div`

English:
theorem TendstoUniformly.div
  given: (hf : TendstoUniformly f g l) (hf' : TendstoUniformly f' g' l)
  proof: fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformly (hf.prodMk hf')) u hu).diag_of_prod

@[to_additive (attr := to_fun)]

中文:
定理 TendstoUniformly.div
  条件: (hf : TendstoUniformly f g l) (hf' : TendstoUniformly f' g' l)
  证明: fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformly (hf.prodMk hf')) u hu).diag_of_prod

@[to_additive (attr := to_fun)]
-/
theorem TendstoUniformly.div (hf : TendstoUniformly f g l) (hf' : TendstoUniformly f' g' l) :
    TendstoUniformly (f / f') (g / g') l := fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformly (hf.prodMk hf')) u hu).diag_of_prod

@[to_additive (attr := to_fun)]
/--
theorem `TendstoUniformly.inv` / 定理 `TendstoUniformly.inv`

English:
theorem TendstoUniformly.inv
  given: (hf : TendstoUniformly f g l)
  proof: fun u hu => uniformContinuous_inv.comp_tendstoUniformly hf u hu

@[to_additive (attr := to_fun)]

中文:
定理 TendstoUniformly.inv
  条件: (hf : TendstoUniformly f g l)
  证明: fun u hu => uniformContinuous_inv.comp_tendstoUniformly hf u hu

@[to_additive (attr := to_fun)]

Depends on / 依赖: comp_tendstoUniformly, uniformContinuous_inv, uniformContinuous_inv.comp_tendstoUniformly
-/
theorem TendstoUniformly.inv (hf : TendstoUniformly f g l) :
    TendstoUniformly (f⁻¹) (g⁻¹) l :=
  fun u hu => uniformContinuous_inv.comp_tendstoUniformly hf u hu

@[to_additive (attr := to_fun)]
/--
theorem `UniformCauchySeqOn.mul` / 定理 `UniformCauchySeqOn.mul`

English:
theorem UniformCauchySeqOn.mul
  given: (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s)
  proof: fun u hu => by
  simpa using (uniformContinuous_mul.comp_uniformCauchySeqOn (hf.prod' hf')) u hu

@[to_additive (attr := to_fun)]

中文:
定理 UniformCauchySeqOn.mul
  条件: (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s)
  证明: fun u hu => by
  simpa using (uniformContinuous_mul.comp_uniformCauchySeqOn (hf.prod' hf')) u hu

@[to_additive (attr := to_fun)]

Depends on / 依赖: comp_uniformCauchySeqOn, hf.prod, uniformContinuous_mul, uniformContinuous_mul.comp_uniformCauchySeqOn
-/
theorem UniformCauchySeqOn.mul (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s) :
    UniformCauchySeqOn (f * f') l s := fun u hu => by
  simpa using (uniformContinuous_mul.comp_uniformCauchySeqOn (hf.prod' hf')) u hu

@[to_additive (attr := to_fun)]
/--
theorem `UniformCauchySeqOn.div` / 定理 `UniformCauchySeqOn.div`

English:
theorem UniformCauchySeqOn.div
  given: (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s)
  proof: fun u hu => by
  simpa using (uniformContinuous_div.comp_uniformCauchySeqOn (hf.prod' hf')) u hu

@[to_additive (attr := to_fun)]

中文:
定理 UniformCauchySeqOn.div
  条件: (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s)
  证明: fun u hu => by
  simpa using (uniformContinuous_div.comp_uniformCauchySeqOn (hf.prod' hf')) u hu

@[to_additive (attr := to_fun)]

Depends on / 依赖: comp_uniformCauchySeqOn, hf.prod, uniformContinuous_div, uniformContinuous_div.comp_uniformCauchySeqOn
-/
theorem UniformCauchySeqOn.div (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s) :
    UniformCauchySeqOn (f / f') l s := fun u hu => by
  simpa using (uniformContinuous_div.comp_uniformCauchySeqOn (hf.prod' hf')) u hu

@[to_additive (attr := to_fun)]
/--
theorem `UniformCauchySeqOn.inv` / 定理 `UniformCauchySeqOn.inv`

English:
theorem UniformCauchySeqOn.inv
  given: (hf : UniformCauchySeqOn f l s)
  proof: fun u hu => by simpa using (uniformContinuous_inv.comp_uniformCauchySeqOn hf u hu)

中文:
定理 UniformCauchySeqOn.inv
  条件: (hf : UniformCauchySeqOn f l s)
  证明: fun u hu => by simpa using (uniformContinuous_inv.comp_uniformCauchySeqOn hf u hu)

Depends on / 依赖: comp_uniformCauchySeqOn, uniformContinuous_inv, uniformContinuous_inv.comp_uniformCauchySeqOn
-/
theorem UniformCauchySeqOn.inv (hf : UniformCauchySeqOn f l s) :
    UniformCauchySeqOn (f⁻¹) l s :=
  fun u hu => by simpa using (uniformContinuous_inv.comp_uniformCauchySeqOn hf u hu)

end UniformConvergence

section LocalUniformConvergence

variable {ι X : Type*} [TopologicalSpace X] {F G : ι -> X -> α} {f g : X -> α} {s : Set X}
  {l : Filter ι}

@[to_additive (attr := to_fun)]
/--
theorem `TendstoLocallyUniformlyOn.mul` / 定理 `TendstoLocallyUniformlyOn.mul`

English:
theorem TendstoLocallyUniformlyOn.mul
  proof: uniformContinuous_mul.comp_tendstoLocallyUniformlyOn (hf.prodMk hg)

@[to_additive (attr := to_fun)]

中文:
定理 TendstoLocallyUniformlyOn.mul
  证明: uniformContinuous_mul.comp_tendstoLocallyUniformlyOn (hf.prodMk hg)

@[to_additive (attr := to_fun)]

Depends on / 依赖: comp_tendstoLocallyUniformlyOn, hf.prodMk, prodMk, uniformContinuous_mul, uniformContinuous_mul.comp_tendstoLocallyUniformlyOn
-/
theorem TendstoLocallyUniformlyOn.mul
    (hf : TendstoLocallyUniformlyOn F f l s) (hg : TendstoLocallyUniformlyOn G g l s) :
    TendstoLocallyUniformlyOn (F * G) (f * g) l s :=
  uniformContinuous_mul.comp_tendstoLocallyUniformlyOn (hf.prodMk hg)

@[to_additive (attr := to_fun)]
/--
theorem `TendstoLocallyUniformlyOn.div` / 定理 `TendstoLocallyUniformlyOn.div`

English:
theorem TendstoLocallyUniformlyOn.div
  proof: uniformContinuous_div.comp_tendstoLocallyUniformlyOn (hf.prodMk hg)

@[to_additive (attr := to_fun)]

中文:
定理 TendstoLocallyUniformlyOn.div
  证明: uniformContinuous_div.comp_tendstoLocallyUniformlyOn (hf.prodMk hg)

@[to_additive (attr := to_fun)]

Depends on / 依赖: comp_tendstoLocallyUniformlyOn, hf.prodMk, prodMk, uniformContinuous_div, uniformContinuous_div.comp_tendstoLocallyUniformlyOn
-/
theorem TendstoLocallyUniformlyOn.div
    (hf : TendstoLocallyUniformlyOn F f l s) (hg : TendstoLocallyUniformlyOn G g l s) :
    TendstoLocallyUniformlyOn (F / G) (f / g) l s :=
  uniformContinuous_div.comp_tendstoLocallyUniformlyOn (hf.prodMk hg)

@[to_additive (attr := to_fun)]
/--
theorem `TendstoLocallyUniformlyOn.inv` / 定理 `TendstoLocallyUniformlyOn.inv`

English:
theorem TendstoLocallyUniformlyOn.inv
  given: (hf : TendstoLocallyUniformlyOn F f l s)
  proof: uniformContinuous_inv.comp_tendstoLocallyUniformlyOn hf

@[to_additive (attr := to_fun)]

中文:
定理 TendstoLocallyUniformlyOn.inv
  条件: (hf : TendstoLocallyUniformlyOn F f l s)
  证明: uniformContinuous_inv.comp_tendstoLocallyUniformlyOn hf

@[to_additive (attr := to_fun)]

Depends on / 依赖: comp_tendstoLocallyUniformlyOn, uniformContinuous_inv, uniformContinuous_inv.comp_tendstoLocallyUniformlyOn
-/
theorem TendstoLocallyUniformlyOn.inv (hf : TendstoLocallyUniformlyOn F f l s) :
    TendstoLocallyUniformlyOn F⁻¹ f⁻¹ l s :=
  uniformContinuous_inv.comp_tendstoLocallyUniformlyOn hf

@[to_additive (attr := to_fun)]
/--
theorem `TendstoLocallyUniformly.mul` / 定理 `TendstoLocallyUniformly.mul`

English:
theorem TendstoLocallyUniformly.mul
  proof: uniformContinuous_mul.comp_tendstoLocallyUniformly (hf.prodMk hg)

@[to_additive (attr := to_fun)]

中文:
定理 TendstoLocallyUniformly.mul
  证明: uniformContinuous_mul.comp_tendstoLocallyUniformly (hf.prodMk hg)

@[to_additive (attr := to_fun)]

Depends on / 依赖: comp_tendstoLocallyUniformly, hf.prodMk, prodMk, uniformContinuous_mul, uniformContinuous_mul.comp_tendstoLocallyUniformly
-/
theorem TendstoLocallyUniformly.mul
    (hf : TendstoLocallyUniformly F f l) (hg : TendstoLocallyUniformly G g l) :
    TendstoLocallyUniformly (F * G) (f * g) l :=
  uniformContinuous_mul.comp_tendstoLocallyUniformly (hf.prodMk hg)

@[to_additive (attr := to_fun)]
/--
theorem `TendstoLocallyUniformly.div` / 定理 `TendstoLocallyUniformly.div`

English:
theorem TendstoLocallyUniformly.div
  proof: uniformContinuous_div.comp_tendstoLocallyUniformly (hf.prodMk hg)

@[to_additive (attr := to_fun)]

中文:
定理 TendstoLocallyUniformly.div
  证明: uniformContinuous_div.comp_tendstoLocallyUniformly (hf.prodMk hg)

@[to_additive (attr := to_fun)]

Depends on / 依赖: comp_tendstoLocallyUniformly, hf.prodMk, prodMk, uniformContinuous_div, uniformContinuous_div.comp_tendstoLocallyUniformly
-/
theorem TendstoLocallyUniformly.div
    (hf : TendstoLocallyUniformly F f l) (hg : TendstoLocallyUniformly G g l) :
    TendstoLocallyUniformly (F / G) (f / g) l :=
  uniformContinuous_div.comp_tendstoLocallyUniformly (hf.prodMk hg)

@[to_additive (attr := to_fun)]
/--
theorem `TendstoLocallyUniformly.inv` / 定理 `TendstoLocallyUniformly.inv`

English:
theorem TendstoLocallyUniformly.inv
  given: (hf : TendstoLocallyUniformly F f l)
  proof: uniformContinuous_inv.comp_tendstoLocallyUniformly hf

中文:
定理 TendstoLocallyUniformly.inv
  条件: (hf : TendstoLocallyUniformly F f l)
  证明: uniformContinuous_inv.comp_tendstoLocallyUniformly hf

Depends on / 依赖: comp_tendstoLocallyUniformly, uniformContinuous_inv, uniformContinuous_inv.comp_tendstoLocallyUniformly
-/
theorem TendstoLocallyUniformly.inv (hf : TendstoLocallyUniformly F f l) :
    TendstoLocallyUniformly F⁻¹ f⁻¹ l :=
  uniformContinuous_inv.comp_tendstoLocallyUniformly hf

end LocalUniformConvergence


@[to_additive]
instance (priority := 100) IsUniformGroup.of_compactSpace [UniformSpace β] [Group β]
    [ContinuousDiv β] [CompactSpace β] :
    IsUniformGroup β where
  uniformContinuous_div := CompactSpace.uniformContinuous_of_continuous continuous_div'

end IsUniformGroup

section IsTopologicalGroup

open Filter

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] IsTopologicalGroup.rightUniformSpace

variable {G}

@[to_additive]
/--
Instance `Subgroup.isClosed_of_discrete` / 实例 `Subgroup.isClosed_of_discrete`

English:
instance Subgroup.isClosed_of_discrete
  signature: [T2Space G] {H : Subgroup G} [DiscreteTopology H]
  body: by
  have hd : IsDiscrete (H : Set G) := isDiscrete_iff_discreteTopology.mpr ‹_›
  obtain ⟨V, V_in, VH⟩ : exists (V : Set G), V in 𝓝 (1 : G) ∧ V inter (H : Set G) = {1} :=
    nhds_inter_eq_singleton_of_mem_discrete hd H.one_mem
  have : (fun p : G × G => p.2 * p.1⁻¹) ⁻¹' V in 𝓤 G := preimage_mem_co

中文:
实例 子群.isClosed_of_discrete
  签名: [T2空间 G] {H : 子群 G} [离散拓扑 H]
  定义体: by
  have hd : IsDiscrete (H : Set G) := isDiscrete_iff_discreteTopology.mpr ‹_›
  obtain ⟨V, V_in, VH⟩ : exists (V : Set G), V in 𝓝 (1 : G) ∧ V inter (H : Set G) = {1} :=
    nhds_inter_eq_singleton_of_mem_discrete hd H.one_mem
  have : (fun p : G × G => p.2 * p.1⁻¹) ⁻¹' V in 𝓤 G := preimage_mem_co

Depends on / 依赖: H.mul_mem, H.one_mem, IsDiscrete, Set.mem_inter, Set.mem_preimage, V_in, contrapose, h_in, isClosed_of_spaced_out, isDiscrete_iff_discreteTopology, isDiscrete_iff_discreteTopology.mpr, mem_inter, mem_preimage, mul_mem, nhds_inter_eq_singleton_of_mem_discrete, one_mem, preimage_mem_comap
-/
instance Subgroup.isClosed_of_discrete [T2Space G] {H : Subgroup G} [DiscreteTopology H] :
    IsClosed (H : Set G) := by
  have hd : IsDiscrete (H : Set G) := isDiscrete_iff_discreteTopology.mpr ‹_›
  obtain ⟨V, V_in, VH⟩ : exists (V : Set G), V in 𝓝 (1 : G) ∧ V inter (H : Set G) = {1} :=
    nhds_inter_eq_singleton_of_mem_discrete hd H.one_mem
  have : (fun p : G × G => p.2 * p.1⁻¹) ⁻¹' V in 𝓤 G := preimage_mem_comap V_in
  apply isClosed_of_spaced_out this
  intro h h_in h' h'_in
  contrapose
  simp only [Set.mem_preimage]
  rintro (hyp : h' * h⁻¹ in V)
  have : h' * h⁻¹ in ({1} : Set G) := VH ▸ Set.mem_inter hyp (H.mul_mem h'_in (H.inv_mem h_in))
  exact (eq_of_mul_inv_eq_one this).symm

@[to_additive]
/--
lemma `Subgroup.tendsto_coe_cofinite_of_discrete` / 引理 `Subgroup.tendsto_coe_cofinite_of_discrete`

English:
lemma Subgroup.tendsto_coe_cofinite_of_discrete
  statement: [T2Space G] (H : Subgroup G)
  proof: haveI : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hH
  IsClosed.tendsto_coe_cofinite_of_isDiscrete isClosed_of_discrete hH

@[to_additive]

中文:
引理 子群.tendsto_coe_cofinite_of_discrete
  结论: [T2空间 G] (H : 子群 G)
  证明: haveI : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hH
  IsClosed.tendsto_coe_cofinite_of_isDiscrete isClosed_of_discrete hH

@[to_additive]

Depends on / 依赖: DiscreteTopology, IsClosed, IsClosed.tendsto_coe_cofinite_of_isDiscrete, isClosed_of_discrete, isDiscrete_iff_discreteTopology, isDiscrete_iff_discreteTopology.mp, tendsto_coe_cofinite_of_isDiscrete
-/
lemma Subgroup.tendsto_coe_cofinite_of_discrete [T2Space G] (H : Subgroup G)
    (hH : IsDiscrete (H : Set G)) : Tendsto ((↑) : H -> G) cofinite (cocompact _) :=
  haveI : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hH
  IsClosed.tendsto_coe_cofinite_of_isDiscrete isClosed_of_discrete hH

@[to_additive]
/--
lemma `MonoidHom.tendsto_coe_cofinite_of_discrete` / 引理 `MonoidHom.tendsto_coe_cofinite_of_discrete`

English:
lemma MonoidHom.tendsto_coe_cofinite_of_discrete
  statement: [T2Space G] {H : Type*} [Group H] {f : H ->* G}
  proof: by
  replace hf : Function.Injective f.rangeRestrict := by simpa
  exact (f.range.tendsto_coe_cofinite_of_discrete hf').comp hf.tendsto_cofinite

中文:
引理 幺半群态射.tendsto_coe_cofinite_of_discrete
  结论: [T2空间 G] {H : 类型} [群 H] {f : H ->* G}
  证明: by
  replace hf : Function.Injective f.rangeRestrict := by simpa
  exact (f.range.tendsto_coe_cofinite_of_discrete hf').comp hf.tendsto_cofinite

Depends on / 依赖: Function, Function.Injective, Injective, f.range.tendsto_coe_cofinite_of_discrete, f.rangeRestrict, hf.tendsto_cofinite, rangeRestrict, replace, tendsto_coe_cofinite_of_discrete, tendsto_cofinite
-/
lemma MonoidHom.tendsto_coe_cofinite_of_discrete [T2Space G] {H : Type*} [Group H] {f : H ->* G}
    (hf : Function.Injective f) (hf' : IsDiscrete (f.range : Set G)) :
    Tendsto f cofinite (cocompact _) := by
  replace hf : Function.Injective f.rangeRestrict := by simpa
  exact (f.range.tendsto_coe_cofinite_of_discrete hf').comp hf.tendsto_cofinite

end IsTopologicalGroup

namespace MulOpposite

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
lemma `comap_op_rightUniformSpace` / 引理 `comap_op_rightUniformSpace`

English:
lemma comap_op_rightUniformSpace
  proof: by
  ext : 1
  change comap (fun (x : G × G) => (MulOpposite.op x.1, MulOpposite.op x.2))
      (comap (fun p : Gᵐᵒᵖ × Gᵐᵒᵖ => p.2 * p.1⁻¹) (𝓝 1))
    = comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1)
  have : 𝓝 (1 : G) = comap (MulOpposite.opHomeomorph) (𝓝 (1 : Gᵐᵒᵖ)) := by
    simp [Homeomorph.comap_nh

中文:
引理 comap_op_rightUniformSpace
  证明: by
  ext : 1
  change comap (fun (x : G × G) => (MulOpposite.op x.1, MulOpposite.op x.2))
      (comap (fun p : Gᵐᵒᵖ × Gᵐᵒᵖ => p.2 * p.1⁻¹) (𝓝 1))
    = comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1)
  have : 𝓝 (1 : G) = comap (MulOpposite.opHomeomorph) (𝓝 (1 : Gᵐᵒᵖ)) := by
    simp [Homeomorph.comap_nh
-/
@[to_additive] lemma comap_op_rightUniformSpace :
    (IsTopologicalGroup.rightUniformSpace Gᵐᵒᵖ).comap MulOpposite.op =
      IsTopologicalGroup.leftUniformSpace G := by
  ext : 1
  change comap (fun (x : G × G) => (MulOpposite.op x.1, MulOpposite.op x.2))
      (comap (fun p : Gᵐᵒᵖ × Gᵐᵒᵖ => p.2 * p.1⁻¹) (𝓝 1))
    = comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1)
  have : 𝓝 (1 : G) = comap (MulOpposite.opHomeomorph) (𝓝 (1 : Gᵐᵒᵖ)) := by
    simp [Homeomorph.comap_nhds_eq]
  simp_rw [comap_comap, this, comap_comap]
  rfl

/--
lemma `comap_op_leftUniformSpace` / 引理 `comap_op_leftUniformSpace`

English:
lemma comap_op_leftUniformSpace
  proof: by
  ext : 1
  change comap (fun (x : G × G) => (MulOpposite.op x.1, MulOpposite.op x.2))
      (comap (fun p : Gᵐᵒᵖ × Gᵐᵒᵖ => p.1⁻¹ * p.2) (𝓝 1))
    = comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1)
  have : 𝓝 (1 : G) = comap (MulOpposite.opHomeomorph) (𝓝 (1 : Gᵐᵒᵖ)) := by
    simp [Homeomorph.comap_nh

中文:
引理 comap_op_leftUniformSpace
  证明: by
  ext : 1
  change comap (fun (x : G × G) => (MulOpposite.op x.1, MulOpposite.op x.2))
      (comap (fun p : Gᵐᵒᵖ × Gᵐᵒᵖ => p.1⁻¹ * p.2) (𝓝 1))
    = comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1)
  have : 𝓝 (1 : G) = comap (MulOpposite.opHomeomorph) (𝓝 (1 : Gᵐᵒᵖ)) := by
    simp [Homeomorph.comap_nh
-/
@[to_additive] lemma comap_op_leftUniformSpace :
    (IsTopologicalGroup.leftUniformSpace Gᵐᵒᵖ).comap MulOpposite.op =
      IsTopologicalGroup.rightUniformSpace G := by
  ext : 1
  change comap (fun (x : G × G) => (MulOpposite.op x.1, MulOpposite.op x.2))
      (comap (fun p : Gᵐᵒᵖ × Gᵐᵒᵖ => p.1⁻¹ * p.2) (𝓝 1))
    = comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1)
  have : 𝓝 (1 : G) = comap (MulOpposite.opHomeomorph) (𝓝 (1 : Gᵐᵒᵖ)) := by
    simp [Homeomorph.comap_nhds_eq]
  simp_rw [comap_comap, this, comap_comap]
  rfl

/-- The equivalence between a topological group `G` and `Gᵐᵒᵖ` as a uniform equivalence when `G`
is equipped with the right uniformity and `Gᵐᵒᵖ` with the left uniformity. -/
@[to_additive /-- The equivalence between an additive topological group `G` and `Gᵐᵒᵖ` as a uniform
equivalence when `G` is equipped with the right uniformity and `Gᵐᵒᵖ` with the left uniformity. -/]
/--
Definition of `opUniformEquivRight` / `opUniformEquivRight` 的定义

English:
definition opUniformEquivRight
  body: by
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  letI : UniformSpace Gᵐᵒᵖ := IsTopologicalGroup.leftUniformSpace Gᵐᵒᵖ
  refine ⟨MulOpposite.opEquiv, ?_, ?_⟩
  · simp [uniformContinuous_iff_le_comap, ← comap_op_leftUniformSpace]
  · simp [uniformContinuous_iff_le_comap, ← comap_

中文:
定义 opUniformEquivRight
  定义体: by
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  letI : UniformSpace Gᵐᵒᵖ := IsTopologicalGroup.leftUniformSpace Gᵐᵒᵖ
  refine ⟨MulOpposite.opEquiv, ?_, ?_⟩
  · simp [uniformContinuous_iff_le_comap, ← comap_op_leftUniformSpace]
  · simp [uniformContinuous_iff_le_comap, ← comap_

Depends on / 依赖: IsTopologicalGroup, IsTopologicalGroup.leftUniformSpace, IsTopologicalGroup.rightUniformSpace, MulOpposite, MulOpposite.opEquiv, UniformSpace, UniformSpace.comap_comap, comap_comap, comap_op_leftUniformSpace, leftUniformSpace, opEquiv, rightUniformSpace, uniformContinuous_iff_le_comap
-/
def opUniformEquivRight
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    @UniformEquiv G Gᵐᵒᵖ (IsTopologicalGroup.rightUniformSpace G)
      (IsTopologicalGroup.leftUniformSpace Gᵐᵒᵖ) := by
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  letI : UniformSpace Gᵐᵒᵖ := IsTopologicalGroup.leftUniformSpace Gᵐᵒᵖ
  refine ⟨MulOpposite.opEquiv, ?_, ?_⟩
  · simp [uniformContinuous_iff_le_comap, ← comap_op_leftUniformSpace]
  · simp [uniformContinuous_iff_le_comap, ← comap_op_leftUniformSpace, ← UniformSpace.comap_comap]

/-- The equivalence between a topological group `G` and `Gᵐᵒᵖ` as a uniform equivalence when `G`
is equipped with the left uniformity and `Gᵐᵒᵖ` with the right uniformity. -/
@[to_additive /-- The equivalence between an additive topological group `G` and `Gᵃᵒᵖ` as a uniform
equivalence when `G` is equipped with the left uniformity and `Gᵃᵒᵖ` with the right uniformity. -/]
/--
Definition of `opUniformEquivLeft` / `opUniformEquivLeft` 的定义

English:
definition opUniformEquivLeft
  body: by
  letI : UniformSpace G := IsTopologicalGroup.leftUniformSpace G
  letI : UniformSpace Gᵐᵒᵖ := IsTopologicalGroup.rightUniformSpace Gᵐᵒᵖ
  refine ⟨MulOpposite.opEquiv, ?_, ?_⟩
  · simp [uniformContinuous_iff_le_comap, ← comap_op_rightUniformSpace]
  · simp [uniformContinuous_iff_le_comap, ← comap

中文:
定义 opUniformEquivLeft
  定义体: by
  letI : UniformSpace G := IsTopologicalGroup.leftUniformSpace G
  letI : UniformSpace Gᵐᵒᵖ := IsTopologicalGroup.rightUniformSpace Gᵐᵒᵖ
  refine ⟨MulOpposite.opEquiv, ?_, ?_⟩
  · simp [uniformContinuous_iff_le_comap, ← comap_op_rightUniformSpace]
  · simp [uniformContinuous_iff_le_comap, ← comap

Depends on / 依赖: IsTopologicalGroup, IsTopologicalGroup.leftUniformSpace, IsTopologicalGroup.rightUniformSpace, MulOpposite, MulOpposite.opEquiv, UniformSpace, UniformSpace.comap_comap, comap_comap, comap_op_rightUniformSpace, leftUniformSpace, opEquiv, rightUniformSpace, uniformContinuous_iff_le_comap
-/
def opUniformEquivLeft
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    @UniformEquiv G Gᵐᵒᵖ (IsTopologicalGroup.leftUniformSpace G)
      (IsTopologicalGroup.rightUniformSpace Gᵐᵒᵖ) := by
  letI : UniformSpace G := IsTopologicalGroup.leftUniformSpace G
  letI : UniformSpace Gᵐᵒᵖ := IsTopologicalGroup.rightUniformSpace Gᵐᵒᵖ
  refine ⟨MulOpposite.opEquiv, ?_, ?_⟩
  · simp [uniformContinuous_iff_le_comap, ← comap_op_rightUniformSpace]
  · simp [uniformContinuous_iff_le_comap, ← comap_op_rightUniformSpace, ← UniformSpace.comap_comap]

end MulOpposite

section Inv

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive]
/--
lemma `comap_inv_leftUniformSpace` / 引理 `comap_inv_leftUniformSpace`

English:
lemma comap_inv_leftUniformSpace
  statement: (IsTopologicalGroup.leftUniformSpace G).comap (Equiv.inv G)
  proof: by
  ext : 1
  change comap (fun (x : G × G) => (Equiv.inv G x.1, Equiv.inv G x.2))
      (comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1)) =
    comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1)
  have : 𝓝 (1 : G) = comap (Homeomorph.inv G) (𝓝 1) := by rw [Homeomorph.comap_nhds_eq]; simp
  nth_rewrite 1 [this]

中文:
引理 comap_inv_leftUniformSpace
  结论: (是拓扑群.leftUniformSpace G).comap (等价.inv G)
  证明: by
  ext : 1
  change comap (fun (x : G × G) => (Equiv.inv G x.1, Equiv.inv G x.2))
      (comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1)) =
    comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1)
  have : 𝓝 (1 : G) = comap (Homeomorph.inv G) (𝓝 1) := by rw [Homeomorph.comap_nhds_eq]; simp
  nth_rewrite 1 [this]

Depends on / 依赖: Equiv.inv, Function, Function.comp_def, Homeomorph, Homeomorph.comap_nhds_eq, Homeomorph.inv, comap_comap, comap_nhds_eq, comp_def, nth_rewrite
-/
lemma comap_inv_leftUniformSpace : (IsTopologicalGroup.leftUniformSpace G).comap (Equiv.inv G)
    = IsTopologicalGroup.rightUniformSpace G := by
  ext : 1
  change comap (fun (x : G × G) => (Equiv.inv G x.1, Equiv.inv G x.2))
      (comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1)) =
    comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1)
  have : 𝓝 (1 : G) = comap (Homeomorph.inv G) (𝓝 1) := by rw [Homeomorph.comap_nhds_eq]; simp
  nth_rewrite 1 [this]
  rw [comap_comap]; rw [comap_comap]
  simp [Function.comp_def]

/-- Inversion on a topological group, as a uniform equivalence between the right uniformity and
the left uniformity. -/
@[to_additive /-- Negation on an additive topological group, as a uniform equivalence between the
right uniformity and the left uniformity. -/]
/--
Definition of `UniformEquiv.inv` / `UniformEquiv.inv` 的定义

English:
definition UniformEquiv.inv
  signature: : @UniformEquiv G G (IsTopologicalGroup.rightUniformSpace G)
  body: by
  have A : @UniformContinuous G G (IsTopologicalGroup.rightUniformSpace G)
      (IsTopologicalGroup.leftUniformSpace G) (Equiv.inv G) := by
    apply uniformContinuous_iff_le_comap.2
    rw [← comap_inv_leftUniformSpace]
  have B : @UniformContinuous G G (IsTopologicalGroup.leftUniformSpace G)
 

中文:
定义 一致等价.inv
  签名: : @一致等价 G G (是拓扑群.rightUniformSpace G)
  定义体: by
  have A : @UniformContinuous G G (IsTopologicalGroup.rightUniformSpace G)
      (IsTopologicalGroup.leftUniformSpace G) (Equiv.inv G) := by
    apply uniformContinuous_iff_le_comap.2
    rw [← comap_inv_leftUniformSpace]
  have B : @UniformContinuous G G (IsTopologicalGroup.leftUniformSpace G)
 

Depends on / 依赖: Equiv.inv, IsTopologicalGroup, IsTopologicalGroup.leftUniformSpace, IsTopologicalGroup.rightUniformSpace, UniformContinuous, UniformEquiv, UniformEquiv.mk, UniformSpace, UniformSpace.comap_comap, comap_comap, comap_inv_leftUniformSpace, leftUniformSpace, rightUniformSpace, uniformContinuous_iff_le_comap
-/
def UniformEquiv.inv : @UniformEquiv G G (IsTopologicalGroup.rightUniformSpace G)
    (IsTopologicalGroup.leftUniformSpace G) := by
  have A : @UniformContinuous G G (IsTopologicalGroup.rightUniformSpace G)
      (IsTopologicalGroup.leftUniformSpace G) (Equiv.inv G) := by
    apply uniformContinuous_iff_le_comap.2
    rw [← comap_inv_leftUniformSpace]
  have B : @UniformContinuous G G (IsTopologicalGroup.leftUniformSpace G)
      (IsTopologicalGroup.rightUniformSpace G) (Equiv.inv G) := by
    apply uniformContinuous_iff_le_comap.2
    rw [← comap_inv_leftUniformSpace]; rw [← UniformSpace.comap_comap]
    simp
  exact @UniformEquiv.mk G G (IsTopologicalGroup.rightUniformSpace G)
    (IsTopologicalGroup.leftUniformSpace G) (Equiv.inv G) A B

@[to_additive]
/--
lemma `IsTopologicalGroup.completeSpace_rightUniformSpace_iff_leftUniformSpace` / 引理 `IsTopologicalGroup.completeSpace_rightUniformSpace_iff_leftUniformSpace`

English:
lemma IsTopologicalGroup.completeSpace_rightUniformSpace_iff_leftUniformSpace
  proof: @UniformEquiv.completeSpace_iff G G (IsTopologicalGroup.rightUniformSpace G)
    (IsTopologicalGroup.leftUniformSpace G) (UniformEquiv.inv G)

中文:
引理 是拓扑群.completeSpace_rightUniformSpace_iff_leftUniformSpace
  证明: @UniformEquiv.completeSpace_iff G G (IsTopologicalGroup.rightUniformSpace G)
    (IsTopologicalGroup.leftUniformSpace G) (UniformEquiv.inv G)

Depends on / 依赖: IsTopologicalGroup, IsTopologicalGroup.leftUniformSpace, IsTopologicalGroup.rightUniformSpace, UniformEquiv, UniformEquiv.completeSpace_iff, UniformEquiv.inv, completeSpace_iff, leftUniformSpace, rightUniformSpace
-/
lemma IsTopologicalGroup.completeSpace_rightUniformSpace_iff_leftUniformSpace :
    @CompleteSpace G (IsTopologicalGroup.rightUniformSpace G) ↔
    @CompleteSpace G (IsTopologicalGroup.leftUniformSpace G) :=
  @UniformEquiv.completeSpace_iff G G (IsTopologicalGroup.rightUniformSpace G)
    (IsTopologicalGroup.leftUniformSpace G) (UniformEquiv.inv G)

end Inv

namespace IsTopologicalGroup

variable {ι α G : Type*} [Group G] [u : UniformSpace G] [IsTopologicalGroup G]

@[to_additive]
/--
theorem `uniformCauchySeqOn_iff` / 定理 `uniformCauchySeqOn_iff`

English:
theorem uniformCauchySeqOn_iff
  statement: (F : ι -> α -> G) (p : Filter ι) (s : Set α)
  proof: by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩,
    fun h _ ⟨u, hu, hv⟩ => mem_of_superset (h u hu) fun _ hi a ha => hv (hi a ha)⟩

@[to_additive]

中文:
定理 uniformCauchySeqOn_iff
  结论: (F : ι -> α -> G) (p : 滤子 ι) (s : 集合 α)
  证明: by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩,
    fun h _ ⟨u, hu, hv⟩ => mem_of_superset (h u hu) fun _ hi a ha => hv (hi a ha)⟩

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, mem_of_superset
-/
theorem uniformCauchySeqOn_iff (F : ι -> α -> G) (p : Filter ι) (s : Set α)
    (hu : IsTopologicalGroup.rightUniformSpace G = u) :
    UniformCauchySeqOn F p s ↔ forall u in 𝓝 (1 : G), forallᶠ m in p ×ˢ p, forall a in s, F m.2 a / F m.1 a in u := by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩,
    fun h _ ⟨u, hu, hv⟩ => mem_of_superset (h u hu) fun _ hi a ha => hv (hi a ha)⟩

@[to_additive]
/--
theorem `tendstoUniformly_iff` / 定理 `tendstoUniformly_iff`

English:
theorem tendstoUniformly_iff
  statement: (F : ι -> α -> G) (f : α -> G) (p : Filter ι)
  proof: by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩,
    fun h _ ⟨u, hu, hv⟩ => mem_of_superset (h u hu) fun _ hi a => hv (hi a)⟩

@[to_additive]

中文:
定理 tendstoUniformly_iff
  结论: (F : ι -> α -> G) (f : α -> G) (p : 滤子 ι)
  证明: by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩,
    fun h _ ⟨u, hu, hv⟩ => mem_of_superset (h u hu) fun _ hi a => hv (hi a)⟩

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, mem_of_superset
-/
theorem tendstoUniformly_iff (F : ι -> α -> G) (f : α -> G) (p : Filter ι)
    (hu : IsTopologicalGroup.rightUniformSpace G = u) :
    TendstoUniformly F f p ↔ forall u in 𝓝 (1 : G), forallᶠ i in p, forall a, F i a / f a in u := by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩,
    fun h _ ⟨u, hu, hv⟩ => mem_of_superset (h u hu) fun _ hi a => hv (hi a)⟩

@[to_additive]
/--
theorem `tendstoUniformlyOn_iff` / 定理 `tendstoUniformlyOn_iff`

English:
theorem tendstoUniformlyOn_iff
  statement: (F : ι -> α -> G) (f : α -> G) (p : Filter ι) (s : Set α)
  proof: by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩,
    fun h _ ⟨u, hu, hv⟩ => mem_of_superset (h u hu) fun _ hi a ha => hv (hi a ha)⟩

@[to_additive]

中文:
定理 tendstoUniformlyOn_iff
  结论: (F : ι -> α -> G) (f : α -> G) (p : 滤子 ι) (s : 集合 α)
  证明: by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩,
    fun h _ ⟨u, hu, hv⟩ => mem_of_superset (h u hu) fun _ hi a ha => hv (hi a ha)⟩

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, mem_of_superset
-/
theorem tendstoUniformlyOn_iff (F : ι -> α -> G) (f : α -> G) (p : Filter ι) (s : Set α)
    (hu : IsTopologicalGroup.rightUniformSpace G = u) :
    TendstoUniformlyOn F f p s ↔ forall u in 𝓝 (1 : G), forallᶠ i in p, forall a in s, F i a / f a in u := by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩,
    fun h _ ⟨u, hu, hv⟩ => mem_of_superset (h u hu) fun _ hi a ha => hv (hi a ha)⟩

@[to_additive]
/--
theorem `tendstoLocallyUniformly_iff` / 定理 `tendstoLocallyUniformly_iff`

English:
theorem tendstoLocallyUniformly_iff
  statement: [TopologicalSpace α] (F : ι -> α -> G) (f : α -> G)
  proof: by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h _ ⟨u, hu, hv⟩ x =>
    Exists.imp (fun _ ⟨h, hp⟩ => ⟨h, mem_of_superset hp fun _ hi a ha => hv (hi a ha)⟩)
      (h u hu x)⟩

@[to_additive]

中文:
定理 tendstoLocallyUniformly_iff
  结论: [拓扑空间 α] (F : ι -> α -> G) (f : α -> G)
  证明: by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h _ ⟨u, hu, hv⟩ x =>
    Exists.imp (fun _ ⟨h, hp⟩ => ⟨h, mem_of_superset hp fun _ hi a ha => hv (hi a ha)⟩)
      (h u hu x)⟩

@[to_additive]

Depends on / 依赖: Exists, Exists.imp, div_eq_mul_inv, mem_of_superset
-/
theorem tendstoLocallyUniformly_iff [TopologicalSpace α] (F : ι -> α -> G) (f : α -> G)
    (p : Filter ι) (hu : IsTopologicalGroup.rightUniformSpace G = u) :
    TendstoLocallyUniformly F f p ↔
      forall u in 𝓝 (1 : G), forall (x : α), exists t in 𝓝 x, forallᶠ i in p, forall a in t, F i a / f a in u := by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h _ ⟨u, hu, hv⟩ x =>
    Exists.imp (fun _ ⟨h, hp⟩ => ⟨h, mem_of_superset hp fun _ hi a ha => hv (hi a ha)⟩)
      (h u hu x)⟩

@[to_additive]
/--
theorem `tendstoLocallyUniformlyOn_iff` / 定理 `tendstoLocallyUniformlyOn_iff`

English:
theorem tendstoLocallyUniformlyOn_iff
  statement: [TopologicalSpace α] (F : ι -> α -> G) (f : α -> G)
  proof: by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h _ ⟨u, hu, hv⟩ x =>
    (Exists.imp fun _ ⟨h, hp⟩ => ⟨h, mem_of_superset hp fun _ hi a ha => hv (hi a ha)⟩) ∘
      h u hu x⟩

中文:
定理 tendstoLocallyUniformlyOn_iff
  结论: [拓扑空间 α] (F : ι -> α -> G) (f : α -> G)
  证明: by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h _ ⟨u, hu, hv⟩ x =>
    (Exists.imp fun _ ⟨h, hp⟩ => ⟨h, mem_of_superset hp fun _ hi a ha => hv (hi a ha)⟩) ∘
      h u hu x⟩

Depends on / 依赖: Exists, Exists.imp, div_eq_mul_inv, mem_of_superset
-/
theorem tendstoLocallyUniformlyOn_iff [TopologicalSpace α] (F : ι -> α -> G) (f : α -> G)
    (p : Filter ι) (s : Set α) (hu : IsTopologicalGroup.rightUniformSpace G = u) :
    TendstoLocallyUniformlyOn F f p s ↔
      forall u in 𝓝 (1 : G), forall x in s, exists t in 𝓝[s] x, forallᶠ i in p, forall a in t, F i a / f a in u := by
  simp only [div_eq_mul_inv]
  exact hu ▸ ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h _ ⟨u, hu, hv⟩ x =>
    (Exists.imp fun _ ⟨h, hp⟩ => ⟨h, mem_of_superset hp fun _ hi a ha => hv (hi a ha)⟩) ∘
      h u hu x⟩

end IsTopologicalGroup

open Filter Set Function

section

variable {α : Type*} {β : Type*} {hom : Type*}
variable [TopologicalSpace α] [Group α] [IsTopologicalGroup α]

-- β is a dense subgroup of α, inclusion is denoted by e
variable [TopologicalSpace β] [Group β]
variable [FunLike hom β α] [MonoidHomClass hom β α] {e : hom}

@[to_additive]
/--
theorem `tendsto_div_comap_self` / 定理 `tendsto_div_comap_self`

English:
theorem tendsto_div_comap_self
  given: (de : IsDenseInducing e) (x₀ : α)
  proof: by
  have comm : ((fun x : α × α => x.2 / x.1) ∘ fun t : β × β => (e t.1, e t.2)) =
      e ∘ fun t : β × β => t.2 / t.1 := by
    ext t
    simp
  have lim : Tendsto (fun x : α × α => x.2 / x.1) (𝓝 (x₀, x₀)) (𝓝 (e 1)) := by
    simpa using! (continuous_div'.comp (@continuous_swap α α _ _)).tendsto 

中文:
定理 tendsto_div_comap_self
  条件: (de : 是DenseInducing e) (x₀ : α)
  证明: by
  have comm : ((fun x : α × α => x.2 / x.1) ∘ fun t : β × β => (e t.1, e t.2)) =
      e ∘ fun t : β × β => t.2 / t.1 := by
    ext t
    simp
  have lim : Tendsto (fun x : α × α => x.2 / x.1) (𝓝 (x₀, x₀)) (𝓝 (e 1)) := by
    simpa using! (continuous_div'.comp (@continuous_swap α α _ _)).tendsto 

Depends on / 依赖: Tendsto, continuous_div, continuous_swap, de.tendsto_comap_nhds_nhds, tendsto, tendsto_comap_nhds_nhds
-/
theorem tendsto_div_comap_self (de : IsDenseInducing e) (x₀ : α) :
    Tendsto (fun t : β × β => t.2 / t.1) ((comap fun p : β × β => (e p.1, e p.2)) <| 𝓝 (x₀, x₀))
      (𝓝 1) := by
  have comm : ((fun x : α × α => x.2 / x.1) ∘ fun t : β × β => (e t.1, e t.2)) =
      e ∘ fun t : β × β => t.2 / t.1 := by
    ext t
    simp
  have lim : Tendsto (fun x : α × α => x.2 / x.1) (𝓝 (x₀, x₀)) (𝓝 (e 1)) := by
    simpa using! (continuous_div'.comp (@continuous_swap α α _ _)).tendsto (x₀, x₀)
  simpa using! de.tendsto_comap_nhds_nhds lim comm

end

namespace IsDenseInducing

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variable {G : Type*}

-- β is a dense subgroup of α, inclusion is denoted by e
-- δ is a dense subgroup of γ, inclusion is denoted by f
variable [TopologicalSpace α] [AddCommGroup α] [IsTopologicalAddGroup α]
variable [TopologicalSpace β] [AddCommGroup β]
variable [TopologicalSpace γ] [AddCommGroup γ] [IsTopologicalAddGroup γ]
variable [TopologicalSpace δ] [AddCommGroup δ]
variable [UniformSpace G] [AddCommGroup G]
variable {e : β ->+ α} (de : IsDenseInducing e)
variable {f : δ ->+ γ} (df : IsDenseInducing f)
variable {φ : β ->+ δ ->+ G}
variable (hφ : Continuous (fun p : β × δ => φ p.1 p.2))
variable {W' : Set G} (W'_nhds : W' in 𝓝 (0 : G))
include de hφ

include W'_nhds in
/--
theorem `extend_Z_bilin_aux` / 定理 `extend_Z_bilin_aux`

English:
theorem extend_Z_bilin_aux
  given: (x₀ : α) (y₁ : δ)
  statement: exists U₂ in comap e (𝓝 x₀), forall x in U₂, forall x' in U₂,
  proof: by
  let Nx := 𝓝 x₀
  let ee := fun u : β × β => (e u.1, e u.2)
  have lim1 : Tendsto (fun a : β × β => (a.2 - a.1, y₁))
      (comap e Nx ×ˢ comap e Nx) (𝓝 (0, y₁)) := by
    have := Tendsto.prodMk (tendsto_sub_comap_self de x₀)
      (tendsto_const_nhds : Tendsto (fun _ : β × β => y₁) (comap ee <|

中文:
定理 extend_Z_bilin_aux
  条件: (x₀ : α) (y₁ : δ)
  结论: 存在 U₂ in comap e (𝓝 x₀), 对任意 x in U₂, 对任意 x' in U₂,
  证明: by
  let Nx := 𝓝 x₀
  let ee := fun u : β × β => (e u.1, e u.2)
  have lim1 : Tendsto (fun a : β × β => (a.2 - a.1, y₁))
      (comap e Nx ×ˢ comap e Nx) (𝓝 (0, y₁)) := by
    have := Tendsto.prodMk (tendsto_sub_comap_self de x₀)
      (tendsto_const_nhds : Tendsto (fun _ : β × β => y₁) (comap ee <|
-/
private theorem extend_Z_bilin_aux (x₀ : α) (y₁ : δ) : exists U₂ in comap e (𝓝 x₀), forall x in U₂, forall x' in U₂,
    (fun p : β × δ => φ p.1 p.2) (x' - x, y₁) in W' := by
  let Nx := 𝓝 x₀
  let ee := fun u : β × β => (e u.1, e u.2)
  have lim1 : Tendsto (fun a : β × β => (a.2 - a.1, y₁))
      (comap e Nx ×ˢ comap e Nx) (𝓝 (0, y₁)) := by
    have := Tendsto.prodMk (tendsto_sub_comap_self de x₀)
      (tendsto_const_nhds : Tendsto (fun _ : β × β => y₁) (comap ee <| 𝓝 (x₀, x₀)) (𝓝 y₁))
    rw [nhds_prod_eq]; rw [prod_comap_comap_eq]; rw [← nhds_prod_eq]
    exact (this :)
  have lim2 : Tendsto (fun p : β × δ => φ p.1 p.2) (𝓝 (0, y₁)) (𝓝 0) := by
    simpa using hφ.tendsto (0, y₁)
  have lim := lim2.comp lim1
  rw [tendsto_prod_self_iff] at lim
  simp_rw [forall_mem_comm]
  exact lim W' W'_nhds

variable [IsUniformAddGroup G]

include df W'_nhds in
/--
theorem `extend_Z_bilin_key` / 定理 `extend_Z_bilin_key`

English:
theorem extend_Z_bilin_key
  given: (x₀ : α) (y₀ : γ)
  statement: exists U in comap e (𝓝 x₀), exists V in comap f (𝓝 y₀),
  proof: by
  let ee := fun u : β × β => (e u.1, e u.2)
  let ff := fun u : δ × δ => (f u.1, f u.2)
  have lim_φ : Filter.Tendsto (fun p : β × δ => φ p.1 p.2) (𝓝 (0, 0)) (𝓝 0) := by
    simpa using hφ.tendsto (0, 0)
  have lim_φ_sub_sub :
    Tendsto (fun p : (β × β) × δ × δ => (fun p : β × δ => φ p.1 p.2) (

中文:
定理 extend_Z_bilin_key
  条件: (x₀ : α) (y₀ : γ)
  结论: 存在 U in comap e (𝓝 x₀), 存在 V in comap f (𝓝 y₀),
  证明: by
  let ee := fun u : β × β => (e u.1, e u.2)
  let ff := fun u : δ × δ => (f u.1, f u.2)
  have lim_φ : Filter.Tendsto (fun p : β × δ => φ p.1 p.2) (𝓝 (0, 0)) (𝓝 0) := by
    simpa using hφ.tendsto (0, 0)
  have lim_φ_sub_sub :
    Tendsto (fun p : (β × β) × δ × δ => (fun p : β × δ => φ p.1 p.2) (
-/
private theorem extend_Z_bilin_key (x₀ : α) (y₀ : γ) : exists U in comap e (𝓝 x₀), exists V in comap f (𝓝 y₀),
    forall x in U, forall x' in U, forall (y) (_ : y in V) (y') (_ : y' in V),
    (fun p : β × δ => φ p.1 p.2) (x', y') - (fun p : β × δ => φ p.1 p.2) (x, y) in W' := by
  let ee := fun u : β × β => (e u.1, e u.2)
  let ff := fun u : δ × δ => (f u.1, f u.2)
  have lim_φ : Filter.Tendsto (fun p : β × δ => φ p.1 p.2) (𝓝 (0, 0)) (𝓝 0) := by
    simpa using hφ.tendsto (0, 0)
  have lim_φ_sub_sub :
    Tendsto (fun p : (β × β) × δ × δ => (fun p : β × δ => φ p.1 p.2) (p.1.2 - p.1.1, p.2.2 - p.2.1))
      ((comap ee <| 𝓝 (x₀, x₀)) ×ˢ (comap ff <| 𝓝 (y₀, y₀))) (𝓝 0) := by
    have lim_sub_sub :
      Tendsto (fun p : (β × β) × δ × δ => (p.1.2 - p.1.1, p.2.2 - p.2.1))
        (comap ee (𝓝 (x₀, x₀)) ×ˢ comap ff (𝓝 (y₀, y₀))) (𝓝 0 ×ˢ 𝓝 0) := by
      have := Filter.prod_mono (tendsto_sub_comap_self de x₀) (tendsto_sub_comap_self df y₀)
      rwa [prod_map_map_eq] at this
    rw [← nhds_prod_eq] at lim_sub_sub
    exact Tendsto.comp lim_φ lim_sub_sub
  rcases exists_nhds_zero_quarter W'_nhds with ⟨W, W_nhds, W4⟩
  have :
    exists U₁ in comap e (𝓝 x₀), exists V₁ in comap f (𝓝 y₀), forall (x) (_ : x in U₁) (x') (_ : x' in U₁),
      forall (y) (_ : y in V₁) (y') (_ : y' in V₁), (fun p : β × δ => φ p.1 p.2) (x' - x, y' - y) in W := by
    rcases tendsto_prod_iff.1 lim_φ_sub_sub W W_nhds with ⟨U, U_in, V, V_in, H⟩
    rw [nhds_prod_eq]; rw [← prod_comap_comap_eq]; rw [mem_prod_same_iff] at U_in V_in
    rcases U_in with ⟨U₁, U₁_in, HU₁⟩
    rcases V_in with ⟨V₁, V₁_in, HV₁⟩
    exists U₁, U₁_in, V₁, V₁_in
    intro x x_in x' x'_in y y_in y' y'_in
    exact H _ _ (HU₁ (mk_mem_prod x_in x'_in)) (HV₁ (mk_mem_prod y_in y'_in))
  rcases this with ⟨U₁, U₁_nhds, V₁, V₁_nhds, H⟩
  obtain ⟨x₁, x₁_in⟩ : U₁.Nonempty := (de.comap_nhds_neBot _).nonempty_of_mem U₁_nhds
  obtain ⟨y₁, y₁_in⟩ : V₁.Nonempty := (df.comap_nhds_neBot _).nonempty_of_mem V₁_nhds
  have cont_flip : Continuous fun p : δ × β => φ.flip p.1 p.2 := by
    change Continuous ((fun p : β × δ => φ p.1 p.2) ∘ Prod.swap)
    exact hφ.comp continuous_swap
  rcases extend_Z_bilin_aux de hφ W_nhds x₀ y₁ with ⟨U₂, U₂_nhds, HU⟩
  rcases extend_Z_bilin_aux df cont_flip W_nhds y₀ x₁ with ⟨V₂, V₂_nhds, HV⟩
  exists U₁ inter U₂, inter_mem U₁_nhds U₂_nhds, V₁ inter V₂, inter_mem V₁_nhds V₂_nhds
  rintro x ⟨xU₁, xU₂⟩ x' ⟨x'U₁, x'U₂⟩ y ⟨yV₁, yV₂⟩ y' ⟨y'V₁, y'V₂⟩
  have key_formula : φ x' y' - φ x y
    = φ (x' - x) y₁ + φ (x' - x) (y' - y₁) + φ x₁ (y' - y) + φ (x - x₁) (y' - y) := by simp; abel
  rw [key_formula]
  have h₁ := HU x xU₂ x' x'U₂
  have h₂ := H x xU₁ x' x'U₁ y₁ y₁_in y' y'V₁
  have h₃ := HV y yV₂ y' y'V₂
  have h₄ := H x₁ x₁_in x xU₁ y yV₁ y' y'V₁
  exact W4 h₁ h₂ h₃ h₄

open IsDenseInducing

variable [T0Space G] [CompleteSpace G]

/--
theorem `extend_Z_bilin` / 定理 `extend_Z_bilin`

English:
theorem extend_Z_bilin
  statement: Continuous (extend (de.prodMap df) (fun p : β × δ => φ p.1 p.2))
  proof: by
  refine continuous_extend_of_cauchy _ ?_
  rintro ⟨x₀, y₀⟩
  constructor
  · apply NeBot.map
    apply comap_neBot
    intro U h
    rcases mem_closure_iff_nhds.1 ((de.prodMap df).dense (x₀, y₀)) U h with ⟨x, x_in, ⟨z, z_x⟩⟩
    exists z
    simp_all
  · suffices map (fun p : (β × δ) × β × δ => 

中文:
定理 extend_Z_bilin
  结论: 连续 (extend (de.prodMap df) (fun p : β × δ => φ p.1 p.2))
  证明: by
  refine continuous_extend_of_cauchy _ ?_
  rintro ⟨x₀, y₀⟩
  constructor
  · apply NeBot.map
    apply comap_neBot
    intro U h
    rcases mem_closure_iff_nhds.1 ((de.prodMap df).dense (x₀, y₀)) U h with ⟨x, x_in, ⟨z, z_x⟩⟩
    exists z
    simp_all
  · suffices map (fun p : (β × δ) × β × δ => 

Depends on / 依赖: NeBot.map, comap_neBot, continuous_extend_of_cauchy, de.prodMap, mem_closure_iff_nhds, prodMap, prod_map, uniformity_eq_comap_nhds_zero, x_in
-/
theorem extend_Z_bilin : Continuous (extend (de.prodMap df) (fun p : β × δ => φ p.1 p.2)) := by
  refine continuous_extend_of_cauchy _ ?_
  rintro ⟨x₀, y₀⟩
  constructor
  · apply NeBot.map
    apply comap_neBot
    intro U h
    rcases mem_closure_iff_nhds.1 ((de.prodMap df).dense (x₀, y₀)) U h with ⟨x, x_in, ⟨z, z_x⟩⟩
    exists z
    simp_all
  · suffices map (fun p : (β × δ) × β × δ => (fun p : β × δ => φ p.1 p.2) p.2 -
      (fun p : β × δ => φ p.1 p.2) p.1)
        (comap (fun p : (β × δ) × β × δ => ((e p.1.1, f p.1.2), (e p.2.1, f p.2.2)))
        (𝓝 (x₀, y₀) ×ˢ 𝓝 (x₀, y₀))) <= 𝓝 0 by
      rwa [uniformity_eq_comap_nhds_zero G, prod_map_map_eq, ← map_le_iff_le_comap, Filter.map_map,
        prod_comap_comap_eq]
    intro W' W'_nhds
    have key := extend_Z_bilin_key de df hφ W'_nhds x₀ y₀
    rcases key with ⟨U, U_nhds, V, V_nhds, h⟩
    rw [mem_comap] at U_nhds
    rcases U_nhds with ⟨U', U'_nhds, U'_sub⟩
    rw [mem_comap] at V_nhds
    rcases V_nhds with ⟨V', V'_nhds, V'_sub⟩
    rw [mem_map]; rw [mem_comap]; rw [nhds_prod_eq]
    exists (U' ×ˢ V') ×ˢ U' ×ˢ V'
    rw [mem_prod_same_iff]
    have := prod_mem_prod U'_nhds V'_nhds
    grind

end IsDenseInducing

section CompleteQuotient

universe u

open TopologicalSpace

/-- The quotient `G ⧸ N` of a complete first countable topological group `G` by a normal subgroup
is itself complete. [N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Because a topological group is not equipped with a `UniformSpace` instance by default, we must
explicitly provide it in order to consider completeness. See `QuotientGroup.completeSpace_right` for
a version in which `G` is already equipped with a uniform structure. -/
@[to_additive /-- The quotient `G ⧸ N` of a complete first countable topological additive group
`G` by a normal additive subgroup is itself complete. Consequently, quotients of Banach spaces by
subspaces are complete. [N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Because an additive topological group is not equipped with a `UniformSpace` instance by default,
we must explicitly provide it in order to consider completeness. See
`QuotientAddGroup.completeSpace_right` for a version in which `G` is already equipped with a uniform
structure. -/]
/--
Instance `QuotientGroup.completeSpace_right'` / 实例 `QuotientGroup.completeSpace_right'`

English:
instance QuotientGroup.completeSpace_right'
  signature: (G : Type u) [Group G] [TopologicalSpace G]
  body: by
  /- Since `G ⧸ N` is a topological group it is a uniform space, and since `G` is first countable
    the uniformities of both `G` and `G ⧸ N` are countably generated. Moreover, we may choose a
    sequential antitone neighborhood basis `u` for `𝓝 (1 : G)` so that `(u (n + 1)) ^ 2 ⊆ u n`, and
   

中文:
实例 商群.completeSpace_right'
  签名: (G : 类型u) [群 G] [拓扑空间 G]
  定义体: by
  /- Since `G ⧸ N` is a topological group it is a uniform space, and since `G` is first countable
    the uniformities of both `G` and `G ⧸ N` are countably generated. Moreover, we may choose a
    sequential antitone neighborhood basis `u` for `𝓝 (1 : G)` so that `(u (n + 1)) ^ 2 ⊆ u n`, and
   
-/
instance QuotientGroup.completeSpace_right' (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [FirstCountableTopology G] (N : Subgroup G) [N.Normal]
    [@CompleteSpace G (IsTopologicalGroup.rightUniformSpace G)] :
    @CompleteSpace (G ⧸ N) (IsTopologicalGroup.rightUniformSpace (G ⧸ N)) := by
  /- Since `G ⧸ N` is a topological group it is a uniform space, and since `G` is first countable
    the uniformities of both `G` and `G ⧸ N` are countably generated. Moreover, we may choose a
    sequential antitone neighborhood basis `u` for `𝓝 (1 : G)` so that `(u (n + 1)) ^ 2 ⊆ u n`, and
    this descends to an antitone neighborhood basis `v` for `𝓝 (1 : G ⧸ N)`. Since `𝓤 (G ⧸ N)` is
    countably generated, it suffices to show any Cauchy sequence `x` converges. -/
  let : UniformSpace (G ⧸ N) := IsTopologicalGroup.rightUniformSpace (G ⧸ N)
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : (𝓤 (G ⧸ N)).IsCountablyGenerated := comap.isCountablyGenerated _ _
  obtain ⟨u, hu, u_mul⟩ := IsTopologicalGroup.exists_antitone_basis_nhds_one G
  obtain ⟨hv, v_anti⟩ := hu.map ((↑) : G -> G ⧸ N)
  rw [← QuotientGroup.nhds_eq N 1]; rw [QuotientGroup.mk_one] at hv
  refine UniformSpace.complete_of_cauchySeq_tendsto fun x hx => ?_
  /- Given `n : ℕ`, for sufficiently large `a b : ℕ`, given any lift of `x b`, we can find a lift
    of `x a` such that the quotient of the lifts lies in `u n`. -/
  have key₀ : forall i j : Nat, exists M : Nat, j < M ∧ forall a b : Nat, M <= a -> M <= b ->
      forall g : G, x b = g -> exists g' : G, g / g' in u i ∧ x a = g' := by
    have h𝓤GN : (𝓤 (G ⧸ N)).HasBasis (fun _ => True) fun i => { x | x.snd / x.fst in (↑) '' u i } := by
      simpa [uniformity_eq_comap_nhds_one', div_eq_mul_inv] using! hv.comap _
    rw [h𝓤GN.cauchySeq_iff] at hx
    simp only [mem_ofPred_eq, forall_true_left, mem_image] at hx
    intro i j
    rcases hx i with ⟨M, hM⟩
    refine ⟨max j M + 1, (le_max_left _ _).trans_lt (lt_add_one _), fun a b ha hb g hg => ?_⟩
    obtain ⟨y, y_mem, hy⟩ :=
      hM a (((le_max_right j _).trans (lt_add_one _).le).trans ha) b
        (((le_max_right j _).trans (lt_add_one _).le).trans hb)
    refine
      ⟨y⁻¹ * g, by
        simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_cancel_left] using y_mem, ?_⟩
    rw [QuotientGroup.mk_mul]; rw [QuotientGroup.mk_inv]; rw [hy]; rw [hg]; rw [inv_div]; rw [div_mul_cancel]
  /- Inductively construct a subsequence `φ : ℕ → ℕ` using `key₀` so that if `a b : ℕ` exceed
    `φ (n + 1)`, then we may find lifts whose quotients lie within `u n`. -/
  set φ : Nat -> Nat := fun n => Nat.recOn n
(Classical.choose <| key₀ 0 0) fun k yk => Classical.choose key₀ (k + 1) yk
  have hφ :
    forall n : Nat,
      φ n < φ (n + 1) ∧
        forall a b : Nat,
          φ (n + 1) <= a ->
            φ (n + 1) <= b -> forall g : G, x b = g -> exists g' : G, g / g' in u (n + 1) ∧ x a = g' :=
    fun n => Classical.choose_spec (key₀ (n + 1) (φ n))
  /- Inductively construct a sequence `x' n : G` of lifts of `x (φ (n + 1))` such that quotients of
    successive terms lie in `x' n / x' (n + 1) ∈ u (n + 1)`. We actually need the proofs that each
    term is a lift to construct the next term, so we use a Σ-type. -/
  set x' : forall n, PSigma fun g : G => x (φ (n + 1)) = g := fun n =>
    Nat.recOn n
      ⟨Classical.choose (QuotientGroup.mk_surjective (x (φ 1))),
        (Classical.choose_spec (QuotientGroup.mk_surjective (x (φ 1)))).symm⟩
      fun k hk =>
⟨Classical.choose (hφ k).2 _ _ (hφ (k + 1)).1.le le_rfl hk.fst hk.snd,
        (Classical.choose_spec <| (hφ k).2 _ _ (hφ (k + 1)).1.le le_rfl hk.fst hk.snd).2⟩
  have hx' : forall n : Nat, (x' n).fst / (x' (n + 1)).fst in u (n + 1) := fun n =>
    (Classical.choose_spec <| (hφ n).2 _ _ (hφ (n + 1)).1.le le_rfl (x' n).fst (x' n).snd).1
  /- The sequence `x'` is Cauchy. This is where we exploit the condition on `u`. The key idea
    is to show by decreasing induction that `x' m / x' n ∈ u m` if `m ≤ n`. -/
  have x'_cauchy : CauchySeq fun n => (x' n).fst := by
    have h𝓤G : (𝓤 G).HasBasis (fun _ => True) fun i => { x | x.snd / x.fst in u i } := by
      simpa [uniformity_eq_comap_nhds_one', div_eq_mul_inv] using! hu.toHasBasis.comap _
    rw [h𝓤G.cauchySeq_iff']
    simp only [mem_ofPred_eq, forall_true_left]
    exact fun m =>
      ⟨m, fun n hmn =>
        Nat.decreasingInduction'
          (fun k _ _ hk => u_mul k ⟨_, hx' k, _, hk, div_mul_div_cancel _ _ _⟩) hmn
          (by simpa only [div_self'] using mem_of_mem_nhds (hu.mem _))⟩
  /- Since `G` is complete, `x'` converges to some `x₀`, and so the image of this sequence under
    the quotient map converges to `↑x₀`. The image of `x'` is a convergent subsequence of `x`, and
    since `x` is Cauchy, this implies it converges. -/
  rcases cauchySeq_tendsto_of_complete x'_cauchy with ⟨x₀, hx₀⟩
  refine
    ⟨↑x₀,
      tendsto_nhds_of_cauchySeq_of_subseq hx
        (strictMono_nat_of_lt_succ fun n => (hφ (n + 1)).1).tendsto_atTop ?_⟩
  convert! ((continuous_coinduced_rng : Continuous ((↑) : G -> G ⧸ N)).tendsto x₀).comp hx₀
  exact funext fun n => (x' n).snd

/-- The quotient `G ⧸ N` of a complete first countable uniform group `G` by a normal subgroup
is itself complete. In contrast to `QuotientGroup.completeSpace_right'`, in this version `G` is
already equipped with a uniform structure.
[N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Even though `G` is equipped with a uniform structure, the quotient `G ⧸ N` does not inherit a
uniform structure, so it is still provided manually via `IsTopologicalGroup.rightUniformSpace`.
In the most common use cases, this coincides (definitionally) with the uniform structure on the
quotient obtained via other means. -/
@[to_additive /-- The quotient `G ⧸ N` of a complete first countable uniform additive group
`G` by a normal additive subgroup is itself complete. Consequently, quotients of Banach spaces by
subspaces are complete. In contrast to `QuotientAddGroup.completeSpace_right'`, in this version
`G` is already equipped with a uniform structure.
[N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Even though `G` is equipped with a uniform structure, the quotient `G ⧸ N` does not inherit a
uniform structure, so it is still provided manually via `IsTopologicalAddGroup.rightUniformSpace`.
-/]
/--
Instance `QuotientGroup.completeSpace_right` / 实例 `QuotientGroup.completeSpace_right`

English:
instance QuotientGroup.completeSpace_right
  signature: (G : Type*)
  body: by
  have : IsTopologicalGroup.rightUniformSpace G = us := by
    ext : 1
    rw [@IsRightUniformGroup.uniformity_eq (G := G) us _ _]
    rfl
  rw [← this] at hG
  infer_instance

中文:
实例 商群.completeSpace_right
  签名: (G : 类型)
  定义体: by
  have : IsTopologicalGroup.rightUniformSpace G = us := by
    ext : 1
    rw [@IsRightUniformGroup.uniformity_eq (G := G) us _ _]
    rfl
  rw [← this] at hG
  infer_instance

Depends on / 依赖: IsRightUniformGroup, IsRightUniformGroup.uniformity_eq, IsTopologicalGroup, IsTopologicalGroup.rightUniformSpace, infer_instance, rightUniformSpace, uniformity_eq
-/
instance QuotientGroup.completeSpace_right (G : Type*)
    [Group G] [us : UniformSpace G] [IsRightUniformGroup G]
    [FirstCountableTopology G] (N : Subgroup G) [N.Normal] [hG : CompleteSpace G] :
    @CompleteSpace (G ⧸ N) (IsTopologicalGroup.rightUniformSpace (G ⧸ N)) := by
  have : IsTopologicalGroup.rightUniformSpace G = us := by
    ext : 1
    rw [@IsRightUniformGroup.uniformity_eq (G := G) us _ _]
    rfl
  rw [← this] at hG
  infer_instance

/-- The quotient `G ⧸ N` of a complete first countable topological group `G` by a normal subgroup
is itself complete. [N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Because a topological group is not equipped with a `UniformSpace` instance by default, we must
explicitly provide it in order to consider completeness. See `QuotientGroup.completeSpace_left` for
a version in which `G` is already equipped with a uniform structure. -/
@[to_additive /-- The quotient `G ⧸ N` of a complete first countable topological additive group
`G` by a normal additive subgroup is itself complete. Consequently, quotients of Banach spaces by
subspaces are complete. [N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Because an additive topological group is not equipped with a `UniformSpace` instance by default,
we must explicitly provide it in order to consider completeness. See
`QuotientAddGroup.completeSpace_left` for a version in which `G` is already equipped with a uniform
structure. -/]
/--
Instance `QuotientGroup.completeSpace_left'` / 实例 `QuotientGroup.completeSpace_left'`

English:
instance QuotientGroup.completeSpace_left'
  signature: (G : Type u) [Group G] [TopologicalSpace G]
  body: by
  rw [← IsTopologicalGroup.completeSpace_rightUniformSpace_iff_leftUniformSpace] at hG ⊢
  infer_instance

中文:
实例 商群.completeSpace_left'
  签名: (G : 类型u) [群 G] [拓扑空间 G]
  定义体: by
  rw [← IsTopologicalGroup.completeSpace_rightUniformSpace_iff_leftUniformSpace] at hG ⊢
  infer_instance

Depends on / 依赖: IsTopologicalGroup, IsTopologicalGroup.completeSpace_rightUniformSpace_iff_leftUniformSpace, completeSpace_rightUniformSpace_iff_leftUniformSpace, infer_instance
-/
instance QuotientGroup.completeSpace_left' (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [FirstCountableTopology G] (N : Subgroup G) [N.Normal]
    [hG : @CompleteSpace G (IsTopologicalGroup.leftUniformSpace G)] :
    @CompleteSpace (G ⧸ N) (IsTopologicalGroup.leftUniformSpace (G ⧸ N)) := by
  rw [← IsTopologicalGroup.completeSpace_rightUniformSpace_iff_leftUniformSpace] at hG ⊢
  infer_instance

/-- The quotient `G ⧸ N` of a complete first countable uniform group `G` by a normal subgroup
is itself complete. In contrast to `QuotientGroup.completeSpace_left'`, in this version `G` is
already equipped with a uniform structure.
[N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Even though `G` is equipped with a uniform structure, the quotient `G ⧸ N` does not inherit a
uniform structure, so it is still provided manually via `IsTopologicalGroup.leftUniformSpace`.
In the most common use cases, this coincides (definitionally) with the uniform structure on the
quotient obtained via other means. -/
@[to_additive /-- The quotient `G ⧸ N` of a complete first countable uniform additive group
`G` by a normal additive subgroup is itself complete. Consequently, quotients of Banach spaces by
subspaces are complete. In contrast to `QuotientAddGroup.completeSpace_left'`, in this version
`G` is already equipped with a uniform structure.
[N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Even though `G` is equipped with a uniform structure, the quotient `G ⧸ N` does not inherit a
uniform structure, so it is still provided manually via `IsTopologicalAddGroup.leftUniformSpace`.
In the most common use case ─ quotients of normed additive commutative groups by subgroups ─
significant care was taken so that the uniform structure inherent in that setting coincides
(definitionally) with the uniform structure provided here. -/]
/--
Instance `QuotientGroup.completeSpace_left` / 实例 `QuotientGroup.completeSpace_left`

English:
instance QuotientGroup.completeSpace_left
  signature: (G : Type*)
  body: by
  have : IsTopologicalGroup.leftUniformSpace G = us := by
    ext : 1
    rw [@IsLeftUniformGroup.uniformity_eq (G := G) us _ _]
    rfl
  rw [← this] at hG
  infer_instance

中文:
实例 商群.completeSpace_left
  签名: (G : 类型)
  定义体: by
  have : IsTopologicalGroup.leftUniformSpace G = us := by
    ext : 1
    rw [@IsLeftUniformGroup.uniformity_eq (G := G) us _ _]
    rfl
  rw [← this] at hG
  infer_instance

Depends on / 依赖: IsLeftUniformGroup, IsLeftUniformGroup.uniformity_eq, IsTopologicalGroup, IsTopologicalGroup.leftUniformSpace, infer_instance, leftUniformSpace, uniformity_eq
-/
instance QuotientGroup.completeSpace_left (G : Type*)
    [Group G] [us : UniformSpace G] [IsLeftUniformGroup G]
    [FirstCountableTopology G] (N : Subgroup G) [N.Normal] [hG : CompleteSpace G] :
    @CompleteSpace (G ⧸ N) (IsTopologicalGroup.leftUniformSpace (G ⧸ N)) := by
  have : IsTopologicalGroup.leftUniformSpace G = us := by
    ext : 1
    rw [@IsLeftUniformGroup.uniformity_eq (G := G) us _ _]
    rfl
  rw [← this] at hG
  infer_instance

end CompleteQuotient
