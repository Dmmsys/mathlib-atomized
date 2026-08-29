/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Bingyu Xia
-/
module

public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Data.Finsupp.Weight

/-!
# Functions tending to the cofinite filter

This file introduces the typeclass `Filter.TendstoCofinite`, which represents functions
`f : α → β` that tend to the cofinite filter along the cofinite filter. Functions of this class
are precisely the valid index transformations for renaming variables in multivariate power series.

## Main definitions

* `Filter.TendstoCofinite`: A typeclass for functions `f` satisfying
  `Filter.Tendsto f cofinite cofinite`. By `Filter.tendstoCofinite_iff_finite_preimage_singleton`,
  this is equivalent to `f` having finite fibers.
* `Filter.TendstoCofinite.mapDomain`: Given a function `v : α → M` into an `AddCommMonoid`,
  this is the pushforward function `β → M` defined by summing the values of `v` over the
  finite fibers of `f`.

## Main results

* `Filter.tendstoCofinite_iff_finite_preimage_singleton`: Characterizes `TendstoCofinite`
  as exactly those functions with finite fibers.
* Basic instances of `TendstoCofinite`.
* `Finsupp.mapDomain_tendstoCofinite`: Pushing forward finitely supported functions along
  a `TendstoCofinite` function preserves the `TendstoCofinite` property.

-/

@[expose] public section

variable {α β ι R M : Type*} (f : α -> β) (g : β -> ι) [AddCommMonoid M]

open Set Filter

namespace Filter

/--
Definition of `TendstoCofinite` / `TendstoCofinite` 的定义

English:
class TendstoCofinite
  parameters: (f : α -> β)
  axioms and operations (1):
    - tendsto_cofinite((f)) : Tendsto f cofinite cofinite

中文:
类 TendstoCofinite
  参数: (f : α -> β)
  公理与运算 (1 个):
    - tendsto_cofinite((f)) : 收敛 f cofinite cofinite
-/
@[mk_iff] class TendstoCofinite (f : α -> β) : Prop where
  tendsto_cofinite (f) : Tendsto f cofinite cofinite

/--
lemma `TendstoCofinite.finite_preimage` / 引理 `TendstoCofinite.finite_preimage`

English:
lemma TendstoCofinite.finite_preimage
  given: [TendstoCofinite f] {s : Set β} (hs : s.Finite)
  proof: by
  simpa [compl_eq_univ_sdiff] using TendstoCofinite.tendsto_cofinite f
    (show univ \ s in cofinite by simpa [compl_eq_univ_sdiff])

中文:
引理 TendstoCofinite.finite_preimage
  条件: [TendstoCofinite f] {s : 集合 β} (hs : s.有限)
  证明: by
  simpa [compl_eq_univ_sdiff] using TendstoCofinite.tendsto_cofinite f
    (show univ \ s in cofinite by simpa [compl_eq_univ_sdiff])

Depends on / 依赖: TendstoCofinite, TendstoCofinite.tendsto_cofinite, cofinite, compl_eq_univ_sdiff, tendsto_cofinite
-/
lemma TendstoCofinite.finite_preimage [TendstoCofinite f] {s : Set β} (hs : s.Finite) :
    Set.Finite (f ⁻¹' s) := by
  simpa [compl_eq_univ_sdiff] using TendstoCofinite.tendsto_cofinite f
    (show univ \ s in cofinite by simpa [compl_eq_univ_sdiff])

/--
lemma `TendstoCofinite.finite_preimage_singleton` / 引理 `TendstoCofinite.finite_preimage_singleton`

English:
lemma TendstoCofinite.finite_preimage_singleton
  given: [TendstoCofinite f] (b : β)
  proof: by simpa using TendstoCofinite.finite_preimage f (by simp)

中文:
引理 TendstoCofinite.finite_preimage_singleton
  条件: [TendstoCofinite f] (b : β)
  证明: by simpa using TendstoCofinite.finite_preimage f (by simp)

Depends on / 依赖: TendstoCofinite, TendstoCofinite.finite_preimage, finite_preimage
-/
lemma TendstoCofinite.finite_preimage_singleton [TendstoCofinite f] (b : β) :
    Set.Finite (f ⁻¹' {b}) := by simpa using TendstoCofinite.finite_preimage f (by simp)

/--
theorem `tendstoCofinite_iff_finite_preimage_singleton` / 定理 `tendstoCofinite_iff_finite_preimage_singleton`

English:
theorem tendstoCofinite_iff_finite_preimage_singleton
  statement: TendstoCofinite f ↔
  proof: ⟨fun _ => TendstoCofinite.finite_preimage_singleton f,
  fun h => ⟨Tendsto.cofinite_of_finite_preimage_singleton h⟩⟩

中文:
定理 tendstoCofinite_iff_finite_preimage_singleton
  结论: TendstoCofinite f ↔
  证明: ⟨fun _ => TendstoCofinite.finite_preimage_singleton f,
  fun h => ⟨Tendsto.cofinite_of_finite_preimage_singleton h⟩⟩

Depends on / 依赖: TendstoCofinite, TendstoCofinite.finite_preimage_singleton, finite_preimage_singleton
-/
theorem tendstoCofinite_iff_finite_preimage_singleton : TendstoCofinite f ↔
    forall b : β, Set.Finite (f ⁻¹' {b}) := ⟨fun _ => TendstoCofinite.finite_preimage_singleton f,
  fun h => ⟨Tendsto.cofinite_of_finite_preimage_singleton h⟩⟩

variable {f} in
/--
lemma `tendstoCofinite_of_injective` / 引理 `tendstoCofinite_of_injective`

English:
lemma tendstoCofinite_of_injective
  given: (h : f.Injective)
  statement: TendstoCofinite f
  proof: ⟨h.tendsto_cofinite⟩

@[instance]

中文:
引理 tendstoCofinite_of_injective
  条件: (h : f.单射)
  结论: TendstoCofinite f
  证明: ⟨h.tendsto_cofinite⟩

@[instance]

Depends on / 依赖: h.tendsto_cofinite, tendsto_cofinite
-/
lemma tendstoCofinite_of_injective (h : f.Injective) : TendstoCofinite f := ⟨h.tendsto_cofinite⟩

@[instance]
/--
lemma `tendstoCofinite_of_finite` / 引理 `tendstoCofinite_of_finite`

English:
lemma tendstoCofinite_of_finite
  given: [Finite α]
  statement: TendstoCofinite f
  proof: (tendstoCofinite_iff_finite_preimage_singleton f).mpr fun b => Set.toFinite (f ⁻¹' {b})

中文:
引理 tendstoCofinite_of_finite
  条件: [有限 α]
  结论: TendstoCofinite f
  证明: (tendstoCofinite_iff_finite_preimage_singleton f).mpr fun b => Set.toFinite (f ⁻¹' {b})

Depends on / 依赖: Set.toFinite, tendstoCofinite_iff_finite_preimage_singleton, toFinite
-/
lemma tendstoCofinite_of_finite [Finite α] : TendstoCofinite f :=
  (tendstoCofinite_iff_finite_preimage_singleton f).mpr fun b => Set.toFinite (f ⁻¹' {b})

namespace TendstoCofinite

@[instance]
/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  given: [TendstoCofinite g] [TendstoCofinite f]
  statement: TendstoCofinite (g ∘ f)
  proof: (tendstoCofinite_iff_finite_preimage_singleton _).mpr (fun r => by
    simpa using! TendstoCofinite.finite_preimage f (TendstoCofinite.finite_preimage g (by simp)))

@[instance]

中文:
引理 comp
  条件: [TendstoCofinite g] [TendstoCofinite f]
  结论: TendstoCofinite (g ∘ f)
  证明: (tendstoCofinite_iff_finite_preimage_singleton _).mpr (fun r => by
    simpa using! TendstoCofinite.finite_preimage f (TendstoCofinite.finite_preimage g (by simp)))

@[instance]

Depends on / 依赖: TendstoCofinite, TendstoCofinite.finite_preimage, finite_preimage, tendstoCofinite_iff_finite_preimage_singleton
-/
lemma comp [TendstoCofinite g] [TendstoCofinite f] : TendstoCofinite (g ∘ f) :=
  (tendstoCofinite_iff_finite_preimage_singleton _).mpr (fun r => by
    simpa using! TendstoCofinite.finite_preimage f (TendstoCofinite.finite_preimage g (by simp)))

@[instance]
/--
lemma `id` / 引理 `id`

English:
lemma id
  statement: TendstoCofinite (id : α -> α)
  proof: by simp [tendstoCofinite_iff_finite_preimage_singleton]

@[instance]

中文:
引理 id
  结论: TendstoCofinite (id : α -> α)
  证明: by simp [tendstoCofinite_iff_finite_preimage_singleton]

@[instance]

Depends on / 依赖: tendstoCofinite_iff_finite_preimage_singleton
-/
lemma id : TendstoCofinite (id : α -> α) := by simp [tendstoCofinite_iff_finite_preimage_singleton]

@[instance]
/--
lemma `embedding` / 引理 `embedding`

English:
lemma embedding
  given: (e : α ↪ β)
  statement: TendstoCofinite e
  proof: ⟨e.injective.tendsto_cofinite⟩

@[instance]

中文:
引理 embedding
  条件: (e : α ↪ β)
  结论: TendstoCofinite e
  证明: ⟨e.injective.tendsto_cofinite⟩

@[instance]

Depends on / 依赖: e.injective.tendsto_cofinite, injective, tendsto_cofinite
-/
lemma embedding (e : α ↪ β) : TendstoCofinite e := ⟨e.injective.tendsto_cofinite⟩

@[instance]
/--
lemma `equiv` / 引理 `equiv`

English:
lemma equiv
  given: (e : α ≃ β)
  statement: TendstoCofinite e
  proof: ⟨e.injective.tendsto_cofinite⟩

中文:
引理 equiv
  条件: (e : α ≃ β)
  结论: TendstoCofinite e
  证明: ⟨e.injective.tendsto_cofinite⟩

Depends on / 依赖: e.injective.tendsto_cofinite, injective, tendsto_cofinite
-/
lemma equiv (e : α ≃ β) : TendstoCofinite e := ⟨e.injective.tendsto_cofinite⟩

variable [TendstoCofinite f]

/--
Definition of `mapDomain` / `mapDomain` 的定义

English:
definition mapDomain
  signature: (v : α -> M)
  body: fun i => (finite_preimage_singleton f i).toFinset.sum v

@[simp]

中文:
定义 mapDomain
  签名: (v : α -> M)
  定义体: fun i => (finite_preimage_singleton f i).toFinset.sum v

@[simp]

Depends on / 依赖: finite_preimage_singleton, toFinset, toFinset.sum
-/
noncomputable def mapDomain (v : α -> M) : β -> M :=
  fun i => (finite_preimage_singleton f i).toFinset.sum v

@[simp]
/--
lemma `mapDomain_add` / 引理 `mapDomain_add`

English:
lemma mapDomain_add
  given: (u v : α -> M)
  statement: mapDomain f (u + v) = mapDomain f u + mapDomain f v
  proof: by
  ext; simp [mapDomain, Finset.sum_add_distrib]

@[simp]

中文:
引理 mapDomain_add
  条件: (u v : α -> M)
  结论: mapDomain f (u + v) = mapDomain f u + mapDomain f v
  证明: by
  ext; simp [mapDomain, Finset.sum_add_distrib]

@[simp]

Depends on / 依赖: Finset, Finset.sum_add_distrib, mapDomain, sum_add_distrib
-/
lemma mapDomain_add (u v : α -> M) : mapDomain f (u + v) = mapDomain f u + mapDomain f v := by
  ext; simp [mapDomain, Finset.sum_add_distrib]

@[simp]
/--
lemma `mapDomain_smul` / 引理 `mapDomain_smul`

English:
lemma mapDomain_smul
  given: [DistribSMul R M] (r : R) (v : α -> M)
  proof: by ext; simp [mapDomain, Finset.smul_sum]

中文:
引理 mapDomain_smul
  条件: [分配标量乘法 R M] (r : R) (v : α -> M)
  证明: by ext; simp [mapDomain, Finset.smul_sum]

Depends on / 依赖: Finset, Finset.smul_sum, mapDomain, smul_sum
-/
lemma mapDomain_smul [DistribSMul R M] (r : R) (v : α -> M) :
    mapDomain f (r • v) = r • (mapDomain f v) := by ext; simp [mapDomain, Finset.smul_sum]

/--
theorem `mapDomain_eq_zero` / 定理 `mapDomain_eq_zero`

English:
theorem mapDomain_eq_zero
  given: (v : α -> M) {i : β} (h' : i ∉ Set.range f)
  statement: mapDomain f v i = 0
  proof: by
  rw [← Set.preimage_singleton_eq_empty] at h'
  simp [mapDomain, Set.Finite.toFinset, h']

中文:
定理 mapDomain_eq_zero
  条件: (v : α -> M) {i : β} (h' : i ∉ 集合.range f)
  结论: mapDomain f v i = 0
  证明: by
  rw [← Set.preimage_singleton_eq_empty] at h'
  simp [mapDomain, Set.Finite.toFinset, h']

Depends on / 依赖: Finite, Set.Finite.toFinset, Set.preimage_singleton_eq_empty, mapDomain, preimage_singleton_eq_empty, toFinset
-/
theorem mapDomain_eq_zero (v : α -> M) {i : β} (h' : i ∉ Set.range f) : mapDomain f v i = 0 := by
  rw [← Set.preimage_singleton_eq_empty] at h'
  simp [mapDomain, Set.Finite.toFinset, h']

end TendstoCofinite

end Filter

@[instance]
/--
theorem `Finsupp.mapDomain_tendstoCofinite` / 定理 `Finsupp.mapDomain_tendstoCofinite`

English:
theorem Finsupp.mapDomain_tendstoCofinite
  given: [TendstoCofinite f]
  proof: by
  classical
  refine (tendstoCofinite_iff_finite_preimage_singleton _).mpr fun x => ?_
  let s := Finset.sup x.support (fun t => (TendstoCofinite.finite_preimage_singleton f t).toFinset)
  let e : s ↪ α := Function.Embedding.subtype (fun u => u in s)
  refine Set.Finite.subset (Set.Finite.image (embDomain e) <| finite_of_degree_le (degree x)) ?_
  simp only [Set.subset_def, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image,
    Set.mem_ofPred_eq]
  refine fun y hy => ⟨y.comapDomain e e.injective.injOn, ?_, embDomain_comapDomain ?_⟩
  · rw [← hy, degree_mapDomain]
    exact degree_comapDomain_le_of_canonicallyOrderedAdd ..
  · suffices y.support subseteq s by simpa [e]
    simpa [← hy, mapDomain, sum, Finset.subset_iff, single_apply, s] using
      fun i hi => ⟨i, by simp [hi]⟩

中文:
定理 有限支撑.mapDomain_tendstoCofinite
  条件: [TendstoCofinite f]
  证明: by
  classical
  refine (tendstoCofinite_iff_finite_preimage_singleton _).mpr fun x => ?_
  let s := Finset.sup x.support (fun t => (TendstoCofinite.finite_preimage_singleton f t).toFinset)
  let e : s ↪ α := Function.Embedding.subtype (fun u => u in s)
  refine Set.Finite.subset (Set.Finite.image (embDomain e) <| finite_of_degree_le (degree x)) ?_
  simp only [Set.subset_def, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image,
    Set.mem_ofPred_eq]
  refine fun y hy => ⟨y.comapDomain e e.injective.injOn, ?_, embDomain_comapDomain ?_⟩
  · rw [← hy, degree_mapDomain]
    exact degree_comapDomain_le_of_canonicallyOrderedAdd ..
  · suffices y.support subseteq s by simpa [e]
    simpa [← hy, mapDomain, sum, Finset.subset_iff, single_apply, s] using
      fun i hi => ⟨i, by simp [hi]⟩

Depends on / 依赖: Embedding, Finite, Finset, Finset.sup, Function, Function.Embedding.subtype, Set.Finite.image, Set.Finite.subset, Set.mem_image, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, Set.subset_def, TendstoCofinite, TendstoCofinite.finite_preimage_singleton, classical, comapDomain, degree, e.injectiv, embDomain
-/
theorem Finsupp.mapDomain_tendstoCofinite [TendstoCofinite f] :
    TendstoCofinite (mapDomain (M := Nat) f) := by
  classical
  refine (tendstoCofinite_iff_finite_preimage_singleton _).mpr fun x => ?_
  let s := Finset.sup x.support (fun t => (TendstoCofinite.finite_preimage_singleton f t).toFinset)
  let e : s ↪ α := Function.Embedding.subtype (fun u => u in s)
  refine Set.Finite.subset (Set.Finite.image (embDomain e) <| finite_of_degree_le (degree x)) ?_
  simp only [Set.subset_def, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image,
    Set.mem_ofPred_eq]
  refine fun y hy => ⟨y.comapDomain e e.injective.injOn, ?_, embDomain_comapDomain ?_⟩
  · rw [← hy, degree_mapDomain]
    exact degree_comapDomain_le_of_canonicallyOrderedAdd ..
  · suffices y.support subseteq s by simpa [e]
    simpa [← hy, mapDomain, sum, Finset.subset_iff, single_apply, s] using
      fun i hi => ⟨i, by simp [hi]⟩
