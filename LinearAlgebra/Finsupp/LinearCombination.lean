/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Data.Finsupp.Option
public import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# `Finsupp.linearCombination`

## Main definitions

* `Finsupp.linearCombination R (v : ι → M)`: sends `l : ι →₀ R` to the linear combination of
  `v i` with coefficients `l i`;
* `Finsupp.linearCombinationOn`: a restricted version of `Finsupp.linearCombination` with domain

* `Fintype.linearCombination R (v : ι → M)`: sends `l : ι → R` to the linear combination of
  `v i` with coefficients `l i` (for a finite type `ι`)

* `Finsupp.bilinearCombination R S`, `Fintype.bilinearCombination R S`:
  a bilinear version of `Finsupp.linearCombination` and `Fintype.linearCombination`.
  It requires that `M` is both an `R`-module and an `S`-module, with `SMulCommClass R S M`;
  the case `S = R` typically requires that `R` is commutative.

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

section LinearCombination

variable (R)
variable {α' : Type*} {M' : Type*} [AddCommMonoid M'] [Module R M'] (v : α -> M) {v' : α' -> M'}

/--
Definition of `linearCombination` / `linearCombination` 的定义

English:
definition linearCombination
  signature: : (α ->₀ R) ->ₗ[R] M
  body: Finsupp.lsum Nat fun i => LinearMap.id.smulRight (v i)

中文:
定义 linearCombination
  签名: : (α ->₀ R) ->ₗ[R] M
  定义体: Finsupp.lsum Nat fun i => LinearMap.id.smulRight (v i)

Depends on / 依赖: Finsupp, Finsupp.lsum, LinearMap, LinearMap.id.smulRight, smulRight
-/
def linearCombination : (α ->₀ R) ->ₗ[R] M :=
  Finsupp.lsum Nat fun i => LinearMap.id.smulRight (v i)

variable {v}

/--
theorem `linearCombination_apply` / 定理 `linearCombination_apply`

English:
theorem linearCombination_apply
  given: (l : α ->₀ R)
  statement: linearCombination R v l = l.sum fun i a => a • v i
  proof: rfl

中文:
定理 linearCombination_apply
  条件: (l : α ->₀ R)
  结论: linearCombination R v l = l.sum fun i a => a • v i
  证明: rfl
-/
theorem linearCombination_apply (l : α ->₀ R) : linearCombination R v l = l.sum fun i a => a • v i :=
  rfl

/--
theorem `linearCombination_apply_of_mem_supported` / 定理 `linearCombination_apply_of_mem_supported`

English:
theorem linearCombination_apply_of_mem_supported
  statement: {l : α ->₀ R} {s : Finset α}
  proof: Finset.sum_subset hs fun x _ hxg =>
    show l x • v x = 0 by rw [notMem_support_iff.1 hxg, zero_smul]

@[simp]

中文:
定理 linearCombination_apply_of_mem_supported
  结论: {l : α ->₀ R} {s : Finset α}
  证明: Finset.sum_subset hs fun x _ hxg =>
    show l x • v x = 0 by rw [notMem_support_iff.1 hxg, zero_smul]

@[simp]

Depends on / 依赖: Finset, Finset.sum_subset, notMem_support_iff, sum_subset, zero_smul
-/
theorem linearCombination_apply_of_mem_supported {l : α ->₀ R} {s : Finset α}
    (hs : l in supported R R (↑s : Set α)) : linearCombination R v l = s.sum fun i => l i • v i :=
  Finset.sum_subset hs fun x _ hxg =>
    show l x • v x = 0 by rw [notMem_support_iff.1 hxg, zero_smul]

@[simp]
/--
theorem `linearCombination_single` / 定理 `linearCombination_single`

English:
theorem linearCombination_single
  given: (c : R) (a : α)
  proof: by
  simp [linearCombination_apply, sum_single_index]

中文:
定理 linearCombination_single
  条件: (c : R) (a : α)
  证明: by
  simp [linearCombination_apply, sum_single_index]

Depends on / 依赖: MeasurableSpace, linearCombination_apply, sum_single_index
-/
theorem linearCombination_single (c : R) (a : α) :
    linearCombination R v (single a c) = c • v a := by
  simp [linearCombination_apply, sum_single_index]

/--
theorem `linearCombination_zero_apply` / 定理 `linearCombination_zero_apply`

English:
theorem linearCombination_zero_apply
  given: (x : α ->₀ R)
  statement: (linearCombination R (0 : α -> M)) x = 0
  proof: by
  simp [linearCombination_apply]

中文:
定理 linearCombination_zero_apply
  条件: (x : α ->₀ R)
  结论: (linearCombination R (0 : α -> M)) x = 0
  证明: by
  simp [linearCombination_apply]

Depends on / 依赖: MeasurableDiv, MeasurableDiv.toMeasurableInv, MeasurableSpace, linearCombination_apply, toMeasurableInv
-/
theorem linearCombination_zero_apply (x : α ->₀ R) : (linearCombination R (0 : α -> M)) x = 0 := by
  simp [linearCombination_apply]

variable (α M)

@[simp]
/--
theorem `linearCombination_zero` / 定理 `linearCombination_zero`

English:
theorem linearCombination_zero
  statement: linearCombination R (0 : α -> M) = 0
  proof: LinearMap.ext (linearCombination_zero_apply R)

@[simp]

中文:
定理 linearCombination_zero
  结论: linearCombination R (0 : α -> M) = 0
  证明: LinearMap.ext (linearCombination_zero_apply R)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, linearCombination_zero_apply
-/
theorem linearCombination_zero : linearCombination R (0 : α -> M) = 0 :=
  LinearMap.ext (linearCombination_zero_apply R)

@[simp]
/--
theorem `linearCombination_single_index` / 定理 `linearCombination_single_index`

English:
theorem linearCombination_single_index
  given: (c : M) (a : α) (f : α ->₀ R) [DecidableEq α]
  proof: by
  rw [linearCombination_apply]; rw [sum_eq_single a]; rw [Pi.single_eq_same]
  · exact fun i _ hi => by rw [Pi.single_eq_of_ne hi, smul_zero]
  · exact fun _ => by simp only [zero_smul]

中文:
定理 linearCombination_single_index
  条件: (c : M) (a : α) (f : α ->₀ R) [DecidableEq α]
  证明: by
  rw [linearCombination_apply]; rw [sum_eq_single a]; rw [Pi.single_eq_same]
  · exact fun i _ hi => by rw [Pi.single_eq_of_ne hi, smul_zero]
  · exact fun _ => by simp only [zero_smul]

Depends on / 依赖: Pi.single_eq_of_ne, Pi.single_eq_same, linearCombination_apply, single_eq_of_ne, single_eq_same, smul_zero, sum_eq_single, zero_smul
-/
theorem linearCombination_single_index (c : M) (a : α) (f : α ->₀ R) [DecidableEq α] :
    linearCombination R (Pi.single a c) f = f a • c := by
  rw [linearCombination_apply]; rw [sum_eq_single a]; rw [Pi.single_eq_same]
  · exact fun i _ hi => by rw [Pi.single_eq_of_ne hi, smul_zero]
  · exact fun _ => by simp only [zero_smul]

variable {α M}

/--
theorem `linearCombination_linear_comp` / 定理 `linearCombination_linear_comp`

English:
theorem linearCombination_linear_comp
  given: (f : M ->ₗ[R] M')
  proof: by
  ext
  simp [linearCombination_apply]

中文:
定理 linearCombination_linear_comp
  条件: (f : M ->ₗ[R] M')
  证明: by
  ext
  simp [linearCombination_apply]

Depends on / 依赖: linearCombination_apply
-/
theorem linearCombination_linear_comp (f : M ->ₗ[R] M') :
    linearCombination R (f ∘ v) = f ∘ₗ linearCombination R v := by
  ext
  simp [linearCombination_apply]

/--
theorem `apply_linearCombination` / 定理 `apply_linearCombination`

English:
theorem apply_linearCombination
  given: (f : M ->ₗ[R] M') (v) (l : α ->₀ R)
  proof: congr($(linearCombination_linear_comp R f) l).symm

中文:
定理 apply_linearCombination
  条件: (f : M ->ₗ[R] M') (v) (l : α ->₀ R)
  证明: congr($(linearCombination_linear_comp R f) l).symm

Depends on / 依赖: linearCombination_linear_comp
-/
theorem apply_linearCombination (f : M ->ₗ[R] M') (v) (l : α ->₀ R) :
    f (linearCombination R v l) = linearCombination R (f ∘ v) l :=
  congr($(linearCombination_linear_comp R f) l).symm

/--
theorem `apply_linearCombination_id` / 定理 `apply_linearCombination_id`

English:
theorem apply_linearCombination_id
  given: (f : M ->ₗ[R] M') (l : M ->₀ R)
  proof: apply_linearCombination ..

中文:
定理 apply_linearCombination_id
  条件: (f : M ->ₗ[R] M') (l : M ->₀ R)
  证明: apply_linearCombination ..

Depends on / 依赖: apply_linearCombination
-/
theorem apply_linearCombination_id (f : M ->ₗ[R] M') (l : M ->₀ R) :
    f (linearCombination R _root_.id l) = linearCombination R f l :=
  apply_linearCombination ..

/--
theorem `linearCombination_unique` / 定理 `linearCombination_unique`

English:
theorem linearCombination_unique
  given: [Unique α] (l : α ->₀ R) (v : α -> M)
  proof: by
  rw [← linearCombination_single]; rw [← unique_single l]

中文:
定理 linearCombination_unique
  条件: [Unique α] (l : α ->₀ R) (v : α -> M)
  证明: by
  rw [← linearCombination_single]; rw [← unique_single l]

Depends on / 依赖: linearCombination_single, unique_single
-/
theorem linearCombination_unique [Unique α] (l : α ->₀ R) (v : α -> M) :
    linearCombination R v l = l default • v default := by
  rw [← linearCombination_single]; rw [← unique_single l]

/--
theorem `linearCombination_surjective` / 定理 `linearCombination_surjective`

English:
theorem linearCombination_surjective
  given: (h : Function.Surjective v)
  proof: by
  intro x
  obtain ⟨y, hy⟩ := h x
  exact ⟨single y 1, by simp [hy]⟩

中文:
定理 linearCombination_surjective
  条件: (h : Function.Surjective v)
  证明: by
  intro x
  obtain ⟨y, hy⟩ := h x
  exact ⟨single y 1, by simp [hy]⟩

Depends on / 依赖: single
-/
theorem linearCombination_surjective (h : Function.Surjective v) :
    Function.Surjective (linearCombination R v) := by
  intro x
  obtain ⟨y, hy⟩ := h x
  exact ⟨single y 1, by simp [hy]⟩

/--
theorem `linearCombination_range` / 定理 `linearCombination_range`

English:
theorem linearCombination_range
  given: (h : Function.Surjective v)
  proof: range_eq_top.2 linearCombination_surjective R h

中文:
定理 linearCombination_range
  条件: (h : Function.Surjective v)
  证明: range_eq_top.2 linearCombination_surjective R h

Depends on / 依赖: linearCombination_surjective, range_eq_top
-/
theorem linearCombination_range (h : Function.Surjective v) :
    LinearMap.range (linearCombination R v) = ⊤ :=
range_eq_top.2 linearCombination_surjective R h

/--
theorem `linearCombination_id_surjective` / 定理 `linearCombination_id_surjective`

English:
theorem linearCombination_id_surjective
  given: (M) [AddCommMonoid M] [Module R M]
  proof: linearCombination_surjective R Function.surjective_id

中文:
定理 linearCombination_id_surjective
  条件: (M) [AddCommMonoid M] [Module R M]
  证明: linearCombination_surjective R Function.surjective_id

Depends on / 依赖: Function, Function.surjective_id, linearCombination_surjective, surjective_id
-/
theorem linearCombination_id_surjective (M) [AddCommMonoid M] [Module R M] :
    Function.Surjective (linearCombination R (id : M -> M)) :=
  linearCombination_surjective R Function.surjective_id

/--
theorem `range_linearCombination` / 定理 `range_linearCombination`

English:
theorem range_linearCombination
  statement: LinearMap.range (linearCombination R v) = span R (range v)
  proof: by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_range] at hx
    rcases hx with ⟨l, hl⟩
    rw [← hl]
    rw [linearCombination_apply]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (subset_span (mem_range_self i))
  · apply span_le.2
    intro x hx
    rcases hx with ⟨i, hi⟩
    rw

中文:
定理 range_linearCombination
  结论: LinearMap.range (linearCombination R v) = span R (range v)
  证明: by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_range] at hx
    rcases hx with ⟨l, hl⟩
    rw [← hl]
    rw [linearCombination_apply]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (subset_span (mem_range_self i))
  · apply span_le.2
    intro x hx
    rcases hx with ⟨i, hi⟩
    rw

Depends on / 依赖: LinearMap, LinearMap.mem_range, SetLike, SetLike.mem_coe, Submodule, Submodule.smul_mem, linearCombination_apply, mem_coe, mem_range, mem_range_self, single, smul_mem, span_le, subset_span, sum_mem
-/
theorem range_linearCombination : LinearMap.range (linearCombination R v) = span R (range v) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_range] at hx
    rcases hx with ⟨l, hl⟩
    rw [← hl]
    rw [linearCombination_apply]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (subset_span (mem_range_self i))
  · apply span_le.2
    intro x hx
    rcases hx with ⟨i, hi⟩
    rw [SetLike.mem_coe]; rw [LinearMap.mem_range]
    use single i 1
    simp [hi]

/--
theorem `_root_.span_range_eq_top_iff_surjective_finsuppLinearCombination` / 定理 `_root_.span_range_eq_top_iff_surjective_finsuppLinearCombination`

English:
theorem _root_.span_range_eq_top_iff_surjective_finsuppLinearCombination
  proof: by
  rw [← LinearMap.range_eq_top]; rw [range_linearCombination]

中文:
定理 _root_.span_range_eq_top_iff_surjective_finsuppLinearCombination
  证明: by
  rw [← LinearMap.range_eq_top]; rw [range_linearCombination]

Depends on / 依赖: LinearMap, LinearMap.range_eq_top, range_eq_top, range_linearCombination
-/
theorem _root_.span_range_eq_top_iff_surjective_finsuppLinearCombination :
    Submodule.span R (Set.range v) = ⊤ ↔
      Function.Surjective (Finsupp.linearCombination R v) := by
  rw [← LinearMap.range_eq_top]; rw [range_linearCombination]

/--
theorem `lmapDomain_linearCombination` / 定理 `lmapDomain_linearCombination`

English:
theorem lmapDomain_linearCombination
  given: (f : α -> α') (g : M ->ₗ[R] M') (h : forall i, g (v i) = v' (f i))
  proof: by
  ext l
  simp [linearCombination_apply, h]

中文:
定理 lmapDomain_linearCombination
  条件: (f : α -> α') (g : M ->ₗ[R] M') (h : 对任意 i, g (v i) = v' (f i))
  证明: by
  ext l
  simp [linearCombination_apply, h]

Depends on / 依赖: linearCombination_apply
-/
theorem lmapDomain_linearCombination (f : α -> α') (g : M ->ₗ[R] M') (h : forall i, g (v i) = v' (f i)) :
    (linearCombination R v').comp (lmapDomain R R f) = g.comp (linearCombination R v) := by
  ext l
  simp [linearCombination_apply, h]

/--
theorem `linearCombination_comp_lmapDomain` / 定理 `linearCombination_comp_lmapDomain`

English:
theorem linearCombination_comp_lmapDomain
  given: (f : α -> α')
  proof: by
  ext
  simp

@[simp]

中文:
定理 linearCombination_comp_lmapDomain
  条件: (f : α -> α')
  证明: by
  ext
  simp

@[simp]
-/
theorem linearCombination_comp_lmapDomain (f : α -> α') :
    (linearCombination R v').comp (Finsupp.lmapDomain R R f) = linearCombination R (v' ∘ f) := by
  ext
  simp

@[simp]
/--
theorem `linearCombination_embDomain` / 定理 `linearCombination_embDomain`

English:
theorem linearCombination_embDomain
  given: (f : α ↪ α') (l : α ->₀ R)
  proof: by
  simp [linearCombination_apply, Finsupp.sum, support_embDomain, embDomain_apply]

@[simp]

中文:
定理 linearCombination_embDomain
  条件: (f : α ↪ α') (l : α ->₀ R)
  证明: by
  simp [linearCombination_apply, Finsupp.sum, support_embDomain, embDomain_apply]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum, embDomain_apply, linearCombination_apply, support_embDomain, toMeasurableSMul
-/
theorem linearCombination_embDomain (f : α ↪ α') (l : α ->₀ R) :
    (linearCombination R v') (embDomain f l) = (linearCombination R (v' ∘ f)) l := by
  simp [linearCombination_apply, Finsupp.sum, support_embDomain, embDomain_apply]

@[simp]
/--
theorem `linearCombination_mapDomain` / 定理 `linearCombination_mapDomain`

English:
theorem linearCombination_mapDomain
  given: (f : α -> α') (l : α ->₀ R)
  proof: LinearMap.congr_fun (linearCombination_comp_lmapDomain _ _) l

@[simp]

中文:
定理 linearCombination_mapDomain
  条件: (f : α -> α') (l : α ->₀ R)
  证明: LinearMap.congr_fun (linearCombination_comp_lmapDomain _ _) l

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, linearCombination_comp_lmapDomain
-/
theorem linearCombination_mapDomain (f : α -> α') (l : α ->₀ R) :
    (linearCombination R v') (mapDomain f l) = (linearCombination R (v' ∘ f)) l :=
  LinearMap.congr_fun (linearCombination_comp_lmapDomain _ _) l

@[simp]
/--
theorem `linearCombination_equivMapDomain` / 定理 `linearCombination_equivMapDomain`

English:
theorem linearCombination_equivMapDomain
  given: (f : α ≃ α') (l : α ->₀ R)
  proof: by
  rw [equivMapDomain_eq_mapDomain]; rw [linearCombination_mapDomain]

中文:
定理 linearCombination_equivMapDomain
  条件: (f : α ≃ α') (l : α ->₀ R)
  证明: by
  rw [equivMapDomain_eq_mapDomain]; rw [linearCombination_mapDomain]

Depends on / 依赖: equivMapDomain_eq_mapDomain, linearCombination_mapDomain
-/
theorem linearCombination_equivMapDomain (f : α ≃ α') (l : α ->₀ R) :
    (linearCombination R v') (equivMapDomain f l) = (linearCombination R (v' ∘ f)) l := by
  rw [equivMapDomain_eq_mapDomain]; rw [linearCombination_mapDomain]

/--
theorem `span_eq_range_linearCombination` / 定理 `span_eq_range_linearCombination`

English:
theorem span_eq_range_linearCombination
  given: (s : Set M)
  proof: by
  rw [range_linearCombination]; rw [Subtype.range_coe_subtype]; rw [Set.ofPred_mem_eq]

中文:
定理 span_eq_range_linearCombination
  条件: (s : Set M)
  证明: by
  rw [range_linearCombination]; rw [Subtype.range_coe_subtype]; rw [Set.ofPred_mem_eq]

Depends on / 依赖: Set.ofPred_mem_eq, Subtype, Subtype.range_coe_subtype, ofPred_mem_eq, range_coe_subtype, range_linearCombination
-/
theorem span_eq_range_linearCombination (s : Set M) :
    span R s = LinearMap.range (linearCombination R ((↑) : s -> M)) := by
  rw [range_linearCombination]; rw [Subtype.range_coe_subtype]; rw [Set.ofPred_mem_eq]

/--
theorem `mem_span_iff_linearCombination` / 定理 `mem_span_iff_linearCombination`

English:
theorem mem_span_iff_linearCombination
  given: (s : Set M) (x : M)
  proof: (SetLike.ext_iff.1 <| span_eq_range_linearCombination _ _) x

中文:
定理 mem_span_iff_linearCombination
  条件: (s : Set M) (x : M)
  证明: (SetLike.ext_iff.1 <| span_eq_range_linearCombination _ _) x

Depends on / 依赖: SetLike, SetLike.ext_iff, ext_iff, span_eq_range_linearCombination
-/
theorem mem_span_iff_linearCombination (s : Set M) (x : M) :
    x in span R s ↔ exists l : s ->₀ R, linearCombination R (↑) l = x :=
  (SetLike.ext_iff.1 <| span_eq_range_linearCombination _ _) x

variable {R} in
/--
theorem `mem_span_range_iff_exists_finsupp` / 定理 `mem_span_range_iff_exists_finsupp`

English:
theorem mem_span_range_iff_exists_finsupp
  given: {v : α -> M} {x : M}
  proof: by
  simp only [← Finsupp.range_linearCombination, LinearMap.mem_range, linearCombination_apply]

中文:
定理 mem_span_range_iff_exists_finsupp
  条件: {v : α -> M} {x : M}
  证明: by
  simp only [← Finsupp.range_linearCombination, LinearMap.mem_range, linearCombination_apply]

Depends on / 依赖: Finsupp, Finsupp.range_linearCombination, LinearMap, LinearMap.mem_range, linearCombination_apply, mem_range, range_linearCombination
-/
theorem mem_span_range_iff_exists_finsupp {v : α -> M} {x : M} :
    x in span R (range v) ↔ exists c : α ->₀ R, (c.sum fun i a => a • v i) = x := by
  simp only [← Finsupp.range_linearCombination, LinearMap.mem_range, linearCombination_apply]

/--
theorem `span_image_eq_map_linearCombination` / 定理 `span_image_eq_map_linearCombination`

English:
theorem span_image_eq_map_linearCombination
  given: (s : Set α)
  proof: by
  apply span_eq_of_le
  · intro x hx
    rw [Set.mem_image] at hx
    apply Exists.elim hx
    intro i hi
    exact ⟨_, Finsupp.single_mem_supported R 1 hi.1, by simp [hi.2]⟩
  · refine map_le_iff_le_comap.2 fun z hz => ?_
    have : forall i, z i • v i in span R (v '' s) := by
      intro c
    

中文:
定理 span_image_eq_map_linearCombination
  条件: (s : Set α)
  证明: by
  apply span_eq_of_le
  · intro x hx
    rw [Set.mem_image] at hx
    apply Exists.elim hx
    intro i hi
    exact ⟨_, Finsupp.single_mem_supported R 1 hi.1, by simp [hi.2]⟩
  · refine map_le_iff_le_comap.2 fun z hz => ?_
    have : forall i, z i • v i in span R (v '' s) := by
      intro c
    

Depends on / 依赖: Classical, Classical.decPred, Exists, Exists.elim, Finsupp, Finsupp.mem_supported, Finsupp.single_mem_supported, Set.mem_image, Set.mem_image_of_mem, decPred, linearCombination_apply, map_le_iff_le_comap, mem_comap, mem_image, mem_image_of_mem, mem_supported, single_mem_supported, smul_mem, span_eq_of_le, subset_span
-/
theorem span_image_eq_map_linearCombination (s : Set α) :
    span R (v '' s) = Submodule.map (linearCombination R v) (supported R R s) := by
  apply span_eq_of_le
  · intro x hx
    rw [Set.mem_image] at hx
    apply Exists.elim hx
    intro i hi
    exact ⟨_, Finsupp.single_mem_supported R 1 hi.1, by simp [hi.2]⟩
  · refine map_le_iff_le_comap.2 fun z hz => ?_
    have : forall i, z i • v i in span R (v '' s) := by
      intro c
      have := Classical.decPred fun x => x in s
      by_cases h : c in s
      · exact smul_mem _ _ (subset_span (Set.mem_image_of_mem _ h))
      · simp [(Finsupp.mem_supported' R _).1 hz _ h]
    rw [mem_comap]; rw [linearCombination_apply]
    refine sum_mem ?_
    simp [this]

/--
theorem `mem_span_image_iff_linearCombination` / 定理 `mem_span_image_iff_linearCombination`

English:
theorem mem_span_image_iff_linearCombination
  given: {s : Set α} {x : M}
  proof: by
  rw [span_image_eq_map_linearCombination]
  simp

中文:
定理 mem_span_image_iff_linearCombination
  条件: {s : Set α} {x : M}
  证明: by
  rw [span_image_eq_map_linearCombination]
  simp

Depends on / 依赖: span_image_eq_map_linearCombination
-/
theorem mem_span_image_iff_linearCombination {s : Set α} {x : M} :
    x in span R (v '' s) ↔ exists l in supported R R s, linearCombination R v l = x := by
  rw [span_image_eq_map_linearCombination]
  simp

/--
theorem `linearCombination_option` / 定理 `linearCombination_option`

English:
theorem linearCombination_option
  given: (v : Option α -> M) (f : Option α ->₀ R)
  proof: by
  rw [linearCombination_apply]; rw [sum_option_index_smul]; rw [linearCombination_apply]; simp

中文:
定理 linearCombination_option
  条件: (v : Option α -> M) (f : Option α ->₀ R)
  证明: by
  rw [linearCombination_apply]; rw [sum_option_index_smul]; rw [linearCombination_apply]; simp

Depends on / 依赖: linearCombination_apply, sum_option_index_smul
-/
theorem linearCombination_option (v : Option α -> M) (f : Option α ->₀ R) :
    linearCombination R v f =
      f none • v none + linearCombination R (v ∘ Option.some) f.some := by
  rw [linearCombination_apply]; rw [sum_option_index_smul]; rw [linearCombination_apply]; simp

/--
theorem `linearCombination_linearCombination` / 定理 `linearCombination_linearCombination`

English:
theorem linearCombination_linearCombination
  statement: {α β : Type*} (A : α -> M) (B : β -> α ->₀ R)
  proof: by
  classical
  simp only [linearCombination_apply]
  induction f using induction_linear with
  | zero => simp only [sum_zero_index]
  | add f₁ f₂ h₁ h₂ => simp [sum_add_index, h₁, h₂, add_smul]
  | single => simp [sum_single_index, sum_smul_index, smul_sum, mul_smul]

中文:
定理 linearCombination_linearCombination
  结论: {α β : 类型} (A : α -> M) (B : β -> α ->₀ R)
  证明: by
  classical
  simp only [linearCombination_apply]
  induction f using induction_linear with
  | zero => simp only [sum_zero_index]
  | add f₁ f₂ h₁ h₂ => simp [sum_add_index, h₁, h₂, add_smul]
  | single => simp [sum_single_index, sum_smul_index, smul_sum, mul_smul]

Depends on / 依赖: add_smul, classical, induction_linear, linearCombination_apply, mul_smul, single, smul_sum, sum_add_index, sum_single_index, sum_smul_index, sum_zero_index
-/
theorem linearCombination_linearCombination {α β : Type*} (A : α -> M) (B : β -> α ->₀ R)
    (f : β ->₀ R) : linearCombination R A (linearCombination R B f) =
      linearCombination R (fun b => linearCombination R A (B b)) f := by
  classical
  simp only [linearCombination_apply]
  induction f using induction_linear with
  | zero => simp only [sum_zero_index]
  | add f₁ f₂ h₁ h₂ => simp [sum_add_index, h₁, h₂, add_smul]
  | single => simp [sum_single_index, sum_smul_index, smul_sum, mul_smul]

/--
theorem `linearCombination_smul` / 定理 `linearCombination_smul`

English:
theorem linearCombination_smul
  given: [Module R S] [Module S M] [IsScalarTower R S M] {w : α' -> S}
  proof: by
  ext; simp

@[simp]

中文:
定理 linearCombination_smul
  条件: [Module R S] [Module S M] [IsScalarTower R S M] {w : α' -> S}
  证明: by
  ext; simp

@[simp]
-/
theorem linearCombination_smul [Module R S] [Module S M] [IsScalarTower R S M] {w : α' -> S} :
    linearCombination R (fun i : α × α' => w i.2 • v i.1) = (linearCombination S v).restrictScalars R
      ∘ₗ mapRange.linearMap (linearCombination R w) ∘ₗ (curryLinearEquiv R).toLinearMap := by
  ext; simp

@[simp]
/--
theorem `linearCombination_fin_zero` / 定理 `linearCombination_fin_zero`

English:
theorem linearCombination_fin_zero
  given: (f : Fin 0 -> M)
  statement: linearCombination R f = 0
  proof: by
  ext i
  apply finZeroElim i

中文:
定理 linearCombination_fin_zero
  条件: (f : Fin 0 -> M)
  结论: linearCombination R f = 0
  证明: by
  ext i
  apply finZeroElim i

Depends on / 依赖: finZeroElim
-/
theorem linearCombination_fin_zero (f : Fin 0 -> M) : linearCombination R f = 0 := by
  ext i
  apply finZeroElim i

variable (α) (M) (v)

/--
Definition of `linearCombinationOn` / `linearCombinationOn` 的定义

English:
definition linearCombinationOn
  signature: (s : Set α)
  body: LinearMap.codRestrict _ ((linearCombination _ v).comp (Submodule.subtype (supported R R s)))
    fun ⟨l, hl⟩ => (mem_span_image_iff_linearCombination _).2 ⟨l, hl, rfl⟩

中文:
定义 linearCombinationOn
  签名: (s : Set α)
  定义体: LinearMap.codRestrict _ ((linearCombination _ v).comp (Submodule.subtype (supported R R s)))
    fun ⟨l, hl⟩ => (mem_span_image_iff_linearCombination _).2 ⟨l, hl, rfl⟩

Depends on / 依赖: LinearMap, LinearMap.codRestrict, Submodule, Submodule.subtype, codRestrict, linearCombination, mem_span_image_iff_linearCombination, subtype, supported
-/
def linearCombinationOn (s : Set α) : supported R R s ->ₗ[R] span R (v '' s) :=
  LinearMap.codRestrict _ ((linearCombination _ v).comp (Submodule.subtype (supported R R s)))
    fun ⟨l, hl⟩ => (mem_span_image_iff_linearCombination _).2 ⟨l, hl, rfl⟩

variable {α} {M} {v}

/--
theorem `linearCombinationOn_range` / 定理 `linearCombinationOn_range`

English:
theorem linearCombinationOn_range
  given: (s : Set α)
  proof: by
  rw [linearCombinationOn]; rw [LinearMap.range_eq_map]; rw [LinearMap.map_codRestrict]; rw [← LinearMap.range_le_iff_comap]; rw [range_subtype]; rw [Submodule.map_top]; rw [LinearMap.range_comp]; rw [range_subtype]
  exact (span_image_eq_map_linearCombination _ _).le

中文:
定理 linearCombinationOn_range
  条件: (s : Set α)
  证明: by
  rw [linearCombinationOn]; rw [LinearMap.range_eq_map]; rw [LinearMap.map_codRestrict]; rw [← LinearMap.range_le_iff_comap]; rw [range_subtype]; rw [Submodule.map_top]; rw [LinearMap.range_comp]; rw [range_subtype]
  exact (span_image_eq_map_linearCombination _ _).le

Depends on / 依赖: LinearMap, LinearMap.map_codRestrict, LinearMap.range_comp, LinearMap.range_eq_map, LinearMap.range_le_iff_comap, Submodule, Submodule.map_top, linearCombinationOn, map_codRestrict, map_top, range_comp, range_eq_map, range_le_iff_comap, range_subtype, span_image_eq_map_linearCombination
-/
theorem linearCombinationOn_range (s : Set α) :
    LinearMap.range (linearCombinationOn α M R v s) = ⊤ := by
  rw [linearCombinationOn]; rw [LinearMap.range_eq_map]; rw [LinearMap.map_codRestrict]; rw [← LinearMap.range_le_iff_comap]; rw [range_subtype]; rw [Submodule.map_top]; rw [LinearMap.range_comp]; rw [range_subtype]
  exact (span_image_eq_map_linearCombination _ _).le

set_option backward.isDefEq.respectTransparency false in
/--
theorem `linearCombination_restrict` / 定理 `linearCombination_restrict`

English:
theorem linearCombination_restrict
  given: (s : Set α)
  proof: by
  ext; simp [linearCombinationOn]

中文:
定理 linearCombination_restrict
  条件: (s : Set α)
  证明: by
  ext; simp [linearCombinationOn]

Depends on / 依赖: linearCombinationOn
-/
theorem linearCombination_restrict (s : Set α) :
    linearCombination R (s.domRestrict v) = Submodule.subtype _ ∘ₗ
      linearCombinationOn α M R v s ∘ₗ (supportedEquivFinsupp s).symm.toLinearMap := by
  ext; simp [linearCombinationOn]

/--
theorem `linearCombination_comp` / 定理 `linearCombination_comp`

English:
theorem linearCombination_comp
  given: (f : α' -> α)
  proof: by
  ext
  simp [linearCombination_apply]

中文:
定理 linearCombination_comp
  条件: (f : α' -> α)
  证明: by
  ext
  simp [linearCombination_apply]

Depends on / 依赖: linearCombination_apply
-/
theorem linearCombination_comp (f : α' -> α) :
    linearCombination R (v ∘ f) = (linearCombination R v).comp (lmapDomain R R f) := by
  ext
  simp [linearCombination_apply]

/--
theorem `linearCombination_comapDomain` / 定理 `linearCombination_comapDomain`

English:
theorem linearCombination_comapDomain
  statement: (f : α -> α') (l : α' ->₀ R)
  proof: by
  rw [linearCombination_apply]; rfl

中文:
定理 linearCombination_comapDomain
  结论: (f : α -> α') (l : α' ->₀ R)
  证明: by
  rw [linearCombination_apply]; rfl

Depends on / 依赖: linearCombination_apply
-/
theorem linearCombination_comapDomain (f : α -> α') (l : α' ->₀ R)
    (hf : Set.InjOn f (f ⁻¹' ↑l.support)) : linearCombination R v (Finsupp.comapDomain f l hf) =
      (l.support.preimage f hf).sum fun i => l (f i) • v i := by
  rw [linearCombination_apply]; rfl

/--
theorem `linearCombination_onFinset` / 定理 `linearCombination_onFinset`

English:
theorem linearCombination_onFinset
  statement: {s : Finset α} {f : α -> R} (g : α -> M)
  proof: by
  classical
  simp only [linearCombination_apply, Finsupp.sum, Finsupp.onFinset_apply, Finsupp.support_onFinset]
  rw [Finset.sum_filter_of_ne]
  intro x _ h
  contrapose h
  simp [h]

中文:
定理 linearCombination_onFinset
  结论: {s : Finset α} {f : α -> R} (g : α -> M)
  证明: by
  classical
  simp only [linearCombination_apply, Finsupp.sum, Finsupp.onFinset_apply, Finsupp.support_onFinset]
  rw [Finset.sum_filter_of_ne]
  intro x _ h
  contrapose h
  simp [h]

Depends on / 依赖: Finset, Finset.sum_filter_of_ne, Finsupp, Finsupp.onFinset_apply, Finsupp.sum, Finsupp.support_onFinset, classical, contrapose, linearCombination_apply, onFinset_apply, sum_filter_of_ne, support_onFinset
-/
theorem linearCombination_onFinset {s : Finset α} {f : α -> R} (g : α -> M)
    (hf : forall a, f a != 0 -> a in s) :
    linearCombination R g (Finsupp.onFinset s f hf) = Finset.sum s fun x : α => f x • g x := by
  classical
  simp only [linearCombination_apply, Finsupp.sum, Finsupp.onFinset_apply, Finsupp.support_onFinset]
  rw [Finset.sum_filter_of_ne]
  intro x _ h
  contrapose h
  simp [h]

variable [Module S M] [SMulCommClass R S M]

variable (S) in
/--
Definition of `bilinearCombination` / `bilinearCombination` 的定义

English:
definition bilinearCombination
  signature: : (α -> M) ->ₗ[S] (α ->₀ R) ->ₗ[R] M where
  body: linearCombination R v
  map_add' u v := by ext; simp [Pi.add_apply, smul_add]
  map_smul' r v := by ext; simp [smul_comm]

@[simp]

中文:
定义 bilinearCombination
  签名: : (α -> M) ->ₗ[S] (α ->₀ R) ->ₗ[R] M where
  定义体: linearCombination R v
  map_add' u v := by ext; simp [Pi.add_apply, smul_add]
  map_smul' r v := by ext; simp [smul_comm]

@[simp]

Depends on / 依赖: linearCombination
-/
def bilinearCombination : (α -> M) ->ₗ[S] (α ->₀ R) ->ₗ[R] M where
  toFun v := linearCombination R v
  map_add' u v := by ext; simp [Pi.add_apply, smul_add]
  map_smul' r v := by ext; simp [smul_comm]

@[simp]
/--
theorem `bilinearCombination_apply` / 定理 `bilinearCombination_apply`

English:
theorem bilinearCombination_apply
  proof: rfl

中文:
定理 bilinearCombination_apply
  证明: rfl
-/
theorem bilinearCombination_apply :
    bilinearCombination R S v = linearCombination R v :=
  rfl

end LinearCombination

end Finsupp

section Fintype

variable {α M : Type*} (R : Type*) [Fintype α] [Semiring R] [AddCommMonoid M] [Module R M]
variable (S : Type*) [Semiring S] [Module S M] [SMulCommClass R S M]
variable (v : α -> M)

/--
Definition of `Fintype.linearCombination` / `Fintype.linearCombination` 的定义

English:
definition Fintype.linearCombination
  signature: : (α -> R) ->ₗ[R] M where
  body: ∑ i, f i • v i
  map_add' f g := by simp_rw [← Finset.sum_add_distrib, ← add_smul]; rfl
  map_smul' r f := by simp_rw [Finset.smul_sum, smul_smul]; rfl

中文:
定义 Fintype.linearCombination
  签名: : (α -> R) ->ₗ[R] M where
  定义体: ∑ i, f i • v i
  map_add' f g := by simp_rw [← Finset.sum_add_distrib, ← add_smul]; rfl
  map_smul' r f := by simp_rw [Finset.smul_sum, smul_smul]; rfl
-/
protected def Fintype.linearCombination : (α -> R) ->ₗ[R] M where
  toFun f := ∑ i, f i • v i
  map_add' f g := by simp_rw [← Finset.sum_add_distrib, ← add_smul]; rfl
  map_smul' r f := by simp_rw [Finset.smul_sum, smul_smul]; rfl

/--
theorem `Fintype.linearCombination_apply` / 定理 `Fintype.linearCombination_apply`

English:
theorem Fintype.linearCombination_apply
  given: (f)
  statement: Fintype.linearCombination R v f = ∑ i, f i • v i
  proof: rfl

@[simp]

中文:
定理 Fintype.linearCombination_apply
  条件: (f)
  结论: Fintype.linearCombination R v f = ∑ i, f i • v i
  证明: rfl

@[simp]
-/
theorem Fintype.linearCombination_apply (f) : Fintype.linearCombination R v f = ∑ i, f i • v i :=
  rfl

@[simp]
/--
theorem `Fintype.linearCombination_apply_single` / 定理 `Fintype.linearCombination_apply_single`

English:
theorem Fintype.linearCombination_apply_single
  given: [DecidableEq α] (i : α) (r : R)
  proof: by
  simp_rw [Fintype.linearCombination_apply, Pi.single_apply, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq']; rw [if_pos (Finset.mem_univ _)]

中文:
定理 Fintype.linearCombination_apply_single
  条件: [DecidableEq α] (i : α) (r : R)
  证明: by
  simp_rw [Fintype.linearCombination_apply, Pi.single_apply, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq']; rw [if_pos (Finset.mem_univ _)]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sum_ite_eq, Fintype, Fintype.linearCombination_apply, Pi.single_apply, if_pos, ite_smul, linearCombination_apply, mem_univ, simp_rw, single_apply, sum_ite_eq, zero_smul
-/
theorem Fintype.linearCombination_apply_single [DecidableEq α] (i : α) (r : R) :
    Fintype.linearCombination R v (Pi.single i r) = r • v i := by
  simp_rw [Fintype.linearCombination_apply, Pi.single_apply, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq']; rw [if_pos (Finset.mem_univ _)]

/--
theorem `Finsupp.linearCombination_eq_fintype_linearCombination_apply` / 定理 `Finsupp.linearCombination_eq_fintype_linearCombination_apply`

English:
theorem Finsupp.linearCombination_eq_fintype_linearCombination_apply
  given: (x : α -> R)
  proof: by
  apply Finset.sum_subset
  · exact Finset.subset_univ _
  · intro x _ hx
    rw [Finsupp.notMem_support_iff.mp hx]
    exact zero_smul _ _

中文:
定理 Finsupp.linearCombination_eq_fintype_linearCombination_apply
  条件: (x : α -> R)
  证明: by
  apply Finset.sum_subset
  · exact Finset.subset_univ _
  · intro x _ hx
    rw [Finsupp.notMem_support_iff.mp hx]
    exact zero_smul _ _

Depends on / 依赖: Finset, Finset.subset_univ, Finset.sum_subset, Finsupp, Finsupp.notMem_support_iff.mp, notMem_support_iff, subset_univ, sum_subset, zero_smul
-/
theorem Finsupp.linearCombination_eq_fintype_linearCombination_apply (x : α -> R) :
    linearCombination R v ((Finsupp.linearEquivFunOnFinite R R α).symm x) =
      Fintype.linearCombination R v x := by
  apply Finset.sum_subset
  · exact Finset.subset_univ _
  · intro x _ hx
    rw [Finsupp.notMem_support_iff.mp hx]
    exact zero_smul _ _

/--
theorem `Finsupp.linearCombination_eq_fintype_linearCombination` / 定理 `Finsupp.linearCombination_eq_fintype_linearCombination`

English:
theorem Finsupp.linearCombination_eq_fintype_linearCombination
  proof: LinearMap.ext linearCombination_eq_fintype_linearCombination_apply R v

@[simp]

中文:
定理 Finsupp.linearCombination_eq_fintype_linearCombination
  证明: LinearMap.ext linearCombination_eq_fintype_linearCombination_apply R v

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, linearCombination_eq_fintype_linearCombination_apply
-/
theorem Finsupp.linearCombination_eq_fintype_linearCombination :
    (linearCombination R v).comp (Finsupp.linearEquivFunOnFinite R R α).symm.toLinearMap =
      Fintype.linearCombination R v :=
LinearMap.ext linearCombination_eq_fintype_linearCombination_apply R v

@[simp]
/--
theorem `Fintype.range_linearCombination` / 定理 `Fintype.range_linearCombination`

English:
theorem Fintype.range_linearCombination
  proof: by
  rw [← Finsupp.linearCombination_eq_fintype_linearCombination]; rw [LinearMap.range_comp]; rw [LinearEquiv.range]; rw [Submodule.map_top]; rw [Finsupp.range_linearCombination]

中文:
定理 Fintype.range_linearCombination
  证明: by
  rw [← Finsupp.linearCombination_eq_fintype_linearCombination]; rw [LinearMap.range_comp]; rw [LinearEquiv.range]; rw [Submodule.map_top]; rw [Finsupp.range_linearCombination]

Depends on / 依赖: Finsupp, Finsupp.linearCombination_eq_fintype_linearCombination, Finsupp.range_linearCombination, LinearEquiv, LinearEquiv.range, LinearMap, LinearMap.range_comp, Submodule, Submodule.map_top, linearCombination_eq_fintype_linearCombination, map_top, range_comp, range_linearCombination
-/
theorem Fintype.range_linearCombination :
    LinearMap.range (Fintype.linearCombination R v) = Submodule.span R (Set.range v) := by
  rw [← Finsupp.linearCombination_eq_fintype_linearCombination]; rw [LinearMap.range_comp]; rw [LinearEquiv.range]; rw [Submodule.map_top]; rw [Finsupp.range_linearCombination]

/--
theorem `span_range_eq_top_iff_surjective_fintypeLinearCombination` / 定理 `span_range_eq_top_iff_surjective_fintypeLinearCombination`

English:
theorem span_range_eq_top_iff_surjective_fintypeLinearCombination
  proof: by
  rw [← LinearMap.range_eq_top]; rw [Fintype.range_linearCombination]

中文:
定理 span_range_eq_top_iff_surjective_fintypeLinearCombination
  证明: by
  rw [← LinearMap.range_eq_top]; rw [Fintype.range_linearCombination]

Depends on / 依赖: Fintype, Fintype.range_linearCombination, LinearMap, LinearMap.range_eq_top, range_eq_top, range_linearCombination
-/
theorem span_range_eq_top_iff_surjective_fintypeLinearCombination :
    Submodule.span R (Set.range v) = ⊤ ↔
      Function.Surjective (Fintype.linearCombination R v) := by
  rw [← LinearMap.range_eq_top]; rw [Fintype.range_linearCombination]

/--
Definition of `Fintype.bilinearCombination` / `Fintype.bilinearCombination` 的定义

English:
definition Fintype.bilinearCombination
  signature: : (α -> M) ->ₗ[S] (α -> R) ->ₗ[R] M where
  body: Fintype.linearCombination R v
  map_add' u v := by ext; simp [Fintype.linearCombination,
    Finset.sum_add_distrib, Pi.add_apply, smul_add]
  map_smul' r v := by ext; simp [Fintype.linearCombination, Finset.smul_sum, smul_comm]

中文:
定义 Fintype.bilinearCombination
  签名: : (α -> M) ->ₗ[S] (α -> R) ->ₗ[R] M where
  定义体: Fintype.linearCombination R v
  map_add' u v := by ext; simp [Fintype.linearCombination,
    Finset.sum_add_distrib, Pi.add_apply, smul_add]
  map_smul' r v := by ext; simp [Fintype.linearCombination, Finset.smul_sum, smul_comm]
-/
protected def Fintype.bilinearCombination : (α -> M) ->ₗ[S] (α -> R) ->ₗ[R] M where
  toFun v := Fintype.linearCombination R v
  map_add' u v := by ext; simp [Fintype.linearCombination,
    Finset.sum_add_distrib, Pi.add_apply, smul_add]
  map_smul' r v := by ext; simp [Fintype.linearCombination, Finset.smul_sum, smul_comm]

variable {S}

@[simp]
/--
theorem `Fintype.bilinearCombination_apply` / 定理 `Fintype.bilinearCombination_apply`

English:
theorem Fintype.bilinearCombination_apply
  proof: rfl

中文:
定理 Fintype.bilinearCombination_apply
  证明: rfl
-/
theorem Fintype.bilinearCombination_apply :
    Fintype.bilinearCombination R S v = Fintype.linearCombination R v :=
  rfl

/--
theorem `Fintype.bilinearCombination_apply_single` / 定理 `Fintype.bilinearCombination_apply_single`

English:
theorem Fintype.bilinearCombination_apply_single
  given: [DecidableEq α] (i : α) (r : R)
  proof: by
  simp [Fintype.bilinearCombination]

中文:
定理 Fintype.bilinearCombination_apply_single
  条件: [DecidableEq α] (i : α) (r : R)
  证明: by
  simp [Fintype.bilinearCombination]

Depends on / 依赖: Fintype, Fintype.bilinearCombination, bilinearCombination
-/
theorem Fintype.bilinearCombination_apply_single [DecidableEq α] (i : α) (r : R) :
    Fintype.bilinearCombination R S v (Pi.single i r) = r • v i := by
  simp [Fintype.bilinearCombination]

section SpanRange

variable {v} {x : M}

/--
theorem `Submodule.mem_span_range_iff_exists_fun` / 定理 `Submodule.mem_span_range_iff_exists_fun`

English:
theorem Submodule.mem_span_range_iff_exists_fun
  proof: by
  rw [Finsupp.equivFunOnFinite.surjective.exists]
  simp only [Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.equivFunOnFinite_apply]
exact exists_congr fun c => Eq.congr_left Finsupp.sum_fintype _ _ fun i => zero_smul _ _

中文:
定理 Submodule.mem_span_range_iff_exists_fun
  证明: by
  rw [Finsupp.equivFunOnFinite.surjective.exists]
  simp only [Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.equivFunOnFinite_apply]
exact exists_congr fun c => Eq.congr_left Finsupp.sum_fintype _ _ fun i => zero_smul _ _

Depends on / 依赖: Eq.congr_left, Finsupp, Finsupp.equivFunOnFinite.surjective.exists, Finsupp.equivFunOnFinite_apply, Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.sum_fintype, congr_left, equivFunOnFinite, equivFunOnFinite_apply, exists_congr, mem_span_range_iff_exists_finsupp, sum_fintype, surjective, zero_smul
-/
theorem Submodule.mem_span_range_iff_exists_fun :
    x in span R (range v) ↔ exists c : α -> R, ∑ i, c i • v i = x := by
  rw [Finsupp.equivFunOnFinite.surjective.exists]
  simp only [Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.equivFunOnFinite_apply]
exact exists_congr fun c => Eq.congr_left Finsupp.sum_fintype _ _ fun i => zero_smul _ _

/--
theorem `Submodule.top_le_span_range_iff_forall_exists_fun` / 定理 `Submodule.top_le_span_range_iff_forall_exists_fun`

English:
theorem Submodule.top_le_span_range_iff_forall_exists_fun
  proof: by
  simp_rw [← mem_span_range_iff_exists_fun]
  exact ⟨fun h x => h trivial, fun h x _ => h x⟩

omit [Fintype α]

中文:
定理 Submodule.top_le_span_range_iff_forall_exists_fun
  证明: by
  simp_rw [← mem_span_range_iff_exists_fun]
  exact ⟨fun h x => h trivial, fun h x _ => h x⟩

omit [Fintype α]

Depends on / 依赖: mem_span_range_iff_exists_fun, simp_rw
-/
theorem Submodule.top_le_span_range_iff_forall_exists_fun :
    ⊤ <= span R (range v) ↔ forall x, exists c : α -> R, ∑ i, c i • v i = x := by
  simp_rw [← mem_span_range_iff_exists_fun]
  exact ⟨fun h x => h trivial, fun h x _ => h x⟩

omit [Fintype α]

/--
theorem `Submodule.mem_span_image_iff_exists_fun` / 定理 `Submodule.mem_span_image_iff_exists_fun`

English:
theorem Submodule.mem_span_image_iff_exists_fun
  given: {s : Set α}
  proof: by
  refine ⟨fun h => ?_, fun ⟨t, ht, c, hx⟩ => ?_⟩
  · obtain ⟨l, hl, hx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).mp h
    refine ⟨l.support, hl, l ∘ (↑), ?_⟩
    rw [← hx]
    exact l.support.sum_coe_sort fun a => l a • v a
  · rw [← hx]
exact sum_smul_mem (span R (v '' s)) c fun a _ =

中文:
定理 Submodule.mem_span_image_iff_exists_fun
  条件: {s : Set α}
  证明: by
  refine ⟨fun h => ?_, fun ⟨t, ht, c, hx⟩ => ?_⟩
  · obtain ⟨l, hl, hx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).mp h
    refine ⟨l.support, hl, l ∘ (↑), ?_⟩
    rw [← hx]
    exact l.support.sum_coe_sort fun a => l a • v a
  · rw [← hx]
exact sum_smul_mem (span R (v '' s)) c fun a _ =

Depends on / 依赖: Finsupp, Finsupp.mem_span_image_iff_linearCombination, l.support, l.support.sum_coe_sort, mem_span_image_iff_linearCombination, subset_span, sum_coe_sort, sum_smul_mem, support
-/
theorem Submodule.mem_span_image_iff_exists_fun {s : Set α} :
    x in span R (v '' s) ↔ exists t : Finset α, ↑t subseteq s ∧ exists c : t -> R, ∑ i, c i • v i = x := by
  refine ⟨fun h => ?_, fun ⟨t, ht, c, hx⟩ => ?_⟩
  · obtain ⟨l, hl, hx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).mp h
    refine ⟨l.support, hl, l ∘ (↑), ?_⟩
    rw [← hx]
    exact l.support.sum_coe_sort fun a => l a • v a
  · rw [← hx]
exact sum_smul_mem (span R (v '' s)) c fun a _ => subset_span by aesop

/--
theorem `Submodule.mem_span_image_finset_iff_exists_fun` / 定理 `Submodule.mem_span_image_finset_iff_exists_fun`

English:
theorem Submodule.mem_span_image_finset_iff_exists_fun
  given: {s : Finset α}
  proof: by
  rw [← mem_span_range_iff_exists_fun]; rw [image_eq_range]
  rfl

中文:
定理 Submodule.mem_span_image_finset_iff_exists_fun
  条件: {s : Finset α}
  证明: by
  rw [← mem_span_range_iff_exists_fun]; rw [image_eq_range]
  rfl

Depends on / 依赖: image_eq_range, mem_span_range_iff_exists_fun
-/
theorem Submodule.mem_span_image_finset_iff_exists_fun {s : Finset α} :
    x in span R (v '' s) ↔ exists c : s -> R, ∑ i, c i • v i = x := by
  rw [← mem_span_range_iff_exists_fun]; rw [image_eq_range]
  rfl

/--
theorem `Submodule.mem_span_image_finset_iff_exists_fun'` / 定理 `Submodule.mem_span_image_finset_iff_exists_fun'`

English:
theorem Submodule.mem_span_image_finset_iff_exists_fun'
  given: {s : Finset α}
  proof: by
  classical
  rw [Submodule.mem_span_image_finset_iff_exists_fun]
  refine ⟨fun ⟨c, hc⟩ => ?_, fun ⟨c, hc⟩ => ?_⟩
  · refine ⟨fun i => if h : i in s then c ⟨i, h⟩ else 0, ?_⟩
    rw [← hc]; rw [← Finset.sum_coe_sort (s := s)]
    simp
  · refine ⟨fun i => c i, ?_⟩
    rw [← hc]; rw [← Finset.sum_

中文:
定理 Submodule.mem_span_image_finset_iff_exists_fun'
  条件: {s : Finset α}
  证明: by
  classical
  rw [Submodule.mem_span_image_finset_iff_exists_fun]
  refine ⟨fun ⟨c, hc⟩ => ?_, fun ⟨c, hc⟩ => ?_⟩
  · refine ⟨fun i => if h : i in s then c ⟨i, h⟩ else 0, ?_⟩
    rw [← hc]; rw [← Finset.sum_coe_sort (s := s)]
    simp
  · refine ⟨fun i => c i, ?_⟩
    rw [← hc]; rw [← Finset.sum_

Depends on / 依赖: Finset, Finset.sum_coe_sort, Submodule, Submodule.mem_span_image_finset_iff_exists_fun, classical, mem_span_image_finset_iff_exists_fun, sum_coe_sort
-/
theorem Submodule.mem_span_image_finset_iff_exists_fun' {s : Finset α} :
    x in span R (v '' s) ↔ exists c : α -> R, ∑ i in s, c i • v i = x := by
  classical
  rw [Submodule.mem_span_image_finset_iff_exists_fun]
  refine ⟨fun ⟨c, hc⟩ => ?_, fun ⟨c, hc⟩ => ?_⟩
  · refine ⟨fun i => if h : i in s then c ⟨i, h⟩ else 0, ?_⟩
    rw [← hc]; rw [← Finset.sum_coe_sort (s := s)]
    simp
  · refine ⟨fun i => c i, ?_⟩
    rw [← hc]; rw [← Finset.sum_coe_sort (s := s)]

/--
theorem `Fintype.mem_span_image_iff_exists_fun` / 定理 `Fintype.mem_span_image_iff_exists_fun`

English:
theorem Fintype.mem_span_image_iff_exists_fun
  given: {s : Set α} [Fintype s]
  proof: by
  rw [← mem_span_range_iff_exists_fun]; rw [image_eq_range]

中文:
定理 Fintype.mem_span_image_iff_exists_fun
  条件: {s : Set α} [Fintype s]
  证明: by
  rw [← mem_span_range_iff_exists_fun]; rw [image_eq_range]

Depends on / 依赖: image_eq_range, mem_span_range_iff_exists_fun
-/
theorem Fintype.mem_span_image_iff_exists_fun {s : Set α} [Fintype s] :
    x in span R (v '' s) ↔ exists c : s -> R, ∑ i, c i • v i = x := by
  rw [← mem_span_range_iff_exists_fun]; rw [image_eq_range]

end SpanRange

end Fintype

variable {R : Type*} {M : Type*} {N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Finsupp

section

variable (R)

/-- Pick some representation of `x : span R w` as a linear combination in `w`,
`((Finsupp.mem_span_iff_linearCombination _ _ _).mp x.2).choose`
-/
irreducible_def Span.repr (w : Set M) (x : span R w) : w ->₀ R :=
  ((Finsupp.mem_span_iff_linearCombination _ _ _).mp x.2).choose

@[simp]
/--
theorem `Span.finsupp_linearCombination_repr` / 定理 `Span.finsupp_linearCombination_repr`

English:
theorem Span.finsupp_linearCombination_repr
  given: {w : Set M} (x : span R w)
  proof: by
  rw [Span.repr_def]
  exact ((Finsupp.mem_span_iff_linearCombination _ _ _).mp x.2).choose_spec

中文:
定理 Span.finsupp_linearCombination_repr
  条件: {w : Set M} (x : span R w)
  证明: by
  rw [Span.repr_def]
  exact ((Finsupp.mem_span_iff_linearCombination _ _ _).mp x.2).choose_spec

Depends on / 依赖: DiscreteMeasurableSpace, DiscreteMeasurableSpace.toMeasurableMul, Finsupp, Finsupp.mem_span_iff_linearCombination, Span.repr_def, choose_spec, mem_span_iff_linearCombination, repr_def, toMeasurableMul
-/
theorem Span.finsupp_linearCombination_repr {w : Set M} (x : span R w) :
    Finsupp.linearCombination R ((↑) : w -> M) (Span.repr R w x) = x := by
  rw [Span.repr_def]
  exact ((Finsupp.mem_span_iff_linearCombination _ _ _).mp x.2).choose_spec

end

/--
theorem `LinearMap.map_finsupp_linearCombination` / 定理 `LinearMap.map_finsupp_linearCombination`

English:
theorem LinearMap.map_finsupp_linearCombination
  statement: (f : M ->ₗ[R] N) {ι : Type*} {g : ι -> M}
  proof: apply_linearCombination _ _ _ _

中文:
定理 LinearMap.map_finsupp_linearCombination
  结论: (f : M ->ₗ[R] N) {ι : 类型} {g : ι -> M}
  证明: apply_linearCombination _ _ _ _

Depends on / 依赖: DiscreteMeasurableSpace, DiscreteMeasurableSpace.toMeasurableMul, apply_linearCombination
-/
theorem LinearMap.map_finsupp_linearCombination (f : M ->ₗ[R] N) {ι : Type*} {g : ι -> M}
    (l : ι ->₀ R) : f (linearCombination R g l) = linearCombination R (f ∘ g) l :=
  apply_linearCombination _ _ _ _

/--
lemma `Submodule.mem_span_iff_exists_finset_subset` / 引理 `Submodule.mem_span_iff_exists_finset_subset`

English:
lemma Submodule.mem_span_iff_exists_finset_subset
  given: {s : Set M} {x : M}
  proof: by
    rw [← s.image_id]; rw [mem_span_image_iff_linearCombination]
    rintro ⟨l, hl, rfl⟩
    exact ⟨l, l.support, by simpa [linearCombination, Finsupp.sum] using! hl⟩
  mpr := by
rintro ⟨n, t, hts, -, rfl⟩; exact sum_mem fun x hx => smul_mem _ _ subset_span hts hx

中文:
引理 Submodule.mem_span_iff_exists_finset_subset
  条件: {s : Set M} {x : M}
  证明: by
    rw [← s.image_id]; rw [mem_span_image_iff_linearCombination]
    rintro ⟨l, hl, rfl⟩
    exact ⟨l, l.support, by simpa [linearCombination, Finsupp.sum] using! hl⟩
  mpr := by
rintro ⟨n, t, hts, -, rfl⟩; exact sum_mem fun x hx => smul_mem _ _ subset_span hts hx

Depends on / 依赖: DiscreteMeasurableSpace, DiscreteMeasurableSpace.toMeasurableInv, Finsupp, Finsupp.sum, image_id, l.support, linearCombination, mem_span_image_iff_linearCombination, s.image_id, smul_mem, subset_span, sum_mem, support, toMeasurableInv
-/
lemma Submodule.mem_span_iff_exists_finset_subset {s : Set M} {x : M} :
    x in span R s ↔
      exists (f : M -> R) (t : Finset M), ↑t subseteq s ∧ f.support subseteq t ∧ ∑ a in t, f a • a = x where
  mp := by
    rw [← s.image_id]; rw [mem_span_image_iff_linearCombination]
    rintro ⟨l, hl, rfl⟩
    exact ⟨l, l.support, by simpa [linearCombination, Finsupp.sum] using! hl⟩
  mpr := by
rintro ⟨n, t, hts, -, rfl⟩; exact sum_mem fun x hx => smul_mem _ _ subset_span hts hx

/--
lemma `Submodule.mem_span_finset` / 引理 `Submodule.mem_span_finset`

English:
lemma Submodule.mem_span_finset
  given: {s : Finset M} {x : M}
  proof: by
    rw [mem_span_iff_exists_finset_subset]
    rintro ⟨f, t, hts, hf, rfl⟩
refine ⟨f, hf.trans hts, .symm Finset.sum_subset hts ?_⟩
    simp +contextual [Function.support_subset_iff'.1 hf]
mpr := by rintro ⟨f, -, rfl⟩; exact sum_mem fun x hx => smul_mem _ _ subset_span hx

中文:
引理 Submodule.mem_span_finset
  条件: {s : Finset M} {x : M}
  证明: by
    rw [mem_span_iff_exists_finset_subset]
    rintro ⟨f, t, hts, hf, rfl⟩
refine ⟨f, hf.trans hts, .symm Finset.sum_subset hts ?_⟩
    simp +contextual [Function.support_subset_iff'.1 hf]
mpr := by rintro ⟨f, -, rfl⟩; exact sum_mem fun x hx => smul_mem _ _ subset_span hx

Depends on / 依赖: DiscreteMeasurableSpace, DiscreteMeasurableSpace.toMeasurableDiv, Finset, Finset.sum_subset, Function, Function.support_subset_iff, contextual, hf.trans, mem_span_iff_exists_finset_subset, smul_mem, subset_span, sum_mem, sum_subset, support_subset_iff, toMeasurableDiv
-/
lemma Submodule.mem_span_finset {s : Finset M} {x : M} :
    x in span R s ↔ exists f : M -> R, f.support subseteq s ∧ ∑ a in s, f a • a = x where
  mp := by
    rw [mem_span_iff_exists_finset_subset]
    rintro ⟨f, t, hts, hf, rfl⟩
refine ⟨f, hf.trans hts, .symm Finset.sum_subset hts ?_⟩
    simp +contextual [Function.support_subset_iff'.1 hf]
mpr := by rintro ⟨f, -, rfl⟩; exact sum_mem fun x hx => smul_mem _ _ subset_span hx

/--
lemma `Submodule.mem_span_iff_of_fintype` / 引理 `Submodule.mem_span_iff_of_fintype`

English:
lemma Submodule.mem_span_iff_of_fintype
  given: {s : Set M} [Fintype s] {x : M}
  proof: by
  conv_lhs => rw [← Subtype.range_val (s := s)]
  exact mem_span_range_iff_exists_fun _

中文:
引理 Submodule.mem_span_iff_of_fintype
  条件: {s : Set M} [Fintype s] {x : M}
  证明: by
  conv_lhs => rw [← Subtype.range_val (s := s)]
  exact mem_span_range_iff_exists_fun _

Depends on / 依赖: DiscreteMeasurableSpace, DiscreteMeasurableSpace.toMeasurableDiv, Subtype, Subtype.range_val, conv_lhs, mem_span_range_iff_exists_fun, range_val
-/
lemma Submodule.mem_span_iff_of_fintype {s : Set M} [Fintype s] {x : M} :
    x in span R s ↔ exists f : s -> R, ∑ a : s, f a • a.1 = x := by
  conv_lhs => rw [← Subtype.range_val (s := s)]
  exact mem_span_range_iff_exists_fun _

/--
lemma `Submodule.mem_span_finset'` / 引理 `Submodule.mem_span_finset'`

English:
lemma Submodule.mem_span_finset'
  given: {s : Finset M} {x : M}
  proof: mem_span_iff_of_fintype

中文:
引理 Submodule.mem_span_finset'
  条件: {s : Finset M} {x : M}
  证明: mem_span_iff_of_fintype

Depends on / 依赖: mem_span_iff_of_fintype
-/
lemma Submodule.mem_span_finset' {s : Finset M} {x : M} :
    x in span R s ↔ exists f : s -> R, ∑ a : s, f a • a.1 = x :=
  mem_span_iff_of_fintype

/--
theorem `Submodule.mem_span_set` / 定理 `Submodule.mem_span_set`

English:
theorem Submodule.mem_span_set
  given: {m : M} {s : Set M}
  proof: by
  conv_lhs => rw [← Set.image_id s]
  exact Finsupp.mem_span_image_iff_linearCombination R (v := _root_.id (α := M))

中文:
定理 Submodule.mem_span_set
  条件: {m : M} {s : Set M}
  证明: by
  conv_lhs => rw [← Set.image_id s]
  exact Finsupp.mem_span_image_iff_linearCombination R (v := _root_.id (α := M))

Depends on / 依赖: Finsupp, Finsupp.mem_span_image_iff_linearCombination, Set.image_id, _root_, _root_.id, conv_lhs, image_id, mem_span_image_iff_linearCombination
-/
theorem Submodule.mem_span_set {m : M} {s : Set M} :
    m in Submodule.span R s ↔
      exists c : M ->₀ R, (c.support : Set M) subseteq s ∧ (c.sum fun mi r => r • mi) = m := by
  conv_lhs => rw [← Set.image_id s]
  exact Finsupp.mem_span_image_iff_linearCombination R (v := _root_.id (α := M))

/--
lemma `Submodule.mem_span_set'` / 引理 `Submodule.mem_span_set'`

English:
lemma Submodule.mem_span_set'
  given: {m : M} {s : Set M}
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · rcases mem_span_set.1 h with ⟨c, cs, rfl⟩
    have A : c.support ≃ Fin c.support.card := Finset.equivFin _
    refine ⟨_, fun i => c (A.symm i), fun i => ⟨A.symm i, cs (A.symm i).2⟩, ?_⟩
    rw [Finsupp.sum]; rw [← Finset.sum_coe_sort c.support]
    exact Fintype.su

中文:
引理 Submodule.mem_span_set'
  条件: {m : M} {s : Set M}
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · rcases mem_span_set.1 h with ⟨c, cs, rfl⟩
    have A : c.support ≃ Fin c.support.card := Finset.equivFin _
    refine ⟨_, fun i => c (A.symm i), fun i => ⟨A.symm i, cs (A.symm i).2⟩, ?_⟩
    rw [Finsupp.sum]; rw [← Finset.sum_coe_sort c.support]
    exact Fintype.su

Depends on / 依赖: A.symm, Finset, Finset.equivFin, Finset.sum_coe_sort, Finsupp, Finsupp.sum, Fintype, Fintype.sum_equiv, Submodule, Submodule.smul_mem, Submodule.subset_span, Submodule.sum_mem, c.support, c.support.card, equivFin, mem_span_set, smul_mem, subset_span, sum_coe_sort, sum_equiv
-/
lemma Submodule.mem_span_set' {m : M} {s : Set M} :
    m in Submodule.span R s ↔ exists (n : Nat) (f : Fin n -> R) (g : Fin n -> s),
      ∑ i, f i • (g i : M) = m := by
  refine ⟨fun h => ?_, ?_⟩
  · rcases mem_span_set.1 h with ⟨c, cs, rfl⟩
    have A : c.support ≃ Fin c.support.card := Finset.equivFin _
    refine ⟨_, fun i => c (A.symm i), fun i => ⟨A.symm i, cs (A.symm i).2⟩, ?_⟩
    rw [Finsupp.sum]; rw [← Finset.sum_coe_sort c.support]
    exact Fintype.sum_equiv A.symm _ (fun j => c j • (j : M)) (fun i => rfl)
  · rintro ⟨n, f, g, rfl⟩
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (g i).2))

/--
lemma `Submodule.span_eq_iUnion_nat` / 引理 `Submodule.span_eq_iUnion_nat`

English:
lemma Submodule.span_eq_iUnion_nat
  given: (s : Set M)
  proof: by
  ext m
  simp only [SetLike.mem_coe, mem_iUnion, mem_image, mem_ofPred_eq, mem_span_set']
  refine exists_congr (fun n => ⟨?_, ?_⟩)
  · rintro ⟨f, g, rfl⟩
    exact ⟨fun i => (f i, g i), fun i => (g i).2, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨fun i => (f i).1, fun i => ⟨(f i).2, (hf i)⟩, rfl⟩

中文:
引理 Submodule.span_eq_iUnion_nat
  条件: (s : Set M)
  证明: by
  ext m
  simp only [SetLike.mem_coe, mem_iUnion, mem_image, mem_ofPred_eq, mem_span_set']
  refine exists_congr (fun n => ⟨?_, ?_⟩)
  · rintro ⟨f, g, rfl⟩
    exact ⟨fun i => (f i, g i), fun i => (g i).2, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨fun i => (f i).1, fun i => ⟨(f i).2, (hf i)⟩, rfl⟩

Depends on / 依赖: SetLike, SetLike.mem_coe, exists_congr, mem_coe, mem_iUnion, mem_image, mem_ofPred_eq, mem_span_set
-/
lemma Submodule.span_eq_iUnion_nat (s : Set M) :
    (Submodule.span R s : Set M) = ⋃ (n : Nat),
      (fun (f : Fin n -> (R × M)) => ∑ i, (f i).1 • (f i).2) '' ({f | forall i, (f i).2 in s}) := by
  ext m
  simp only [SetLike.mem_coe, mem_iUnion, mem_image, mem_ofPred_eq, mem_span_set']
  refine exists_congr (fun n => ⟨?_, ?_⟩)
  · rintro ⟨f, g, rfl⟩
    exact ⟨fun i => (f i, g i), fun i => (g i).2, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨fun i => (f i).1, fun i => ⟨(f i).2, (hf i)⟩, rfl⟩

section Ring

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M] (i : ι) (c : ι -> R) (h₀ : c i = 0)

/--
Definition of `Finsupp.addSingleEquiv` / `Finsupp.addSingleEquiv` 的定义

English:
definition Finsupp.addSingleEquiv
  signature: : (ι ->₀ R) ≃ₗ[R] (ι ->₀ R)
  body: by
  refine .ofLinearMap (linearCombination _ fun j => single j 1 + single i (c j))
    (linearCombination _ fun j => single j 1 - single i (c j)) ?_ ?_ <;>
  ext j k <;> obtain rfl | hk := eq_or_ne i k
  · simp [h₀]
  · simp [hk]
  · simp [h₀]
  · simp [hk]

中文:
定义 Finsupp.addSingleEquiv
  签名: : (ι ->₀ R) ≃ₗ[R] (ι ->₀ R)
  定义体: by
  refine .ofLinearMap (linearCombination _ fun j => single j 1 + single i (c j))
    (linearCombination _ fun j => single j 1 - single i (c j)) ?_ ?_ <;>
  ext j k <;> obtain rfl | hk := eq_or_ne i k
  · simp [h₀]
  · simp [hk]
  · simp [h₀]
  · simp [hk]

Depends on / 依赖: eq_or_ne, linearCombination, ofLinearMap, single
-/
def Finsupp.addSingleEquiv : (ι ->₀ R) ≃ₗ[R] (ι ->₀ R) := by
  refine .ofLinearMap (linearCombination _ fun j => single j 1 + single i (c j))
    (linearCombination _ fun j => single j 1 - single i (c j)) ?_ ?_ <;>
  ext j k <;> obtain rfl | hk := eq_or_ne i k
  · simp [h₀]
  · simp [hk]
  · simp [h₀]
  · simp [hk]

/--
theorem `Finsupp.linearCombination_comp_addSingleEquiv` / 定理 `Finsupp.linearCombination_comp_addSingleEquiv`

English:
theorem Finsupp.linearCombination_comp_addSingleEquiv
  given: (v : ι -> M)
  proof: by
  ext; simp [addSingleEquiv]

中文:
定理 Finsupp.linearCombination_comp_addSingleEquiv
  条件: (v : ι -> M)
  证明: by
  ext; simp [addSingleEquiv]

Depends on / 依赖: addSingleEquiv
-/
theorem Finsupp.linearCombination_comp_addSingleEquiv (v : ι -> M) :
    linearCombination R v ∘ₗ addSingleEquiv i c h₀ = linearCombination R (v + (c · • v i)) := by
  ext; simp [addSingleEquiv]

end Ring
