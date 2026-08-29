/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.LinearAlgebra.Countable
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Localization.Module

/-!
# ℤ-lattices

Let `E` be a finite-dimensional vector space over a `NormedLinearOrderedField` `K` with a solid
norm that is also a `FloorRing`, e.g. `ℝ`. A (full) `ℤ`-lattice `L` of `E` is a discrete
subgroup of `E` such that `L` spans `E` over `K`.

A `ℤ`-lattice `L` can be defined in two ways:
* For `b` a basis of `E`, then `L = Submodule.span ℤ (Set.range b)` is a ℤ-lattice of `E`
* As a `ℤ-submodule` of `E` with the additional properties:
  * `DiscreteTopology L`, that is `L` is discrete
  * `Submodule.span ℝ (L : Set E) = ⊤`, that is `L` spans `E` over `K`.

Results about the first point of view are in the `ZSpan` namespace and results about the second
point of view are in the `ZLattice` namespace.

## Main results and definitions

* `ZSpan.isAddFundamentalDomain`: for a ℤ-lattice `Submodule.span ℤ (Set.range b)`, proves that
  the set defined by `ZSpan.fundamentalDomain` is a fundamental domain.
* `ZLattice.module_free`: a `ℤ`-submodule of `E` that is discrete and spans `E` over `K` is a free
  `ℤ`-module
* `ZLattice.rank`: a `ℤ`-submodule of `E` that is discrete and spans `E` over `K` is free
  of `ℤ`-rank equal to the `K`-rank of `E`
* `ZLattice.comap`: for `e : E → F` a linear map and `L : Submodule ℤ E`, define the pullback of
  `L` by `e`. If `L` is a `IsZLattice` and `e` is a continuous linear equiv, then it is also a
  `IsZLattice`, see `instIsZLatticeComap`.

## Note

There is also `Submodule.IsLattice` which has slightly different applications. There no
topology is needed and the discrete condition is replaced by finitely generated.

## Implementation Notes

A `ZLattice` could be defined either as a `AddSubgroup E` or a `Submodule ℤ E`. However, the module
aspect appears to be the more useful one (especially in computations involving basis) and is also
consistent with the `ZSpan` construction of `ℤ`-lattices.

-/

@[expose] public section


noncomputable section

namespace ZSpan

open MeasureTheory MeasurableSet Module Submodule Bornology

variable {E ι : Type*}

section NormedLatticeField

variable {K : Type*} [NormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable (b : Basis ι K E)

/--
theorem `span_top` / 定理 `span_top`

English:
theorem span_top
  statement: span K (span Int (Set.range b) : Set E) = ⊤
  proof: by simp [span_span_of_tower]

中文:
定理 span_top
  结论: span K (span 整数 (Set.range b) : Set E) = ⊤
  证明: by simp [span_span_of_tower]

Depends on / 依赖: span_span_of_tower
-/
theorem span_top : span K (span Int (Set.range b) : Set E) = ⊤ := by simp [span_span_of_tower]

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: {F : Type*} [AddCommGroup F] [Module K F] (f : E ≃ₗ[K] F)
  proof: by
  simp_rw [Submodule.map_span, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
    Basis.coe_map, Set.range_comp]

中文:
定理 map
  条件: {F : 类型} [AddCommGroup F] [Module K F] (f : E ≃ₗ[K] F)
  证明: by
  simp_rw [Submodule.map_span, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
    Basis.coe_map, Set.range_comp]

Depends on / 依赖: Basis.coe_map, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply, Set.range_comp, Submodule, Submodule.map_span, coe_coe, coe_map, map_span, range_comp, restrictScalars_apply, simp_rw
-/
theorem map {F : Type*} [AddCommGroup F] [Module K F] (f : E ≃ₗ[K] F) :
    Submodule.map (f.restrictScalars Int : E ->ₗ[Int] F) (span Int (Set.range b)) =
      span Int (Set.range (b.map f)) := by
  simp_rw [Submodule.map_span, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
    Basis.coe_map, Set.range_comp]

open scoped Pointwise in
/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: {c : K} (hc : c != 0)
  proof: by
  rw [smul_span]; rw [Set.smul_set_range]
  congr!
  rw [Basis.isUnitSMul_apply]

中文:
定理 smul
  条件: {c : K} (hc : c != 0)
  证明: by
  rw [smul_span]; rw [Set.smul_set_range]
  congr!
  rw [Basis.isUnitSMul_apply]

Depends on / 依赖: Basis.isUnitSMul_apply, Set.smul_set_range, isUnitSMul_apply, smul_set_range, smul_span
-/
theorem smul {c : K} (hc : c != 0) :
    c • span Int (Set.range b) = span Int (Set.range (b.isUnitSMul (fun _ => hc.isUnit))) := by
  rw [smul_span]; rw [Set.smul_set_range]
  congr!
  rw [Basis.isUnitSMul_apply]

variable [LinearOrder K]

/--
Definition of `fundamentalDomain` / `fundamentalDomain` 的定义

English:
definition fundamentalDomain
  signature: : Set E
  body: {m | forall i, b.repr m i in Set.Ico (0 : K) 1}

@[simp]

中文:
定义 fundamentalDomain
  签名: : Set E
  定义体: {m | forall i, b.repr m i in Set.Ico (0 : K) 1}

@[simp]

Depends on / 依赖: Set.Ico, b.repr
-/
def fundamentalDomain : Set E := {m | forall i, b.repr m i in Set.Ico (0 : K) 1}

@[simp]
/--
theorem `mem_fundamentalDomain` / 定理 `mem_fundamentalDomain`

English:
theorem mem_fundamentalDomain
  given: {m : E}
  proof: Iff.rfl

中文:
定理 mem_fundamentalDomain
  条件: {m : E}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_fundamentalDomain {m : E} :
    m in fundamentalDomain b ↔ forall i, b.repr m i in Set.Ico (0 : K) 1 := Iff.rfl

/--
theorem `map_fundamentalDomain` / 定理 `map_fundamentalDomain`

English:
theorem map_fundamentalDomain
  given: {F : Type*} [NormedAddCommGroup F] [NormedSpace K F] (f : E ≃ₗ[K] F)
  proof: by
  ext x
  rw [mem_fundamentalDomain]; rw [Basis.map_repr]; rw [LinearEquiv.trans_apply]; rw [← mem_fundamentalDomain]; rw [show f.symm x = f.toEquiv.symm x by rfl]; rw [← Set.mem_image_equiv]
  rfl

@[simp]

中文:
定理 map_fundamentalDomain
  条件: {F : 类型} [NormedAddCommGroup F] [NormedSpace K F] (f : E ≃ₗ[K] F)
  证明: by
  ext x
  rw [mem_fundamentalDomain]; rw [Basis.map_repr]; rw [LinearEquiv.trans_apply]; rw [← mem_fundamentalDomain]; rw [show f.symm x = f.toEquiv.symm x by rfl]; rw [← Set.mem_image_equiv]
  rfl

@[simp]

Depends on / 依赖: Basis.map_repr, LinearEquiv, LinearEquiv.trans_apply, Set.mem_image_equiv, f.symm, f.toEquiv.symm, map_repr, mem_fundamentalDomain, mem_image_equiv, toEquiv, trans_apply
-/
theorem map_fundamentalDomain {F : Type*} [NormedAddCommGroup F] [NormedSpace K F] (f : E ≃ₗ[K] F) :
    f '' (fundamentalDomain b) = fundamentalDomain (b.map f) := by
  ext x
  rw [mem_fundamentalDomain]; rw [Basis.map_repr]; rw [LinearEquiv.trans_apply]; rw [← mem_fundamentalDomain]; rw [show f.symm x = f.toEquiv.symm x by rfl]; rw [← Set.mem_image_equiv]
  rfl

@[simp]
/--
theorem `fundamentalDomain_reindex` / 定理 `fundamentalDomain_reindex`

English:
theorem fundamentalDomain_reindex
  given: {ι' : Type*} (e : ι ≃ ι')
  proof: by
  ext
  simp [e.forall_congr_left]

中文:
定理 fundamentalDomain_reindex
  条件: {ι' : 类型} (e : ι ≃ ι')
  证明: by
  ext
  simp [e.forall_congr_left]

Depends on / 依赖: e.forall_congr_left, forall_congr_left
-/
theorem fundamentalDomain_reindex {ι' : Type*} (e : ι ≃ ι') :
    fundamentalDomain (b.reindex e) = fundamentalDomain b := by
  ext
  simp [e.forall_congr_left]

variable [IsStrictOrderedRing K]

/--
lemma `fundamentalDomain_pi_basisFun` / 引理 `fundamentalDomain_pi_basisFun`

English:
lemma fundamentalDomain_pi_basisFun
  given: [Fintype ι]
  proof: by
  ext; simp

中文:
引理 fundamentalDomain_pi_basisFun
  条件: [Fintype ι]
  证明: by
  ext; simp
-/
lemma fundamentalDomain_pi_basisFun [Fintype ι] :
    fundamentalDomain (Pi.basisFun Real ι) = Set.pi Set.univ fun _ : ι => Set.Ico (0 : Real) 1 := by
  ext; simp

variable [FloorRing K]

section Fintype

variable [Fintype ι]

/--
Definition of `floor` / `floor` 的定义

English:
definition floor
  signature: (m : E)
  body: ∑ i, ⌊b.repr m i⌋ • b.restrictScalars Int i

中文:
定义 floor
  签名: (m : E)
  定义体: ∑ i, ⌊b.repr m i⌋ • b.restrictScalars Int i

Depends on / 依赖: b.repr, b.restrictScalars, restrictScalars
-/
def floor (m : E) : span Int (Set.range b) := ∑ i, ⌊b.repr m i⌋ • b.restrictScalars Int i

/--
Definition of `ceil` / `ceil` 的定义

English:
definition ceil
  signature: (m : E)
  body: ∑ i, ⌈b.repr m i⌉ • b.restrictScalars Int i

@[simp]

中文:
定义 ceil
  签名: (m : E)
  定义体: ∑ i, ⌈b.repr m i⌉ • b.restrictScalars Int i

@[simp]

Depends on / 依赖: b.repr, b.restrictScalars, restrictScalars
-/
def ceil (m : E) : span Int (Set.range b) := ∑ i, ⌈b.repr m i⌉ • b.restrictScalars Int i

@[simp]
/--
theorem `repr_floor_apply` / 定理 `repr_floor_apply`

English:
theorem repr_floor_apply
  given: (m : E) (i : ι)
  statement: b.repr (floor b m) i = ⌊b.repr m i⌋
  proof: by
  classical simp only [floor, ← Int.cast_smul_eq_zsmul K, b.repr.map_smul, Finsupp.single_apply,
    Finset.sum_apply', Basis.repr_self, Finsupp.smul_single', mul_one, Finset.sum_ite_eq', coe_sum,
    Finset.mem_univ, if_true, coe_smul_of_tower, Basis.restrictScalars_apply, map_sum]

@[simp]

中文:
定理 repr_floor_apply
  条件: (m : E) (i : ι)
  结论: b.repr (floor b m) i = ⌊b.repr m i⌋
  证明: by
  classical simp only [floor, ← Int.cast_smul_eq_zsmul K, b.repr.map_smul, Finsupp.single_apply,
    Finset.sum_apply', Basis.repr_self, Finsupp.smul_single', mul_one, Finset.sum_ite_eq', coe_sum,
    Finset.mem_univ, if_true, coe_smul_of_tower, Basis.restrictScalars_apply, map_sum]

@[simp]

Depends on / 依赖: Basis.repr_self, Basis.restrictScalars_apply, Finset, Finset.mem_univ, Finset.sum_apply, Finset.sum_ite_eq, Finsupp, Finsupp.single_apply, Finsupp.smul_single, Int.cast_smul_eq_zsmul, b.repr.map_smul, cast_smul_eq_zsmul, classical, coe_smul_of_tower, coe_sum, if_true, map_smul, map_sum, mem_univ, mul_one
-/
theorem repr_floor_apply (m : E) (i : ι) : b.repr (floor b m) i = ⌊b.repr m i⌋ := by
  classical simp only [floor, ← Int.cast_smul_eq_zsmul K, b.repr.map_smul, Finsupp.single_apply,
    Finset.sum_apply', Basis.repr_self, Finsupp.smul_single', mul_one, Finset.sum_ite_eq', coe_sum,
    Finset.mem_univ, if_true, coe_smul_of_tower, Basis.restrictScalars_apply, map_sum]

@[simp]
/--
theorem `repr_ceil_apply` / 定理 `repr_ceil_apply`

English:
theorem repr_ceil_apply
  given: (m : E) (i : ι)
  statement: b.repr (ceil b m) i = ⌈b.repr m i⌉
  proof: by
  classical simp only [ceil, ← Int.cast_smul_eq_zsmul K, b.repr.map_smul, Finsupp.single_apply,
    Finset.sum_apply', Basis.repr_self, Finsupp.smul_single', mul_one, Finset.sum_ite_eq', coe_sum,
    Finset.mem_univ, if_true, coe_smul_of_tower, Basis.restrictScalars_apply, map_sum]

@[simp]

中文:
定理 repr_ceil_apply
  条件: (m : E) (i : ι)
  结论: b.repr (ceil b m) i = ⌈b.repr m i⌉
  证明: by
  classical simp only [ceil, ← Int.cast_smul_eq_zsmul K, b.repr.map_smul, Finsupp.single_apply,
    Finset.sum_apply', Basis.repr_self, Finsupp.smul_single', mul_one, Finset.sum_ite_eq', coe_sum,
    Finset.mem_univ, if_true, coe_smul_of_tower, Basis.restrictScalars_apply, map_sum]

@[simp]

Depends on / 依赖: Basis.repr_self, Basis.restrictScalars_apply, Finset, Finset.mem_univ, Finset.sum_apply, Finset.sum_ite_eq, Finsupp, Finsupp.single_apply, Finsupp.smul_single, Int.cast_smul_eq_zsmul, b.repr.map_smul, cast_smul_eq_zsmul, classical, coe_smul_of_tower, coe_sum, if_true, map_smul, map_sum, mem_univ, mul_one
-/
theorem repr_ceil_apply (m : E) (i : ι) : b.repr (ceil b m) i = ⌈b.repr m i⌉ := by
  classical simp only [ceil, ← Int.cast_smul_eq_zsmul K, b.repr.map_smul, Finsupp.single_apply,
    Finset.sum_apply', Basis.repr_self, Finsupp.smul_single', mul_one, Finset.sum_ite_eq', coe_sum,
    Finset.mem_univ, if_true, coe_smul_of_tower, Basis.restrictScalars_apply, map_sum]

@[simp]
/--
theorem `floor_eq_self_of_mem` / 定理 `floor_eq_self_of_mem`

English:
theorem floor_eq_self_of_mem
  given: (m : E) (h : m in span Int (Set.range b))
  statement: (floor b m : E) = m
  proof: by
  apply b.ext_elem
  simp_rw [repr_floor_apply b]
  intro i
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem Int _).mp h i
  rw [← hz]
  exact congr_arg (Int.cast : Int -> K) (Int.floor_intCast z)

@[simp]

中文:
定理 floor_eq_self_of_mem
  条件: (m : E) (h : m in span 整数 (Set.range b))
  结论: (floor b m : E) = m
  证明: by
  apply b.ext_elem
  simp_rw [repr_floor_apply b]
  intro i
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem Int _).mp h i
  rw [← hz]
  exact congr_arg (Int.cast : Int -> K) (Int.floor_intCast z)

@[simp]

Depends on / 依赖: Int.cast, Int.floor_intCast, b.ext_elem, b.mem_span_iff_repr_mem, congr_arg, ext_elem, floor_intCast, mem_span_iff_repr_mem, repr_floor_apply, simp_rw
-/
theorem floor_eq_self_of_mem (m : E) (h : m in span Int (Set.range b)) : (floor b m : E) = m := by
  apply b.ext_elem
  simp_rw [repr_floor_apply b]
  intro i
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem Int _).mp h i
  rw [← hz]
  exact congr_arg (Int.cast : Int -> K) (Int.floor_intCast z)

@[simp]
/--
theorem `ceil_eq_self_of_mem` / 定理 `ceil_eq_self_of_mem`

English:
theorem ceil_eq_self_of_mem
  given: (m : E) (h : m in span Int (Set.range b))
  statement: (ceil b m : E) = m
  proof: by
  apply b.ext_elem
  simp_rw [repr_ceil_apply b]
  intro i
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem Int _).mp h i
  rw [← hz]
  exact congr_arg (Int.cast : Int -> K) (Int.ceil_intCast z)

中文:
定理 ceil_eq_self_of_mem
  条件: (m : E) (h : m in span 整数 (Set.range b))
  结论: (ceil b m : E) = m
  证明: by
  apply b.ext_elem
  simp_rw [repr_ceil_apply b]
  intro i
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem Int _).mp h i
  rw [← hz]
  exact congr_arg (Int.cast : Int -> K) (Int.ceil_intCast z)

Depends on / 依赖: Int.cast, Int.ceil_intCast, b.ext_elem, b.mem_span_iff_repr_mem, ceil_intCast, congr_arg, ext_elem, mem_span_iff_repr_mem, repr_ceil_apply, simp_rw
-/
theorem ceil_eq_self_of_mem (m : E) (h : m in span Int (Set.range b)) : (ceil b m : E) = m := by
  apply b.ext_elem
  simp_rw [repr_ceil_apply b]
  intro i
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem Int _).mp h i
  rw [← hz]
  exact congr_arg (Int.cast : Int -> K) (Int.ceil_intCast z)

/--
Definition of `fract` / `fract` 的定义

English:
definition fract
  signature: (m : E)
  body: m - floor b m

中文:
定义 fract
  签名: (m : E)
  定义体: m - floor b m
-/
def fract (m : E) : E := m - floor b m

/--
theorem `fract_apply` / 定理 `fract_apply`

English:
theorem fract_apply
  given: (m : E)
  statement: fract b m = m - floor b m
  proof: rfl

@[simp]

中文:
定理 fract_apply
  条件: (m : E)
  结论: fract b m = m - floor b m
  证明: rfl

@[simp]
-/
theorem fract_apply (m : E) : fract b m = m - floor b m := rfl

@[simp]
/--
theorem `repr_fract_apply` / 定理 `repr_fract_apply`

English:
theorem repr_fract_apply
  given: (m : E) (i : ι)
  statement: b.repr (fract b m) i = Int.fract (b.repr m i)
  proof: by
  rw [fract]; rw [map_sub]; rw [Finsupp.coe_sub]; rw [Pi.sub_apply]; rw [repr_floor_apply]; rw [Int.fract]

@[simp]

中文:
定理 repr_fract_apply
  条件: (m : E) (i : ι)
  结论: b.repr (fract b m) i = 整数.fract (b.repr m i)
  证明: by
  rw [fract]; rw [map_sub]; rw [Finsupp.coe_sub]; rw [Pi.sub_apply]; rw [repr_floor_apply]; rw [Int.fract]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.coe_sub, Int.fract, Pi.sub_apply, coe_sub, map_sub, repr_floor_apply, sub_apply
-/
theorem repr_fract_apply (m : E) (i : ι) : b.repr (fract b m) i = Int.fract (b.repr m i) := by
  rw [fract]; rw [map_sub]; rw [Finsupp.coe_sub]; rw [Pi.sub_apply]; rw [repr_floor_apply]; rw [Int.fract]

@[simp]
/--
theorem `fract_fract` / 定理 `fract_fract`

English:
theorem fract_fract
  given: (m : E)
  statement: fract b (fract b m) = fract b m
  proof: Basis.ext_elem b fun _ => by simp only [repr_fract_apply, Int.fract_fract]

@[simp]

中文:
定理 fract_fract
  条件: (m : E)
  结论: fract b (fract b m) = fract b m
  证明: Basis.ext_elem b fun _ => by simp only [repr_fract_apply, Int.fract_fract]

@[simp]

Depends on / 依赖: Basis.ext_elem, Int.fract_fract, ext_elem, fract_fract, repr_fract_apply
-/
theorem fract_fract (m : E) : fract b (fract b m) = fract b m :=
  Basis.ext_elem b fun _ => by simp only [repr_fract_apply, Int.fract_fract]

@[simp]
/--
theorem `fract_zSpan_add` / 定理 `fract_zSpan_add`

English:
theorem fract_zSpan_add
  given: (m : E) {v : E} (h : v in span Int (Set.range b))
  proof: by
  refine (Basis.ext_elem_iff b).mpr fun i => ?_
  simp_rw [repr_fract_apply, Int.fract_eq_fract]
  use (b.restrictScalars Int).repr ⟨v, h⟩ i
  rw [map_add]; rw [Finsupp.coe_add]; rw [Pi.add_apply]; rw [add_tsub_cancel_right]; rw [← eq_intCast (algebraMap Int K) _]; rw [Basis.restrictScalars_repr_

中文:
定理 fract_zSpan_add
  条件: (m : E) {v : E} (h : v in span 整数 (Set.range b))
  证明: by
  refine (Basis.ext_elem_iff b).mpr fun i => ?_
  simp_rw [repr_fract_apply, Int.fract_eq_fract]
  use (b.restrictScalars Int).repr ⟨v, h⟩ i
  rw [map_add]; rw [Finsupp.coe_add]; rw [Pi.add_apply]; rw [add_tsub_cancel_right]; rw [← eq_intCast (algebraMap Int K) _]; rw [Basis.restrictScalars_repr_

Depends on / 依赖: Basis.ext_elem_iff, Basis.restrictScalars_repr_apply, Finsupp, Finsupp.coe_add, Int.fract_eq_fract, Pi.add_apply, add_apply, add_tsub_cancel_right, algebraMap, b.restrictScalars, coe_add, coe_mk, eq_intCast, ext_elem_iff, fract_eq_fract, map_add, repr_fract_apply, restrictScalars, restrictScalars_repr_apply, simp_rw
-/
theorem fract_zSpan_add (m : E) {v : E} (h : v in span Int (Set.range b)) :
    fract b (v + m) = fract b m := by
  refine (Basis.ext_elem_iff b).mpr fun i => ?_
  simp_rw [repr_fract_apply, Int.fract_eq_fract]
  use (b.restrictScalars Int).repr ⟨v, h⟩ i
  rw [map_add]; rw [Finsupp.coe_add]; rw [Pi.add_apply]; rw [add_tsub_cancel_right]; rw [← eq_intCast (algebraMap Int K) _]; rw [Basis.restrictScalars_repr_apply]; rw [coe_mk]

@[simp]
/--
theorem `fract_add_ZSpan` / 定理 `fract_add_ZSpan`

English:
theorem fract_add_ZSpan
  given: (m : E) {v : E} (h : v in span Int (Set.range b))
  proof: by rw [add_comm, fract_zSpan_add b m h]

中文:
定理 fract_add_ZSpan
  条件: (m : E) {v : E} (h : v in span 整数 (Set.range b))
  证明: by rw [add_comm, fract_zSpan_add b m h]

Depends on / 依赖: add_comm, fract_zSpan_add
-/
theorem fract_add_ZSpan (m : E) {v : E} (h : v in span Int (Set.range b)) :
    fract b (m + v) = fract b m := by rw [add_comm, fract_zSpan_add b m h]

variable {b} in
/--
theorem `fract_eq_self` / 定理 `fract_eq_self`

English:
theorem fract_eq_self
  given: {x : E}
  statement: fract b x = x ↔ x in fundamentalDomain b
  proof: by
  simp only [Basis.ext_elem_iff b, repr_fract_apply, Int.fract_eq_self,
    mem_fundamentalDomain, Set.mem_Ico]

中文:
定理 fract_eq_self
  条件: {x : E}
  结论: fract b x = x ↔ x in fundamentalDomain b
  证明: by
  simp only [Basis.ext_elem_iff b, repr_fract_apply, Int.fract_eq_self,
    mem_fundamentalDomain, Set.mem_Ico]

Depends on / 依赖: Basis.ext_elem_iff, Int.fract_eq_self, Set.mem_Ico, ext_elem_iff, fract_eq_self, mem_Ico, mem_fundamentalDomain, repr_fract_apply
-/
theorem fract_eq_self {x : E} : fract b x = x ↔ x in fundamentalDomain b := by
  simp only [Basis.ext_elem_iff b, repr_fract_apply, Int.fract_eq_self,
    mem_fundamentalDomain, Set.mem_Ico]

/--
theorem `fract_mem_fundamentalDomain` / 定理 `fract_mem_fundamentalDomain`

English:
theorem fract_mem_fundamentalDomain
  given: (x : E)
  statement: fract b x in fundamentalDomain b
  proof: fract_eq_self.mp (fract_fract b _)

中文:
定理 fract_mem_fundamentalDomain
  条件: (x : E)
  结论: fract b x in fundamentalDomain b
  证明: fract_eq_self.mp (fract_fract b _)

Depends on / 依赖: fract_eq_self, fract_eq_self.mp, fract_fract
-/
theorem fract_mem_fundamentalDomain (x : E) : fract b x in fundamentalDomain b :=
  fract_eq_self.mp (fract_fract b _)

/--
Definition of `fractRestrict` / `fractRestrict` 的定义

English:
definition fractRestrict
  signature: (x : E)
  body: ⟨fract b x, fract_mem_fundamentalDomain b x⟩

中文:
定义 fractRestrict
  签名: (x : E)
  定义体: ⟨fract b x, fract_mem_fundamentalDomain b x⟩

Depends on / 依赖: fract_mem_fundamentalDomain
-/
def fractRestrict (x : E) : fundamentalDomain b := ⟨fract b x, fract_mem_fundamentalDomain b x⟩

/--
theorem `fractRestrict_surjective` / 定理 `fractRestrict_surjective`

English:
theorem fractRestrict_surjective
  statement: Function.Surjective (fractRestrict b)
  proof: fun x => ⟨↑x, Subtype.ext (fract_eq_self.mpr (Subtype.mem x))⟩

@[simp]

中文:
定理 fractRestrict_surjective
  结论: Function.Surjective (fractRestrict b)
  证明: fun x => ⟨↑x, Subtype.ext (fract_eq_self.mpr (Subtype.mem x))⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, Subtype.mem, fract_eq_self, fract_eq_self.mpr
-/
theorem fractRestrict_surjective : Function.Surjective (fractRestrict b) :=
  fun x => ⟨↑x, Subtype.ext (fract_eq_self.mpr (Subtype.mem x))⟩

@[simp]
/--
theorem `fractRestrict_apply` / 定理 `fractRestrict_apply`

English:
theorem fractRestrict_apply
  given: (x : E)
  statement: (fractRestrict b x : E) = fract b x
  proof: rfl

中文:
定理 fractRestrict_apply
  条件: (x : E)
  结论: (fractRestrict b x : E) = fract b x
  证明: rfl
-/
theorem fractRestrict_apply (x : E) : (fractRestrict b x : E) = fract b x := rfl

/--
theorem `fract_eq_fract` / 定理 `fract_eq_fract`

English:
theorem fract_eq_fract
  given: (m n : E)
  statement: fract b m = fract b n ↔ -m + n in span Int (Set.range b)
  proof: by
  rw [eq_comm]; rw [Basis.ext_elem_iff b]
  simp_rw [repr_fract_apply, Int.fract_eq_fract, eq_comm, Basis.mem_span_iff_repr_mem,
    sub_eq_neg_add, map_add, map_neg, Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply,
    Pi.neg_apply, ← eq_intCast (algebraMap Int K) _, Set.mem_range]

中文:
定理 fract_eq_fract
  条件: (m n : E)
  结论: fract b m = fract b n ↔ -m + n in span 整数 (Set.range b)
  证明: by
  rw [eq_comm]; rw [Basis.ext_elem_iff b]
  simp_rw [repr_fract_apply, Int.fract_eq_fract, eq_comm, Basis.mem_span_iff_repr_mem,
    sub_eq_neg_add, map_add, map_neg, Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply,
    Pi.neg_apply, ← eq_intCast (algebraMap Int K) _, Set.mem_range]

Depends on / 依赖: Basis.ext_elem_iff, Basis.mem_span_iff_repr_mem, Finsupp, Finsupp.coe_add, Finsupp.coe_neg, Int.fract_eq_fract, Pi.add_apply, Pi.neg_apply, Set.mem_range, add_apply, algebraMap, coe_add, coe_neg, eq_comm, eq_intCast, ext_elem_iff, fract_eq_fract, map_add, map_neg, mem_range
-/
theorem fract_eq_fract (m n : E) : fract b m = fract b n ↔ -m + n in span Int (Set.range b) := by
  rw [eq_comm]; rw [Basis.ext_elem_iff b]
  simp_rw [repr_fract_apply, Int.fract_eq_fract, eq_comm, Basis.mem_span_iff_repr_mem,
    sub_eq_neg_add, map_add, map_neg, Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply,
    Pi.neg_apply, ← eq_intCast (algebraMap Int K) _, Set.mem_range]

/--
theorem `norm_fract_le` / 定理 `norm_fract_le`

English:
theorem norm_fract_le
  given: [HasSolidNorm K] (m : E)
  statement: ‖fract b m‖ <= ∑ i, ‖b i‖
  proof: by
  calc
    ‖fract b m‖ = ‖∑ i, b.repr (fract b m) i • b i‖ := by rw [b.sum_repr]
    _ = ‖∑ i, Int.fract (b.repr m i) • b i‖ := by simp_rw [repr_fract_apply]
    _ <= ∑ i, ‖Int.fract (b.repr m i) • b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖Int.fract (b.repr m i)‖ * ‖b i‖ := by simp_rw [norm_smul]
   

中文:
定理 norm_fract_le
  条件: [HasSolidNorm K] (m : E)
  结论: ‖fract b m‖ <= ∑ i, ‖b i‖
  证明: by
  calc
    ‖fract b m‖ = ‖∑ i, b.repr (fract b m) i • b i‖ := by rw [b.sum_repr]
    _ = ‖∑ i, Int.fract (b.repr m i) • b i‖ := by simp_rw [repr_fract_apply]
    _ <= ∑ i, ‖Int.fract (b.repr m i) • b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖Int.fract (b.repr m i)‖ * ‖b i‖ := by simp_rw [norm_smul]
   

Depends on / 依赖: Finset, Finset.sum_le_sum, Int.fract, b.repr, b.sum_repr, convert, mul_le_mul_of_nonneg_right, norm_nonneg, norm_one, norm_one.symm, norm_smul, norm_sum_le, one_mul, repr_fract_apply, simp_rw, sum_le_sum, sum_repr
-/
theorem norm_fract_le [HasSolidNorm K] (m : E) : ‖fract b m‖ <= ∑ i, ‖b i‖ := by
  calc
    ‖fract b m‖ = ‖∑ i, b.repr (fract b m) i • b i‖ := by rw [b.sum_repr]
    _ = ‖∑ i, Int.fract (b.repr m i) • b i‖ := by simp_rw [repr_fract_apply]
    _ <= ∑ i, ‖Int.fract (b.repr m i) • b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖Int.fract (b.repr m i)‖ * ‖b i‖ := by simp_rw [norm_smul]
    _ <= ∑ i, ‖b i‖ := Finset.sum_le_sum fun i _ => ?_
  suffices ‖Int.fract ((b.repr m) i)‖ <= 1 by
    convert! mul_le_mul_of_nonneg_right this (norm_nonneg _ : 0 <= ‖b i‖)
    exact (one_mul _).symm
  rw [(norm_one.symm : 1 = ‖(1 : K)‖)]
  apply norm_le_norm_of_abs_le_abs
  rw [abs_one]; rw [Int.abs_fract]
  exact le_of_lt (Int.fract_lt_one _)

section Unique

variable [Unique ι]

@[simp]
/--
theorem `coe_floor_self` / 定理 `coe_floor_self`

English:
theorem coe_floor_self
  given: (k : K)
  statement: (floor (Basis.singleton ι K) k : K) = ⌊k⌋
  proof: Basis.ext_elem (Basis.singleton ι K) fun _ => by
    rw [repr_floor_apply]; rw [Basis.singleton_repr]; rw [Basis.singleton_repr]

@[simp]

中文:
定理 coe_floor_self
  条件: (k : K)
  结论: (floor (Basis.singleton ι K) k : K) = ⌊k⌋
  证明: Basis.ext_elem (Basis.singleton ι K) fun _ => by
    rw [repr_floor_apply]; rw [Basis.singleton_repr]; rw [Basis.singleton_repr]

@[simp]

Depends on / 依赖: Basis.ext_elem, Basis.singleton, Basis.singleton_repr, ext_elem, repr_floor_apply, singleton, singleton_repr
-/
theorem coe_floor_self (k : K) : (floor (Basis.singleton ι K) k : K) = ⌊k⌋ :=
  Basis.ext_elem (Basis.singleton ι K) fun _ => by
    rw [repr_floor_apply]; rw [Basis.singleton_repr]; rw [Basis.singleton_repr]

@[simp]
/--
theorem `coe_fract_self` / 定理 `coe_fract_self`

English:
theorem coe_fract_self
  given: (k : K)
  statement: (fract (Basis.singleton ι K) k : K) = Int.fract k
  proof: Basis.ext_elem (Basis.singleton ι K) fun _ => by
    rw [repr_fract_apply]; rw [Basis.singleton_repr]; rw [Basis.singleton_repr]

中文:
定理 coe_fract_self
  条件: (k : K)
  结论: (fract (Basis.singleton ι K) k : K) = 整数.fract k
  证明: Basis.ext_elem (Basis.singleton ι K) fun _ => by
    rw [repr_fract_apply]; rw [Basis.singleton_repr]; rw [Basis.singleton_repr]

Depends on / 依赖: Basis.ext_elem, Basis.singleton, Basis.singleton_repr, ext_elem, repr_fract_apply, singleton, singleton_repr
-/
theorem coe_fract_self (k : K) : (fract (Basis.singleton ι K) k : K) = Int.fract k :=
  Basis.ext_elem (Basis.singleton ι K) fun _ => by
    rw [repr_fract_apply]; rw [Basis.singleton_repr]; rw [Basis.singleton_repr]

end Unique

end Fintype

/--
theorem `fundamentalDomain_isBounded` / 定理 `fundamentalDomain_isBounded`

English:
theorem fundamentalDomain_isBounded
  given: [Finite ι] [HasSolidNorm K]
  proof: by
  cases nonempty_fintype ι
  refine isBounded_iff_forall_norm_le.2 ⟨∑ j, ‖b j‖, fun x hx => ?_⟩
  rw [← fract_eq_self.mpr hx]
  apply norm_fract_le

中文:
定理 fundamentalDomain_isBounded
  条件: [Finite ι] [HasSolidNorm K]
  证明: by
  cases nonempty_fintype ι
  refine isBounded_iff_forall_norm_le.2 ⟨∑ j, ‖b j‖, fun x hx => ?_⟩
  rw [← fract_eq_self.mpr hx]
  apply norm_fract_le

Depends on / 依赖: fract_eq_self, fract_eq_self.mpr, isBounded_iff_forall_norm_le, nonempty_fintype, norm_fract_le
-/
theorem fundamentalDomain_isBounded [Finite ι] [HasSolidNorm K] :
    IsBounded (fundamentalDomain b) := by
  cases nonempty_fintype ι
  refine isBounded_iff_forall_norm_le.2 ⟨∑ j, ‖b j‖, fun x hx => ?_⟩
  rw [← fract_eq_self.mpr hx]
  apply norm_fract_le

/--
theorem `vadd_mem_fundamentalDomain` / 定理 `vadd_mem_fundamentalDomain`

English:
theorem vadd_mem_fundamentalDomain
  given: [Fintype ι] (y : span Int (Set.range b)) (x : E)
  proof: by
  rw [Subtype.ext_iff]; rw [← add_right_inj x]; rw [NegMemClass.coe_neg]; rw [← sub_eq_add_neg]; rw [← fract_apply]; rw [← fract_zSpan_add b _ (Subtype.mem y)]; rw [add_comm]; rw [← vadd_eq_add]; rw [← vadd_def]; rw [eq_comm]; rw [←
    fract_eq_self]

中文:
定理 vadd_mem_fundamentalDomain
  条件: [Fintype ι] (y : span 整数 (Set.range b)) (x : E)
  证明: by
  rw [Subtype.ext_iff]; rw [← add_right_inj x]; rw [NegMemClass.coe_neg]; rw [← sub_eq_add_neg]; rw [← fract_apply]; rw [← fract_zSpan_add b _ (Subtype.mem y)]; rw [add_comm]; rw [← vadd_eq_add]; rw [← vadd_def]; rw [eq_comm]; rw [←
    fract_eq_self]

Depends on / 依赖: NegMemClass, NegMemClass.coe_neg, Subtype, Subtype.ext_iff, Subtype.mem, add_comm, add_right_inj, coe_neg, eq_comm, ext_iff, fract_apply, fract_eq_self, fract_zSpan_add, sub_eq_add_neg, vadd_def, vadd_eq_add
-/
theorem vadd_mem_fundamentalDomain [Fintype ι] (y : span Int (Set.range b)) (x : E) :
    y +ᵥ x in fundamentalDomain b ↔ y = -floor b x := by
  rw [Subtype.ext_iff]; rw [← add_right_inj x]; rw [NegMemClass.coe_neg]; rw [← sub_eq_add_neg]; rw [← fract_apply]; rw [← fract_zSpan_add b _ (Subtype.mem y)]; rw [add_comm]; rw [← vadd_eq_add]; rw [← vadd_def]; rw [eq_comm]; rw [←
    fract_eq_self]

/--
theorem `exist_unique_vadd_mem_fundamentalDomain` / 定理 `exist_unique_vadd_mem_fundamentalDomain`

English:
theorem exist_unique_vadd_mem_fundamentalDomain
  given: [Finite ι] (x : E)
  proof: by
  cases nonempty_fintype ι
  refine ⟨-floor b x, ?_, fun y h => ?_⟩
  · exact (vadd_mem_fundamentalDomain b (-floor b x) x).mpr rfl
  · exact (vadd_mem_fundamentalDomain b y x).mp h

中文:
定理 exist_unique_vadd_mem_fundamentalDomain
  条件: [Finite ι] (x : E)
  证明: by
  cases nonempty_fintype ι
  refine ⟨-floor b x, ?_, fun y h => ?_⟩
  · exact (vadd_mem_fundamentalDomain b (-floor b x) x).mpr rfl
  · exact (vadd_mem_fundamentalDomain b y x).mp h

Depends on / 依赖: nonempty_fintype, vadd_mem_fundamentalDomain
-/
theorem exist_unique_vadd_mem_fundamentalDomain [Finite ι] (x : E) :
    exists! v : span Int (Set.range b), v +ᵥ x in fundamentalDomain b := by
  cases nonempty_fintype ι
  refine ⟨-floor b x, ?_, fun y h => ?_⟩
  · exact (vadd_mem_fundamentalDomain b (-floor b x) x).mpr rfl
  · exact (vadd_mem_fundamentalDomain b y x).mp h

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `quotientEquiv` / `quotientEquiv` 的定义

English:
definition quotientEquiv
  signature: [Fintype ι]
  body: by
  refine Equiv.ofBijective ?_ ⟨fun x y => ?_, fun x => ?_⟩
  · refine fun q => Quotient.liftOn q (fractRestrict b) (fun _ _ h => ?_)
    rw [Subtype.mk.injEq]; rw [fractRestrict_apply]; rw [fractRestrict_apply]; rw [fract_eq_fract]
    exact QuotientAddGroup.leftRel_apply.mp h
  · induction x, y 

中文:
定义 quotientEquiv
  签名: [Fintype ι]
  定义体: by
  refine Equiv.ofBijective ?_ ⟨fun x y => ?_, fun x => ?_⟩
  · refine fun q => Quotient.liftOn q (fractRestrict b) (fun _ _ h => ?_)
    rw [Subtype.mk.injEq]; rw [fractRestrict_apply]; rw [fractRestrict_apply]; rw [fract_eq_fract]
    exact QuotientAddGroup.leftRel_apply.mp h
  · induction x, y 

Depends on / 依赖: Equiv.ofBijective, Quotient, Quotient.inductionOn, Quotient.liftOn, Quotient.liftOn_mk, QuotientAddGroup, QuotientAddGroup.leftRel_apply.mp, Set.range, Subtype, Subtype.mk.injEq, fractRestrict, fractRestrict_apply, fract_eq_fract, leftRel_apply, liftOn, liftOn_mk, ofBijective, quotientRel
-/
def quotientEquiv [Fintype ι] :
    E ⧸ span Int (Set.range b) ≃ (fundamentalDomain b) := by
  refine Equiv.ofBijective ?_ ⟨fun x y => ?_, fun x => ?_⟩
  · refine fun q => Quotient.liftOn q (fractRestrict b) (fun _ _ h => ?_)
    rw [Subtype.mk.injEq]; rw [fractRestrict_apply]; rw [fractRestrict_apply]; rw [fract_eq_fract]
    exact QuotientAddGroup.leftRel_apply.mp h
  · induction x, y using Quotient.inductionOn₂
    intro hxy
    rw [Quotient.liftOn_mk (s := quotientRel (span Int (Set.range b)))]; rw [fractRestrict]; rw [Quotient.liftOn_mk (s := quotientRel (span Int (Set.range b)))]; rw [fractRestrict]; rw [Subtype.mk.injEq] at hxy
    apply Quotient.sound'
    rwa [QuotientAddGroup.leftRel_apply, mem_toAddSubgroup, ← fract_eq_fract]
  · obtain ⟨a, rfl⟩ := fractRestrict_surjective b x
    exact ⟨Quotient.mk'' a, rfl⟩

@[simp]
/--
theorem `quotientEquiv_apply_mk` / 定理 `quotientEquiv_apply_mk`

English:
theorem quotientEquiv_apply_mk
  given: [Fintype ι] (x : E)
  proof: rfl

@[simp]

中文:
定理 quotientEquiv_apply_mk
  条件: [Fintype ι] (x : E)
  证明: rfl

@[simp]
-/
theorem quotientEquiv_apply_mk [Fintype ι] (x : E) :
    quotientEquiv b (Submodule.Quotient.mk x) = fractRestrict b x := rfl

@[simp]
/--
theorem `quotientEquiv.symm_apply` / 定理 `quotientEquiv.symm_apply`

English:
theorem quotientEquiv.symm_apply
  given: [Fintype ι] (x : fundamentalDomain b)
  proof: by
  rw [Equiv.symm_apply_eq]; rw [quotientEquiv_apply_mk b ↑x]; rw [Subtype.ext_iff]; rw [fractRestrict_apply]
  exact (fract_eq_self.mpr x.prop).symm

中文:
定理 quotientEquiv.symm_apply
  条件: [Fintype ι] (x : fundamentalDomain b)
  证明: by
  rw [Equiv.symm_apply_eq]; rw [quotientEquiv_apply_mk b ↑x]; rw [Subtype.ext_iff]; rw [fractRestrict_apply]
  exact (fract_eq_self.mpr x.prop).symm

Depends on / 依赖: Equiv.symm_apply_eq, Subtype, Subtype.ext_iff, ext_iff, fractRestrict_apply, fract_eq_self, fract_eq_self.mpr, quotientEquiv_apply_mk, symm_apply_eq, x.prop
-/
theorem quotientEquiv.symm_apply [Fintype ι] (x : fundamentalDomain b) :
    (quotientEquiv b).symm x = Submodule.Quotient.mk ↑x := by
  rw [Equiv.symm_apply_eq]; rw [quotientEquiv_apply_mk b ↑x]; rw [Subtype.ext_iff]; rw [fractRestrict_apply]
  exact (fract_eq_self.mpr x.prop).symm

end NormedLatticeField

section Real

/--
theorem `discreteTopology_pi_basisFun` / 定理 `discreteTopology_pi_basisFun`

English:
theorem discreteTopology_pi_basisFun
  given: [Finite ι]
  proof: by
  cases nonempty_fintype ι
  refine discreteTopology_iff_isOpen_singleton_zero.mpr ⟨Metric.ball 0 1, Metric.isOpen_ball, ?_⟩
  ext x
  rw [Set.mem_preimage]; rw [mem_ball_zero_iff]; rw [pi_norm_lt_iff zero_lt_one]; rw [Set.mem_singleton_iff]
  simp_rw [← coe_eq_zero, funext_iff, Pi.zero_apply, Re

中文:
定理 discreteTopology_pi_basisFun
  条件: [Finite ι]
  证明: by
  cases nonempty_fintype ι
  refine discreteTopology_iff_isOpen_singleton_zero.mpr ⟨Metric.ball 0 1, Metric.isOpen_ball, ?_⟩
  ext x
  rw [Set.mem_preimage]; rw [mem_ball_zero_iff]; rw [pi_norm_lt_iff zero_lt_one]; rw [Set.mem_singleton_iff]
  simp_rw [← coe_eq_zero, funext_iff, Pi.zero_apply, Re

Depends on / 依赖: Int.abs_lt_one_iff, Int.cast_abs, Int.cast_eq_z, Int.cast_lt, Int.cast_one, Metric, Metric.ball, Metric.isOpen_ball, Pi.zero_apply, Real.norm_eq_abs, Set.mem_preimage, Set.mem_singleton_iff, abs_lt_one_iff, cast_abs, cast_eq_z, cast_lt, cast_one, coe_eq_zero, discreteTopology_iff_isOpen_singleton_zero, discreteTopology_iff_isOpen_singleton_zero.mpr
-/
theorem discreteTopology_pi_basisFun [Finite ι] :
    DiscreteTopology (span Int (Set.range (Pi.basisFun Real ι))) := by
  cases nonempty_fintype ι
  refine discreteTopology_iff_isOpen_singleton_zero.mpr ⟨Metric.ball 0 1, Metric.isOpen_ball, ?_⟩
  ext x
  rw [Set.mem_preimage]; rw [mem_ball_zero_iff]; rw [pi_norm_lt_iff zero_lt_one]; rw [Set.mem_singleton_iff]
  simp_rw [← coe_eq_zero, funext_iff, Pi.zero_apply, Real.norm_eq_abs]
  refine forall_congr' (fun i => ?_)
  rsuffices ⟨y, hy⟩ : exists (y : Int), (y : Real) = (x : ι -> Real) i
  · rw [← hy, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff, Int.cast_eq_zero]
  exact ((Pi.basisFun Real ι).mem_span_iff_repr_mem Int x).mp (SetLike.coe_mem x) i

variable [NormedAddCommGroup E] [NormedSpace Real E] (b : Basis ι Real E)

/--
theorem `fundamentalDomain_subset_parallelepiped` / 定理 `fundamentalDomain_subset_parallelepiped`

English:
theorem fundamentalDomain_subset_parallelepiped
  given: [Fintype ι]
  proof: by
  rw [fundamentalDomain]; rw [parallelepiped_basis_eq]; rw [Set.ofPred_subset_ofPred]
  exact fun _ h i => Set.Ico_subset_Icc_self (h i)

中文:
定理 fundamentalDomain_subset_parallelepiped
  条件: [Fintype ι]
  证明: by
  rw [fundamentalDomain]; rw [parallelepiped_basis_eq]; rw [Set.ofPred_subset_ofPred]
  exact fun _ h i => Set.Ico_subset_Icc_self (h i)

Depends on / 依赖: Ico_subset_Icc_self, Set.Ico_subset_Icc_self, Set.ofPred_subset_ofPred, fundamentalDomain, ofPred_subset_ofPred, parallelepiped_basis_eq
-/
theorem fundamentalDomain_subset_parallelepiped [Fintype ι] :
    fundamentalDomain b subseteq parallelepiped b := by
  rw [fundamentalDomain]; rw [parallelepiped_basis_eq]; rw [Set.ofPred_subset_ofPred]
  exact fun _ h i => Set.Ico_subset_Icc_self (h i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: ι] : DiscreteTopology (span Int (Set.range b))
  body: by
  have h : Set.MapsTo b.equivFun (span Int (Set.range b)) (span Int (Set.range (Pi.basisFun Real ι))) := by
    intro _ hx
    rwa [SetLike.mem_coe, Basis.mem_span_iff_repr_mem] at hx ⊢
  convert! DiscreteTopology.of_continuous_injective ((continuous_equivFun_basis b).restrict h) ?_
  · exact dis

中文:
实例 [Finite
  签名: ι] : DiscreteTopology (span 整数 (Set.range b))
  定义体: by
  have h : Set.MapsTo b.equivFun (span Int (Set.range b)) (span Int (Set.range (Pi.basisFun Real ι))) := by
    intro _ hx
    rwa [SetLike.mem_coe, Basis.mem_span_iff_repr_mem] at hx ⊢
  convert! DiscreteTopology.of_continuous_injective ((continuous_equivFun_basis b).restrict h) ?_
  · exact dis

Depends on / 依赖: Basis.equivFun, Basis.mem_span_iff_repr_mem, DiscreteTopology, DiscreteTopology.of_continuous_injective, MapsTo, Pi.basisFun, Set.MapsTo, Set.range, SetLike, SetLike.mem_coe, Subtype, Subtype.map_injective, b.equivFun, basisFun, continuous_equivFun_basis, convert, discreteTopology_pi_basisFun, equivFun, injective, map_injective
-/
instance [Finite ι] : DiscreteTopology (span Int (Set.range b)) := by
  have h : Set.MapsTo b.equivFun (span Int (Set.range b)) (span Int (Set.range (Pi.basisFun Real ι))) := by
    intro _ hx
    rwa [SetLike.mem_coe, Basis.mem_span_iff_repr_mem] at hx ⊢
  convert! DiscreteTopology.of_continuous_injective ((continuous_equivFun_basis b).restrict h) ?_
  · exact discreteTopology_pi_basisFun
  · refine Subtype.map_injective _ (Basis.equivFun b).injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: ι] : DiscreteTopology (span Int (Set.range b)).toAddSubgroup
  body: inferInstanceAs DiscreteTopology (span Int (Set.range b))

中文:
实例 [Finite
  签名: ι] : DiscreteTopology (span 整数 (Set.range b)).toAddSubgroup
  定义体: inferInstanceAs DiscreteTopology (span Int (Set.range b))

Depends on / 依赖: DiscreteTopology, Set.range
-/
instance [Finite ι] : DiscreteTopology (span Int (Set.range b)).toAddSubgroup :=
inferInstanceAs DiscreteTopology (span Int (Set.range b))

/--
theorem `setFinite_inter` / 定理 `setFinite_inter`

English:
theorem setFinite_inter
  given: [ProperSpace E] [Finite ι] {s : Set E} (hs : Bornology.IsBounded s)
  proof: by
  have : DiscreteTopology (span Int (Set.range b)) := inferInstance
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hs ?_
  rw [← coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete

@[measurability]

中文:
定理 setFinite_inter
  条件: [命题erSpace E] [Finite ι] {s : Set E} (hs : Bornology.IsBounded s)
  证明: by
  have : DiscreteTopology (span Int (Set.range b)) := inferInstance
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hs ?_
  rw [← coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete

@[measurability]

Depends on / 依赖: AddSubgroup, AddSubgroup.isClosed_of_discrete, DiscreteTopology, DiscreteTopology.isDiscrete, Metric, Metric.finite_isBounded_inter_isClosed, Set.range, coe_toAddSubgroup, finite_isBounded_inter_isClosed, isClosed_of_discrete, isDiscrete
-/
theorem setFinite_inter [ProperSpace E] [Finite ι] {s : Set E} (hs : Bornology.IsBounded s) :
    Set.Finite (s inter span Int (Set.range b)) := by
  have : DiscreteTopology (span Int (Set.range b)) := inferInstance
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hs ?_
  rw [← coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete

@[measurability]
/--
theorem `fundamentalDomain_measurableSet` / 定理 `fundamentalDomain_measurableSet`

English:
theorem fundamentalDomain_measurableSet
  given: [MeasurableSpace E] [OpensMeasurableSpace E] [Finite ι]
  proof: by
  cases nonempty_fintype ι
  have : FiniteDimensional Real E := b.finiteDimensional_of_finite
  let D : Set (ι -> Real) := Set.pi Set.univ fun _ : ι => Set.Ico (0 : Real) 1
  rw [(_ : fundamentalDomain b = b.equivFun.toLinearMap ⁻¹' D)]
  · refine measurableSet_preimage (LinearMap.continuous_of_f

中文:
定理 fundamentalDomain_measurableSet
  条件: [MeasurableSpace E] [OpensMeasurableSpace E] [Finite ι]
  证明: by
  cases nonempty_fintype ι
  have : FiniteDimensional Real E := b.finiteDimensional_of_finite
  let D : Set (ι -> Real) := Set.pi Set.univ fun _ : ι => Set.Ico (0 : Real) 1
  rw [(_ : fundamentalDomain b = b.equivFun.toLinearMap ⁻¹' D)]
  · refine measurableSet_preimage (LinearMap.continuous_of_f

Depends on / 依赖: FiniteDimensional, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.continuous_of_finiteDimensional, MeasurableSet, MeasurableSet.pi, Set.Ico, Set.countable_univ, Set.mem_Ico, Set.mem_ofPred_eq, Set.mem_preim, Set.pi, Set.univ, b.equivFun.toLinearMap, b.finiteDimensional_of_finite, coe_coe, continuous_of_finiteDimensional, countable_univ, equivFun
-/
theorem fundamentalDomain_measurableSet [MeasurableSpace E] [OpensMeasurableSpace E] [Finite ι] :
    MeasurableSet (fundamentalDomain b) := by
  cases nonempty_fintype ι
  have : FiniteDimensional Real E := b.finiteDimensional_of_finite
  let D : Set (ι -> Real) := Set.pi Set.univ fun _ : ι => Set.Ico (0 : Real) 1
  rw [(_ : fundamentalDomain b = b.equivFun.toLinearMap ⁻¹' D)]
  · refine measurableSet_preimage (LinearMap.continuous_of_finiteDimensional _).measurable ?_
    exact MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico
  · ext
    simp only [D, fundamentalDomain, Set.mem_Ico, Set.mem_ofPred_eq, LinearEquiv.coe_coe,
      Set.mem_preimage, Basis.equivFun_apply, Set.mem_pi, Set.mem_univ, forall_true_left]

/--
theorem `isAddFundamentalDomain` / 定理 `isAddFundamentalDomain`

English:
theorem isAddFundamentalDomain
  statement: [Finite ι] [MeasurableSpace E] [OpensMeasurableSpace E]
  proof: by
  cases nonempty_fintype ι
  exact IsAddFundamentalDomain.mk' (nullMeasurableSet (fundamentalDomain_measurableSet b))
    fun x => exist_unique_vadd_mem_fundamentalDomain b x

中文:
定理 isAddFundamentalDomain
  结论: [Finite ι] [MeasurableSpace E] [OpensMeasurableSpace E]
  证明: by
  cases nonempty_fintype ι
  exact IsAddFundamentalDomain.mk' (nullMeasurableSet (fundamentalDomain_measurableSet b))
    fun x => exist_unique_vadd_mem_fundamentalDomain b x
-/
protected theorem isAddFundamentalDomain [Finite ι] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) :
    IsAddFundamentalDomain (span Int (Set.range b)) (fundamentalDomain b) μ := by
  cases nonempty_fintype ι
  exact IsAddFundamentalDomain.mk' (nullMeasurableSet (fundamentalDomain_measurableSet b))
    fun x => exist_unique_vadd_mem_fundamentalDomain b x

/--
theorem `isAddFundamentalDomain'` / 定理 `isAddFundamentalDomain'`

English:
theorem isAddFundamentalDomain'
  statement: [Finite ι] [MeasurableSpace E] [OpensMeasurableSpace E]
  proof: ZSpan.isAddFundamentalDomain b μ

中文:
定理 isAddFundamentalDomain'
  结论: [Finite ι] [MeasurableSpace E] [OpensMeasurableSpace E]
  证明: ZSpan.isAddFundamentalDomain b μ
-/
protected theorem isAddFundamentalDomain' [Finite ι] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) :
    IsAddFundamentalDomain (span Int (Set.range b)).toAddSubgroup (fundamentalDomain b) μ :=
  ZSpan.isAddFundamentalDomain b μ

/--
theorem `measure_fundamentalDomain_ne_zero` / 定理 `measure_fundamentalDomain_ne_zero`

English:
theorem measure_fundamentalDomain_ne_zero
  statement: [Finite ι] [MeasurableSpace E] [BorelSpace E]
  proof: by
  convert! (ZSpan.isAddFundamentalDomain b μ).measure_ne_zero (NeZero.ne μ)
exact inferInstanceAs VAddInvariantMeasure (span Int (Set.range b)).toAddSubgroup E μ

中文:
定理 measure_fundamentalDomain_ne_zero
  结论: [Finite ι] [MeasurableSpace E] [BorelSpace E]
  证明: by
  convert! (ZSpan.isAddFundamentalDomain b μ).measure_ne_zero (NeZero.ne μ)
exact inferInstanceAs VAddInvariantMeasure (span Int (Set.range b)).toAddSubgroup E μ

Depends on / 依赖: NeZero, NeZero.ne, Set.range, VAddInvariantMeasure, ZSpan.isAddFundamentalDomain, convert, isAddFundamentalDomain, measure_ne_zero, toAddSubgroup
-/
theorem measure_fundamentalDomain_ne_zero [Finite ι] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ] :
    μ (fundamentalDomain b) != 0 := by
  convert! (ZSpan.isAddFundamentalDomain b μ).measure_ne_zero (NeZero.ne μ)
exact inferInstanceAs VAddInvariantMeasure (span Int (Set.range b)).toAddSubgroup E μ

/--
theorem `measure_fundamentalDomain` / 定理 `measure_fundamentalDomain`

English:
theorem measure_fundamentalDomain
  statement: [Fintype ι] [DecidableEq ι] [MeasurableSpace E] (μ : Measure E)
  proof: by
  have : FiniteDimensional Real E := b.finiteDimensional_of_finite
  convert! μ.addHaar_preimage_linearEquiv (b.equiv b₀ (Equiv.refl ι)) (fundamentalDomain b₀)
  · rw [Set.eq_preimage_iff_image_eq (LinearEquiv.bijective _), map_fundamentalDomain,
      Basis.map_equiv, Equiv.refl_symm, Basis.rein

中文:
定理 measure_fundamentalDomain
  结论: [Fintype ι] [DecidableEq ι] [MeasurableSpace E] (μ : Measure E)
  证明: by
  have : FiniteDimensional Real E := b.finiteDimensional_of_finite
  convert! μ.addHaar_preimage_linearEquiv (b.equiv b₀ (Equiv.refl ι)) (fundamentalDomain b₀)
  · rw [Set.eq_preimage_iff_image_eq (LinearEquiv.bijective _), map_fundamentalDomain,
      Basis.map_equiv, Equiv.refl_symm, Basis.rein

Depends on / 依赖: Basis.map_equiv, Basis.reindex_refl, Equiv.refl, Equiv.refl_symm, FiniteDimensional, LinearEquiv, LinearEquiv.bijective, Set.eq_preimage_iff_image_eq, addHaar_preimage_linearEquiv, b.equiv, b.finiteDimensional_of_finite, bijective, convert, eq_preimage_iff_image_eq, finiteDimensional_of_finite, fundamentalDomain, map_equiv, map_fundamentalDomain, refl_symm, reindex_refl
-/
theorem measure_fundamentalDomain [Fintype ι] [DecidableEq ι] [MeasurableSpace E] (μ : Measure E)
    [BorelSpace E] [Measure.IsAddHaarMeasure μ] (b₀ : Basis ι Real E) :
    μ (fundamentalDomain b) = ENNReal.ofReal |b₀.det b| * μ (fundamentalDomain b₀) := by
  have : FiniteDimensional Real E := b.finiteDimensional_of_finite
  convert! μ.addHaar_preimage_linearEquiv (b.equiv b₀ (Equiv.refl ι)) (fundamentalDomain b₀)
  · rw [Set.eq_preimage_iff_image_eq (LinearEquiv.bijective _), map_fundamentalDomain,
      Basis.map_equiv, Equiv.refl_symm, Basis.reindex_refl]
  · simp

/--
theorem `measureReal_fundamentalDomain` / 定理 `measureReal_fundamentalDomain`

English:
theorem measureReal_fundamentalDomain
  proof: by
  simp [measureReal_def, measure_fundamentalDomain b μ b₀]

@[simp]

中文:
定理 measureReal_fundamentalDomain
  证明: by
  simp [measureReal_def, measure_fundamentalDomain b μ b₀]

@[simp]

Depends on / 依赖: measureReal_def, measure_fundamentalDomain
-/
theorem measureReal_fundamentalDomain
    [Fintype ι] [DecidableEq ι] [MeasurableSpace E] (μ : Measure E)
    [BorelSpace E] [Measure.IsAddHaarMeasure μ] (b₀ : Basis ι Real E) :
    μ.real (fundamentalDomain b) = |b₀.det b| * μ.real (fundamentalDomain b₀) := by
  simp [measureReal_def, measure_fundamentalDomain b μ b₀]

@[simp]
/--
theorem `volume_fundamentalDomain` / 定理 `volume_fundamentalDomain`

English:
theorem volume_fundamentalDomain
  given: [Fintype ι] [DecidableEq ι] (b : Basis ι Real (ι -> Real))
  proof: by
  rw [measure_fundamentalDomain b volume (b₀ := Pi.basisFun Real ι)]; rw [fundamentalDomain_pi_basisFun]; rw [volume_pi]; rw [Measure.pi_pi]; rw [Real.volume_Ico]; rw [sub_zero]; rw [ENNReal.ofReal_one]; rw [Finset.prod_const_one]; rw [mul_one]; rw [← Matrix.det_transpose]
  rfl

@[simp]

中文:
定理 volume_fundamentalDomain
  条件: [Fintype ι] [DecidableEq ι] (b : Basis ι 实数 (ι -> 实数))
  证明: by
  rw [measure_fundamentalDomain b volume (b₀ := Pi.basisFun Real ι)]; rw [fundamentalDomain_pi_basisFun]; rw [volume_pi]; rw [Measure.pi_pi]; rw [Real.volume_Ico]; rw [sub_zero]; rw [ENNReal.ofReal_one]; rw [Finset.prod_const_one]; rw [mul_one]; rw [← Matrix.det_transpose]
  rfl

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_one, Finset, Finset.prod_const_one, Matrix, Matrix.det_transpose, Measure, Measure.pi_pi, Pi.basisFun, Real.volume_Ico, basisFun, det_transpose, fundamentalDomain_pi_basisFun, measure_fundamentalDomain, mul_one, ofReal_one, pi_pi, prod_const_one, sub_zero, volume
-/
theorem volume_fundamentalDomain [Fintype ι] [DecidableEq ι] (b : Basis ι Real (ι -> Real)) :
    volume (fundamentalDomain b) = ENNReal.ofReal |(Matrix.of b).det| := by
  rw [measure_fundamentalDomain b volume (b₀ := Pi.basisFun Real ι)]; rw [fundamentalDomain_pi_basisFun]; rw [volume_pi]; rw [Measure.pi_pi]; rw [Real.volume_Ico]; rw [sub_zero]; rw [ENNReal.ofReal_one]; rw [Finset.prod_const_one]; rw [mul_one]; rw [← Matrix.det_transpose]
  rfl

@[simp]
/--
theorem `volume_real_fundamentalDomain` / 定理 `volume_real_fundamentalDomain`

English:
theorem volume_real_fundamentalDomain
  given: [Fintype ι] [DecidableEq ι] (b : Basis ι Real (ι -> Real))
  proof: by
  simp [measureReal_def]

中文:
定理 volume_real_fundamentalDomain
  条件: [Fintype ι] [DecidableEq ι] (b : Basis ι 实数 (ι -> 实数))
  证明: by
  simp [measureReal_def]

Depends on / 依赖: measureReal_def
-/
theorem volume_real_fundamentalDomain [Fintype ι] [DecidableEq ι] (b : Basis ι Real (ι -> Real)) :
    volume.real (fundamentalDomain b) = |(Matrix.of b).det| := by
  simp [measureReal_def]

/--
theorem `fundamentalDomain_ae_parallelepiped` / 定理 `fundamentalDomain_ae_parallelepiped`

English:
theorem fundamentalDomain_ae_parallelepiped
  statement: [Fintype ι] [MeasurableSpace E] (μ : Measure E)
  proof: by
  classical
  have : FiniteDimensional Real E := b.finiteDimensional_of_finite
  rw [← measure_symmDiff_eq_zero_iff]; rw [symmDiff_of_le (fundamentalDomain_subset_parallelepiped b)]
  suffices (parallelepiped b \ fundamentalDomain b) subseteq ⋃ i,
      AffineSubspace.mk' (b i) (span Real (b '' (

中文:
定理 fundamentalDomain_ae_parallelepiped
  结论: [Fintype ι] [MeasurableSpace E] (μ : Measure E)
  证明: by
  classical
  have : FiniteDimensional Real E := b.finiteDimensional_of_finite
  rw [← measure_symmDiff_eq_zero_iff]; rw [symmDiff_of_le (fundamentalDomain_subset_parallelepiped b)]
  suffices (parallelepiped b \ fundamentalDomain b) subseteq ⋃ i,
      AffineSubspace.mk' (b i) (span Real (b '' (

Depends on / 依赖: AffineSubspace, AffineSubspace.mem_mk, AffineSubspace.mem_top, AffineSubspace.mk, FiniteDimensional, Measure, Measure.addHaar_affineSubspace, Set.univ, addHaar_affineSubspace, b.finiteDimensional_of_finite, classical, finiteDimensional_of_finite, fundamentalDomain, fundamentalDomain_subset_parallelepiped, measure_iUnion_null_iff, measure_iUnion_null_iff.mpr, measure_mono_null, measure_symmDiff_eq_zero_iff, mem_mk, mem_top
-/
theorem fundamentalDomain_ae_parallelepiped [Fintype ι] [MeasurableSpace E] (μ : Measure E)
    [BorelSpace E] [Measure.IsAddHaarMeasure μ] :
    fundamentalDomain b =ᵐ[μ] parallelepiped b := by
  classical
  have : FiniteDimensional Real E := b.finiteDimensional_of_finite
  rw [← measure_symmDiff_eq_zero_iff]; rw [symmDiff_of_le (fundamentalDomain_subset_parallelepiped b)]
  suffices (parallelepiped b \ fundamentalDomain b) subseteq ⋃ i,
      AffineSubspace.mk' (b i) (span Real (b '' (Set.univ \ {i}))) by
    refine measure_mono_null this
      (measure_iUnion_null_iff.mpr fun i => Measure.addHaar_affineSubspace μ _ ?_)
    refine (ne_of_mem_of_not_mem' (AffineSubspace.mem_top _ _ 0)
      (AffineSubspace.mem_mk'.not.mpr ?_)).symm
    simp_rw [vsub_eq_sub, zero_sub, neg_mem_iff]
    exact linearIndependent_iff_notMem_span.mp b.linearIndependent i
  intro x hx
  simp_rw [parallelepiped_basis_eq, Set.mem_Icc, Set.mem_sdiff, Set.mem_ofPred_eq,
    mem_fundamentalDomain, Set.mem_Ico, not_forall, not_and, not_lt] at hx
  obtain ⟨i, hi⟩ := hx.2
  have : b.repr x i = 1 := le_antisymm (hx.1 i).2 (hi (hx.1 i).1)
  rw [← b.sum_repr x]; rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]; rw [this]; rw [one_smul]; rw [← vadd_eq_add]
  refine Set.mem_iUnion.mpr ⟨i, AffineSubspace.vadd_mem_mk' _
    (sum_smul_mem _ _ (fun i hi => Submodule.subset_span ?_))⟩
  exact ⟨i, Set.mem_sdiff_singleton.mpr ⟨trivial, Finset.ne_of_mem_erase hi⟩, rfl⟩

end Real

end ZSpan

section ZLattice

open Submodule Module ZSpan

-- TODO: generalize this class to other rings than `ℤ`
/--
Definition of `IsZLattice` / `IsZLattice` 的定义

English:
class IsZLattice
  parameters: (K : Type*) [NormedField K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  axioms and operations (1):
    - span_top : span K (L : Set E) = ⊤

中文:
类 IsZLattice
  参数: (K : 类型) [NormedField K] {E : 类型} [NormedAddCommGroup E] [NormedSpace K E]
  公理与运算 (1 个):
    - span_top : span K (L : Set E) = ⊤
-/
class IsZLattice (K : Type*) [NormedField K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    (L : Submodule Int E) [DiscreteTopology L] : Prop where
  /-- `L` spans the full space `E` over `K`. -/
  span_top : span K (L : Set E) = ⊤

/--
Instance `instIsZLatticeRealSpan` / 实例 `instIsZLatticeRealSpan`

English:
instance instIsZLatticeRealSpan
  signature: {E ι : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  body: ZSpan.span_top b

中文:
实例 instIsZLatticeRealSpan
  签名: {E ι : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E]
  定义体: ZSpan.span_top b

Depends on / 依赖: ZSpan.span_top, span_top
-/
instance instIsZLatticeRealSpan {E ι : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [Finite ι] (b : Basis ι Real E) :
    IsZLattice Real (span Int (Set.range b)) where
  span_top := ZSpan.span_top b

section NormedLinearOrderedField

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [HasSolidNorm K] [FloorRing K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
variable [ProperSpace E] (L : Submodule Int E) [DiscreteTopology L]

/--
theorem `ZLattice.FG` / 定理 `ZLattice.FG`

English:
theorem ZLattice.FG
  given: [hs : IsZLattice K L]
  statement: L.FG
  proof: by
  obtain ⟨s, ⟨h_incl, ⟨h_span, h_lind⟩⟩⟩ := exists_linearIndependent K (L : Set E)
  -- Let `s` be a maximal `K`-linear independent family of elements of `L`. We show that
  -- `L` is finitely generated (as a ℤ-module) because it fits in the exact sequence
  -- `0 → span ℤ s → L → L ⧸ span ℤ s → 

中文:
定理 ZLattice.FG
  条件: [hs : IsZLattice K L]
  结论: L.FG
  证明: by
  obtain ⟨s, ⟨h_incl, ⟨h_span, h_lind⟩⟩⟩ := exists_linearIndependent K (L : Set E)
  -- Let `s` be a maximal `K`-linear independent family of elements of `L`. We show that
  -- `L` is finitely generated (as a ℤ-module) because it fits in the exact sequence
  -- `0 → span ℤ s → L → L ⧸ span ℤ s → 

Depends on / 依赖: exists_linearIndependent, h_incl, h_lind, h_span
-/
theorem ZLattice.FG [hs : IsZLattice K L] : L.FG := by
  obtain ⟨s, ⟨h_incl, ⟨h_span, h_lind⟩⟩⟩ := exists_linearIndependent K (L : Set E)
  -- Let `s` be a maximal `K`-linear independent family of elements of `L`. We show that
  -- `L` is finitely generated (as a ℤ-module) because it fits in the exact sequence
  -- `0 → span ℤ s → L → L ⧸ span ℤ s → 0` with `span ℤ s` and `L ⧸ span ℤ s` finitely generated.
  refine fg_of_fg_map_of_fg_inf_ker (span Int s).mkQ ?_ ?_
  · -- Let `b` be the `K`-basis of `E` formed by the vectors in `s`. The elements of
    -- `L ⧸ span ℤ s = L ⧸ span ℤ b` are in bijection with elements of `L ∩ fundamentalDomain b`
    -- so there are finitely many since `fundamentalDomain b` is bounded.
    refine fg_def.mpr ⟨map (span Int s).mkQ L, ?_, span_eq _⟩
    let b := Basis.mk h_lind (by
      rw [← hs.span_top]; rw [← h_span]
      exact span_mono (by simp only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, subset_rfl]))
    rw [show span Int s = span Int (Set.range b) by simp [b]; rw [Basis.coe_mk]; rw [Subtype.range_coe_subtype]]
    have : Fintype s := h_lind.setFinite.fintype
    refine Set.Finite.of_finite_image (f := ((↑) : _ -> E) ∘ quotientEquiv b) ?_
      (Function.Injective.injOn (Subtype.coe_injective.comp (quotientEquiv b).injective))
    have : ((fundamentalDomain b) inter L).Finite := by
      change ((fundamentalDomain b) inter L.toAddSubgroup).Finite
      have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
      exact Metric.finite_isBounded_inter_isClosed
        DiscreteTopology.isDiscrete (fundamentalDomain_isBounded b) inferInstance
    refine Set.Finite.subset this ?_
    rintro _ ⟨_, ⟨⟨x, ⟨h_mem, rfl⟩⟩, rfl⟩⟩
    rw [Function.comp_apply]; rw [mkQ_apply]; rw [quotientEquiv_apply_mk]; rw [fractRestrict_apply]
    refine ⟨?_, ?_⟩
    · exact fract_mem_fundamentalDomain b x
    · rw [fract, SetLike.mem_coe, sub_eq_add_neg]
      refine Submodule.add_mem _ h_mem
        (neg_mem (Set.mem_of_subset_of_mem ?_ (Subtype.mem (floor b x))))
      rw [SetLike.coe_subset_coe]; rw [Basis.coe_mk]; rw [Subtype.range_coe_subtype]; rw [Set.ofPred_mem_eq]
      exact span_le.mpr h_incl
  · -- `span ℤ s` is finitely generated because `s` is finite
    rw [ker_mkQ]; rw [inf_of_le_right (span_le.mpr h_incl)]
    exact fg_span (LinearIndependent.setFinite h_lind)

/--
theorem `ZLattice.module_finite` / 定理 `ZLattice.module_finite`

English:
theorem ZLattice.module_finite
  given: [IsZLattice K L]
  statement: Module.Finite Int L
  proof: .of_fg (ZLattice.FG K L)

中文:
定理 ZLattice.module_finite
  条件: [IsZLattice K L]
  结论: Module.Finite 整数 L
  证明: .of_fg (ZLattice.FG K L)

Depends on / 依赖: ZLattice, ZLattice.FG, of_fg
-/
theorem ZLattice.module_finite [IsZLattice K L] : Module.Finite Int L :=
  .of_fg (ZLattice.FG K L)

/--
Instance `instModuleFinite_of_discrete_submodule` / 实例 `instModuleFinite_of_discrete_submodule`

English:
instance instModuleFinite_of_discrete_submodule
  signature: {E : Type*} [NormedAddCommGroup E]
  body: by
  let f := (span Real (L : Set E)).subtype
  let L₀ := L.comap (f.restrictScalars Int)
  have h_img : f '' L₀ = L := by
    rw [← LinearMap.coe_restrictScalars Int f]; rw [← Submodule.map_coe (f.restrictScalars Int)]; rw [Submodule.map_comap_eq_self]
    exact fun x hx => LinearMap.mem_range.mpr 

中文:
实例 instModuleFinite_of_discrete_submodule
  签名: {E : 类型} [NormedAddCommGroup E]
  定义体: by
  let f := (span Real (L : Set E)).subtype
  let L₀ := L.comap (f.restrictScalars Int)
  have h_img : f '' L₀ = L := by
    rw [← LinearMap.coe_restrictScalars Int f]; rw [← Submodule.map_coe (f.restrictScalars Int)]; rw [Submodule.map_comap_eq_self]
    exact fun x hx => LinearMap.mem_range.mpr 

Depends on / 依赖: Finite, L.comap, LinearMap, LinearMap.coe_restrictScalars, LinearMap.mem_range.mpr, Module, Module.Finite, Module.Finite.map, SetLike, SetLike.ext, Submodule, Submodule.map_coe, Submodule.map_comap_eq_self, Submodule.subset_span, _iff, _iff.mpr, coe_restrictScalars, convert, f.restrictScalars, h_img
-/
instance instModuleFinite_of_discrete_submodule {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] (L : Submodule Int E) [DiscreteTopology L] :
    Module.Finite Int L := by
  let f := (span Real (L : Set E)).subtype
  let L₀ := L.comap (f.restrictScalars Int)
  have h_img : f '' L₀ = L := by
    rw [← LinearMap.coe_restrictScalars Int f]; rw [← Submodule.map_coe (f.restrictScalars Int)]; rw [Submodule.map_comap_eq_self]
    exact fun x hx => LinearMap.mem_range.mpr ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩
  suffices Module.Finite Int L₀ by
    have : L₀.map (f.restrictScalars Int) = L :=
      SetLike.ext'_iff.mpr h_img
    convert! this ▸ Module.Finite.map L₀ (f.restrictScalars Int)
  have : DiscreteTopology L₀ := by
    refine DiscreteTopology.preimage_of_continuous_injective (L : Set E) ?_ (injective_subtype _)
    exact LinearMap.continuous_of_finiteDimensional f
  have : IsZLattice Real L₀ := ⟨by
    rw [← (Submodule.map_injective_of_injective (injective_subtype _)).eq_iff]; rw [Submodule.map_span]; rw [Submodule.map_top]; rw [range_subtype]; rw [h_img]⟩
  exact ZLattice.module_finite Real L₀

/--
theorem `ZLattice.module_free` / 定理 `ZLattice.module_free`

English:
theorem ZLattice.module_free
  given: [IsZLattice K L]
  statement: Module.Free Int L
  proof: by
  have : Module.Finite Int L := module_finite K L
  have : Module Rat E := Module.compHom E (algebraMap Rat K)
  have : IsAddTorsionFree E := .of_module_rat _
  infer_instance

中文:
定理 ZLattice.module_free
  条件: [IsZLattice K L]
  结论: Module.Free 整数 L
  证明: by
  have : Module.Finite Int L := module_finite K L
  have : Module Rat E := Module.compHom E (algebraMap Rat K)
  have : IsAddTorsionFree E := .of_module_rat _
  infer_instance

Depends on / 依赖: Finite, IsAddTorsionFree, IsBotZeroClass, Module, Module.Finite, Module.compHom, ZeroLEOneClass, algebraMap, compHom, infer_instance, module_finite, of_module_rat
-/
theorem ZLattice.module_free [IsZLattice K L] : Module.Free Int L := by
  have : Module.Finite Int L := module_finite K L
  have : Module Rat E := Module.compHom E (algebraMap Rat K)
  have : IsAddTorsionFree E := .of_module_rat _
  infer_instance

/--
Instance `instModuleFree_of_discrete_submodule` / 实例 `instModuleFree_of_discrete_submodule`

English:
instance instModuleFree_of_discrete_submodule
  signature: {E : Type*} [NormedAddCommGroup E]
  body: by
  have : Module Rat E := Module.compHom E (algebraMap Rat Real)
  have : IsAddTorsionFree E := .of_module_rat _
  infer_instance

中文:
实例 instModuleFree_of_discrete_submodule
  签名: {E : 类型} [NormedAddCommGroup E]
  定义体: by
  have : Module Rat E := Module.compHom E (algebraMap Rat Real)
  have : IsAddTorsionFree E := .of_module_rat _
  infer_instance

Depends on / 依赖: IsAddTorsionFree, Module, Module.compHom, algebraMap, compHom, infer_instance, of_module_rat
-/
instance instModuleFree_of_discrete_submodule {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] (L : Submodule Int E) [DiscreteTopology L] :
    Module.Free Int L := by
  have : Module Rat E := Module.compHom E (algebraMap Rat Real)
  have : IsAddTorsionFree E := .of_module_rat _
  infer_instance

/--
theorem `ZLattice.rank` / 定理 `ZLattice.rank`

English:
theorem ZLattice.rank
  given: [hs : IsZLattice K L]
  statement: finrank Int L = finrank K E
  proof: by
  classical
  have : Module.Finite Int L := module_finite K L
  have : Module Rat E := Module.compHom E (algebraMap Rat K)
  have : IsAddTorsionFree E := .of_module_rat _
  let b₀ := Module.Free.chooseBasis Int L
  -- Let `b` be a `ℤ`-basis of `L` formed of vectors of `E`
  let b := Subtype.val ∘

中文:
定理 ZLattice.rank
  条件: [hs : IsZLattice K L]
  结论: finrank 整数 L = finrank K E
  证明: by
  classical
  have : Module.Finite Int L := module_finite K L
  have : Module Rat E := Module.compHom E (algebraMap Rat K)
  have : IsAddTorsionFree E := .of_module_rat _
  let b₀ := Module.Free.chooseBasis Int L
  -- Let `b` be a `ℤ`-basis of `L` formed of vectors of `E`
  let b := Subtype.val ∘

Depends on / 依赖: Finite, IsAddTorsionFree, Module, Module.Finite, Module.Free.chooseBasis, Module.compHom, algebraMap, chooseBasis, classical, compHom, module_finite, of_module_rat
-/
theorem ZLattice.rank [hs : IsZLattice K L] : finrank Int L = finrank K E := by
  classical
  have : Module.Finite Int L := module_finite K L
  have : Module Rat E := Module.compHom E (algebraMap Rat K)
  have : IsAddTorsionFree E := .of_module_rat _
  let b₀ := Module.Free.chooseBasis Int L
  -- Let `b` be a `ℤ`-basis of `L` formed of vectors of `E`
  let b := Subtype.val ∘ b₀
  have : LinearIndependent Int b :=
    LinearIndependent.map' b₀.linearIndependent (L.subtype) (ker_subtype _)
  -- We prove some assertions that will be useful later on
  have h_spanL : span Int (Set.range b) = L := by
    convert! congrArg (map (Submodule.subtype L)) b₀.span_eq
    · rw [map_span, Set.range_comp]
      rfl
    · exact (map_subtype_top _).symm
  have h_spanE : span K (Set.range b) = ⊤ := by
    rw [← span_span_of_tower (R := Int)]; rw [h_spanL]
    exact hs.span_top
  have h_card : Fintype.card (Module.Free.ChooseBasisIndex Int L) =
      (Set.range b).toFinset.card := by
    rw [Set.toFinset_range]; rw [Finset.univ.card_image_of_injective]
    · rfl
    · exact Subtype.coe_injective.comp (Basis.injective _)
  rw [finrank_eq_card_chooseBasisIndex]
    -- We prove that `finrank ℤ L ≤ finrank K E` and `finrank K E ≤ finrank ℤ L`
  refine le_antisymm ?_ ?_
  · -- To prove that `finrank ℤ L ≤ finrank K E`, we proceed by contradiction and prove that, in
    -- this case, there is a ℤ-relation between the vectors of `b`
    obtain ⟨t, ⟨ht_inc, ⟨ht_span, ht_lin⟩⟩⟩ := exists_linearIndependent K (Set.range b)
    -- `e` is a `K`-basis of `E` formed of vectors of `b`
    let e : Basis t K E := Basis.mk ht_lin (by simp [ht_span, h_spanE])
    have : Fintype t := Set.Finite.fintype ((Set.range b).toFinite.subset ht_inc)
    have h : LinearIndepOn Int id (Set.range b) := by
      rwa [linearIndepOn_id_range_iff (Subtype.coe_injective.comp b₀.injective)]
    contrapose! h
    -- Since `finrank ℤ L > finrank K E`, there exists a vector `v ∈ b` with `v ∉ e`
    obtain ⟨v, hv⟩ : (Set.range b \ Set.range e).Nonempty := by
      rw [Basis.coe_mk]; rw [Subtype.range_coe_subtype]; rw [Set.ofPred_mem_eq]; rw [← Set.toFinset_nonempty]
      contrapose! h
      rw [Set.toFinset_sdiff]; rw [Finset.sdiff_eq_empty_iff_subset] at h
      replace h := Finset.card_le_card h
      rwa [h_card, ← topEquiv.finrank_eq, ← h_spanE, ← ht_span, finrank_span_set_eq_card ht_lin]
    -- Assume that `e ∪ {v}` is not `ℤ`-linear independent then we get the contradiction
    suffices ¬ LinearIndepOn Int id (insert v (Set.range e)) by
      contrapose this
      refine this.mono ?_
      exact Set.insert_subset (Set.mem_of_mem_sdiff hv) (by simp [e, ht_inc])
    -- We prove finally that `e ∪ {v}` is not ℤ-linear independent or, equivalently,
    -- not ℚ-linear independent by showing that `v ∈ span ℚ e`.
    rw [LinearIndepOn]; rw [LinearIndependent.iff_fractionRing Int Rat]; rw [← LinearIndepOn]; rw [linearIndepOn_id_insert (Set.notMem_of_mem_sdiff hv)]; rw [not_and]; rw [not_not]
    intro _
    -- But that follows from the fact that there exist `n, m : ℕ`, `n ≠ m`
    -- such that `(n - m) • v ∈ span ℤ e` which is true since `n ↦ ZSpan.fract e (n • v)`
    -- takes value into the finite set `fundamentalDomain e ∩ L`
    have h_mapsto : Set.MapsTo (fun n : Int => fract e (n • v)) Set.univ
        (Metric.closedBall 0 (∑ i, ‖e i‖) inter (L : Set E)) := by
      rw [Set.mapsTo_inter]; rw [Set.mapsTo_univ_iff]; rw [Set.mapsTo_univ_iff]
      refine ⟨fun _ => mem_closedBall_zero_iff.mpr (norm_fract_le e _), fun _ => ?_⟩
      · rw [← h_spanL]
        refine sub_mem ?_ ?_
        · exact zsmul_mem (subset_span (Set.sdiff_subset hv)) _
        · exact span_mono (by simp [e, ht_inc]) (coe_mem _)
    have h_finite : Set.Finite (Metric.closedBall 0 (∑ i, ‖e i‖) inter (L : Set E)) := by
      change ((_ : Set E) inter L.toAddSubgroup).Finite
      have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
      exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
        Metric.isBounded_closedBall inferInstance
    obtain ⟨n, -, m, -, h_ne, h_eq⟩ := Set.Infinite.exists_ne_map_eq_of_mapsTo
      Set.infinite_univ h_mapsto h_finite
    have h_nz : (-n + m : Rat) != 0 := by
      rwa [Ne, add_eq_zero_iff_eq_neg.not, neg_inj, Rat.intCast_inj, ← Ne]
    apply (smul_mem_iff _ h_nz).mp
    refine span_subset_span Int Rat _ ?_
    rwa [add_smul, neg_smul, SetLike.mem_coe, ← fract_eq_fract, Int.cast_smul_eq_zsmul Rat,
      Int.cast_smul_eq_zsmul Rat]
  · -- To prove that `finrank K E ≤ finrank ℤ L`, we use the fact `b` generates `E` over `K`
    -- and thus `finrank K E ≤ card b = finrank ℤ L`
    rw [← topEquiv.finrank_eq]; rw [← h_spanE]
    convert! finrank_span_le_card (R := K) (Set.range b)

variable {ι : Type*} [hs : IsZLattice K L] (b : Basis ι Int L)

namespace Module.Basis

/--
Definition of `ofZLatticeBasis` / `ofZLatticeBasis` 的定义

English:
definition ofZLatticeBasis
  signature: : Basis ι K E
  body: by
  have : Module.Finite Int L := ZLattice.module_finite K L
  have : Free Int L := ZLattice.module_free K L
  let e := (Free.chooseBasis Int L).indexEquiv b
  have : Fintype ι := Fintype.ofEquiv _ e
  refine basisOfTopLeSpanOfCardEqFinrank (L.subtype ∘ b) ?_ ?_
  · rw [← span_span_of_tower Int, Se

中文:
定义 ofZLatticeBasis
  签名: : Basis ι K E
  定义体: by
  have : Module.Finite Int L := ZLattice.module_finite K L
  have : Free Int L := ZLattice.module_free K L
  let e := (Free.chooseBasis Int L).indexEquiv b
  have : Fintype ι := Fintype.ofEquiv _ e
  refine basisOfTopLeSpanOfCardEqFinrank (L.subtype ∘ b) ?_ ?_
  · rw [← span_span_of_tower Int, Se

Depends on / 依赖: Basis.span_eq, Finite, Fintype, Fintype.card_congr, Fintype.ofEquiv, Free.chooseBasis, L.subtype, Module, Module.Finite, Set.range_comp, Submodule, Submodule.map_top, ZLattice, ZLattice.module_finite, ZLattice.module_free, ZLattice.rank, basisOfTopLeSpanOfCardEqFinrank, card_congr, chooseBasis, finrank_eq_card_chooseBasisIndex
-/
def ofZLatticeBasis : Basis ι K E := by
  have : Module.Finite Int L := ZLattice.module_finite K L
  have : Free Int L := ZLattice.module_free K L
  let e := (Free.chooseBasis Int L).indexEquiv b
  have : Fintype ι := Fintype.ofEquiv _ e
  refine basisOfTopLeSpanOfCardEqFinrank (L.subtype ∘ b) ?_ ?_
  · rw [← span_span_of_tower Int, Set.range_comp, ← map_span, Basis.span_eq, Submodule.map_top,
      range_subtype, top_le_iff, hs.span_top]
  · rw [← Fintype.card_congr e, ← finrank_eq_card_chooseBasisIndex, ZLattice.rank K L]

@[simp]
/--
theorem `ofZLatticeBasis_apply` / 定理 `ofZLatticeBasis_apply`

English:
theorem ofZLatticeBasis_apply
  given: (i : ι)
  statement: b.ofZLatticeBasis K L i = b i
  proof: by
  simp [Basis.ofZLatticeBasis]

@[simp]

中文:
定理 ofZLatticeBasis_apply
  条件: (i : ι)
  结论: b.ofZLatticeBasis K L i = b i
  证明: by
  simp [Basis.ofZLatticeBasis]

@[simp]

Depends on / 依赖: Basis.ofZLatticeBasis, ofZLatticeBasis
-/
theorem ofZLatticeBasis_apply (i : ι) : b.ofZLatticeBasis K L i = b i := by
  simp [Basis.ofZLatticeBasis]

@[simp]
/--
theorem `ofZLatticeBasis_repr_apply` / 定理 `ofZLatticeBasis_repr_apply`

English:
theorem ofZLatticeBasis_repr_apply
  given: (x : L) (i : ι)
  proof: by
  suffices ((b.ofZLatticeBasis K L).repr.toLinearMap.restrictScalars Int) ∘ₗ L.subtype
      = Finsupp.mapRange.linearMap (Algebra.linearMap Int K) ∘ₗ b.repr.toLinearMap by
    exact DFunLike.congr_fun (LinearMap.congr_fun this x) i
  refine Basis.ext b fun i => ?_
  simp_rw [LinearMap.coe_comp, 

中文:
定理 ofZLatticeBasis_repr_apply
  条件: (x : L) (i : ι)
  证明: by
  suffices ((b.ofZLatticeBasis K L).repr.toLinearMap.restrictScalars Int) ∘ₗ L.subtype
      = Finsupp.mapRange.linearMap (Algebra.linearMap Int K) ∘ₗ b.repr.toLinearMap by
    exact DFunLike.congr_fun (LinearMap.congr_fun this x) i
  refine Basis.ext b fun i => ?_
  simp_rw [LinearMap.coe_comp, 

Depends on / 依赖: Algebra, Algebra.linearMap, Algebra.linearMap_apply, Basis.ext, DFunLike, DFunLike.congr_fun, Finsupp, Finsupp.mapRange.linearMap, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Function, Function.comp_apply, L.subtype, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearMap.congr_fun, b.ofZLatticeBasis
-/
theorem ofZLatticeBasis_repr_apply (x : L) (i : ι) :
    (b.ofZLatticeBasis K L).repr x i = b.repr x i := by
  suffices ((b.ofZLatticeBasis K L).repr.toLinearMap.restrictScalars Int) ∘ₗ L.subtype
      = Finsupp.mapRange.linearMap (Algebra.linearMap Int K) ∘ₗ b.repr.toLinearMap by
    exact DFunLike.congr_fun (LinearMap.congr_fun this x) i
  refine Basis.ext b fun i => ?_
  simp_rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, coe_subtype, ← b.ofZLatticeBasis_apply K, repr_self,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Algebra.linearMap_apply, map_one]

/--
theorem `ofZLatticeBasis_span` / 定理 `ofZLatticeBasis_span`

English:
theorem ofZLatticeBasis_span
  statement: span Int (Set.range (b.ofZLatticeBasis K)) = L
  proof: by
  calc span Int (Set.range (b.ofZLatticeBasis K))
    _ = span Int (L.subtype '' Set.range b) := by congr; ext; simp
    _ = map L.subtype (span Int (Set.range b)) := by rw [Submodule.map_span]
    _ = L := by simp [b.span_eq]

中文:
定理 ofZLatticeBasis_span
  结论: span 整数 (Set.range (b.ofZLatticeBasis K)) = L
  证明: by
  calc span Int (Set.range (b.ofZLatticeBasis K))
    _ = span Int (L.subtype '' Set.range b) := by congr; ext; simp
    _ = map L.subtype (span Int (Set.range b)) := by rw [Submodule.map_span]
    _ = L := by simp [b.span_eq]

Depends on / 依赖: L.subtype, Set.range, Submodule, Submodule.map_span, b.ofZLatticeBasis, b.span_eq, map_span, ofZLatticeBasis, span_eq, subtype
-/
theorem ofZLatticeBasis_span : span Int (Set.range (b.ofZLatticeBasis K)) = L := by
  calc span Int (Set.range (b.ofZLatticeBasis K))
    _ = span Int (L.subtype '' Set.range b) := by congr; ext; simp
    _ = map L.subtype (span Int (Set.range b)) := by rw [Submodule.map_span]
    _ = L := by simp [b.span_eq]

end Module.Basis

open MeasureTheory in
/--
theorem `ZLattice.isAddFundamentalDomain` / 定理 `ZLattice.isAddFundamentalDomain`

English:
theorem ZLattice.isAddFundamentalDomain
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  convert! ZSpan.isAddFundamentalDomain (b.ofZLatticeBasis Real) μ
  all_goals exact (b.ofZLatticeBasis_span Real).symm

中文:
定理 ZLattice.isAddFundamentalDomain
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E]
  证明: by
  convert! ZSpan.isAddFundamentalDomain (b.ofZLatticeBasis Real) μ
  all_goals exact (b.ofZLatticeBasis_span Real).symm

Depends on / 依赖: ZSpan.isAddFundamentalDomain, all_goals, b.ofZLatticeBasis, b.ofZLatticeBasis_span, convert, isAddFundamentalDomain, ofZLatticeBasis, ofZLatticeBasis_span
-/
theorem ZLattice.isAddFundamentalDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] {L : Submodule Int E} [DiscreteTopology L] [IsZLattice Real L] [Finite ι]
    (b : Basis ι Int L) [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E) :
    IsAddFundamentalDomain L (fundamentalDomain (b.ofZLatticeBasis Real)) μ := by
  convert! ZSpan.isAddFundamentalDomain (b.ofZLatticeBasis Real) μ
  all_goals exact (b.ofZLatticeBasis_span Real).symm

/--
Instance `instCountable_of_discrete_submodule` / 实例 `instCountable_of_discrete_submodule`

English:
instance instCountable_of_discrete_submodule
  signature: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  body: by
  simp_rw [← (Module.Free.chooseBasis Int L).ofZLatticeBasis_span Real]
  infer_instance

中文:
实例 instCountable_of_discrete_submodule
  签名: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E]
  定义体: by
  simp_rw [← (Module.Free.chooseBasis Int L).ofZLatticeBasis_span Real]
  infer_instance

Depends on / 依赖: Module, Module.Free.chooseBasis, chooseBasis, infer_instance, ofZLatticeBasis_span, simp_rw
-/
instance instCountable_of_discrete_submodule {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] (L : Submodule Int E) [DiscreteTopology L] [IsZLattice Real L] :
    Countable L := by
  simp_rw [← (Module.Free.chooseBasis Int L).ofZLatticeBasis_span Real]
  infer_instance

/--
theorem `Real.finrank_eq_int_finrank_of_discrete` / 定理 `Real.finrank_eq_int_finrank_of_discrete`

English:
theorem Real.finrank_eq_int_finrank_of_discrete
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  let F := span Real s
  let L : Submodule Int (span Real s) := comap (F.restrictScalars Int).subtype (span Int s)
  let f := Submodule.comapSubtypeEquivOfLe (span_le_restrictScalars Int Real s)
  have : DiscreteTopology L := by
    let e : span Int s ≃L[Int] L :=
      ⟨f.symm, continuous_of_dis

中文:
定理 Real.finrank_eq_int_finrank_of_discrete
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E]
  证明: by
  let F := span Real s
  let L : Submodule Int (span Real s) := comap (F.restrictScalars Int).subtype (span Int s)
  let f := Submodule.comapSubtypeEquivOfLe (span_le_restrictScalars Int Real s)
  have : DiscreteTopology L := by
    let e : span Int s ≃L[Int] L :=
      ⟨f.symm, continuous_of_dis

Depends on / 依赖: DiscreteTopology, F.restrictScalars, IsZLattice, Isometry, Isometry.continuous, Set.preimage_mono, Submodule, Submodule.comapSubtypeEquivOfLe, comapSubtypeEquivOfLe, continuous, continuous_of_discreteTopology, discreteTopology, e.toHomeomorph.discreteTopology, eq_top_iff, eq_top_iff.mpr, f.symm, preimage_mono, restrictScalars, span_le_restrictScalars, span_mono
-/
theorem Real.finrank_eq_int_finrank_of_discrete {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] {s : Set E} (hs : DiscreteTopology (span Int s)) :
    Set.finrank Real s = Set.finrank Int s := by
  let F := span Real s
  let L : Submodule Int (span Real s) := comap (F.restrictScalars Int).subtype (span Int s)
  let f := Submodule.comapSubtypeEquivOfLe (span_le_restrictScalars Int Real s)
  have : DiscreteTopology L := by
    let e : span Int s ≃L[Int] L :=
      ⟨f.symm, continuous_of_discreteTopology, Isometry.continuous fun _ => congrFun rfl⟩
    exact e.toHomeomorph.discreteTopology
have : IsZLattice Real L := ⟨eq_top_iff.mpr
    span_span_coe_preimage.symm.le.trans (span_mono (Set.preimage_mono subset_span))⟩
  rw [Set.finrank]; rw [Set.finrank]; rw [← f.finrank_eq]
  exact (ZLattice.rank Real L).symm

end NormedLinearOrderedField

section Basis

variable {ι : Type*} [Fintype ι] (L : Submodule Int (ι -> Real)) [DiscreteTopology L] [IsZLattice Real L]

/--
Definition of `IsZLattice.basis` / `IsZLattice.basis` 的定义

English:
definition IsZLattice.basis
  signature: : Basis ι Int L
  body: (Free.chooseBasis Int L).reindex (Fintype.equivOfCardEq
    (by rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank Real, finrank_fintype_fun_eq_card]))

中文:
定义 IsZLattice.basis
  签名: : Basis ι 整数 L
  定义体: (Free.chooseBasis Int L).reindex (Fintype.equivOfCardEq
    (by rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank Real, finrank_fintype_fun_eq_card]))

Depends on / 依赖: Fintype, Fintype.equivOfCardEq, Free.chooseBasis, ZLattice, ZLattice.rank, chooseBasis, equivOfCardEq, finrank_eq_card_chooseBasisIndex, finrank_fintype_fun_eq_card, reindex
-/
def IsZLattice.basis : Basis ι Int L :=
  (Free.chooseBasis Int L).reindex (Fintype.equivOfCardEq
    (by rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank Real, finrank_fintype_fun_eq_card]))

end Basis

section comap

variable (K : Type*) [NormedField K] {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule Int E)

/--
Definition of `ZLattice.comap` / `ZLattice.comap` 的定义

English:
definition ZLattice.comap
  signature: (e : F ->ₗ[K] E)
  body: L.comap (e.restrictScalars Int)

@[simp]

中文:
定义 ZLattice.comap
  签名: (e : F ->ₗ[K] E)
  定义体: L.comap (e.restrictScalars Int)

@[simp]
-/
protected def ZLattice.comap (e : F ->ₗ[K] E) := L.comap (e.restrictScalars Int)

@[simp]
/--
theorem `ZLattice.coe_comap` / 定理 `ZLattice.coe_comap`

English:
theorem ZLattice.coe_comap
  given: (e : F ->ₗ[K] E)
  proof: rfl

中文:
定理 ZLattice.coe_comap
  条件: (e : F ->ₗ[K] E)
  证明: rfl
-/
theorem ZLattice.coe_comap (e : F ->ₗ[K] E) :
    (ZLattice.comap K L e : Set F) = e ⁻¹' L := rfl

/--
theorem `ZLattice.comap_refl` / 定理 `ZLattice.comap_refl`

English:
theorem ZLattice.comap_refl
  proof: Submodule.comap_id L

中文:
定理 ZLattice.comap_refl
  证明: Submodule.comap_id L

Depends on / 依赖: Submodule, Submodule.comap_id, comap_id
-/
theorem ZLattice.comap_refl :
    ZLattice.comap K L (1 : E ->ₗ[K] E) = L := Submodule.comap_id L

/--
theorem `ZLattice.comap_discreteTopology` / 定理 `ZLattice.comap_discreteTopology`

English:
theorem ZLattice.comap_discreteTopology
  statement: [hL : DiscreteTopology L] {e : F ->ₗ[K] E}
  proof: by
  exact DiscreteTopology.preimage_of_continuous_injective L he₁ he₂

中文:
定理 ZLattice.comap_discreteTopology
  结论: [hL : DiscreteTopology L] {e : F ->ₗ[K] E}
  证明: by
  exact DiscreteTopology.preimage_of_continuous_injective L he₁ he₂

Depends on / 依赖: DiscreteTopology, DiscreteTopology.preimage_of_continuous_injective, preimage_of_continuous_injective
-/
theorem ZLattice.comap_discreteTopology [hL : DiscreteTopology L] {e : F ->ₗ[K] E}
    (he₁ : Continuous e) (he₂ : Function.Injective e) :
    DiscreteTopology (ZLattice.comap K L e) := by
  exact DiscreteTopology.preimage_of_continuous_injective L he₁ he₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DiscreteTopology
  signature: L] (e
  body: ZLattice.comap_discreteTopology K L e.continuous e.injective

中文:
实例 [DiscreteTopology
  签名: L] (e
  定义体: ZLattice.comap_discreteTopology K L e.continuous e.injective

Depends on / 依赖: ZLattice, ZLattice.comap_discreteTopology, comap_discreteTopology, continuous, e.continuous, e.injective, injective
-/
instance [DiscreteTopology L] (e : F ≃L[K] E) :
    DiscreteTopology (ZLattice.comap K L e.toLinearMap) :=
  ZLattice.comap_discreteTopology K L e.continuous e.injective

/--
theorem `ZLattice.comap_span_top` / 定理 `ZLattice.comap_span_top`

English:
theorem ZLattice.comap_span_top
  statement: (hL : span K (L : Set E) = ⊤) {e : F ->ₗ[K] E}
  proof: by
  rw [ZLattice.coe_comap]; rw [Submodule.span_preimage_eq (Submodule.nonempty L) he]; rw [hL]; rw [comap_top]

中文:
定理 ZLattice.comap_span_top
  结论: (hL : span K (L : Set E) = ⊤) {e : F ->ₗ[K] E}
  证明: by
  rw [ZLattice.coe_comap]; rw [Submodule.span_preimage_eq (Submodule.nonempty L) he]; rw [hL]; rw [comap_top]

Depends on / 依赖: Submodule, Submodule.nonempty, Submodule.span_preimage_eq, ZLattice, ZLattice.coe_comap, coe_comap, comap_top, nonempty, span_preimage_eq
-/
theorem ZLattice.comap_span_top (hL : span K (L : Set E) = ⊤) {e : F ->ₗ[K] E}
    (he : (L : Set E) subseteq LinearMap.range e) :
    span K (ZLattice.comap K L e : Set F) = ⊤ := by
  rw [ZLattice.coe_comap]; rw [Submodule.span_preimage_eq (Submodule.nonempty L) he]; rw [hL]; rw [comap_top]

/--
Instance `instIsZLatticeComap` / 实例 `instIsZLatticeComap`

English:
instance instIsZLatticeComap
  signature: [DiscreteTopology L] [IsZLattice K L] (e : F ≃L[K] E)
  body: by
    rw [ZLattice.coe_comap]; rw [LinearEquiv.coe_coe]; rw [e.coe_toLinearEquiv]; rw [← e.image_symm_eq_preimage]; rw [← ContinuousLinearEquiv.coe_toLinearEquiv]; rw [← LinearEquiv.coe_coe]; rw [← Submodule.map_span]; rw [IsZLattice.span_top]; rw [Submodule.map_top]; rw [e.symm.range]

@[simp]

中文:
实例 instIsZLatticeComap
  签名: [DiscreteTopology L] [IsZLattice K L] (e : F ≃L[K] E)
  定义体: by
    rw [ZLattice.coe_comap]; rw [LinearEquiv.coe_coe]; rw [e.coe_toLinearEquiv]; rw [← e.image_symm_eq_preimage]; rw [← ContinuousLinearEquiv.coe_toLinearEquiv]; rw [← LinearEquiv.coe_coe]; rw [← Submodule.map_span]; rw [IsZLattice.span_top]; rw [Submodule.map_top]; rw [e.symm.range]

@[simp]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_toLinearEquiv, IsBotZeroClass, IsZLattice, IsZLattice.span_top, LinearEquiv, LinearEquiv.coe_coe, Preorder, Submodule, Submodule.map_span, Submodule.map_top, ZLattice, ZLattice.coe_comap, coe_coe, coe_comap, coe_toLinearEquiv, e.coe_toLinearEquiv, e.image_symm_eq_preimage, e.symm.range, image_symm_eq_preimage
-/
instance instIsZLatticeComap [DiscreteTopology L] [IsZLattice K L] (e : F ≃L[K] E) :
    IsZLattice K (ZLattice.comap K L e.toLinearMap) where
  span_top := by
    rw [ZLattice.coe_comap]; rw [LinearEquiv.coe_coe]; rw [e.coe_toLinearEquiv]; rw [← e.image_symm_eq_preimage]; rw [← ContinuousLinearEquiv.coe_toLinearEquiv]; rw [← LinearEquiv.coe_coe]; rw [← Submodule.map_span]; rw [IsZLattice.span_top]; rw [Submodule.map_top]; rw [e.symm.range]

@[simp]
/--
theorem `ZLattice.comap_toAddSubgroup` / 定理 `ZLattice.comap_toAddSubgroup`

English:
theorem ZLattice.comap_toAddSubgroup
  given: (e : F ->ₗ[K] E)
  proof: rfl

中文:
定理 ZLattice.comap_toAddSubgroup
  条件: (e : F ->ₗ[K] E)
  证明: rfl
-/
theorem ZLattice.comap_toAddSubgroup (e : F ->ₗ[K] E) :
    (ZLattice.comap K L e).toAddSubgroup = L.toAddSubgroup.comap e.toAddMonoidHom := rfl

/--
theorem `ZLattice.comap_comp` / 定理 `ZLattice.comap_comp`

English:
theorem ZLattice.comap_comp
  statement: {G : Type*} [NormedAddCommGroup G] [NormedSpace K G]
  proof: (Submodule.comap_comp _ _ L).symm

中文:
定理 ZLattice.comap_comp
  结论: {G : 类型} [NormedAddCommGroup G] [NormedSpace K G]
  证明: (Submodule.comap_comp _ _ L).symm

Depends on / 依赖: Submodule, Submodule.comap_comp, comap_comp
-/
theorem ZLattice.comap_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace K G]
    (e : F ->ₗ[K] E) (e' : G ->ₗ[K] F) :
    (ZLattice.comap K (ZLattice.comap K L e) e') = ZLattice.comap K L (e ∘ₗ e') :=
  (Submodule.comap_comp _ _ L).symm

/--
Definition of `ZLattice.comap_equiv` / `ZLattice.comap_equiv` 的定义

English:
definition ZLattice.comap_equiv
  signature: (e : F ≃ₗ[K] E)
  body: LinearEquiv.ofBijective
    ((e.symm.toLinearMap.restrictScalars Int).restrict
      (fun _ h => by simpa [← SetLike.mem_coe] using h))
    ⟨fun _ _ h => Subtype.ext_iff.mpr (e.symm.injective (congr_arg Subtype.val h)),
    fun ⟨x, hx⟩ => ⟨⟨e x, by rwa [← SetLike.mem_coe, ZLattice.coe_comap] at hx⟩,

中文:
定义 ZLattice.comap_equiv
  签名: (e : F ≃ₗ[K] E)
  定义体: LinearEquiv.ofBijective
    ((e.symm.toLinearMap.restrictScalars Int).restrict
      (fun _ h => by simpa [← SetLike.mem_coe] using h))
    ⟨fun _ _ h => Subtype.ext_iff.mpr (e.symm.injective (congr_arg Subtype.val h)),
    fun ⟨x, hx⟩ => ⟨⟨e x, by rwa [← SetLike.mem_coe, ZLattice.coe_comap] at hx⟩,

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, SetLike, SetLike.mem_coe, Subtype, Subtype.ext_iff, Subtype.ext_iff.mpr, Subtype.val, ZLattice, ZLattice.coe_comap, coe_comap, congr_arg, e.symm.injective, e.symm.toLinearMap.restrictScalars, ext_iff, injective, mem_coe, ofBijective, restrict, restrictScalars
-/
def ZLattice.comap_equiv (e : F ≃ₗ[K] E) :
    L ≃ₗ[Int] (ZLattice.comap K L e.toLinearMap) :=
  LinearEquiv.ofBijective
    ((e.symm.toLinearMap.restrictScalars Int).restrict
      (fun _ h => by simpa [← SetLike.mem_coe] using h))
    ⟨fun _ _ h => Subtype.ext_iff.mpr (e.symm.injective (congr_arg Subtype.val h)),
    fun ⟨x, hx⟩ => ⟨⟨e x, by rwa [← SetLike.mem_coe, ZLattice.coe_comap] at hx⟩,
      by simp [Subtype.ext_iff]⟩⟩

@[simp]
/--
theorem `ZLattice.comap_equiv_apply` / 定理 `ZLattice.comap_equiv_apply`

English:
theorem ZLattice.comap_equiv_apply
  given: (e : F ≃ₗ[K] E) (x : L)
  proof: rfl

中文:
定理 ZLattice.comap_equiv_apply
  条件: (e : F ≃ₗ[K] E) (x : L)
  证明: rfl
-/
theorem ZLattice.comap_equiv_apply (e : F ≃ₗ[K] E) (x : L) :
    ZLattice.comap_equiv K L e x = e.symm x := rfl

namespace Module.Basis

/--
Definition of `ofZLatticeComap` / `ofZLatticeComap` 的定义

English:
definition ofZLatticeComap
  signature: (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι Int L)
  body: b.map (ZLattice.comap_equiv K L e)

@[simp]

中文:
定义 ofZLatticeComap
  签名: (e : F ≃ₗ[K] E) {ι : 类型} (b : Basis ι 整数 L)
  定义体: b.map (ZLattice.comap_equiv K L e)

@[simp]

Depends on / 依赖: ZLattice, ZLattice.comap_equiv, b.map, comap_equiv
-/
def ofZLatticeComap (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι Int L) :
    Basis ι Int (ZLattice.comap K L e.toLinearMap) := b.map (ZLattice.comap_equiv K L e)

@[simp]
/--
theorem `ofZLatticeComap_apply` / 定理 `ofZLatticeComap_apply`

English:
theorem ofZLatticeComap_apply
  given: (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι Int L) (i : ι)
  proof: by simp [Basis.ofZLatticeComap]

@[simp]

中文:
定理 ofZLatticeComap_apply
  条件: (e : F ≃ₗ[K] E) {ι : 类型} (b : Basis ι 整数 L) (i : ι)
  证明: by simp [Basis.ofZLatticeComap]

@[simp]

Depends on / 依赖: Basis.ofZLatticeComap, ofZLatticeComap
-/
theorem ofZLatticeComap_apply (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι Int L) (i : ι) :
    b.ofZLatticeComap K L e i = e.symm (b i) := by simp [Basis.ofZLatticeComap]

@[simp]
/--
theorem `ofZLatticeComap_repr_apply` / 定理 `ofZLatticeComap_repr_apply`

English:
theorem ofZLatticeComap_repr_apply
  given: (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι Int L) (x : L) (i : ι)
  proof: by
  simp [Basis.ofZLatticeComap]

中文:
定理 ofZLatticeComap_repr_apply
  条件: (e : F ≃ₗ[K] E) {ι : 类型} (b : Basis ι 整数 L) (x : L) (i : ι)
  证明: by
  simp [Basis.ofZLatticeComap]

Depends on / 依赖: Basis.ofZLatticeComap, ofZLatticeComap
-/
theorem ofZLatticeComap_repr_apply (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι Int L) (x : L) (i : ι) :
    (b.ofZLatticeComap K L e).repr (ZLattice.comap_equiv K L e x) i = b.repr x i := by
  simp [Basis.ofZLatticeComap]

end Module.Basis
end comap

section NormedLinearOrderedField_comap

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K] [HasSolidNorm K]
  [FloorRing K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
  [ProperSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F] [FiniteDimensional K F]
  [ProperSpace F]
variable (L : Submodule Int E) [DiscreteTopology L] [IsZLattice K L]

/--
theorem `Module.Basis.ofZLatticeBasis_comap` / 定理 `Module.Basis.ofZLatticeBasis_comap`

English:
theorem Module.Basis.ofZLatticeBasis_comap
  given: (e : F ≃L[K] E) {ι : Type*} (b : Basis ι Int L)
  proof: by
  ext
  simp

中文:
定理 Module.Basis.ofZLatticeBasis_comap
  条件: (e : F ≃L[K] E) {ι : 类型} (b : Basis ι 整数 L)
  证明: by
  ext
  simp
-/
theorem Module.Basis.ofZLatticeBasis_comap (e : F ≃L[K] E) {ι : Type*} (b : Basis ι Int L) :
    (b.ofZLatticeComap K L e.toLinearEquiv).ofZLatticeBasis K (ZLattice.comap K L e.toLinearMap) =
    (b.ofZLatticeBasis K L).map e.symm.toLinearEquiv := by
  ext
  simp

end NormedLinearOrderedField_comap

/--
lemma `IsZLattice.isCompact_range_of_periodic` / 引理 `IsZLattice.isCompact_range_of_periodic`

English:
lemma IsZLattice.isCompact_range_of_periodic
  proof: by
  have := ZLattice.module_free Real L
  let b := Module.Free.chooseBasis Int L
  convert! (b.ofZLatticeBasis Real).parallelepiped.isCompact.image hf
  refine le_antisymm ?_ (Set.image_subset_range _ _)
  rintro _ ⟨x, rfl⟩
  let x' : L := b.repr.symm (Finsupp.equivFunOnFinite.symm
    fun i => ⌊(b

中文:
引理 IsZLattice.isCompact_range_of_periodic
  证明: by
  have := ZLattice.module_free Real L
  let b := Module.Free.chooseBasis Int L
  convert! (b.ofZLatticeBasis Real).parallelepiped.isCompact.image hf
  refine le_antisymm ?_ (Set.image_subset_range _ _)
  rintro _ ⟨x, rfl⟩
  let x' : L := b.repr.symm (Finsupp.equivFunOnFinite.symm
    fun i => ⌊(b

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite.symm, Int.floor_le, Int.lt_floor_add_one, Module, Module.Free.chooseBasis, Set.image_subset_range, ZLattice, ZLattice.module_free, add_comm, b.ofZLatticeBasis, b.repr.symm, chooseBasis, convert, equivFunOnFinite, floor_le, image_subset_range, isCompact, le_antisymm, le_of_lt
-/
lemma IsZLattice.isCompact_range_of_periodic
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
    [TopologicalSpace F]
    (L : Submodule Int E) [DiscreteTopology L] [IsZLattice Real L] (f : E -> F) (hf : Continuous f)
    (hf' : forall z w, w in L -> f (z + w) = f z) : IsCompact (Set.range f) := by
  have := ZLattice.module_free Real L
  let b := Module.Free.chooseBasis Int L
  convert! (b.ofZLatticeBasis Real).parallelepiped.isCompact.image hf
  refine le_antisymm ?_ (Set.image_subset_range _ _)
  rintro _ ⟨x, rfl⟩
  let x' : L := b.repr.symm (Finsupp.equivFunOnFinite.symm
    fun i => ⌊(b.ofZLatticeBasis Real).repr x i⌋)
  refine ⟨x + (- x'), ?_, hf' _ _ (- x').2⟩
  simp [parallelepiped_basis_eq, x', Int.floor_le, Int.lt_floor_add_one, le_of_lt, add_comm (1 : Real)]

end ZLattice
