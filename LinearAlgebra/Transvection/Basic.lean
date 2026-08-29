/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Transvections in a module

* When `f : Module.Dual R V` and `v : V`,
  `LinearMap.transvection f v` is the linear map given by `x ↦ x + f x • v`,

* `LinearMap.transvection.det` shows that the determinant of
  `LinearMap.transvection f v` is equal to `1 + f v`.

* If, moreover, `f v = 0`, then `LinearEquiv.transvection` shows that it is
  a linear equivalence.

* `LinearMap.transvections R V`: the set of transvections.

* `LinearEquiv.dilatransvections R V`: the set of linear equivalences
  whose associated linear map is of the form `LinearMap.transvection f v`.

* `LinearEquiv.transvection.det` shows that it has determinant `1`.

## Note on terminology

In the mathematical literature, linear maps of the form `LinearMap.transvection f v`
are only called “transvections” when `f v = 0`. Otherwise, they are sometimes
called “dilations” (especially if `f v ≠ -1`).

The definition is almost the same as that of `Module.preReflection f v`,
up to a sign change, which are interesting when `f v = 2`, because they give “reflections”.

-/

@[expose] public section

namespace LinearMap

open Module

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

/--
Definition of `transvection` / `transvection` 的定义

English:
definition transvection
  signature: (f : Dual R V) (v : V)
  body: x + f x • v
  map_add' x y := by simp [add_add_add_comm, add_smul]
  map_smul' r x := by simp [smul_eq_mul, smul_add, mul_smul]

中文:
定义 transvection
  签名: (f : 对偶 R V) (v : V)
  定义体: x + f x • v
  map_add' x y := by simp [add_add_add_comm, add_smul]
  map_smul' r x := by simp [smul_eq_mul, smul_add, mul_smul]
-/
def transvection (f : Dual R V) (v : V) : V ->ₗ[R] V where
  toFun x := x + f x • v
  map_add' x y := by simp [add_add_add_comm, add_smul]
  map_smul' r x := by simp [smul_eq_mul, smul_add, mul_smul]

namespace transvection

open Submodule LinearMap

/--
theorem `apply` / 定理 `apply`

English:
theorem apply
  given: (f : Dual R V) (v x : V)
  proof: rfl

中文:
定理 apply
  条件: (f : 对偶 R V) (v x : V)
  证明: rfl
-/
theorem apply (f : Dual R V) (v x : V) :
    transvection f v x = x + f x • v :=
  rfl

/--
theorem `comp_of_left_eq_apply` / 定理 `comp_of_left_eq_apply`

English:
theorem comp_of_left_eq_apply
  given: {f : Dual R V} {v w : V} {x : V} (hw : f w = 0)
  proof: by
  simp [transvection, map_add, hw, add_assoc]

中文:
定理 comp_of_left_eq_apply
  条件: {f : 对偶 R V} {v w : V} {x : V} (hw : f w = 0)
  证明: by
  simp [transvection, map_add, hw, add_assoc]

Depends on / 依赖: add_assoc, map_add, transvection
-/
theorem comp_of_left_eq_apply {f : Dual R V} {v w : V} {x : V} (hw : f w = 0) :
    transvection f v (transvection f w x) = transvection f (v + w) x := by
  simp [transvection, map_add, hw, add_assoc]

/--
theorem `comp_of_left_eq` / 定理 `comp_of_left_eq`

English:
theorem comp_of_left_eq
  given: {f : Dual R V} {v w : V} (hw : f w = 0)
  proof: by
  ext; simp [comp_of_left_eq_apply hw]

中文:
定理 comp_of_left_eq
  条件: {f : 对偶 R V} {v w : V} (hw : f w = 0)
  证明: by
  ext; simp [comp_of_left_eq_apply hw]

Depends on / 依赖: comp_of_left_eq_apply
-/
theorem comp_of_left_eq {f : Dual R V} {v w : V} (hw : f w = 0) :
    (transvection f v) ∘ₗ (transvection f w) = transvection f (v + w) := by
  ext; simp [comp_of_left_eq_apply hw]

/--
theorem `comp_of_right_eq_apply` / 定理 `comp_of_right_eq_apply`

English:
theorem comp_of_right_eq_apply
  given: {f g : Dual R V} {v : V} {x : V} (hf : f v = 0)
  proof: by
  simp [transvection, map_add, hf, add_smul, add_assoc]

中文:
定理 comp_of_right_eq_apply
  条件: {f g : 对偶 R V} {v : V} {x : V} (hf : f v = 0)
  证明: by
  simp [transvection, map_add, hf, add_smul, add_assoc]

Depends on / 依赖: add_assoc, add_smul, map_add, transvection
-/
theorem comp_of_right_eq_apply {f g : Dual R V} {v : V} {x : V} (hf : f v = 0) :
    (transvection f v) (transvection g v x) = transvection (f + g) v x := by
  simp [transvection, map_add, hf, add_smul, add_assoc]

/--
theorem `comp_of_right_eq` / 定理 `comp_of_right_eq`

English:
theorem comp_of_right_eq
  given: {f g : Dual R V} {v : V} (hf : f v = 0)
  proof: by
  ext; simp [comp_of_right_eq_apply hf]

@[simp]

中文:
定理 comp_of_right_eq
  条件: {f g : 对偶 R V} {v : V} (hf : f v = 0)
  证明: by
  ext; simp [comp_of_right_eq_apply hf]

@[simp]

Depends on / 依赖: comp_of_right_eq_apply
-/
theorem comp_of_right_eq {f g : Dual R V} {v : V} (hf : f v = 0) :
    (transvection f v) ∘ₗ (transvection g v) = transvection (f + g) v := by
  ext; simp [comp_of_right_eq_apply hf]

@[simp]
/--
theorem `of_left_eq_zero` / 定理 `of_left_eq_zero`

English:
theorem of_left_eq_zero
  given: (v : V)
  proof: by
  ext
  simp [transvection]

@[simp]

中文:
定理 of_left_eq_zero
  条件: (v : V)
  证明: by
  ext
  simp [transvection]

@[simp]

Depends on / 依赖: transvection
-/
theorem of_left_eq_zero (v : V) :
    transvection (0 : Dual R V) v = id := by
  ext
  simp [transvection]

@[simp]
/--
theorem `of_right_eq_zero` / 定理 `of_right_eq_zero`

English:
theorem of_right_eq_zero
  given: (f : Dual R V)
  proof: by
  ext
  simp [transvection]

中文:
定理 of_right_eq_zero
  条件: (f : 对偶 R V)
  证明: by
  ext
  simp [transvection]

Depends on / 依赖: transvection
-/
theorem of_right_eq_zero (f : Dual R V) :
    transvection f 0 = id := by
  ext
  simp [transvection]

/--
theorem `comp_smul_smul` / 定理 `comp_smul_smul`

English:
theorem comp_smul_smul
  given: {f : Dual R V} {v : V} {r s : R}
  proof: by
  ext x
  simp only [LinearMap.comp_apply, apply, map_add, map_smul, add_assoc]
  simp only [smul_add, ← mul_smul, ← add_smul, ← mul_add (f x), mul_assoc]

中文:
定理 comp_smul_smul
  条件: {f : 对偶 R V} {v : V} {r s : R}
  证明: by
  ext x
  simp only [LinearMap.comp_apply, apply, map_add, map_smul, add_assoc]
  simp only [smul_add, ← mul_smul, ← add_smul, ← mul_add (f x), mul_assoc]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, add_assoc, add_smul, comp_apply, map_add, map_smul, mul_add, mul_assoc, mul_smul, smul_add
-/
theorem comp_smul_smul {f : Dual R V} {v : V} {r s : R} :
    transvection f (r • v) ∘ₗ transvection f (s • v) =
      transvection f ((r + s + s * f v * r) • v) := by
  ext x
  simp only [LinearMap.comp_apply, apply, map_add, map_smul, add_assoc]
  simp only [smul_add, ← mul_smul, ← add_smul, ← mul_add (f x), mul_assoc]

/--
theorem `eq_id_of_finrank_le_one` / 定理 `eq_id_of_finrank_le_one`

English:
theorem eq_id_of_finrank_le_one
  proof: by
  interval_cases h : finrank R V
  · have : Subsingleton V := (finrank_eq_zero_iff_of_free R V).mp h
    simp [Subsingleton.eq_zero v]
  · let b := finBasis R V
    ext x
    suffices f x • v = 0 by
      simp [apply, this]
    let i : Fin (finrank R V) := ⟨0, by simp [h]⟩
    suffices forall x, x = b.repr x i • (b i) by
      rw [this v]; rw [map_smul]; rw [smul_eq_mul]; rw [mul_comm] at hfv
      rw [this x]; rw [this v]; rw [map_smul]; rw [smul_eq_mul]; rw [← mul_smul]; rw [mul_assoc]; rw [hfv]; rw [mul_zero]; rw [zero_smul]
    intro x
    have : x = ∑ i, b.repr x i • b i := (b.sum_equivFun x).symm
    rwa [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (by grind)] at this

中文:
定理 eq_id_of_finrank_le_one
  证明: by
  interval_cases h : finrank R V
  · have : Subsingleton V := (finrank_eq_zero_iff_of_free R V).mp h
    simp [Subsingleton.eq_zero v]
  · let b := finBasis R V
    ext x
    suffices f x • v = 0 by
      simp [apply, this]
    let i : Fin (finrank R V) := ⟨0, by simp [h]⟩
    suffices forall x, x = b.repr x i • (b i) by
      rw [this v]; rw [map_smul]; rw [smul_eq_mul]; rw [mul_comm] at hfv
      rw [this x]; rw [this v]; rw [map_smul]; rw [smul_eq_mul]; rw [← mul_smul]; rw [mul_assoc]; rw [hfv]; rw [mul_zero]; rw [zero_smul]
    intro x
    have : x = ∑ i, b.repr x i • b i := (b.sum_equivFun x).symm
    rwa [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (by grind)] at this

Depends on / 依赖: Subsingleton, Subsingleton.eq_zero, b.repr, eq_zero, finBasis, finrank, finrank_eq_zero_iff_of_free, interval_cases, map_smul, mul_assoc, mul_comm, mul_smul, mul_zero, smul_eq_mul, zero_smul
-/
theorem eq_id_of_finrank_le_one
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    [Free R V] [Module.Finite R V] [StrongRankCondition R]
    {f : Dual R V} {v : V} (hfv : f v = 0) (h1 : finrank R V <= 1) :
    transvection f v = id := by
  interval_cases h : finrank R V
  · have : Subsingleton V := (finrank_eq_zero_iff_of_free R V).mp h
    simp [Subsingleton.eq_zero v]
  · let b := finBasis R V
    ext x
    suffices f x • v = 0 by
      simp [apply, this]
    let i : Fin (finrank R V) := ⟨0, by simp [h]⟩
    suffices forall x, x = b.repr x i • (b i) by
      rw [this v]; rw [map_smul]; rw [smul_eq_mul]; rw [mul_comm] at hfv
      rw [this x]; rw [this v]; rw [map_smul]; rw [smul_eq_mul]; rw [← mul_smul]; rw [mul_assoc]; rw [hfv]; rw [mul_zero]; rw [zero_smul]
    intro x
    have : x = ∑ i, b.repr x i • b i := (b.sum_equivFun x).symm
    rwa [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (by grind)] at this

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  statement: {W : Type*} [AddCommMonoid W] [Module R W]
  proof: by
  ext; simp [transvection.apply]

中文:
定理 congr
  结论: {W : 类型} [加法交换幺半群 W] [模 R W]
  证明: by
  ext; simp [transvection.apply]

Depends on / 依赖: transvection, transvection.apply
-/
theorem congr {W : Type*} [AddCommMonoid W] [Module R W]
    (f : Dual R V) (v : V) (e : V ≃ₗ[R] W) :
    e ∘ₗ (transvection f v) ∘ₗ e.symm = transvection (f ∘ₗ e.symm) (e v) := by
  ext; simp [transvection.apply]

end LinearMap.transvection

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

namespace LinearEquiv

open LinearMap LinearMap.transvection Module Submodule

/--
Definition of `transvection` / `transvection` 的定义

English:
definition transvection
  signature: {f : Dual R V} {v : V} (h : f v = 0)
  body: LinearMap.transvection f v
  invFun := LinearMap.transvection f (-v)
  map_add' x y := by simp [map_add]
  map_smul' r x := by simp
  left_inv x := by
    simp [comp_of_left_eq_apply h]
  right_inv x := by
    have h' : f (-v) = 0 := by simp [h]
    simp [comp_of_left_eq_apply h']

中文:
定义 transvection
  签名: {f : 对偶 R V} {v : V} (h : f v = 0)
  定义体: LinearMap.transvection f v
  invFun := LinearMap.transvection f (-v)
  map_add' x y := by simp [map_add]
  map_smul' r x := by simp
  left_inv x := by
    simp [comp_of_left_eq_apply h]
  right_inv x := by
    have h' : f (-v) = 0 := by simp [h]
    simp [comp_of_left_eq_apply h']

Depends on / 依赖: LinearMap, LinearMap.transvection, transvection
-/
def transvection {f : Dual R V} {v : V} (h : f v = 0) :
    V ≃ₗ[R] V where
  toFun := LinearMap.transvection f v
  invFun := LinearMap.transvection f (-v)
  map_add' x y := by simp [map_add]
  map_smul' r x := by simp
  left_inv x := by
    simp [comp_of_left_eq_apply h]
  right_inv x := by
    have h' : f (-v) = 0 := by simp [h]
    simp [comp_of_left_eq_apply h']

namespace transvection

/--
theorem `apply` / 定理 `apply`

English:
theorem apply
  given: {f : Dual R V} {v : V} (h : f v = 0) (x : V)
  proof: rfl

@[simp]

中文:
定理 apply
  条件: {f : 对偶 R V} {v : V} (h : f v = 0) (x : V)
  证明: rfl

@[simp]
-/
theorem apply {f : Dual R V} {v : V} (h : f v = 0) (x : V) :
    transvection h x = x + f x • v :=
  rfl

@[simp]
/--
theorem `coe_toLinearMap` / 定理 `coe_toLinearMap`

English:
theorem coe_toLinearMap
  given: {f : Dual R V} {v : V} (h : f v = 0)
  proof: rfl

@[simp]

中文:
定理 coe_toLinearMap
  条件: {f : 对偶 R V} {v : V} (h : f v = 0)
  证明: rfl

@[simp]
-/
theorem coe_toLinearMap {f : Dual R V} {v : V} (h : f v = 0) :
    LinearEquiv.transvection h = LinearMap.transvection f v :=
  rfl

@[simp]
/--
theorem `coe_apply` / 定理 `coe_apply`

English:
theorem coe_apply
  given: {f : Dual R V} {v x : V} {h : f v = 0}
  proof: rfl

中文:
定理 coe_apply
  条件: {f : 对偶 R V} {v x : V} {h : f v = 0}
  证明: rfl
-/
theorem coe_apply {f : Dual R V} {v x : V} {h : f v = 0} :
    LinearEquiv.transvection h x = LinearMap.transvection f v x :=
  rfl

/--
theorem `trans_of_left_eq` / 定理 `trans_of_left_eq`

English:
theorem trans_of_left_eq
  statement: {f : Dual R V} {v w : V}
  proof: by
  ext; simp [comp_of_left_eq_apply hw]

中文:
定理 trans_of_left_eq
  结论: {f : 对偶 R V} {v w : V}
  证明: by
  ext; simp [comp_of_left_eq_apply hw]

Depends on / 依赖: comp_of_left_eq_apply, transvection
-/
theorem trans_of_left_eq {f : Dual R V} {v w : V}
    (hv : f v = 0) (hw : f w = 0) (hvw : f (v + w) = 0 := by simp [hv, hw]) :
    (transvection hw).trans (transvection hv) = transvection hvw := by
  ext; simp [comp_of_left_eq_apply hw]

/--
theorem `trans_of_right_eq` / 定理 `trans_of_right_eq`

English:
theorem trans_of_right_eq
  statement: {f g : Dual R V} {v : V}
  proof: by
  ext; simp [comp_of_right_eq_apply hf]

@[simp]

中文:
定理 trans_of_right_eq
  结论: {f g : 对偶 R V} {v : V}
  证明: by
  ext; simp [comp_of_right_eq_apply hf]

@[simp]

Depends on / 依赖: comp_of_right_eq_apply, transvection
-/
theorem trans_of_right_eq {f g : Dual R V} {v : V}
    (hf : f v = 0) (hg : g v = 0) (hfg : (f + g) v = 0 := by simp [hf, hg]) :
    (transvection hg).trans (transvection hf) = transvection hfg := by
  ext; simp [comp_of_right_eq_apply hf]

@[simp]
/--
theorem `of_left_eq_zero` / 定理 `of_left_eq_zero`

English:
theorem of_left_eq_zero
  given: (v : V) (hv := LinearMap.zero_apply v)
  proof: by
  ext; simp [transvection]

@[simp]

中文:
定理 of_left_eq_zero
  条件: (v : V) (hv := 线性映射.zero_apply v)
  证明: by
  ext; simp [transvection]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.zero_apply, zero_apply
-/
theorem of_left_eq_zero (v : V) (hv := LinearMap.zero_apply v) :
    transvection hv = refl R V := by
  ext; simp [transvection]

@[simp]
/--
theorem `of_right_eq_zero` / 定理 `of_right_eq_zero`

English:
theorem of_right_eq_zero
  given: (f : Dual R V) (hf := f.map_zero)
  proof: by
  ext; simp [transvection]

中文:
定理 of_right_eq_zero
  条件: (f : 对偶 R V) (hf := f.map_zero)
  证明: by
  ext; simp [transvection]

Depends on / 依赖: f.map_zero, map_zero
-/
theorem of_right_eq_zero (f : Dual R V) (hf := f.map_zero) :
    transvection hf = refl R V := by
  ext; simp [transvection]

/--
theorem `symm_eq` / 定理 `symm_eq`

English:
theorem symm_eq
  statement: {f : Dual R V} {v : V}
  proof: by
  ext;
  simp [symm_apply_eq, comp_of_left_eq_apply hv']

中文:
定理 symm_eq
  结论: {f : 对偶 R V} {v : V}
  证明: by
  ext;
  simp [symm_apply_eq, comp_of_left_eq_apply hv']

Depends on / 依赖: comp_of_left_eq_apply, symm_apply_eq, transvection
-/
theorem symm_eq {f : Dual R V} {v : V}
    (hv : f v = 0) (hv' : f (-v) = 0 := by simp [hv]) :
    (transvection hv).symm = transvection hv' := by
  ext;
  simp [symm_apply_eq, comp_of_left_eq_apply hv']

/--
theorem `inv_eq` / 定理 `inv_eq`

English:
theorem inv_eq
  statement: {f : Dual R V} {v : V}
  proof: symm_eq hv

中文:
定理 inv_eq
  结论: {f : 对偶 R V} {v : V}
  证明: symm_eq hv

Depends on / 依赖: symm_eq, transvection
-/
theorem inv_eq {f : Dual R V} {v : V}
    (hv : f v = 0) (hv' : f (-v) = 0 := by simp [hv]) :
    (transvection hv)⁻¹ = transvection hv' :=
  symm_eq hv

/--
theorem `symm_eq'` / 定理 `symm_eq'`

English:
theorem symm_eq'
  statement: {f : Dual R V} {v : V}
  proof: by
  ext; simp [symm_apply_eq, comp_of_right_eq_apply hf]

中文:
定理 symm_eq'
  结论: {f : 对偶 R V} {v : V}
  证明: by
  ext; simp [symm_apply_eq, comp_of_right_eq_apply hf]

Depends on / 依赖: comp_of_right_eq_apply, symm_apply_eq, transvection
-/
theorem symm_eq' {f : Dual R V} {v : V}
    (hf : f v = 0) (hf' : (-f) v = 0 := by simp [hf]) :
    (transvection hf).symm = transvection hf' := by
  ext; simp [symm_apply_eq, comp_of_right_eq_apply hf]

/--
theorem `inv_eq'` / 定理 `inv_eq'`

English:
theorem inv_eq'
  statement: {f : Dual R V} {v : V}
  proof: symm_eq' hf

中文:
定理 inv_eq'
  结论: {f : 对偶 R V} {v : V}
  证明: symm_eq' hf

Depends on / 依赖: symm_eq, transvection
-/
theorem inv_eq' {f : Dual R V} {v : V}
    (hf : f v = 0) (hf' : (-f) v = 0 := by simp [hf]) :
    (transvection hf)⁻¹ = transvection hf' :=
  symm_eq' hf

end transvection

/--
theorem `mem_fixedSubmodule_transvection_iff` / 定理 `mem_fixedSubmodule_transvection_iff`

English:
theorem mem_fixedSubmodule_transvection_iff
  given: {f : Dual R V} {v : V} {hfv : f v = 0} {x : V}
  proof: by
  simp [LinearMap.transvection.apply, add_eq_left]

中文:
定理 mem_fixedSubmodule_transvection_iff
  条件: {f : 对偶 R V} {v : V} {hfv : f v = 0} {x : V}
  证明: by
  simp [LinearMap.transvection.apply, add_eq_left]

Depends on / 依赖: LinearMap, LinearMap.transvection.apply, add_eq_left, transvection
-/
theorem mem_fixedSubmodule_transvection_iff {f : Dual R V} {v : V} {hfv : f v = 0} {x : V} :
    x in (LinearEquiv.transvection hfv).fixedSubmodule ↔ f x • v = 0 := by
  simp [LinearMap.transvection.apply, add_eq_left]

/--
theorem `ker_le_fixedSubmodule_transvection` / 定理 `ker_le_fixedSubmodule_transvection`

English:
theorem ker_le_fixedSubmodule_transvection
  given: {f : Dual R V} {v : V} (hfv : f v = 0)
  proof: by
  intro x hx
  rw [mem_ker] at hx
  simp [LinearMap.transvection.apply, hx]

中文:
定理 ker_le_fixedSubmodule_transvection
  条件: {f : 对偶 R V} {v : V} (hfv : f v = 0)
  证明: by
  intro x hx
  rw [mem_ker] at hx
  simp [LinearMap.transvection.apply, hx]

Depends on / 依赖: LinearMap, LinearMap.transvection.apply, mem_ker, transvection
-/
theorem ker_le_fixedSubmodule_transvection {f : Dual R V} {v : V} (hfv : f v = 0) :
    LinearMap.ker f <= (transvection hfv).fixedSubmodule := by
  intro x hx
  rw [mem_ker] at hx
  simp [LinearMap.transvection.apply, hx]

section dilatransvections

variable (R V) in
/--
Definition of `transvections` / `transvections` 的定义

English:
definition transvections
  signature: : Set (V ≃ₗ[R] V)
  body: { e | exists (f : Dual R V) (v : V) (hfv : f v = 0), e = transvection hfv }

中文:
定义 transvections
  签名: : 集合 (V ≃ₗ[R] V)
  定义体: { e | exists (f : Dual R V) (v : V) (hfv : f v = 0), e = transvection hfv }

Depends on / 依赖: transvection
-/
def transvections : Set (V ≃ₗ[R] V) :=
  { e | exists (f : Dual R V) (v : V) (hfv : f v = 0), e = transvection hfv }

/--
theorem `mem_transvections_iff` / 定理 `mem_transvections_iff`

English:
theorem mem_transvections_iff
  given: {e : V ≃ₗ[R] V}
  proof: Iff.rfl

中文:
定理 mem_transvections_iff
  条件: {e : V ≃ₗ[R] V}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_transvections_iff {e : V ≃ₗ[R] V} :
    e in transvections R V ↔
      exists (f : Dual R V) (v : V) (hfv : f v = 0), e = LinearEquiv.transvection hfv :=
  Iff.rfl

/--
theorem `mem_transvections` / 定理 `mem_transvections`

English:
theorem mem_transvections
  given: {f : Dual R V} {v : V} (hfv : f v = 0)
  proof: ⟨f, v, hfv, rfl⟩

中文:
定理 mem_transvections
  条件: {f : 对偶 R V} {v : V} (hfv : f v = 0)
  证明: ⟨f, v, hfv, rfl⟩
-/
@[simp] theorem mem_transvections {f : Dual R V} {v : V} (hfv : f v = 0) :
    transvection hfv in transvections R V :=
  ⟨f, v, hfv, rfl⟩

/--
theorem `refl_mem_transvections` / 定理 `refl_mem_transvections`

English:
theorem refl_mem_transvections
  proof: ⟨0, 0, by simp, by aesop⟩

中文:
定理 refl_mem_transvections
  证明: ⟨0, 0, by simp, by aesop⟩
-/
@[simp] theorem refl_mem_transvections :
    refl R V in transvections R V :=
  ⟨0, 0, by simp, by aesop⟩

/--
theorem `one_mem_transvections` / 定理 `one_mem_transvections`

English:
theorem one_mem_transvections
  proof: refl_mem_transvections

@[simp]

中文:
定理 one_mem_transvections
  证明: refl_mem_transvections

@[simp]
-/
@[simp] theorem one_mem_transvections :
    1 in transvections R V :=
  refl_mem_transvections

@[simp]
/--
theorem `symm_mem_transvections_iff` / 定理 `symm_mem_transvections_iff`

English:
theorem symm_mem_transvections_iff
  given: {e : V ≃ₗ[R] V}
  proof: by
  suffices forall e in transvections R V, e.symm in transvections R V by
    refine ⟨fun h => ?_, this e⟩
    rw [← symm_symm e]
    exact this _ h
  rintro _ ⟨f, v, hv, rfl⟩
  rw [transvection.symm_eq]
  apply mem_transvections

@[simp]

中文:
定理 symm_mem_transvections_iff
  条件: {e : V ≃ₗ[R] V}
  证明: by
  suffices forall e in transvections R V, e.symm in transvections R V by
    refine ⟨fun h => ?_, this e⟩
    rw [← symm_symm e]
    exact this _ h
  rintro _ ⟨f, v, hv, rfl⟩
  rw [transvection.symm_eq]
  apply mem_transvections

@[simp]

Depends on / 依赖: e.symm, mem_transvections, symm_eq, symm_symm, transvection, transvection.symm_eq, transvections
-/
theorem symm_mem_transvections_iff {e : V ≃ₗ[R] V} :
    e.symm in transvections R V ↔ e in transvections R V := by
  suffices forall e in transvections R V, e.symm in transvections R V by
    refine ⟨fun h => ?_, this e⟩
    rw [← symm_symm e]
    exact this _ h
  rintro _ ⟨f, v, hv, rfl⟩
  rw [transvection.symm_eq]
  apply mem_transvections

@[simp]
/--
theorem `inv_mem_transvections_iff` / 定理 `inv_mem_transvections_iff`

English:
theorem inv_mem_transvections_iff
  given: {e : V ≃ₗ[R] V}
  proof: symm_mem_transvections_iff

中文:
定理 inv_mem_transvections_iff
  条件: {e : V ≃ₗ[R] V}
  证明: symm_mem_transvections_iff

Depends on / 依赖: symm_mem_transvections_iff
-/
theorem inv_mem_transvections_iff {e : V ≃ₗ[R] V} :
    e⁻¹ in transvections R V ↔ e in transvections R V :=
  symm_mem_transvections_iff

open scoped Pointwise in
/--
theorem `transvections_pow_mono` / 定理 `transvections_pow_mono`

English:
theorem transvections_pow_mono
  proof: Set.pow_right_monotone one_mem_transvections

中文:
定理 transvections_pow_mono
  证明: Set.pow_right_monotone one_mem_transvections

Depends on / 依赖: Set.pow_right_monotone, one_mem_transvections, pow_right_monotone
-/
theorem transvections_pow_mono :
    Monotone (fun n : Nat => (transvections R V) ^ n) :=
  Set.pow_right_monotone one_mem_transvections

variable (R V) in
/--
Definition of `dilatransvections` / `dilatransvections` 的定义

English:
definition dilatransvections
  signature: : Set (V ≃ₗ[R] V)
  body: { e : V ≃ₗ[R] V | exists (f : Dual R V) (v : V), e = LinearMap.transvection f v }

中文:
定义 dilatransvections
  签名: : 集合 (V ≃ₗ[R] V)
  定义体: { e : V ≃ₗ[R] V | exists (f : Dual R V) (v : V), e = LinearMap.transvection f v }

Depends on / 依赖: LinearMap, LinearMap.transvection, transvection
-/
def dilatransvections : Set (V ≃ₗ[R] V) :=
  { e : V ≃ₗ[R] V | exists (f : Dual R V) (v : V), e = LinearMap.transvection f v }

/--
theorem `transvections_subset_dilatransvections` / 定理 `transvections_subset_dilatransvections`

English:
theorem transvections_subset_dilatransvections
  proof: by
  rintro e ⟨f, v, hfv, rfl⟩
  exact ⟨f, v, by simp⟩

@[simp]

中文:
定理 transvections_subset_dilatransvections
  证明: by
  rintro e ⟨f, v, hfv, rfl⟩
  exact ⟨f, v, by simp⟩

@[simp]
-/
theorem transvections_subset_dilatransvections :
    transvections R V subseteq dilatransvections R V := by
  rintro e ⟨f, v, hfv, rfl⟩
  exact ⟨f, v, by simp⟩

@[simp]
/--
theorem `refl_mem_dilatransvections` / 定理 `refl_mem_dilatransvections`

English:
theorem refl_mem_dilatransvections
  statement: refl R V in dilatransvections R V
  proof: transvections_subset_dilatransvections one_mem_transvections

中文:
定理 refl_mem_dilatransvections
  结论: refl R V in dilatransvections R V
  证明: transvections_subset_dilatransvections one_mem_transvections

Depends on / 依赖: one_mem_transvections, transvections_subset_dilatransvections
-/
theorem refl_mem_dilatransvections : refl R V in dilatransvections R V :=
  transvections_subset_dilatransvections one_mem_transvections

/--
theorem `transvection_mem_transvections` / 定理 `transvection_mem_transvections`

English:
theorem transvection_mem_transvections
  given: {f : Dual R V} {v : V} {hfv : f v = 0}
  proof: ⟨f, v, hfv, rfl⟩

中文:
定理 transvection_mem_transvections
  条件: {f : 对偶 R V} {v : V} {hfv : f v = 0}
  证明: ⟨f, v, hfv, rfl⟩
-/
theorem transvection_mem_transvections {f : Dual R V} {v : V} {hfv : f v = 0} :
    transvection hfv in transvections R V :=
  ⟨f, v, hfv, rfl⟩

/--
theorem `transvection_mem_dilatransvections` / 定理 `transvection_mem_dilatransvections`

English:
theorem transvection_mem_dilatransvections
  given: {f : Dual R V} {v : V} (hfv : f v = 0)
  proof: transvections_subset_dilatransvections transvection_mem_transvections

@[simp]

中文:
定理 transvection_mem_dilatransvections
  条件: {f : 对偶 R V} {v : V} (hfv : f v = 0)
  证明: transvections_subset_dilatransvections transvection_mem_transvections

@[simp]

Depends on / 依赖: transvection_mem_transvections, transvections_subset_dilatransvections
-/
theorem transvection_mem_dilatransvections {f : Dual R V} {v : V} (hfv : f v = 0) :
    transvection hfv in dilatransvections R V :=
  transvections_subset_dilatransvections transvection_mem_transvections

@[simp]
/--
theorem `one_mem_dilatransvections` / 定理 `one_mem_dilatransvections`

English:
theorem one_mem_dilatransvections
  statement: 1 in dilatransvections R V
  proof: refl_mem_dilatransvections

@[simp]

中文:
定理 one_mem_dilatransvections
  结论: 1 in dilatransvections R V
  证明: refl_mem_dilatransvections

@[simp]

Depends on / 依赖: refl_mem_dilatransvections
-/
theorem one_mem_dilatransvections : 1 in dilatransvections R V :=
  refl_mem_dilatransvections

@[simp]
/--
theorem `symm_mem_dilatransvections_iff` / 定理 `symm_mem_dilatransvections_iff`

English:
theorem symm_mem_dilatransvections_iff
  given: {e : V ≃ₗ[R] V}
  proof: by
  suffices forall e in dilatransvections R V, e.symm in dilatransvections R V from
    ⟨by simpa using this e.symm, this e⟩
  rintro e ⟨f, v, he⟩
  use f, - e.symm v
  ext x
  suffices x = e x - f x • v by
    simpa [LinearMap.transvection.apply, ← sub_eq_add_neg, symm_apply_eq]
  rw [eq_comm]; rw [sub_eq_iff_eq_add]; rw [← coe_coe]; rw [he]; rw [LinearMap.transvection.apply]

@[simp]

中文:
定理 symm_mem_dilatransvections_iff
  条件: {e : V ≃ₗ[R] V}
  证明: by
  suffices forall e in dilatransvections R V, e.symm in dilatransvections R V from
    ⟨by simpa using this e.symm, this e⟩
  rintro e ⟨f, v, he⟩
  use f, - e.symm v
  ext x
  suffices x = e x - f x • v by
    simpa [LinearMap.transvection.apply, ← sub_eq_add_neg, symm_apply_eq]
  rw [eq_comm]; rw [sub_eq_iff_eq_add]; rw [← coe_coe]; rw [he]; rw [LinearMap.transvection.apply]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.transvection.apply, coe_coe, dilatransvections, e.symm, eq_comm, sub_eq_add_neg, sub_eq_iff_eq_add, symm_apply_eq, transvection
-/
theorem symm_mem_dilatransvections_iff {e : V ≃ₗ[R] V} :
    e.symm in dilatransvections R V ↔ e in dilatransvections R V := by
  suffices forall e in dilatransvections R V, e.symm in dilatransvections R V from
    ⟨by simpa using this e.symm, this e⟩
  rintro e ⟨f, v, he⟩
  use f, - e.symm v
  ext x
  suffices x = e x - f x • v by
    simpa [LinearMap.transvection.apply, ← sub_eq_add_neg, symm_apply_eq]
  rw [eq_comm]; rw [sub_eq_iff_eq_add]; rw [← coe_coe]; rw [he]; rw [LinearMap.transvection.apply]

@[simp]
/--
theorem `inv_mem_dilatransvections_iff` / 定理 `inv_mem_dilatransvections_iff`

English:
theorem inv_mem_dilatransvections_iff
  given: {e : V ≃ₗ[R] V}
  proof: symm_mem_dilatransvections_iff

中文:
定理 inv_mem_dilatransvections_iff
  条件: {e : V ≃ₗ[R] V}
  证明: symm_mem_dilatransvections_iff

Depends on / 依赖: symm_mem_dilatransvections_iff
-/
theorem inv_mem_dilatransvections_iff {e : V ≃ₗ[R] V} :
    e⁻¹ in dilatransvections R V ↔ e in dilatransvections R V :=
  symm_mem_dilatransvections_iff

/--
Definition of `dilatransvection` / `dilatransvection` 的定义

English:
definition dilatransvection
  signature: {f : Dual R V} {v : V} (h : IsUnit (1 + f v))
  body: LinearMap.transvection f v
  invFun := LinearMap.transvection f (-h.unit⁻¹ • v)
  map_add' x y := by simp [map_add]
  map_smul' r x := by simp
  left_inv x := by
    nth_rewrite 3 [← one_smul R v]
    rw [← LinearMap.comp_apply]; rw [Units.smul_def]; rw [LinearMap.transvection.comp_smul_smul]
    simp only [Units.val_neg, one_mul, mul_neg, ← sub_eq_add_neg]
    suffices (-h.unit⁻¹) + 1 - f v * (h.unit⁻¹) = 0 by simp [this]
    rw [sub_eq_zero]; rw [neg_add_eq_iff_eq_add]
    nth_rewrite 1 [← one_mul (h.unit⁻¹), Units.val_mul, ← add_mul]
    simp
  right_inv x := by
    simp only [LinearMap.transvection.apply, add_assoc, add_eq_left,
      Units.smul_def]
    rw [smul_smul]; rw [← add_smul]
    suffices (f x * ↑(-h.unit⁻¹) + f (x + (f x * ↑(-h.unit⁻¹)) • v)) = 0 by rw [this, zero_smul]
    rw [LinearMap.map_add]; rw [LinearMap.map_smul]; rw [smul_eq_mul]
    nth_rewrite 2 [← mul_one (f x)]
    rw [mul_assoc]; rw [← mul_add]; rw [← mul_add]
    rw [← add_assoc]; rw [add_comm _ 1]; rw [add_assoc]
    nth_rewrite 1 [← mul_one (-h.unit⁻¹), Units.val_mul, Units.val_one, ← mul_add]
    simp

@[simp]

中文:
定义 dilatransvection
  签名: {f : 对偶 R V} {v : V} (h : 是单位 (1 + f v))
  定义体: LinearMap.transvection f v
  invFun := LinearMap.transvection f (-h.unit⁻¹ • v)
  map_add' x y := by simp [map_add]
  map_smul' r x := by simp
  left_inv x := by
    nth_rewrite 3 [← one_smul R v]
    rw [← LinearMap.comp_apply]; rw [Units.smul_def]; rw [LinearMap.transvection.comp_smul_smul]
    simp only [Units.val_neg, one_mul, mul_neg, ← sub_eq_add_neg]
    suffices (-h.unit⁻¹) + 1 - f v * (h.unit⁻¹) = 0 by simp [this]
    rw [sub_eq_zero]; rw [neg_add_eq_iff_eq_add]
    nth_rewrite 1 [← one_mul (h.unit⁻¹), Units.val_mul, ← add_mul]
    simp
  right_inv x := by
    simp only [LinearMap.transvection.apply, add_assoc, add_eq_left,
      Units.smul_def]
    rw [smul_smul]; rw [← add_smul]
    suffices (f x * ↑(-h.unit⁻¹) + f (x + (f x * ↑(-h.unit⁻¹)) • v)) = 0 by rw [this, zero_smul]
    rw [LinearMap.map_add]; rw [LinearMap.map_smul]; rw [smul_eq_mul]
    nth_rewrite 2 [← mul_one (f x)]
    rw [mul_assoc]; rw [← mul_add]; rw [← mul_add]
    rw [← add_assoc]; rw [add_comm _ 1]; rw [add_assoc]
    nth_rewrite 1 [← mul_one (-h.unit⁻¹), Units.val_mul, Units.val_one, ← mul_add]
    simp

@[simp]

Depends on / 依赖: LinearMap, LinearMap.transvection, transvection
-/
noncomputable def dilatransvection {f : Dual R V} {v : V} (h : IsUnit (1 + f v)) :
    V ≃ₗ[R] V where
  toFun := LinearMap.transvection f v
  invFun := LinearMap.transvection f (-h.unit⁻¹ • v)
  map_add' x y := by simp [map_add]
  map_smul' r x := by simp
  left_inv x := by
    nth_rewrite 3 [← one_smul R v]
    rw [← LinearMap.comp_apply]; rw [Units.smul_def]; rw [LinearMap.transvection.comp_smul_smul]
    simp only [Units.val_neg, one_mul, mul_neg, ← sub_eq_add_neg]
    suffices (-h.unit⁻¹) + 1 - f v * (h.unit⁻¹) = 0 by simp [this]
    rw [sub_eq_zero]; rw [neg_add_eq_iff_eq_add]
    nth_rewrite 1 [← one_mul (h.unit⁻¹), Units.val_mul, ← add_mul]
    simp
  right_inv x := by
    simp only [LinearMap.transvection.apply, add_assoc, add_eq_left,
      Units.smul_def]
    rw [smul_smul]; rw [← add_smul]
    suffices (f x * ↑(-h.unit⁻¹) + f (x + (f x * ↑(-h.unit⁻¹)) • v)) = 0 by rw [this, zero_smul]
    rw [LinearMap.map_add]; rw [LinearMap.map_smul]; rw [smul_eq_mul]
    nth_rewrite 2 [← mul_one (f x)]
    rw [mul_assoc]; rw [← mul_add]; rw [← mul_add]
    rw [← add_assoc]; rw [add_comm _ 1]; rw [add_assoc]
    nth_rewrite 1 [← mul_one (-h.unit⁻¹), Units.val_mul, Units.val_one, ← mul_add]
    simp

@[simp]
/--
theorem `dilatransvection.coe_toLinearMap` / 定理 `dilatransvection.coe_toLinearMap`

English:
theorem dilatransvection.coe_toLinearMap
  given: {f : Dual R V} {v : V} {h : IsUnit (1 + f v)}
  proof: rfl

中文:
定理 dilatransvection.coe_toLinearMap
  条件: {f : 对偶 R V} {v : V} {h : 是单位 (1 + f v)}
  证明: rfl
-/
theorem dilatransvection.coe_toLinearMap {f : Dual R V} {v : V} {h : IsUnit (1 + f v)} :
    (dilatransvection h).toLinearMap = LinearMap.transvection f v :=
  rfl

/--
theorem `dilatransvection.apply` / 定理 `dilatransvection.apply`

English:
theorem dilatransvection.apply
  given: {f : Dual R V} {v : V} {h : IsUnit (1 + f v)} {x : V}
  proof: by
  simp [dilatransvection, LinearMap.transvection.apply]

@[simp]

中文:
定理 dilatransvection.apply
  条件: {f : 对偶 R V} {v : V} {h : 是单位 (1 + f v)} {x : V}
  证明: by
  simp [dilatransvection, LinearMap.transvection.apply]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.transvection.apply, dilatransvection, transvection
-/
theorem dilatransvection.apply {f : Dual R V} {v : V} {h : IsUnit (1 + f v)} {x : V} :
    dilatransvection h x = x + f x • v := by
  simp [dilatransvection, LinearMap.transvection.apply]

@[simp]
/--
theorem `dilatransvection_mem_dilatransvections` / 定理 `dilatransvection_mem_dilatransvections`

English:
theorem dilatransvection_mem_dilatransvections
  given: {f : Dual R V} {v : V} {h : IsUnit (1 + f v)}
  proof: by
  simp only [dilatransvections, Set.mem_ofPred_eq]
  refine ⟨f, v, by simp⟩

中文:
定理 dilatransvection_mem_dilatransvections
  条件: {f : 对偶 R V} {v : V} {h : 是单位 (1 + f v)}
  证明: by
  simp only [dilatransvections, Set.mem_ofPred_eq]
  refine ⟨f, v, by simp⟩

Depends on / 依赖: Set.mem_ofPred_eq, dilatransvections, mem_ofPred_eq
-/
theorem dilatransvection_mem_dilatransvections {f : Dual R V} {v : V} {h : IsUnit (1 + f v)} :
    dilatransvection h in dilatransvections R V := by
  simp only [dilatransvections, Set.mem_ofPred_eq]
  refine ⟨f, v, by simp⟩

open scoped Pointwise in
/--
theorem `dilatransvections_pow_mono` / 定理 `dilatransvections_pow_mono`

English:
theorem dilatransvections_pow_mono
  proof: Set.pow_right_monotone one_mem_dilatransvections

中文:
定理 dilatransvections_pow_mono
  证明: Set.pow_right_monotone one_mem_dilatransvections

Depends on / 依赖: Set.pow_right_monotone, one_mem_dilatransvections, pow_right_monotone
-/
theorem dilatransvections_pow_mono :
    Monotone (fun n : Nat => (dilatransvections R V) ^ n) :=
  Set.pow_right_monotone one_mem_dilatransvections

section divisionRing

variable {K : Type*} [DivisionRing K] [Module K V]

/--
theorem `mem_dilatransvections_iff_rank` / 定理 `mem_dilatransvections_iff_rank`

English:
theorem mem_dilatransvections_iff_rank
  given: {e : V ≃ₗ[K] V}
  proof: by
  simp only [dilatransvections]
  constructor
  · simp only [Set.mem_ofPred_eq]
    rintro ⟨f, v, he⟩
    apply le_trans (rank_mono (t := K ∙ v) ?_)
    · apply le_trans (rank_span_le _) (by simp)
    rintro _ ⟨x, rfl⟩
    simp [mem_span_singleton, he, LinearMap.transvection.apply]
  · intro he
    simp only [Set.mem_ofPred_eq]
    set u := (e : V ->ₗ[K] V) - LinearMap.id with hu
    rw [eq_sub_iff_add_eq] at hu
    by_cases hr : Module.rank K (range u) = 0
    · use 0, 0
      ext x
      suffices u x = 0 by simp [← hu, this]
      rw [rank_zero_iff] at hr
      simpa [← Subtype.coe_inj] using Subsingleton.allEq (⟨u x , mem_range_self u x⟩ : range u) 0
    rw [← ne_eq]; rw [← Cardinal.one_le_iff_ne_zero] at hr
    replace he : Module.rank K (range u) = 1 := le_antisymm he hr
    rw [rank_eq_one_iff_finrank_eq_one]; rw [finrank_eq_one_iff Unit] at he
    obtain ⟨b⟩ := he
    use (b.coord default) ∘ₗ u.rangeRestrict, b default
    ext x
    rw [← hu]; rw [LinearMap.transvection.apply]; rw [add_comm]
    suffices u x = b.repr (u.rangeRestrict x) default • b default by
      simp [this]
    suffices u.rangeRestrict x = u x by
      rw [← this]; rw [← Submodule.coe_smul]; rw [Subtype.coe_inj]
      nth_rewrite 1 [← b.linearCombination_repr (u.rangeRestrict x)]
      rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum_eq_single default] <;> simp
    exact codRestrict_apply (range u) u x

中文:
定理 mem_dilatransvections_iff_rank
  条件: {e : V ≃ₗ[K] V}
  证明: by
  simp only [dilatransvections]
  constructor
  · simp only [Set.mem_ofPred_eq]
    rintro ⟨f, v, he⟩
    apply le_trans (rank_mono (t := K ∙ v) ?_)
    · apply le_trans (rank_span_le _) (by simp)
    rintro _ ⟨x, rfl⟩
    simp [mem_span_singleton, he, LinearMap.transvection.apply]
  · intro he
    simp only [Set.mem_ofPred_eq]
    set u := (e : V ->ₗ[K] V) - LinearMap.id with hu
    rw [eq_sub_iff_add_eq] at hu
    by_cases hr : Module.rank K (range u) = 0
    · use 0, 0
      ext x
      suffices u x = 0 by simp [← hu, this]
      rw [rank_zero_iff] at hr
      simpa [← Subtype.coe_inj] using Subsingleton.allEq (⟨u x , mem_range_self u x⟩ : range u) 0
    rw [← ne_eq]; rw [← Cardinal.one_le_iff_ne_zero] at hr
    replace he : Module.rank K (range u) = 1 := le_antisymm he hr
    rw [rank_eq_one_iff_finrank_eq_one]; rw [finrank_eq_one_iff Unit] at he
    obtain ⟨b⟩ := he
    use (b.coord default) ∘ₗ u.rangeRestrict, b default
    ext x
    rw [← hu]; rw [LinearMap.transvection.apply]; rw [add_comm]
    suffices u x = b.repr (u.rangeRestrict x) default • b default by
      simp [this]
    suffices u.rangeRestrict x = u x by
      rw [← this]; rw [← Submodule.coe_smul]; rw [Subtype.coe_inj]
      nth_rewrite 1 [← b.linearCombination_repr (u.rangeRestrict x)]
      rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum_eq_single default] <;> simp
    exact codRestrict_apply (range u) u x

Depends on / 依赖: LinearMap, LinearMap.id, LinearMap.transvection.apply, Module, Module.rank, Set.mem_ofPred_eq, dilatransvections, eq_sub_iff_add_eq, le_trans, mem_ofPred_eq, mem_span_singleton, rank_mono, rank_span_le, rank_ze, transvection
-/
theorem mem_dilatransvections_iff_rank {e : V ≃ₗ[K] V} :
    e in dilatransvections K V ↔
      Module.rank K (range ((e : V ->ₗ[K] V) - LinearMap.id (R := K))) <= 1 := by
  simp only [dilatransvections]
  constructor
  · simp only [Set.mem_ofPred_eq]
    rintro ⟨f, v, he⟩
    apply le_trans (rank_mono (t := K ∙ v) ?_)
    · apply le_trans (rank_span_le _) (by simp)
    rintro _ ⟨x, rfl⟩
    simp [mem_span_singleton, he, LinearMap.transvection.apply]
  · intro he
    simp only [Set.mem_ofPred_eq]
    set u := (e : V ->ₗ[K] V) - LinearMap.id with hu
    rw [eq_sub_iff_add_eq] at hu
    by_cases hr : Module.rank K (range u) = 0
    · use 0, 0
      ext x
      suffices u x = 0 by simp [← hu, this]
      rw [rank_zero_iff] at hr
      simpa [← Subtype.coe_inj] using Subsingleton.allEq (⟨u x , mem_range_self u x⟩ : range u) 0
    rw [← ne_eq]; rw [← Cardinal.one_le_iff_ne_zero] at hr
    replace he : Module.rank K (range u) = 1 := le_antisymm he hr
    rw [rank_eq_one_iff_finrank_eq_one]; rw [finrank_eq_one_iff Unit] at he
    obtain ⟨b⟩ := he
    use (b.coord default) ∘ₗ u.rangeRestrict, b default
    ext x
    rw [← hu]; rw [LinearMap.transvection.apply]; rw [add_comm]
    suffices u x = b.repr (u.rangeRestrict x) default • b default by
      simp [this]
    suffices u.rangeRestrict x = u x by
      rw [← this]; rw [← Submodule.coe_smul]; rw [Subtype.coe_inj]
      nth_rewrite 1 [← b.linearCombination_repr (u.rangeRestrict x)]
      rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum_eq_single default] <;> simp
    exact codRestrict_apply (range u) u x

open Cardinal in
/--
theorem `mem_dilatransvections_iff_finrank` / 定理 `mem_dilatransvections_iff_finrank`

English:
theorem mem_dilatransvections_iff_finrank
  given: [Module.Finite K V] {e : V ≃ₗ[K] V}
  proof: by
  rw [mem_dilatransvections_iff_rank]; rw [finrank]; rw [← one_toNat]; rw [toNat_le_iff_le_of_lt_aleph0 (rank_lt_aleph0 K _) one_lt_aleph0]

中文:
定理 mem_dilatransvections_iff_finrank
  条件: [模.有限 K V] {e : V ≃ₗ[K] V}
  证明: by
  rw [mem_dilatransvections_iff_rank]; rw [finrank]; rw [← one_toNat]; rw [toNat_le_iff_le_of_lt_aleph0 (rank_lt_aleph0 K _) one_lt_aleph0]

Depends on / 依赖: finrank, mem_dilatransvections_iff_rank, one_lt_aleph0, one_toNat, rank_lt_aleph0, toNat_le_iff_le_of_lt_aleph0
-/
theorem mem_dilatransvections_iff_finrank [Module.Finite K V] {e : V ≃ₗ[K] V} :
    e in dilatransvections K V ↔
      finrank K (range ((e : V ->ₗ[K] V) - LinearMap.id (R := K))) <= 1 := by
  rw [mem_dilatransvections_iff_rank]; rw [finrank]; rw [← one_toNat]; rw [toNat_le_iff_le_of_lt_aleph0 (rank_lt_aleph0 K _) one_lt_aleph0]

/--
theorem `mem_dilatransvections_iff_finrank_quotient` / 定理 `mem_dilatransvections_iff_finrank_quotient`

English:
theorem mem_dilatransvections_iff_finrank_quotient
  given: [Module.Finite K V] {e : V ≃ₗ[K] V}
  proof: by
  rw [mem_dilatransvections_iff_finrank]; rw [← (quotKerEquivRange _).finrank_eq]; rw [← fixedSubmodule_eq_ker]

中文:
定理 mem_dilatransvections_iff_finrank_quotient
  条件: [模.有限 K V] {e : V ≃ₗ[K] V}
  证明: by
  rw [mem_dilatransvections_iff_finrank]; rw [← (quotKerEquivRange _).finrank_eq]; rw [← fixedSubmodule_eq_ker]

Depends on / 依赖: finrank_eq, fixedSubmodule_eq_ker, mem_dilatransvections_iff_finrank, quotKerEquivRange
-/
theorem mem_dilatransvections_iff_finrank_quotient [Module.Finite K V] {e : V ≃ₗ[K] V} :
    e in dilatransvections K V ↔ finrank K (V ⧸ e.fixedSubmodule) <= 1 := by
  rw [mem_dilatransvections_iff_finrank]; rw [← (quotKerEquivRange _).finrank_eq]; rw [← fixedSubmodule_eq_ker]

/--
theorem `mem_dilatransvections_iff_rank_quotient` / 定理 `mem_dilatransvections_iff_rank_quotient`

English:
theorem mem_dilatransvections_iff_rank_quotient
  given: {e : V ≃ₗ[K] V}
  proof: by
  rw [mem_dilatransvections_iff_rank]; rw [← (quotKerEquivRange _).rank_eq]; rw [← fixedSubmodule_eq_ker]

中文:
定理 mem_dilatransvections_iff_rank_quotient
  条件: {e : V ≃ₗ[K] V}
  证明: by
  rw [mem_dilatransvections_iff_rank]; rw [← (quotKerEquivRange _).rank_eq]; rw [← fixedSubmodule_eq_ker]

Depends on / 依赖: fixedSubmodule_eq_ker, mem_dilatransvections_iff_rank, quotKerEquivRange, rank_eq
-/
theorem mem_dilatransvections_iff_rank_quotient {e : V ≃ₗ[K] V} :
    e in dilatransvections K V ↔ Module.rank K (V ⧸ e.fixedSubmodule) <= 1 := by
  rw [mem_dilatransvections_iff_rank]; rw [← (quotKerEquivRange _).rank_eq]; rw [← fixedSubmodule_eq_ker]

variable (e f : V ≃ₗ[K] V)

/--
theorem `mem_transvections_iff_mem_dilatransvections_and_fixedReduce_eq_one` / 定理 `mem_transvections_iff_mem_dilatransvections_and_fixedReduce_eq_one`

English:
theorem mem_transvections_iff_mem_dilatransvections_and_fixedReduce_eq_one
  proof: by
  refine ⟨fun ⟨f, v, hfv, he⟩ => ?_, fun ⟨he, he'⟩ => ?_⟩
  · constructor
    · rw [he]
      exact transvection_mem_dilatransvections hfv
    · rw [one_eq_refl, fixedReduce_eq_one, he]
      intro x
      apply ker_le_fixedSubmodule_transvection hfv
      rw [transvection.apply]
      simp [hfv]
  · by_cases he_one : e = 1
    · use 0, 0, by simp, by aesop
    have hefixed_ne_top : e.fixedSubmodule != ⊤ := by
      rwa [ne_eq, LinearEquiv.fixedSubmodule_eq_top_iff]
    obtain ⟨w : V, hw : w ∉ e.fixedSubmodule⟩ :=
      SetLike.exists_not_mem_of_ne_top e.fixedSubmodule hefixed_ne_top rfl
    obtain ⟨f, hfw, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw inferInstance
    rw [mem_dilatransvections_iff_finrank_quotient] at he
    have hf' : e.fixedSubmodule = LinearMap.ker f := by
      suffices finrank K (V ⧸ LinearMap.ker f) = 1 by
        apply Submodule.eq_of_le_of_finrank_le
        · intro x
          rw [mem_ker]; rw [← Submodule.mem_bot K]; rw [← hf]
          exact mem_map_of_mem
        rw [← Nat.add_le_add_iff_right]; rw [finrank_quotient_add_finrank] at he
        have := (LinearMap.ker f).finrank_quotient_add_finrank
        linarith
      rw [← Nat.add_left_inj]; rw [Submodule.finrank_quotient_add_finrank]
      rw [← f.finrank_ker_add_one_of_ne_zero]; rw [add_comm]
      aesop
    have eq_top : e.fixedSubmodule ⊔ Submodule.span K {w} = ⊤ := by
      rw [Submodule.sup_span_singleton_eq_top_iff hw]
      apply le_antisymm he
      apply Nat.one_le_of_lt
      rw [← Nat.ne_zero_iff_zero_lt]
      contrapose hefixed_ne_top
      apply eq_top_of_finrank_eq
      rw [← Nat.add_left_cancel_iff]; rw [finrank_quotient_add_finrank]; rw [hefixed_ne_top]; rw [zero_add]
    set v := (f w)⁻¹ • (e w - w)
    suffices hfv : f v = 0 by
      use f, v, hfv
      rw [← LinearEquiv.toLinearMap_inj]; rw [← sub_eq_zero]; rw [← LinearMap.ker_eq_top]; rw [eq_top_iff]; rw [← eq_top]
      simp only [LinearEquiv.transvection.coe_toLinearMap,
        sup_le_iff, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearEquiv.coe_coe]
      constructor
      · intro x hx
        suffices f x = 0 by
          simpa [this, LinearMap.transvection.apply, sub_eq_zero] using hx
        rwa [hf', LinearMap.mem_ker] at hx
      · simp_all [v, LinearMap.transvection.apply]
    suffices e w - w in LinearMap.ker f by
      simp only [LinearMap.mem_ker, map_sub] at this
      simp only [v, LinearMap.map_smul, map_sub, this, smul_zero]
    rw [← hf']; rw [← Submodule.ker_mkQ e.fixedSubmodule]; rw [LinearMap.mem_ker]
    simp [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, ← fixedReduce_mk, he']

中文:
定理 mem_transvections_iff_mem_dilatransvections_and_fixedReduce_eq_one
  证明: by
  refine ⟨fun ⟨f, v, hfv, he⟩ => ?_, fun ⟨he, he'⟩ => ?_⟩
  · constructor
    · rw [he]
      exact transvection_mem_dilatransvections hfv
    · rw [one_eq_refl, fixedReduce_eq_one, he]
      intro x
      apply ker_le_fixedSubmodule_transvection hfv
      rw [transvection.apply]
      simp [hfv]
  · by_cases he_one : e = 1
    · use 0, 0, by simp, by aesop
    have hefixed_ne_top : e.fixedSubmodule != ⊤ := by
      rwa [ne_eq, LinearEquiv.fixedSubmodule_eq_top_iff]
    obtain ⟨w : V, hw : w ∉ e.fixedSubmodule⟩ :=
      SetLike.exists_not_mem_of_ne_top e.fixedSubmodule hefixed_ne_top rfl
    obtain ⟨f, hfw, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw inferInstance
    rw [mem_dilatransvections_iff_finrank_quotient] at he
    have hf' : e.fixedSubmodule = LinearMap.ker f := by
      suffices finrank K (V ⧸ LinearMap.ker f) = 1 by
        apply Submodule.eq_of_le_of_finrank_le
        · intro x
          rw [mem_ker]; rw [← Submodule.mem_bot K]; rw [← hf]
          exact mem_map_of_mem
        rw [← Nat.add_le_add_iff_right]; rw [finrank_quotient_add_finrank] at he
        have := (LinearMap.ker f).finrank_quotient_add_finrank
        linarith
      rw [← Nat.add_left_inj]; rw [Submodule.finrank_quotient_add_finrank]
      rw [← f.finrank_ker_add_one_of_ne_zero]; rw [add_comm]
      aesop
    have eq_top : e.fixedSubmodule ⊔ Submodule.span K {w} = ⊤ := by
      rw [Submodule.sup_span_singleton_eq_top_iff hw]
      apply le_antisymm he
      apply Nat.one_le_of_lt
      rw [← Nat.ne_zero_iff_zero_lt]
      contrapose hefixed_ne_top
      apply eq_top_of_finrank_eq
      rw [← Nat.add_left_cancel_iff]; rw [finrank_quotient_add_finrank]; rw [hefixed_ne_top]; rw [zero_add]
    set v := (f w)⁻¹ • (e w - w)
    suffices hfv : f v = 0 by
      use f, v, hfv
      rw [← LinearEquiv.toLinearMap_inj]; rw [← sub_eq_zero]; rw [← LinearMap.ker_eq_top]; rw [eq_top_iff]; rw [← eq_top]
      simp only [LinearEquiv.transvection.coe_toLinearMap,
        sup_le_iff, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearEquiv.coe_coe]
      constructor
      · intro x hx
        suffices f x = 0 by
          simpa [this, LinearMap.transvection.apply, sub_eq_zero] using hx
        rwa [hf', LinearMap.mem_ker] at hx
      · simp_all [v, LinearMap.transvection.apply]
    suffices e w - w in LinearMap.ker f by
      simp only [LinearMap.mem_ker, map_sub] at this
      simp only [v, LinearMap.map_smul, map_sub, this, smul_zero]
    rw [← hf']; rw [← Submodule.ker_mkQ e.fixedSubmodule]; rw [LinearMap.mem_ker]
    simp [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, ← fixedReduce_mk, he']

Depends on / 依赖: LinearEquiv, LinearEquiv.fixedSubmodule_eq_top_iff, SetLike, SetLike.exists_not_mem_of_ne_top, e.fixe, e.fixedSubmodule, exists_not_mem_of_ne_top, fixedReduce_eq_one, fixedSubmodule, fixedSubmodule_eq_top_iff, he_one, hefixed_ne_top, ker_le_fixedSubmodule_transvection, ne_eq, one_eq_refl, transvection, transvection.apply, transvection_mem_dilatransvections
-/
theorem mem_transvections_iff_mem_dilatransvections_and_fixedReduce_eq_one
    [Module.Finite K V] (e : V ≃ₗ[K] V) :
    e in transvections K V ↔ e in dilatransvections K V ∧ e.fixedReduce = 1 := by
  refine ⟨fun ⟨f, v, hfv, he⟩ => ?_, fun ⟨he, he'⟩ => ?_⟩
  · constructor
    · rw [he]
      exact transvection_mem_dilatransvections hfv
    · rw [one_eq_refl, fixedReduce_eq_one, he]
      intro x
      apply ker_le_fixedSubmodule_transvection hfv
      rw [transvection.apply]
      simp [hfv]
  · by_cases he_one : e = 1
    · use 0, 0, by simp, by aesop
    have hefixed_ne_top : e.fixedSubmodule != ⊤ := by
      rwa [ne_eq, LinearEquiv.fixedSubmodule_eq_top_iff]
    obtain ⟨w : V, hw : w ∉ e.fixedSubmodule⟩ :=
      SetLike.exists_not_mem_of_ne_top e.fixedSubmodule hefixed_ne_top rfl
    obtain ⟨f, hfw, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw inferInstance
    rw [mem_dilatransvections_iff_finrank_quotient] at he
    have hf' : e.fixedSubmodule = LinearMap.ker f := by
      suffices finrank K (V ⧸ LinearMap.ker f) = 1 by
        apply Submodule.eq_of_le_of_finrank_le
        · intro x
          rw [mem_ker]; rw [← Submodule.mem_bot K]; rw [← hf]
          exact mem_map_of_mem
        rw [← Nat.add_le_add_iff_right]; rw [finrank_quotient_add_finrank] at he
        have := (LinearMap.ker f).finrank_quotient_add_finrank
        linarith
      rw [← Nat.add_left_inj]; rw [Submodule.finrank_quotient_add_finrank]
      rw [← f.finrank_ker_add_one_of_ne_zero]; rw [add_comm]
      aesop
    have eq_top : e.fixedSubmodule ⊔ Submodule.span K {w} = ⊤ := by
      rw [Submodule.sup_span_singleton_eq_top_iff hw]
      apply le_antisymm he
      apply Nat.one_le_of_lt
      rw [← Nat.ne_zero_iff_zero_lt]
      contrapose hefixed_ne_top
      apply eq_top_of_finrank_eq
      rw [← Nat.add_left_cancel_iff]; rw [finrank_quotient_add_finrank]; rw [hefixed_ne_top]; rw [zero_add]
    set v := (f w)⁻¹ • (e w - w)
    suffices hfv : f v = 0 by
      use f, v, hfv
      rw [← LinearEquiv.toLinearMap_inj]; rw [← sub_eq_zero]; rw [← LinearMap.ker_eq_top]; rw [eq_top_iff]; rw [← eq_top]
      simp only [LinearEquiv.transvection.coe_toLinearMap,
        sup_le_iff, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearEquiv.coe_coe]
      constructor
      · intro x hx
        suffices f x = 0 by
          simpa [this, LinearMap.transvection.apply, sub_eq_zero] using hx
        rwa [hf', LinearMap.mem_ker] at hx
      · simp_all [v, LinearMap.transvection.apply]
    suffices e w - w in LinearMap.ker f by
      simp only [LinearMap.mem_ker, map_sub] at this
      simp only [v, LinearMap.map_smul, map_sub, this, smul_zero]
    rw [← hf']; rw [← Submodule.ker_mkQ e.fixedSubmodule]; rw [LinearMap.mem_ker]
    simp [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, ← fixedReduce_mk, he']

end divisionRing

end LinearEquiv.dilatransvections

section baseChange

open IsBaseChange LinearMap LinearEquiv Module

open scoped TensorProduct

section

variable
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    (A : Type*) [CommSemiring A] [Algebra R A]

/--
theorem `LinearMap.transvection.baseChange` / 定理 `LinearMap.transvection.baseChange`

English:
theorem LinearMap.transvection.baseChange
  given: (f : Dual R V) (v : V)
  proof: by
  ext; simp [transvection, TensorProduct.tmul_add]

中文:
定理 线性映射.transvection.baseChange
  条件: (f : 对偶 R V) (v : V)
  证明: by
  ext; simp [transvection, TensorProduct.tmul_add]

Depends on / 依赖: TensorProduct, TensorProduct.tmul_add, tmul_add, transvection
-/
theorem LinearMap.transvection.baseChange (f : Dual R V) (v : V) :
    (transvection f v).baseChange A = transvection (f.baseChange A) (1 otimesₜ[R] v) := by
  ext; simp [transvection, TensorProduct.tmul_add]

variable {W : Type*} [AddCommMonoid W] [Module R W] [Module A W]
  [IsScalarTower R A W] {ε : V ->ₗ[R] W} (ibc : IsBaseChange A ε)

/--
theorem `IsBaseChange.transvection` / 定理 `IsBaseChange.transvection`

English:
theorem IsBaseChange.transvection
  given: (f : Dual R V) (v : V)
  proof: by
  ext w
  induction w using ibc.inductionOn with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul a w hw => simp [hw]
  | tmul x => simp [LinearMap.transvection.apply, endHom_comp_apply, toDual_comp_apply]

中文:
定理 IsBaseChange.transvection
  条件: (f : 对偶 R V) (v : V)
  证明: by
  ext w
  induction w using ibc.inductionOn with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul a w hw => simp [hw]
  | tmul x => simp [LinearMap.transvection.apply, endHom_comp_apply, toDual_comp_apply]

Depends on / 依赖: LinearMap, LinearMap.transvection.apply, endHom_comp_apply, ibc.inductionOn, inductionOn, toDual_comp_apply, transvection
-/
theorem IsBaseChange.transvection (f : Dual R V) (v : V) :
    ibc.endHom (transvection f v) = transvection (ibc.toDual f) (ε v) := by
  ext w
  induction w using ibc.inductionOn with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul a w hw => simp [hw]
  | tmul x => simp [LinearMap.transvection.apply, endHom_comp_apply, toDual_comp_apply]

end

section

variable {R V A : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [CommRing A] [Algebra R A]
    {f : Module.Dual R V} {v : V} (h : f v = 0)
    {W : Type*} [AddCommMonoid W] [Module R W] [Module A W]
  [IsScalarTower R A W] {ε : V ->ₗ[R] W} (ibc : IsBaseChange A ε)

/--
theorem `LinearEquiv.transvection.baseChange` / 定理 `LinearEquiv.transvection.baseChange`

English:
theorem LinearEquiv.transvection.baseChange
  proof: by
  simp [← toLinearMap_inj, coe_baseChange,
    LinearEquiv.transvection.coe_toLinearMap, LinearMap.transvection.baseChange]

中文:
定理 线性等价.transvection.baseChange
  证明: by
  simp [← toLinearMap_inj, coe_baseChange,
    LinearEquiv.transvection.coe_toLinearMap, LinearMap.transvection.baseChange]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, LinearEquiv, LinearEquiv.transvection, LinearEquiv.transvection.coe_toLinearMap, LinearMap, LinearMap.transvection.baseChange, algebraMap_eq_smul_one, baseChange, coe_baseChange, coe_toLinearMap, toLinearMap_inj, transvection
-/
theorem LinearEquiv.transvection.baseChange
    (hA : f.baseChange A (1 otimesₜ[R] v) = 0 := by simp [Algebra.algebraMap_eq_smul_one]) :
    (LinearEquiv.transvection h).baseChange R A V V = LinearEquiv.transvection hA := by
  simp [← toLinearMap_inj, coe_baseChange,
    LinearEquiv.transvection.coe_toLinearMap, LinearMap.transvection.baseChange]

/--
theorem `LinearEquiv.dilatransvection.baseChange` / 定理 `LinearEquiv.dilatransvection.baseChange`

English:
theorem LinearEquiv.dilatransvection.baseChange
  statement: (e : V ≃ₗ[R] V)
  proof: by
  obtain ⟨f, v, he⟩ := he
  use (f.baseChange A), (1 otimesₜ[R] v)
  simp [he, LinearMap.transvection.baseChange]

中文:
定理 线性等价.dilatransvection.baseChange
  结论: (e : V ≃ₗ[R] V)
  证明: by
  obtain ⟨f, v, he⟩ := he
  use (f.baseChange A), (1 otimesₜ[R] v)
  simp [he, LinearMap.transvection.baseChange]

Depends on / 依赖: LinearMap, LinearMap.transvection.baseChange, baseChange, f.baseChange, transvection
-/
theorem LinearEquiv.dilatransvection.baseChange (e : V ≃ₗ[R] V)
    (he : e in LinearEquiv.dilatransvections R V) :
    e.baseChange R A V V in LinearEquiv.dilatransvections A (A otimes[R] V) := by
  obtain ⟨f, v, he⟩ := he
  use (f.baseChange A), (1 otimesₜ[R] v)
  simp [he, LinearMap.transvection.baseChange]

end

end baseChange

section determinant

namespace LinearMap.transvection

open Polynomial Module

open scoped TensorProduct

section Field

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]

/--
theorem `det_ofField` / 定理 `det_ofField`

English:
theorem det_ofField
  given: [FiniteDimensional K V] (f : Dual K V) (v : V)
  proof: by
  classical
  by_cases hfv : f v = 0
  · by_cases hv : v = 0
    · simp [hv]
    by_cases hf : f = 0
    · simp [hf]
    obtain ⟨ι, b, i, j, hi, hj⟩ := exists_basis_of_pairing_eq_zero hfv hf hv
    have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
    rw [← det_toMatrix b]
    suffices toMatrix b b (LinearMap.transvection f v) = Matrix.transvection i j 1 by
      rw [this]; rw [Matrix.det_transvection_of_ne i j hi 1]; rw [hfv]; rw [add_zero]
    ext x y
    rw [toMatrix_apply]; rw [transvection.apply]; rw [Matrix.transvection]
    simp only [hj.2, Basis.coord_apply, Basis.repr_self, hj.1, map_add, map_smul,
      Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_add, Pi.add_apply, Matrix.add_apply]
    apply congr_arg₂
    · by_cases h : x = y
      · rw [h]; simp
      · rw [Finsupp.single_eq_of_ne h, Matrix.one_apply_ne h]
    · by_cases h : i = x ∧ j = y
      · rw [h.1, h.2]; simp
      · rcases not_and_or.mp h with h' | h' <;>
          simp [Finsupp.single_eq_of_ne' h',
            Finsupp.single_eq_of_ne h',
            Matrix.single_apply_of_ne (h := h)]
  · obtain ⟨ι, b, i, hv, hf⟩ := exists_basis_of_pairing_ne_zero hfv
    have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
    rw [← det_toMatrix b]
    suffices toMatrix b b (transvection f v) =
      Matrix.diagonal (Function.update 1 i (1 + f v)) by
      rw [this]
      simp only [Matrix.det_diagonal]
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        simp [Function.update_of_ne hj]
      · simp
    ext x y
    rw [toMatrix_apply]; rw [transvection.apply]; rw [Matrix.diagonal]
    simp only [map_add, Basis.repr_self, map_smul, Finsupp.coe_add, Finsupp.coe_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    rw [hv]; rw [Function.update_apply]; rw [Basis.repr_self]; rw [Pi.one_apply]; rw [hf]
    simp only [smul_apply, Basis.coord_apply, Basis.repr_self, smul_eq_mul,
      Finsupp.single_eq_same, mul_one]
    split_ifs with hxy hxi
    · simp [← hxy, hxi]
    · rw [Finsupp.single_eq_of_ne hxi]; simp [hxy]
    · rw [Finsupp.single_eq_of_ne hxy, zero_add, mul_assoc]
      convert! mul_zero _
      by_cases hxi : x = i
      · simp [← hxi, Finsupp.single_eq_of_ne hxy]
      · simp [Finsupp.single_eq_of_ne hxi]

中文:
定理 det_ofField
  条件: [有限维 K V] (f : 对偶 K V) (v : V)
  证明: by
  classical
  by_cases hfv : f v = 0
  · by_cases hv : v = 0
    · simp [hv]
    by_cases hf : f = 0
    · simp [hf]
    obtain ⟨ι, b, i, j, hi, hj⟩ := exists_basis_of_pairing_eq_zero hfv hf hv
    have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
    rw [← det_toMatrix b]
    suffices toMatrix b b (LinearMap.transvection f v) = Matrix.transvection i j 1 by
      rw [this]; rw [Matrix.det_transvection_of_ne i j hi 1]; rw [hfv]; rw [add_zero]
    ext x y
    rw [toMatrix_apply]; rw [transvection.apply]; rw [Matrix.transvection]
    simp only [hj.2, Basis.coord_apply, Basis.repr_self, hj.1, map_add, map_smul,
      Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_add, Pi.add_apply, Matrix.add_apply]
    apply congr_arg₂
    · by_cases h : x = y
      · rw [h]; simp
      · rw [Finsupp.single_eq_of_ne h, Matrix.one_apply_ne h]
    · by_cases h : i = x ∧ j = y
      · rw [h.1, h.2]; simp
      · rcases not_and_or.mp h with h' | h' <;>
          simp [Finsupp.single_eq_of_ne' h',
            Finsupp.single_eq_of_ne h',
            Matrix.single_apply_of_ne (h := h)]
  · obtain ⟨ι, b, i, hv, hf⟩ := exists_basis_of_pairing_ne_zero hfv
    have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
    rw [← det_toMatrix b]
    suffices toMatrix b b (transvection f v) =
      Matrix.diagonal (Function.update 1 i (1 + f v)) by
      rw [this]
      simp only [Matrix.det_diagonal]
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        simp [Function.update_of_ne hj]
      · simp
    ext x y
    rw [toMatrix_apply]; rw [transvection.apply]; rw [Matrix.diagonal]
    simp only [map_add, Basis.repr_self, map_smul, Finsupp.coe_add, Finsupp.coe_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    rw [hv]; rw [Function.update_apply]; rw [Basis.repr_self]; rw [Pi.one_apply]; rw [hf]
    simp only [smul_apply, Basis.coord_apply, Basis.repr_self, smul_eq_mul,
      Finsupp.single_eq_same, mul_one]
    split_ifs with hxy hxi
    · simp [← hxy, hxi]
    · rw [Finsupp.single_eq_of_ne hxi]; simp [hxy]
    · rw [Finsupp.single_eq_of_ne hxy, zero_add, mul_assoc]
      convert! mul_zero _
      by_cases hxi : x = i
      · simp [← hxi, Finsupp.single_eq_of_ne hxy]
      · simp [Finsupp.single_eq_of_ne hxi]
-/
private theorem det_ofField [FiniteDimensional K V] (f : Dual K V) (v : V) :
    (LinearMap.transvection f v).det = 1 + f v := by
  classical
  by_cases hfv : f v = 0
  · by_cases hv : v = 0
    · simp [hv]
    by_cases hf : f = 0
    · simp [hf]
    obtain ⟨ι, b, i, j, hi, hj⟩ := exists_basis_of_pairing_eq_zero hfv hf hv
    have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
    rw [← det_toMatrix b]
    suffices toMatrix b b (LinearMap.transvection f v) = Matrix.transvection i j 1 by
      rw [this]; rw [Matrix.det_transvection_of_ne i j hi 1]; rw [hfv]; rw [add_zero]
    ext x y
    rw [toMatrix_apply]; rw [transvection.apply]; rw [Matrix.transvection]
    simp only [hj.2, Basis.coord_apply, Basis.repr_self, hj.1, map_add, map_smul,
      Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_add, Pi.add_apply, Matrix.add_apply]
    apply congr_arg₂
    · by_cases h : x = y
      · rw [h]; simp
      · rw [Finsupp.single_eq_of_ne h, Matrix.one_apply_ne h]
    · by_cases h : i = x ∧ j = y
      · rw [h.1, h.2]; simp
      · rcases not_and_or.mp h with h' | h' <;>
          simp [Finsupp.single_eq_of_ne' h',
            Finsupp.single_eq_of_ne h',
            Matrix.single_apply_of_ne (h := h)]
  · obtain ⟨ι, b, i, hv, hf⟩ := exists_basis_of_pairing_ne_zero hfv
    have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
    rw [← det_toMatrix b]
    suffices toMatrix b b (transvection f v) =
      Matrix.diagonal (Function.update 1 i (1 + f v)) by
      rw [this]
      simp only [Matrix.det_diagonal]
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        simp [Function.update_of_ne hj]
      · simp
    ext x y
    rw [toMatrix_apply]; rw [transvection.apply]; rw [Matrix.diagonal]
    simp only [map_add, Basis.repr_self, map_smul, Finsupp.coe_add, Finsupp.coe_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    rw [hv]; rw [Function.update_apply]; rw [Basis.repr_self]; rw [Pi.one_apply]; rw [hf]
    simp only [smul_apply, Basis.coord_apply, Basis.repr_self, smul_eq_mul,
      Finsupp.single_eq_same, mul_one]
    split_ifs with hxy hxi
    · simp [← hxy, hxi]
    · rw [Finsupp.single_eq_of_ne hxi]; simp [hxy]
    · rw [Finsupp.single_eq_of_ne hxy, zero_add, mul_assoc]
      convert! mul_zero _
      by_cases hxi : x = i
      · simp [← hxi, Finsupp.single_eq_of_ne hxy]
      · simp [Finsupp.single_eq_of_ne hxi]

end Field

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/--
theorem `det_ofDomain` / 定理 `det_ofDomain`

English:
theorem det_ofDomain
  given: [Free R V] [Module.Finite R V] [IsDomain R] (f : Dual R V) (v : V)
  proof: by
  let K := FractionRing R
  let : Field K := inferInstance
  apply FaithfulSMul.algebraMap_injective R K
  have := det_ofField (f.baseChange K) (1 otimesₜ[R] v)
  rw [← transvection.baseChange]; rw [det_baseChange]; rw [← algebraMap.coe_one (R := R) (A := K)] at this
  simpa [Algebra.algebraMap_eq_smul_one, add_smul] using this

中文:
定理 det_ofDomain
  条件: [自由 R V] [模.有限 R V] [是整环 R] (f : 对偶 R V) (v : V)
  证明: by
  let K := FractionRing R
  let : Field K := inferInstance
  apply FaithfulSMul.algebraMap_injective R K
  have := det_ofField (f.baseChange K) (1 otimesₜ[R] v)
  rw [← transvection.baseChange]; rw [det_baseChange]; rw [← algebraMap.coe_one (R := R) (A := K)] at this
  simpa [Algebra.algebraMap_eq_smul_one, add_smul] using this
-/
private theorem det_ofDomain [Free R V] [Module.Finite R V] [IsDomain R] (f : Dual R V) (v : V) :
    (transvection f v).det = 1 + f v := by
  let K := FractionRing R
  let : Field K := inferInstance
  apply FaithfulSMul.algebraMap_injective R K
  have := det_ofField (f.baseChange K) (1 otimesₜ[R] v)
  rw [← transvection.baseChange]; rw [det_baseChange]; rw [← algebraMap.coe_one (R := R) (A := K)] at this
  simpa [Algebra.algebraMap_eq_smul_one, add_smul] using this

open IsBaseChange

/--
theorem `det` / 定理 `det`

English:
theorem det
  given: [Free R V] [Module.Finite R V] (f : Dual R V) (v : V)
  proof: by
  rcases subsingleton_or_nontrivial R with hR | hR
  · subsingleton
  let b := finBasis R V
  set n := finrank R V
  let S := MvPolynomial (Fin n oplus Fin n) Int
  let γ : S ->+* R :=
    (MvPolynomial.aeval (Sum.elim (fun i => f (b i)) (fun i => b.coord i v)) :
      MvPolynomial (Fin n oplus Fin n) Int ->ₐ[Int] R)
  have : IsDomain S := inferInstance
  let _ : Algebra S R := RingHom.toAlgebra γ
  let _ : Module S V := compHom V γ
  have _ : IsScalarTower S R V := IsScalarTower.of_compHom S R V
  have ibc := IsBaseChange.of_fintype_basis S b
  set ε := Fintype.linearCombination S (fun i => b i)
  set M := Fin n -> S
  have hε (i) : ε (Pi.single i 1) = b i := by
    rw [Fintype.linearCombination_apply_single]; rw [one_smul]
  let fM : Dual S M :=
    Fintype.linearCombination S fun i => MvPolynomial.X (Sum.inl i)
  let vM : M := fun i => MvPolynomial.X (Sum.inr i)
  have hf : ibc.toDual fM = f := by
    apply b.ext
    intro i
    rw [← hε]; rw [toDual_comp_apply]; rw [Fintype.linearCombination_apply_single]; rw [one_smul]; rw [RingHom.algebraMap_toAlgebra]; rw [hε]
    apply MvPolynomial.aeval_X
  have hv : ε vM = v := by
    rw [of_fintype_basis_eq]
    ext i
    rw [RingHom.algebraMap_toAlgebra]
    simp only [vM, γ, Function.comp_apply]
    apply MvPolynomial.aeval_X
  rw [← hf]; rw [← hv]; rw [← IsBaseChange.transvection]; rw [det_endHom]; rw [det_ofDomain]
  rw [map_add]; rw [map_one]; rw [add_right_inj]; rw [toDual_comp_apply]

中文:
定理 det
  条件: [自由 R V] [模.有限 R V] (f : 对偶 R V) (v : V)
  证明: by
  rcases subsingleton_or_nontrivial R with hR | hR
  · subsingleton
  let b := finBasis R V
  set n := finrank R V
  let S := MvPolynomial (Fin n oplus Fin n) Int
  let γ : S ->+* R :=
    (MvPolynomial.aeval (Sum.elim (fun i => f (b i)) (fun i => b.coord i v)) :
      MvPolynomial (Fin n oplus Fin n) Int ->ₐ[Int] R)
  have : IsDomain S := inferInstance
  let _ : Algebra S R := RingHom.toAlgebra γ
  let _ : Module S V := compHom V γ
  have _ : IsScalarTower S R V := IsScalarTower.of_compHom S R V
  have ibc := IsBaseChange.of_fintype_basis S b
  set ε := Fintype.linearCombination S (fun i => b i)
  set M := Fin n -> S
  have hε (i) : ε (Pi.single i 1) = b i := by
    rw [Fintype.linearCombination_apply_single]; rw [one_smul]
  let fM : Dual S M :=
    Fintype.linearCombination S fun i => MvPolynomial.X (Sum.inl i)
  let vM : M := fun i => MvPolynomial.X (Sum.inr i)
  have hf : ibc.toDual fM = f := by
    apply b.ext
    intro i
    rw [← hε]; rw [toDual_comp_apply]; rw [Fintype.linearCombination_apply_single]; rw [one_smul]; rw [RingHom.algebraMap_toAlgebra]; rw [hε]
    apply MvPolynomial.aeval_X
  have hv : ε vM = v := by
    rw [of_fintype_basis_eq]
    ext i
    rw [RingHom.algebraMap_toAlgebra]
    simp only [vM, γ, Function.comp_apply]
    apply MvPolynomial.aeval_X
  rw [← hf]; rw [← hv]; rw [← IsBaseChange.transvection]; rw [det_endHom]; rw [det_ofDomain]
  rw [map_add]; rw [map_one]; rw [add_right_inj]; rw [toDual_comp_apply]
-/
@[simp] theorem det [Free R V] [Module.Finite R V] (f : Dual R V) (v : V) :
    (transvection f v).det = 1 + f v := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · subsingleton
  let b := finBasis R V
  set n := finrank R V
  let S := MvPolynomial (Fin n oplus Fin n) Int
  let γ : S ->+* R :=
    (MvPolynomial.aeval (Sum.elim (fun i => f (b i)) (fun i => b.coord i v)) :
      MvPolynomial (Fin n oplus Fin n) Int ->ₐ[Int] R)
  have : IsDomain S := inferInstance
  let _ : Algebra S R := RingHom.toAlgebra γ
  let _ : Module S V := compHom V γ
  have _ : IsScalarTower S R V := IsScalarTower.of_compHom S R V
  have ibc := IsBaseChange.of_fintype_basis S b
  set ε := Fintype.linearCombination S (fun i => b i)
  set M := Fin n -> S
  have hε (i) : ε (Pi.single i 1) = b i := by
    rw [Fintype.linearCombination_apply_single]; rw [one_smul]
  let fM : Dual S M :=
    Fintype.linearCombination S fun i => MvPolynomial.X (Sum.inl i)
  let vM : M := fun i => MvPolynomial.X (Sum.inr i)
  have hf : ibc.toDual fM = f := by
    apply b.ext
    intro i
    rw [← hε]; rw [toDual_comp_apply]; rw [Fintype.linearCombination_apply_single]; rw [one_smul]; rw [RingHom.algebraMap_toAlgebra]; rw [hε]
    apply MvPolynomial.aeval_X
  have hv : ε vM = v := by
    rw [of_fintype_basis_eq]
    ext i
    rw [RingHom.algebraMap_toAlgebra]
    simp only [vM, γ, Function.comp_apply]
    apply MvPolynomial.aeval_X
  rw [← hf]; rw [← hv]; rw [← IsBaseChange.transvection]; rw [det_endHom]; rw [det_ofDomain]
  rw [map_add]; rw [map_one]; rw [add_right_inj]; rw [toDual_comp_apply]

/--
theorem `_root_.LinearEquiv.transvection.det_eq_one` / 定理 `_root_.LinearEquiv.transvection.det_eq_one`

English:
theorem _root_.LinearEquiv.transvection.det_eq_one
  proof: by
  rw [← Units.val_inj]; rw [LinearEquiv.coe_det]; rw [LinearEquiv.transvection.coe_toLinearMap hfv]; rw [Units.val_one]
  by_contra! h
  have : Free R V := Free.of_det_ne_one h
  have : Module.Finite R V := finite_of_det_ne_one h
  apply h
  rw [transvection.det]; rw [hfv]; rw [add_zero]

中文:
定理 _root_.线性等价.transvection.det_eq_one
  证明: by
  rw [← Units.val_inj]; rw [LinearEquiv.coe_det]; rw [LinearEquiv.transvection.coe_toLinearMap hfv]; rw [Units.val_one]
  by_contra! h
  have : Free R V := Free.of_det_ne_one h
  have : Module.Finite R V := finite_of_det_ne_one h
  apply h
  rw [transvection.det]; rw [hfv]; rw [add_zero]
-/
@[simp] theorem _root_.LinearEquiv.transvection.det_eq_one
    {f : Dual R V} {v : V} (hfv : f v = 0) :
    (LinearEquiv.transvection hfv).det = 1 := by
  rw [← Units.val_inj]; rw [LinearEquiv.coe_det]; rw [LinearEquiv.transvection.coe_toLinearMap hfv]; rw [Units.val_one]
  by_contra! h
  have : Free R V := Free.of_det_ne_one h
  have : Module.Finite R V := finite_of_det_ne_one h
  apply h
  rw [transvection.det]; rw [hfv]; rw [add_zero]

end transvection

end LinearMap

end determinant

end
