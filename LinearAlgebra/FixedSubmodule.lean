/-
Copyright (c) 2026 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The fixed submodule of a linear map

- `LinearMap.fixedSubmodule`: the submodule of a linear map consisting of its fixed points.

-/

@[expose] public section

namespace LinearMap

variable {R : Type*} [Semiring R]
  {U V : Type*} [AddCommMonoid U] [AddCommMonoid V]
  [Module R U] [Module R V] (e : V ≃ₗ[R] V)


/--
Definition of `fixedSubmodule` / `fixedSubmodule` 的定义

English:
definition fixedSubmodule
  signature: (f : V ->ₗ[R] V)
  body: { x | f x = x }
  add_mem' {x y} hx hy := by aesop
  zero_mem' := by simp
  smul_mem' r x hx := by aesop

@[simp]

中文:
定义 fixedSubmodule
  签名: (f : V ->ₗ[R] V)
  定义体: { x | f x = x }
  add_mem' {x y} hx hy := by aesop
  zero_mem' := by simp
  smul_mem' r x hx := by aesop

@[simp]
-/
def fixedSubmodule (f : V ->ₗ[R] V) : Submodule R V where
  carrier := { x | f x = x }
  add_mem' {x y} hx hy := by aesop
  zero_mem' := by simp
  smul_mem' r x hx := by aesop

@[simp]
/--
theorem `mem_fixedSubmodule_iff` / 定理 `mem_fixedSubmodule_iff`

English:
theorem mem_fixedSubmodule_iff
  given: {f : V ->ₗ[R] V} {v : V}
  proof: by
  simp [fixedSubmodule]

中文:
定理 mem_fixedSubmodule_iff
  条件: {f : V ->ₗ[R] V} {v : V}
  证明: by
  simp [fixedSubmodule]

Depends on / 依赖: fixedSubmodule
-/
theorem mem_fixedSubmodule_iff {f : V ->ₗ[R] V} {v : V} :
    v in f.fixedSubmodule ↔ f v = v := by
  simp [fixedSubmodule]

/--
theorem `fixedSubmodule_eq_ker` / 定理 `fixedSubmodule_eq_ker`

English:
theorem fixedSubmodule_eq_ker
  statement: {R : Type*} [Ring R]
  proof: by
  ext; simp [sub_eq_zero]

中文:
定理 fixedSubmodule_eq_ker
  结论: {R : 类型} [环 R]
  证明: by
  ext; simp [sub_eq_zero]

Depends on / 依赖: sub_eq_zero
-/
theorem fixedSubmodule_eq_ker {R : Type*} [Ring R]
    {V : Type*} [AddCommGroup V] [Module R V] (f : V ->ₗ[R] V) :
    f.fixedSubmodule = LinearMap.ker (f - id (R := R)) := by
  ext; simp [sub_eq_zero]

/--
theorem `fixedSubmodule_eq_top_iff` / 定理 `fixedSubmodule_eq_top_iff`

English:
theorem fixedSubmodule_eq_top_iff
  given: {f : V ->ₗ[R] V}
  proof: by
  simp [LinearMap.ext_iff, Submodule.ext_iff]

中文:
定理 fixedSubmodule_eq_top_iff
  条件: {f : V ->ₗ[R] V}
  证明: by
  simp [LinearMap.ext_iff, Submodule.ext_iff]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, Submodule, Submodule.ext_iff, ext_iff
-/
theorem fixedSubmodule_eq_top_iff {f : V ->ₗ[R] V} :
    f.fixedSubmodule = ⊤ ↔ f = id (R := R) := by
  simp [LinearMap.ext_iff, Submodule.ext_iff]

/--
theorem `fixedSubmodule_inf_fixedSubmodule_le_comp` / 定理 `fixedSubmodule_inf_fixedSubmodule_le_comp`

English:
theorem fixedSubmodule_inf_fixedSubmodule_le_comp
  given: (f g : V ->ₗ[R] V)
  proof: by
  intro; simp_all

中文:
定理 fixedSubmodule_inf_fixedSubmodule_le_comp
  条件: (f g : V ->ₗ[R] V)
  证明: by
  intro; simp_all
-/
theorem fixedSubmodule_inf_fixedSubmodule_le_comp (f g : V ->ₗ[R] V) :
    f.fixedSubmodule ⊓ g.fixedSubmodule <= (f ∘ₗ g).fixedSubmodule := by
  intro; simp_all

/--
theorem `fixedSubmodule_comp_inf_fixedSubmodule_le` / 定理 `fixedSubmodule_comp_inf_fixedSubmodule_le`

English:
theorem fixedSubmodule_comp_inf_fixedSubmodule_le
  given: (f g : V ->ₗ[R] V)
  proof: by intro; aesop

中文:
定理 fixedSubmodule_comp_inf_fixedSubmodule_le
  条件: (f g : V ->ₗ[R] V)
  证明: by intro; aesop
-/
theorem fixedSubmodule_comp_inf_fixedSubmodule_le (f g : V ->ₗ[R] V) :
    (f ∘ₗ g).fixedSubmodule ⊓ g.fixedSubmodule <= f.fixedSubmodule := by intro; aesop

end LinearMap

namespace LinearEquiv

open scoped Pointwise
open LinearMap Submodule MulAction

variable {R : Type*} [Semiring R]
  {U V : Type*} [AddCommMonoid U] [AddCommMonoid V]
  [Module R U] [Module R V] (e : V ≃ₗ[R] V)

variable {P : Submodule R U} {Q : Submodule R V}

/--
theorem `fixedSubmodule_eq_top_iff` / 定理 `fixedSubmodule_eq_top_iff`

English:
theorem fixedSubmodule_eq_top_iff
  given: {f : V ≃ₗ[R] V}
  proof: by
  simp [LinearEquiv.ext_iff, Submodule.ext_iff]

中文:
定理 fixedSubmodule_eq_top_iff
  条件: {f : V ≃ₗ[R] V}
  证明: by
  simp [LinearEquiv.ext_iff, Submodule.ext_iff]

Depends on / 依赖: LinearEquiv, LinearEquiv.ext_iff, Submodule, Submodule.ext_iff, ext_iff
-/
theorem fixedSubmodule_eq_top_iff {f : V ≃ₗ[R] V} :
    f.fixedSubmodule = ⊤ ↔ f = .refl R V := by
  simp [LinearEquiv.ext_iff, Submodule.ext_iff]

/--
theorem `mem_stabilizer_submodule_of_le_fixedSubmodule` / 定理 `mem_stabilizer_submodule_of_le_fixedSubmodule`

English:
theorem mem_stabilizer_submodule_of_le_fixedSubmodule
  proof: by
  rw [mem_stabilizer_submodule_iff_map_eq]
  apply le_antisymm
  · rintro _ ⟨x, hx : x in W, rfl⟩
    suffices e x = x by simpa [this, coe_coe]
    rw [← coe_toLinearMap]; rw [← mem_fixedSubmodule_iff]
    exact hW hx
  · intro x hx
    refine ⟨x, hx, ?_⟩
    simp only [DistribSMul.toLinearMap_ap

中文:
定理 mem_stabilizer_submodule_of_le_fixedSubmodule
  证明: by
  rw [mem_stabilizer_submodule_iff_map_eq]
  apply le_antisymm
  · rintro _ ⟨x, hx : x in W, rfl⟩
    suffices e x = x by simpa [this, coe_coe]
    rw [← coe_toLinearMap]; rw [← mem_fixedSubmodule_iff]
    exact hW hx
  · intro x hx
    refine ⟨x, hx, ?_⟩
    simp only [DistribSMul.toLinearMap_ap

Depends on / 依赖: DistribSMul, DistribSMul.toLinearMap_apply, LinearEquiv, LinearEquiv.smul_def, coe_coe, coe_toLinearMap, le_antisymm, mem_fixedSubmodule_iff, mem_stabilizer_submodule_iff_map_eq, smul_def, toLinearMap_apply
-/
theorem mem_stabilizer_submodule_of_le_fixedSubmodule
    {e : V ≃ₗ[R] V} {W : Submodule R V} (hW : W <= LinearMap.fixedSubmodule e) :
    e in stabilizer (V ≃ₗ[R] V) W := by
  rw [mem_stabilizer_submodule_iff_map_eq]
  apply le_antisymm
  · rintro _ ⟨x, hx : x in W, rfl⟩
    suffices e x = x by simpa [this, coe_coe]
    rw [← coe_toLinearMap]; rw [← mem_fixedSubmodule_iff]
    exact hW hx
  · intro x hx
    refine ⟨x, hx, ?_⟩
    simp only [DistribSMul.toLinearMap_apply, LinearEquiv.smul_def]
    rw [← coe_toLinearMap]; rw [← mem_fixedSubmodule_iff]
    exact hW hx

/--
theorem `mem_stabilizer_fixedSubmodule` / 定理 `mem_stabilizer_fixedSubmodule`

English:
theorem mem_stabilizer_fixedSubmodule
  given: (e : V ≃ₗ[R] V)
  proof: mem_stabilizer_submodule_of_le_fixedSubmodule (le_refl _)

中文:
定理 mem_stabilizer_fixedSubmodule
  条件: (e : V ≃ₗ[R] V)
  证明: mem_stabilizer_submodule_of_le_fixedSubmodule (le_refl _)

Depends on / 依赖: le_refl, mem_stabilizer_submodule_of_le_fixedSubmodule
-/
theorem mem_stabilizer_fixedSubmodule (e : V ≃ₗ[R] V) :
    e in stabilizer _ e.fixedSubmodule :=
  mem_stabilizer_submodule_of_le_fixedSubmodule (le_refl _)

/--
theorem `map_eq_of_mem_fixingSubgroup` / 定理 `map_eq_of_mem_fixingSubgroup`

English:
theorem map_eq_of_mem_fixingSubgroup
  statement: (W : Submodule R V)
  proof: by
  ext v
  simp only [mem_fixingSubgroup_iff, carrier_eq_coe, SetLike.mem_coe, LinearEquiv.smul_def] at he
  refine ⟨fun ⟨w, hv, hv'⟩ => ?_, fun hv => ?_⟩
  · simp only [SetLike.mem_coe, coe_coe] at hv hv'
    rwa [← hv', he w hv]
  · refine ⟨v, hv, he v hv⟩

中文:
定理 map_eq_of_mem_fixingSubgroup
  结论: (W : 子模 R V)
  证明: by
  ext v
  simp only [mem_fixingSubgroup_iff, carrier_eq_coe, SetLike.mem_coe, LinearEquiv.smul_def] at he
  refine ⟨fun ⟨w, hv, hv'⟩ => ?_, fun hv => ?_⟩
  · simp only [SetLike.mem_coe, coe_coe] at hv hv'
    rwa [← hv', he w hv]
  · refine ⟨v, hv, he v hv⟩

Depends on / 依赖: LinearEquiv, LinearEquiv.smul_def, SetLike, SetLike.mem_coe, carrier_eq_coe, coe_coe, mem_coe, mem_fixingSubgroup_iff, smul_def
-/
theorem map_eq_of_mem_fixingSubgroup (W : Submodule R V)
    (he : e in fixingSubgroup _ W.carrier) :
    map e.toLinearMap W = W := by
  ext v
  simp only [mem_fixingSubgroup_iff, carrier_eq_coe, SetLike.mem_coe, LinearEquiv.smul_def] at he
  refine ⟨fun ⟨w, hv, hv'⟩ => ?_, fun hv => ?_⟩
  · simp only [SetLike.mem_coe, coe_coe] at hv hv'
    rwa [← hv', he w hv]
  · refine ⟨v, hv, he v hv⟩

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `reduce` / `reduce` 的定义

English:
definition reduce
  signature: (W : Submodule R V)
  body: Quotient.equiv W W u.val u.prop
  map_mul' u v := by
    ext x
    obtain ⟨y, rfl⟩ := W.mkQ_surjective x
    simp
  map_one' := by aesop

@[simp]

中文:
定义 reduce
  签名: (W : 子模 R V)
  定义体: Quotient.equiv W W u.val u.prop
  map_mul' u v := by
    ext x
    obtain ⟨y, rfl⟩ := W.mkQ_surjective x
    simp
  map_one' := by aesop

@[simp]

Depends on / 依赖: Quotient, Quotient.equiv, u.prop, u.val
-/
def reduce (W : Submodule R V) : stabilizer (V ≃ₗ[R] V) W ->* (V ⧸ W) ≃ₗ[R] (V ⧸ W) where
  toFun u := Quotient.equiv W W u.val u.prop
  map_mul' u v := by
    ext x
    obtain ⟨y, rfl⟩ := W.mkQ_surjective x
    simp
  map_one' := by aesop

@[simp]
/--
theorem `reduce_mk` / 定理 `reduce_mk`

English:
theorem reduce_mk
  given: (W : Submodule R V) (u : stabilizer (V ≃ₗ[R] V) W) (x : V)
  proof: rfl

中文:
定理 reduce_mk
  条件: (W : 子模 R V) (u : stabilizer (V ≃ₗ[R] V) W) (x : V)
  证明: rfl
-/
theorem reduce_mk (W : Submodule R V) (u : stabilizer (V ≃ₗ[R] V) W) (x : V) :
    reduce W u (Submodule.Quotient.mk x) = Submodule.Quotient.mk (u.val x) :=
  rfl

/--
theorem `reduce_mkQ` / 定理 `reduce_mkQ`

English:
theorem reduce_mkQ
  given: (W : Submodule R V) (u : stabilizer (V ≃ₗ[R] V) W) (x : V)
  proof: rfl

中文:
定理 reduce_mkQ
  条件: (W : 子模 R V) (u : stabilizer (V ≃ₗ[R] V) W) (x : V)
  证明: rfl
-/
theorem reduce_mkQ (W : Submodule R V) (u : stabilizer (V ≃ₗ[R] V) W) (x : V) :
    reduce W u (W.mkQ x) = W.mkQ (u.val x) :=
  rfl

/--
Definition of `fixedReduce` / `fixedReduce` 的定义

English:
definition fixedReduce
  signature: (e : V ≃ₗ[R] V)
  body: reduce e.fixedSubmodule ⟨e, e.mem_stabilizer_fixedSubmodule⟩

@[simp]

中文:
定义 fixedReduce
  签名: (e : V ≃ₗ[R] V)
  定义体: reduce e.fixedSubmodule ⟨e, e.mem_stabilizer_fixedSubmodule⟩

@[simp]

Depends on / 依赖: e.fixedSubmodule, e.mem_stabilizer_fixedSubmodule, fixedSubmodule, mem_stabilizer_fixedSubmodule
-/
def fixedReduce (e : V ≃ₗ[R] V) :
    (V ⧸ e.fixedSubmodule) ≃ₗ[R] V ⧸ e.fixedSubmodule :=
  reduce e.fixedSubmodule ⟨e, e.mem_stabilizer_fixedSubmodule⟩

@[simp]
/--
theorem `fixedReduce_mk` / 定理 `fixedReduce_mk`

English:
theorem fixedReduce_mk
  given: (e : V ≃ₗ[R] V) (x : V)
  proof: rfl

@[simp]

中文:
定理 fixedReduce_mk
  条件: (e : V ≃ₗ[R] V) (x : V)
  证明: rfl

@[simp]
-/
theorem fixedReduce_mk (e : V ≃ₗ[R] V) (x : V) :
    fixedReduce e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) :=
  rfl

@[simp]
/--
theorem `fixedReduce_mkQ` / 定理 `fixedReduce_mkQ`

English:
theorem fixedReduce_mkQ
  given: (e : V ≃ₗ[R] V) (x : V)
  proof: rfl

中文:
定理 fixedReduce_mkQ
  条件: (e : V ≃ₗ[R] V) (x : V)
  证明: rfl
-/
theorem fixedReduce_mkQ (e : V ≃ₗ[R] V) (x : V) :
    fixedReduce e (e.fixedSubmodule.mkQ x) = e.fixedSubmodule.mkQ (e x) :=
  rfl

/--
theorem `fixedReduce_eq_smul_iff` / 定理 `fixedReduce_eq_smul_iff`

English:
theorem fixedReduce_eq_smul_iff
  given: (e : V ≃ₗ[R] V) (a : R)
  proof: by
  simp only [← e.fixedSubmodule.ker_mkQ, mem_ker, map_sub, ← fixedReduce_mkQ, sub_eq_zero]
  constructor
  · intro H x; simp [H]
  · intro H x
    have ⟨y, hy⟩ := e.fixedSubmodule.mkQ_surjective x
    rw [← hy]
    apply H

中文:
定理 fixedReduce_eq_smul_iff
  条件: (e : V ≃ₗ[R] V) (a : R)
  证明: by
  simp only [← e.fixedSubmodule.ker_mkQ, mem_ker, map_sub, ← fixedReduce_mkQ, sub_eq_zero]
  constructor
  · intro H x; simp [H]
  · intro H x
    have ⟨y, hy⟩ := e.fixedSubmodule.mkQ_surjective x
    rw [← hy]
    apply H

Depends on / 依赖: e.fixedSubmodule.ker_mkQ, e.fixedSubmodule.mkQ_surjective, fixedReduce_mkQ, fixedSubmodule, ker_mkQ, map_sub, mem_ker, mkQ_surjective, sub_eq_zero
-/
theorem fixedReduce_eq_smul_iff (e : V ≃ₗ[R] V) (a : R) :
    (forall x, e.fixedReduce x = a • x) ↔
      forall v, e v - a • v in e.fixedSubmodule := by
  simp only [← e.fixedSubmodule.ker_mkQ, mem_ker, map_sub, ← fixedReduce_mkQ, sub_eq_zero]
  constructor
  · intro H x; simp [H]
  · intro H x
    have ⟨y, hy⟩ := e.fixedSubmodule.mkQ_surjective x
    rw [← hy]
    apply H

/--
theorem `fixedReduce_eq_one` / 定理 `fixedReduce_eq_one`

English:
theorem fixedReduce_eq_one
  given: (e : V ≃ₗ[R] V)
  proof: by
  simpa [LinearEquiv.ext_iff] using fixedReduce_eq_smul_iff e 1

中文:
定理 fixedReduce_eq_one
  条件: (e : V ≃ₗ[R] V)
  证明: by
  simpa [LinearEquiv.ext_iff] using fixedReduce_eq_smul_iff e 1

Depends on / 依赖: LinearEquiv, LinearEquiv.ext_iff, ext_iff, fixedReduce_eq_smul_iff
-/
theorem fixedReduce_eq_one (e : V ≃ₗ[R] V) :
    e.fixedReduce = LinearEquiv.refl R _ ↔ forall v, e v - v in e.fixedSubmodule := by
  simpa [LinearEquiv.ext_iff] using fixedReduce_eq_smul_iff e 1

end LinearEquiv

end
