/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Bases and scalar multiplication

This file defines the scalar multiplication of bases by multiplying each basis vector.

-/

@[expose] public section

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι R R₂ M : Type*}

namespace Module.Basis
variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

section SMul
variable {G G'}
variable [Group G] [Group G']
variable [DistribMulAction G M] [DistribMulAction G' M]
variable [SMulCommClass G R M] [SMulCommClass G' R M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul G (Basis ι R M)
  body: b.map DistribMulAction.toLinearEquiv _ _ g

@[simp]

中文:
实例 :
  签名: SMul G (Basis ι R M)
  定义体: b.map DistribMulAction.toLinearEquiv _ _ g

@[simp]

Depends on / 依赖: DistribMulAction, DistribMulAction.toLinearEquiv, b.map, toLinearEquiv
-/
instance : SMul G (Basis ι R M) where
smul g b := b.map DistribMulAction.toLinearEquiv _ _ g

@[simp]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (g : G) (b : Basis ι R M) (i : ι)
  statement: (g • b) i = g • b i
  proof: rfl

中文:
定理 smul_apply
  条件: (g : G) (b : Basis ι R M) (i : ι)
  结论: (g • b) i = g • b i
  证明: rfl
-/
theorem smul_apply (g : G) (b : Basis ι R M) (i : ι) : (g • b) i = g • b i := rfl

/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (g : G) (b : Basis ι R M)
  statement: ⇑(g • b) = g • ⇑b
  proof: rfl

中文:
定理 coe_smul
  条件: (g : G) (b : Basis ι R M)
  结论: ⇑(g • b) = g • ⇑b
  证明: rfl
-/
@[norm_cast] theorem coe_smul (g : G) (b : Basis ι R M) : ⇑(g • b) = g • ⇑b := rfl

/-- When the group in question is the automorphisms, `•` coincides with `Basis.map`. -/
@[simp]
/--
theorem `smul_eq_map` / 定理 `smul_eq_map`

English:
theorem smul_eq_map
  given: (g : M ≃ₗ[R] M) (b : Basis ι R M)
  statement: g • b = b.map g
  proof: rfl

中文:
定理 smul_eq_map
  条件: (g : M ≃ₗ[R] M) (b : Basis ι R M)
  结论: g • b = b.map g
  证明: rfl
-/
theorem smul_eq_map (g : M ≃ₗ[R] M) (b : Basis ι R M) : g • b = b.map g := rfl

/--
theorem `repr_smul` / 定理 `repr_smul`

English:
theorem repr_smul
  given: (g : G) (b : Basis ι R M)
  proof: rfl

中文:
定理 repr_smul
  条件: (g : G) (b : Basis ι R M)
  证明: rfl
-/
@[simp] theorem repr_smul (g : G) (b : Basis ι R M) :
    (g • b).repr = (DistribMulAction.toLinearEquiv _ _ g).symm.trans b.repr := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction G (Basis ι R M)
  body: Function.Injective.mulAction _ DFunLike.coe_injective coe_smul

中文:
实例 :
  签名: MulAction G (Basis ι R M)
  定义体: Function.Injective.mulAction _ DFunLike.coe_injective coe_smul

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Function, Function.Injective.mulAction, Injective, coe_injective, coe_smul, mulAction
-/
instance : MulAction G (Basis ι R M) :=
  Function.Injective.mulAction _ DFunLike.coe_injective coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: G G' M] : SMulCommClass G G' (Basis ι R M) where
  body: DFunLike.ext _ _ fun _ => smul_comm _ _ _

中文:
实例 [SMulCommClass
  签名: G G' M] : SMulCommClass G G' (Basis ι R M) where
  定义体: DFunLike.ext _ _ fun _ => smul_comm _ _ _

Depends on / 依赖: DFunLike, DFunLike.ext, smul_comm
-/
instance [SMulCommClass G G' M] : SMulCommClass G G' (Basis ι R M) where
  smul_comm _g _g' _b := DFunLike.ext _ _ fun _ => smul_comm _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: G G'] [IsScalarTower G G' M] : IsScalarTower G G' (Basis ι R M) where
  body: DFunLike.ext _ _ fun _ => smul_assoc _ _ _

中文:
实例 [SMul
  签名: G G'] [IsScalarTower G G' M] : IsScalarTower G G' (Basis ι R M) where
  定义体: DFunLike.ext _ _ fun _ => smul_assoc _ _ _

Depends on / 依赖: DFunLike, DFunLike.ext, smul_assoc
-/
instance [SMul G G'] [IsScalarTower G G' M] : IsScalarTower G G' (Basis ι R M) where
  smul_assoc _g _g' _b := DFunLike.ext _ _ fun _ => smul_assoc _ _ _

end SMul

section CommSemiring

variable {v : ι -> M} {x y : M}

/--
theorem `groupSMul_span_eq_top` / 定理 `groupSMul_span_eq_top`

English:
theorem groupSMul_span_eq_top
  statement: {G : Type*} [Group G] [SMul G R] [MulAction G M]
  proof: by
  rw [eq_top_iff]
  intro j hj
  rw [← hv] at hj
  rw [Submodule.mem_span] at hj ⊢
  refine fun p hp => hj p fun u hu => ?_
  obtain ⟨i, rfl⟩ := hu
  have : ((w i)⁻¹ • (1 : R)) • w i • v i in p := p.smul_mem ((w i)⁻¹ • (1 : R)) (hp ⟨i, rfl⟩)
  rwa [smul_one_smul, inv_smul_smul] at this

中文:
定理 groupSMul_span_eq_top
  结论: {G : 类型} [Group G] [SMul G R] [MulAction G M]
  证明: by
  rw [eq_top_iff]
  intro j hj
  rw [← hv] at hj
  rw [Submodule.mem_span] at hj ⊢
  refine fun p hp => hj p fun u hu => ?_
  obtain ⟨i, rfl⟩ := hu
  have : ((w i)⁻¹ • (1 : R)) • w i • v i in p := p.smul_mem ((w i)⁻¹ • (1 : R)) (hp ⟨i, rfl⟩)
  rwa [smul_one_smul, inv_smul_smul] at this

Depends on / 依赖: Submodule, Submodule.mem_span, eq_top_iff, inv_smul_smul, mem_span, p.smul_mem, smul_mem, smul_one_smul
-/
theorem groupSMul_span_eq_top {G : Type*} [Group G] [SMul G R] [MulAction G M]
    [IsScalarTower G R M] {v : ι -> M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι -> G} :
    Submodule.span R (Set.range (w • v)) = ⊤ := by
  rw [eq_top_iff]
  intro j hj
  rw [← hv] at hj
  rw [Submodule.mem_span] at hj ⊢
  refine fun p hp => hj p fun u hu => ?_
  obtain ⟨i, rfl⟩ := hu
  have : ((w i)⁻¹ • (1 : R)) • w i • v i in p := p.smul_mem ((w i)⁻¹ • (1 : R)) (hp ⟨i, rfl⟩)
  rwa [smul_one_smul, inv_smul_smul] at this

/--
Definition of `groupSMul` / `groupSMul` 的定义

English:
definition groupSMul
  signature: {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
  body: Basis.mk (LinearIndependent.group_smul v.linearIndependent w) (groupSMul_span_eq_top v.span_eq).ge

中文:
定义 groupSMul
  签名: {G : 类型} [Group G] [DistribMulAction G R] [DistribMulAction G M]
  定义体: Basis.mk (LinearIndependent.group_smul v.linearIndependent w) (groupSMul_span_eq_top v.span_eq).ge

Depends on / 依赖: Basis.mk, LinearIndependent, LinearIndependent.group_smul, groupSMul_span_eq_top, group_smul, linearIndependent, span_eq, v.linearIndependent, v.span_eq
-/
def groupSMul {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] (v : Basis ι R M) (w : ι -> G) : Basis ι R M :=
  Basis.mk (LinearIndependent.group_smul v.linearIndependent w) (groupSMul_span_eq_top v.span_eq).ge

/--
theorem `groupSMul_apply` / 定理 `groupSMul_apply`

English:
theorem groupSMul_apply
  statement: {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
  proof: mk_apply (LinearIndependent.group_smul v.linearIndependent w)
    (groupSMul_span_eq_top v.span_eq).ge i

中文:
定理 groupSMul_apply
  结论: {G : 类型} [Group G] [DistribMulAction G R] [DistribMulAction G M]
  证明: mk_apply (LinearIndependent.group_smul v.linearIndependent w)
    (groupSMul_span_eq_top v.span_eq).ge i

Depends on / 依赖: LinearIndependent, LinearIndependent.group_smul, groupSMul_span_eq_top, group_smul, linearIndependent, mk_apply, span_eq, v.linearIndependent, v.span_eq
-/
theorem groupSMul_apply {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] {v : Basis ι R M} {w : ι -> G} (i : ι) :
    v.groupSMul w i = (w • (v : ι -> M)) i :=
  mk_apply (LinearIndependent.group_smul v.linearIndependent w)
    (groupSMul_span_eq_top v.span_eq).ge i

/--
theorem `units_smul_span_eq_top` / 定理 `units_smul_span_eq_top`

English:
theorem units_smul_span_eq_top
  given: {v : ι -> M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι -> Rˣ}
  proof: groupSMul_span_eq_top hv

中文:
定理 units_smul_span_eq_top
  条件: {v : ι -> M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι -> Rˣ}
  证明: groupSMul_span_eq_top hv

Depends on / 依赖: groupSMul_span_eq_top
-/
theorem units_smul_span_eq_top {v : ι -> M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι -> Rˣ} :
    Submodule.span R (Set.range (w • v)) = ⊤ :=
  groupSMul_span_eq_top hv

/--
Definition of `unitsSMul` / `unitsSMul` 的定义

English:
definition unitsSMul
  signature: (v : Basis ι R M) (w : ι -> Rˣ)
  body: Basis.mk (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge

中文:
定义 unitsSMul
  签名: (v : Basis ι R M) (w : ι -> Rˣ)
  定义体: Basis.mk (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge

Depends on / 依赖: Basis.mk, LinearIndependent, LinearIndependent.units_smul, linearIndependent, span_eq, units_smul, units_smul_span_eq_top, v.linearIndependent, v.span_eq
-/
def unitsSMul (v : Basis ι R M) (w : ι -> Rˣ) : Basis ι R M :=
  Basis.mk (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge

/--
theorem `unitsSMul_apply` / 定理 `unitsSMul_apply`

English:
theorem unitsSMul_apply
  given: {v : Basis ι R M} {w : ι -> Rˣ} (i : ι)
  statement: unitsSMul v w i = w i • v i
  proof: mk_apply (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge i

中文:
定理 unitsSMul_apply
  条件: {v : Basis ι R M} {w : ι -> Rˣ} (i : ι)
  结论: unitsSMul v w i = w i • v i
  证明: mk_apply (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge i

Depends on / 依赖: LinearIndependent, LinearIndependent.units_smul, linearIndependent, mk_apply, span_eq, units_smul, units_smul_span_eq_top, v.linearIndependent, v.span_eq
-/
theorem unitsSMul_apply {v : Basis ι R M} {w : ι -> Rˣ} (i : ι) : unitsSMul v w i = w i • v i :=
  mk_apply (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge i

variable [CommSemiring R₂] [Module R₂ M]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `coord_unitsSMul` / 定理 `coord_unitsSMul`

English:
theorem coord_unitsSMul
  given: (e : Basis ι R₂ M) (w : ι -> R₂ˣ) (i : ι)
  proof: by
  classical
    apply e.ext
    intro j
    trans ((unitsSMul e w).coord i) ((w j)⁻¹ • (unitsSMul e w) j)
    · simp [Basis.unitsSMul, ← mul_smul]
    simp only [Basis.coord_apply, LinearMap.smul_apply, Basis.repr_self, Units.smul_def,
      map_smul, Finsupp.single_apply]
    split_ifs with h <;

中文:
定理 coord_unitsSMul
  条件: (e : Basis ι R₂ M) (w : ι -> R₂ˣ) (i : ι)
  证明: by
  classical
    apply e.ext
    intro j
    trans ((unitsSMul e w).coord i) ((w j)⁻¹ • (unitsSMul e w) j)
    · simp [Basis.unitsSMul, ← mul_smul]
    simp only [Basis.coord_apply, LinearMap.smul_apply, Basis.repr_self, Units.smul_def,
      map_smul, Finsupp.single_apply]
    split_ifs with h <;

Depends on / 依赖: Basis.coord_apply, Basis.repr_self, Basis.unitsSMul, Finsupp, Finsupp.single_apply, LinearMap, LinearMap.smul_apply, Units.smul_def, classical, coord_apply, e.ext, map_smul, mul_smul, repr_self, single_apply, smul_apply, smul_def, split_ifs, unitsSMul
-/
theorem coord_unitsSMul (e : Basis ι R₂ M) (w : ι -> R₂ˣ) (i : ι) :
    (unitsSMul e w).coord i = (w i)⁻¹ • e.coord i := by
  classical
    apply e.ext
    intro j
    trans ((unitsSMul e w).coord i) ((w j)⁻¹ • (unitsSMul e w) j)
    · simp [Basis.unitsSMul, ← mul_smul]
    simp only [Basis.coord_apply, LinearMap.smul_apply, Basis.repr_self, Units.smul_def,
      map_smul, Finsupp.single_apply]
    split_ifs with h <;> simp [h]

@[simp]
/--
theorem `repr_unitsSMul` / 定理 `repr_unitsSMul`

English:
theorem repr_unitsSMul
  given: (e : Basis ι R₂ M) (w : ι -> R₂ˣ) (v : M) (i : ι)
  proof: congr_arg (fun f : M ->ₗ[R₂] R₂ => f v) (e.coord_unitsSMul w i)

中文:
定理 repr_unitsSMul
  条件: (e : Basis ι R₂ M) (w : ι -> R₂ˣ) (v : M) (i : ι)
  证明: congr_arg (fun f : M ->ₗ[R₂] R₂ => f v) (e.coord_unitsSMul w i)

Depends on / 依赖: congr_arg, coord_unitsSMul, e.coord_unitsSMul
-/
theorem repr_unitsSMul (e : Basis ι R₂ M) (w : ι -> R₂ˣ) (v : M) (i : ι) :
    (e.unitsSMul w).repr v i = (w i)⁻¹ • e.repr v i :=
  congr_arg (fun f : M ->ₗ[R₂] R₂ => f v) (e.coord_unitsSMul w i)

/--
Definition of `isUnitSMul` / `isUnitSMul` 的定义

English:
definition isUnitSMul
  signature: (v : Basis ι R M) {w : ι -> R} (hw : forall i, IsUnit (w i))
  body: unitsSMul v fun i => (hw i).unit

中文:
定义 isUnitSMul
  签名: (v : Basis ι R M) {w : ι -> R} (hw : 对任意 i, IsUnit (w i))
  定义体: unitsSMul v fun i => (hw i).unit

Depends on / 依赖: unitsSMul
-/
def isUnitSMul (v : Basis ι R M) {w : ι -> R} (hw : forall i, IsUnit (w i)) : Basis ι R M :=
  unitsSMul v fun i => (hw i).unit

/--
theorem `isUnitSMul_apply` / 定理 `isUnitSMul_apply`

English:
theorem isUnitSMul_apply
  given: {v : Basis ι R M} {w : ι -> R} (hw : forall i, IsUnit (w i)) (i : ι)
  proof: unitsSMul_apply i

中文:
定理 isUnitSMul_apply
  条件: {v : Basis ι R M} {w : ι -> R} (hw : 对任意 i, IsUnit (w i)) (i : ι)
  证明: unitsSMul_apply i

Depends on / 依赖: unitsSMul_apply
-/
theorem isUnitSMul_apply {v : Basis ι R M} {w : ι -> R} (hw : forall i, IsUnit (w i)) (i : ι) :
    v.isUnitSMul hw i = w i • v i :=
  unitsSMul_apply i

/--
theorem `repr_isUnitSMul` / 定理 `repr_isUnitSMul`

English:
theorem repr_isUnitSMul
  given: {v : Basis ι R₂ M} {w : ι -> R₂} (hw : forall i, IsUnit (w i)) (x : M) (i : ι)
  proof: repr_unitsSMul _ _ _ _

中文:
定理 repr_isUnitSMul
  条件: {v : Basis ι R₂ M} {w : ι -> R₂} (hw : 对任意 i, IsUnit (w i)) (x : M) (i : ι)
  证明: repr_unitsSMul _ _ _ _

Depends on / 依赖: repr_unitsSMul
-/
theorem repr_isUnitSMul {v : Basis ι R₂ M} {w : ι -> R₂} (hw : forall i, IsUnit (w i)) (x : M) (i : ι) :
    (v.isUnitSMul hw).repr x i = (hw i).unit⁻¹ • v.repr x i :=
  repr_unitsSMul _ _ _ _

end CommSemiring
end Module.Basis
