/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, David Ledvinka
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Monoid

/-!
# Topological properties of units

This file contains lemmas about the topology of units in topological monoids,
including results about submonoid units and units of product spaces.
-/

@[expose] public section

open Units

/-- If a submonoid is open in a topological monoid, then its units form an open subset
of the units of the monoid. -/
@[to_additive /-- If a submonoid is open in a topological additive monoid,
then its additive units form an open subset of the additive units of the monoid. -/]
/-
**Submonoid.isOpen_units** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submonoid.isOpen_units {M : Type*} [TopologicalSpace M] [Monoid M] {U : Su
bmonoid M} (hU : IsOpen (U : Set M)) : IsOpen (U.units : Set Mˣ)
参数：hU : IsOpen (U : Set M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Units.continuous_val`：continuous_val : Continuous ((↑) : Mˣ -> M)
· 使用定理 `Units.continuous_coe_inv`：continuous_coe_inv : Continuous (fun u => ↑u⁻¹
 : Mˣ -> M)
-/
lemma Submonoid.isOpen_units {M : Type*} [TopologicalSpace M] [Monoid M]
    {U : Submonoid M} (hU : IsOpen (U : Set M)) : IsOpen (U.units : Set Mˣ) :=
  (hU.preimage Units.continuous_val).inter (hU.preimage Units.continuous_coe_inv)

/-- The isomorphism of topological groups between the units of a product and
the product of the units. -/
@[to_additive /-- The isomorphism of topological additive groups between the additive units of a
product and the product of the additive units. -/]
/-
**ContinuousMulEquiv.piUnits** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousMulEquiv.piUnits {ι : Type*} {M : ι -> Type*} [(i : ι) -> Monoid
 (M i)] [(i : ι) -> TopologicalSpace (M i)] : (Π i, M i)ˣ ≃ₜ* Π i, (M i)ˣ where 
__
参数：i : ι；M i；i : ι；M i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ContinuousMulEquiv.piUnits {ι : Type*}
    {M : ι → Type*} [(i : ι) → Monoid (M i)] [(i : ι) → TopologicalSpace (M i)] :
    (Π i, M i)ˣ ≃ₜ* Π i, (M i)ˣ where
  __ := MulEquiv.piUnits
  continuous_toFun := continuous_pi fun _ ↦ Units.continuous_iff.mpr
    ⟨continuous_apply _ |>.comp Units.continuous_val,
      continuous_apply _ |>.comp Units.continuous_coe_inv⟩
  continuous_invFun := Units.continuous_iff.mpr
    ⟨continuous_pi fun _ ↦ Units.continuous_val.comp <| continuous_apply _,
      continuous_pi fun _ ↦ Units.continuous_coe_inv.comp <| continuous_apply _⟩

namespace Units

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [Monoid M] [Monoid N]

/-- Any `ContinuousMulEquiv` induces a `ContinuousMulEquiv` on units. -/
@[simps! apply]
/-
**Units.mapContinuousMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：mapContinuousMulEquiv (f : M ≃ₜ* N) : Mˣ ≃ₜ* Nˣ
参数：f : M ≃ₜ* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any `ContinuousMulEquiv` induces a `ContinuousMulEquiv` on units.
-/
def mapContinuousMulEquiv (f : M ≃ₜ* N) : Mˣ ≃ₜ* Nˣ :=
  { __ := Units.mapEquiv f
    continuous_toFun := f.continuous.units_map _
    continuous_invFun := f.symm.continuous.units_map _ }

@[simp]
/-
**Units.symm_mapContinuousMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：symm_mapContinuousMulEquiv (f : M ≃ₜ* N) : (mapContinuousMulEquiv f).symm 
= mapContinuousMulEquiv f.symm
参数：f : M ≃ₜ* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_mapContinuousMulEquiv (f : M ≃ₜ* N) :
    (mapContinuousMulEquiv f).symm = mapContinuousMulEquiv f.symm := rfl

@[simp]
/-
**Units.toMulEquiv_mapContinuousMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：toMulEquiv_mapContinuousMulEquiv (f : M ≃ₜ* N) : (mapContinuousMulEquiv f 
: Mˣ ≃* Nˣ) = mapEquiv f
参数：f : M ≃ₜ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMulEquiv.instMulEquivClass`：∀ {M : Type u_1} {N : Type u_2} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace N] [inst_2 : Mul M]   [inst
_3 : Mul N], MulEquivClass…
-/
theorem toMulEquiv_mapContinuousMulEquiv (f : M ≃ₜ* N) :
    (mapContinuousMulEquiv f : Mˣ ≃* Nˣ) = mapEquiv f := rfl

end Units

