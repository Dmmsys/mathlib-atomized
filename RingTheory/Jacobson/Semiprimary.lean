/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Semiprimary rings

## Main definition

* `IsSemiprimaryRing R`: a ring `R` is semiprimary if
  `Ring.jacobson R` is nilpotent and `R ⧸ Ring.jacobson R` is semisimple.
-/

public section

variable (R R₂ M M₂ : Type*) [Ring R] [Ring R₂]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]
variable {τ₁₂ : R ->+* R₂} [RingHomSurjective τ₁₂]

/--
theorem `IsSimpleModule.jacobson_eq_bot` / 定理 `IsSimpleModule.jacobson_eq_bot`

English:
theorem IsSimpleModule.jacobson_eq_bot
  given: [IsSimpleModule R M]
  statement: Module.jacobson R M = ⊥
  proof: le_bot_iff.mp sInf_le isCoatom_bot

中文:
定理 是单模.jacobson_eq_bot
  条件: [是单模 R M]
  结论: 模.jacobson R M = ⊥
  证明: le_bot_iff.mp sInf_le isCoatom_bot

Depends on / 依赖: isCoatom_bot, le_bot_iff, le_bot_iff.mp, sInf_le
-/
theorem IsSimpleModule.jacobson_eq_bot [IsSimpleModule R M] : Module.jacobson R M = ⊥ :=
le_bot_iff.mp sInf_le isCoatom_bot

/--
theorem `IsSemisimpleModule.jacobson_eq_bot` / 定理 `IsSemisimpleModule.jacobson_eq_bot`

English:
theorem IsSemisimpleModule.jacobson_eq_bot
  given: [IsSemisimpleModule R M]
  proof: have ⟨s, e, simple⟩ := isSemisimpleModule_iff_exists_linearEquiv_dfinsupp.mp ‹_›
  let f : M ->ₗ[R] forall m : s, m.1 := (LinearMap.pi DFinsupp.lapply).comp e.toLinearMap
  Module.jacobson_eq_bot_of_injective f (DFinsupp.injective_pi_lapply (R := R).comp e.injective)
    (Module.jacobson_pi_eq_bot _ _ fun i => IsSimpleModule.jacobson_eq_bot R _)

中文:
定理 是半单模.jacobson_eq_bot
  条件: [是半单模 R M]
  证明: have ⟨s, e, simple⟩ := isSemisimpleModule_iff_exists_linearEquiv_dfinsupp.mp ‹_›
  let f : M ->ₗ[R] forall m : s, m.1 := (LinearMap.pi DFinsupp.lapply).comp e.toLinearMap
  Module.jacobson_eq_bot_of_injective f (DFinsupp.injective_pi_lapply (R := R).comp e.injective)
    (Module.jacobson_pi_eq_bot _ _ fun i => IsSimpleModule.jacobson_eq_bot R _)

Depends on / 依赖: DFinsupp, DFinsupp.injective_pi_lapply, DFinsupp.lapply, IsSimpleModule, IsSimpleModule.jacobson_eq_bot, LinearMap, LinearMap.pi, Module, Module.jacobson_eq_bot_of_injective, Module.jacobson_pi_eq_bot, e.injective, e.toLinearMap, injective, injective_pi_lapply, isSemisimpleModule_iff_exists_linearEquiv_dfinsupp, isSemisimpleModule_iff_exists_linearEquiv_dfinsupp.mp, jacobson_eq_bot, jacobson_eq_bot_of_injective, jacobson_pi_eq_bot, lapply
-/
theorem IsSemisimpleModule.jacobson_eq_bot [IsSemisimpleModule R M] :
    Module.jacobson R M = ⊥ :=
  have ⟨s, e, simple⟩ := isSemisimpleModule_iff_exists_linearEquiv_dfinsupp.mp ‹_›
  let f : M ->ₗ[R] forall m : s, m.1 := (LinearMap.pi DFinsupp.lapply).comp e.toLinearMap
  Module.jacobson_eq_bot_of_injective f (DFinsupp.injective_pi_lapply (R := R).comp e.injective)
    (Module.jacobson_pi_eq_bot _ _ fun i => IsSimpleModule.jacobson_eq_bot R _)

/--
theorem `IsSemisimpleRing.jacobson_eq_bot` / 定理 `IsSemisimpleRing.jacobson_eq_bot`

English:
theorem IsSemisimpleRing.jacobson_eq_bot
  given: [IsSemisimpleRing R]
  statement: Ring.jacobson R = ⊥
  proof: IsSemisimpleModule.jacobson_eq_bot R R

中文:
定理 IsSemisimpleRing.jacobson_eq_bot
  条件: [IsSemisimpleRing R]
  结论: 环.jacobson R = ⊥
  证明: IsSemisimpleModule.jacobson_eq_bot R R

Depends on / 依赖: IsSemisimpleModule, IsSemisimpleModule.jacobson_eq_bot, jacobson_eq_bot
-/
theorem IsSemisimpleRing.jacobson_eq_bot [IsSemisimpleRing R] : Ring.jacobson R = ⊥ :=
  IsSemisimpleModule.jacobson_eq_bot R R

/--
theorem `IsSemisimpleModule.jacobson_le_ker` / 定理 `IsSemisimpleModule.jacobson_le_ker`

English:
theorem IsSemisimpleModule.jacobson_le_ker
  given: [IsSemisimpleModule R₂ M₂] (f : M ->ₛₗ[τ₁₂] M₂)
  proof: (Module.le_comap_jacobson f).trans by simp_rw [jacobson_eq_bot, LinearMap.ker, le_rfl]

中文:
定理 是半单模.jacobson_le_ker
  条件: [是半单模 R₂ M₂] (f : M ->ₛₗ[τ₁₂] M₂)
  证明: (Module.le_comap_jacobson f).trans by simp_rw [jacobson_eq_bot, LinearMap.ker, le_rfl]

Depends on / 依赖: LinearMap, LinearMap.ker, Module, Module.le_comap_jacobson, jacobson_eq_bot, le_comap_jacobson, le_rfl, simp_rw
-/
theorem IsSemisimpleModule.jacobson_le_ker [IsSemisimpleModule R₂ M₂] (f : M ->ₛₗ[τ₁₂] M₂) :
    Module.jacobson R M <= LinearMap.ker f :=
(Module.le_comap_jacobson f).trans by simp_rw [jacobson_eq_bot, LinearMap.ker, le_rfl]

/--
theorem `IsSemisimpleModule.jacobson_le_annihilator` / 定理 `IsSemisimpleModule.jacobson_le_annihilator`

English:
theorem IsSemisimpleModule.jacobson_le_annihilator
  given: [IsSemisimpleModule R M]
  proof: fun r hr => Module.mem_annihilator.mpr fun m => by
    have := Module.le_comap_jacobson (LinearMap.toSpanSingleton R M m) hr
    rwa [jacobson_eq_bot] at this

中文:
定理 是半单模.jacobson_le_annihilator
  条件: [是半单模 R M]
  证明: fun r hr => Module.mem_annihilator.mpr fun m => by
    have := Module.le_comap_jacobson (LinearMap.toSpanSingleton R M m) hr
    rwa [jacobson_eq_bot] at this

Depends on / 依赖: LinearMap, LinearMap.toSpanSingleton, Module, Module.le_comap_jacobson, Module.mem_annihilator.mpr, jacobson_eq_bot, le_comap_jacobson, mem_annihilator, toSpanSingleton
-/
theorem IsSemisimpleModule.jacobson_le_annihilator [IsSemisimpleModule R M] :
    Ring.jacobson R <= Module.annihilator R M :=
  fun r hr => Module.mem_annihilator.mpr fun m => by
    have := Module.le_comap_jacobson (LinearMap.toSpanSingleton R M m) hr
    rwa [jacobson_eq_bot] at this

instance (priority := low) (R) [CommRing R] [IsSemisimpleRing R] : IsReduced R where
eq_zero _ := fun ⟨n, eq⟩ => (IsSemisimpleRing.jacobson_eq_bot R).le Ideal.mem_sInf.mpr
    fun I hI => (Ideal.isMaximal_def.mpr hI).isPrime.mem_of_pow_mem n (eq ▸ I.zero_mem)

/--
Definition of `IsSemiprimaryRing` / `IsSemiprimaryRing` 的定义

English:
class IsSemiprimaryRing
  parameters: : Prop where
  axioms and operations (2):
    - isSemisimpleRing : IsSemisimpleRing (R ⧸ Ring.jacobson R)
    - isNilpotent : IsNilpotent (Ring.jacobson R)

中文:
类 是Semiprimary环
  参数: : 命题 where
  公理与运算 (2 个):
    - isSemisimpleRing : IsSemisimpleRing (R ⧸ 环.jacobson R)
    - isNilpotent : 是幂零 (环.jacobson R)
-/
@[mk_iff] class IsSemiprimaryRing : Prop where
  isSemisimpleRing : IsSemisimpleRing (R ⧸ Ring.jacobson R)
  isNilpotent : IsNilpotent (Ring.jacobson R)

attribute [instance] IsSemiprimaryRing.isSemisimpleRing
