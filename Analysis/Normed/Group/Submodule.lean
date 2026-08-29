/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Analysis.Normed.Group.Basic

/-! # Submodules of normed groups -/

public section

variable {𝕜 E : Type*}

namespace Submodule

/--
Instance `seminormedAddCommGroup` / 实例 `seminormedAddCommGroup`

English:
instance seminormedAddCommGroup
  signature: [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]
  body: fast_instance% SeminormedAddCommGroup.induced _ _ s.subtype.toAddMonoidHom

中文:
实例 seminormedAddCommGroup
  签名: [环 𝕜] [SeminormedAddComm群 E] [模 𝕜 E]
  定义体: fast_instance% SeminormedAddCommGroup.induced _ _ s.subtype.toAddMonoidHom

Depends on / 依赖: SeminormedAddCommGroup, SeminormedAddCommGroup.induced, fast_instance, induced, s.subtype.toAddMonoidHom, subtype, toAddMonoidHom
-/
instance seminormedAddCommGroup [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]
    (s : Submodule 𝕜 E) : SeminormedAddCommGroup s :=
  fast_instance% SeminormedAddCommGroup.induced _ _ s.subtype.toAddMonoidHom

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `s` is equal to its
norm in `E`. -/
@[simp]
/--
theorem `coe_norm` / 定理 `coe_norm`

English:
theorem coe_norm
  statement: [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : Submodule 𝕜 E}
  proof: rfl

中文:
定理 coe_norm
  结论: [环 𝕜] [SeminormedAddComm群 E] [模 𝕜 E] {s : 子模 𝕜 E}
  证明: rfl
-/
theorem coe_norm [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : Submodule 𝕜 E}
    (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `E` is equal to its
norm in `s`.

This is a reversed version of the `simp` lemma `Submodule.coe_norm` for use by `norm_cast`. -/
@[norm_cast]
/--
theorem `norm_coe` / 定理 `norm_coe`

English:
theorem norm_coe
  statement: [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : Submodule 𝕜 E}
  proof: rfl

中文:
定理 norm_coe
  结论: [环 𝕜] [SeminormedAddComm群 E] [模 𝕜 E] {s : 子模 𝕜 E}
  证明: rfl
-/
theorem norm_coe [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : Submodule 𝕜 E}
    (x : s) : ‖(x : E)‖ = ‖x‖ :=
  rfl

/--
Instance `normedAddCommGroup` / 实例 `normedAddCommGroup`

English:
instance normedAddCommGroup
  signature: [Ring 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
  body: { Submodule.seminormedAddCommGroup s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
实例 normedAddCommGroup
  签名: [环 𝕜] [赋范交换加群 E] [模 𝕜 E]
  定义体: { Submodule.seminormedAddCommGroup s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: Submodule, Submodule.seminormedAddCommGroup, eq_of_dist_eq_zero, seminormedAddCommGroup
-/
instance normedAddCommGroup [Ring 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    (s : Submodule 𝕜 E) : NormedAddCommGroup s :=
  { Submodule.seminormedAddCommGroup s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

end Submodule

@[continuity, fun_prop]
/--
theorem `LinearMap.continuous_domRestrict` / 定理 `LinearMap.continuous_domRestrict`

English:
theorem LinearMap.continuous_domRestrict
  statement: {R R' M M' : Type*} [Semiring R] [Semiring R']
  proof: by
  rw [coe_domRestrict]
  fun_prop

中文:
定理 线性映射.continuous_domRestrict
  结论: {R R' M M' : 类型} [半环 R] [半环 R']
  证明: by
  rw [coe_domRestrict]
  fun_prop

Depends on / 依赖: coe_domRestrict, fun_prop
-/
theorem LinearMap.continuous_domRestrict {R R' M M' : Type*} [Semiring R] [Semiring R']
    [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R' M'] {σ₁₂ : R ->+* R'}
    (f : M ->ₛₗ[σ₁₂] M') [TopologicalSpace M] [TopologicalSpace M'] (hf : Continuous f)
    (p : Submodule R M) : Continuous (f.domRestrict p) := by
  rw [coe_domRestrict]
  fun_prop
