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

/-- A submodule of a seminormed group is also a seminormed group, with the restriction of the norm.
-/
/-
**Submodule.seminormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：seminormedAddCommGroup [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] (s
 : Submodule 𝕜 E) : SeminormedAddCommGroup s
参数：s : Submodule 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule of a seminormed group is also a seminormed group, with the restricti
on of the norm.
-/
instance seminormedAddCommGroup [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]
    (s : Submodule 𝕜 E) : SeminormedAddCommGroup s :=
  fast_instance% SeminormedAddCommGroup.induced _ _ s.subtype.toAddMonoidHom

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `s` is equal to its
norm in `E`. -/
@[simp]
/-
**Submodule.coe_norm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_norm [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : Submodule 𝕜
 E} (x : s) : ‖x‖ = ‖(x : E)‖
参数：x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x` is an element of a submodule `s` of a normed group `E`, its norm in `s` i
s equal to its
norm in `E`.
-/
theorem coe_norm [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : Submodule 𝕜 E}
    (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `E` is equal to its
norm in `s`.

This is a reversed version of the `simp` lemma `Submodule.coe_norm` for use by `norm_cast`. -/
@[norm_cast]
/-
**Submodule.norm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：norm_coe [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : Submodule 𝕜
 E} (x : s) : ‖(x : E)‖ = ‖x‖
参数：x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x` is an element of a submodule `s` of a normed group `E`, its norm in `E` i
s equal to its
norm in `s`.

This is a reversed version of the `simp` lemma `Submodule.coe_norm` for use by `
norm_cast`.
-/
theorem norm_coe [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : Submodule 𝕜 E}
    (x : s) : ‖(x : E)‖ = ‖x‖ :=
  rfl

/-- A submodule of a normed group is also a normed group, with the restriction of the norm. -/
/-
**Submodule.normedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：normedAddCommGroup [Ring 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] (s : Submo
dule 𝕜 E) : NormedAddCommGroup s
参数：s : Submodule 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule of a normed group is also a normed group, with the restriction of th
e norm.
-/
instance normedAddCommGroup [Ring 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    (s : Submodule 𝕜 E) : NormedAddCommGroup s :=
  { Submodule.seminormedAddCommGroup s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

end Submodule

@[continuity, fun_prop]
/-
**LinearMap.continuous_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.continuous_domRestrict {R R' M M' : Type*} [Semiring R] [Semirin
g R'] [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R' M'] {σ₁₂ : R 
->+* R'} (f : M ->ₛₗ[σ₁₂] M') [TopologicalSpace M] [TopologicalSpace M'] (hf : C
ontinuous f) (p : Submodule R M) : Continuous (f.domRestrict p)
参数：f : M ->ₛₗ[σ₁₂] M'；hf : Continuous f；p : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.coe_domRestrict`：coe_domRestrict (f : M ->ₛₗ[σ₁₂] M₂) (p : Sub
module R M) : ⇑(f.domRestrict p) = Set.domRestrict p f
· 使用定理 `Pi.continuous_domRestrict_apply`：Pi.continuous_domRestrict_apply (s : Se
t X) {f : X -> Z} (hf : Continuous f) : Continuous (s.domRestrict f)
-/
theorem LinearMap.continuous_domRestrict {R R' M M' : Type*} [Semiring R] [Semiring R']
    [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R' M'] {σ₁₂ : R →+* R'}
    (f : M →ₛₗ[σ₁₂] M') [TopologicalSpace M] [TopologicalSpace M'] (hf : Continuous f)
    (p : Submodule R M) : Continuous (f.domRestrict p) := by
  rw [coe_domRestrict]
  fun_prop
