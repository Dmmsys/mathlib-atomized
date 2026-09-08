/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# The span of a single vector

The equivalence of `𝕜` and `𝕜 • x` for `x ≠ 0` are defined as continuous linear equivalence and
isometry.

## Main definitions

* `ContinuousLinearEquiv.toSpanNonzeroSingleton`: The continuous linear equivalence between `𝕜` and
  `𝕜 • x` for `x ≠ 0`.
* `LinearIsometryEquiv.toSpanUnitSingleton`: For `‖x‖ = 1` the continuous linear equivalence is a
  linear isometry equivalence.

-/

@[expose] public section

variable {𝕜 E : Type*}

namespace LinearMap

variable (𝕜)

section Seminormed

variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-
**LinearMap.toSpanSingleton_homothety** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toSpanSingleton_homothety (x : E) (c : 𝕜) : ‖LinearMap.toSpanSingleton 𝕜 E
 x c‖ = ‖x‖ * ‖c‖
参数：x : E；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
-/
theorem toSpanSingleton_homothety (x : E) (c : 𝕜) :
    ‖LinearMap.toSpanSingleton 𝕜 E x c‖ = ‖x‖ * ‖c‖ := by
  rw [mul_comm]
  exact norm_smul _ _

end Seminormed

end LinearMap

namespace ContinuousLinearEquiv

variable (𝕜)

section Seminormed
variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-
**ContinuousLinearEquiv._root_.LinearEquiv.toSpanNonzeroSingleton_homothety** 是 
Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.toSpanNonzeroSingleton_homothety (x : E) (h : x ≠ 0) (c : 𝕜) :
    ‖LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h c‖ = ‖x‖ * ‖c‖ :=
  LinearMap.toSpanSingleton_homothety _ _ _

end Seminormed

section Normed
variable [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural
continuous linear equivalence from `𝕜` to the span of `x`. -/
@[simps!]
/-
**ContinuousLinearEquiv.toSpanNonzeroSingleton** 是 Mathlib 中的一个定义，位于命名空间 `Contin
uousLinearEquiv`。
形式化陈述：toSpanNonzeroSingleton (x : E) (h : x != 0) : 𝕜 ≃L[𝕜] 𝕜 ∙ x
参数：x : E；h : x != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural
continuous linear equivalence from `𝕜` to the span of `x`.
-/
noncomputable def toSpanNonzeroSingleton (x : E) (h : x ≠ 0) : 𝕜 ≃L[𝕜] 𝕜 ∙ x :=
  ofHomothety (LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h) ‖x‖ (norm_pos_iff.mpr h)
    (LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x h)

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural continuous
linear map from the span of `x` to `𝕜`. -/
/-
**ContinuousLinearEquiv.coord** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：coord (x : E) (h : x != 0) : StrongDual 𝕜 (𝕜 ∙ x)
参数：x : E；h : x != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural
 continuous
linear map from the span of `x` to `𝕜`.
-/
noncomputable def coord (x : E) (h : x ≠ 0) : StrongDual 𝕜 (𝕜 ∙ x) :=
  (toSpanNonzeroSingleton 𝕜 x h).symm

@[simp]
/-
**ContinuousLinearEquiv.coe_toSpanNonzeroSingleton_symm** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearEquiv`。
形式化陈述：coe_toSpanNonzeroSingleton_symm {x : E} (h : x != 0) : ⇑(toSpanNonzeroSing
leton 𝕜 x h).symm = coord 𝕜 x h
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSpanNonzeroSingleton_symm {x : E} (h : x ≠ 0) :
    ⇑(toSpanNonzeroSingleton 𝕜 x h).symm = coord 𝕜 x h :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.coord_toSpanNonzeroSingleton** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearEquiv`。
形式化陈述：coord_toSpanNonzeroSingleton {x : E} (h : x != 0) (c : 𝕜) : coord 𝕜 x h (t
oSpanNonzeroSingleton 𝕜 x h c) = c
参数：h : x != 0；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
-/
theorem coord_toSpanNonzeroSingleton {x : E} (h : x ≠ 0) (c : 𝕜) :
    coord 𝕜 x h (toSpanNonzeroSingleton 𝕜 x h c) = c :=
  (toSpanNonzeroSingleton 𝕜 x h).symm_apply_apply c

@[simp]
/-
**ContinuousLinearEquiv.toSpanNonzeroSingleton_coord** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearEquiv`。
形式化陈述：toSpanNonzeroSingleton_coord {x : E} (h : x != 0) (y : 𝕜 ∙ x) : toSpanNonz
eroSingleton 𝕜 x h (coord 𝕜 x h y) = y
参数：h : x != 0；y : 𝕜 ∙ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
-/
theorem toSpanNonzeroSingleton_coord {x : E} (h : x ≠ 0) (y : 𝕜 ∙ x) :
    toSpanNonzeroSingleton 𝕜 x h (coord 𝕜 x h y) = y :=
  (toSpanNonzeroSingleton 𝕜 x h).apply_symm_apply y

@[simp]
/-
**ContinuousLinearEquiv.coord_self** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：coord_self (x : E) (h : x != 0) : (coord 𝕜 x h) (⟨x, Submodule.mem_span_si
ngleton_self x⟩ : 𝕜 ∙ x) = 1
参数：x : E；h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.coord_self`：coord_self : (coord R M x h) (⟨x, Submodule.mem_
span_singleton_self x⟩ : R ∙ x) = 1
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
-/
theorem coord_self (x : E) (h : x ≠ 0) :
    (coord 𝕜 x h) (⟨x, Submodule.mem_span_singleton_self x⟩ : 𝕜 ∙ x) = 1 :=
  LinearEquiv.coord_self 𝕜 E x h

end Normed

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-- Given a unit element `x` of a normed space `E` over a field `𝕜`, the natural
linear isometry equivalence from `𝕜` to the span of `x`. -/
/-
**LinearIsometryEquiv.toSpanUnitSingleton** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsome
tryEquiv`。
形式化陈述：toSpanUnitSingleton (x : E) (hx : ‖x‖ = 1) : 𝕜 ≃ₗᵢ[𝕜] 𝕜 ∙ x where toLinear
Equiv
参数：x : E；hx : ‖x‖ = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a unit element `x` of a normed space `E` over a field `𝕜`, the natural
linear isometry equivalence from `𝕜` to the span of `x`.
-/
noncomputable def toSpanUnitSingleton (x : E) (hx : ‖x‖ = 1) :
    𝕜 ≃ₗᵢ[𝕜] 𝕜 ∙ x where
  toLinearEquiv := LinearEquiv.toSpanNonzeroSingleton 𝕜 E x (by aesop)
  norm_map' := by
    intro
    rw [LinearEquiv.toSpanNonzeroSingleton_homothety, hx, one_mul]
/-
**LinearIsometryEquiv.toSpanUnitSingleton_apply** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rIsometryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NormedDivisionRing 𝕜] [inst_1 : Se
minormedAddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : NormSMulClass 𝕜
 E] (x : E) (hx : ‖x‖ = 1) (r : 𝕜),   (LinearIsometryEquiv.toSpanUnitSingleton x
 hx) r = ⟨r • x, ⋯⟩
参数：x : E；hx : ‖x‖ = 1；r : 𝕜；LinearIsometryEquiv.toSpanUnitSingleton x hx。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toSpanUnitSingleton_apply (x : E) (hx : ‖x‖ = 1) (r : 𝕜) :
    toSpanUnitSingleton x hx r = (⟨r • x, by aesop⟩ : 𝕜 ∙ x) := by
  rfl

end LinearIsometryEquiv

