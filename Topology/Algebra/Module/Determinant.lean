/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.LinearAlgebra.Determinant

/-!
# The determinant of a continuous linear map.
-/

public section


namespace ContinuousLinearMap

/-- The determinant of a continuous linear map, mainly as a convenience device to be able to
write `A.det` instead of `(A : M →ₗ[R] M).det`. -/
/-
**ContinuousLinearMap.det** 是 Mathlib 中的一个缩写定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：det {R : Type*} [CommRing R] {M : Type*} [TopologicalSpace M] [AddCommGrou
p M] [Module R M] (A : M ->L[R] M) : R
参数：A : M ->L[R] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The determinant of a continuous linear map, mainly as a convenience device to be
 able to
write `A.det` instead of `(A : M →ₗ[R] M).det`.
-/
noncomputable abbrev det {R : Type*} [CommRing R] {M : Type*} [TopologicalSpace M] [AddCommGroup M]
    [Module R M] (A : M →L[R] M) : R :=
  LinearMap.det (A : M →ₗ[R] M)
/-
**ContinuousLinearMap.det_pi** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：det_pi {ι R M : Type*} [Fintype ι] [CommRing R] [AddCommGroup M] [Topologi
calSpace M] [Module R M] [Module.Free R M] [Module.Finite R M] (f : ι -> M ->L[R
] M) : (pi (fun i => (f i).comp (proj i))).det = ∏ i, (f i).det
参数：f : ι -> M ->L[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.det_pi`：det_pi [Module.Free R M] [Module.Finite R M] (f : ι ->
 M ->ₗ[R] M) : (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))).det = ∏ i
, (f i…
-/
theorem det_pi {ι R M : Type*} [Fintype ι] [CommRing R] [AddCommGroup M]
    [TopologicalSpace M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : ι → M →L[R] M) :
    (pi (fun i ↦ (f i).comp (proj i))).det = ∏ i, (f i).det :=
  LinearMap.det_pi _
/-
**ContinuousLinearMap.det_smulRight** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：det_smulRight {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousMul
 𝕜] (f : 𝕜 ->L[𝕜] 𝕜) (v : 𝕜) : (smulRight f v).det = f 1 * v
参数：f : 𝕜 ->L[𝕜] 𝕜；v : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.det_ring`：∀ {R : Type u_1} [inst : CommRing R] (f : R →ₗ[R] R)
, LinearMap.det f = f 1
· 使用定理 `ContinuousLinearMap.coe_smulRight`：∀ {M₁ : Type u_4} [inst : Topological
Space M₁] [inst_1 : AddCommMonoid M₁] {M₂ : Type u_6}   [inst_2 : TopologicalSpa
ce M₂] [inst_3 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_smulRight {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜]
    (f : 𝕜 →L[𝕜] 𝕜) (v : 𝕜) : (smulRight f v).det = f 1 * v := by simp
/-
**ContinuousLinearMap.det_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：det_toSpanSingleton {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [Continu
ousMul 𝕜] (v : 𝕜) : (toSpanSingleton 𝕜 v).det = v
参数：v : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.smulRight_id`：smulRight_id : smulRight (.id R₁ R₁) =
 toSpanSingleton R₁ (M₁
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `ContinuousLinearMap.det_smulRight`：det_smulRight {𝕜 : Type*} [CommRing 𝕜
] [TopologicalSpace 𝕜] [ContinuousMul 𝕜] (f : 𝕜 ->L[𝕜] 𝕜) (v : 𝕜) : (smulRight f
 v).det = f 1 * v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_toSpanSingleton {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜]
    (v : 𝕜) : (toSpanSingleton 𝕜 v).det = v := by rw [← smulRight_id, det_smulRight]; simp

end ContinuousLinearMap

namespace ContinuousLinearEquiv

@[simp]
/-
**ContinuousLinearEquiv.det_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Equiv`。
形式化陈述：det_coe_symm {R : Type*} [Field R] {M : Type*} [TopologicalSpace M] [AddCo
mmGroup M] [Module R M] (A : M ≃L[R] M) : (A.symm : M ->L[R] M).det = (A : M ->L
[R] M).det⁻¹
参数：A : M ≃L[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.det_coe_symm`：LinearEquiv.det_coe_symm {𝕜 : Type*} [Field 𝕜]
 [Module 𝕜 M] (f : M ≃ₗ[𝕜] M) : LinearMap.det (f.symm : M ->ₗ[𝕜] M) = (LinearMap
.det (f : M ->…
-/
theorem det_coe_symm {R : Type*} [Field R] {M : Type*} [TopologicalSpace M] [AddCommGroup M]
    [Module R M] (A : M ≃L[R] M) : (A.symm : M →L[R] M).det = (A : M →L[R] M).det⁻¹ :=
  LinearEquiv.det_coe_symm A.toLinearEquiv

end ContinuousLinearEquiv

