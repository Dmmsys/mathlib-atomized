/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Topology.Algebra.Module.Equiv

/-! # Type classes for the Fourier transform

In this file we define type classes for the Fourier transform and the inverse Fourier transform.
We introduce the notation `𝓕` and `𝓕⁻` in these classes to denote the Fourier transform and
the inverse Fourier transform, respectively.

Moreover, we provide type-classes that encode the linear structure and the Fourier inversion
theorem.
-/

@[expose] public section

universe u v w

variable {ι R E F : Type*}

/--
The notation typeclass for the Fourier transform.

While the Fourier transform is a linear operator, the notation is for the function `E → F` without
any additional properties. This makes it possible to use the notation for functions where
integrability is an issue.
Moreover, including a scalar multiplication causes problems for inferring the notation type class.
-/
/-
**FourierTransform** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → outParam (Type v) → Type (max u v)
参数：Type v；max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The notation typeclass for the Fourier transform.

While the Fourier transform is a linear operator, the notation is for the functi
on `E → F` without
any additional properties. This makes it possible to use the notation for functi
ons where
integrability is an issue.
Moreover, including a scalar multiplication causes problems for inferring the no
tation type class.
-/
class FourierTransform (E : Type u) (F : outParam (Type v)) where
  /-- `𝓕 f` is the Fourier transform of `f`. The meaning of this notation is type-dependent. -/
  fourier : E → F

/--
The notation typeclass for the inverse Fourier transform.

While the inverse Fourier transform is a linear operator, the notation is for the function `E → F`
without any additional properties. This makes it possible to use the notation for functions where
integrability is an issue.
Moreover, including a scalar multiplication causes problems for inferring the notation type class.
-/
/-
**FourierTransformInv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → outParam (Type v) → Type (max u v)
参数：Type v；max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The notation typeclass for the inverse Fourier transform.

While the inverse Fourier transform is a linear operator, the notation is for th
e function `E → F`
without any additional properties. This makes it possible to use the notation fo
r functions where
integrability is an issue.
Moreover, including a scalar multiplication causes problems for inferring the no
tation type class.
-/
class FourierTransformInv (E : Type u) (F : outParam (Type v)) where
  /-- `𝓕⁻ f` is the inverse Fourier transform of `f`. The meaning of this notation is
  type-dependent. -/
  fourierInv : E → F

namespace FourierTransform

export FourierTransformInv (fourierInv)

@[inherit_doc] scoped notation "𝓕" => fourier
@[inherit_doc] scoped notation "𝓕⁻" => fourierInv

end FourierTransform

section Module

open scoped FourierTransform

/-- A `FourierAdd` is a function space on which the Fourier transform is additive. -/
/-
**FourierAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_5) → (F : outParam (Type u_6)) → [Add E] → [Add F] → [FourierT
ransform E F] → Prop
参数：Type u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FourierAdd` is a function space on which the Fourier transform is additive.
-/
class FourierAdd (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [FourierTransform E F] where
  fourier_add : ∀ (f g : E), 𝓕 (f + g) = 𝓕 f + 𝓕 g

/-- A `FourierSMul` is a function space on which the Fourier transform is homogeneous. -/
/-
**FourierSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_5) → (E : Type u_6) → (F : outParam (Type u_7)) → [SMul R E] →
 [SMul R F] → [FourierTransform E F] → Prop
参数：Type u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FourierSMul` is a function space on which the Fourier transform is homogeneou
s.
-/
class FourierSMul (R : Type*) (E : Type*) (F : outParam (Type*)) [SMul R E] [SMul R F]
    [FourierTransform E F] where
  fourier_smul : ∀ (r : R) (f : E), 𝓕 (r • f) = r • 𝓕 f

/-- The Fourier transform is continuous. -/
/-
**ContinuousFourier** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_5) → (F : outParam (Type u_6)) → [TopologicalSpace E] → [Topol
ogicalSpace F] → [FourierTransform E F] → Prop
参数：Type u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Fourier transform is continuous.
-/
class ContinuousFourier (E : Type*) (F : outParam (Type*))
    [TopologicalSpace E] [TopologicalSpace F] [FourierTransform E F] where
  continuous_fourier : Continuous (𝓕 : E → F)

/-- A `FourierInvAdd` is a function space on which the inverse Fourier transform is additive. -/
/-
**FourierInvAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_5) → (F : outParam (Type u_6)) → [Add E] → [Add F] → [FourierT
ransformInv E F] → Prop
参数：Type u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FourierInvAdd` is a function space on which the inverse Fourier transform is 
additive.
-/
class FourierInvAdd (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [FourierTransformInv E F]
    where
  fourierInv_add : ∀ (f g : E), 𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g

/-- A `FourierInvSMul` is a function space on which the inverse Fourier transform is homogeneous. -/
/-
**FourierInvSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_5) → (E : Type u_6) → (F : outParam (Type u_7)) → [SMul R E] →
 [SMul R F] → [FourierTransformInv E F] → Prop
参数：Type u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FourierInvSMul` is a function space on which the inverse Fourier transform is
 homogeneous.
-/
class FourierInvSMul (R : Type*) (E : Type*) (F : outParam (Type*)) [SMul R E] [SMul R F]
    [FourierTransformInv E F] where
  fourierInv_smul : ∀ (r : R) (f : E), 𝓕⁻ (r • f) = r • 𝓕⁻ f

/-- The inverse Fourier transform is continuous. -/
/-
**ContinuousFourierInv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_5) →   (F : outParam (Type u_6)) → [TopologicalSpace E] → [Top
ologicalSpace F] → [FourierTransformInv E F] → Prop
参数：Type u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse Fourier transform is continuous.
-/
class ContinuousFourierInv (E : Type*) (F : outParam (Type*))
    [TopologicalSpace E] [TopologicalSpace F] [FourierTransformInv E F] where
  continuous_fourierInv : Continuous (𝓕⁻ : E → F)

/-- A `FourierModule` is a function space on which the Fourier transform is a linear map. -/
@[deprecated "use `FourierAdd` and `FourierSMul` instead" (since := "2026-01-06")]
/-
**FourierModule** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_5) →   (E : Type u_6) → (F : outParam (Type u_7)) → [Add E] → 
[Add F] → [SMul R E] → [SMul R F] → Type (max u_6 u_7)
参数：Type u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FourierModule` is a function space on which the Fourier transform is a linear
 map.
-/
structure FourierModule (R : Type*) (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [SMul R E]
    [SMul R F] extends FourierTransform E F where
  fourier_add : ∀ (f g : E), 𝓕 (f + g) = 𝓕 f + 𝓕 g
  fourier_smul : ∀ (r : R) (f : E), 𝓕 (r • f) = r • 𝓕 f

/-- A `FourierInvModule` is a function space on which the Fourier transform is a linear map. -/
@[deprecated "use `FourierInvAdd` and `FourierInvSMul` instead" (since := "2026-01-06")]
/-
**FourierInvModule** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_5) →   (E : Type u_6) → (F : outParam (Type u_7)) → [Add E] → 
[Add F] → [SMul R E] → [SMul R F] → Type (max u_6 u_7)
参数：Type u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FourierInvModule` is a function space on which the Fourier transform is a lin
ear map.
-/
structure FourierInvModule (R : Type*) (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [SMul R E]
    [SMul R F] extends FourierTransformInv E F where
  fourierInv_add : ∀ (f g : E), 𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g
  fourierInv_smul : ∀ (r : R) (f : E), 𝓕⁻ (r • f) = r • 𝓕⁻ f

namespace FourierTransform

export FourierAdd (fourier_add)
export FourierSMul (fourier_smul)
export ContinuousFourier (continuous_fourier)
export FourierInvAdd (fourierInv_add)
export FourierInvSMul (fourierInv_smul)
export ContinuousFourierInv (continuous_fourierInv)

attribute [simp] fourier_add
attribute [simp] fourier_smul
attribute [simp] fourierInv_add
attribute [simp] fourierInv_smul
attribute [fun_prop] continuous_fourier
attribute [fun_prop] continuous_fourierInv

section fourier

variable [AddCommGroup E] [AddCommGroup F] [FourierTransform E F] [FourierAdd E F]

@[simp]
/-
**FourierTransform.fourier_zero** 是 Mathlib 中的一个定理，位于命名空间 `FourierTransform`。
形式化陈述：fourier_zero : 𝓕 (0 : E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `FourierAdd.fourier_add`：∀ {E : Type u_5} {F : outParam (Type u_6)} {inst
 : Add E} {inst_1 : Add F} {inst_2 : FourierTransform E F}   [self : FourierAdd 
E F] (f g : …
-/
theorem fourier_zero : 𝓕 (0 : E) = 0 :=
  map_zero (AddMonoidHom.mk' 𝓕 fourier_add)

@[simp]
/-
**FourierTransform.fourier_neg** 是 Mathlib 中的一个定理，位于命名空间 `FourierTransform`。
形式化陈述：fourier_neg (f : E) : 𝓕 (-f) = - 𝓕 f
参数：f : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `FourierAdd.fourier_add`：∀ {E : Type u_5} {F : outParam (Type u_6)} {inst
 : Add E} {inst_1 : Add F} {inst_2 : FourierTransform E F}   [self : FourierAdd 
E F] (f g : …
-/
theorem fourier_neg (f : E) : 𝓕 (-f) = - 𝓕 f :=
  map_neg (AddMonoidHom.mk' 𝓕 fourier_add) f

@[simp]
/-
**FourierTransform.fourier_sum** 是 Mathlib 中的一个定理，位于命名空间 `FourierTransform`。
形式化陈述：fourier_sum (f : ι -> E) (s : Finset ι) : 𝓕 (∑ i in s, f i) = ∑ i in s, 𝓕 
(f i)
参数：f : ι -> E；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `FourierAdd.fourier_add`：∀ {E : Type u_5} {F : outParam (Type u_6)} {inst
 : Add E} {inst_1 : Add F} {inst_2 : FourierTransform E F}   [self : FourierAdd 
E F] (f g : …
-/
theorem fourier_sum (f : ι → E) (s : Finset ι) : 𝓕 (∑ i ∈ s, f i) = ∑ i ∈ s, 𝓕 (f i) :=
  map_sum (AddMonoidHom.mk' 𝓕 fourier_add) f s

end fourier

section fourierInv

variable [AddCommGroup E] [AddCommGroup F] [FourierTransformInv E F] [FourierInvAdd E F]

@[simp]
/-
**FourierTransform.fourierInv_zero** 是 Mathlib 中的一个定理，位于命名空间 `FourierTransform`。
形式化陈述：fourierInv_zero : 𝓕⁻ (0 : E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `FourierInvAdd.fourierInv_add`：∀ {E : Type u_5} {F : outParam (Type u_6)}
 {inst : Add E} {inst_1 : Add F} {inst_2 : FourierTransformInv E F}   [self : Fo
urierInvAdd E F] (…
-/
theorem fourierInv_zero : 𝓕⁻ (0 : E) = 0 :=
  map_zero (AddMonoidHom.mk' 𝓕⁻ fourierInv_add)

@[simp]
/-
**FourierTransform.fourierInv_neg** 是 Mathlib 中的一个定理，位于命名空间 `FourierTransform`。
形式化陈述：fourierInv_neg (f : E) : 𝓕⁻ (-f) = - 𝓕⁻ f
参数：f : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `FourierInvAdd.fourierInv_add`：∀ {E : Type u_5} {F : outParam (Type u_6)}
 {inst : Add E} {inst_1 : Add F} {inst_2 : FourierTransformInv E F}   [self : Fo
urierInvAdd E F] (…
-/
theorem fourierInv_neg (f : E) : 𝓕⁻ (-f) = - 𝓕⁻ f :=
  map_neg (AddMonoidHom.mk' 𝓕⁻ fourierInv_add) f

@[simp]
/-
**FourierTransform.fourierInv_sum** 是 Mathlib 中的一个定理，位于命名空间 `FourierTransform`。
形式化陈述：fourierInv_sum (f : ι -> E) (s : Finset ι) : 𝓕⁻ (∑ i in s, f i) = ∑ i in s
, 𝓕⁻ (f i)
参数：f : ι -> E；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `FourierInvAdd.fourierInv_add`：∀ {E : Type u_5} {F : outParam (Type u_6)}
 {inst : Add E} {inst_1 : Add F} {inst_2 : FourierTransformInv E F}   [self : Fo
urierInvAdd E F] (…
-/
theorem fourierInv_sum (f : ι → E) (s : Finset ι) : 𝓕⁻ (∑ i ∈ s, f i) = ∑ i ∈ s, 𝓕⁻ (f i) :=
  map_sum (AddMonoidHom.mk' 𝓕⁻ fourierInv_add) f s

end fourierInv

variable [Semiring R] [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]

section fourierCLM

variable [FourierTransform E F] [FourierAdd E F] [FourierSMul R E F]

variable (R E) in
/-- The Fourier transform as a linear map. -/
/-
**FourierTransform.fourier** 是 Mathlib 中的一个定义，位于命名空间 `FourierTransform`。
形式化陈述：{E : Type u} → {F : outParam (Type v)} → [self : FourierTransform E F] → E
 → F
参数：Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Fourier transform as a linear map.
-/
def fourierₗ : E →ₗ[R] F where
  toFun := 𝓕
  map_add' := fourier_add
  map_smul' := fourier_smul

@[simp]
/-
**FourierTransform.fourier** 是 Mathlib 中的一个定义，位于命名空间 `FourierTransform`。
形式化陈述：{E : Type u} → {F : outParam (Type v)} → [self : FourierTransform E F] → E
 → F
参数：Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fourierₗ_apply (f : E) : fourierₗ R E f = 𝓕 f := rfl

variable [TopologicalSpace E] [TopologicalSpace F] [ContinuousFourier E F]

variable (R E) in
/-- The Fourier transform as a continuous linear map. -/
/-
**FourierTransform.fourierCLM** 是 Mathlib 中的一个定义，位于命名空间 `FourierTransform`。
形式化陈述：fourierCLM : E ->L[R] F where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Fourier transform as a continuous linear map.
-/
def fourierCLM : E →L[R] F where
  __ := fourierₗ R E

@[simp]
/-
**FourierTransform.fourierCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `FourierTransform`
。
形式化陈述：fourierCLM_apply (f : E) : fourierCLM R E f = 𝓕 f
参数：f : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fourierCLM_apply (f : E) : fourierCLM R E f = 𝓕 f := rfl

end fourierCLM

section fourierInvCLM

variable [FourierTransformInv E F] [FourierInvAdd E F] [FourierInvSMul R E F]

variable (R E) in
/-- The inverse Fourier transform as a linear map. -/
/-
**FourierTransform.fourierInv** 是 Mathlib 中的一个定义，位于命名空间 `FourierTransform`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse Fourier transform as a linear map.
-/
def fourierInvₗ : E →ₗ[R] F where
  toFun := 𝓕⁻
  map_add' := fourierInv_add
  map_smul' := fourierInv_smul

@[simp]
/-
**FourierTransform.fourierInv** 是 Mathlib 中的一个引理，位于命名空间 `FourierTransform`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fourierInvₗ_apply (f : E) : fourierInvₗ R E f = 𝓕⁻ f := rfl

variable [TopologicalSpace E] [TopologicalSpace F] [ContinuousFourierInv E F]

variable (R E) in
/-- The inverse Fourier transform as a continuous linear map. -/
/-
**FourierTransform.fourierInvCLM** 是 Mathlib 中的一个定义，位于命名空间 `FourierTransform`。
形式化陈述：fourierInvCLM : E ->L[R] F where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse Fourier transform as a continuous linear map.
-/
def fourierInvCLM : E →L[R] F where
  toFun := 𝓕⁻
  map_add' := fourierInv_add
  map_smul' := fourierInv_smul

@[simp]
/-
**FourierTransform.fourierInvCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `FourierTransfo
rm`。
形式化陈述：fourierInvCLM_apply (f : E) : fourierInvCLM R E f = 𝓕⁻ f
参数：f : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fourierInvCLM_apply (f : E) : fourierInvCLM R E f = 𝓕⁻ f := rfl

end fourierInvCLM

end FourierTransform

end Module

section Pair

open FourierTransform

/-- A `FourierPair` is a pair of spaces `E` and `F` such that `𝓕⁻ ∘ 𝓕 = id` on `E`. -/
/-
**FourierPair** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_5) → (F : Type u_6) → [FourierTransform E F] → [FourierTransfo
rmInv F E] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FourierPair` is a pair of spaces `E` and `F` such that `𝓕⁻ ∘ 𝓕 = id` on `E`.
-/
class FourierPair (E F : Type*) [FourierTransform E F] [FourierTransformInv F E] where
  fourierInv_fourier_eq : ∀ (f : E), 𝓕⁻ (𝓕 f) = f

/-- A `FourierInvPair` is a pair of spaces `E` and `F` such that `𝓕 ∘ 𝓕⁻ = id` on `E`. -/
/-
**FourierInvPair** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_5) → (F : Type u_6) → [FourierTransform F E] → [FourierTransfo
rmInv E F] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FourierInvPair` is a pair of spaces `E` and `F` such that `𝓕 ∘ 𝓕⁻ = id` on `E
`.
-/
class FourierInvPair (E F : Type*) [FourierTransform F E] [FourierTransformInv E F] where
  fourier_fourierInv_eq : ∀ (f : E), 𝓕 (𝓕⁻ f) = f

namespace FourierTransform

export FourierPair (fourierInv_fourier_eq)
export FourierInvPair (fourier_fourierInv_eq)

attribute [simp] fourierInv_fourier_eq
attribute [simp] fourier_fourierInv_eq

variable {R E F : Type*} [Semiring R] [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]
  [FourierTransform E F] [FourierAdd E F] [FourierSMul R E F]
  [FourierTransformInv F E]
  [FourierPair E F] [FourierInvPair F E]

variable (R E) in
/-- The Fourier transform as a linear equivalence. -/
/-
**FourierTransform.fourierEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FourierTransform`。
形式化陈述：fourierEquiv : E ≃ₗ[R] F where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FourierPair.fourierInv_fourier_eq`：∀ {E : Type u_5} {F : Type u_6} {inst
 : FourierTransform E F} {inst_1 : FourierTransformInv F E}   [self : FourierPai
r E F] (f : E), Fourier…
· 使用定理 `FourierInvPair.fourier_fourierInv_eq`：∀ {E : Type u_5} {F : Type u_6} {i
nst : FourierTransform F E} {inst_1 : FourierTransformInv E F}   [self : Fourier
InvPair E F] (f : E), Four…

--- 原说明 ---
The Fourier transform as a linear equivalence.
-/
def fourierEquiv : E ≃ₗ[R] F where
  __ := fourierₗ R E
  invFun := 𝓕⁻
  left_inv := fourierInv_fourier_eq
  right_inv := fourier_fourierInv_eq

@[simp]
/-
**FourierTransform.fourierEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `FourierTransfor
m`。
形式化陈述：fourierEquiv_apply (f : E) : fourierEquiv R E f = 𝓕 f
参数：f : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fourierEquiv_apply (f : E) : fourierEquiv R E f = 𝓕 f := rfl

@[simp]
/-
**FourierTransform.fourierEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `FourierTra
nsform`。
形式化陈述：fourierEquiv_symm_apply (f : F) : (fourierEquiv R E).symm f = 𝓕⁻ f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fourierEquiv_symm_apply (f : F) : (fourierEquiv R E).symm f = 𝓕⁻ f := rfl

variable [TopologicalSpace E] [TopologicalSpace F]
  [ContinuousFourier E F] [ContinuousFourierInv F E]

variable (R E) in
/-- The Fourier transform as a continuous linear equivalence. -/
/-
**FourierTransform.fourierCLE** 是 Mathlib 中的一个定义，位于命名空间 `FourierTransform`。
形式化陈述：fourierCLE : E ≃L[R] F where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Fourier transform as a continuous linear equivalence.
-/
def fourierCLE : E ≃L[R] F where
  __ := fourierEquiv R E

@[simp]
/-
**FourierTransform.fourierCLE_apply** 是 Mathlib 中的一个引理，位于命名空间 `FourierTransform`
。
形式化陈述：fourierCLE_apply (f : E) : fourierCLE R E f = 𝓕 f
参数：f : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fourierCLE_apply (f : E) : fourierCLE R E f = 𝓕 f := rfl

@[simp]
/-
**FourierTransform.fourierCLE_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `FourierTrans
form`。
形式化陈述：fourierCLE_symm_apply (f : F) : (fourierCLE R E).symm f = 𝓕⁻ f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fourierCLE_symm_apply (f : F) : (fourierCLE R E).symm f = 𝓕⁻ f := rfl

end FourierTransform

end Pair

