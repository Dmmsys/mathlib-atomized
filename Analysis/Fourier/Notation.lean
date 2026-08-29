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
Definition of `FourierTransform` / `FourierTransform` 的定义

English:
class FourierTransform
  parameters: (E : Type u) (F : outParam (Type v))
  axioms and operations (1):
    - fourier : E -> F

中文:
类 FourierTransform
  参数: (E : 类型u) (F : outParam (类型v))
  公理与运算 (1 个):
    - fourier : E -> F
-/
class FourierTransform (E : Type u) (F : outParam (Type v)) where
  /-- `𝓕 f` is the Fourier transform of `f`. The meaning of this notation is type-dependent. -/
  fourier : E -> F

/--
Definition of `FourierTransformInv` / `FourierTransformInv` 的定义

English:
class FourierTransformInv
  parameters: (E : Type u) (F : outParam (Type v))
  axioms and operations (1):
    - fourierInv : E -> F

中文:
类 FourierTransformInv
  参数: (E : 类型u) (F : outParam (类型v))
  公理与运算 (1 个):
    - fourierInv : E -> F
-/
class FourierTransformInv (E : Type u) (F : outParam (Type v)) where
  /-- `𝓕⁻ f` is the inverse Fourier transform of `f`. The meaning of this notation is
  type-dependent. -/
  fourierInv : E -> F

namespace FourierTransform

export FourierTransformInv (fourierInv)

@[inherit_doc] scoped notation "𝓕" => fourier
@[inherit_doc] scoped notation "𝓕⁻" => fourierInv

end FourierTransform

section Module

open scoped FourierTransform

/--
Definition of `FourierAdd` / `FourierAdd` 的定义

English:
class FourierAdd
  parameters: (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [FourierTransform E F]
  axioms and operations (1):
    - fourier_add : forall (f g : E), 𝓕 (f + g) = 𝓕 f + 𝓕 g

中文:
类 FourierAdd
  参数: (E : 类型) (F : outParam (类型)) [Add E] [Add F] [FourierTransform E F]
  公理与运算 (1 个):
    - fourier_add : 对任意 (f g : E), 𝓕 (f + g) = 𝓕 f + 𝓕 g
-/
class FourierAdd (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [FourierTransform E F] where
  fourier_add : forall (f g : E), 𝓕 (f + g) = 𝓕 f + 𝓕 g

/--
Definition of `FourierSMul` / `FourierSMul` 的定义

English:
class FourierSMul
  parameters: (R : Type*) (E : Type*) (F : outParam (Type*)) [SMul R E] [SMul R F]
  axioms and operations (1):
    - fourier_smul : forall (r : R) (f : E), 𝓕 (r • f) = r • 𝓕 f

中文:
类 FourierSMul
  参数: (R : 类型) (E : 类型) (F : outParam (类型)) [SMul R E] [SMul R F]
  公理与运算 (1 个):
    - fourier_smul : 对任意 (r : R) (f : E), 𝓕 (r • f) = r • 𝓕 f
-/
class FourierSMul (R : Type*) (E : Type*) (F : outParam (Type*)) [SMul R E] [SMul R F]
    [FourierTransform E F] where
  fourier_smul : forall (r : R) (f : E), 𝓕 (r • f) = r • 𝓕 f

/--
Definition of `ContinuousFourier` / `ContinuousFourier` 的定义

English:
class ContinuousFourier
  parameters: (E : Type*) (F : outParam (Type*))
  axioms and operations (1):
    - continuous_fourier : Continuous (𝓕 : E -> F)

中文:
类 ContinuousFourier
  参数: (E : 类型) (F : outParam (类型))
  公理与运算 (1 个):
    - continuous_fourier : Continuous (𝓕 : E -> F)
-/
class ContinuousFourier (E : Type*) (F : outParam (Type*))
    [TopologicalSpace E] [TopologicalSpace F] [FourierTransform E F] where
  continuous_fourier : Continuous (𝓕 : E -> F)

/--
Definition of `FourierInvAdd` / `FourierInvAdd` 的定义

English:
class FourierInvAdd
  parameters: (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [FourierTransformInv E F]
  axioms and operations (1):
    - fourierInv_add : forall (f g : E), 𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g

中文:
类 FourierInvAdd
  参数: (E : 类型) (F : outParam (类型)) [Add E] [Add F] [FourierTransformInv E F]
  公理与运算 (1 个):
    - fourierInv_add : 对任意 (f g : E), 𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g
-/
class FourierInvAdd (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [FourierTransformInv E F]
    where
  fourierInv_add : forall (f g : E), 𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g

/--
Definition of `FourierInvSMul` / `FourierInvSMul` 的定义

English:
class FourierInvSMul
  parameters: (R : Type*) (E : Type*) (F : outParam (Type*)) [SMul R E] [SMul R F]
  axioms and operations (1):
    - fourierInv_smul : forall (r : R) (f : E), 𝓕⁻ (r • f) = r • 𝓕⁻ f

中文:
类 FourierInvSMul
  参数: (R : 类型) (E : 类型) (F : outParam (类型)) [SMul R E] [SMul R F]
  公理与运算 (1 个):
    - fourierInv_smul : 对任意 (r : R) (f : E), 𝓕⁻ (r • f) = r • 𝓕⁻ f
-/
class FourierInvSMul (R : Type*) (E : Type*) (F : outParam (Type*)) [SMul R E] [SMul R F]
    [FourierTransformInv E F] where
  fourierInv_smul : forall (r : R) (f : E), 𝓕⁻ (r • f) = r • 𝓕⁻ f

/--
Definition of `ContinuousFourierInv` / `ContinuousFourierInv` 的定义

English:
class ContinuousFourierInv
  parameters: (E : Type*) (F : outParam (Type*))
  axioms and operations (1):
    - continuous_fourierInv : Continuous (𝓕⁻ : E -> F)

中文:
类 ContinuousFourierInv
  参数: (E : 类型) (F : outParam (类型))
  公理与运算 (1 个):
    - continuous_fourierInv : Continuous (𝓕⁻ : E -> F)
-/
class ContinuousFourierInv (E : Type*) (F : outParam (Type*))
    [TopologicalSpace E] [TopologicalSpace F] [FourierTransformInv E F] where
  continuous_fourierInv : Continuous (𝓕⁻ : E -> F)

/-- A `FourierModule` is a function space on which the Fourier transform is a linear map. -/
@[deprecated "use `FourierAdd` and `FourierSMul` instead" (since := "2026-01-06")]
/--
Definition of `FourierModule` / `FourierModule` 的定义

English:
structure FourierModule
  parameters: (R : Type*) (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [SMul R E]
  extends: FourierTransform E F
  axioms and operations (2):
    - fourier_add : forall (f g : E), 𝓕 (f + g) = 𝓕 f + 𝓕 g
    - fourier_smul : forall (r : R) (f : E), 𝓕 (r • f) = r • 𝓕 f

中文:
结构 FourierModule
  参数: (R : 类型) (E : 类型) (F : outParam (类型)) [Add E] [Add F] [SMul R E]
  继承: FourierTransform E F
  公理与运算 (2 个):
    - fourier_add : 对任意 (f g : E), 𝓕 (f + g) = 𝓕 f + 𝓕 g
    - fourier_smul : 对任意 (r : R) (f : E), 𝓕 (r • f) = r • 𝓕 f
-/
structure FourierModule (R : Type*) (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [SMul R E]
    [SMul R F] extends FourierTransform E F where
  fourier_add : forall (f g : E), 𝓕 (f + g) = 𝓕 f + 𝓕 g
  fourier_smul : forall (r : R) (f : E), 𝓕 (r • f) = r • 𝓕 f

/-- A `FourierInvModule` is a function space on which the Fourier transform is a linear map. -/
@[deprecated "use `FourierInvAdd` and `FourierInvSMul` instead" (since := "2026-01-06")]
/--
Definition of `FourierInvModule` / `FourierInvModule` 的定义

English:
structure FourierInvModule
  parameters: (R : Type*) (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [SMul R E]
  extends: FourierTransformInv E F
  axioms and operations (2):
    - fourierInv_add : forall (f g : E), 𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g
    - fourierInv_smul : forall (r : R) (f : E), 𝓕⁻ (r • f) = r • 𝓕⁻ f

中文:
结构 FourierInvModule
  参数: (R : 类型) (E : 类型) (F : outParam (类型)) [Add E] [Add F] [SMul R E]
  继承: FourierTransformInv E F
  公理与运算 (2 个):
    - fourierInv_add : 对任意 (f g : E), 𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g
    - fourierInv_smul : 对任意 (r : R) (f : E), 𝓕⁻ (r • f) = r • 𝓕⁻ f
-/
structure FourierInvModule (R : Type*) (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [SMul R E]
    [SMul R F] extends FourierTransformInv E F where
  fourierInv_add : forall (f g : E), 𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g
  fourierInv_smul : forall (r : R) (f : E), 𝓕⁻ (r • f) = r • 𝓕⁻ f

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
/--
theorem `fourier_zero` / 定理 `fourier_zero`

English:
theorem fourier_zero
  statement: 𝓕 (0 : E) = 0
  proof: map_zero (AddMonoidHom.mk' 𝓕 fourier_add)

@[simp]

中文:
定理 fourier_zero
  结论: 𝓕 (0 : E) = 0
  证明: map_zero (AddMonoidHom.mk' 𝓕 fourier_add)

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, fourier_add, map_zero
-/
theorem fourier_zero : 𝓕 (0 : E) = 0 :=
  map_zero (AddMonoidHom.mk' 𝓕 fourier_add)

@[simp]
/--
theorem `fourier_neg` / 定理 `fourier_neg`

English:
theorem fourier_neg
  given: (f : E)
  statement: 𝓕 (-f) = - 𝓕 f
  proof: map_neg (AddMonoidHom.mk' 𝓕 fourier_add) f

@[simp]

中文:
定理 fourier_neg
  条件: (f : E)
  结论: 𝓕 (-f) = - 𝓕 f
  证明: map_neg (AddMonoidHom.mk' 𝓕 fourier_add) f

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, fourier_add, map_neg
-/
theorem fourier_neg (f : E) : 𝓕 (-f) = - 𝓕 f :=
  map_neg (AddMonoidHom.mk' 𝓕 fourier_add) f

@[simp]
/--
theorem `fourier_sum` / 定理 `fourier_sum`

English:
theorem fourier_sum
  given: (f : ι -> E) (s : Finset ι)
  statement: 𝓕 (∑ i in s, f i) = ∑ i in s, 𝓕 (f i)
  proof: map_sum (AddMonoidHom.mk' 𝓕 fourier_add) f s

中文:
定理 fourier_sum
  条件: (f : ι -> E) (s : Finset ι)
  结论: 𝓕 (∑ i in s, f i) = ∑ i in s, 𝓕 (f i)
  证明: map_sum (AddMonoidHom.mk' 𝓕 fourier_add) f s

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, fourier_add, map_sum
-/
theorem fourier_sum (f : ι -> E) (s : Finset ι) : 𝓕 (∑ i in s, f i) = ∑ i in s, 𝓕 (f i) :=
  map_sum (AddMonoidHom.mk' 𝓕 fourier_add) f s

end fourier

section fourierInv

variable [AddCommGroup E] [AddCommGroup F] [FourierTransformInv E F] [FourierInvAdd E F]

@[simp]
/--
theorem `fourierInv_zero` / 定理 `fourierInv_zero`

English:
theorem fourierInv_zero
  statement: 𝓕⁻ (0 : E) = 0
  proof: map_zero (AddMonoidHom.mk' 𝓕⁻ fourierInv_add)

@[simp]

中文:
定理 fourierInv_zero
  结论: 𝓕⁻ (0 : E) = 0
  证明: map_zero (AddMonoidHom.mk' 𝓕⁻ fourierInv_add)

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, fourierInv_add, map_zero
-/
theorem fourierInv_zero : 𝓕⁻ (0 : E) = 0 :=
  map_zero (AddMonoidHom.mk' 𝓕⁻ fourierInv_add)

@[simp]
/--
theorem `fourierInv_neg` / 定理 `fourierInv_neg`

English:
theorem fourierInv_neg
  given: (f : E)
  statement: 𝓕⁻ (-f) = - 𝓕⁻ f
  proof: map_neg (AddMonoidHom.mk' 𝓕⁻ fourierInv_add) f

@[simp]

中文:
定理 fourierInv_neg
  条件: (f : E)
  结论: 𝓕⁻ (-f) = - 𝓕⁻ f
  证明: map_neg (AddMonoidHom.mk' 𝓕⁻ fourierInv_add) f

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, fourierInv_add, map_neg
-/
theorem fourierInv_neg (f : E) : 𝓕⁻ (-f) = - 𝓕⁻ f :=
  map_neg (AddMonoidHom.mk' 𝓕⁻ fourierInv_add) f

@[simp]
/--
theorem `fourierInv_sum` / 定理 `fourierInv_sum`

English:
theorem fourierInv_sum
  given: (f : ι -> E) (s : Finset ι)
  statement: 𝓕⁻ (∑ i in s, f i) = ∑ i in s, 𝓕⁻ (f i)
  proof: map_sum (AddMonoidHom.mk' 𝓕⁻ fourierInv_add) f s

中文:
定理 fourierInv_sum
  条件: (f : ι -> E) (s : Finset ι)
  结论: 𝓕⁻ (∑ i in s, f i) = ∑ i in s, 𝓕⁻ (f i)
  证明: map_sum (AddMonoidHom.mk' 𝓕⁻ fourierInv_add) f s

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, fourierInv_add, map_sum
-/
theorem fourierInv_sum (f : ι -> E) (s : Finset ι) : 𝓕⁻ (∑ i in s, f i) = ∑ i in s, 𝓕⁻ (f i) :=
  map_sum (AddMonoidHom.mk' 𝓕⁻ fourierInv_add) f s

end fourierInv

variable [Semiring R] [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]

section fourierCLM

variable [FourierTransform E F] [FourierAdd E F] [FourierSMul R E F]

variable (R E) in
/--
Definition of `fourierₗ` / `fourierₗ` 的定义

English:
definition fourierₗ
  signature: : E ->ₗ[R] F where
  body: 𝓕
  map_add' := fourier_add
  map_smul' := fourier_smul

@[simp]

中文:
定义 fourierₗ
  签名: : E ->ₗ[R] F where
  定义体: 𝓕
  map_add' := fourier_add
  map_smul' := fourier_smul

@[simp]
-/
def fourierₗ : E ->ₗ[R] F where
  toFun := 𝓕
  map_add' := fourier_add
  map_smul' := fourier_smul

@[simp]
/--
lemma `fourierₗ_apply` / 引理 `fourierₗ_apply`

English:
lemma fourierₗ_apply
  given: (f : E)
  statement: fourierₗ R E f = 𝓕 f
  proof: rfl

中文:
引理 fourierₗ_apply
  条件: (f : E)
  结论: fourierₗ R E f = 𝓕 f
  证明: rfl
-/
lemma fourierₗ_apply (f : E) : fourierₗ R E f = 𝓕 f := rfl

variable [TopologicalSpace E] [TopologicalSpace F] [ContinuousFourier E F]

variable (R E) in
/--
Definition of `fourierCLM` / `fourierCLM` 的定义

English:
definition fourierCLM
  signature: : E ->L[R] F where
  body: fourierₗ R E

@[simp]

中文:
定义 fourierCLM
  签名: : E ->L[R] F where
  定义体: fourierₗ R E

@[simp]
-/
def fourierCLM : E ->L[R] F where
  __ := fourierₗ R E

@[simp]
/--
lemma `fourierCLM_apply` / 引理 `fourierCLM_apply`

English:
lemma fourierCLM_apply
  given: (f : E)
  statement: fourierCLM R E f = 𝓕 f
  proof: rfl

中文:
引理 fourierCLM_apply
  条件: (f : E)
  结论: fourierCLM R E f = 𝓕 f
  证明: rfl
-/
lemma fourierCLM_apply (f : E) : fourierCLM R E f = 𝓕 f := rfl

end fourierCLM

section fourierInvCLM

variable [FourierTransformInv E F] [FourierInvAdd E F] [FourierInvSMul R E F]

variable (R E) in
/--
Definition of `fourierInvₗ` / `fourierInvₗ` 的定义

English:
definition fourierInvₗ
  signature: : E ->ₗ[R] F where
  body: 𝓕⁻
  map_add' := fourierInv_add
  map_smul' := fourierInv_smul

@[simp]

中文:
定义 fourierInvₗ
  签名: : E ->ₗ[R] F where
  定义体: 𝓕⁻
  map_add' := fourierInv_add
  map_smul' := fourierInv_smul

@[simp]
-/
def fourierInvₗ : E ->ₗ[R] F where
  toFun := 𝓕⁻
  map_add' := fourierInv_add
  map_smul' := fourierInv_smul

@[simp]
/--
lemma `fourierInvₗ_apply` / 引理 `fourierInvₗ_apply`

English:
lemma fourierInvₗ_apply
  given: (f : E)
  statement: fourierInvₗ R E f = 𝓕⁻ f
  proof: rfl

中文:
引理 fourierInvₗ_apply
  条件: (f : E)
  结论: fourierInvₗ R E f = 𝓕⁻ f
  证明: rfl
-/
lemma fourierInvₗ_apply (f : E) : fourierInvₗ R E f = 𝓕⁻ f := rfl

variable [TopologicalSpace E] [TopologicalSpace F] [ContinuousFourierInv E F]

variable (R E) in
/--
Definition of `fourierInvCLM` / `fourierInvCLM` 的定义

English:
definition fourierInvCLM
  signature: : E ->L[R] F where
  body: 𝓕⁻
  map_add' := fourierInv_add
  map_smul' := fourierInv_smul

@[simp]

中文:
定义 fourierInvCLM
  签名: : E ->L[R] F where
  定义体: 𝓕⁻
  map_add' := fourierInv_add
  map_smul' := fourierInv_smul

@[simp]
-/
def fourierInvCLM : E ->L[R] F where
  toFun := 𝓕⁻
  map_add' := fourierInv_add
  map_smul' := fourierInv_smul

@[simp]
/--
lemma `fourierInvCLM_apply` / 引理 `fourierInvCLM_apply`

English:
lemma fourierInvCLM_apply
  given: (f : E)
  statement: fourierInvCLM R E f = 𝓕⁻ f
  proof: rfl

中文:
引理 fourierInvCLM_apply
  条件: (f : E)
  结论: fourierInvCLM R E f = 𝓕⁻ f
  证明: rfl
-/
lemma fourierInvCLM_apply (f : E) : fourierInvCLM R E f = 𝓕⁻ f := rfl

end fourierInvCLM

end FourierTransform

end Module

section Pair

open FourierTransform

/--
Definition of `FourierPair` / `FourierPair` 的定义

English:
class FourierPair
  parameters: (E F : Type*) [FourierTransform E F] [FourierTransformInv F E]
  axioms and operations (1):
    - fourierInv_fourier_eq : forall (f : E), 𝓕⁻ (𝓕 f) = f

中文:
类 FourierPair
  参数: (E F : 类型) [FourierTransform E F] [FourierTransformInv F E]
  公理与运算 (1 个):
    - fourierInv_fourier_eq : 对任意 (f : E), 𝓕⁻ (𝓕 f) = f
-/
class FourierPair (E F : Type*) [FourierTransform E F] [FourierTransformInv F E] where
  fourierInv_fourier_eq : forall (f : E), 𝓕⁻ (𝓕 f) = f

/--
Definition of `FourierInvPair` / `FourierInvPair` 的定义

English:
class FourierInvPair
  parameters: (E F : Type*) [FourierTransform F E] [FourierTransformInv E F]
  axioms and operations (1):
    - fourier_fourierInv_eq : forall (f : E), 𝓕 (𝓕⁻ f) = f

中文:
类 FourierInvPair
  参数: (E F : 类型) [FourierTransform F E] [FourierTransformInv E F]
  公理与运算 (1 个):
    - fourier_fourierInv_eq : 对任意 (f : E), 𝓕 (𝓕⁻ f) = f
-/
class FourierInvPair (E F : Type*) [FourierTransform F E] [FourierTransformInv E F] where
  fourier_fourierInv_eq : forall (f : E), 𝓕 (𝓕⁻ f) = f

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
/--
Definition of `fourierEquiv` / `fourierEquiv` 的定义

English:
definition fourierEquiv
  signature: : E ≃ₗ[R] F where
  body: fourierₗ R E
  invFun := 𝓕⁻
  left_inv := fourierInv_fourier_eq
  right_inv := fourier_fourierInv_eq

@[simp]

中文:
定义 fourierEquiv
  签名: : E ≃ₗ[R] F where
  定义体: fourierₗ R E
  invFun := 𝓕⁻
  left_inv := fourierInv_fourier_eq
  right_inv := fourier_fourierInv_eq

@[simp]
-/
def fourierEquiv : E ≃ₗ[R] F where
  __ := fourierₗ R E
  invFun := 𝓕⁻
  left_inv := fourierInv_fourier_eq
  right_inv := fourier_fourierInv_eq

@[simp]
/--
lemma `fourierEquiv_apply` / 引理 `fourierEquiv_apply`

English:
lemma fourierEquiv_apply
  given: (f : E)
  statement: fourierEquiv R E f = 𝓕 f
  proof: rfl

@[simp]

中文:
引理 fourierEquiv_apply
  条件: (f : E)
  结论: fourierEquiv R E f = 𝓕 f
  证明: rfl

@[simp]
-/
lemma fourierEquiv_apply (f : E) : fourierEquiv R E f = 𝓕 f := rfl

@[simp]
/--
lemma `fourierEquiv_symm_apply` / 引理 `fourierEquiv_symm_apply`

English:
lemma fourierEquiv_symm_apply
  given: (f : F)
  statement: (fourierEquiv R E).symm f = 𝓕⁻ f
  proof: rfl

中文:
引理 fourierEquiv_symm_apply
  条件: (f : F)
  结论: (fourierEquiv R E).symm f = 𝓕⁻ f
  证明: rfl
-/
lemma fourierEquiv_symm_apply (f : F) : (fourierEquiv R E).symm f = 𝓕⁻ f := rfl

variable [TopologicalSpace E] [TopologicalSpace F]
  [ContinuousFourier E F] [ContinuousFourierInv F E]

variable (R E) in
/--
Definition of `fourierCLE` / `fourierCLE` 的定义

English:
definition fourierCLE
  signature: : E ≃L[R] F where
  body: fourierEquiv R E

@[simp]

中文:
定义 fourierCLE
  签名: : E ≃L[R] F where
  定义体: fourierEquiv R E

@[simp]

Depends on / 依赖: fourierEquiv
-/
def fourierCLE : E ≃L[R] F where
  __ := fourierEquiv R E

@[simp]
/--
lemma `fourierCLE_apply` / 引理 `fourierCLE_apply`

English:
lemma fourierCLE_apply
  given: (f : E)
  statement: fourierCLE R E f = 𝓕 f
  proof: rfl

@[simp]

中文:
引理 fourierCLE_apply
  条件: (f : E)
  结论: fourierCLE R E f = 𝓕 f
  证明: rfl

@[simp]
-/
lemma fourierCLE_apply (f : E) : fourierCLE R E f = 𝓕 f := rfl

@[simp]
/--
lemma `fourierCLE_symm_apply` / 引理 `fourierCLE_symm_apply`

English:
lemma fourierCLE_symm_apply
  given: (f : F)
  statement: (fourierCLE R E).symm f = 𝓕⁻ f
  proof: rfl

中文:
引理 fourierCLE_symm_apply
  条件: (f : F)
  结论: (fourierCLE R E).symm f = 𝓕⁻ f
  证明: rfl
-/
lemma fourierCLE_symm_apply (f : F) : (fourierCLE R E).symm f = 𝓕⁻ f := rfl

end FourierTransform

end Pair
