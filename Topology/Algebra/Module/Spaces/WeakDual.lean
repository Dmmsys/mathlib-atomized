/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Moritz Doll
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin

/-!
# Weak dual topology

We continue in the setting of `Mathlib/Topology/Algebra/Module/WeakBilin.lean`,
which defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`𝕜` and a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `fun x => B x y` is continuous.

In this file, we consider two special cases.
In the case that `F = E →L[𝕜] 𝕜` and `B` being the canonical pairing, we obtain the weak-\*
topology, `WeakDual 𝕜 E := (E →L[𝕜] 𝕜)`. Interchanging the arguments in the bilinear form yields the
weak topology `WeakSpace 𝕜 E := E`.

## Main definitions

The main definitions are the types `WeakDual 𝕜 E` and `WeakSpace 𝕜 E`,
with the respective topology instances on it.

* `WeakDual 𝕜 E` is a type synonym for `Dual 𝕜 E` (when the latter is defined): both are equal to
  the type `E →L[𝕜] 𝕜` of continuous linear maps from a module `E` over `𝕜` to the ring `𝕜`.
* The instance `WeakDual.instTopologicalSpace` is the weak-\* topology on `WeakDual 𝕜 E`, i.e., the
  coarsest topology making the evaluation maps at all `z : E` continuous.
* `WeakSpace 𝕜 E` is a type synonym for `E` (when the latter is defined).
* The instance `WeakSpace.instTopologicalSpace` is the weak topology on `E`, i.e., the
  coarsest topology such that all `v : dual 𝕜 E` remain continuous.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

weak-star, weak dual, duality

-/

@[expose] public section


noncomputable section

open Filter

open Topology

variable {α 𝕜 𝕝 E F : Type*}

/-- The weak star topology is the topology coarsest topology on `E →L[𝕜] 𝕜` such that all
functionals `fun v => v x` are continuous. -/
/-
**WeakDual** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WeakDual (𝕜 E : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAd
d 𝕜] [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace 
E]
参数：𝕜 E : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weak star topology is the topology coarsest topology on `E →L[𝕜] 𝕜` such tha
t all
functionals `fun v => v x` are continuous.
-/
def WeakDual (𝕜 E : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E)
deriving TopologicalSpace, Inhabited, FunLike, ContinuousLinearMapClass

namespace WeakDual

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts on `WeakDual 𝕜 E`. -/
/-
**WeakDual.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual`。
形式化陈述：instMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜] 
[ContinuousConstSMul M 𝕜] : MulAction M (WeakDual 𝕜 E)
参数：M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a monoid `M` distributively continuously acts on `𝕜` and this action commutes
 with
multiplication on `𝕜`, then it acts on `WeakDual 𝕜 E`.
-/
instance instMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : MulAction M (WeakDual 𝕜 E) :=
  inferInstanceAs <| MulAction M (E →L[𝕜] 𝕜)

deriving instance AddCommMonoid, ContinuousAdd for WeakDual

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts distributively on `WeakDual 𝕜 E`. -/
/-
**WeakDual.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual`。
形式化陈述：instDistribMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 
𝕜 M 𝕜] [ContinuousConstSMul M 𝕜] : DistribMulAction M (WeakDual 𝕜 E)
参数：M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a monoid `M` distributively continuously acts on `𝕜` and this action commutes
 with
multiplication on `𝕜`, then it acts distributively on `WeakDual 𝕜 E`.
-/
instance instDistribMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : DistribMulAction M (WeakDual 𝕜 E) :=
  inferInstanceAs <| DistribMulAction M (E →L[𝕜] 𝕜)
/-
**WeakDual.instContinuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual`。
形式化陈述：instContinuousConstSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommCla
ss 𝕜 M 𝕜] [ContinuousConstSMul M 𝕜] : ContinuousConstSMul M (WeakDual 𝕜 E)
参数：M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instContinuousConstSMulForall`：∀ {M : Type u_1} {ι : Type u_4} {γ : ι → 
Type u_5} [inst : (i : ι) → TopologicalSpace (γ i)]   [inst_1 : (i : ι) → SMul M
 (γ i)] [∀ (i : ι),…
· 使用定理 `WeakBilin.coeFn_continuous`：coeFn_continuous : Continuous fun (x : WeakB
ilin B) y => B x y
-/
instance instContinuousConstSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : ContinuousConstSMul M (WeakDual 𝕜 E) :=
  ⟨fun m =>
    continuous_induced_rng.2 <| (WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).const_smul m⟩

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it continuously acts on `WeakDual 𝕜 E`. -/
/-
**WeakDual.instContinuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual`。
形式化陈述：instContinuousSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 
M 𝕜] [TopologicalSpace M] [ContinuousSMul M 𝕜] : ContinuousSMul M (WeakDual 𝕜 E)
参数：M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `Continuous.smul`：Continuous.smul (hf : Continuous f) (hg : Continuous g)
 : Continuous (f • g)
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `WeakBilin.coeFn_continuous`：coeFn_continuous : Continuous fun (x : WeakB
ilin B) y => B x y
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
If a monoid `M` distributively continuously acts on `𝕜` and this action commutes
 with
multiplication on `𝕜`, then it continuously acts on `WeakDual 𝕜 E`.
-/
instance instContinuousSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [TopologicalSpace M] [ContinuousSMul M 𝕜] : ContinuousSMul M (WeakDual 𝕜 E) :=
  ⟨continuous_induced_rng.2 <|
      continuous_fst.smul ((WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).comp continuous_snd)⟩

/-- If `𝕜` is a topological module over a semiring `R` and scalar multiplication commutes with the
multiplication on `𝕜`, then `WeakDual 𝕜 E` is a module over `R`. -/
/-
**WeakDual.** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `𝕜` is a topological module over a semiring `R` and scalar multiplication com
mutes with the
multiplication on `𝕜`, then `WeakDual 𝕜 E` is a module over `R`.
-/
instance (priority := 950) instModule'
    (R : Type*) [Semiring R] [Module R 𝕜] [SMulCommClass 𝕜 R 𝕜] [ContinuousConstSMul R 𝕜] :
    Module R (WeakDual 𝕜 E) :=
  inferInstanceAs <| Module R (E →L[𝕜] 𝕜)
/-
**WeakDual.instModule** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual`。
形式化陈述：instModule : Module 𝕜 (WeakDual 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule : Module 𝕜 (WeakDual 𝕜 E) := inferInstance

end WeakDual

namespace StrongDual

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- For vector spaces `E`, there is a canonical map `StrongDual 𝕜 E → WeakDual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. -/
/-
**StrongDual.toWeakDual** 是 Mathlib 中的一个定义，位于命名空间 `StrongDual`。
形式化陈述：toWeakDual : StrongDual 𝕜 E ≃ₗ[𝕜] WeakDual 𝕜 E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For vector spaces `E`, there is a canonical map `StrongDual 𝕜 E → WeakDual 𝕜 E` 
(the "identity"
mapping). It is a linear equivalence.
-/
def toWeakDual : StrongDual 𝕜 E ≃ₗ[𝕜] WeakDual 𝕜 E :=
  LinearEquiv.refl 𝕜 (StrongDual 𝕜 E)
/-
**StrongDual.coe_toWeakDual** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：coe_toWeakDual (x' : StrongDual 𝕜 E) : (toWeakDual x' : E -> 𝕜) = x'
参数：x' : StrongDual 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem coe_toWeakDual (x' : StrongDual 𝕜 E) : (toWeakDual x' : E → 𝕜) = x' := rfl

@[simp]
/-
**StrongDual.toWeakDual_apply** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：toWeakDual_apply (x' : StrongDual 𝕜 E) (y : E) : (toWeakDual x') y = x' y
参数：x' : StrongDual 𝕜 E；y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem toWeakDual_apply (x' : StrongDual 𝕜 E) (y : E) : (toWeakDual x') y = x' y := rfl
/-
**StrongDual.toWeakDual_inj** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：toWeakDual_inj (x' y' : StrongDual 𝕜 E) : toWeakDual x' = toWeakDual y' ↔ 
x' = y'
参数：x' y' : StrongDual 𝕜 E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem toWeakDual_inj (x' y' : StrongDual 𝕜 E) : toWeakDual x' = toWeakDual y' ↔ x' = y' :=
  (LinearEquiv.injective toWeakDual).eq_iff

end StrongDual

namespace WeakDual

section Semiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- For vector spaces `E`, there is a canonical map `WeakDual 𝕜 E → StrongDual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. Here it is implemented as the inverse of the linear
equivalence `StrongDual.toWeakDual` in the other direction. -/
/-
**WeakDual.toStrongDual** 是 Mathlib 中的一个定义，位于命名空间 `WeakDual`。
形式化陈述：toStrongDual : WeakDual 𝕜 E ≃ₗ[𝕜] StrongDual 𝕜 E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For vector spaces `E`, there is a canonical map `WeakDual 𝕜 E → StrongDual 𝕜 E` 
(the "identity"
mapping). It is a linear equivalence. Here it is implemented as the inverse of t
he linear
equivalence `StrongDual.toWeakDual` in the other direction.
-/
def toStrongDual : WeakDual 𝕜 E ≃ₗ[𝕜] StrongDual 𝕜 E :=
  StrongDual.toWeakDual.symm

@[simp]
/-
**WeakDual.symm_toStrongDual** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：symm_toStrongDual : (toStrongDual (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem symm_toStrongDual :
    (toStrongDual (𝕜 := 𝕜) (E := E)).symm = StrongDual.toWeakDual :=
  rfl

@[simp]
/-
**WeakDual._root_.StrongDual.symm_toWeakDual** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.StrongDual.symm_toWeakDual :
    (StrongDual.toWeakDual (𝕜 := 𝕜) (E := E)).symm = toStrongDual :=
  rfl

@[simp]
/-
**WeakDual._root_.StrongDual.toStrongDual_toWeakDual** 是 Mathlib 中的一个定理，位于命名空间 `
WeakDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.StrongDual.toStrongDual_toWeakDual (x : StrongDual 𝕜 E) :
    x.toWeakDual.toStrongDual = x :=
  rfl

@[simp]
/-
**WeakDual.toWeakDual_toStrongDual** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：toWeakDual_toStrongDual (x : WeakDual 𝕜 E) : x.toStrongDual.toWeakDual = x
参数：x : WeakDual 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem toWeakDual_toStrongDual (x : WeakDual 𝕜 E) : x.toStrongDual.toWeakDual = x :=
  rfl

@[simp]
/-
**WeakDual.toStrongDual_apply** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：toStrongDual_apply (x : WeakDual 𝕜 E) (y : E) : (toStrongDual x) y = x y
参数：x : WeakDual 𝕜 E；y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem toStrongDual_apply (x : WeakDual 𝕜 E) (y : E) : (toStrongDual x) y = x y := rfl
/-
**WeakDual.coe_toStrongDual** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：coe_toStrongDual (x' : WeakDual 𝕜 E) : (toStrongDual x' : E -> 𝕜) = x'
参数：x' : WeakDual 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem coe_toStrongDual (x' : WeakDual 𝕜 E) : (toStrongDual x' : E → 𝕜) = x' := rfl
/-
**WeakDual.toStrongDual_inj** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：toStrongDual_inj (x' y' : WeakDual 𝕜 E) : toStrongDual x' = toStrongDual y
' ↔ x' = y'
参数：x' y' : WeakDual 𝕜 E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem toStrongDual_inj (x' y' : WeakDual 𝕜 E) : toStrongDual x' = toStrongDual y' ↔ x' = y' :=
  (LinearEquiv.injective toStrongDual).eq_iff
/-
**WeakDual.coeFn_continuous** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：coeFn_continuous : Continuous fun (x : WeakDual 𝕜 E) y => x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
theorem coeFn_continuous : Continuous fun (x : WeakDual 𝕜 E) y => x y :=
  continuous_induced_dom
/-
**WeakDual.eval_continuous** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：eval_continuous (y : E) : Continuous fun x : WeakDual 𝕜 E => x y
参数：y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_pi_iff`：continuous_pi_iff : Continuous f ↔ forall i, Continuo
us fun a => f a i
· 使用定理 `WeakDual.coeFn_continuous`：coeFn_continuous : Continuous fun (x : WeakDu
al 𝕜 E) y => x y
-/
theorem eval_continuous (y : E) : Continuous fun x : WeakDual 𝕜 E => x y :=
  continuous_pi_iff.mp coeFn_continuous y
/-
**WeakDual.continuous_of_continuous_eval** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：continuous_of_continuous_eval [TopologicalSpace α] {g : α -> WeakDual 𝕜 E}
 (h : forall y, Continuous fun a => (g a) y) : Continuous g
参数：h : forall y, Continuous fun a => (g a) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `continuous_pi_iff`：continuous_pi_iff : Continuous f ↔ forall i, Continuo
us fun a => f a i
-/
theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakDual 𝕜 E}
    (h : ∀ y, Continuous fun a => (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)
/-
**WeakDual.instT2Space** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual`。
形式化陈述：instT2Space [T2Space 𝕜] : T2Space (WeakDual 𝕜 E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t2Space`：Topology.IsEmbedding.t2Space [TopologicalS
pace Y] [T2Space Y] {f : X -> Y} (hf : IsEmbedding f) : T2Space X
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `WeakBilin.isEmbedding`：isEmbedding {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜} (hB : Funct
ion.Injective B) : IsEmbedding fun (x : WeakBilin B) y => B x y
· 使用定理 `ContinuousLinearMap.coe_injective`：coe_injective : Function.Injective ((
↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
-/
instance instT2Space [T2Space 𝕜] : T2Space (WeakDual 𝕜 E) :=
  (WeakBilin.isEmbedding ContinuousLinearMap.coe_injective).t2Space

end Semiring

section Ring

variable [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜] [ContinuousConstSMul 𝕜 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/-
**WeakDual.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual`。
形式化陈述：instAddCommGroup : AddCommGroup (WeakDual 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup : AddCommGroup (WeakDual 𝕜 E) :=
  inferInstanceAs <| AddCommGroup (WeakBilin (topDualPairing 𝕜 E))
/-
**WeakDual.instIsTopologicalAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual`。
形式化陈述：instIsTopologicalAddGroup : IsTopologicalAddGroup (WeakDual 𝕜 E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (WeakDual 𝕜 E) :=
  WeakBilin.instIsTopologicalAddGroup (topDualPairing 𝕜 E)

end Ring

end WeakDual

/-- The weak topology is the coarsest topology on `E` such that all functionals
`fun x => v x` are continuous. -/
/-
**WeakSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WeakSpace (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [C
ontinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]
参数：𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weak topology is the coarsest topology on `E` such that all functionals
`fun x => v x` are continuous.
-/
def WeakSpace (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E).flip
deriving TopologicalSpace

section Semiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

-- The `SMul` instance exists to avoid an nsmul diamond.
variable [CommSemiring 𝕝] [Module 𝕝 E] in
deriving instance SMul 𝕝 for WeakSpace 𝕜 E

deriving instance AddCommMonoid, ContinuousAdd for WeakSpace

namespace WeakSpace

/-
**WeakSpace.instModule'** 是 Mathlib 中的一个实例，位于命名空间 `WeakSpace`。
形式化陈述：instModule' [CommSemiring 𝕝] [Module 𝕝 E] : Module 𝕝 (WeakSpace 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule' [CommSemiring 𝕝] [Module 𝕝 E] : Module 𝕝 (WeakSpace 𝕜 E) :=
  inferInstanceAs <| Module 𝕝 (WeakBilin (topDualPairing 𝕜 E).flip)
/-
**WeakSpace.instModule** 是 Mathlib 中的一个实例，位于命名空间 `WeakSpace`。
形式化陈述：instModule : Module 𝕜 (WeakSpace 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule : Module 𝕜 (WeakSpace 𝕜 E) := inferInstance
/-
**WeakSpace.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `WeakSpace`。
形式化陈述：instIsScalarTower [CommSemiring 𝕝] [Module 𝕝 𝕜] [Module 𝕝 E] [IsScalarTowe
r 𝕝 𝕜 E] : IsScalarTower 𝕝 𝕜 (WeakSpace 𝕜 E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance instIsScalarTower [CommSemiring 𝕝] [Module 𝕝 𝕜] [Module 𝕝 E] [IsScalarTower 𝕝 𝕜 E] :
    IsScalarTower 𝕝 𝕜 (WeakSpace 𝕜 E) :=
  WeakBilin.instIsScalarTower (topDualPairing 𝕜 E).flip
/-
**WeakSpace.instContinuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `WeakSpace`。
形式化陈述：instContinuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (WeakSpace 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instContinuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (WeakSpace 𝕜 E) :=
  WeakBilin.instContinuousSMul _

variable [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

/-- A continuous linear map from `E` to `F` is still continuous when `E` and `F` are equipped with
their weak topologies. -/
/-
**WeakSpace.map** 是 Mathlib 中的一个定义，位于命名空间 `WeakSpace`。
形式化陈述：map (f : E ->L[𝕜] F) : WeakSpace 𝕜 E ->L[𝕜] WeakSpace 𝕜 F
参数：f : E ->L[𝕜] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear map from `E` to `F` is still continuous when `E` and `F` are
 equipped with
their weak topologies.
-/
def map (f : E →L[𝕜] F) : WeakSpace 𝕜 E →L[𝕜] WeakSpace 𝕜 F :=
  { f with
    cont :=
      WeakBilin.continuous_of_continuous_eval _ fun l => WeakBilin.eval_continuous _ (l ∘L f) }
/-
**WeakSpace.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `WeakSpace`。
形式化陈述：map_apply (f : E ->L[𝕜] F) (x : E) : WeakSpace.map f x = f x
参数：f : E ->L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply (f : E →L[𝕜] F) (x : E) : WeakSpace.map f x = f x :=
  rfl

@[simp]
/-
**WeakSpace.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `WeakSpace`。
形式化陈述：coe_map (f : E ->L[𝕜] F) : (WeakSpace.map f : E -> F) = f
参数：f : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (f : E →L[𝕜] F) : (WeakSpace.map f : E → F) = f :=
  rfl

end WeakSpace

variable (𝕜 E) in
/-- There is a canonical map `E → WeakSpace 𝕜 E` (the "identity"
mapping). It is a linear equivalence. -/
/-
**toWeakSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toWeakSpace : E ≃ₗ[𝕜] WeakSpace 𝕜 E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a canonical map `E → WeakSpace 𝕜 E` (the "identity"
mapping). It is a linear equivalence.
-/
def toWeakSpace : E ≃ₗ[𝕜] WeakSpace 𝕜 E := LinearEquiv.refl 𝕜 E

variable (𝕜 E) in
/-- For a topological vector space `E`, "identity mapping" `E → WeakSpace 𝕜 E` is continuous.
This definition implements it as a continuous linear map. -/
/-
**toWeakSpaceCLM** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toWeakSpaceCLM : E ->L[𝕜] WeakSpace 𝕜 E where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a topological vector space `E`, "identity mapping" `E → WeakSpace 𝕜 E` is co
ntinuous.
This definition implements it as a continuous linear map.
-/
def toWeakSpaceCLM : E →L[𝕜] WeakSpace 𝕜 E where
  __ := toWeakSpace 𝕜 E
  cont := by
    apply WeakBilin.continuous_of_continuous_eval
    exact ContinuousLinearMap.continuous

variable (𝕜 E) in
@[simp]
/-
**toWeakSpaceCLM_eq_toWeakSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toWeakSpaceCLM_eq_toWeakSpace (x : E) : toWeakSpaceCLM 𝕜 E x = toWeakSpace
 𝕜 E x
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toWeakSpaceCLM_eq_toWeakSpace (x : E) :
    toWeakSpaceCLM 𝕜 E x = toWeakSpace 𝕜 E x := by rfl
/-
**toWeakSpaceCLM_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toWeakSpaceCLM_bijective : Function.Bijective (toWeakSpaceCLM 𝕜 E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem toWeakSpaceCLM_bijective :
    Function.Bijective (toWeakSpaceCLM 𝕜 E) :=
  (toWeakSpace 𝕜 E).bijective

/-- The canonical map from `WeakSpace 𝕜 E` to `E` is an open map. -/
/-
**isOpenMap_toWeakSpace_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_toWeakSpace_symm : IsOpenMap (toWeakSpace 𝕜 E).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.of_inverse`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f' : Y → X},   Continuous f
' → Functi…
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…

--- 原说明 ---
The canonical map from `WeakSpace 𝕜 E` to `E` is an open map.
-/
theorem isOpenMap_toWeakSpace_symm : IsOpenMap (toWeakSpace 𝕜 E).symm :=
  IsOpenMap.of_inverse (toWeakSpaceCLM 𝕜 E).cont
    (toWeakSpace 𝕜 E).left_inv (toWeakSpace 𝕜 E).right_inv

/-- A set in `E` which is open in the weak topology is open. -/
/-
**WeakSpace.isOpen_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WeakSpace.isOpen_of_isOpen (V : Set E) (hV : IsOpen ((toWeakSpaceCLM 𝕜 E) 
'' V : Set (WeakSpace 𝕜 E))) : IsOpen V
参数：V : Set E；hV : IsOpen ((toWeakSpaceCLM 𝕜 E) '' V : Set (WeakSpace 𝕜 E))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `toWeakSpaceCLM_eq_toWeakSpace`：toWeakSpaceCLM_eq_toWeakSpace (x : E) : t
oWeakSpaceCLM 𝕜 E x = toWeakSpace 𝕜 E x
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `isOpenMap_toWeakSpace_symm`：isOpenMap_toWeakSpace_symm : IsOpenMap (toWe
akSpace 𝕜 E).symm

--- 原说明 ---
A set in `E` which is open in the weak topology is open.
-/
theorem WeakSpace.isOpen_of_isOpen (V : Set E)
    (hV : IsOpen ((toWeakSpaceCLM 𝕜 E) '' V : Set (WeakSpace 𝕜 E))) : IsOpen V := by
  simpa [Set.image_image] using isOpenMap_toWeakSpace_symm _ hV
/-
**tendsto_iff_forall_eval_tendsto_topDualPairing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_iff_forall_eval_tendsto_topDualPairing {l : Filter α} {f : α -> We
akDual 𝕜 E} {x : WeakDual 𝕜 E} : Tendsto f l (𝓝 x) ↔ forall y, Tendsto (fun i =>
 topDualPairing 𝕜 E (f i) y) l (𝓝 (topDualPairing 𝕜 E x y))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeakBilin.tendsto_iff_forall_eval_tendsto`：tendsto_iff_forall_eval_tends
to {l : Filter α} {f : α -> WeakBilin B} {x : WeakBilin B} (hB : Function.Inject
ive B) : Tendsto f l (𝓝 x) ↔ fo…
· 使用定理 `ContinuousLinearMap.coe_injective`：coe_injective : Function.Injective ((
↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
-/
theorem tendsto_iff_forall_eval_tendsto_topDualPairing {l : Filter α} {f : α → WeakDual 𝕜 E}
    {x : WeakDual 𝕜 E} :
    Tendsto f l (𝓝 x) ↔
      ∀ y, Tendsto (fun i => topDualPairing 𝕜 E (f i) y) l (𝓝 (topDualPairing 𝕜 E x y)) :=
  WeakBilin.tendsto_iff_forall_eval_tendsto _ ContinuousLinearMap.coe_injective

end Semiring

section Ring

namespace WeakSpace

variable [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜] [ContinuousConstSMul 𝕜 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/-
**WeakSpace.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `WeakSpace`。
形式化陈述：instAddCommGroup : AddCommGroup (WeakSpace 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup : AddCommGroup (WeakSpace 𝕜 E) :=
  inferInstanceAs <| AddCommGroup (WeakBilin (topDualPairing 𝕜 E).flip)
/-
**WeakSpace.instIsTopologicalAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `WeakSpace`。
形式化陈述：instIsTopologicalAddGroup : IsTopologicalAddGroup (WeakSpace 𝕜 E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (WeakSpace 𝕜 E) :=
  WeakBilin.instIsTopologicalAddGroup (topDualPairing 𝕜 E).flip

end WeakSpace

end Ring

