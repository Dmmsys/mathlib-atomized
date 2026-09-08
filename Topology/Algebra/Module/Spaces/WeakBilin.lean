/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Moritz Doll
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Weak dual topology

This file defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`𝕜` and a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `fun x => B x y` is continuous.

## Main definitions

The main definition is the type `WeakBilin B`.

* Given `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, the type `WeakBilin B` is a type synonym for `E`.
* The instance `WeakBilin.instTopologicalSpace` is the weak topology induced by the bilinear form
  `B`.

## Main results

We establish that `WeakBilin B` has the following structure:
* `WeakBilin.instContinuousAdd`: The addition in `WeakBilin B` is continuous.
* `WeakBilin.instContinuousSMul`: The scalar multiplication in `WeakBilin B` is continuous.

We prove the following results characterizing the weak topology:
* `eval_continuous`: For any `y : F`, the evaluation mapping `fun x => B x y` is continuous.
* `continuous_of_continuous_eval`: For a mapping to `WeakBilin B` to be continuous,
  it suffices that its compositions with pairing with `B` at all points `y : F` is continuous.
* `tendsto_iff_forall_eval_tendsto`: Convergence in `WeakBilin B` can be characterized
  in terms of convergence of the evaluations at all points `y : F`.

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

section WeakTopology

/-- The space `E` equipped with the weak topology induced by the bilinear form `B`. -/
@[nolint unusedArguments]
/-
**WeakBilin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WeakBilin [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F
] [Module 𝕜 F] (_ : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)
参数：_ : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space `E` equipped with the weak topology induced by the bilinear form `B`.
-/
def WeakBilin [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    (_ : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) := E

namespace WeakBilin

variable [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
  (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [CommSemiring 𝕝] [Module 𝕝 E] in
deriving instance SMul 𝕝, AddCommMonoid, Module 𝕝 for WeakBilin B

/-
**WeakBilin.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `WeakBilin`。
形式化陈述：instAddCommGroup [CommSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommMo
noid F] [Module 𝕜 F] (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) : AddCommGroup (WeakBilin B)
参数：B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup [CommSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : AddCommGroup (WeakBilin B) :=
  inferInstanceAs <| AddCommGroup E
/-
**WeakBilin.** 是 Mathlib 中的一个实例，位于命名空间 `WeakBilin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : Module 𝕜 (WeakBilin B) :=
  inferInstance
/-
**WeakBilin.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `WeakBilin`。
形式化陈述：instIsScalarTower [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommMonoid E] [Mod
ule 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] [SMul 𝕝 𝕜] [Module 𝕝 E] [IsScalarTower 𝕝
 𝕜 E] (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) : IsScalarTower 𝕝 𝕜 (WeakBilin B)
参数：B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance instIsScalarTower [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommMonoid E] [Module 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F] [SMul 𝕝 𝕜] [Module 𝕝 E] [IsScalarTower 𝕝 𝕜 E]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : IsScalarTower 𝕝 𝕜 (WeakBilin B) :=
  inferInstanceAs <| IsScalarTower 𝕝 𝕜 E

section Semiring

variable [TopologicalSpace 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]
variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-
**WeakBilin.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `WeakBilin`。
形式化陈述：instTopologicalSpace : TopologicalSpace (WeakBilin B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpace : TopologicalSpace (WeakBilin B) :=
  TopologicalSpace.induced (fun x y => B x y) Pi.topologicalSpace

/-- The coercion `(fun x y => B x y) : E → (F → 𝕜)` is continuous. -/
/-
**WeakBilin.coeFn_continuous** 是 Mathlib 中的一个定理，位于命名空间 `WeakBilin`。
形式化陈述：coeFn_continuous : Continuous fun (x : WeakBilin B) y => B x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f

--- 原说明 ---
The coercion `(fun x y => B x y) : E → (F → 𝕜)` is continuous.
-/
theorem coeFn_continuous : Continuous fun (x : WeakBilin B) y => B x y :=
  continuous_induced_dom

@[fun_prop]
/-
**WeakBilin.eval_continuous** 是 Mathlib 中的一个定理，位于命名空间 `WeakBilin`。
形式化陈述：eval_continuous (y : F) : Continuous fun x : WeakBilin B => B x y
参数：y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_pi_iff`：continuous_pi_iff : Continuous f ↔ forall i, Continuo
us fun a => f a i
· 使用定理 `WeakBilin.coeFn_continuous`：coeFn_continuous : Continuous fun (x : WeakB
ilin B) y => B x y
-/
theorem eval_continuous (y : F) : Continuous fun x : WeakBilin B => B x y :=
  (continuous_pi_iff.mp (coeFn_continuous B)) y
/-
**WeakBilin.continuous_of_continuous_eval** 是 Mathlib 中的一个定理，位于命名空间 `WeakBilin`。
形式化陈述：continuous_of_continuous_eval [TopologicalSpace α] {g : α -> WeakBilin B} 
(h : forall y, Continuous fun a => B (g a) y) : Continuous g
参数：h : forall y, Continuous fun a => B (g a) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `continuous_pi_iff`：continuous_pi_iff : Continuous f ↔ forall i, Continuo
us fun a => f a i
-/
theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakBilin B}
    (h : ∀ y, Continuous fun a => B (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)

/-- The coercion `(fun x y => B x y) : E → (F → 𝕜)` is an embedding. -/
/-
**WeakBilin.isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `WeakBilin`。
形式化陈述：isEmbedding {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜} (hB : Function.Injective B) : IsEmbe
dding fun (x : WeakBilin B) y => B x y
参数：hB : Function.Injective B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Function.Injective.isEmbedding_induced`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [t : TopologicalSpace Y], Function.Injective f → Topology.IsEmbeddin
g f
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearMap.coe_injective`：coe_injective : Injective (DFunLike.coe : (M ->
ₛₗ[σ] M₃) -> _)

--- 原说明 ---
The coercion `(fun x y => B x y) : E → (F → 𝕜)` is an embedding.
-/
theorem isEmbedding {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (hB : Function.Injective B) :
    IsEmbedding fun (x : WeakBilin B) y => B x y :=
  Function.Injective.isEmbedding_induced <| LinearMap.coe_injective.comp hB
/-
**WeakBilin.tendsto_iff_forall_eval_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `WeakBilin
`。
形式化陈述：tendsto_iff_forall_eval_tendsto {l : Filter α} {f : α -> WeakBilin B} {x :
 WeakBilin B} (hB : Function.Injective B) : Tendsto f l (𝓝 x) ↔ forall y, Tendst
o (fun i => B (f i) y) l (𝓝 (B x y))
参数：hB : Function.Injective B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Topology.IsEmbedding.tendsto_nhds_iff`：∀ {Y : Type u_2} {Z : Type u_3} {
ι : Type u_4} {g : Y → Z} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace
 Z]   {f : ι → Y} {l : Filt…
· 使用定理 `WeakBilin.isEmbedding`：isEmbedding {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜} (hB : Funct
ion.Injective B) : IsEmbedding fun (x : WeakBilin B) y => B x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_iff_forall_eval_tendsto {l : Filter α} {f : α → WeakBilin B} {x : WeakBilin B}
    (hB : Function.Injective B) :
    Tendsto f l (𝓝 x) ↔ ∀ y, Tendsto (fun i => B (f i) y) l (𝓝 (B x y)) := by
  rw [← tendsto_pi_nhds, (isEmbedding hB).tendsto_nhds_iff]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Addition in `WeakBilin B` is continuous. -/
/-
**WeakBilin.instContinuousAdd** 是 Mathlib 中的一个实例，位于命名空间 `WeakBilin`。
形式化陈述：instContinuousAdd [ContinuousAdd 𝕜] : ContinuousAdd (WeakBilin B)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `WeakBilin.coeFn_continuous`：coeFn_continuous : Continuous fun (x : WeakB
ilin B) y => B x y
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
Addition in `WeakBilin B` is continuous.
-/
instance instContinuousAdd [ContinuousAdd 𝕜] : ContinuousAdd (WeakBilin B) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine
    cast (congr_arg _ ?_)
      (((coeFn_continuous B).comp continuous_fst).add ((coeFn_continuous B).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.add_apply, map_add, LinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Scalar multiplication by `𝕜` on `WeakBilin B` is continuous. -/
/-
**WeakBilin.instContinuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `WeakBilin`。
形式化陈述：instContinuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (WeakBilin B)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `WeakBilin.coeFn_continuous`：coeFn_continuous : Continuous fun (x : WeakB
ilin B) y => B x y
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
Scalar multiplication by `𝕜` on `WeakBilin B` is continuous.
-/
instance instContinuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (WeakBilin B) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine cast (congr_arg _ ?_) (continuous_fst.fun_smul ((coeFn_continuous B).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.smul_apply, map_smulₛₗ, RingHom.id_apply, LinearMap.smul_apply]

set_option backward.isDefEq.respectTransparency false in
/--
Map `F` into the topological dual of `E` with the weak topology induced by `F`
-/
/-
**WeakBilin.eval** 是 Mathlib 中的一个定义，位于命名空间 `WeakBilin`。
形式化陈述：eval [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] : F ->ₗ[𝕜] StrongDual 𝕜 (
WeakBilin B) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map `F` into the topological dual of `E` with the weak topology induced by `F`
-/
def eval [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] :
    F →ₗ[𝕜] StrongDual 𝕜 (WeakBilin B) where
  toFun f := ⟨B.flip f, by fun_prop⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

end Semiring

section Ring

variable [TopologicalSpace 𝕜] [CommRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]


variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

set_option backward.isDefEq.respectTransparency false in
/-- `WeakBilin B` is a `IsTopologicalAddGroup`, meaning that addition and negation are
continuous. -/
/-
**WeakBilin.instIsTopologicalAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `WeakBilin`。
形式化陈述：instIsTopologicalAddGroup [ContinuousAdd 𝕜] : IsTopologicalAddGroup (WeakB
ilin B) where toContinuousAdd
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `continuous_pi_iff`：continuous_pi_iff : Continuous f ↔ forall i, Continuo
us fun a => f a i
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `WeakBilin.eval_continuous`：eval_continuous (y : F) : Continuous fun x : 
WeakBilin B => B x y

--- 原说明 ---
`WeakBilin B` is a `IsTopologicalAddGroup`, meaning that addition and negation a
re
continuous.
-/
instance instIsTopologicalAddGroup [ContinuousAdd 𝕜] : IsTopologicalAddGroup (WeakBilin B) where
  toContinuousAdd := by infer_instance
  continuous_neg := by
    refine continuous_induced_rng.2 (continuous_pi_iff.mpr fun y => ?_)
    refine cast (congr_arg _ ?_) (eval_continuous B (-y))
    ext x
    simp only [map_neg, Function.comp_apply, LinearMap.neg_apply]

end Ring

end WeakBilin

end WeakTopology

