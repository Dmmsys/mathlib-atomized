/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.LinearAlgebra.BilinearMap

/-! # Weak topologies on modules

Given a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, the weak topology on `E` is the coarsest topology
such that for all `y : F` every map `(B · y)` is continuous; equivalently, it is the topology
on `E` induced by the map `(B · · : E → (F → 𝕜))`.

This file defines a `Prop`-valued typeclass `LinearMap.IsWeak` expressing that an existing topology
on `E` is the weak topology. Although this could be passed around explicitly as a hypothesis
`Topology.IsInducing (B · ·)`, given the ubiquity of weak topologies in functional analysis, the
numerous properties that can be deduced because the inducing map `B` is bilinear, the fact that
several theorems (e.g., one version of the bipolar theorem) require this hypothesis, and we can
instantiate this class for several extant types in Mathlib, we choose to make this a typeclass
instead.

Note that establishing `LinearMap.IsWeak` before proving theorems about a particular type can help
prevent abuse of definitional equalities. This because spaces equipped with a weak topology are
frequently type synonyms of some other type `E'`. For example, suppose `E'` is a type (potentially
with some extant topology other than the weak topology) and `B' : E' →ₗ[𝕜] F →ₗ[𝕜] 𝕜` is a
bilinear form. To consider the weak topology on `E'` induced by `B'`, in practice we must create a
type synonym `E` with an instance `TopologicalSpace E := .induced (B' · ·) Pi.topologicalSpace`.
It would then be tempting to create theorems such as:

```lean
example (y : F) : Continuous (fun x : E ↦ B' x y) := sorry
```

However, this statement contains an abuse of the the definitional equality `E := E'` since `x : E`,
but `B'` has domain `E'`. Moreover, one might be tempted to say that `B'.IsWeak`, but this is
impossible because the domain of `B'` is `E'`, which is equipped with the incorrect topology.
Instead, what one should do is to first define a new bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` by
composing `B'` with the linear equivalence between `E` and `E'`, and then establish `B.IsWeak`.
If then one proves theorems about `E` using only the `LinearMap.IsWeak` API, then one can have more
confidence that the statements are type correct.

## Main definitions

+ `LinearMap.IsWeak`: a typeclass expressing that the topology on `E` is the weak topology induced
  by the bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`.
+ `LinearMap.IsWeak.eval`: the evaluation map `F →ₗ[𝕜] StrongDual 𝕜 E` sending `y : F` to the
  continuous linear functional `(B · y)`.

## Main results

We prove the following results characterizing the weak topology:

* `LinearMap.IsWeak.continuous_eval`: For any `y : F`, the evaluation mapping `(B · y)` is
  continuous.
* `LinearMap.IsWeak.continuous_of_continuous_eval`: For a mapping to `WeakBilin B` to be continuous,
  it suffices that its compositions with pairing with `B` at all points `y : F` is continuous.
* `LinearMap.IsWeak.tendsto_iff_forall_eval_tendsto`: Convergence in `WeakBilin B` can be
  characterized in terms of convergence of the evaluations at all points `y : F`.

-/

@[expose] public section

open Topology Filter

section Basic

variable {α 𝕜 E F E' F' : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜]
    [AddCommMonoid E] [Module 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F]

/-- Typeclass expressing that the topology on `E` is the weak topology induced
by the bilinear form `B`. -/
@[mk_iff]
/-
**LinearMap.IsWeak** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinearMap`。
形式化陈述：{𝕜 : Type u_2} →   {E : Type u_3} →     {F : Type u_4} →       [inst : Com
mSemiring 𝕜] →         [TopologicalSpace 𝕜] →           [inst_2 : AddCommMonoid 
E] →             [inst_3 : _root_.Module 𝕜 E] →               [inst_4 : AddCommM
onoid F] →                 [inst_5 : _root_.Module 𝕜 F] → [t : TopologicalSpace 
E] → (E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) → Prop
参数：E →ₗ[𝕜] F →ₗ[𝕜] 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass expressing that the topology on `E` is the weak topology induced
by the bilinear form `B`.
-/
class LinearMap.IsWeak [t : TopologicalSpace E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : Prop where
  eq_induced : t = .induced (B · ·) Pi.topologicalSpace

variable [inst : TopologicalSpace E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsWeak]

namespace LinearMap.IsWeak

/-
**LinearMap.IsWeak.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap.IsWeak`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : B.flip.flip.IsWeak := hB

/-- The coercion `(B · ·) : E → (F → 𝕜)` is continuous. -/
/-
**LinearMap.IsWeak.coeFn_continuous** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsWeak`
。
形式化陈述：coeFn_continuous : Continuous (B · ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsWeak.eq_induced`：∀ {𝕜 : Type u_2} {E : Type u_3} {F : Type u
_4} {inst : CommSemiring 𝕜} {inst_1 : TopologicalSpace 𝕜}   {inst_2 : AddCommMon
oid E} {inst_3 : …

--- 原说明 ---
The coercion `(B · ·) : E → (F → 𝕜)` is continuous.
-/
theorem coeFn_continuous : Continuous (B · ·) :=
  hB.eq_induced ▸ continuous_induced_dom

/-- The evaluation map `(B · y) : E → 𝕜` is continuous for each `y : F`. -/
@[fun_prop]
/-
**LinearMap.IsWeak.continuous_eval** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.IsWeak`。
形式化陈述：continuous_eval (y : F) : Continuous (B · y)
参数：y : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_pi_iff`：continuous_pi_iff : Continuous f ↔ forall i, Continuo
us fun a => f a i
· 使用定理 `LinearMap.IsWeak.coeFn_continuous`：coeFn_continuous : Continuous (B · ·)

--- 原说明 ---
The evaluation map `(B · y) : E → 𝕜` is continuous for each `y : F`.
-/
lemma continuous_eval (y : F) : Continuous (B · y) :=
  continuous_pi_iff.mp (coeFn_continuous B) _

/-- A map `f : α → E` is continuous if all the maps `fun a ↦ B (f a) y` are continuous
for each `y : F`. -/
/-
**LinearMap.IsWeak.continuous_of_continuous_eval** 是 Mathlib 中的一个引理，位于命名空间 `Line
arMap.IsWeak`。
形式化陈述：continuous_of_continuous_eval {α : Type*} [TopologicalSpace α] {f : α -> E
} (hf : forall y, Continuous (fun x => B (f x) y)) : Continuous f
参数：hf : forall y, Continuous (fun x => B (f x) y)。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsWeak.eq_induced`：∀ {𝕜 : Type u_2} {E : Type u_3} {F : Type u
_4} {inst : CommSemiring 𝕜} {inst_1 : TopologicalSpace 𝕜}   {inst_2 : AddCommMon
oid E} {inst_3 : …

--- 原说明 ---
A map `f : α → E` is continuous if all the maps `fun a ↦ B (f a) y` are continuo
us
for each `y : F`.
-/
lemma continuous_of_continuous_eval {α : Type*} [TopologicalSpace α]
    {f : α → E} (hf : ∀ y, Continuous (fun x ↦ B (f x) y)) :
    Continuous f :=
  hB.eq_induced ▸ continuous_induced_rng.mpr (continuous_pi_iff.mpr hf)
/-
**LinearMap.IsWeak.continuous_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.IsWeak`。
形式化陈述：continuous_iff {α : Type*} [TopologicalSpace α] {f : α -> E} : Continuous 
f ↔ forall y, Continuous (fun x => B (f x) y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用引理 `LinearMap.IsWeak.continuous_eval`：continuous_eval (y : F) : Continuous (
B · y)
· 使用引理 `LinearMap.IsWeak.continuous_of_continuous_eval`：continuous_of_continuous
_eval {α : Type*} [TopologicalSpace α] {f : α -> E} (hf : forall y, Continuous (
fun x => B (f x) y)) : Continuous f
-/
lemma continuous_iff {α : Type*} [TopologicalSpace α] {f : α → E} :
    Continuous f ↔ ∀ y, Continuous (fun x ↦ B (f x) y) :=
  ⟨fun _ ↦ by fun_prop, hB.continuous_of_continuous_eval⟩

/-- The coercion `(B · ·) : E → (F → 𝕜)` is an embedding. -/
/-
**LinearMap.IsWeak.isInducing** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsWeak`。
形式化陈述：isInducing : IsInducing (B · ·) where eq_induced
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsWeak.eq_induced`：∀ {𝕜 : Type u_2} {E : Type u_3} {F : Type u
_4} {inst : CommSemiring 𝕜} {inst_1 : TopologicalSpace 𝕜}   {inst_2 : AddCommMon
oid E} {inst_3 : …

--- 原说明 ---
The coercion `(B · ·) : E → (F → 𝕜)` is an embedding.
-/
theorem isInducing : IsInducing (B · ·) where
  eq_induced := hB.eq_induced

variable {B} in
/-- The coercion `(B · ·) : E → (F → 𝕜)` is an embedding. -/
/-
**LinearMap.IsWeak.isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsWeak`。
形式化陈述：isEmbedding (hB_inj : Function.Injective B) : IsEmbedding (B · ·)
参数：hB_inj : Function.Injective B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsWeak.eq_induced`：∀ {𝕜 : Type u_2} {E : Type u_3} {F : Type u
_4} {inst : CommSemiring 𝕜} {inst_1 : TopologicalSpace 𝕜}   {inst_2 : AddCommMon
oid E} {inst_3 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.isEmbedding_induced`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [t : TopologicalSpace Y], Function.Injective f → Topology.IsEmbeddin
g f
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearMap.coe_injective`：coe_injective : Injective (DFunLike.coe : (M ->
ₛₗ[σ] M₃) -> _)

--- 原说明 ---
The coercion `(B · ·) : E → (F → 𝕜)` is an embedding.
-/
theorem isEmbedding (hB_inj : Function.Injective B) :
    IsEmbedding (B · ·) := by
  convert! (LinearMap.coe_injective.comp hB_inj |>.isEmbedding_induced)
  exact hB.eq_induced

variable {B} in
/-
**LinearMap.IsWeak.tendsto_iff_forall_eval_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap.IsWeak`。
形式化陈述：tendsto_iff_forall_eval_tendsto {α : Type*} {l : Filter α} {f : α -> E} {x
 : E} (hB_inj : Function.Injective B) : Tendsto f l (𝓝 x) ↔ forall y, Tendsto (f
un i => B (f i) y) l (𝓝 (B x y))
参数：hB_inj : Function.Injective B。
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
· 使用定理 `LinearMap.IsWeak.isEmbedding`：isEmbedding (hB_inj : Function.Injective B
) : IsEmbedding (B · ·)
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_iff_forall_eval_tendsto {α : Type*} {l : Filter α} {f : α → E} {x : E}
    (hB_inj : Function.Injective B) :
    Tendsto f l (𝓝 x) ↔ ∀ y, Tendsto (fun i ↦ B (f i) y) l (𝓝 (B x y)) := by
  rw [← tendsto_pi_nhds, (isEmbedding hB_inj).tendsto_nhds_iff, Function.comp_def]

/-- Suppose `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` and `B' : E' →ₗ[𝕜] F' →ₗ[𝕜] 𝕜` are bilinear maps such that
`E ≃L[𝕜] E'` and `F ≃ₗ[𝕜] F'`. If `B.IsWeak`, then so also `B'.IsWeak`. -/
/-
**LinearMap.IsWeak.congr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsWeak`。
形式化陈述：∀ {𝕜 : Type u_2} {E : Type u_3} {F : Type u_4} {E' : Type u_5} {F' : Type 
u_6} [inst : CommSemiring 𝕜]   [inst_1 : TopologicalSpace 𝕜] [inst_2 : AddCommMo
noid E] [inst_3 : _root_.Module 𝕜 E] [inst_4 : AddCommMonoid F]   [inst_5 : _roo
t_.Module 𝕜 F] [inst_6 : TopologicalSpace E] [inst_7 : AddCommMonoid E'] [inst_8
 : _root_.Module 𝕜 E']   [inst_9 : AddCommMonoid F'] [inst_10 : _root_.Module 𝕜 
F'] [inst_11 : TopologicalSpace E'] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)   (B' : E' →ₗ[𝕜] F' 
→ₗ[𝕜] 𝕜) (e : E ≃L[𝕜] E') (f : F ≃ₗ[𝕜] F'),   ((↑e).arrowCongr (f.arrowCongr (Li
nearEquiv.refl 𝕜 𝕜))) B = B' → ∀ [hB : B.IsWeak], B'.IsWeak
参数：B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜；B' : E' →ₗ[𝕜] F' →ₗ[𝕜] 𝕜；e : E ≃L[𝕜] E'；f : F ≃ₗ[𝕜] F'；
(↑e).arrowCongr (f.arrowCongr (LinearEquiv.refl 𝕜 𝕜))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.induced_eq`：induced_eq (h : X ≃ₜ Y) : TopologicalSpace.induce
d h ‹_› = ‹_›
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.IsWeak.eq_induced`：∀ {𝕜 : Type u_2} {E : Type u_3} {F : Type u
_4} {inst : CommSemiring 𝕜} {inst_1 : TopologicalSpace 𝕜}   {inst_2 : AddCommMon
oid E} {inst_3 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `induced_to_pi`：induced_to_pi {X : Type*} (f : X -> forall i, A i) : indu
ced f Pi.topologicalSpace = ⨅ i, induced (f · i) inferInstance
· 使用定理 `Equiv.iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst 
: InfSet α] {f : ι → α} {g : ι' → α} (e : ι ≃ ι'),   (∀ (x : ι), g (e x) = f x) 
→ ⨅ x,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Suppose `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` and `B' : E' →ₗ[𝕜] F' →ₗ[𝕜] 𝕜` are bilinear maps
 such that
`E ≃L[𝕜] E'` and `F ≃ₗ[𝕜] F'`. If `B.IsWeak`, then so also `B'.IsWeak`.
-/
protected theorem congr [AddCommMonoid E'] [Module 𝕜 E']
    [AddCommMonoid F'] [Module 𝕜 F'] [TopologicalSpace E']
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (B' : E' →ₗ[𝕜] F' →ₗ[𝕜] 𝕜) (e : E ≃L[𝕜] E') (f : F ≃ₗ[𝕜] F')
    (hBB' : e.toLinearEquiv.arrowCongr (f.arrowCongr (.refl ..)) B = B') [hB : B.IsWeak] :
    B'.IsWeak where
  eq_induced := by
    rw [e.symm.toHomeomorph.induced_eq.symm]
    apply congr(TopologicalSpace.induced e.symm $(hB.eq_induced)).trans
    simp_rw [induced_compose, ← hBB', induced_to_pi]
    rw [f.toEquiv.iInf_congr]
    simp

/-- Map `F` into the topological dual of `E` with the weak topology induced by `F` -/
/-
**LinearMap.IsWeak.eval** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.IsWeak`。
形式化陈述：eval [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] : F ->ₗ[𝕜] StrongDual 𝕜 E
 where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map `F` into the topological dual of `E` with the weak topology induced by `F`
-/
def eval [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] : F →ₗ[𝕜] StrongDual 𝕜 E where
  toFun f := ⟨B.flip f, by fun_prop⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

include hB in
/-- Addition in `E` is continuous when `E` is equipped with a `LinearMap.IsWeak` topology. -/
/-
**LinearMap.IsWeak.continuousAdd** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsWeak`。
形式化陈述：continuousAdd [ContinuousAdd 𝕜] : ContinuousAdd E where continuous_add
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsWeak.eq_induced`：∀ {𝕜 : Type u_2} {E : Type u_3} {F : Type u
_4} {inst : CommSemiring 𝕜} {inst_1 : TopologicalSpace 𝕜}   {inst_2 : AddCommMon
oid E} {inst_3 : …
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用引理 `LinearMap.IsWeak.continuous_eval`：continuous_eval (y : F) : Continuous (
B · y)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2

--- 原说明 ---
Addition in `E` is continuous when `E` is equipped with a `LinearMap.IsWeak` top
ology.
-/
theorem continuousAdd [ContinuousAdd 𝕜] : ContinuousAdd E where
  continuous_add := by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced, continuous_induced_rng]
    simp only [Function.comp_def, map_add, add_apply]
    fun_prop

include hB in
/-- Scalar multiplication in `E` is continuous when `E` is equipped with a `LinearMap.IsWeak`
topology. -/
/-
**LinearMap.IsWeak.continuousSMul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsWeak`。
形式化陈述：continuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 E where continuous_
smul
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsWeak.eq_induced`：∀ {𝕜 : Type u_2} {E : Type u_3} {F : Type u
_4} {inst : CommSemiring 𝕜} {inst_1 : TopologicalSpace 𝕜}   {inst_2 : AddCommMon
oid E} {inst_3 : …
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用引理 `LinearMap.IsWeak.continuous_eval`：continuous_eval (y : F) : Continuous (
B · y)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2

--- 原说明 ---
Scalar multiplication in `E` is continuous when `E` is equipped with a `LinearMa
p.IsWeak`
topology.
-/
theorem continuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 E where
  continuous_smul := by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced, continuous_induced_rng]
    simp only [Function.comp_def, map_smul, smul_apply]
    fun_prop

/-- `E` is a `IsTopologicalAddGroup` when `E` is equipped with a `LinearMap.IsWeak` topology. -/
/-
**LinearMap.IsWeak.isTopologicalAddGroup** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Is
Weak`。
形式化陈述：isTopologicalAddGroup {𝕜 E F : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [A
ddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace E] [
ContinuousAdd 𝕜] (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) [hB : B.IsWeak] : IsTopologicalAddGro
up E where toContinuousAdd
参数：B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsWeak.continuousAdd`：continuousAdd [ContinuousAdd 𝕜] : Contin
uousAdd E where continuous_add
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsWeak.eq_induced`：∀ {𝕜 : Type u_2} {E : Type u_3} {F : Type u
_4} {inst : CommSemiring 𝕜} {inst_1 : TopologicalSpace 𝕜}   {inst_2 : AddCommMon
oid E} {inst_3 : …
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `continuous_pi_iff`：continuous_pi_iff : Continuous f ↔ forall i, Continuo
us fun a => f a i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.IsWeak.continuous_eval`：continuous_eval (y : F) : Continuous (
B · y)

--- 原说明 ---
`E` is a `IsTopologicalAddGroup` when `E` is equipped with a `LinearMap.IsWeak` 
topology.
-/
theorem isTopologicalAddGroup {𝕜 E F : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace E]
    [ContinuousAdd 𝕜] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsWeak] : IsTopologicalAddGroup E where
  toContinuousAdd := continuousAdd B
  continuous_neg := by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced, continuous_induced_rng, continuous_pi_iff]
    simp_rw [Function.comp_apply, map_neg, neg_apply, ← map_neg (B _)]
    fun_prop

end LinearMap.IsWeak

end Basic

