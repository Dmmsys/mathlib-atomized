/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.UniformSpace.AbsoluteValue
public import Mathlib.Topology.UniformSpace.Completion

/-!
# Comparison of Cauchy reals and Bourbaki reals

In `Data.Real.Basic` real numbers are defined using the so called Cauchy construction (although
it is due to Georg Cantor). More precisely, this construction applies to commutative rings equipped
with an absolute value with values in a linear ordered field.

On the other hand, in the `UniformSpace` folder, we construct completions of general uniform
spaces, which allows to construct the Bourbaki real numbers. In this file we build uniformly
continuous bijections from Cauchy reals to Bourbaki reals and back. This is a cross sanity check of
both constructions. Of course those two constructions are variations on the completion idea, simply
with different level of generality. Comparing with Dedekind cuts or quasi-morphisms would be of a
completely different nature.

Note that `MetricSpace/cau_seq_filter` also relates the notions of Cauchy sequences in metric
spaces and Cauchy filters in general uniform spaces, and `MetricSpace/Completion` makes sure
the completion (as a uniform space) of a metric space is a metric space.

Historical note: mathlib used to define real numbers in an intermediate way, using completion
of uniform spaces but extending multiplication in an ad-hoc way.

TODO:
* Upgrade this isomorphism to a topological ring isomorphism.
* Do the same comparison for p-adic numbers

## Implementation notes

The heavy work is done in `Topology/UniformSpace/AbstractCompletion` which provides an abstract
characterization of completions of uniform spaces, and isomorphisms between them. The only work left
here is to prove the uniform space structure coming from the absolute value on ℚ (with values in ℚ,
not referring to ℝ) coincides with the one coming from the metric space structure (which of course
does use ℝ).

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

real numbers, completion, uniform spaces
-/

@[expose] public section


open Set Function Filter CauSeq UniformSpace

/-- The metric space uniform structure on ℚ (which presupposes the existence
of real numbers) agrees with the one coming directly from (abs : ℚ → ℚ). -/
/-
**Rat.uniformSpace_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Rat.uniformSpace_eq : (AbsoluteValue.abs : AbsoluteValue Rat Rat).uniformS
pace = PseudoMetricSpace.toUniformSpace
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `AbsoluteValue.hasBasis_uniformity`：hasBasis_uniformity : 𝓤[abv.uniformSp
ace].HasBasis ((0 : 𝕜) < ·) fun ε => { p : R × R | abv (p.2 - p.1) < ε }
· 使用定理 `Metric.uniformity_basis_dist_rat`：uniformity_basis_dist_rat : (𝓤 α).HasB
asis (fun r : Rat => 0 < r) fun r => { p : α × α | dist p.1 p.2 < r }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AbsoluteValue.abs_apply`：∀ {S : Type u_6} [inst : Ring S] [inst_1 : Line
arOrder S] [inst_2 : IsStrictOrderedRing S] (a : S),   AbsoluteValue.abs a = |a|
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The metric space uniform structure on ℚ (which presupposes the existence
of real numbers) agrees with the one coming directly from (abs : ℚ → ℚ).
-/
theorem Rat.uniformSpace_eq :
    (AbsoluteValue.abs : AbsoluteValue ℚ ℚ).uniformSpace = PseudoMetricSpace.toUniformSpace := by
  ext s
  rw [(AbsoluteValue.hasBasis_uniformity _).mem_iff, Metric.uniformity_basis_dist_rat.mem_iff]
  simp only [Rat.dist_eq, AbsoluteValue.abs_apply, ← Rat.cast_sub, ← Rat.cast_abs, Rat.cast_lt,
    _root_.abs_sub_comm]

/-- Cauchy reals packaged as a completion of ℚ using the absolute value route. -/
/-
**rationalCauSeqPkg** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rationalCauSeqPkg : @AbstractCompletion Rat (@AbsoluteValue.abs Rat _).uni
formSpace
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cauchy reals packaged as a completion of ℚ using the absolute value route.
-/
def rationalCauSeqPkg : @AbstractCompletion ℚ <| (@AbsoluteValue.abs ℚ _).uniformSpace :=
  @AbstractCompletion.mk
    (space := ℝ)
    (coe := ((↑) : ℚ → ℝ))
    (uniformStruct := by infer_instance)
    (complete := by infer_instance)
    (separation := by infer_instance)
    (isUniformInducing := by
      rw [Rat.uniformSpace_eq]
      exact Rat.isUniformEmbedding_coe_real.isUniformInducing)
    (dense := Rat.isDenseEmbedding_coe_real.dense)

namespace CompareReals

/-- Type wrapper around ℚ to make sure the absolute value uniform space instance is picked up
instead of the metric space one. We proved in `Rat.uniformSpace_eq` that they are equal,
but they are not definitionaly equal, so it would confuse the type class system (and probably
also human readers). -/
/-
**CompareReals.Q** 是 Mathlib 中的一个定义，位于命名空间 `CompareReals`。
形式化陈述：Q
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type wrapper around ℚ to make sure the absolute value uniform space instance is 
picked up
instead of the metric space one. We proved in `Rat.uniformSpace_eq` that they ar
e equal,
but they are not definitionaly equal, so it would confuse the type class system 
(and probably
also human readers).
-/
def Q :=
  ℚ deriving CommRing, Inhabited
/-
**CompareReals.uniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `CompareReals`。
形式化陈述：uniformSpace : UniformSpace Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniformSpace : UniformSpace Q :=
  fast_instance% (@AbsoluteValue.abs ℚ _).uniformSpace

/-- Real numbers constructed as in Bourbaki. -/
/-
**CompareReals.Bourbaki** 是 Mathlib 中的一个定义，位于命名空间 `CompareReals`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Real numbers constructed as in Bourbaki.
-/
def Bourbakiℝ : Type :=
  Completion Q deriving Inhabited
/-
**CompareReals.Bourbaki.uniformSpace** 是 Mathlib 中的一个定义，位于命名空间 `CompareReals.Bou
rbaki`。
形式化陈述：UniformSpace CompareReals.Bourbakiℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Bourbaki.uniformSpace : UniformSpace Bourbakiℝ :=
  fast_instance% Completion.uniformSpace Q

/-- Bourbaki reals packaged as a completion of Q using the general theory. -/
/-
**CompareReals.bourbakiPkg** 是 Mathlib 中的一个定义，位于命名空间 `CompareReals`。
形式化陈述：bourbakiPkg : AbstractCompletion Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bourbaki reals packaged as a completion of Q using the general theory.
-/
def bourbakiPkg : AbstractCompletion Q :=
  Completion.cPkg

/-- The uniform bijection between Bourbaki and Cauchy reals. -/
/-
**CompareReals.compareEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CompareReals`。
形式化陈述：compareEquiv : BourbakiReal ≃ᵤ Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniform bijection between Bourbaki and Cauchy reals.
-/
noncomputable def compareEquiv : Bourbakiℝ ≃ᵤ ℝ :=
  bourbakiPkg.compareEquiv rationalCauSeqPkg
/-
**CompareReals.compare_uc** 是 Mathlib 中的一个定理，位于命名空间 `CompareReals`。
形式化陈述：compare_uc : UniformContinuous compareEquiv
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.uniformContinuous_compareEquiv`：uniformContinuous_com
pareEquiv : UniformContinuous (pkg.compareEquiv pkg')
-/
theorem compare_uc : UniformContinuous compareEquiv :=
  bourbakiPkg.uniformContinuous_compareEquiv rationalCauSeqPkg
/-
**CompareReals.compare_uc_symm** 是 Mathlib 中的一个定理，位于命名空间 `CompareReals`。
形式化陈述：compare_uc_symm : UniformContinuous compareEquiv.symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.uniformContinuous_compareEquiv_symm`：uniformContinuou
s_compareEquiv_symm : UniformContinuous (pkg.compareEquiv pkg').symm
-/
theorem compare_uc_symm : UniformContinuous compareEquiv.symm :=
  bourbakiPkg.uniformContinuous_compareEquiv_symm rationalCauSeqPkg

end CompareReals

