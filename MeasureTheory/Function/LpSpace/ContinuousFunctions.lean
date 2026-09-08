/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuous functions in Lp space

When `α` is a topological space equipped with a finite Borel measure, there is a bounded linear map
from the normed space of bounded continuous functions (`α →ᵇ E`) to `Lp E p μ`. We construct this
as `BoundedContinuousFunction.toLp`.

-/

@[expose] public section

open BoundedContinuousFunction MeasureTheory Filter
open scoped ENNReal

variable {α E : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
  [TopologicalSpace α] [BorelSpace α] [NormedAddCommGroup E] [SecondCountableTopologyEither α E]

variable (E p μ) in
/-- An additive subgroup of `Lp E p μ`, consisting of the equivalence classes which contain a
bounded continuous representative. -/
/-
**MeasureTheory.Lp.boundedContinuousFunction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MeasureTheory.Lp.boundedContinuousFunction : AddSubgroup (Lp E p μ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive subgroup of `Lp E p μ`, consisting of the equivalence classes which 
contain a
bounded continuous representative.
-/
noncomputable def MeasureTheory.Lp.boundedContinuousFunction : AddSubgroup (Lp E p μ) :=
  AddSubgroup.addSubgroupOf
    ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddMonoidHom α E)).range (Lp E p μ)

/-- By definition, the elements of `Lp.boundedContinuousFunction E p μ` are the elements of
`Lp E p μ` which contain a bounded continuous representative. -/
/-
**MeasureTheory.Lp.mem_boundedContinuousFunction_iff** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：MeasureTheory.Lp.mem_boundedContinuousFunction_iff {f : Lp E p μ} : f in M
easureTheory.Lp.boundedContinuousFunction E p μ ↔ exists f₀ : α ->ᵇ E, f₀.toCont
inuousMap.toAEEqFun μ = (f : α ->ₘ[μ] E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `AddSubgroup.mem_addSubgroupOf`：∀ {G : Type u_1} [inst : AddGroup G] {H K
 : AddSubgroup G} {h : ↥K}, h ∈ H.addSubgroupOf K ↔ ↑h ∈ H

--- 原说明 ---
By definition, the elements of `Lp.boundedContinuousFunction E p μ` are the elem
ents of
`Lp E p μ` which contain a bounded continuous representative.
-/
theorem MeasureTheory.Lp.mem_boundedContinuousFunction_iff {f : Lp E p μ} :
    f ∈ MeasureTheory.Lp.boundedContinuousFunction E p μ ↔
      ∃ f₀ : α →ᵇ E, f₀.toContinuousMap.toAEEqFun μ = (f : α →ₘ[μ] E) :=
  AddSubgroup.mem_addSubgroupOf

namespace BoundedContinuousFunction

/-- A bounded continuous function is in `L∞`. -/
/-
**BoundedContinuousFunction.memLp_top** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuo
usFunction`。
形式化陈述：memLp_top (f : α ->ᵇ E) : MemLp f ⊤ μ
参数：f : α ->ᵇ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `BoundedContinuousMapClass.toContinuousMapClass`：∀ {F : Type u_2} {α : ou
tParam (Type u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α}   {inst
_1 : PseudoMetricSpace β} {inst_2 : …
· 使用定理 `MeasureTheory.eLpNormEssSup_lt_top_of_ae_bound`：eLpNormEssSup_lt_top_of_
ae_bound {f : α -> F} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : eLpNormEssSu
p f μ < ∞
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖

--- 原说明 ---
A bounded continuous function is in `L∞`.
-/
theorem memLp_top (f : α →ᵇ E) : MemLp f ⊤ μ :=
  ⟨by fun_prop, eLpNormEssSup_lt_top_of_ae_bound <| univ_mem' (id norm_coe_le_norm f)⟩

variable [IsFiniteMeasure μ]

/-- A bounded continuous function on a finite-measure space is in `Lp`. -/
/-
**BoundedContinuousFunction.mem_Lp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuousF
unction`。
形式化陈述：mem_Lp (f : α ->ᵇ E) : f.toContinuousMap.toAEEqFun μ in Lp E p μ
参数：f : α ->ᵇ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.mem_Lp_of_ae_bound`：mem_Lp_of_ae_bound [IsFiniteMeasure
 μ] {f : α ->ₘ[μ] E} (C : Real) (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : f in Lp E p μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ContinuousMap.coeFn_toAEEqFun`：coeFn_toAEEqFun (f : C(α, β)) : f.toAEEqF
un μ =ᵐ[μ] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖

--- 原说明 ---
A bounded continuous function on a finite-measure space is in `Lp`.
-/
theorem mem_Lp (f : α →ᵇ E) : f.toContinuousMap.toAEEqFun μ ∈ Lp E p μ := by
  refine Lp.mem_Lp_of_ae_bound ‖f‖ ?_
  filter_upwards [f.toContinuousMap.coeFn_toAEEqFun μ] with x _
  convert! f.norm_coe_le_norm x using 2

/-- The `Lp`-norm of a bounded continuous function is at most a constant (depending on the measure
of the whole space) times its sup-norm. -/
/-
**BoundedContinuousFunction.Lp_nnnorm_le** 是 Mathlib 中的一个定理，位于命名空间 `BoundedConti
nuousFunction`。
形式化陈述：Lp_nnnorm_le (f : α ->ᵇ E) : ‖(⟨f.toContinuousMap.toAEEqFun μ, mem_Lp f⟩ :
 Lp E p μ)‖₊ <= measureUnivNNReal μ ^ p.toReal⁻¹ * ‖f‖₊
参数：f : α ->ᵇ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.nnnorm_le_of_ae_bound`：nnnorm_le_of_ae_bound [IsFiniteM
easure μ] {f : Lp E p μ} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C) : ‖f‖₊ 
<= measureUnivNNReal μ ^ p.t…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BoundedContinuousFunction.mem_Lp`：mem_Lp (f : α ->ᵇ E) : f.toContinuousM
ap.toAEEqFun μ in Lp E p μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ContinuousMap.coeFn_toAEEqFun`：coeFn_toAEEqFun (f : C(α, β)) : f.toAEEqF
un μ =ᵐ[μ] f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖

--- 原说明 ---
The `Lp`-norm of a bounded continuous function is at most a constant (depending 
on the measure
of the whole space) times its sup-norm.
-/
theorem Lp_nnnorm_le (f : α →ᵇ E) :
    ‖(⟨f.toContinuousMap.toAEEqFun μ, mem_Lp f⟩ : Lp E p μ)‖₊ ≤
      measureUnivNNReal μ ^ p.toReal⁻¹ * ‖f‖₊ := by
  apply Lp.nnnorm_le_of_ae_bound
  refine (f.toContinuousMap.coeFn_toAEEqFun μ).mono ?_
  intro x hx
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
  convert! f.norm_coe_le_norm x using 2

/-- The `Lp`-norm of a bounded continuous function is at most a constant (depending on the measure
of the whole space) times its sup-norm. -/
/-
**BoundedContinuousFunction.Lp_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：Lp_norm_le (f : α ->ᵇ E) : ‖(⟨f.toContinuousMap.toAEEqFun μ, mem_Lp f⟩ : L
p E p μ)‖ <= measureUnivNNReal μ ^ p.toReal⁻¹ * ‖f‖
参数：f : α ->ᵇ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.Lp_nnnorm_le`：Lp_nnnorm_le (f : α ->ᵇ E) : ‖(⟨
f.toContinuousMap.toAEEqFun μ, mem_Lp f⟩ : Lp E p μ)‖₊ <= measureUnivNNReal μ ^ 
p.toReal⁻¹ * ‖f‖₊

--- 原说明 ---
The `Lp`-norm of a bounded continuous function is at most a constant (depending 
on the measure
of the whole space) times its sup-norm.
-/
theorem Lp_norm_le (f : α →ᵇ E) :
    ‖(⟨f.toContinuousMap.toAEEqFun μ, mem_Lp f⟩ : Lp E p μ)‖ ≤
      measureUnivNNReal μ ^ p.toReal⁻¹ * ‖f‖ :=
  Lp_nnnorm_le f

variable (p μ)

/-- The normed group homomorphism of considering a bounded continuous function on a finite-measure
space as an element of `Lp`. -/
/-
**BoundedContinuousFunction.toLpHom** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinuous
Function`。
形式化陈述：toLpHom [Fact (1 <= p)] : NormedAddGroupHom (α ->ᵇ E) (Lp E p μ)
参数：1 <= p。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.mem_Lp`：mem_Lp (f : α ->ᵇ E) : f.toContinuousM
ap.toAEEqFun μ in Lp E p μ

--- 原说明 ---
The normed group homomorphism of considering a bounded continuous function on a 
finite-measure
space as an element of `Lp`.
-/
def toLpHom [Fact (1 ≤ p)] : NormedAddGroupHom (α →ᵇ E) (Lp E p μ) :=
  { AddMonoidHom.codRestrict ((ContinuousMap.toAEEqFunAddHom μ).comp
    (toContinuousMapAddMonoidHom α E)) (Lp E p μ) mem_Lp with
    bound' := ⟨_, Lp_norm_le⟩ }
/-
**BoundedContinuousFunction.range_toLpHom** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCont
inuousFunction`。
形式化陈述：range_toLpHom [Fact (1 <= p)] : ((toLpHom p μ).range : AddSubgroup (Lp E p
 μ)) = MeasureTheory.Lp.boundedContinuousFunction E p μ
参数：1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `AddMonoidHom.addSubgroupOf_range_eq_of_le`：∀ {G₁ : Type u_7} {G₂ : Type 
u_8} [inst : AddGroup G₁] [inst_1 : AddGroup G₂] {K : AddSubgroup G₂} (f : G₁ →+
 G₂)   (h : f.range ≤ K), f.ran…
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `BoundedContinuousFunction.mem_Lp`：mem_Lp (f : α ->ᵇ E) : f.toContinuousM
ap.toAEEqFun μ in Lp E p μ
-/
theorem range_toLpHom [Fact (1 ≤ p)] :
    ((toLpHom p μ).range : AddSubgroup (Lp E p μ)) =
      MeasureTheory.Lp.boundedContinuousFunction E p μ := by
  symm
  exact AddMonoidHom.addSubgroupOf_range_eq_of_le
      ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddMonoidHom α E))
      (by rintro - ⟨f, rfl⟩; exact mem_Lp f : _ ≤ Lp E p μ)

variable (𝕜 : Type*) [Fact (1 ≤ p)] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- The bounded linear map of considering a bounded continuous function on a finite-measure space
as an element of `Lp`. -/
/-
**BoundedContinuousFunction.toLp** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinuousFun
ction`。
形式化陈述：toLp : (α ->ᵇ E) ->L[𝕜] Lp E p μ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.mem_Lp`：mem_Lp (f : α ->ᵇ E) : f.toContinuousM
ap.toAEEqFun μ in Lp E p μ
· 使用定理 `BoundedContinuousFunction.Lp_norm_le`：Lp_norm_le (f : α ->ᵇ E) : ‖(⟨f.to
ContinuousMap.toAEEqFun μ, mem_Lp f⟩ : Lp E p μ)‖ <= measureUnivNNReal μ ^ p.toR
eal⁻¹ * ‖f‖

--- 原说明 ---
The bounded linear map of considering a bounded continuous function on a finite-
measure space
as an element of `Lp`.
-/
noncomputable def toLp : (α →ᵇ E) →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous
    (LinearMap.codRestrict (Lp.LpSubmodule 𝕜 E p μ)
      ((ContinuousMap.toAEEqFunLinearMap μ).comp (toContinuousMapLinearMap α E 𝕜)) mem_Lp)
    _ Lp_norm_le
/-
**BoundedContinuousFunction.coeFn_toLp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：coeFn_toLp (f : α ->ᵇ E) : toLp (E
参数：f : α ->ᵇ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
-/
theorem coeFn_toLp (f : α →ᵇ E) :
    toLp (E := E) p μ 𝕜 f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk f _

variable {𝕜}
/-
**BoundedContinuousFunction.range_toLp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：range_toLp : (toLp p μ 𝕜 : (α ->ᵇ E) ->L[𝕜] Lp E p μ).range.toAddSubgroup 
= MeasureTheory.Lp.boundedContinuousFunction E p μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.range_toLpHom`：range_toLpHom [Fact (1 <= p)] :
 ((toLpHom p μ).range : AddSubgroup (Lp E p μ)) = MeasureTheory.Lp.boundedContin
uousFunction E p μ
-/
theorem range_toLp :
    (toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ).range.toAddSubgroup =
      MeasureTheory.Lp.boundedContinuousFunction E p μ :=
  range_toLpHom p μ

variable {p}
/-
**BoundedContinuousFunction.toLp_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `BoundedConti
nuousFunction`。
形式化陈述：toLp_norm_le {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] : ‖
(toLp p μ 𝕜 : (α ->ᵇ E) ->L[𝕜] Lp E p μ)‖ <= measureUnivNNReal μ ^ p.toReal⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous_norm_le`：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F)
 {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h
‖ <= C
· 使用定理 `BoundedContinuousFunction.mem_Lp`：mem_Lp (f : α ->ᵇ E) : f.toContinuousM
ap.toAEEqFun μ in Lp E p μ
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `BoundedContinuousFunction.Lp_norm_le`：Lp_norm_le (f : α ->ᵇ E) : ‖(⟨f.to
ContinuousMap.toAEEqFun μ, mem_Lp f⟩ : Lp E p μ)‖ <= measureUnivNNReal μ ^ p.toR
eal⁻¹ * ‖f‖
-/
theorem toLp_norm_le {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] :
    ‖(toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ)‖ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (measureUnivNNReal μ ^ p.toReal⁻¹).coe_nonneg _
/-
**BoundedContinuousFunction.toLp_inj** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuou
sFunction`。
形式化陈述：toLp_inj {f g : α ->ᵇ E} [μ.IsOpenPosMeasure] : toLp (E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Continuous.ae_eq_iff_eq`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] {m : MeasurableSpace X} [inst_1 : TopologicalSpace Y]   [T2Space Y]
 (μ : Measure…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `BoundedContinuousMapClass.toContinuousMapClass`：∀ {F : Type u_2} {α : ou
tParam (Type u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α}   {inst
_1 : PseudoMetricSpace β} {inst_2 : …
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `BoundedContinuousFunction.coeFn_toLp`：coeFn_toLp (f : α ->ᵇ E) : toLp (E
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem toLp_inj {f g : α →ᵇ E} [μ.IsOpenPosMeasure] :
    toLp (E := E) p μ 𝕜 f = toLp (E := E) p μ 𝕜 g ↔ f = g := by
  refine ⟨fun h => ?_, by tauto⟩
  rw [← DFunLike.coe_fn_eq, ← (map_continuous f).ae_eq_iff_eq μ (map_continuous g)]
  refine (coeFn_toLp p μ 𝕜 f).symm.trans (EventuallyEq.trans ?_ <| coeFn_toLp p μ 𝕜 g)
  rw [h]
/-
**BoundedContinuousFunction.toLp_injective** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCon
tinuousFunction`。
形式化陈述：toLp_injective [μ.IsOpenPosMeasure] : Function.Injective (⇑(toLp p μ 𝕜 : (
α ->ᵇ E) ->L[𝕜] Lp E p μ))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoundedContinuousFunction.toLp_inj`：toLp_inj {f g : α ->ᵇ E} [μ.IsOpenPo
sMeasure] : toLp (E
-/
theorem toLp_injective [μ.IsOpenPosMeasure] :
    Function.Injective (⇑(toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ)) :=
  fun _f _g hfg => (toLp_inj μ).mp hfg

end BoundedContinuousFunction

namespace ContinuousMap

variable [CompactSpace α] [IsFiniteMeasure μ]
variable (𝕜 : Type*) (p μ) [Fact (1 ≤ p)]
  [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- The bounded linear map of considering a continuous function on a compact finite-measure
space `α` as an element of `Lp`.  By definition, the norm on `C(α, E)` is the sup-norm, transferred
from the space `α →ᵇ E` of bounded continuous functions, so this construction is just a matter of
transferring the structure from `BoundedContinuousFunction.toLp` along the isometry. -/
/-
**ContinuousMap.toLp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：toLp : C(α, E) ->L[𝕜] Lp E p μ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bounded linear map of considering a continuous function on a compact finite-
measure
space `α` as an element of `Lp`.  By definition, the norm on `C(α, E)` is the su
p-norm, transferred
from the space `α →ᵇ E` of bounded continuous functions, so this construction is
 just a matter of
transferring the structure from `BoundedContinuousFunction.toLp` along the isome
try.
-/
noncomputable def toLp : C(α, E) →L[𝕜] Lp E p μ :=
  (BoundedContinuousFunction.toLp p μ 𝕜).comp
    (linearIsometryBoundedOfCompact α E 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

variable {𝕜}
/-
**ContinuousMap.range_toLp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：range_toLp : (toLp p μ 𝕜 : C(α, E) ->L[𝕜] Lp E p μ).range.toAddSubgroup = 
MeasureTheory.Lp.boundedContinuousFunction E p μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `LinearIsometryEquiv.surjective`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.range_toLp`：range_toLp : (toLp p μ 𝕜 : (α ->ᵇ 
E) ->L[𝕜] Lp E p μ).range.toAddSubgroup = MeasureTheory.Lp.boundedContinuousFunc
tion E p μ
· 使用定理 `Submodule.coe_toAddSubgroup`：coe_toAddSubgroup : (p.toAddSubgroup : Set 
M) = p
· 使用定理 `LinearMap.coe_range`：coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] 
M₂) : (range f : Set M₂) = Set.range f
· 使用定理 `ContinuousLinearMap.coe_coe`：coe_coe (f : M₁ ->SL[σ₁₂] M₂) : ⇑(f : M₁ ->
ₛₗ[σ₁₂] M₂) = f
· 使用定理 `Function.Surjective.range_comp`：∀ {α : Type u_1} {ι : Sort u_3} {ι' : So
rt u_4} {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α), Set.range (g ∘ f
) = Set.range g
-/
theorem range_toLp :
    (toLp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ).range.toAddSubgroup =
      MeasureTheory.Lp.boundedContinuousFunction E p μ := by
  refine SetLike.ext' ?_
  have := (linearIsometryBoundedOfCompact α E 𝕜).surjective
  convert! Function.Surjective.range_comp this (BoundedContinuousFunction.toLp (E := E) p μ 𝕜)
  rw [← BoundedContinuousFunction.range_toLp p μ (𝕜 := 𝕜), Submodule.coe_toAddSubgroup,
    LinearMap.coe_range, ContinuousLinearMap.coe_coe]

variable {p}
/-
**ContinuousMap.coeFn_toLp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coeFn_toLp (f : C(α, E)) : toLp (E
参数：f : C(α, E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
-/
theorem coeFn_toLp (f : C(α, E)) :
    toLp (E := E) p μ 𝕜 f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk f _
/-
**ContinuousMap.toLp_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：toLp_def (f : C(α, E)) : toLp (E
参数：f : C(α, E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem toLp_def (f : C(α, E)) :
    toLp (E := E) p μ 𝕜 f =
      BoundedContinuousFunction.toLp (E := E) p μ 𝕜 (linearIsometryBoundedOfCompact α E 𝕜 f) :=
  rfl

@[simp]
/-
**ContinuousMap.toLp_comp_toContinuousMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ap`。
形式化陈述：toLp_comp_toContinuousMap (f : α ->ᵇ E) : toLp (E
参数：f : α ->ᵇ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem toLp_comp_toContinuousMap (f : α →ᵇ E) :
    toLp (E := E) p μ 𝕜 f.toContinuousMap = BoundedContinuousFunction.toLp (E := E) p μ 𝕜 f :=
  rfl

@[simp]
/-
**ContinuousMap.coe_toLp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_toLp (f : C(α, E)) : (toLp (E
参数：f : C(α, E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem coe_toLp (f : C(α, E)) :
    (toLp (E := E) p μ 𝕜 f : α →ₘ[μ] E) = f.toAEEqFun μ :=
  rfl
/-
**ContinuousMap.toLp_injective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：toLp_injective [μ.IsOpenPosMeasure] : Function.Injective (⇑(toLp p μ 𝕜 : C
(α, E) ->L[𝕜] Lp E p μ))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `BoundedContinuousFunction.toLp_injective`：toLp_injective [μ.IsOpenPosMea
sure] : Function.Injective (⇑(toLp p μ 𝕜 : (α ->ᵇ E) ->L[𝕜] Lp E p μ))
· 使用定理 `LinearIsometryEquiv.injective`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Typ
e u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+*
 R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem toLp_injective [μ.IsOpenPosMeasure] :
    Function.Injective (⇑(toLp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ)) :=
  (BoundedContinuousFunction.toLp_injective _).comp (linearIsometryBoundedOfCompact α E 𝕜).injective
/-
**ContinuousMap.toLp_inj** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：toLp_inj {f g : C(α, E)} [μ.IsOpenPosMeasure] : toLp (E
参数：α, E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMap.toLp_injective`：toLp_injective [μ.IsOpenPosMeasure] : Func
tion.Injective (⇑(toLp p μ 𝕜 : C(α, E) ->L[𝕜] Lp E p μ))
-/
theorem toLp_inj {f g : C(α, E)} [μ.IsOpenPosMeasure] :
    toLp (E := E) p μ 𝕜 f = toLp (E := E) p μ 𝕜 g ↔ f = g :=
  (toLp_injective μ).eq_iff

variable {μ}

/-- If a sum of continuous functions `g n` is convergent, and the same sum converges in `Lᵖ` to `h`,
then in fact `g n` converges uniformly to `h`. -/
/-
**ContinuousMap.hasSum_of_hasSum_Lp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：hasSum_of_hasSum_Lp {β : Type*} [μ.IsOpenPosMeasure] {g : β -> C(α, E)} {f
 : C(α, E)} (hg : Summable g) (hg2 : HasSum (toLp (E
参数：α, E；α, E；hg : Summable g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.toLp_injective`：toLp_injective [μ.IsOpenPosMeasure] : Func
tion.Injective (⇑(toLp p μ 𝕜 : C(α, E) ->L[𝕜] Lp E p μ))
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ContinuousLinearMap.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u
_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂]
 [inst_2 : AddCo…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…

--- 原说明 ---
If a sum of continuous functions `g n` is convergent, and the same sum converges
 in `Lᵖ` to `h`,
then in fact `g n` converges uniformly to `h`.
-/
theorem hasSum_of_hasSum_Lp {β : Type*} [μ.IsOpenPosMeasure]
    {g : β → C(α, E)} {f : C(α, E)} (hg : Summable g)
    (hg2 : HasSum (toLp (E := E) p μ 𝕜 ∘ g) (toLp (E := E) p μ 𝕜 f)) : HasSum g f := by
  convert! Summable.hasSum hg
  exact toLp_injective μ (hg2.unique ((toLp p μ 𝕜).hasSum <| Summable.hasSum hg))

variable (μ) {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
/-
**ContinuousMap.toLp_norm_eq_toLp_norm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
Map`。
形式化陈述：toLp_norm_eq_toLp_norm_coe : ‖(toLp p μ 𝕜 : C(α, E) ->L[𝕜] Lp E p μ)‖ = ‖(
BoundedContinuousFunction.toLp p μ 𝕜 : (α ->ᵇ E) ->L[𝕜] Lp E p μ)‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.opNorm_comp_linearIsometryEquiv`：opNorm_comp_linearI
sometryEquiv [RingHomIsometric σ₂₃] (f : F ->SL[σ₂₃] G) (e : E ≃ₛₗᵢ[σ₁₂] F) : ‖f
.comp (e : E ->SL[σ₁₂] F)‖ = ‖f‖
-/
theorem toLp_norm_eq_toLp_norm_coe :
    ‖(toLp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ)‖ =
      ‖(BoundedContinuousFunction.toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ)‖ :=
  ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _

/-- Bound for the operator norm of `ContinuousMap.toLp`. -/
/-
**ContinuousMap.toLp_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：toLp_norm_le : ‖(toLp p μ 𝕜 : C(α, E) ->L[𝕜] Lp E p μ)‖ <= measureUnivNNRe
al μ ^ p.toReal⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.toLp_norm_eq_toLp_norm_coe`：toLp_norm_eq_toLp_norm_coe : ‖
(toLp p μ 𝕜 : C(α, E) ->L[𝕜] Lp E p μ)‖ = ‖(BoundedContinuousFunction.toLp p μ 𝕜
 : (α ->ᵇ E) ->L[𝕜] Lp E p μ)‖
· 使用定理 `BoundedContinuousFunction.toLp_norm_le`：toLp_norm_le {𝕜 : Type*} [Nontri
viallyNormedField 𝕜] [NormedSpace 𝕜 E] : ‖(toLp p μ 𝕜 : (α ->ᵇ E) ->L[𝕜] Lp E p 
μ)‖ <= measureUnivNNReal μ ^…

--- 原说明 ---
Bound for the operator norm of `ContinuousMap.toLp`.
-/
theorem toLp_norm_le :
    ‖(toLp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ)‖ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ := by
  rw [toLp_norm_eq_toLp_norm_coe]
  exact BoundedContinuousFunction.toLp_norm_le μ
/-
**ContinuousMap.memLp** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：memLp (𝕜' : Type*) [NormedField 𝕜'] [NormedSpace 𝕜' E] (f : C(α, E)) : Mem
Lp f p μ
参数：𝕜' : Type*；f : C(α, E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Lp.mem_Lp_iff_memLp`：mem_Lp_iff_memLp {f : α ->ₘ[μ] E} : f
 in Lp E p μ ↔ MemLp f p μ
· 使用定理 `Subtype.val_prop`：val_prop {S : Set α} (a : { a // a in S }) : a.val in 
S
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.memLp_congr_ae`：memLp_congr_ae [TopologicalSpace ε] {f g :
 α -> ε} (hfg : f =ᵐ[μ] g) : MemLp f p μ ↔ MemLp g p μ
· 使用定理 `ContinuousMap.coeFn_toAEEqFun`：coeFn_toAEEqFun (f : C(α, β)) : f.toAEEqF
un μ =ᵐ[μ] f
· 使用定理 `ContinuousMap.coe_toLp`：coe_toLp (f : C(α, E)) : (toLp (E
-/
lemma memLp (𝕜' : Type*) [NormedField 𝕜'] [NormedSpace 𝕜' E] (f : C(α, E)) :
    MemLp f p μ := by
  have := Lp.mem_Lp_iff_memLp.mp (Subtype.val_prop (f.toLp p μ 𝕜'))
  rwa [coe_toLp, memLp_congr_ae (coeFn_toAEEqFun _ _)] at this

end ContinuousMap

