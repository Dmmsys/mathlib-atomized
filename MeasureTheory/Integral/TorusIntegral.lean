/-
Copyright (c) 2022 Cuma Kökmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cuma Kökmen, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integral over a torus in `ℂⁿ`

In this file we define the integral of a function `f : ℂⁿ → E` over a torus
`{z : ℂⁿ | ∀ i, z i ∈ Metric.sphere (c i) (R i)}`. In order to do this, we define
`torusMap (c : ℂⁿ) (R θ : ℝⁿ)` to be the point in `ℂⁿ` given by $z_k=c_k+R_ke^{θ_ki}$,
where $i$ is the imaginary unit, then define `torusIntegral f c R` as the integral over
the cube $[0, (fun _ ↦ 2π)] = \{θ\|∀ k, 0 ≤ θ_k ≤ 2π\}$ of the Jacobian of the
`torusMap` multiplied by `f (torusMap c R θ)`.

We also define a predicate saying that `f ∘ torusMap c R` is integrable on the cube
`[0, (fun _ ↦ 2π)]`.

## Main definitions

* `torusMap c R`: the generalized multidimensional exponential map from `ℝⁿ` to `ℂⁿ` that sends
  $θ=(θ_0,…,θ_{n-1})$ to $z=(z_0,…,z_{n-1})$, where $z_k= c_k + R_ke^{θ_k i}$;

* `TorusIntegrable f c R`: a function `f : ℂⁿ → E` is integrable over the generalized torus
  with center `c : ℂⁿ` and radius `R : ℝⁿ` if `f ∘ torusMap c R` is integrable on the
  closed cube `Icc (0 : ℝⁿ) (fun _ ↦ 2 * π)`;

* `torusIntegral f c R`: the integral of a function `f : ℂⁿ → E` over a torus with
  center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ` defined as
  $\iiint_{[0, 2 * π]} (∏_{k = 1}^{n} i R_k e^{θ_k * i}) • f (c + Re^{θ_k i})\,dθ_0…dθ_{k-1}$.

## Main statements

* `torusIntegral_dim0`, `torusIntegral_dim1`, `torusIntegral_succ`: formulas for `torusIntegral`
  in cases of dimension `0`, `1`, and `n + 1`.

## Notation

- `ℝ⁰`, `ℝ¹`, `ℝⁿ`, `ℝⁿ⁺¹`: local notation for `Fin 0 → ℝ`, `Fin 1 → ℝ`, `Fin n → ℝ`, and
  `Fin (n + 1) → ℝ`, respectively;
- `ℂ⁰`, `ℂ¹`, `ℂⁿ`, `ℂⁿ⁺¹`: local notation for `Fin 0 → ℂ`, `Fin 1 → ℂ`, `Fin n → ℂ`, and
  `Fin (n + 1) → ℂ`, respectively;
- `∯ z in T(c, R), f z`: notation for `torusIntegral f c R`;
- `∮ z in C(c, R), f z`: notation for `circleIntegral f c R`, defined elsewhere;
- `∏ k, f k`: notation for `Finset.prod`, defined elsewhere;
- `π`: notation for `Real.pi`, defined elsewhere.

## Tags

integral, torus
-/

@[expose] public section


variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E]

noncomputable section

open Complex Set MeasureTheory Function Filter TopologicalSpace
open Mathlib.Tactic (superscriptTerm)

open scoped Real

local syntax:arg term:max noWs superscriptTerm : term
local macro_rules | `($t:term$n:superscript) => `(Fin $n → $t)

/-!
### `torusMap`, a parametrization of a torus
-/

/-- The n-dimensional exponential map $θ_i ↦ c + R e^{θ_i*I}, θ ∈ ℝⁿ$ representing
a torus in `ℂⁿ` with center `c ∈ ℂⁿ` and generalized radius `R ∈ ℝⁿ`, so we can adjust
it to every n axis. -/
/-
**torusMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：torusMap (c : Complexⁿ) (R : Realⁿ) : Realⁿ -> Complexⁿ
参数：c : Complexⁿ；R : Realⁿ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The n-dimensional exponential map $θ_i ↦ c + R e^{θ_i*I}, θ ∈ ℝⁿ$ representing
a torus in `ℂⁿ` with center `c ∈ ℂⁿ` and generalized radius `R ∈ ℝⁿ`, so we can 
adjust
it to every n axis.
-/
def torusMap (c : ℂⁿ) (R : ℝⁿ) : ℝⁿ → ℂⁿ := fun θ i => c i + R i * exp (θ i * I)
/-
**torusMap_sub_center** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：torusMap_sub_center (c : Complexⁿ) (R : Realⁿ) (θ : Realⁿ) : torusMap c R 
θ - c = torusMap 0 R θ
参数：c : Complexⁿ；R : Realⁿ；θ : Realⁿ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem torusMap_sub_center (c : ℂⁿ) (R : ℝⁿ) (θ : ℝⁿ) : torusMap c R θ - c = torusMap 0 R θ := by
  ext1 i; simp [torusMap]
/-
**torusMap_eq_center_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：torusMap_eq_center_iff {c : Complexⁿ} {R : Realⁿ} {θ : Realⁿ} : torusMap c
 R θ = c ↔ R = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem torusMap_eq_center_iff {c : ℂⁿ} {R : ℝⁿ} {θ : ℝⁿ} : torusMap c R θ = c ↔ R = 0 := by
  simp [funext_iff, torusMap, exp_ne_zero]

@[simp]
/-
**torusMap_zero_radius** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：torusMap_zero_radius (c : Complexⁿ) : torusMap c 0 = const Realⁿ c
参数：c : Complexⁿ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `torusMap_eq_center_iff`：torusMap_eq_center_iff {c : Complexⁿ} {R : Realⁿ
} {θ : Realⁿ} : torusMap c R θ = c ↔ R = 0
-/
theorem torusMap_zero_radius (c : ℂⁿ) : torusMap c 0 = const ℝⁿ c :=
  funext fun _ ↦ torusMap_eq_center_iff.2 rfl

/-!
### Integrability of a function on a generalized torus
-/

/-- A function `f : ℂⁿ → E` is integrable on the generalized torus if the function
`f ∘ torusMap c R θ` is integrable on `Icc (0 : ℝⁿ) (fun _ ↦ 2 * π)`. -/
/-
**TorusIntegrable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TorusIntegrable (f : Complexⁿ -> E) (c : Complexⁿ) (R : Realⁿ) : Prop
参数：f : Complexⁿ -> E；c : Complexⁿ；R : Realⁿ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : ℂⁿ → E` is integrable on the generalized torus if the function
`f ∘ torusMap c R θ` is integrable on `Icc (0 : ℝⁿ) (fun _ ↦ 2 * π)`.
-/
def TorusIntegrable (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) : Prop :=
  IntegrableOn (fun θ : ℝⁿ => f (torusMap c R θ)) (Icc (0 : ℝⁿ) fun _ => 2 * π) volume

namespace TorusIntegrable

variable {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ}

/-- Constant functions are torus integrable -/
/-
**TorusIntegrable.torusIntegrable_const** 是 Mathlib 中的一个定理，位于命名空间 `TorusIntegrab
le`。
形式化陈述：torusIntegrable_const (a : E) (c : Complexⁿ) (R : Realⁿ) : TorusIntegrable
 (fun _ => a) c R
参数：a : E；c : Complexⁿ；R : Realⁿ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `MeasureTheory.Measure.instIsLocallyFiniteMeasureForallVolumeOfSigmaFinit
e`：∀ {ι : Type u_1} [inst : Fintype ι] {X : ι → Type u_4} [inst_1 : (i : ι) → To
pologicalSpace (X i)]   [inst_2 : (i : ι) → MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True

--- 原说明 ---
Constant functions are torus integrable
-/
theorem torusIntegrable_const (a : E) (c : ℂⁿ) (R : ℝⁿ) : TorusIntegrable (fun _ => a) c R := by
  simp [TorusIntegrable, measure_Icc_lt_top]

/-- If `f` is torus integrable then `-f` is torus integrable. -/
protected nonrec theorem neg (hf : TorusIntegrable f c R) : TorusIntegrable (-f) c R := hf.neg

/-- If `f` and `g` are two torus integrable functions, then so is `f + g`. -/
protected nonrec theorem add (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    TorusIntegrable (f + g) c R :=
  hf.add hg

/-- If `f` and `g` are two torus integrable functions, then so is `f - g`. -/
protected nonrec theorem sub (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    TorusIntegrable (f - g) c R :=
  hf.sub hg

/-
**TorusIntegrable.torusIntegrable_zero_radius** 是 Mathlib 中的一个定理，位于命名空间 `TorusIn
tegrable`。
形式化陈述：torusIntegrable_zero_radius {f : Complexⁿ -> E} {c : Complexⁿ} : TorusInte
grable f c 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TorusIntegrable.eq_1`：∀ {n : ℕ} {E : Type u_1} [inst : NormedAddCommGrou
p E] (f : (Fin n → ℂ) → E) (c : Fin n → ℂ) (R : Fin n → ℝ),   TorusIntegrable f 
c R =     …
· 使用定理 `torusMap_zero_radius`：torusMap_zero_radius (c : Complexⁿ) : torusMap c 0
 = const Realⁿ c
· 使用定理 `TorusIntegrable.torusIntegrable_const`：torusIntegrable_const (a : E) (c 
: Complexⁿ) (R : Realⁿ) : TorusIntegrable (fun _ => a) c R
-/
theorem torusIntegrable_zero_radius {f : ℂⁿ → E} {c : ℂⁿ} : TorusIntegrable f c 0 := by
  rw [TorusIntegrable, torusMap_zero_radius]
  apply torusIntegrable_const (f c) c 0

/-- The function given in the definition of `torusIntegral` is integrable. -/
/-
**TorusIntegrable.function_integrable** 是 Mathlib 中的一个定理，位于命名空间 `TorusIntegrable
`。
形式化陈述：function_integrable [NormedSpace Complex E] (hf : TorusIntegrable f c R) :
 IntegrableOn (fun θ : Realⁿ => (∏ i, R i * exp (θ i * I) * I : Complex) • f (to
rusMap c R θ)) (Icc (0 : Realⁿ) fun _ => 2 * π) volume
参数：hf : TorusIntegrable f c R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.smul`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measu
re α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `continuous_finsetProd`：continuous_finsetProd {f : ι -> X -> M} (s : Fins
et ι) : (forall i in s, Continuous (f i)) -> Continuous fun a => ∏ i in s, f i a
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Continuous.mul_const`：Continuous.mul_const (hf : Continuous f) (b : M) :
 Continuous (f · * b)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The function given in the definition of `torusIntegral` is integrable.
-/
theorem function_integrable [NormedSpace ℂ E] (hf : TorusIntegrable f c R) :
    IntegrableOn (fun θ : ℝⁿ => (∏ i, R i * exp (θ i * I) * I : ℂ) • f (torusMap c R θ))
      (Icc (0 : ℝⁿ) fun _ => 2 * π) volume := by
  refine (hf.norm.const_mul (∏ i, |R i|)).mono' ?_ ?_
  · refine (Continuous.aestronglyMeasurable ?_).smul hf.1; fun_prop
  simp [norm_smul]

end TorusIntegrable

variable [NormedSpace ℂ E] {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ}

/-- The integral over a generalized torus with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ`, defined
as the `•`-product of the derivative of `torusMap` and `f (torusMap c R θ)` -/
/-
**torusIntegral** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：torusIntegral (f : Complexⁿ -> E) (c : Complexⁿ) (R : Realⁿ)
参数：f : Complexⁿ -> E；c : Complexⁿ；R : Realⁿ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The integral over a generalized torus with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ`, 
defined
as the `•`-product of the derivative of `torusMap` and `f (torusMap c R θ)`
-/
def torusIntegral (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) :=
  ∫ θ : ℝⁿ in Icc (0 : ℝⁿ) fun _ => 2 * π, (∏ i, R i * exp (θ i * I) * I : ℂ) • f (torusMap c R θ)

@[inherit_doc torusIntegral]
notation3 "∯ " (...) " in " "T(" c ", " R ")" ", " r:(scoped f => torusIntegral f c R) => r
/-
**torusIntegral_radius_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：torusIntegral_radius_zero (hn : n != 0) (f : Complexⁿ -> E) (c : Complexⁿ)
 : (∯ x in T(c, 0), f x) = 0
参数：hn : n != 0；f : Complexⁿ -> E；c : Complexⁿ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Fin.prod_const`：prod_const (n : Nat) (x : M) : ∏ _i : Fin n, x = x ^ n
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem torusIntegral_radius_zero (hn : n ≠ 0) (f : ℂⁿ → E) (c : ℂⁿ) :
    (∯ x in T(c, 0), f x) = 0 := by
  simp only [torusIntegral, Pi.zero_apply, ofReal_zero, zero_mul, Fin.prod_const,
    zero_pow hn, zero_smul, integral_zero]
/-
**torusIntegral_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：torusIntegral_neg (f : Complexⁿ -> E) (c : Complexⁿ) (R : Realⁿ) : (∯ x in
 T(c, R), -f x) = -∯ x in T(c, R), f x
参数：f : Complexⁿ -> E；c : Complexⁿ；R : Realⁿ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem torusIntegral_neg (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) :
    (∯ x in T(c, R), -f x) = -∯ x in T(c, R), f x := by simp [torusIntegral, integral_neg]
/-
**torusIntegral_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：torusIntegral_add (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R
) : (∯ x in T(c, R), f x + g x) = (∯ x in T(c, R), f x) + ∯ x in T(c, R), g x
参数：hf : TorusIntegrable f c R；hg : TorusIntegrable g c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `TorusIntegrable.function_integrable`：function_integrable [NormedSpace Co
mplex E] (hf : TorusIntegrable f c R) : IntegrableOn (fun θ : Realⁿ => (∏ i, R i
 * exp (θ i * I) * I : Co…
-/
theorem torusIntegral_add (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    (∯ x in T(c, R), f x + g x) = (∯ x in T(c, R), f x) + ∯ x in T(c, R), g x := by
  simpa only [torusIntegral, smul_add, Pi.add_apply] using
    integral_add hf.function_integrable hg.function_integrable
/-
**torusIntegral_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：torusIntegral_sub (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R
) : (∯ x in T(c, R), f x - g x) = (∯ x in T(c, R), f x) - ∯ x in T(c, R), g x
参数：hf : TorusIntegrable f c R；hg : TorusIntegrable g c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `torusIntegral_add`：torusIntegral_add (hf : TorusIntegrable f c R) (hg : 
TorusIntegrable g c R) : (∯ x in T(c, R), f x + g x) = (∯ x in T(c, R), f x) + ∯
 x in T…
· 使用定理 `TorusIntegrable.neg`：∀ {n : ℕ} {E : Type u_1} [inst : NormedAddCommGroup
 E] {f : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : Fin n → ℝ},   TorusIntegrable f c
 R → Toru…
-/
theorem torusIntegral_sub (hf : TorusIntegrable f c R) (hg : TorusIntegrable g c R) :
    (∯ x in T(c, R), f x - g x) = (∯ x in T(c, R), f x) - ∯ x in T(c, R), g x := by
  simpa only [sub_eq_add_neg, ← torusIntegral_neg] using! torusIntegral_add hf hg.neg
/-
**torusIntegral_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：torusIntegral_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass
 𝕜 Complex E] (a : 𝕜) (f : Complexⁿ -> E) (c : Complexⁿ) (R : Realⁿ) : (∯ x in T
(c, R), a • f x) = a • ∯ x in T(c, R), f x
参数：a : 𝕜；f : Complexⁿ -> E；c : Complexⁿ；R : Realⁿ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `MeasureTheory.integral_smul`：integral_smul [Module 𝕜 G] [NormSMulClass 𝕜
 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G) : ∫ a, c • f a ∂μ = c • ∫ a, f
 a ∂μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem torusIntegral_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass 𝕜 ℂ E] (a : 𝕜)
    (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) : (∯ x in T(c, R), a • f x) = a • ∯ x in T(c, R), f x := by
  simp only [torusIntegral, integral_smul, ← smul_comm a (_ : ℂ) (_ : E)]
/-
**torusIntegral_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：torusIntegral_const_mul (a : Complex) (f : Complexⁿ -> Complex) (c : Compl
exⁿ) (R : Realⁿ) : (∯ x in T(c, R), a * f x) = a * ∯ x in T(c, R), f x
参数：a : Complex；f : Complexⁿ -> Complex；c : Complexⁿ；R : Realⁿ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `torusIntegral_smul`：torusIntegral_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpa
ce 𝕜 E] [SMulCommClass 𝕜 Complex E] (a : 𝕜) (f : Complexⁿ -> E) (c : Complexⁿ) (
R : Real…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem torusIntegral_const_mul (a : ℂ) (f : ℂⁿ → ℂ) (c : ℂⁿ) (R : ℝⁿ) :
    (∯ x in T(c, R), a * f x) = a * ∯ x in T(c, R), f x :=
  torusIntegral_smul a f c R

/-- If for all `θ : ℝⁿ`, `‖f (torusMap c R θ)‖` is less than or equal to a constant `C : ℝ`, then
`‖∯ x in T(c, R), f x‖` is less than or equal to `(2 * π)^n * (∏ i, |R i|) * C` -/
/-
**norm_torusIntegral_le_of_norm_le_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_torusIntegral_le_of_norm_le_const {C : Real} (hf : forall θ, ‖f (toru
sMap c R θ)‖ <= C) : ‖∯ x in T(c, R), f x‖ <= ((2 * π) ^ (n : Nat) * ∏ i, |R i|)
 * C
参数：hf : forall θ, ‖f (torusMap c R θ)‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.norm_setIntegral_le_of_norm_le_const`：norm_setIntegral_le_
of_norm_le_const {C : Real} (hs : μ s < ∞) (hC : forall x in s, ‖f x‖ <= C) : ‖∫
 x in s, f x ∂μ‖ <= C * μ.real s
· 使用定理 `measure_Icc_lt_top`：measure_Icc_lt_top : μ (Icc a b) < ∞
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `MeasureTheory.Measure.instIsLocallyFiniteMeasureForallVolumeOfSigmaFinit
e`：∀ {ι : Type u_1} [inst : Fintype ι] {X : ι → Type u_4} [inst_1 : (i : ι) → To
pologicalSpace (X i)]   [inst_2 : (i : ι) → MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_prod`：norm_prod (s : Finset β) (f : β -> α) : ‖∏ b in s, f b‖ = ∏ b
 in s, ‖f b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Complex.norm_exp_ofReal_mul_I`：norm_exp_ofReal_mul_I (x : Real) : ‖exp (
x * I)‖ = 1
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
If for all `θ : ℝⁿ`, `‖f (torusMap c R θ)‖` is less than or equal to a constant 
`C : ℝ`, then
`‖∯ x in T(c, R), f x‖` is less than or equal to `(2 * π)^n * (∏ i, |R i|) * C`
-/
theorem norm_torusIntegral_le_of_norm_le_const {C : ℝ} (hf : ∀ θ, ‖f (torusMap c R θ)‖ ≤ C) :
    ‖∯ x in T(c, R), f x‖ ≤ ((2 * π) ^ (n : ℕ) * ∏ i, |R i|) * C :=
  calc
    ‖∯ x in T(c, R), f x‖ ≤ (∏ i, |R i|) * C * (volume (Icc (0 : ℝⁿ) fun _ => 2 * π)).toReal :=
      norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top fun θ _ =>
        calc
          ‖(∏ i : Fin n, R i * exp (θ i * I) * I : ℂ) • f (torusMap c R θ)‖ =
              (∏ i : Fin n, |R i|) * ‖f (torusMap c R θ)‖ := by simp [norm_smul]
          _ ≤ (∏ i : Fin n, |R i|) * C := mul_le_mul_of_nonneg_left (hf _) <| by positivity
    _ = ((2 * π) ^ (n : ℕ) * ∏ i, |R i|) * C := by
      simp only [Pi.zero_def, Real.volume_Icc_pi_toReal fun _ => Real.two_pi_pos.le, sub_zero,
        Fin.prod_const, mul_assoc, mul_comm ((2 * π) ^ (n : ℕ))]

@[simp]
/-
**torusIntegral_dim0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：torusIntegral_dim0 [CompleteSpace E] (f : Complex⁰ -> E) (c : Complex⁰) (R
 : Real⁰) : (∯ x in T(c, R), f x) = f c
参数：f : Complex⁰ -> E；c : Complex⁰；R : Real⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.pi_of_empty`：pi_of_empty {α : Type*} [Fintype α] [
IsEmpty α] {β : α -> Type*} {m : forall a, MeasurableSpace (β a)} (μ : forall a 
: α, Measure (β a)) (x …
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `MeasureTheory.Measure.restrict_singleton`：restrict_singleton (μ : Measur
e α) (a : α) : μ.restrict {a} = μ {a} • dirac a
· 使用定理 `MeasureTheory.Measure.dirac_apply_of_mem`：dirac_apply_of_mem {a : α} (h 
: a in s) : dirac a s = 1
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
（共 31 条，此处仅展示前 30 条）
-/
theorem torusIntegral_dim0 [CompleteSpace E]
    (f : ℂ⁰ → E) (c : ℂ⁰) (R : ℝ⁰) : (∯ x in T(c, R), f x) = f c := by
  simp only [torusIntegral, Fin.prod_univ_zero, one_smul,
    Subsingleton.elim (fun _ : Fin 0 => 2 * π) 0, Icc_self, Measure.restrict_singleton, volume_pi,
    integral_dirac, Measure.pi_of_empty (fun _ : Fin 0 ↦ volume) 0,
    Measure.dirac_apply_of_mem (mem_singleton _), Subsingleton.elim (torusMap c R 0) c]

set_option backward.isDefEq.respectTransparency false in
/-- In dimension one, `torusIntegral` is the same as `circleIntegral`
(up to the natural equivalence between `ℂ` and `Fin 1 → ℂ`). -/
/-
**torusIntegral_dim1** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：torusIntegral_dim1 (f : Complex¹ -> E) (c : Complex¹) (R : Real¹) : (∯ x i
n T(c, R), f x) = ∮ z in C(c 0, R 0), f fun _ => z
参数：f : Complex¹ -> E；c : Complex¹；R : Real¹。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `OrderIso.preimage_Icc`：preimage_Icc (e : α ≃o β) (a b : β) : e ⁻¹' Icc a
 b = Icc (e.symm a) (e.symm b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `torusIntegral.eq_1`：∀ {n : ℕ} {E : Type u_1} [inst : NormedAddCommGroup 
E] [inst_1 : NormedSpace ℂ E] (f : (Fin n → ℂ) → E) (c : Fin n → ℂ)   (R : Fin n
 → ℝ),  …
· 使用定理 `circleIntegral.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [ins
t_1 : NormedSpace ℂ E] (f : ℂ → E) (c : ℂ) (R : ℝ),   circleIntegral f c R = ∫ (
θ : ℝ) in…
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioc_ae_eq_Icc`：Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.setIntegral_preimage_emb`：∀ {X : Type u_
1} {E : Type u_3} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E] [inst_1
 : NormedSpace ℝ E]   {μ : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `MeasureTheory.volume_preserving_funUnique`：volume_preserving_funUnique (
α : Type u) (β : Type v) [Unique α] [MeasureSpace β] : MeasurePreserving (Measur
ableEquiv.funUnique α β) volume…
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableEquiv.funUnique_symm_apply`：∀ (α : Type u_8) (β : Type u_9) [i
nst : Unique α] [inst_1 : MeasurableSpace β],   ⇑(MeasurableEquiv.funUnique α β)
.symm = uniqueElim
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `deriv_circleMap`：deriv_circleMap (c : Complex) (R : Real) (θ : Real) : d
eriv (circleMap c R) θ = circleMap 0 R θ * I
· 使用定理 `circleMap_zero`：circleMap_zero (R θ : Real) : circleMap 0 R θ = R * exp 
(θ * I)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In dimension one, `torusIntegral` is the same as `circleIntegral`
(up to the natural equivalence between `ℂ` and `Fin 1 → ℂ`).
-/
theorem torusIntegral_dim1 (f : ℂ¹ → E) (c : ℂ¹) (R : ℝ¹) :
    (∯ x in T(c, R), f x) = ∮ z in C(c 0, R 0), f fun _ => z := by
  have H₁ : (((MeasurableEquiv.funUnique _ _).symm) ⁻¹' Icc 0 fun _ => 2 * π) = Icc 0 (2 * π) :=
    (OrderIso.funUnique (Fin 1) ℝ).symm.preimage_Icc _ _
  have H₂ : torusMap c R = fun θ _ ↦ circleMap (c 0) (R 0) (θ 0) := by
    ext θ i : 2
    rw [Subsingleton.elim i 0]; rfl
  rw [torusIntegral, circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    Measure.restrict_congr_set Ioc_ae_eq_Icc,
    ← ((volume_preserving_funUnique (Fin 1) ℝ).symm _).setIntegral_preimage_emb
      (MeasurableEquiv.measurableEmbedding _), H₁, H₂]
  simp [circleMap_zero]

set_option backward.isDefEq.respectTransparency.types false in
/-- Recurrent formula for `torusIntegral`, see also `torusIntegral_succ`. -/
/-
**torusIntegral_succAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：torusIntegral_succAbove {f : Complexⁿ⁺¹ -> E} {c : Complexⁿ⁺¹} {R : Realⁿ⁺
¹} (hf : TorusIntegrable f c R) (i : Fin (n + 1)) : (∯ x in T(c, R), f x) = ∮ x 
in C(c i, R i), ∯ y in T(c ∘ i.succAbove, R ∘ i.succAbove), f (i.insertNth x y)
参数：hf : TorusIntegrable f c R；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `MeasureTheory.volume_preserving_piFinSuccAbove`：volume_preserving_piFinS
uccAbove {n : Nat} (α : Fin (n + 1) -> Type u) [forall i, MeasureSpace (α i)] [f
orall i, SigmaFinite (volume : Measu…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrderIso.preimage_Icc`：preimage_Icc (e : α ≃o β) (a b : β) : e ⁻¹' Icc a
 b = Icc (e.symm a) (e.symm b)
· 使用定理 `Set.Icc_prod_eq`：Icc_prod_eq (a b : α × β) : Icc a b = Icc a.1 b.1 ×ˢ Ic
c a.2 b.2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `torusIntegral.eq_1`：∀ {n : ℕ} {E : Type u_1} [inst : NormedAddCommGroup 
E] [inst_1 : NormedSpace ℂ E] (f : (Fin n → ℂ) → E) (c : Fin n → ℂ)   (R : Fin n
 → ℝ),  …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.setIntegral_map_equiv`：setIntegral_map_equiv {Y} [Measurab
leSpace Y] (e : X ≃ᵐ Y) (f : Y -> E) (s : Set Y) : ∫ y in s, f y ∂Measure.map e 
μ = ∫ x in e ⁻¹' s, f (e …
· 使用定理 `MeasureTheory.Measure.volume_eq_prod`：volume_eq_prod (α β) [MeasureSpace
 α] [MeasureSpace β] : (volume : Measure (α × β)) = (volume : Measure α).prod (v
olume : Measure β)
· 使用定理 `MeasureTheory.setIntegral_prod`：setIntegral_prod (f : α × β -> E) {s : S
et α} {t : Set β} (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) : ∫ z in s ×ˢ t, f z
 ∂μ.prod ν = ∫ x in …
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.instSigmaFiniteForallVolume`：∀ {ι : Type u_1} [ins
t : Fintype ι] {α : ι → Type u_4} [inst_1 : (i : ι) → MeasureTheory.MeasureSpace
 (α i)]   [∀ (i : ι), MeasureTheory.Sig…
· 使用定理 `TorusIntegrable.function_integrable`：function_integrable [NormedSpace Co
mplex E] (hf : TorusIntegrable f c R) : IntegrableOn (fun θ : Realⁿ => (∏ i, R i
 * exp (θ i * I) * I : Co…
· 使用定理 `MeasureTheory.MeasurePreserving.integrableOn_comp_preimage`：∀ {α : Type 
u_1} {β : Type u_2} {ε : Type u_3} {mα : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [inst : TopologicalSpace ε] [inst_1 …
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `circleIntegral_def_Icc`：circleIntegral_def_Icc (f : Complex -> E) (c : C
omplex) (R : Real) : (∮ z in C(c, R), f z) = ∫ θ in Icc 0 (2 * π), deriv (circle
Map c R) θ •…
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
Recurrent formula for `torusIntegral`, see also `torusIntegral_succ`.
-/
theorem torusIntegral_succAbove
    {f : ℂⁿ⁺¹ → E} {c : ℂⁿ⁺¹} {R : ℝⁿ⁺¹} (hf : TorusIntegrable f c R)
    (i : Fin (n + 1)) :
    (∯ x in T(c, R), f x) =
      ∮ x in C(c i, R i), ∯ y in T(c ∘ i.succAbove, R ∘ i.succAbove), f (i.insertNth x y) := by
  set e : ℝ × ℝⁿ ≃ᵐ ℝⁿ⁺¹ := (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have heπ : (e ⁻¹' Icc 0 fun _ => 2 * π) = Icc 0 (2 * π) ×ˢ Icc (0 : ℝⁿ) fun _ => 2 * π :=
    ((Fin.insertNthOrderIso (fun _ => ℝ) i).preimage_Icc _ _).trans (Icc_prod_eq _ _)
  rw [torusIntegral, ← hem.map_eq, setIntegral_map_equiv, heπ, Measure.volume_eq_prod,
    setIntegral_prod, circleIntegral_def_Icc]
  · refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    simp +unfoldPartialApp only [e, torusIntegral, ← integral_smul,
      deriv_circleMap, i.prod_univ_succAbove _, smul_smul, torusMap, circleMap_zero]
    refine setIntegral_congr_fun measurableSet_Icc fun Θ _ => ?_
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, i.insertNth_apply_same,
      i.insertNth_apply_succAbove, (· ∘ ·), Fin.insertNthEquiv, Equiv.coe_fn_mk]
    congr 2
    simp only [funext_iff, i.forall_iff_succAbove, circleMap, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, imp_true_iff, and_self_iff]
  · have := hf.function_integrable
    rwa [← hem.integrableOn_comp_preimage e.measurableEmbedding, heπ] at this

/-- Recurrent formula for `torusIntegral`, see also `torusIntegral_succAbove`. -/
/-
**torusIntegral_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：torusIntegral_succ {f : Complexⁿ⁺¹ -> E} {c : Complexⁿ⁺¹} {R : Realⁿ⁺¹} (h
f : TorusIntegrable f c R) : (∯ x in T(c, R), f x) = ∮ x in C(c 0, R 0), ∯ y in 
T(c ∘ Fin.succ, R ∘ Fin.succ), f (Fin.cons x y)
参数：hf : TorusIntegrable f c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.insertNth_zero'`：insertNth_zero' (x : β) (p : Fin n -> β) : @insertN
th _ (fun _ => β) 0 x p = cons x p
· 使用定理 `torusIntegral_succAbove`：torusIntegral_succAbove {f : Complexⁿ⁺¹ -> E} {
c : Complexⁿ⁺¹} {R : Realⁿ⁺¹} (hf : TorusIntegrable f c R) (i : Fin (n + 1)) : (
∯ x in T(c, R…

--- 原说明 ---
Recurrent formula for `torusIntegral`, see also `torusIntegral_succAbove`.
-/
theorem torusIntegral_succ
    {f : ℂⁿ⁺¹ → E} {c : ℂⁿ⁺¹} {R : ℝⁿ⁺¹} (hf : TorusIntegrable f c R) :
    (∯ x in T(c, R), f x) =
      ∮ x in C(c 0, R 0), ∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ), f (Fin.cons x y) := by
  simpa using torusIntegral_succAbove hf 0
