/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Cauchy Distribution over ℝ

Define the Cauchy distribution with location parameter `x₀` and scale parameter `γ`.

Note that we use "location" and "scale" to refer to these parameters in theorem names.

## Main definition

* `cauchyPDFReal`: the function `x₀ γ x ↦ π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹`,
  which is the probability density function of a Cauchy distribution with location parameter `x₀`
  and scale parameter `γ` (when `γ ≠ 0`).
* `cauchyPDF`: `ℝ≥0∞`-valued pdf, `cauchyPDF μ v x = ENNReal.ofReal (cauchyPDFReal μ v x)`.
* `cauchyMeasure`: a Cauchy measure on `ℝ`, parametrized by a location parameter `x₀ : ℝ` and a
  scale parameter `γ : ℝ≥0`.  If `γ = 0`, this is `dirac x₀`, otherwise it is defined as the
  measure with density `cauchyPDF x₀ γ` with respect to the Lebesgue measure.

-/

@[expose] public section

open scoped Real ENNReal NNReal

open MeasureTheory Measure

namespace ProbabilityTheory

section CauchyPDF

/-- The pdf of the cauchy distribution depending on its location `x₀` and scale `γ` parameters. -/
/-
**ProbabilityTheory.cauchyPDFReal** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：cauchyPDFReal (x₀ : Real) (γ : Real>=0) (x : Real) : Real
参数：x₀ : Real；γ : Real>=0；x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pdf of the cauchy distribution depending on its location `x₀` and scale `γ` 
parameters.
-/
noncomputable def cauchyPDFReal (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) : ℝ :=
  π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹

@[deprecated (since := "2026-03-06")] alias _root_Probability.CauchyPDFReal := cauchyPDFReal

@[simp]
/-
**ProbabilityTheory.cauchyPDFReal_scale_zero** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：cauchyPDFReal_scale_zero (x₀ : Real) : cauchyPDFReal x₀ 0 = 0
参数：x₀ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cauchyPDFReal_scale_zero (x₀ : ℝ) : cauchyPDFReal x₀ 0 = 0 := by
  ext
  simp [cauchyPDFReal]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_scale_zero := cauchyPDFReal_scale_zero
/-
**ProbabilityTheory.cauchyPDFReal_def** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：cauchyPDFReal_def (x₀ : Real) (γ : Real>=0) (x : Real) : cauchyPDFReal x₀ 
γ x = π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹
参数：x₀ : Real；γ : Real>=0；x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cauchyPDFReal_def (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) :
    cauchyPDFReal x₀ γ x = π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹ := by rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_def := cauchyPDFReal_def
/-
**ProbabilityTheory.cauchyPDFReal_def'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：cauchyPDFReal_def' (x₀ : Real) (γ : Real>=0) (x : Real) : cauchyPDFReal x₀
 γ x = π⁻¹ * γ⁻¹ * (1 + ((x - x₀) / γ) ^ 2)⁻¹
参数：x₀ : Real；γ : Real>=0；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.cauchyPDFReal_def`：cauchyPDFReal_def (x₀ : Real) (γ : 
Real>=0) (x : Real) : cauchyPDFReal x₀ γ x = π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.pow_eq_eval`：pow_eq_eval [CommGroupWithZero 
M] {l : NF M} {r : Nat} (hr : r != 0) {x : M} (hx : x = l.eval) : x ^ r = (l ^ r
).eval
（共 114 条，此处仅展示前 30 条）
-/
lemma cauchyPDFReal_def' (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) :
    cauchyPDFReal x₀ γ x = π⁻¹ * γ⁻¹ * (1 + ((x - x₀) / γ) ^ 2)⁻¹ := by
  rw [cauchyPDFReal_def]
  by_cases h : γ = 0
  · simp [h]
  simp
  field

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_def' := cauchyPDFReal_def'

/-- The pdf of the gamma distribution, as a function valued in `ℝ≥0∞`. -/
/-
**ProbabilityTheory.cauchyPDF** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：cauchyPDF (x₀ : Real) (γ : Real>=0) (x : Real) : Real>=0∞
参数：x₀ : Real；γ : Real>=0；x : Real。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pdf of the gamma distribution, as a function valued in `ℝ≥0∞`.
-/
noncomputable def cauchyPDF (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (cauchyPDFReal x₀ γ x)

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF := cauchyPDF

@[simp]
/-
**ProbabilityTheory.cauchyPDF_scale_zero** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：cauchyPDF_scale_zero (x₀ : Real) : cauchyPDF x₀ 0 = 0
参数：x₀ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ProbabilityTheory.cauchyPDFReal_scale_zero`：cauchyPDFReal_scale_zero (x₀
 : Real) : cauchyPDFReal x₀ 0 = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cauchyPDF_scale_zero (x₀ : ℝ) : cauchyPDF x₀ 0 = 0 := by
  ext
  simp [cauchyPDF]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF_scale_zero := cauchyPDF_scale_zero
/-
**ProbabilityTheory.cauchyPDF_def** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cauchyPDF_def (x₀ : Real) (γ : Real>=0) (x : Real) : cauchyPDF x₀ γ x = EN
NReal.ofReal (cauchyPDFReal x₀ γ x)
参数：x₀ : Real；γ : Real>=0；x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cauchyPDF_def (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) :
  cauchyPDF x₀ γ x = ENNReal.ofReal (cauchyPDFReal x₀ γ x) := by rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF_def := cauchyPDF_def

@[fun_prop]
/-
**ProbabilityTheory.measurable_cauchyPDFReal** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：measurable_cauchyPDFReal (x₀ : Real) (γ : Real>=0) : Measurable (cauchyPDF
Real x₀ γ)
参数：x₀ : Real；γ : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Measurable.fun_inv`：∀ {G : Type u_2} {α : Type u_3} [inst : Inv G] [inst
_1 : MeasurableSpace G] [MeasurableInv G] {m : MeasurableSpace α}   {f : α → G},
 Measura…
· 使用定理 `ContinuousInv₀.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : GroupWithZero γ]   [T1S
pace γ] [Continuou…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Measurable.add_const`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Add M] {m : MeasurableSpace α} {f : α → M}   [MeasurableAdd M
], Measura…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `Measurable.pow_const`：Measurable.pow_const (hf : Measurable f) (c : γ) :
 Measurable fun x => f x ^ c
· 使用定理 `ContinuousMul.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Mul γ] [Con…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Measurable.sub_const`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurable
Space G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   [MeasurableSub G
], Measura…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma measurable_cauchyPDFReal (x₀ : ℝ) (γ : ℝ≥0) : Measurable (cauchyPDFReal x₀ γ) := by
  unfold cauchyPDFReal
  fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.measurable_cauchyPDFReal := measurable_cauchyPDFReal

@[fun_prop]
/-
**ProbabilityTheory.stronglyMeasurable_cauchyPDFReal** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：stronglyMeasurable_cauchyPDFReal (x₀ : Real) (γ : Real>=0) : StronglyMeasu
rable (cauchyPDFReal x₀ γ)
参数：x₀ : Real；γ : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `ProbabilityTheory.measurable_cauchyPDFReal`：measurable_cauchyPDFReal (x₀
 : Real) (γ : Real>=0) : Measurable (cauchyPDFReal x₀ γ)
-/
lemma stronglyMeasurable_cauchyPDFReal (x₀ : ℝ) (γ : ℝ≥0) :
    StronglyMeasurable (cauchyPDFReal x₀ γ) := by fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.stronglyMeasurable_cauchyPDFReal := stronglyMeasurable_cauchyPDFReal

@[fun_prop]
/-
**ProbabilityTheory.measurable_cauchyPDF** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：measurable_cauchyPDF (x₀ : Real) (γ : Real>=0) : Measurable (cauchyPDF x₀ 
γ)
参数：x₀ : Real；γ : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.ennreal_ofReal`：Measurable.ennreal_ofReal {f : α -> Real} (hf
 : Measurable f) : Measurable fun x => ENNReal.ofReal (f x)
· 使用引理 `ProbabilityTheory.measurable_cauchyPDFReal`：measurable_cauchyPDFReal (x₀
 : Real) (γ : Real>=0) : Measurable (cauchyPDFReal x₀ γ)
-/
lemma measurable_cauchyPDF (x₀ : ℝ) (γ : ℝ≥0) : Measurable (cauchyPDF x₀ γ) := by
  unfold cauchyPDF
  fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.measurable_cauchyPDF := measurable_cauchyPDF

@[fun_prop]
/-
**ProbabilityTheory.stronglyMeasurable_cauchyPDF** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：stronglyMeasurable_cauchyPDF (x₀ : Real) (γ : Real>=0) : StronglyMeasurabl
e (cauchyPDF x₀ γ)
参数：x₀ : Real；γ : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `ProbabilityTheory.measurable_cauchyPDF`：measurable_cauchyPDF (x₀ : Real)
 (γ : Real>=0) : Measurable (cauchyPDF x₀ γ)
-/
lemma stronglyMeasurable_cauchyPDF (x₀ : ℝ) (γ : ℝ≥0) :
    StronglyMeasurable (cauchyPDF x₀ γ) := by fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.stronglyMeasurable_cauchyPDF := stronglyMeasurable_cauchyPDF

/-- `cauchyPDFReal` is positive for `γ > 0`. -/
/-
**ProbabilityTheory.cauchyPDF_pos** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cauchyPDF_pos (x₀ : Real) {γ : Real>=0} (hγ : γ != 0) (x : Real) : 0 < cau
chyPDFReal x₀ γ x
参数：x₀ : Real；hγ : γ != 0；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.cauchyPDFReal_def`：cauchyPDFReal_def (x₀ : Real) (γ : 
Real>=0) (x : Real) : cauchyPDFReal x₀ γ x = π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `Mathlib.Meta.Positivity.nnreal_coe_pos`：∀ {r : NNReal}, 0 < r → 0 < ↑r
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R

--- 原说明 ---
`cauchyPDFReal` is positive for `γ > 0`.
-/
lemma cauchyPDF_pos (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) (x : ℝ) : 0 < cauchyPDFReal x₀ γ x := by
  rw [cauchyPDFReal_def]
  positivity

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyPDF_pos := cauchyPDF_pos
/-
**ProbabilityTheory.integral_cauchyPDFReal_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：integral_cauchyPDFReal_eq_one (x₀ : Real) {γ : Real>=0} (hγ : γ != 0) : ∫ 
x, cauchyPDFReal x₀ γ x = 1
参数：x₀ : Real；hγ : γ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.cauchyPDFReal_def'`：cauchyPDFReal_def' (x₀ : Real) (γ 
: Real>=0) (x : Real) : cauchyPDFReal x₀ γ x = π⁻¹ * γ⁻¹ * (1 + ((x - x₀) / γ) ^
 2)⁻¹
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `MeasureTheory.integral_sub_right_eq_self`：∀ {G : Type u_4} {E : Type u_5
} [inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpa
ce ℝ E]   {μ : MeasureTheory.M…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.IsAddLeftInvariant.isAddRightInvariant`：∀ {G : Type u_1} [
inst : MeasurableSpace G] [inst_1 : AddCommSemigroup G] {μ : MeasureTheory.Measu
re G}   [μ.IsAddLeftInvariant], μ.IsAddRig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.integral_comp_div`：integral_comp_div (g : Real -> 
F) (a : Real) : (∫ x : Real, g (x / a)) = |a| • ∫ y : Real, g y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
· 使用定理 `integral_univ_inv_one_add_sq`：integral_univ_inv_one_add_sq : ∫ (x : Real
), (1 + x ^ 2)⁻¹ = π
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 54 条，此处仅展示前 30 条）
-/
lemma integral_cauchyPDFReal_eq_one (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    ∫ x, cauchyPDFReal x₀ γ x = 1 := by
  simp [cauchyPDFReal_def', NNReal.coe_inv, integral_const_mul,
    integral_sub_right_eq_self (f := fun x : ℝ ↦ (1 + (x / ↑γ) ^ 2)⁻¹),
    integral_comp_div (g := fun x : ℝ ↦ (1 + x ^ 2)⁻¹)]
  field

@[deprecated (since := "2026-03-06")]
alias _root_Probability.integral_cauchyPDFReal := integral_cauchyPDFReal_eq_one

@[fun_prop]
/-
**ProbabilityTheory.integrable_cauchyPDFReal** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：integrable_cauchyPDFReal (x₀ : Real) {γ : Real>=0} : Integrable (cauchyPDF
Real x₀ γ)
参数：x₀ : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.cauchyPDFReal_scale_zero`：cauchyPDFReal_scale_zero (x₀
 : Real) : cauchyPDFReal x₀ 0 = 0
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
· 使用定理 `MeasureTheory.Integrable.of_integral_ne_zero`：∀ {α : Type u_1} {G : Type
 u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSp
ace α}   {μ : MeasureTheory.Measur…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `ProbabilityTheory.integral_cauchyPDFReal_eq_one`：integral_cauchyPDFReal_
eq_one (x₀ : Real) {γ : Real>=0} (hγ : γ != 0) : ∫ x, cauchyPDFReal x₀ γ x = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma integrable_cauchyPDFReal (x₀ : ℝ) {γ : ℝ≥0} :
    Integrable (cauchyPDFReal x₀ γ) := by
  by_cases! h : γ = 0
  · simp only [h, cauchyPDFReal_scale_zero]
    exact integrable_zero _ _ _
  apply Integrable.of_integral_ne_zero
  simp [h, integral_cauchyPDFReal_eq_one]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.integrable_cauchyPDFReal := integrable_cauchyPDFReal

/-- The pdf of the cauchy distribution integrates to 1. -/
@[simp]
/-
**ProbabilityTheory.lintegral_cauchyPDF_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：lintegral_cauchyPDF_eq_one (x₀ : Real) {γ : Real>=0} (hγ : γ != 0) : ∫⁻ x,
 cauchyPDF x₀ γ x = 1
参数：x₀ : Real；hγ : γ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_eq_one_iff`：toReal_eq_one_iff (x : Real>=0∞) : x.toReal =
 1 ↔ x = 1
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `ProbabilityTheory.cauchyPDF_pos`：cauchyPDF_pos (x₀ : Real) {γ : Real>=0}
 (hγ : γ != 0) (x : Real) : 0 < cauchyPDFReal x₀ γ x
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用引理 `ProbabilityTheory.stronglyMeasurable_cauchyPDFReal`：stronglyMeasurable_c
auchyPDFReal (x₀ : Real) (γ : Real>=0) : StronglyMeasurable (cauchyPDFReal x₀ γ)
· 使用引理 `ProbabilityTheory.integral_cauchyPDFReal_eq_one`：integral_cauchyPDFReal_
eq_one (x₀ : Real) {γ : Real>=0} (hγ : γ != 0) : ∫ x, cauchyPDFReal x₀ γ x = 1

--- 原说明 ---
The pdf of the cauchy distribution integrates to 1.
-/
lemma lintegral_cauchyPDF_eq_one (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    ∫⁻ x, cauchyPDF x₀ γ x = 1 := by
  unfold cauchyPDF
  rw [← ENNReal.toReal_eq_one_iff, ← integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x ↦ (cauchyPDF_pos x₀ hγ x).le) (by fun_prop),
    integral_cauchyPDFReal_eq_one x₀ hγ]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.lintegral_cauchyPDF_eq_one := lintegral_cauchyPDF_eq_one

end CauchyPDF

section CauchyMeasure

/-- A Cauchy distribution on `ℝ` with location parameter `x₀` and scale parameter `γ`. -/
/-
**ProbabilityTheory.cauchyMeasure** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：cauchyMeasure (x₀ : Real) (γ : Real>=0) : Measure Real
参数：x₀ : Real；γ : Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Cauchy distribution on `ℝ` with location parameter `x₀` and scale parameter `γ
`.
-/
noncomputable def cauchyMeasure (x₀ : ℝ) (γ : ℝ≥0) : Measure ℝ :=
  if γ = 0 then dirac x₀ else volume.withDensity (cauchyPDF x₀ γ)

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure := cauchyMeasure
/-
**ProbabilityTheory.cauchyMeasure_of_scale_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：cauchyMeasure_of_scale_ne_zero (x₀ : Real) {γ : Real>=0} (hγ : γ != 0) : c
auchyMeasure x₀ γ = volume.withDensity (cauchyPDF x₀ γ)
参数：x₀ : Real；hγ : γ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma cauchyMeasure_of_scale_ne_zero (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    cauchyMeasure x₀ γ = volume.withDensity (cauchyPDF x₀ γ) := if_neg hγ

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure_of_scale_ne_zero := cauchyMeasure_of_scale_ne_zero

@[simp]
/-
**ProbabilityTheory.cauchyMeasure_zero_scale** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：cauchyMeasure_zero_scale (x₀ : Real) : cauchyMeasure x₀ 0 = dirac x₀
参数：x₀ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma cauchyMeasure_zero_scale (x₀ : ℝ) : cauchyMeasure x₀ 0 = dirac x₀ := if_pos rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure_zero_scale := cauchyMeasure_zero_scale
/-
**ProbabilityTheory.instIsProbabilityMeasure_cauchyMeasure** 是 Mathlib 中的一个实例，位于
命名空间 `ProbabilityTheory`。
形式化陈述：instIsProbabilityMeasure_cauchyMeasure (x₀ : Real) (γ : Real>=0) : IsProba
bilityMeasure (cauchyMeasure x₀ γ) where measure_univ
参数：x₀ : Real；γ : Real>=0。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.cauchyMeasure_zero_scale`：cauchyMeasure_zero_scale (x₀
 : Real) : cauchyMeasure x₀ 0 = dirac x₀
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.cauchyMeasure_of_scale_ne_zero`：cauchyMeasure_of_scale
_ne_zero (x₀ : Real) {γ : Real>=0} (hγ : γ != 0) : cauchyMeasure x₀ γ = volume.w
ithDensity (cauchyPDF x₀ γ)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用引理 `ProbabilityTheory.lintegral_cauchyPDF_eq_one`：lintegral_cauchyPDF_eq_one
 (x₀ : Real) {γ : Real>=0} (hγ : γ != 0) : ∫⁻ x, cauchyPDF x₀ γ x = 1
-/
instance instIsProbabilityMeasure_cauchyMeasure (x₀ : ℝ) (γ : ℝ≥0) :
    IsProbabilityMeasure (cauchyMeasure x₀ γ) where
  measure_univ := by by_cases h : γ = 0 <;> simp [cauchyMeasure_of_scale_ne_zero, h]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.instIsProbabilityMeasure_cauchyMeasure :=
  instIsProbabilityMeasure_cauchyMeasure

end CauchyMeasure

end ProbabilityTheory

