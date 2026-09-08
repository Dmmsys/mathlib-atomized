/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.LpSpace

/-! # Sobolev spaces (Bessel potential spaces)

In this file we define Sobolev spaces on normed vector spaces via the Fourier transform.
These spaces are also known as Bessel potential spaces. The Bessel potential operator
`besselPotential` is the Fourier multiplier with the symbol `x ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)` and a
tempered distribution `u` belongs to the Sobolev space `H ^ {s, p}` if
`besselPotential E F s u` can be represented by a `Lp` function, informally this is written as
`𝓕⁻ (fun x ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)) 𝓕 u ∈ Lp`.

Note that the Bessel potential is the operator `(1 - (2 * π) ^ (-2) • Δ) ^ (s / 2)` and not
`(1 - Δ) ^ (s / 2)` due to the convention of the Fourier transform. This obviously does not impact
the definition of the Sobolev spaces.

## Main definitions

* `TemperedDistribution.besselPotential`: The Bessel potential operator is the Fourier multiplier
  with the function `(1 + ‖x‖ ^ 2) ^ (s / 2)`.
* `TemperedDistribution.memSobolev`: A tempered distribution lies in the Sobolev space of order `s`
  and `p` if `besselPotential E F s u ∈ Lp`.

## Main statements

* `SchwartzMap.memSobolev`: Each Schwartz function belongs to every Sobolev space
* `TemperedDistribution.memSobolev_two_iff_fourier`: The characterization of `p = 2` Sobolev
  functions
* `TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded`: If `u` is a Sobolev
  function, then `g • u` is a Sobolev function of the same order provided `g` is bounded.
* `TemperedDistribution.MemSobolev.lineDerivOp`: If `u` is a Sobolev function of order `s`, then
  `∂_{m} u` is a Sobolev function of order `s - 1`.
* `TemperedDistribution.MemSobolev.laplacian`: If `u` is a Sobolev function of order `s`, then
  `Δ u` is a Sobolev function of order `s - 2`.


## References
* [M. Taylor, *Partial Differential Equations 1*][taylorPDE1]
* [W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*][mclean2000]

-/

@[expose] public noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform TemperedDistribution ENNReal MeasureTheory
open scoped SchwartzMap

namespace TemperedDistribution

section normed

variable [NormedSpace ℂ F]

variable (E F) in
/-- The Bessel potential operator is the Fourier multiplier with the function
`(1 + ‖x‖ ^ 2) ^ (s / 2)`.

Note that due to the convention of the Fourier transform, this is the operator
`(1 - (2 * π) ^ (-2) • Δ) ^ (s / 2)` not `(1 - Δ) ^ (s / 2)`. -/
/-
**TemperedDistribution.besselPotential** 是 Mathlib 中的一个定义，位于命名空间 `TemperedDistri
bution`。
形式化陈述：besselPotential (s : Real) : 𝓢'(E, F) ->L[Complex] 𝓢'(E, F)
参数：s : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Bessel potential operator is the Fourier multiplier with the function
`(1 + ‖x‖ ^ 2) ^ (s / 2)`.

Note that due to the convention of the Fourier transform, this is the operator
`(1 - (2 * π) ^ (-2) • Δ) ^ (s / 2)` not `(1 - Δ) ^ (s / 2)`.
-/
def besselPotential (s : ℝ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierMultiplierCLM F (fun x ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ))

variable (E F) in
@[simp]
/-
**TemperedDistribution.besselPotential_zero** 是 Mathlib 中的一个定理，位于命名空间 `TemperedD
istribution`。
形式化陈述：besselPotential_zero : besselPotential E F 0 = ContinuousLinearMap.id Comp
lex _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.fourierMultiplierCLM.congr_simp`：∀ {E : Type u_3} (
F : Type u_4) [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F]   [i
nst_2 : InnerProductSpace ℝ E] [inst_3 : N…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `TemperedDistribution.fourierMultiplierCLM_const`：fourierMultiplierCLM_co
nst (c : Complex) : fourierMultiplierCLM F (fun (_ : E) => c) = c • ContinuousLi
nearMap.id _ _
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem besselPotential_zero : besselPotential E F 0 = ContinuousLinearMap.id ℂ _ := by
  ext f
  simp [besselPotential]

@[simp]
/-
**TemperedDistribution.besselPotential_besselPotential_apply** 是 Mathlib 中的一个定理，
位于命名空间 `TemperedDistribution`。
形式化陈述：besselPotential_besselPotential_apply (s s' : Real) (f : 𝓢'(E, F)) : besse
lPotential E F s' (besselPotential E F s f) = besselPotential E F (s + s') f
参数：s s' : Real；f : 𝓢'(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply`：fo
urierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E -> Complex} (hg₁ : g₁.H
asTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E…
· 使用定理 `Function.HasTemperateGrowth.comp`：∀ {D : Type u_4} {E : Type u_5} {F : T
ype u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : No
rmedAddCommGroup F] [i…
· 使用定理 `Function.Complex.hasTemperateGrowth_ofReal`：Function.HasTemperateGrowth 
Complex.ofReal
· 使用定理 `Function.hasTemperateGrowth_one_add_norm_sq_rpow`：hasTemperateGrowth_one
_add_norm_sq_rpow (r : Real) : (fun (x : H) => (1 + ‖x‖ ^ 2) ^ r).HasTemperateGr
owth
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 49 条，此处仅展示前 30 条）
-/
theorem besselPotential_besselPotential_apply (s s' : ℝ) (f : 𝓢'(E, F)) :
    besselPotential E F s' (besselPotential E F s f) = besselPotential E F (s + s') f := by
  simp only [besselPotential]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp only [Pi.mul_apply]
  norm_cast
  calc
    _ = (1 + ‖x‖ ^ 2) ^ (s / 2 + s' / 2) := by
      rw [← Real.rpow_add (by positivity)]
    _ = _ := by congr; ring
/-
**TemperedDistribution.besselPotential_compL_besselPotential** 是 Mathlib 中的一个定理，
位于命名空间 `TemperedDistribution`。
形式化陈述：besselPotential_compL_besselPotential (s s' : Real) : besselPotential E F 
s' ∘L besselPotential E F s = besselPotential E F (s + s')
参数：s s' : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TemperedDistribution.besselPotential_besselPotential_apply`：besselPotent
ial_besselPotential_apply (s s' : Real) (f : 𝓢'(E, F)) : besselPotential E F s' 
(besselPotential E F s f) = besselPotential E F …
-/
theorem besselPotential_compL_besselPotential (s s' : ℝ) :
    besselPotential E F s' ∘L besselPotential E F s = besselPotential E F (s + s') := by
  ext f : 1
  exact besselPotential_besselPotential_apply s s' f
/-
**TemperedDistribution.besselPotential_neg_apply_eq_iff** 是 Mathlib 中的一个定理，位于命名空
间 `TemperedDistribution`。
形式化陈述：besselPotential_neg_apply_eq_iff (s : Real) (f g : 𝓢'(E, F)) : besselPoten
tial E F (-s) f = g ↔ besselPotential E F s g = f
参数：s : Real；f g : 𝓢'(E, F)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TemperedDistribution.besselPotential_besselPotential_apply`：besselPotent
ial_besselPotential_apply (s s' : Real) (f : 𝓢'(E, F)) : besselPotential E F s' 
(besselPotential E F s f) = besselPotential E F …
· 使用定理 `TemperedDistribution.besselPotential.congr_simp`：∀ (E : Type u_1) (F : T
ype u_2) [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F]   [inst_2
 : InnerProductSpace ℝ E] [inst_3 : F…
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `TemperedDistribution.besselPotential_zero`：besselPotential_zero : bessel
Potential E F 0 = ContinuousLinearMap.id Complex _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
-/
theorem besselPotential_neg_apply_eq_iff (s : ℝ) (f g : 𝓢'(E, F)) :
    besselPotential E F (-s) f = g ↔ besselPotential E F s g = f := by
  constructor <;>
  intro h <;> simp [← h]

open scoped Real Laplacian LineDeriv
/-
**TemperedDistribution.besselPotential_neg_one_lineDerivOp_eq** 是 Mathlib 中的一个定理
，位于命名空间 `TemperedDistribution`。
形式化陈述：besselPotential_neg_one_lineDerivOp_eq {m : E} (f : 𝓢'(E, F)) : (besselPot
ential E F (-1)) (∂_{m} f) = (2 * π * Complex.I) • fourierMultiplierCLM F (fun x
 => Complex.ofReal <| inner Real x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : Real)) f
参数：f : 𝓢'(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM`：lineDeriv_eq_fou
rierMultiplierCLM (m : E) (f : 𝓢'(E, F)) : ∂_{m} f = (2 * π * Complex.I) • fouri
erMultiplierCLM F (inner Real · m) f
· 使用定理 `TemperedDistribution.besselPotential.eq_1`：∀ (E : Type u_1) (F : Type u_
2) [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F]   [inst_2 : Inn
erProductSpace ℝ E] [inst_3 : F…
· 使用定理 `ContinuousLinearMap.map_smul_of_tower`：map_smul_of_tower {R S : Type*} [
Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂] [Module S M₂] [LinearMap.Compa
tibleSMul M₁ M₂ R S] (f : M…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply`：fo
urierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E -> Complex} (hg₁ : g₁.H
asTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E…
· 使用定理 `Function.HasTemperateGrowth.comp`：∀ {D : Type u_4} {E : Type u_5} {F : T
ype u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : No
rmedAddCommGroup F] [i…
· 使用定理 `Function.Complex.hasTemperateGrowth_ofReal`：Function.HasTemperateGrowth 
Complex.ofReal
· 使用定理 `Function.hasTemperateGrowth_inner_left`：hasTemperateGrowth_inner_left (c
 : H) : (inner Real · c).HasTemperateGrowth
· 使用定理 `Function.hasTemperateGrowth_one_add_norm_sq_rpow`：hasTemperateGrowth_one
_add_norm_sq_rpow (r : Real) : (fun (x : H) => (1 + ‖x‖ ^ 2) ^ r).HasTemperateGr
owth
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem besselPotential_neg_one_lineDerivOp_eq {m : E} (f : 𝓢'(E, F)) :
    (besselPotential E F (-1)) (∂_{m} f) =
      (2 * π * Complex.I) • fourierMultiplierCLM F (fun x ↦ Complex.ofReal <|
      inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)) f := by
  rw [lineDeriv_eq_fourierMultiplierCLM, besselPotential,
    ContinuousLinearMap.map_smul_of_tower,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp
/-
**TemperedDistribution.besselPotential_neg_two_laplacian_eq** 是 Mathlib 中的一个定理，位
于命名空间 `TemperedDistribution`。
形式化陈述：besselPotential_neg_two_laplacian_eq (f : 𝓢'(E, F)) : (besselPotential E F
 (-2)) (Δ f) = -(2 * π) ^ 2 • fourierMultiplierCLM F (fun x => Complex.ofReal <|
 ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 : Real)) f
参数：f : 𝓢'(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.laplacian_eq_fourierMultiplierCLM`：laplacian_eq_fou
rierMultiplierCLM (f : 𝓢'(E, F)) : Δ f = -(2 * π) ^ 2 • fourierMultiplierCLM F (
fun x => Complex.ofReal (‖x‖ ^ 2)) f
· 使用定理 `TemperedDistribution.besselPotential.eq_1`：∀ (E : Type u_1) (F : Type u_
2) [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F]   [inst_2 : Inn
erProductSpace ℝ E] [inst_3 : F…
· 使用定理 `ContinuousLinearMap.map_smul_of_tower`：map_smul_of_tower {R S : Type*} [
Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂] [Module S M₂] [LinearMap.Compa
tibleSMul M₁ M₂ R S] (f : M…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply`：fo
urierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E -> Complex} (hg₁ : g₁.H
asTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E…
· 使用定理 `Function.HasTemperateGrowth.comp`：∀ {D : Type u_4} {E : Type u_5} {F : T
ype u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : No
rmedAddCommGroup F] [i…
· 使用定理 `Function.Complex.hasTemperateGrowth_ofReal`：Function.HasTemperateGrowth 
Complex.ofReal
· 使用定理 `Function.hasTemperateGrowth_norm_sq`：hasTemperateGrowth_norm_sq : (fun (
x : H) => ‖x‖ ^ 2).HasTemperateGrowth
· 使用定理 `Function.hasTemperateGrowth_one_add_norm_sq_rpow`：hasTemperateGrowth_one
_add_norm_sq_rpow (r : Real) : (fun (x : H) => (1 + ‖x‖ ^ 2) ^ r).HasTemperateGr
owth
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `neg_div_self`：neg_div_self {a : K} (h : a != 0) : -a / a = -1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem besselPotential_neg_two_laplacian_eq (f : 𝓢'(E, F)) :
    (besselPotential E F (-2)) (Δ f) = -(2 * π) ^ 2 •
      fourierMultiplierCLM F (fun x ↦ Complex.ofReal <| ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 : ℝ)) f := by
  rw [laplacian_eq_fourierMultiplierCLM, besselPotential,
    ContinuousLinearMap.map_smul_of_tower,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp

end normed

section inner

variable [InnerProductSpace ℂ F]

open FourierTransform

@[simp]
/-
**TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply** 是 
Mathlib 中的一个定理，位于命名空间 `TemperedDistribution`。
形式化陈述：fourier_besselPotential_eq_smulLeftCLM_fourier_apply (s : Real) (f : 𝓢'(E,
 F)) : 𝓕 (besselPotential E F s f) = smulLeftCLM F (fun x => ((1 + ‖x‖ ^ 2) ^ (s
 / 2) : Real)) (𝓕 f)
参数：s : Real；f : 𝓢'(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FourierInvPair.fourier_fourierInv_eq`：∀ {E : Type u_5} {F : Type u_6} {i
nst : FourierTransform F E} {inst_1 : FourierTransformInv E F}   [self : Fourier
InvPair E F] (f : E), Four…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourier_besselPotential_eq_smulLeftCLM_fourier_apply (s : ℝ) (f : 𝓢'(E, F)) :
    𝓕 (besselPotential E F s f) =
      smulLeftCLM F (fun x ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 f) := by
  simp [besselPotential, fourierMultiplierCLM]

end inner

section normed

variable [NormedSpace ℂ F] [CompleteSpace F]

/-- A tempered distribution `f` is a Sobolev function of order `s` if there exists an `Lp` function
`f'` such that `𝓕⁻ (1 + ‖x‖ ^ 2) ^ (s / 2) 𝓕 f = f'`. -/
/-
**TemperedDistribution.MemSobolev** 是 Mathlib 中的一个定义，位于命名空间 `TemperedDistributio
n`。
形式化陈述：MemSobolev (s : Real) (p : Real>=0∞) [hp : Fact (1 <= p)] (f : 𝓢'(E, F)) :
 Prop
参数：s : Real；p : Real>=0∞；1 <= p；f : 𝓢'(E, F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A tempered distribution `f` is a Sobolev function of order `s` if there exists a
n `Lp` function
`f'` such that `𝓕⁻ (1 + ‖x‖ ^ 2) ^ (s / 2) 𝓕 f = f'`.
-/
def MemSobolev (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (f : 𝓢'(E, F)) : Prop :=
  ∃ (f' : Lp F p (volume : Measure E)),
    besselPotential E F s f = f'
/-
**TemperedDistribution.memSobolev_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDi
stribution`。
形式化陈述：memSobolev_zero_iff {p : Real>=0∞} [hp : Fact (1 <= p)] {f : 𝓢'(E, F)} : M
emSobolev 0 p f ↔ exists (f' : Lp F p (volume : Measure E)), f = f'
参数：1 <= p；E, F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TemperedDistribution.besselPotential_zero`：besselPotential_zero : bessel
Potential E F 0 = ContinuousLinearMap.id Complex _
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem memSobolev_zero_iff {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f : 𝓢'(E, F)} : MemSobolev 0 p f ↔
    ∃ (f' : Lp F p (volume : Measure E)), f = f' := by
  simp [MemSobolev]
/-
**TemperedDistribution.MemSobolev.add** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDistrib
ution.MemSobolev`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedAddCommGroup F]   [inst_2 : InnerProductSpace ℝ E] [inst_3 : FiniteDimension
al ℝ E] [inst_4 : MeasurableSpace E] [inst_5 : BorelSpace E]   [inst_6 : NormedS
pace ℂ F] [inst_7 : CompleteSpace F] {s : ℝ} {p : ENNReal} [hp : Fact (1 ≤ p)]  
 {f g : TemperedDistribution E F},   TemperedDistribution.MemSobolev s p f →    
 TemperedDistribution.MemSobolev s p g → TemperedDistribution.MemSobolev s p (f 
+ g)
参数：1 ≤ p；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.toTemperedDistributionCLM_apply`：toTemperedDistribution
CLM_apply {p : Real>=0∞} [hp : Fact (1 <= p)] (f : Lp F p μ) : toTemperedDistrib
utionCLM F μ p f = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem MemSobolev.add {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f g : 𝓢'(E, F)}
    (hf : MemSobolev s p f) (hg : MemSobolev s p g) : MemSobolev s p (f + g) := by
  obtain ⟨f', hf⟩ := hf
  obtain ⟨g', hg⟩ := hg
  use f' + g'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_add, hf, hg]
/-
**TemperedDistribution.MemSobolev.sub** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDistrib
ution.MemSobolev`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedAddCommGroup F]   [inst_2 : InnerProductSpace ℝ E] [inst_3 : FiniteDimension
al ℝ E] [inst_4 : MeasurableSpace E] [inst_5 : BorelSpace E]   [inst_6 : NormedS
pace ℂ F] [inst_7 : CompleteSpace F] {s : ℝ} {p : ENNReal} [hp : Fact (1 ≤ p)]  
 {f g : TemperedDistribution E F},   TemperedDistribution.MemSobolev s p f →    
 TemperedDistribution.MemSobolev s p g → TemperedDistribution.MemSobolev s p (f 
- g)
参数：1 ≤ p；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.toTemperedDistributionCLM_apply`：toTemperedDistribution
CLM_apply {p : Real>=0∞} [hp : Fact (1 <= p)] (f : Lp F p μ) : toTemperedDistrib
utionCLM F μ p f = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem MemSobolev.sub {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f g : 𝓢'(E, F)}
    (hf : MemSobolev s p f) (hg : MemSobolev s p g) : MemSobolev s p (f - g) := by
  obtain ⟨f', hf⟩ := hf
  obtain ⟨g', hg⟩ := hg
  use f' - g'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_sub, hf, hg]
/-
**TemperedDistribution.MemSobolev.neg** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDistrib
ution.MemSobolev`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedAddCommGroup F]   [inst_2 : InnerProductSpace ℝ E] [inst_3 : FiniteDimension
al ℝ E] [inst_4 : MeasurableSpace E] [inst_5 : BorelSpace E]   [inst_6 : NormedS
pace ℂ F] [inst_7 : CompleteSpace F] {s : ℝ} {p : ENNReal} [hp : Fact (1 ≤ p)]  
 {f : TemperedDistribution E F}, TemperedDistribution.MemSobolev s p f → Tempere
dDistribution.MemSobolev s p (-f)
参数：1 ≤ p；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.toTemperedDistributionCLM_apply`：toTemperedDistribution
CLM_apply {p : Real>=0∞} [hp : Fact (1 <= p)] (f : Lp F p μ) : toTemperedDistrib
utionCLM F μ p f = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem MemSobolev.neg {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f : 𝓢'(E, F)}
    (hf : MemSobolev s p f) : MemSobolev s p (-f) := by
  obtain ⟨f', hf⟩ := hf
  use -f'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_neg, hf]
/-
**TemperedDistribution.MemSobolev.smul** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDistri
bution.MemSobolev`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedAddCommGroup F]   [inst_2 : InnerProductSpace ℝ E] [inst_3 : FiniteDimension
al ℝ E] [inst_4 : MeasurableSpace E] [inst_5 : BorelSpace E]   [inst_6 : NormedS
pace ℂ F] [inst_7 : CompleteSpace F] {s : ℝ} {p : ENNReal} [hp : Fact (1 ≤ p)] (
c : ℂ)   {f : TemperedDistribution E F}, TemperedDistribution.MemSobolev s p f →
 TemperedDistribution.MemSobolev s p (c • f)
参数：1 ≤ p；c : ℂ；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.toTemperedDistributionCLM_apply`：toTemperedDistribution
CLM_apply {p : Real>=0∞} [hp : Fact (1 <= p)] (f : Lp F p μ) : toTemperedDistrib
utionCLM F μ p f = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem MemSobolev.smul {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (c : ℂ) {f : 𝓢'(E, F)}
    (hf : MemSobolev s p f) : MemSobolev s p (c • f) := by
  obtain ⟨f', hf⟩ := hf
  use c • f'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [hf]

variable (E F) in
@[simp]
/-
**TemperedDistribution.memSobolev_fun_zero** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDi
stribution`。
形式化陈述：memSobolev_fun_zero (s : Real) (p : Real>=0∞) [hp : Fact (1 <= p)] : MemSo
bolev s p (0 : 𝓢'(E, F))
参数：s : Real；p : Real>=0∞；1 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.toTemperedDistributionCLM_apply`：toTemperedDistribution
CLM_apply {p : Real>=0∞} [hp : Fact (1 <= p)] (f : Lp F p μ) : toTemperedDistrib
utionCLM F μ p f = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem memSobolev_fun_zero (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    MemSobolev s p (0 : 𝓢'(E, F)) := by
  use 0
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp only [map_zero]

@[simp]
/-
**TemperedDistribution.memSobolev_besselPotential_iff** 是 Mathlib 中的一个定理，位于命名空间 
`TemperedDistribution`。
形式化陈述：memSobolev_besselPotential_iff {s r : Real} {p : Real>=0∞} [hp : Fact (1 <
= p)] {f : 𝓢'(E, F)} : MemSobolev s p (besselPotential E F r f) ↔ MemSobolev (r 
+ s) p f
参数：1 <= p；E, F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TemperedDistribution.besselPotential_besselPotential_apply`：besselPotent
ial_besselPotential_apply (s s' : Real) (f : 𝓢'(E, F)) : besselPotential E F s' 
(besselPotential E F s f) = besselPotential E F …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem memSobolev_besselPotential_iff {s r : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f : 𝓢'(E, F)} :
    MemSobolev s p (besselPotential E F r f) ↔ MemSobolev (r + s) p f := by
  simp [MemSobolev]

/-- Schwartz functions are in every Sobolev space. -/
/-
**TemperedDistribution._root_.SchwartzMap.memSobolev** 是 Mathlib 中的一个定理，位于命名空间 `
TemperedDistribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Schwartz functions are in every Sobolev space.
-/
theorem _root_.SchwartzMap.memSobolev {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : 𝓢(E, F)) :
    MemSobolev s p (f : 𝓢'(E, F)) := by
  use (SchwartzMap.fourierMultiplierCLM F (fun x ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) f).toLp p
  rw [besselPotential, Lp.toTemperedDistribution_toLp_eq,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]
  congr 1
  apply SchwartzMap.fourierMultiplierCLM_ofReal ℂ
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2))

end normed

section inner

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A tempered distribution belongs to the Sobolev space of order `s` and `p = 2` if and only if
its Fourier transform multiplied by `(1 + ‖x‖ ^ 2) ^ (s / 2)` is in `Lp`. -/
/-
**TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier** 是 Mathlib 中的一
个定理，位于命名空间 `TemperedDistribution`。
形式化陈述：memSobolev_iff_exists_smulLeftCLM_fourier {s : Real} {f : 𝓢'(E, F)} : MemS
obolev s 2 f ↔ exists (f' : Lp F 2 (volume : Measure E)), smulLeftCLM F (fun x =
> ((1 + ‖x‖ ^ 2) ^ (s / 2) : Real)) (𝓕 f) = f'
参数：E, F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_appl
y`：fourier_besselPotential_eq_smulLeftCLM_fourier_apply (s : Real) (f : 𝓢'(E, F)
) : 𝓕 (besselPotential E F s f) = smulLeftCLM F (fun x => ((1 +…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.fourier_toTemperedDistribution_eq`：fourier_toTemperedDi
stribution_eq (f : Lp (α
· 使用定理 `TemperedDistribution.besselPotential.eq_1`：∀ (E : Type u_1) (F : Type u_
2) [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F]   [inst_2 : Inn
erProductSpace ℝ E] [inst_3 : F…
· 使用定理 `TemperedDistribution.fourierMultiplierCLM_apply`：fourierMultiplierCLM_ap
ply (g : E -> Complex) (f : 𝓢'(E, F)) : fourierMultiplierCLM F g f = 𝓕⁻ (smulLef
tCLM F g (𝓕 f))
· 使用定理 `MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq`：fourierInv_toTemp
eredDistribution_eq (f : Lp (α

--- 原说明 ---
A tempered distribution belongs to the Sobolev space of order `s` and `p = 2` if
 and only if
its Fourier transform multiplied by `(1 + ‖x‖ ^ 2) ^ (s / 2)` is in `Lp`.
-/
theorem memSobolev_iff_exists_smulLeftCLM_fourier {s : ℝ} {f : 𝓢'(E, F)} :
    MemSobolev s 2 f ↔ ∃ (f' : Lp F 2 (volume : Measure E)),
    smulLeftCLM F (fun x ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 f) = f' := by
  constructor
  · intro ⟨f', hf'⟩
    use 𝓕 f'
    apply_fun 𝓕 at hf'
    rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply] at hf'
    rw [hf', Lp.fourier_toTemperedDistribution_eq f']
  · intro ⟨f', hf'⟩
    use 𝓕⁻ f'
    rw [besselPotential, TemperedDistribution.fourierMultiplierCLM_apply]
    apply_fun 𝓕⁻ at hf'
    rw [hf', Lp.fourierInv_toTemperedDistribution_eq f']
/-
**TemperedDistribution.memSobolev_zero_iff_exists_fourier** 是 Mathlib 中的一个定理，位于命
名空间 `TemperedDistribution`。
形式化陈述：memSobolev_zero_iff_exists_fourier {f : 𝓢'(E, F)} : MemSobolev 0 2 f ↔ exi
sts (f' : Lp F 2 (volume : Measure E)), 𝓕 f = f'
参数：E, F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `TemperedDistribution.smulLeftCLM_const`：smulLeftCLM_const (c : Complex) 
(f : 𝓢'(E, F)) : smulLeftCLM F (fun _ : E => c) f = c • f
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem memSobolev_zero_iff_exists_fourier {f : 𝓢'(E, F)} :
    MemSobolev 0 2 f ↔ ∃ (f' : Lp F 2 (volume : Measure E)), 𝓕 f = f' := by
  simp [memSobolev_iff_exists_smulLeftCLM_fourier]

/-- The Fourier transform of a Sobolev function of order `s` with `s > d / 2` can be represented by
a `L1` function.

This is the main calculation of the Sobolev embedding theorem. -/
/-
**TemperedDistribution.MemSobolev.fourier_memL1** 是 Mathlib 中的一个定理，位于命名空间 `Tempe
redDistribution.MemSobolev`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedAddCommGroup F]   [inst_2 : InnerProductSpace ℝ E] [inst_3 : FiniteDimension
al ℝ E] [inst_4 : MeasurableSpace E] [inst_5 : BorelSpace E]   [inst_6 : InnerPr
oductSpace ℂ F] [inst_7 : CompleteSpace F] {s : ℝ},   ↑(Module.finrank ℝ E) < 2 
* s →     ∀ {f : TemperedDistribution E F},       TemperedDistribution.MemSobole
v s 2 f →         ∃ v, FourierTransform.fourier f = MeasureTheory.Lp.toTemperedD
istribution v
参数：Module.finrank ℝ E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier`：memSobol
ev_iff_exists_smulLeftCLM_fourier {s : Real} {f : 𝓢'(E, F)} : MemSobolev s 2 f ↔
 exists (f' : Lp F 2 (volume : Measure E)), smulLeft…
· 使用定理 `Function.hasTemperateGrowth_one_add_norm_sq_rpow`：hasTemperateGrowth_one
_add_norm_sq_rpow (r : Real) : (fun (x : H) => (1 + ‖x‖ ^ 2) ^ r).HasTemperateGr
owth
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `ContDiff.continuous`：ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuo
us f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top`：eLpNorm_lt
_top_iff_lintegral_rpow_enorm_lt_top {f : α -> ε} (hp_ne_zero : p != 0) (hp_ne_t
op : p != ∞) : eLpNorm f p μ < ∞ ↔ ∫⁻ a, (‖f a‖ₑ) …
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
（共 123 条，此处仅展示前 30 条）

--- 原说明 ---
The Fourier transform of a Sobolev function of order `s` with `s > d / 2` can be
 represented by
a `L1` function.

This is the main calculation of the Sobolev embedding theorem.
-/
theorem MemSobolev.fourier_memL1 {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) :
    ∃ (v : Lp F 1 (volume : Measure E)), 𝓕 f = (v : 𝓢'(E, F)) := by
  obtain ⟨u, hu⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hf
  have : MemLp (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 := by
    constructor
    · have : (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
        fun_prop
      exact this.1.continuous.aestronglyMeasurable
    · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
      suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
        norm_cast
        simp_rw [ofReal_norm] at h
        simp_rw [← enorm_pow]
        convert h
        rw [← Real.rpow_mul_natCast (by positivity)]
        simp
      apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
      congr
      ring
  have : MemLp (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)) 2 := this.ofReal
  use this.toLp • u
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq]
  · rw [← hu, smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert! (smulLeftCLM_const 1 (𝓕 f)).symm using 1
    · simp
    · congr
      ext x
      rw [Pi.mul_apply]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      ring_nf
      simp
  · fun_prop

open scoped BoundedContinuousFunction

/-- The Fourier multiplier with a bounded function maps `H ^ s` to `H ^ s`. -/
/-
**TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded** 是 Mathlib 中的
一个定理，位于命名空间 `TemperedDistribution.MemSobolev`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedAddCommGroup F]   [inst_2 : InnerProductSpace ℝ E] [inst_3 : FiniteDimension
al ℝ E] [inst_4 : MeasurableSpace E] [inst_5 : BorelSpace E]   [inst_6 : InnerPr
oductSpace ℂ F] [inst_7 : CompleteSpace F] {s : ℝ} {f : TemperedDistribution E F
},   TemperedDistribution.MemSobolev s 2 f →     ∀ {g : E → ℂ},       Function.H
asTemperateGrowth g →         (∃ C, ∀ (x : E), ‖g x‖ ≤ C) →           TemperedDi
stribution.MemSobolev s 2 ((TemperedDistribution.fourierMultiplierCLM F g) f)
参数：∃ C, ∀ (x : E), ‖g x‖ ≤ C；(TemperedDistribution.fourierMultiplierCLM F g) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier`：memSobol
ev_iff_exists_smulLeftCLM_fourier {s : Real} {f : 𝓢'(E, F)} : MemSobolev s 2 f ↔
 exists (f' : Lp F 2 (volume : Measure E)), smulLeft…
· 使用定理 `ContDiff.continuous`：ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuo
us f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `BoundedContinuousFunction.memLp_top`：memLp_top (f : α ->ᵇ E) : MemLp f ⊤
 μ
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `MeasureTheory.Lp.toTemperedDistribution_smul_eq`：∀ {E : Type u_3} {F : T
ype u_4} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : Norm
edAddCommGroup F]   [inst_3 : NormedS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TemperedDistribution.fourierMultiplierCLM_apply`：fourierMultiplierCLM_ap
ply (g : E -> Complex) (f : 𝓢'(E, F)) : fourierMultiplierCLM F g f = 𝓕⁻ (smulLef
tCLM F g (𝓕 f))
· 使用定理 `FourierInvPair.fourier_fourierInv_eq`：∀ {E : Type u_5} {F : Type u_6} {i
nst : FourierTransform F E} {inst_1 : FourierTransformInv E F}   [self : Fourier
InvPair E F] (f : E), Four…
· 使用定理 `TemperedDistribution.smulLeftCLM_smulLeftCLM_apply`：smulLeftCLM_smulLeft
CLM_apply {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemp
erateGrowth) (f : 𝓢'(E, F)) : smulLeftCL…
· 使用定理 `Function.HasTemperateGrowth.comp`：∀ {D : Type u_4} {E : Type u_5} {F : T
ype u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : No
rmedAddCommGroup F] [i…
· 使用定理 `Function.Complex.hasTemperateGrowth_ofReal`：Function.HasTemperateGrowth 
Complex.ofReal
· 使用定理 `Function.hasTemperateGrowth_one_add_norm_sq_rpow`：hasTemperateGrowth_one
_add_norm_sq_rpow (r : Real) : (fun (x : H) => (1 + ‖x‖ ^ 2) ^ r).HasTemperateGr
owth
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
The Fourier multiplier with a bounded function maps `H ^ s` to `H ^ s`.
-/
theorem MemSobolev.fourierMultiplierCLM_of_bounded {s : ℝ} {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) {g : E → ℂ} (hg₁ : g.HasTemperateGrowth) (hg₂ : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    MemSobolev s 2 (fourierMultiplierCLM F g f) := by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier] at hf ⊢
  obtain ⟨f', hf⟩ := hf
  obtain ⟨C, hC⟩ := hg₂
  set g' : E →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup g hg₁.1.continuous C hC
  use (g'.memLp_top.toLp _ (μ := volume)) • f'
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq (by apply hg₁), ← hf,
    fourierMultiplierCLM_apply, fourier_fourierInv_eq,
    smulLeftCLM_smulLeftCLM_apply hg₁ (by fun_prop),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by apply hg₁)]
  congr 2
  ext x
  rw [mul_comm]
  congr
/-
**TemperedDistribution.MemSobolev.mono** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDistri
bution.MemSobolev`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedAddCommGroup F]   [inst_2 : InnerProductSpace ℝ E] [inst_3 : FiniteDimension
al ℝ E] [inst_4 : MeasurableSpace E] [inst_5 : BorelSpace E]   [inst_6 : InnerPr
oductSpace ℂ F] [inst_7 : CompleteSpace F] {s s' : ℝ},   s' ≤ s →     ∀ {f : Tem
peredDistribution E F}, TemperedDistribution.MemSobolev s 2 f → TemperedDistribu
tion.MemSobolev s' 2 f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
（共 67 条，此处仅展示前 30 条）
-/
theorem MemSobolev.mono {s s' : ℝ} (h : s' ≤ s) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
    MemSobolev s' 2 f := by
  have h' : (s' - s) / 2 ≤ 0 := by
    rw [div_le_iff₀ (by norm_num)]
    simp [h]
  have hs : s' = (s' - s) + s := by ring
  rw [hs, ← memSobolev_besselPotential_iff]
  apply hf.fourierMultiplierCLM_of_bounded (by fun_prop)
  use 1
  intro x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) h'

section LineDeriv

open scoped LineDeriv Laplacian Real

/-- The directional derivative maps `H ^ s` to `H ^ {s - 1}`. -/
/-
**TemperedDistribution.MemSobolev.lineDerivOp** 是 Mathlib 中的一个定理，位于命名空间 `Tempere
dDistribution.MemSobolev`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedAddCommGroup F]   [inst_2 : InnerProductSpace ℝ E] [inst_3 : FiniteDimension
al ℝ E] [inst_4 : MeasurableSpace E] [inst_5 : BorelSpace E]   [inst_6 : InnerPr
oductSpace ℂ F] [inst_7 : CompleteSpace F] {s : ℝ} {f : TemperedDistribution E F
},   TemperedDistribution.MemSobolev s 2 f →     ∀ {m : E}, TemperedDistribution
.MemSobolev (s - 1) 2 (LineDeriv.lineDerivOp m f)
参数：s - 1；LineDeriv.lineDerivOp m f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubNegMonoid.sub_eq_add_neg`：∀ {G : Type u} [self : SubNegMonoid G] (a b
 : G), a - b = a + -b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TemperedDistribution.memSobolev_besselPotential_iff`：memSobolev_besselPo
tential_iff {s r : Real} {p : Real>=0∞} [hp : Fact (1 <= p)] {f : 𝓢'(E, F)} : Me
mSobolev s p (besselPotential E F r f) ↔ …
· 使用定理 `TemperedDistribution.besselPotential_neg_one_lineDerivOp_eq`：besselPoten
tial_neg_one_lineDerivOp_eq {m : E} (f : 𝓢'(E, F)) : (besselPotential E F (-1)) 
(∂_{m} f) = (2 * π * Complex.I) • fourierMultipli…
· 使用定理 `TemperedDistribution.MemSobolev.smul`：∀ {E : Type u_1} {F : Type u_2} [i
nst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F]   [inst_2 : InnerPro
ductSpace ℝ E] [inst_3 : F…
· 使用定理 `TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded`：∀ {E : 
Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGr
oup F]   [inst_2 : InnerProductSpace ℝ E] [inst_3 : F…
· 使用定理 `Function.HasTemperateGrowth.comp`：∀ {D : Type u_4} {E : Type u_5} {F : T
ype u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : No
rmedAddCommGroup F] [i…
· 使用定理 `Function.Complex.hasTemperateGrowth_ofReal`：Function.HasTemperateGrowth 
Complex.ofReal
· 使用定理 `Function.HasTemperateGrowth.fun_mul`：∀ {R : Type u_3} {E : Type u_5} [in
st : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedRing R]   
[inst_3 : NormedAlgebra ℝ…
· 使用定理 `Function.hasTemperateGrowth_inner_left`：hasTemperateGrowth_inner_left (c
 : H) : (inner Real · c).HasTemperateGrowth
· 使用定理 `Function.hasTemperateGrowth_one_add_norm_sq_rpow`：hasTemperateGrowth_one
_add_norm_sq_rpow (r : Real) : (fun (x : H) => (1 + ‖x‖ ^ 2) ^ r).HasTemperateGr
owth
· 使用定理 `le_of_sq_le_sq`：le_of_sq_le_sq (h : a ^ 2 <= b ^ 2) (hb : 0 <= b) : a <=
 b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
（共 111 条，此处仅展示前 30 条）

--- 原说明 ---
The directional derivative maps `H ^ s` to `H ^ {s - 1}`.
-/
theorem MemSobolev.lineDerivOp {s : ℝ} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) {m : E} :
    MemSobolev (s - 1) 2 (∂_{m} f) := by
  rw [SubNegMonoid.sub_eq_add_neg s 1, add_comm, ← memSobolev_besselPotential_iff,
    besselPotential_neg_one_lineDerivOp_eq f]
  apply (hf.fourierMultiplierCLM_of_bounded (by fun_prop) ?_).smul
  use ‖m‖
  intro x
  apply le_of_sq_le_sq _ (by positivity)
  simp only [Complex.ofReal_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have h₁ : |(1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)| ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
    field_simp
    norm_cast
    rw [Real.rpow_neg (by positivity), sq_abs, inv_pow]
    field_simp
    calc
      _ = ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]; simp
      _ = _ := by simp
  have h₂ : |inner ℝ x m| ^ 2 ≤ ‖m‖ ^ 2 * (1 + ‖x‖ ^ 2) := by
    grw [abs_real_inner_le_norm]
    rw [mul_pow, mul_comm]
    gcongr
    simp
  grw [h₁, h₂]
  apply le_of_eq
  field_simp

/-- The Laplacian maps `H ^ s` to `H ^ {s - 2}`. -/
/-
**TemperedDistribution.MemSobolev.laplacian** 是 Mathlib 中的一个定理，位于命名空间 `TemperedD
istribution.MemSobolev`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedAddCommGroup F]   [inst_2 : InnerProductSpace ℝ E] [inst_3 : FiniteDimension
al ℝ E] [inst_4 : MeasurableSpace E] [inst_5 : BorelSpace E]   [inst_6 : InnerPr
oductSpace ℂ F] [inst_7 : CompleteSpace F] {s : ℝ} {f : TemperedDistribution E F
},   TemperedDistribution.MemSobolev s 2 f → TemperedDistribution.MemSobolev (s 
- 2) 2 (Laplacian.laplacian f)
参数：s - 2；Laplacian.laplacian f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubNegMonoid.sub_eq_add_neg`：∀ {G : Type u} [self : SubNegMonoid G] (a b
 : G), a - b = a + -b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TemperedDistribution.memSobolev_besselPotential_iff`：memSobolev_besselPo
tential_iff {s r : Real} {p : Real>=0∞} [hp : Fact (1 <= p)] {f : 𝓢'(E, F)} : Me
mSobolev s p (besselPotential E F r f) ↔ …
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `TemperedDistribution.besselPotential_neg_two_laplacian_eq`：besselPotenti
al_neg_two_laplacian_eq (f : 𝓢'(E, F)) : (besselPotential E F (-2)) (Δ f) = -(2 
* π) ^ 2 • fourierMultiplierCLM F (fun x => Com…
· 使用定理 `TemperedDistribution.MemSobolev.smul`：∀ {E : Type u_1} {F : Type u_2} [i
nst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F]   [inst_2 : InnerPro
ductSpace ℝ E] [inst_3 : F…
· 使用定理 `TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded`：∀ {E : 
Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGr
oup F]   [inst_2 : InnerProductSpace ℝ E] [inst_3 : F…
· 使用定理 `Function.HasTemperateGrowth.comp`：∀ {D : Type u_4} {E : Type u_5} {F : T
ype u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : No
rmedAddCommGroup F] [i…
· 使用定理 `Function.Complex.hasTemperateGrowth_ofReal`：Function.HasTemperateGrowth 
Complex.ofReal
· 使用定理 `Function.HasTemperateGrowth.fun_mul`：∀ {R : Type u_3} {E : Type u_5} [in
st : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedRing R]   
[inst_3 : NormedAlgebra ℝ…
· 使用定理 `Function.hasTemperateGrowth_norm_sq`：hasTemperateGrowth_norm_sq : (fun (
x : H) => ‖x‖ ^ 2).HasTemperateGrowth
· 使用定理 `Function.hasTemperateGrowth_one_add_norm_sq_rpow`：hasTemperateGrowth_one
_add_norm_sq_rpow (r : Real) : (fun (x : H) => (1 + ‖x‖ ^ 2) ^ r).HasTemperateGr
owth
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
The Laplacian maps `H ^ s` to `H ^ {s - 2}`.
-/
theorem MemSobolev.laplacian {s : ℝ} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
    MemSobolev (s - 2) 2 (Δ f) := by
  rw [SubNegMonoid.sub_eq_add_neg s 2, add_comm, ← memSobolev_besselPotential_iff,
    besselPotential_neg_two_laplacian_eq f]
  apply (hf.fourierMultiplierCLM_of_bounded (by fun_prop) ?_).smul
  use 1
  intro x
  rw [Real.rpow_neg (by positivity)]
  norm_cast
  simp only [norm_mul, norm_pow, abs_norm, norm_inv, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), mul_inv_le_iff₀ (by positivity)]
  grind

end LineDeriv

end inner

end TemperedDistribution

