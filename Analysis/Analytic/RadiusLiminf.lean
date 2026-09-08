/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Representation of `FormalMultilinearSeries.radius` as a `liminf`

In this file we prove that the radius of convergence of a `FormalMultilinearSeries` is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. This lemma can't go to `Analysis.Analytic.Basic`
because this would create a circular dependency once we redefine `exp` using
`FormalMultilinearSeries`.
-/

public section


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open scoped Topology NNReal ENNReal

open Filter Asymptotics

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F)

/-- The radius of a formal multilinear series is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. The actual statement uses `ℝ≥0` and some
coercions. -/
/-
**FormalMultilinearSeries.radius_eq_liminf** 是 Mathlib 中的一个定理，位于命名空间 `FormalMult
ilinearSeries`。
形式化陈述：radius_eq_liminf : p.radius = liminf (fun n => (1 / (‖p n‖₊ ^ (1 / (n : Re
al)) : Real>=0) : Real>=0∞)) atTop
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.le_inv_iff_mul_le`：le_inv_iff_mul_le : a <= b⁻¹ ↔ a * b <= 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `ENNReal.coe_le_one_iff`：coe_le_one_iff : ↑r <= (1 : Real>=0∞) ↔ r <= 1
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用定理 `NNReal.mul_rpow`：mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^
 z * y ^ z
· 使用定理 `NNReal.one_rpow`：one_rpow (x : Real) : (1 : Real>=0) ^ x = 1
· 使用定理 `NNReal.rpow_le_rpow_iff`：rpow_le_rpow_iff {x y : Real>=0} {z : Real} (hz
 : 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `NNReal.rpow_natCast`：rpow_natCast (x : Real>=0) (n : Nat) : x ^ (n : Rea
l) = x ^ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ENNReal.le_of_forall_nnreal_lt`：le_of_forall_nnreal_lt {x y : Real>=0∞} 
(h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
The radius of a formal multilinear series is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. The actual statement uses `ℝ≥0
` and some
coercions.
-/
theorem radius_eq_liminf :
    p.radius = liminf (fun n => (1 / (‖p n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop := by
  have :
    ∀ (r : ℝ≥0) {n},
      0 < n → ((r : ℝ≥0∞) ≤ 1 / ↑(‖p n‖₊ ^ (1 / (n : ℝ))) ↔ ‖p n‖₊ * r ^ n ≤ 1) := by
    intro r n hn
    have : 0 < (n : ℝ) := Nat.cast_pos.2 hn
    conv_lhs =>
      rw [one_div, ENNReal.le_inv_iff_mul_le, ← ENNReal.coe_mul, ENNReal.coe_le_one_iff, one_div, ←
        NNReal.rpow_one r, ← mul_inv_cancel₀ this.ne', NNReal.rpow_mul, ← NNReal.mul_rpow, ←
        NNReal.one_rpow n⁻¹, NNReal.rpow_le_rpow_iff (inv_pos.2 this), mul_comm,
        NNReal.rpow_natCast]
  apply le_antisymm <;> refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  · have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * r ^ n) 1).out 1 7).1
      (p.isLittleO_of_lt_radius hr)
    obtain ⟨a, ha, H⟩ := this
    apply le_liminf_of_le
    · infer_param
    · rw [← eventually_map]
      refine
        H.mp ((eventually_gt_atTop 0).mono fun n hn₀ hn => (this _ hn₀).2 (NNReal.coe_le_coe.1 ?_))
      push_cast
      exact (le_abs_self _).trans (hn.trans (pow_le_one₀ ha.1.le ha.2.le))
  · refine p.le_radius_of_isBigO <| .of_norm_eventuallyLE ?_
    filter_upwards [eventually_lt_of_lt_liminf hr, eventually_gt_atTop 0] with n hn hn₀
    simpa using NNReal.coe_le_coe.2 ((this _ hn₀).1 hn.le)

/-- The **Cauchy-Hadamard theorem** for formal multilinear series: The inverse of the radius
is equal to $\limsup_{n\to\infty} \sqrt[n]{‖p n‖}$. -/
/-
**FormalMultilinearSeries.radius_inv_eq_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Formal
MultilinearSeries`。
形式化陈述：radius_inv_eq_limsup : p.radius⁻¹ = limsup (fun n => ((‖p n‖₊ ^ (1 / (n : 
Real)) : Real>=0) : Real>=0∞)) atTop
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.inv_liminf`：inv_liminf {ι : Sort _} {x : ι -> Real>=0∞} {l : Fil
ter ι} : (liminf x l)⁻¹ = limsup (fun i => (x i)⁻¹) l
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `FormalMultilinearSeries.radius_eq_liminf`：radius_eq_liminf : p.radius = 
liminf (fun n => (1 / (‖p n‖₊ ^ (1 / (n : Real)) : Real>=0) : Real>=0∞)) atTop

--- 原说明 ---
The **Cauchy-Hadamard theorem** for formal multilinear series: The inverse of th
e radius
is equal to $\limsup_{n\to\infty} \sqrt[n]{‖p n‖}$.
-/
theorem radius_inv_eq_limsup :
    p.radius⁻¹ = limsup (fun n ↦ ((‖p n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop := by
  simpa [ENNReal.inv_liminf] using congr($(p.radius_eq_liminf)⁻¹)

end FormalMultilinearSeries

