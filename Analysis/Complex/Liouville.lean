/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# Liouville's theorem

In this file we prove Liouville's theorem: if `f : E → F` is complex differentiable on the whole
space and its range is bounded, then the function is a constant. Various versions of this theorem
are formalized in `Differentiable.apply_eq_apply_of_bounded`,
`Differentiable.exists_const_forall_eq_of_bounded`, and
`Differentiable.exists_eq_const_of_bounded`.

The proof is based on the Cauchy integral formula for the derivative of an analytic function, see
`Complex.deriv_eq_smul_circleIntegral`.
-/

public section

open TopologicalSpace Metric Set Filter Asymptotics Function MeasureTheory Bornology

open scoped Topology Filter NNReal Real

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : Type v} [NormedAddCommGroup F]
  [NormedSpace ℂ F]

local postfix:100 "̂" => UniformSpace.Completion

namespace Complex

/-- **Cauchy's estimate for derivatives**:  If `f` is complex differentiable on an open disc of
radius `R > 0`, is continuous on its closure, and its values on the boundary circle of this disc
are bounded from above by `C`, then the norm of its `n`-th derivative at the center is at most
`n.factorial * C / R ^ n`. -/
/-
**Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le** 是 Mathlib 中的一个定理，
位于命名空间 `Complex`。
形式化陈述：norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le [CompleteSpace F] {c : 
Complex} {R C : Real} {f : Complex -> F} (n : Nat) (hR : 0 < R) (hf : DiffContOn
Cl Complex f (ball c R)) (hC : forall z in sphere c R, ‖f z‖ <= C) : ‖iteratedDe
riv n f c‖ <= n.factorial * C / R ^ n
参数：n : Nat；hR : 0 < R；hf : DiffContOnCl Complex f (ball c R)；hC : forall z in sp
here c R, ‖f z‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_sphere_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] 
{a b : E} {r : ℝ}, b ∈ Metric.sphere a r ↔ ‖b - a‖ = r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `div_le_div_iff_of_pos_right`：div_le_div_iff_of_pos_right (hc : 0 < c) : 
a / c <= b / c ↔ a <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
**Cauchy's estimate for derivatives**:  If `f` is complex differentiable on an o
pen disc of
radius `R > 0`, is continuous on its closure, and its values on the boundary cir
cle of this disc
are bounded from above by `C`, then the norm of its `n`-th derivative at the cen
ter is at most
`n.factorial * C / R ^ n`.
-/
theorem norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le [CompleteSpace F] {c : ℂ} {R C : ℝ}
    {f : ℂ → F} (n : ℕ) (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R))
    (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖iteratedDeriv n f c‖ ≤ n.factorial * C / R ^ n := by
  have hp (z) (hz : z ∈ sphere c R) : ‖(z - c)⁻¹ ^ (n + 1) • f z‖ ≤ C / (R ^ n * R) := by
    simpa [norm_smul, norm_pow, norm_inv, ← div_eq_inv_mul, mem_sphere_iff_norm.1 hz] using!
      (div_le_div_iff_of_pos_right (mul_pos (pow_pos hR n) hR)).2 (hC z hz)
  have hq : iteratedDeriv n f c = n.factorial • (2 * π * I)⁻¹ •
    ∮ z in C(c, R), (z - c)⁻¹ ^ (n + 1) • f z := by
    have : (2 * π * I / n.factorial) ≠ 0 := by simp [Nat.factorial_ne_zero]
    rw [← inv_smul_smul₀ this (iteratedDeriv n f c), inv_div, div_eq_inv_mul, mul_comm,
      ← nsmul_eq_mul, smul_assoc]
    simp [← DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul hR n hf]
  calc
    ‖iteratedDeriv n f c‖ = ‖n.factorial • (2 * π * I)⁻¹ •
      ∮ z in C(c, R), (z - c)⁻¹ ^ (n + 1) • f z‖ := by rw [hq]
    _ ≤ n.factorial * (R * (C / (R ^ (n + 1)))) := by
      rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul, mul_le_mul_iff_right₀ (by positivity)]
      exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hp
    _ = n.factorial * C / R ^ n := by
      grind
/-
**Complex.norm_deriv_le_aux** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem norm_deriv_le_aux [CompleteSpace F] {c : ℂ} {R C : ℝ} {f : ℂ → F} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖deriv f c‖ ≤ C / R := by
  simpa using norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hR hf hC

/-- **Cauchy's estimate for the first order derivative**: If `f` is complex differentiable on an
open disc of radius `R > 0`, is continuous on its closure, and its values on the boundary circle
of this disc are bounded from above by `C`, then the norm of its derivative at the center is at
most `C / R`. Note that this theorem does not require the completeness of the codomain of `f`. In
contrast, the completeness is needed for `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`. -/
/-
**Complex.norm_deriv_le_of_forall_mem_sphere_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `
Complex`。
形式化陈述：norm_deriv_le_of_forall_mem_sphere_norm_le {c : Complex} {R C : Real} {f :
 Complex -> F} (hR : 0 < R) (hd : DiffContOnCl Complex f (ball c R)) (hC : foral
l z in sphere c R, ‖f z‖ <= C) : ‖deriv f c‖ <= C / R
参数：hR : 0 < R；hd : DiffContOnCl Complex f (ball c R)；hC : forall z in sphere c R
, ‖f z‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `UniformSpace.Completion.instIsBoundedSMul`：∀ {α : Type u} [inst : Pseudo
MetricSpace α] {M : Type u_1} [inst_1 : Zero M] [inst_2 : Zero α] [inst_3 : SMul
 M α]   [inst_4 : PseudoMetricS…
· 使用定理 `HasFDerivAt.comp_hasDerivAt`：HasFDerivAt.comp_hasDerivAt (hl : HasFDeriv
At l l' (f x)) (hf : HasDerivAt f f' x) : HasDerivAt (l ∘ f) (l' f') x
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `DiffContOnCl.differentiableAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniformSpace.Completion.norm_coe`：norm_coe {E} [SeminormedAddCommGroup E
] (x : E) : ‖(x : Completion E)‖ = ‖x‖
· 使用定理 `_private.Mathlib.Analysis.Complex.Liouville.0.Complex.norm_deriv_le_aux`
：∀ {F : Type v} [inst : NormedAddCommGroup F] [inst_1 : NormedSpace ℂ F] [Comple
teSpace F] {c : ℂ} {R C : ℝ} {f : ℂ → F},   0 < R → DiffContO…
· 使用定理 `Differentiable.comp_diffContOnCl`：Differentiable.comp_diffContOnCl {g : 
G -> E} {t : Set G} (hf : Differentiable 𝕜 f) (hg : DiffContOnCl 𝕜 g t) : DiffCo
ntOnCl 𝕜 (f ∘ g) t
· 使用定理 `ContinuousLinearMap.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c

--- 原说明 ---
**Cauchy's estimate for the first order derivative**: If `f` is complex differen
tiable on an
open disc of radius `R > 0`, is continuous on its closure, and its values on the
 boundary circle
of this disc are bounded from above by `C`, then the norm of its derivative at t
he center is at
most `C / R`. Note that this theorem does not require the completeness of the co
domain of `f`. In
contrast, the completeness is needed for `norm_iteratedDeriv_le_of_forall_mem_sp
here_norm_le`.
-/
theorem norm_deriv_le_of_forall_mem_sphere_norm_le {c : ℂ} {R C : ℝ} {f : ℂ → F} (hR : 0 < R)
    (hd : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖deriv f c‖ ≤ C / R := by
  set e : F →L[ℂ] F̂ := UniformSpace.Completion.toComplL
  have : HasDerivAt (e ∘ f) (e (deriv f c)) c :=
    e.hasFDerivAt.comp_hasDerivAt c
      (hd.differentiableAt isOpen_ball <| mem_ball_self hR).hasDerivAt
  calc
    ‖deriv f c‖ = ‖deriv (e ∘ f) c‖ := by
      rw [this.deriv]
      exact (UniformSpace.Completion.norm_coe _).symm
    _ ≤ C / R :=
      norm_deriv_le_aux hR (e.differentiable.comp_diffContOnCl hd) fun z hz =>
        (UniformSpace.Completion.norm_coe _).trans_le (hC z hz)

/-- An auxiliary lemma for Liouville's theorem `Differentiable.apply_eq_apply_of_bounded`. -/
/-
**Complex.liouville_theorem_aux** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：liouville_theorem_aux {f : Complex -> F} (hf : Differentiable Complex f) (
hb : IsBounded (range f)) (z w : Complex) : f z = f w
参数：hf : Differentiable Complex f；hb : IsBounded (range f)；z w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isBounded_iff_forall_norm_le`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] {s : Set E}, Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_max_iff`：lt_max_iff : a < max b c ↔ a < b ∨ a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `le_of_forall_gt_imp_ge_of_dense`：le_of_forall_gt_imp_ge_of_dense (h : fo
rall a, a₂ < a -> a₁ <= a) : a₁ <= a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`：norm_deriv_le_of_for
all_mem_sphere_norm_le {c : Complex} {R C : Real} {f : Complex -> F} (hR : 0 < R
) (hd : DiffContOnCl Complex f (ball c R…
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `Differentiable.diffContOnCl`：Differentiable.diffContOnCl (h : Differenti
able 𝕜 f) : DiffContOnCl 𝕜 f s
· 使用定理 `div_div_cancel₀`：∀ {G₀ : Type u_3} [inst : CommGroupWithZero G₀] {a b : 
G₀}, a ≠ 0 → a / (a / b) = b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a
· 使用定理 `is_const_of_deriv_eq_zero`：∀ {𝕜 : Type u_3} {G : Type u_4} [inst : RCLik
e 𝕜] [inst_1 : NormedAddCommGroup G] [inst_2 : NormedSpace 𝕜 G]   {f : 𝕜 → G}, D
ifferentiable 𝕜…

--- 原说明 ---
An auxiliary lemma for Liouville's theorem `Differentiable.apply_eq_apply_of_bou
nded`.
-/
theorem liouville_theorem_aux {f : ℂ → F} (hf : Differentiable ℂ f) (hb : IsBounded (range f))
    (z w : ℂ) : f z = f w := by
  suffices ∀ c, deriv f c = 0 from is_const_of_deriv_eq_zero hf this z w
  clear z w; intro c
  obtain ⟨C, C₀, hC⟩ : ∃ C > (0 : ℝ), ∀ z, ‖f z‖ ≤ C := by
    rcases isBounded_iff_forall_norm_le.1 hb with ⟨C, hC⟩
    exact
      ⟨max C 1, lt_max_iff.2 (Or.inr zero_lt_one), fun z =>
        (hC (f z) (mem_range_self _)).trans (le_max_left _ _)⟩
  refine norm_le_zero_iff.1 (le_of_forall_gt_imp_ge_of_dense fun ε ε₀ => ?_)
  calc
    ‖deriv f c‖ ≤ C / (C / ε) :=
      norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos C₀ ε₀) hf.diffContOnCl fun z _ => hC z
    _ = ε := div_div_cancel₀ C₀.lt.ne'

end Complex

namespace Differentiable

open Complex

/-- **Liouville's theorem**: a complex differentiable bounded function `f : E → F` is a constant. -/
/-
**Differentiable.apply_eq_apply_of_bounded** 是 Mathlib 中的一个定理，位于命名空间 `Differenti
able`。
形式化陈述：apply_eq_apply_of_bounded {f : E -> F} (hf : Differentiable Complex f) (hb
 : IsBounded (range f)) (z w : E) : f z = f w
参数：hf : Differentiable Complex f；hb : IsBounded (range f)；z w : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.liouville_theorem_aux`：liouville_theorem_aux {f : Complex -> F} 
(hf : Differentiable Complex f) (hb : IsBounded (range f)) (z w : Complex) : f z
 = f w
· 使用定理 `Differentiable.comp`：Differentiable.comp {g : F -> G} (hg : Differentiab
le 𝕜 g) (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (g ∘ f)
· 使用定理 `Differentiable.add_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `Differentiable.smul_const`：Differentiable.smul_const (hc : Differentiabl
e 𝕜 c) (f : F) : Differentiable 𝕜 fun y => c y • f
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a

--- 原说明 ---
**Liouville's theorem**: a complex differentiable bounded function `f : E → F` i
s a constant.
-/
theorem apply_eq_apply_of_bounded {f : E → F} (hf : Differentiable ℂ f) (hb : IsBounded (range f))
    (z w : E) : f z = f w := by
  set g : ℂ → F := f ∘ fun t : ℂ => t • (w - z) + z
  suffices g 0 = g 1 by simpa [g]
  apply liouville_theorem_aux
  exacts [hf.comp ((differentiable_id.smul_const (w - z)).add_const z),
    hb.subset (range_comp_subset_range _ _)]

/-- **Liouville's theorem**: a complex differentiable bounded function is a constant. -/
/-
**Differentiable.exists_const_forall_eq_of_bounded** 是 Mathlib 中的一个定理，位于命名空间 `Di
fferentiable`。
形式化陈述：exists_const_forall_eq_of_bounded {f : E -> F} (hf : Differentiable Comple
x f) (hb : IsBounded (range f)) : exists c, forall z, f z = c
参数：hf : Differentiable Complex f；hb : IsBounded (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.apply_eq_apply_of_bounded`：apply_eq_apply_of_bounded {f :
 E -> F} (hf : Differentiable Complex f) (hb : IsBounded (range f)) (z w : E) : 
f z = f w

--- 原说明 ---
**Liouville's theorem**: a complex differentiable bounded function is a constant
.
-/
theorem exists_const_forall_eq_of_bounded {f : E → F} (hf : Differentiable ℂ f)
    (hb : IsBounded (range f)) : ∃ c, ∀ z, f z = c :=
  ⟨f 0, fun _ => hf.apply_eq_apply_of_bounded hb _ _⟩

/-- **Liouville's theorem**: a complex differentiable bounded function is a constant. -/
/-
**Differentiable.exists_eq_const_of_bounded** 是 Mathlib 中的一个定理，位于命名空间 `Different
iable`。
形式化陈述：exists_eq_const_of_bounded {f : E -> F} (hf : Differentiable Complex f) (h
b : IsBounded (range f)) : exists c, f = const E c
参数：hf : Differentiable Complex f；hb : IsBounded (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Differentiable.exists_const_forall_eq_of_bounded`：exists_const_forall_eq
_of_bounded {f : E -> F} (hf : Differentiable Complex f) (hb : IsBounded (range 
f)) : exists c, forall z, f z = c

--- 原说明 ---
**Liouville's theorem**: a complex differentiable bounded function is a constant
.
-/
theorem exists_eq_const_of_bounded {f : E → F} (hf : Differentiable ℂ f)
    (hb : IsBounded (range f)) : ∃ c, f = const E c :=
  (hf.exists_const_forall_eq_of_bounded hb).imp fun _ => funext

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- A corollary of Liouville's theorem where the function tends to a finite value at infinity
(i.e., along `Filter.cocompact`, which in proper spaces coincides with `Bornology.cobounded`). -/
/-
**Differentiable.eq_const_of_tendsto_cocompact** 是 Mathlib 中的一个定理，位于命名空间 `Differ
entiable`。
形式化陈述：eq_const_of_tendsto_cocompact [Nontrivial E] {f : E -> F} (hf : Differenti
able Complex f) {c : F} (hb : Tendsto f (cocompact E) (𝓝 c)) : f = Function.cons
t E c
参数：hf : Differentiable Complex f；hb : Tendsto f (cocompact E) (𝓝 c)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.exists_isBounded_image_of_tendsto`：exists_isBounded_image_of_tend
sto {α β : Type*} [PseudoMetricSpace β] {l : Filter α} {f : α -> β} {x : β} (hf 
: Tendsto f l (𝓝 x)) : exists …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_cocompact`：mem_cocompact : s in cocompact X ↔ exists t, IsCom
pact t ∧ tᶜ subseteq s
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Bornology.IsBounded.union`：∀ {α : Type u_2} {x : Bornology α} {s t : Set
 α},   Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s ∪ 
t)
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Differentiable.exists_eq_const_of_bounded`：exists_eq_const_of_bounded {f
 : E -> F} (hf : Differentiable Complex f) (hb : IsBounded (range f)) : exists c
, f = const E c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instNeBotCocompactOfNoncompactSpace`：∀ {X : Type u} [inst : TopologicalS
pace X] [NoncompactSpace X], (Filter.cocompact X).NeBot
· 使用定理 `RealNormedSpace.noncompactSpace`：∀ (E : Type u_3) [inst : NormedAddCommG
roup E] [Nontrivial E] [NormedSpace ℝ E], NoncompactSpace E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)

--- 原说明 ---
A corollary of Liouville's theorem where the function tends to a finite value at
 infinity
(i.e., along `Filter.cocompact`, which in proper spaces coincides with `Bornolog
y.cobounded`).
-/
theorem eq_const_of_tendsto_cocompact [Nontrivial E] {f : E → F} (hf : Differentiable ℂ f) {c : F}
    (hb : Tendsto f (cocompact E) (𝓝 c)) : f = Function.const E c := by
  have h_bdd : Bornology.IsBounded (Set.range f) := by
    obtain ⟨s, hs, hs_bdd⟩ := Metric.exists_isBounded_image_of_tendsto hb
    obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
    apply ht.image hf.continuous |>.isBounded.union hs_bdd |>.subset
    simpa [Set.image_union, Set.image_univ] using! Set.image_mono <| calc
      Set.univ = t ∪ tᶜ := t.union_compl_self.symm
      _        ⊆ t ∪ s  := by gcongr
  obtain ⟨c', hc'⟩ := hf.exists_eq_const_of_bounded h_bdd
  convert hc'
  exact tendsto_nhds_unique hb (by simpa [hc'] using! tendsto_const_nhds)

/-- A corollary of Liouville's theorem where the function tends to a finite value at infinity
(i.e., along `Filter.cocompact`, which in proper spaces coincides with `Bornology.cobounded`). -/
/-
**Differentiable.apply_eq_of_tendsto_cocompact** 是 Mathlib 中的一个定理，位于命名空间 `Differ
entiable`。
形式化陈述：apply_eq_of_tendsto_cocompact [Nontrivial E] {f : E -> F} (hf : Differenti
able Complex f) {c : F} (x : E) (hb : Tendsto f (cocompact E) (𝓝 c)) : f x = c
参数：hf : Differentiable Complex f；x : E；hb : Tendsto f (cocompact E) (𝓝 c)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Differentiable.eq_const_of_tendsto_cocompact`：eq_const_of_tendsto_cocomp
act [Nontrivial E] {f : E -> F} (hf : Differentiable Complex f) {c : F} (hb : Te
ndsto f (cocompact E) (𝓝 c)) : f =…

--- 原说明 ---
A corollary of Liouville's theorem where the function tends to a finite value at
 infinity
(i.e., along `Filter.cocompact`, which in proper spaces coincides with `Bornolog
y.cobounded`).
-/
theorem apply_eq_of_tendsto_cocompact [Nontrivial E] {f : E → F} (hf : Differentiable ℂ f) {c : F}
    (x : E) (hb : Tendsto f (cocompact E) (𝓝 c)) : f x = c :=
  congr($(hf.eq_const_of_tendsto_cocompact hb) x)

end Differentiable

