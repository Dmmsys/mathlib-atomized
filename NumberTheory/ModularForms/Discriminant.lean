/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Analysis.Normed.Ring.InfiniteProd
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The modular discriminant Δ

This file defines the modular discriminant `Δ(z) = η(z) ^ 24`, where `η` is the Dedekind eta
function, and proves its key properties including invariance under the generators of `SL(2, ℤ)`.

## Main definitions

* `ModularForm.discriminant`: The modular discriminant function `Δ(z) = η(z) ^ 24`, which can also
  be expressed as `q * ∏' (1 - q ^ (n + 1)) ^ 24` where `q = e ^ (2πiz)`.

## Main results

* `ModularForm.discriminant_ne_zero`: The discriminant is non-vanishing on the upper half-plane.
* `ModularForm.discriminant_T_invariant`: Invariance under the translation `T : z ↦ z + 1`.
* `ModularForm.discriminant_S_invariant`: Invariance under the inversion `S : z ↦ -1 / z`,
  showing `Δ(-1 / z) = z ^ 12 · Δ(z)`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], section 1.2
-/

open Function Complex SlashInvariantForm MatrixGroups Filter

open UpperHalfPlane hiding I

open scoped Real Topology

noncomputable section

namespace ModularForm

/-- The modular discriminant `Δ(z) = η(z) ^ 24`, where `η` is the Dedekind eta function. -/
@[expose] public def discriminant (z : ℍ) := (eta z) ^ 24

local notation "Δ" => discriminant

local notation "𝕢" => Periodic.qParam

section auxiliary

/-
**ModularForm.csqrt_pow_24_eq** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：csqrt_pow_24_eq {z : Complex} (hz : z != 0) : sqrt z ^ 24 = z ^ 12
参数：hz : z != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma csqrt_pow_24_eq {z : ℂ} (hz : z ≠ 0) : sqrt z ^ 24 = z ^ 12 := by
  rw [sqrt_eq_exp hz, ← exp_nat_mul]
  ring_nf
  rw [show (log z * 12) = (12 : ℕ) * log z by ring, exp_nat_mul, exp_log hz]
/-
**ModularForm.csqrt_I_pow_24** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：csqrt_I_pow_24 : sqrt I ^ 24 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma csqrt_I_pow_24 : sqrt I ^ 24 = 1 := by
  rw [csqrt_pow_24_eq I_ne_zero, show 12 = 4 * 3 by lia, pow_mul, I_pow_four, one_pow]
/-
**ModularForm.logDeriv_eta_comp_div_eq** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：logDeriv_eta_comp_div_eq (z : ℍ) : logDeriv (η ∘ (-1 / ·)) z = ((z : Compl
ex) ^ (2 : Int))⁻¹ * logDeriv η (-z)⁻¹
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma logDeriv_eta_comp_div_eq (z : ℍ) :
    logDeriv (η ∘ (-1 / ·)) z = ((z : ℂ) ^ (2 : ℤ))⁻¹ * logDeriv η (-z)⁻¹ := by
  simp only [neg_div, one_div, inv_neg]
  rw [logDeriv_comp, mul_comm]
  · simp [zpow_ofNat]
  · exact differentiableAt_eta_of_mem_upperHalfPlaneSet (by grind [im_pnat_div_pos 1 z])
  · fun_prop (disch := exact z.ne_zero)

open EisensteinSeries in
/-
**ModularForm.logDeriv_eta_comp_eq_logDeriv_csqrt_eta** 是 Mathlib 中的一个引理，位于命名空间 
`ModularForm`。
形式化陈述：logDeriv_eta_comp_eq_logDeriv_csqrt_eta (z : ℍ) : logDeriv (η ∘ (-1 / ·)) 
z = logDeriv (sqrt * η) z
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma logDeriv_eta_comp_eq_logDeriv_csqrt_eta (z : ℍ) :
    logDeriv (η ∘ (-1 / ·)) z = logDeriv (sqrt * η) z := by
  rw [logDeriv_eta_comp_div_eq z, Pi.mul_def,
      logDeriv_mul _ (by simp [sqrt, ne_zero z]) (eta_ne_zero z.2)
      (differentiableAt_sqrt (mem_slitPlane z))
      (differentiableAt_eta_of_mem_upperHalfPlaneSet z.2), logDeriv_apply sqrt]
  have hE2 := congrFun (E2_slash_action ModularGroup.S) z
  simp only [one_div, SL_slash_def, modular_S_smul, ModularGroup.denom_S,
    Int.reduceNeg, zpow_neg, riemannZeta_two, mul_inv_rev, inv_div, Pi.sub_apply, Pi.smul_apply,
    D2, ModularGroup.denom_S, smul_eq_mul] at hE2
  rw [deriv_sqrt (mem_slitPlane z), div_eq_mul_inv, logDeriv_eta_eq_E2 z,
    logDeriv_eta_eq_E2 (.mk _ z.im_inv_neg_coe_pos), ← mul_assoc, mul_comm, ← mul_assoc, hE2, sqrt,
    show ModularGroup.S 1 0 = 1 by simp [ModularGroup.S]]
  transitivity 1 / z / 2 + π * I / 12 * E2 z
  · field_simp
    grind [I_sq]
  · rw [div_mul_eq_mul_div₀ _ _ (2 : ℂ), neg_div, cpow_neg, ← mul_inv, ← cpow_add _ _ z.ne_zero]
    norm_num
/-
**ModularForm.eta_comp_eqOn_const_mul_csqrt_eta** 是 Mathlib 中的一个引理，位于命名空间 `Modul
arForm`。
形式化陈述：eta_comp_eqOn_const_mul_csqrt_eta : exists c : Complex, c != 0 ∧ upperHalf
PlaneSet.EqOn (η ∘ (fun z : Complex => -1 / z)) (c • (sqrt * η))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eta_comp_eqOn_const_mul_csqrt_eta :
    ∃ c : ℂ, c ≠ 0 ∧ upperHalfPlaneSet.EqOn (η ∘ (fun z : ℂ ↦ -1 / z)) (c • (sqrt * η)) := by
  rw [← logDeriv_eqOn_iff]
  · exact fun z hz ↦ logDeriv_eta_comp_eq_logDeriv_csqrt_eta ⟨z, hz⟩
  · apply DifferentiableOn.comp (t := upperHalfPlaneSet)
    · exact fun x hx ↦ (differentiableAt_eta_of_mem_upperHalfPlaneSet hx).differentiableWithinAt
    · exact DifferentiableOn.div (by fun_prop) (by fun_prop)
        (fun x hx ↦ ne_zero (⟨x, hx⟩ : ℍ))
    · exact fun y hy ↦ by grind [im_pnat_div_pos 1 (⟨y, hy⟩ : ℍ)]
  · exact fun x hx ↦ ((differentiableAt_sqrt (mem_slitPlane ⟨x, hx⟩)).mul
     (differentiableAt_eta_of_mem_upperHalfPlaneSet hx)).differentiableWithinAt
  · exact isOpen_upperHalfPlaneSet
  · exact Convex.isPreconnected (convex_halfSpace_im_gt 0)
  · exact fun x hx ↦ mul_ne_zero (by simp [sqrt, ne_zero ⟨x, hx⟩]) (eta_ne_zero hx)
  · exact fun x hx ↦ eta_ne_zero (by grind [im_pnat_div_pos 1 ⟨x, hx⟩])

end auxiliary

public section

/-- The discriminant expressed as a q-expansion: `Δ(z) = q * ∏' (1 - q ^ (n + 1)) ^ 24`. -/
/-
**ModularForm.discriminant_eq_q_prod** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：discriminant_eq_q_prod (z : ℍ) : Δ z = 𝕢 1 z * ∏' n, (1 - eta_q n z) ^ 24
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Multipliable.tprod_pow`：Multipliable.tprod_pow [L.NeBot] (hf : Multiplia
ble f L) (n : Nat) : ∏'[L] b, (f b) ^ n = (∏'[L] b, f b) ^ n
· 使用定理 `Complex.instT2Space`：T2Space ℂ
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
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `MultipliableLocallyUniformlyOn.multipliable`：MultipliableLocallyUniforml
yOn.multipliable (h : MultipliableLocallyUniformlyOn f s) (hx : x in s) : Multip
liable (f · x)
· 使用引理 `ModularForm.multipliableLocallyUniformlyOn_eta`：multipliableLocallyUnifo
rmlyOn_eta : MultipliableLocallyUniformlyOn (fun n a => 1 - eta_q n a) ℍₒ
· 使用定理 `UpperHalfPlane.coe_im_pos`：∀ (self : UpperHalfPlane), 0 < (↑self).im

--- 原说明 ---
The discriminant expressed as a q-expansion: `Δ(z) = q * ∏' (1 - q ^ (n + 1)) ^ 
24`.
-/
lemma discriminant_eq_q_prod (z : ℍ) : Δ z = 𝕢 1 z * ∏' n, (1 - eta_q n z) ^ 24 := by
  simp only [discriminant, eta, mul_pow]
  congr
  · simp [Periodic.qParam, ← exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
    grind
  · exact ((multipliableLocallyUniformlyOn_eta.multipliable z.2).tprod_pow _).symm

/-- The modular discriminant is non-vanishing on the upper half-plane. -/
/-
**ModularForm.discriminant_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：discriminant_ne_zero (z : ℍ) : Δ z != 0
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `ModularForm.eta_ne_zero`：eta_ne_zero {z : Complex} (hz : z in ℍₒ) : η z 
!= 0
· 使用定理 `UpperHalfPlane.coe_im_pos`：∀ (self : UpperHalfPlane), 0 < (↑self).im

--- 原说明 ---
The modular discriminant is non-vanishing on the upper half-plane.
-/
lemma discriminant_ne_zero (z : ℍ) : Δ z ≠ 0 := by
  simpa [discriminant] using eta_ne_zero z.2

set_option backward.isDefEq.respectTransparency.types false in
/-- The discriminant is invariant under `T : z ↦ z + 1`, i.e., `Δ(z + 1) = Δ(z)`. -/
/-
**ModularForm.discriminant_T_invariant** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：discriminant_T_invariant : (Δ ∣[(12 : Int)] ModularGroup.T) = Δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularForm.SL_slash_apply`：SL_slash_apply (γ : SL(2, Int)) (τ : ℍ) : (f
 ∣[k] γ) τ = f (γ • τ) * denom γ τ ^ (-k)
· 使用定理 `UpperHalfPlane.denom.eq_1`：∀ (g : GL (Fin 2) ℝ) (z : ℂ), UpperHalfPlane.
denom g z = ↑(↑g 1 0) * z + ↑(↑g 1 1)
· 使用定理 `UpperHalfPlane.modular_T_smul`：modular_T_smul (z : ℍ) : ModularGroup.T •
 z = (1 : Real) +ᵥ z
· 使用定理 `ModularGroup.T.eq_1`：ModularGroup.T = ⟨!![1, 1; 0, 1], ModularGroup.T._p
roof_1⟩
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ModularForm.discriminant_eq_q_prod`：discriminant_eq_q_prod (z : ℍ) : Δ z
 = 𝕢 1 z * ∏' n, (1 - eta_q n z) ^ 24
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.exp_periodic`：exp_periodic : Function.Periodic exp (2 * π * I)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
（共 87 条，此处仅展示前 30 条）

--- 原说明 ---
The discriminant is invariant under `T : z ↦ z + 1`, i.e., `Δ(z + 1) = Δ(z)`.
-/
lemma discriminant_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ := by
  ext z
  rw [SL_slash_apply, denom, modular_T_smul, ModularGroup.T]
  simp [discriminant_eq_q_prod, eta_q, Periodic.qParam, ← exp_periodic (2 * π * I * z)]
  ring_nf

/-- The transformation formula for `η` under `S : z ↦ -1 / z`: we have
`η(-1 / z) = (√I)⁻¹ · √z · η(z)` on the upper half-plane. -/
/-
**ModularForm.eta_comp_eq_csqrt_I_inv** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：eta_comp_eq_csqrt_I_inv : upperHalfPlaneSet.EqOn (η ∘ (-1 / ·)) ((sqrt I)⁻
¹ • (sqrt * η))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.Discriminant.0.ModularForm.et
a_comp_eqOn_const_mul_csqrt_eta`：∃ c,   c ≠ 0 ∧     Set.EqOn (ModularForm.eta ∘ 
fun z => -1 / z) (c • (Complex.sqrt * ModularForm.eta)) UpperHalfPlane.upperHalf
PlaneSet
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.div_I`：div_I (z : Complex) : z / I = -(z * I)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
The transformation formula for `η` under `S : z ↦ -1 / z`: we have
`η(-1 / z) = (√I)⁻¹ · √z · η(z)` on the upper half-plane.
-/
lemma eta_comp_eq_csqrt_I_inv : upperHalfPlaneSet.EqOn
    (η ∘ (-1 / ·)) ((sqrt I)⁻¹ • (sqrt * η)) := by
  obtain ⟨z, hz, h⟩ := eta_comp_eqOn_const_mul_csqrt_eta
  have h3 : η I = z * sqrt I * η I := by simpa [← mul_assoc] using h (show I ∈ _ by simp)
  grind [sqrt, eta_ne_zero (show 0 < I.im by simp)]

set_option backward.isDefEq.respectTransparency.types false in
/-- The discriminant satisfies the modular transformation for `S : z ↦ -1 / z`:
we have `Δ(-1 / z) = z ^ 12 · Δ(z)`. -/
/-
**ModularForm.discriminant_S_invariant** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：discriminant_S_invariant : (Δ ∣[(12 : Int)] ModularGroup.S) = Δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `ModularForm.eta_comp_eq_csqrt_I_inv`：eta_comp_eq_csqrt_I_inv : upperHalf
PlaneSet.EqOn (η ∘ (-1 / ·)) ((sqrt I)⁻¹ • (sqrt * η))
· 使用定理 `UpperHalfPlane.coe_im_pos`：∀ (self : UpperHalfPlane), 0 < (↑self).im
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.Discriminant.0.ModularForm.cs
qrt_I_pow_24`：Complex.I.sqrt ^ 24 = 1
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.Discriminant.0.ModularForm.cs
qrt_pow_24_eq`：∀ {z : ℂ}, z ≠ 0 → z.sqrt ^ 24 = z ^ 12
· 使用定理 `UpperHalfPlane.ne_zero`：ne_zero (z : ℍ) : (z : Complex) != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.pow_eq_eval`：pow_eq_eval [CommGroupWithZero 
M] {l : NF M} {r : Nat} (hr : r != 0) {x : M} (hx : x = l.eval) : x ^ r = (l ^ r
).eval
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
The discriminant satisfies the modular transformation for `S : z ↦ -1 / z`:
we have `Δ(-1 / z) = z ^ 12 · Δ(z)`.
-/
lemma discriminant_S_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ := by
  ext z
  suffices η (-(↑z)⁻¹) ^ 24 * ((z : ℂ) ^ 12)⁻¹ = η z ^ 24 by
    rw [SL_slash_apply, UpperHalfPlane.modular_S_smul]
    simpa [denom, ModularGroup.S]
  have he : η (-(↑z)⁻¹) = (sqrt I)⁻¹ * (sqrt z * η z) := by
    simpa [neg_div] using eta_comp_eq_csqrt_I_inv z.2
  simp only [he, mul_pow, mul_pow, inv_pow, csqrt_I_pow_24, csqrt_pow_24_eq (ne_zero z)]
  field_simp [z.ne_zero]
/-
**ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow** 是 Mathlib 中的一个引理，位于命名空
间 `ModularForm`。
形式化陈述：tendsto_atImInfty_tprod_one_sub_eta_q_pow : Tendsto (fun x : ℍ => ∏' (n : 
Nat), (1 - eta_q n x) ^ 24) atImInfty (𝓝 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `tendsto_tprod_one_add_of_dominated_convergence`：∀ {α : Type u_1} {R : Ty
pe u_2} {β : Type u_3} [inst : NormedCommRing R] [NormOneClass R] [CompleteSpace
 R] {g : β → R}   {bound : β → ℝ} {𝓕…
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `tprod_one`：tprod_one : ∏'[L] _, (1 : α) = 1
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `summable_geometric_of_abs_lt_one`：summable_geometric_of_abs_lt_one {r : 
Real} (h : |r| < 1) : Summable fun n : Nat => r ^ n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_abs_nonneg`：isNNRat_abs_nonneg {α : Type*} 
[DivisionRing α] [LinearOrder α] [IsStrictOrderedRing α] {a : α} {num den : Nat}
 (ra : IsNNRat a num den) : I…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
（共 75 条，此处仅展示前 30 条）
-/
lemma tendsto_atImInfty_tprod_one_sub_eta_q_pow :
    Tendsto (fun x : ℍ ↦ ∏' (n : ℕ), (1 - eta_q n x) ^ 24) atImInfty (𝓝 1) := by
  have htprod : Tendsto (fun q : ℂ ↦ ∏' (n : ℕ), (1 - q ^ (n + 1))) (𝓝 0) (𝓝 1) := by
    have := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := 𝓝 0) (g := 0)
      (f := fun (q : ℂ) (n : ℕ) ↦ -q ^ (n + 1)) (bound := fun n ↦ (1 / 2 : ℝ) ^ (n + 1))
    simp only [Pi.zero_apply, norm_neg, norm_pow, add_zero, tprod_one] at this
    simp_rw [sub_eq_add_neg]
    refine this
      (by simpa only [pow_succ'] using (summable_geometric_of_abs_lt_one (by norm_num)).mul_left _)
      (fun k ↦ by simpa using ((continuous_pow (M := ℂ) (k + 1)).tendsto 0).neg) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with q hq k
    exact pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq).le _
  have := (htprod.comp (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one)).pow 24
  simp only [Periodic.qParam, ofReal_one, div_one, comp_apply, one_pow, eta_q] at *
  convert! this using 2 with τ
  rw [Multipliable.tprod_pow]
  apply (multipliableLocallyUniformlyOn_eta.multipliable τ.2).congr
  simp [eta_q, Periodic.qParam, ← exp_nat_mul]

@[deprecated (since := "2026-04-30")]
alias discriminant_bounded_factor := tendsto_atImInfty_tprod_one_sub_eta_q_pow
/-
**ModularForm.discriminant_isZeroAtImInfty** 是 Mathlib 中的一个引理，位于命名空间 `ModularFor
m`。
形式化陈述：discriminant_isZeroAtImInfty : IsZeroAtImInfty Δ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModularForm.discriminant_eq_q_prod`：discriminant_eq_q_prod (z : ℍ) : Δ z
 = 𝕢 1 z * ∏' n, (1 - eta_q n z) ^ 24
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
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
· 使用引理 `UpperHalfPlane.qParam_tendsto_atImInfty`：qParam_tendsto_atImInfty {h : R
eal} (hh : 0 < h) : Tendsto (fun τ : ℍ => 𝕢 h τ) atImInfty (nhds 0)
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow`：tendsto_atImInfty
_tprod_one_sub_eta_q_pow : Tendsto (fun x : ℍ => ∏' (n : Nat), (1 - eta_q n x) ^
 24) atImInfty (𝓝 1)
-/
lemma discriminant_isZeroAtImInfty : IsZeroAtImInfty Δ := by
  apply Tendsto.congr (fun z ↦ (discriminant_eq_q_prod z).symm)
  rw [show (0 : ℂ) = 0 * 1 by ring]
  exact (qParam_tendsto_atImInfty zero_lt_one).mul
    (tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr fun z ↦ by congr 1)
/-
**ModularForm.exp_isBigO_discriminant** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：exp_isBigO_discriminant : (fun τ => Real.exp (-2 * π * τ.im)) =O[atImInfty
] Δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}   (
c : ℝ), (∀ᶠ (x : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用引理 `ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow`：tendsto_atImInfty
_tprod_one_sub_eta_q_pow : Tendsto (fun x : ℍ => ∏' (n : Nat), (1 - eta_q n x) ^
 24) atImInfty (𝓝 1)
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModularForm.discriminant_eq_q_prod`：discriminant_eq_q_prod (z : ℍ) : Δ z
 = 𝕢 1 z * ∏' n, (1 - eta_q n z) ^ 24
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
（共 94 条，此处仅展示前 30 条）
-/
lemma exp_isBigO_discriminant : (fun τ ↦ Real.exp (-2 * π * τ.im)) =O[atImInfty] Δ := by
  refine .of_bound 2 ?_
  have hprod := tendsto_atImInfty_tprod_one_sub_eta_q_pow.eventually
    (Metric.ball_mem_nhds 1 (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hprod] with τ hτ
  rw [discriminant_eq_q_prod, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hq_norm : ‖𝕢 1 τ‖ = Real.exp (-2 * π * τ.im) := by simp [Periodic.qParam, Complex.norm_exp]
  rw [← hq_norm]
  have hprod_bound : 1 / 2 ≤ ‖∏' n, (1 - eta_q n τ) ^ 24‖ := by
    have hsub : ‖∏' n, (1 - eta_q n τ) ^ 24 - 1‖ < 1 / 2 := by rwa [Complex.dist_eq] at hτ
    have h1 := norm_sub_norm_le 1 (∏' n, (1 - eta_q n τ) ^ 24)
    grind [norm_one, norm_sub_rev]
  linarith [norm_nonneg (𝕢 1 τ), mul_le_mul_of_nonneg_left hprod_bound (norm_nonneg (𝕢 1 τ))]

/-- The cusp function of the discriminant equals `q * ∏' n, (1 - q^(n+1))^24`
on the open unit disc. -/
/-
**ModularForm.discriminant_cuspFunction_eqOn** 是 Mathlib 中的一个引理，位于命名空间 `ModularF
orm`。
形式化陈述：discriminant_cuspFunction_eqOn : Set.EqOn (cuspFunction 1 Δ) (fun q => q *
 ∏' i, (1 - q ^ (i + 1)) ^ 24) (Metric.ball 0 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `tprod_one`：tprod_one : ∏'[L] _, (1 : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Function.Periodic.cuspFunction_zero_of_zero_at_inf`：cuspFunction_zero_of
_zero_at_inf (hh : 0 < h) (h_zer : ZeroAtFilter I∞ f) : cuspFunction h f 0 = 0
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `UpperHalfPlane.IsZeroAtImInfty.zero_at_infty_comp_ofComplex`：zero_at_inf
ty_comp_ofComplex {f : ℍ -> Complex} (hf : IsZeroAtImInfty f) : ZeroAtFilter I∞ 
(f ∘ ofComplex)
· 使用引理 `ModularForm.discriminant_isZeroAtImInfty`：discriminant_isZeroAtImInfty :
 IsZeroAtImInfty Δ
· 使用定理 `Function.Periodic.im_invQParam_pos_of_norm_lt_one`：Function.Periodic.im_
invQParam_pos_of_norm_lt_one {h : Real} (hh : 0 < h) {q : Complex} (hq : ‖q‖ < 1
) (hq_ne : q != 0) : 0 < im (Periodic.i…
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Function.Periodic.cuspFunction_eq_of_nonzero`：cuspFunction_eq_of_nonzero
 {q : Complex} (hq : q != 0) : cuspFunction h f q = f (invQParam h q)
· 使用引理 `UpperHalfPlane.ofComplex_apply_of_im_pos`：ofComplex_apply_of_im_pos {z :
 Complex} (hz : 0 < z.im) : ofComplex z = ⟨z, hz⟩
· 使用引理 `ModularForm.discriminant_eq_q_prod`：discriminant_eq_q_prod (z : ℍ) : Δ z
 = 𝕢 1 z * ∏' n, (1 - eta_q n z) ^ 24
· 使用定理 `Function.Periodic.qParam_right_inv`：qParam_right_inv (hh : h != 0) {q : 
Complex} (hq : q != 0) : 𝕢 h (invQParam h q) = q
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The cusp function of the discriminant equals `q * ∏' n, (1 - q^(n+1))^24`
on the open unit disc.
-/
lemma discriminant_cuspFunction_eqOn : Set.EqOn (cuspFunction 1 Δ)
    (fun q ↦ q * ∏' i, (1 - q ^ (i + 1)) ^ 24) (Metric.ball 0 1) := by
  intro q hq
  by_cases hq0 : q = 0
  · simpa [hq0] using! Periodic.cuspFunction_zero_of_zero_at_inf one_pos
      discriminant_isZeroAtImInfty.zero_at_infty_comp_ofComplex
  · have him := Periodic.im_invQParam_pos_of_norm_lt_one one_pos
      (by simpa [dist_zero_right] using hq) hq0
    simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero 1 _ hq0,
      ofComplex_apply_of_im_pos him, discriminant_eq_q_prod ⟨_, him⟩,
      Periodic.qParam_right_inv one_ne_zero hq0, eta_q]

/-- The first q-expansion coefficient of the modular discriminant is 1. -/
/-
**ModularForm.discriminant_qExpansion_coeff_one** 是 Mathlib 中的一个引理，位于命名空间 `Modul
arForm`。
形式化陈述：discriminant_qExpansion_coeff_one : (qExpansion 1 Δ).coeff 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.qExpansion_coeff`：qExpansion_coeff (f : ℍ -> Complex) (m 
: Nat) : (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunc
tion h f) 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_one`：iteratedDeriv_one : iteratedDeriv 1 f = deriv f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `derivWithin_of_isOpen`：derivWithin_of_isOpen (hs : IsOpen s) (hx : x in 
s) : derivWithin f s x = deriv f x
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `derivWithin_congr`：derivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x
) : derivWithin f₁ s x = derivWithin f s x
· 使用引理 `ModularForm.discriminant_cuspFunction_eqOn`：discriminant_cuspFunction_eq
On : Set.EqOn (cuspFunction 1 Δ) (fun q => q * ∏' i, (1 - q ^ (i + 1)) ^ 24) (Me
tric.ball 0 1)
· 使用定理 `derivWithin_fun_mul`：derivWithin_fun_mul (hc : DifferentiableWithinAt 𝕜 
c s x) (hd : DifferentiableWithinAt 𝕜 d s x) : derivWithin (fun y => c y * d y) 
s x = der…
· 使用定理 `differentiableWithinAt_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用引理 `ModularForm.differentiableOn_tprod_one_sub_pow_pow`：differentiableOn_tpr
od_one_sub_pow_pow (k : Nat) : DifferentiableOn Complex (fun q => ∏' n, (1 - q ^
 (n + 1)) ^ k) (Metric.ball (0 : Complex…
· 使用定理 `derivWithin_id'`：derivWithin_id' (hxs : UniqueDiffWithinAt 𝕜 s x) : deri
vWithin (fun x => x) s x = 1
· 使用定理 `IsOpen.uniqueDiffWithinAt`：IsOpen.uniqueDiffWithinAt (hs : IsOpen s) (xs
 : x in s) : UniqueDiffWithinAt 𝕜 s x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
The first q-expansion coefficient of the modular discriminant is 1.
-/
lemma discriminant_qExpansion_coeff_one : (qExpansion 1 Δ).coeff 1 = 1 := by
  have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  calc (qExpansion 1 Δ).coeff 1
      = derivWithin (cuspFunction 1 Δ) (Metric.ball 0 1) 0 := by
        simp [qExpansion_coeff, ← derivWithin_of_isOpen Metric.isOpen_ball hmem]
    _ = derivWithin (fun q ↦ q * ∏' i, (1 - q ^ (i + 1)) ^ 24) (Metric.ball 0 1) 0 :=
        derivWithin_congr discriminant_cuspFunction_eqOn (discriminant_cuspFunction_eqOn hmem)
    _ = 1 := by
        simp [derivWithin_fun_mul differentiableWithinAt_fun_id
          (differentiableOn_tprod_one_sub_pow_pow 24 _ hmem),
          derivWithin_id' _ _ (Metric.isOpen_ball.uniqueDiffWithinAt hmem)]

end

end ModularForm

public section

namespace CuspForm

open ModularForm

local notation "Δ" => ModularForm.discriminant

/-- The modular discriminant `Δ` as a cusp form of weight 12 and level 1. -/
/-
**CuspForm.discriminant** 是 Mathlib 中的一个定义，位于命名空间 `CuspForm`。
形式化陈述：CuspForm (Matrix.SpecialLinearGroup.mapGL ℝ).range 12
参数：Matrix.SpecialLinearGroup.mapGL ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The modular discriminant `Δ` as a cusp form of weight 12 and level 1.
-/
@[expose] def discriminant : CuspForm 𝒮ℒ 12 where
  toFun := Δ
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine .congr (fun z hz ↦ (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow
      24 |>.differentiableWithinAt) fun z hz ↦ ?_
    simp [ModularForm.discriminant, ofComplex_apply_of_im_pos hz]
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant]
    exact discriminant_isZeroAtImInfty

@[simp]
/-
**CuspForm.coe_discriminant** 是 Mathlib 中的一个引理，位于命名空间 `CuspForm`。
形式化陈述：coe_discriminant : discriminant = Δ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_discriminant : discriminant = Δ := rfl

variable {k : ℤ}

/-- Any cusp form for `𝒮ℒ` is `O(Δ)` at the cusp `i∞`. -/
/-
**CuspForm.exp_decay_isBigO_discriminant** 是 Mathlib 中的一个引理，位于命名空间 `CuspForm`。
形式化陈述：exp_decay_isBigO_discriminant (f : CuspForm 𝒮ℒ k) : f =O[atImInfty] Modula
rForm.discriminant
参数：f : CuspForm 𝒮ℒ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CuspFormClass.exp_decay_atImInfty`：∀ {k : ℤ} {F : Type u_1} [inst : FunL
ike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F)   [CuspFor
mClass F Γ k],   0 < h …
· 使用定理 `CuspFormClass.cuspForm`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ), CuspFor
mClass (CuspForm Γ k) Γ k
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `one_mem_strictPeriods_SL`：one_mem_strictPeriods_SL : (1 : Real) in (𝒮ℒ).
strictPeriods
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用引理 `ModularForm.exp_isBigO_discriminant`：exp_isBigO_discriminant : (fun τ =>
 Real.exp (-2 * π * τ.im)) =O[atImInfty] Δ

--- 原说明 ---
Any cusp form for `𝒮ℒ` is `O(Δ)` at the cusp `i∞`.
-/
lemma exp_decay_isBigO_discriminant (f : CuspForm 𝒮ℒ k) :
    f =O[atImInfty] ModularForm.discriminant :=
  (CuspFormClass.exp_decay_atImInfty (h := 1) f one_pos one_mem_strictPeriods_SL).trans
    (by simpa using exp_isBigO_discriminant)

end CuspForm

@[deprecated CuspForm.discriminant (since := "2026-04-30")]
alias ModularForm.discriminantCuspForm := CuspForm.discriminant

end

