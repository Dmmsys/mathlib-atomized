/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
public import Mathlib.Analysis.PSeries

/-!
# The `L`-function of a modular form
-/

@[expose] public section

open UpperHalfPlane hiding I
open scoped Real
open Filter Complex MatrixGroups Asymptotics

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
  {k : ℤ} (hk : 0 < k) {F : Type*} [FunLike F ℍ ℂ] (f : F) {s : ℂ}

local notation "h" => Subgroup.strictWidthInfty

open ConjAct Pointwise in
private local instance :
    Subgroup.IsArithmetic (toConjAct (ModularGroup.S : GL (Fin 2) ℝ)⁻¹ • Γ) := by
  convert Subgroup.IsArithmetic.conj Γ ↑(ModularGroup.S⁻¹)
  simp only [ModularGroup.S_inv, ← map_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.S]

namespace ModularForm

variable [ModularFormClass F Γ k]

section asymptotics -- private lemmas about aymptotics along `I * ℝ`

/-
**ModularForm.tendsto_ofComplex_I_mul_atTop_atImInfty** 是 Mathlib 中的一个引理，位于命名空间 
`ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma tendsto_ofComplex_I_mul_atTop_atImInfty :
    Tendsto (fun t : ℝ ↦ ofComplex (I * t)) atTop atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  refine tendsto_id.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ofComplex_apply_of_im_pos, ht, ← coe_im]

include F k Γ in -- conclusion doesn't explicitly refer these
/-
**ModularForm.isBigO_comp_ofComplex_I_mul_sub_valueAtInfty** 是 Mathlib 中的一个引理，位于
命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isBigO_comp_ofComplex_I_mul_sub_valueAtInfty (r : ℝ) :
    (fun t : ℝ ↦ f (ofComplex (I * t)) - valueAtInfty f) =O[atTop] (fun t ↦ t ^ r) := by
  obtain ⟨C, hCpos, hCO⟩ := ModularFormClass.exp_decay_sub_atImInfty' f
  refine (hCO.comp_tendsto tendsto_ofComplex_I_mul_atTop_atImInfty).trans ?_
  refine (EventuallyEq.isBigO ?_).trans (isLittleO_exp_neg_mul_rpow_atTop hCpos r).isBigO
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ht, ofComplex_apply_of_im_pos, ← coe_im]

end asymptotics

/-- A `WeakFEPair` structure associated to a modular form. -/
/-
**ModularForm.weakFEPair** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：{Γ : Subgroup (GL (Fin 2) ℝ)} →   [Γ.IsArithmetic] →     {k : ℤ} → 0 < k →
 {F : Type u_1} → [inst : FunLike F UpperHalfPlane ℂ] → F → [ModularFormClass F 
Γ k] → WeakFEPair ℂ
参数：GL (Fin 2) ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `WeakFEPair` structure associated to a modular form.
-/
@[simps] noncomputable def weakFEPair : WeakFEPair ℂ where
  f t := f (ofComplex (I * t))
  g t := translate f ModularGroup.S (ofComplex (I * t))
  k := k
  hk := mod_cast hk
  ε := I ^ k
  hε := zpow_ne_zero _ I_ne_zero
  f₀ := valueAtInfty f
  g₀ := valueAtInfty (translate f ModularGroup.S)
  hf_int := ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ioi
  hg_int := ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ioi
  h_feq t (ht : 0 < t) := by
    rw [coe_translate, slash_def]
    suffices f (ofComplex (I * t⁻¹)) = I ^ k * t ^ k *
        (f ((ModularGroup.S : GL (Fin 2) ℝ) • ofComplex (I * t)) * ofComplex (I * t) ^ (-k)) by
      simpa [σ, denom]
    rw [ofComplex_apply_of_im_pos (by simpa), ofComplex_apply_of_im_pos (by simpa),
      mul_comm (f _), ← mul_assoc, ← mul_zpow, zpow_neg,
      mul_inv_cancel₀ (zpow_ne_zero _ (by aesop))]
    simp only [one_mul]
    congr 1
    ext
    rw [coe_smul_of_det_pos (by simp)]
    simp [num, denom, div_eq_mul_inv, mul_comm]
  hf_top r := by -- `by exact` to hide use of private lemma in @[expose]'d declaration
    exact isBigO_comp_ofComplex_I_mul_sub_valueAtInfty f r
  hg_top r := by -- `by exact` to hide use of private lemma in @[expose]'d declaration
    exact isBigO_comp_ofComplex_I_mul_sub_valueAtInfty (translate f ModularGroup.S) r

/-- The `L`-series of a modular form (including its Archimedean `Γ`-factor). -/
/-
**ModularForm.** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `L`-series of a modular form (including its Archimedean `Γ`-factor).
-/
noncomputable def Λ : ℂ → ℂ := (weakFEPair hk f).Λ

/-- Shared Dirichlet-series summability argument for modular and cusp forms. -/
/-
**ModularForm.hasSum_** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shared Dirichlet-series summability argument for modular and cusp forms.
-/
private lemma hasSum_Λ_of_qExpansion_isBigO {r : ℝ}
    (hpos : 0 < s.re) (hs : r + 1 < s.re)
    (hΛ : Λ hk f s = mellin (fun t ↦ (weakFEPair hk f).f t - (weakFEPair hk f).f₀) s)
    (hcoeff : (fun n ↦ (qExpansion (h Γ) f).coeff n) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    HasSum (fun n ↦ π ^ (-s) * Gamma s * (qExpansion (h Γ) f).coeff n /
      ↑(2 * n / h Γ : ℝ) ^ s) (Λ hk f s) := by
  rw [hΛ]
  have hh := Γ.strictWidthInfty_pos
  have hΓ := Γ.strictWidthInfty_mem_strictPeriods
  refine hasSum_mellin_pi_mul₀ (fun _ ↦ by positivity) hpos ?_ ?_
  · -- show `q`-expansion converges to `f` on positive imaginary axis
    intro t (ht : 0 < t)
    have := hasSum_qExpansion f hh hΓ (ofComplex (I * t))
    convert! hasSum_ite_sub_hasSum this 0 using 2 with n
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · simp [hn.ne', Function.Periodic.qParam, ofComplex_apply_eq_ite, ht, ← exp_nat_mul]
        grind [I_sq]
    · simp only [weakFEPair]
      rw [qExpansion_coeff_zero hh, pow_zero, mul_one]
      · exact ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
      · exact SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  · -- show summability of Dirichlet series
    simp_rw [mul_comm (2 : ℝ), mul_div_assoc,
      Real.mul_rpow (Nat.cast_nonneg _) (show 0 ≤ 2 / h Γ by positivity), ← div_div]
    apply Summable.div_const
    apply summable_of_isBigO_nat (Real.summable_nat_rpow.mpr <| show r - s.re < -1 by linarith)
    simp only [Real.rpow_sub' (Nat.cast_nonneg _) (show r - s.re ≠ 0 by linarith)]
    apply IsBigO.mul _ (isBigO_refl _ _)
    simpa using hcoeff.norm_left
/-
**ModularForm.hasSum_** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasSum_Λ (hs : k + 1 < s.re) :
    HasSum (fun n ↦ π ^ (-s) * Gamma s * (qExpansion (h Γ) f).coeff n /
      ↑(2 * n / h Γ : ℝ) ^ s) (Λ hk f s) := by
  refine hasSum_Λ_of_qExpansion_isBigO hk f (r := k)
    (by linarith [show (0 : ℝ) < k from mod_cast hk]) (by exact_mod_cast hs) ?_ ?_
  · rw [Λ, ← ((weakFEPair hk f).hasMellin <| by grind [weakFEPair]).2]
  · simpa using ModularFormClass.qExpansion_isBigO hk.le f

/-- The `L`-series of a modular form (without its Archimedean `Γ`-factor). -/
/-
**ModularForm.L** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：L (s : Complex) : Complex
参数：s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `L`-series of a modular form (without its Archimedean `Γ`-factor).
-/
noncomputable def L (s : ℂ) : ℂ :=  Λ hk f s * (2 / Gammaℂ s)

/-- Shared conversion from the completed `Λ`-series to the ordinary `L`-series. -/
/-
**ModularForm.hasSum_L_of_hasSum_** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shared conversion from the completed `Λ`-series to the ordinary `L`-series.
-/
private lemma hasSum_L_of_hasSum_Λ (hs : 0 < s.re)
    (hΛ : HasSum (fun n ↦ π ^ (-s) * Gamma s *
      (qExpansion (h Γ) f).coeff n / ↑(2 * n / h Γ : ℝ) ^ s) (Λ hk f s)) :
    HasSum (fun i ↦ (qExpansion (h Γ) f).coeff i / ↑i ^ s) (h Γ ^ (-s) * L hk f s) := by
  convert! hΛ.mul_right (2 / Gammaℂ s * h Γ ^ (-s)) using 1
  · ext n
    generalize (PowerSeries.coeff n) (qExpansion (h Γ) f) = p
    rw [Gammaℂ, ← div_div, ← div_div, div_self two_ne_zero, one_div, cpow_neg (2 * _), inv_inv,
      ← ofReal_ofNat, mul_cpow_ofReal_nonneg two_pos.le Real.pi_pos.le]
    simp only [ofReal_div, ofReal_mul, ofReal_ofNat, ofReal_natCast]
    have : (2 * n / h Γ : ℂ) ^ s = 2 ^ s * n ^ s / h Γ ^ s := by
      rw [← ofReal_ofNat, ← ofReal_natCast, ← ofReal_mul,
        div_cpow_ofReal_nonneg (by grind) Γ.strictWidthInfty_nonneg, ofReal_mul,
        mul_cpow_ofReal_nonneg zero_le_two n.cast_nonneg]
    rw [this, cpow_neg, cpow_neg]
    have := Gamma_ne_zero_of_re_pos hs
    have := cpow_ne_zero_iff (y := s).mpr (.inl <| ofReal_ne_zero.mpr Γ.strictWidthInfty_pos.ne')
    field_simp
  · grind [L]
/-
**ModularForm.hasSum_L** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：hasSum_L (hs : k + 1 < s.re) : HasSum (fun n => (qExpansion (h Γ) f).coeff
 n / n ^ s) (h Γ ^ (-s) * L hk f s)
参数：hs : k + 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.LFunction.0.ModularForm.hasSu
m_L_of_hasSum_Λ`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} [inst : Γ.IsArithmetic] {k : ℤ}
 (hk : 0 < k) {F : Type u_1}   [inst_1 : FunLike F UpperHalfPlane ℂ] (f : F) …
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
（共 44 条，此处仅展示前 30 条）
-/
theorem hasSum_L (hs : k + 1 < s.re) :
    HasSum (fun n ↦ (qExpansion (h Γ) f).coeff n / n ^ s) (h Γ ^ (-s) * L hk f s) :=
  hasSum_L_of_hasSum_Λ hk f (by linarith [show (0 : ℝ) < k from mod_cast hk]) (hasSum_Λ hk f hs)

end ModularForm

open ModularForm

namespace CuspForm

variable [CuspFormClass F Γ k]

/-- For cusp forms the FE-pair is a strong FE-pair. -/
/-
**CuspForm.isStrongFEPair** 是 Mathlib 中的一个引理，位于命名空间 `CuspForm`。
形式化陈述：isStrongFEPair : IsStrongFEPair (weakFEPair hk f) where hf₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CuspForm.instModularFormClassOfCuspFormClass`：∀ {F : Type u_1} {Γ : Subg
roup (GL (Fin 2) ℝ)} {k : ℤ} [inst : FunLike F UpperHalfPlane ℂ] [CuspFormClass 
F Γ k],   ModularFormClass F Γ k
· 使用定理 `UpperHalfPlane.IsZeroAtImInfty.valueAtInfty_eq_zero`：∀ {f : UpperHalfPla
ne → ℂ}, UpperHalfPlane.IsZeroAtImInfty f → UpperHalfPlane.valueAtInfty f = 0
· 使用引理 `CuspFormClass.zero_at_infty`：CuspFormClass.zero_at_infty [CuspFormClass 
F Γ k] [Fact (IsCusp ∞ Γ)] : IsZeroAtImInfty f
· 使用定理 `instFactIsCuspInftyRealOfIsArithmetic`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} [
Γ.IsArithmetic], Fact (IsCusp OnePoint.infty Γ)
· 使用定理 `CuspFormClass.cuspForm`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ), CuspFor
mClass (CuspForm Γ k) Γ k
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.LFunction.0.instIsArithmeticH
SMulConjActGeneralLinearGroupFinOfNatNatRealSubgroupCoeMulEquivToConjActInvMonoi
dHomSpecialLinearGroupToGLIntMapCastRingHomS`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ
.IsArithmetic],   (ConjAct.toConjAct         (Matrix.SpecialLinearGroup.toGL ((M
atrix.SpecialLinearGroup.m…

--- 原说明 ---
For cusp forms the FE-pair is a strong FE-pair.
-/
lemma isStrongFEPair : IsStrongFEPair (weakFEPair hk f) where
  hf₀ := (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero
  hg₀ := (CuspFormClass.zero_at_infty <| translate f ModularGroup.S).valueAtInfty_eq_zero

@[fun_prop]
/-
**CuspForm.differentiable_** 是 Mathlib 中的一个引理，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma differentiable_Λ : Differentiable ℂ (Λ hk f) :=
  (isStrongFEPair hk f).differentiable_Λ
/-
**CuspForm.** 是 Mathlib 中的一个引理，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Λ_eq_mellin : Λ hk f = mellin (fun t ↦ f (ofComplex (I * t))) :=
  (isStrongFEPair hk f).Λ_eq
/-
**CuspForm.hasSum_** 是 Mathlib 中的一个引理，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasSum_Λ (hk : 0 < k) (hs : k / 2 + 1 < s.re) :
    HasSum (fun n ↦ π ^ (-s) * Gamma s * (qExpansion (h Γ) f).coeff n / ↑(2 * n / h Γ : ℝ) ^ s)
      (Λ hk f s) := by
  refine hasSum_Λ_of_qExpansion_isBigO hk f (r := k / 2)
    (by linarith [show (0 : ℝ) < k from mod_cast hk]) hs ?_ ?_
  · simp [Λ_eq_mellin, (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero]
  · simpa using CuspFormClass.qExpansion_isBigO f

@[fun_prop]
/-
**CuspForm.differentiable_L** 是 Mathlib 中的一个引理，位于命名空间 `CuspForm`。
形式化陈述：differentiable_L : Differentiable Complex (L hk f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CuspForm.instModularFormClassOfCuspFormClass`：∀ {F : Type u_1} {Γ : Subg
roup (GL (Fin 2) ℝ)} {k : ℤ} [inst : FunLike F UpperHalfPlane ℂ] [CuspFormClass 
F Γ k],   ModularFormClass F Γ k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Differentiable.fun_mul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{𝔸 : Type u_…
· 使用引理 `CuspForm.differentiable_Λ`：differentiable_Λ : Differentiable Complex (Λ 
hk f)
· 使用定理 `Differentiable.const_mul`：Differentiable.const_mul (ha : Differentiable 
𝕜 a) (b : 𝔸) : Differentiable 𝕜 fun y => b * a y
· 使用定理 `Complex.differentiable_Gammaℂ_inv`：Differentiable ℂ fun s => s.Gammaℂ⁻¹
-/
lemma differentiable_L : Differentiable ℂ (L hk f) := by
  unfold L
  simp only [div_eq_mul_inv]
  fun_prop
/-
**CuspForm.hasSum_L** 是 Mathlib 中的一个定理，位于命名空间 `CuspForm`。
形式化陈述：hasSum_L (hs : k / 2 + 1 < s.re) : HasSum (fun n => (qExpansion (h Γ) f).c
oeff n / n ^ s) (h Γ ^ (-s) * L hk f s)
参数：hs : k / 2 + 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.LFunction.0.ModularForm.hasSu
m_L_of_hasSum_Λ`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} [inst : Γ.IsArithmetic] {k : ℤ}
 (hk : 0 < k) {F : Type u_1}   [inst_1 : FunLike F UpperHalfPlane ℂ] (f : F) …
· 使用定理 `CuspForm.instModularFormClassOfCuspFormClass`：∀ {F : Type u_1} {Γ : Subg
roup (GL (Fin 2) ℝ)} {k : ℤ} [inst : FunLike F UpperHalfPlane ℂ] [CuspFormClass 
F Γ k],   ModularFormClass F Γ k
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
（共 70 条，此处仅展示前 30 条）
-/
theorem hasSum_L (hs : k / 2 + 1 < s.re) :
    HasSum (fun n ↦ (qExpansion (h Γ) f).coeff n / n ^ s) (h Γ ^ (-s) * L hk f s) :=
  hasSum_L_of_hasSum_Λ hk f (by linarith [show (0 : ℝ) < k from mod_cast hk]) (hasSum_Λ f hk hs)

end CuspForm

