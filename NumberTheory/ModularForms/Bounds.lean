/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.Petersson

/-!
# Bounds for the norm of a modular form

We prove bounds for the norm of a modular form `f τ` in terms of `im τ`, and deduce polynomial
bounds for its q-expansion coefficients. The main results are

* `ModularFormClass.exists_bound`: a modular form of weight `k` (for an arithmetic subgroup `Γ`)
  is bounded by a constant multiple of `max 1 (1 / (im τ) ^ k))`.
* `CuspFormClass.exists_bound`: a cusp form of weight `k` (for an arithmetic subgroup `Γ`)
  is bounded by a constant multiple of `1 / (im τ) ^ (k / 2)`.
* `ModularFormClass.qExpansion_isBigO`: for a a modular form of weight `k` (for an arithmetic
  subgroup `Γ`), the `n`-th q-expansion coefficient is `O(n ^ k)`.
* `CuspFormClass.qExpansion_isBigO`: **Hecke's bound** for a a cusp form of weight `k` (for
  an arithmetic subgroup `Γ`): the `n`-th q-expansion coefficient is `O(n ^ (k / 2))`.
-/

public section

open Filter Topology Asymptotics Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup

open UpperHalfPlane hiding I

open Matrix hiding mul_smul

open scoped Modular MatrixGroups ComplexConjugate ModularForm

variable {E : Type*} [SeminormedAddCommGroup E]

namespace ModularGroup

/--
lemma `exists_bound_fundamental_domain_of_isBigO` / 引理 `exists_bound_fundamental_domain_of_isBigO`

English:
lemma exists_bound_fundamental_domain_of_isBigO
  proof: by
  -- Extract a bound for large `im τ` using `hf_infty`.
  obtain ⟨D, hD, hf_infinity⟩ := hf_infinity.exists_pos
  rw [IsBigOWith]; rw [atImInfty]; rw [eventually_comap]; rw [eventually_atTop] at hf_infinity
  obtain ⟨y, hy⟩ := hf_infinity
  simp only [Real.norm_rpow_of_nonneg (_ : ℍ).im_pos.le,
 

中文:
引理 存在_bound_fundamental_domain_of_isBigO
  证明: by
  -- Extract a bound for large `im τ` using `hf_infty`.
  obtain ⟨D, hD, hf_infinity⟩ := hf_infinity.exists_pos
  rw [IsBigOWith]; rw [atImInfty]; rw [eventually_comap]; rw [eventually_atTop] at hf_infinity
  obtain ⟨y, hy⟩ := hf_infinity
  simp only [Real.norm_rpow_of_nonneg (_ : ℍ).im_pos.le,
 
-/
lemma exists_bound_fundamental_domain_of_isBigO
    {f : ℍ -> E} (hf_cont : Continuous f) {t : Real} (hf_infinity : f =O[atImInfty] fun z => z.im ^ t) :
    exists F, forall τ in 𝒟, ‖f τ‖ <= F * τ.im ^ t := by
  -- Extract a bound for large `im τ` using `hf_infty`.
  obtain ⟨D, hD, hf_infinity⟩ := hf_infinity.exists_pos
  rw [IsBigOWith]; rw [atImInfty]; rw [eventually_comap]; rw [eventually_atTop] at hf_infinity
  obtain ⟨y, hy⟩ := hf_infinity
  simp only [Real.norm_rpow_of_nonneg (_ : ℍ).im_pos.le,
      Real.norm_of_nonneg (_ : ℍ).im_pos.le] at hy
  -- Extract a bound for the rest of `𝒟` using continuity and compactness.
  have hfm : ContinuousOn (fun τ => ‖f τ‖ / (im τ) ^ t) (truncatedFundamentalDomain y) := by
    apply (hf_cont.norm.div ?_ fun τ => by positivity).continuousOn
    exact continuous_im.rpow_const fun τ => .inl τ.im_ne_zero
  obtain ⟨E, hE⟩ : exists E, forall τ in truncatedFundamentalDomain y, ‖f τ‖ / (im τ) ^ t <= E := by
    simpa [norm_mul, norm_norm, Real.norm_rpow_of_nonneg (_ : ℍ).im_pos.le,
      Real.norm_of_nonneg (_ : ℍ).im_pos.le]
      using (isCompact_truncatedFundamentalDomain y).exists_bound_of_continuousOn hfm
  -- Put the two bounds together.
  refine ⟨max D E, fun τ hτ => ?_⟩
  rcases le_total y (im τ) with hτ' | hτ'
· exact (hy _ hτ' _ rfl).trans mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)
  · rw [← div_le_iff₀ (by positivity)]
    exact (hE τ ⟨hτ, hτ'⟩).trans (le_max_right _ _)

/--
lemma `exists_bound_of_invariant_of_isBigO` / 引理 `exists_bound_of_invariant_of_isBigO`

English:
lemma exists_bound_of_invariant_of_isBigO
  statement: {f : ℍ -> E} (hf_cont : Continuous f) {t : Real} (ht : 0 <= t)
  proof: by
  -- First find an `F` such that `∀ τ ∈ 𝒟, ‖f τ‖ ≤ F * τ.im ^ t`.
  obtain ⟨F, hF𝒟⟩ : exists F, forall τ in 𝒟, ‖f τ‖ <= F * τ.im ^ t :=
    exists_bound_fundamental_domain_of_isBigO hf_cont hf_infinity
  refine ⟨F, fun τ => ?_⟩
  -- Given `τ`, choose a `g = [a, b; c, d] ∈ SL(2, ℤ)` that translate

中文:
引理 存在_bound_of_invariant_of_isBigO
  结论: {f : ℍ -> E} (hf_cont : 连续 f) {t : 实数} (ht : 0 <= t)
  证明: by
  -- First find an `F` such that `∀ τ ∈ 𝒟, ‖f τ‖ ≤ F * τ.im ^ t`.
  obtain ⟨F, hF𝒟⟩ : exists F, forall τ in 𝒟, ‖f τ‖ <= F * τ.im ^ t :=
    exists_bound_fundamental_domain_of_isBigO hf_cont hf_infinity
  refine ⟨F, fun τ => ?_⟩
  -- Given `τ`, choose a `g = [a, b; c, d] ∈ SL(2, ℤ)` that translate
-/
lemma exists_bound_of_invariant_of_isBigO {f : ℍ -> E} (hf_cont : Continuous f) {t : Real} (ht : 0 <= t)
    (hf_infinity : f =O[atImInfty] fun z => (im z) ^ t)
    (hf_inv : forall (g : SL(2, Int)) τ, f (g • τ) = f τ) :
    exists C, forall τ, ‖f τ‖ <= C * (max (im τ) (1 / im τ)) ^ t := by
  -- First find an `F` such that `∀ τ ∈ 𝒟, ‖f τ‖ ≤ F * τ.im ^ t`.
  obtain ⟨F, hF𝒟⟩ : exists F, forall τ in 𝒟, ‖f τ‖ <= F * τ.im ^ t :=
    exists_bound_fundamental_domain_of_isBigO hf_cont hf_infinity
  refine ⟨F, fun τ => ?_⟩
  -- Given `τ`, choose a `g = [a, b; c, d] ∈ SL(2, ℤ)` that translates `τ` into `𝒟`.
  obtain ⟨g, hg⟩ := exists_smul_mem_fd τ
  specialize hF𝒟 (g • τ) hg
  rw [hf_inv g τ] at hF𝒟
  grw [hF𝒟]
  gcongr
  · rw [← div_le_iff₀ (by positivity)] at hF𝒟
    exact le_trans (by positivity) hF𝒟
  -- It remains to show `(g • τ).im ≤ max τ.im (1 / τ.im)`.
  -- We split into two cases depending whether `c = g 1 0` is zero.
  rw [im_smul_eq_div_normSq]; rw [denom_apply]
  by_cases hg : g 1 0 = 0
  · -- If `c = 0`, then `(g • τ).im = τ.im / d ^ 2` and `d ^ 2 ≥ 1`.
    -- (In fact `d = ±1`, but we do not need this stronger statement).
have : g 1 1 != 0 := fun hg' => zero_ne_one by
      simpa only [Matrix.det_fin_two, hg, hg', mul_zero, mul_zero, sub_zero] using g.det_coe
    have : (1 : Real) <= g 1 1 ^ 2 := mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs this)
refine le_trans ?_ le_max_left _ _
    rw [show Complex.normSq ((g 1 0) * τ + (g 1 1)) = (g 1 1) ^ 2 by simp [hg]; rw [sq]]
    simpa [field] using inv_le_one_of_one_le₀ this
  · -- If `c ≠ 0`, then `1 ≤ c ^ 2`, so
    -- `(g • τ).im = τ.im / (c ^ 2 * τ.im ^ 2 + ...) ≤ 1 / τ.im`.
refine le_trans ?_ le_max_right _ _
    rw [show 1 / τ.im = τ.im / τ.im ^ 2 by field_simp]
    gcongr
    rw [show Complex.normSq ((g 1 0) * τ + (g 1 1)) =
      ((g 1 0) * τ.re + (g 1 1)) ^ 2 + (g 1 0) ^ 2 * τ.im ^ 2 by simp [Complex.normSq_apply]; ring]
    have : (1 : Real) <= g 1 0 ^ 2 := mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs hg)
    nlinarith

/--
lemma `exists_bound_of_subgroup_invariant_of_isBigO` / 引理 `exists_bound_of_subgroup_invariant_of_isBigO`

English:
lemma exists_bound_of_subgroup_invariant_of_isBigO
  proof: by
  -- marshall the info we have in terms of a function on the quotient
  let f' τ : SL(2, Int) ⧸ Γ -> E := Quotient.lift (fun g => f (g⁻¹ • τ)) fun g h hgh => by
    obtain ⟨j, hj, hj'⟩ : exists j in Γ, h = g * j := by
      rw [← Quotient.eq_iff_equiv]; rw [Quotient.eq]; rw [QuotientGroup.leftRel

中文:
引理 存在_bound_of_subgroup_invariant_of_isBigO
  证明: by
  -- marshall the info we have in terms of a function on the quotient
  let f' τ : SL(2, Int) ⧸ Γ -> E := Quotient.lift (fun g => f (g⁻¹ • τ)) fun g h hgh => by
    obtain ⟨j, hj, hj'⟩ : exists j in Γ, h = g * j := by
      rw [← Quotient.eq_iff_equiv]; rw [Quotient.eq]; rw [QuotientGroup.leftRel
-/
lemma exists_bound_of_subgroup_invariant_of_isBigO
    {f : ℍ -> E} (hf_cont : Continuous f) {t : Real} (ht : 0 <= t)
    (hf_infinity : forall (g : SL(2, Int)), (fun τ => f (g • τ)) =O[atImInfty] fun z => (im z) ^ t)
    {Γ : Subgroup SL(2, Int)} [Γ.FiniteIndex] (hf_inv : forall g in Γ, forall τ, f (g • τ) = f τ) :
    exists C, forall τ, ‖f τ‖ <= C * max τ.im (1 / τ.im) ^ t := by
  -- marshall the info we have in terms of a function on the quotient
  let f' τ : SL(2, Int) ⧸ Γ -> E := Quotient.lift (fun g => f (g⁻¹ • τ)) fun g h hgh => by
    obtain ⟨j, hj, hj'⟩ : exists j in Γ, h = g * j := by
      rw [← Quotient.eq_iff_equiv]; rw [Quotient.eq]; rw [QuotientGroup.leftRel_apply] at hgh
      exact ⟨g⁻¹ * h, hgh, (mul_inv_cancel_left g h).symm⟩
    simp [-sl_moeb, hj', mul_smul, hf_inv j⁻¹ (inv_mem hj)]
  have hf'_cont γ : Continuous (f' · γ) := QuotientGroup.induction_on γ fun g => by
    simp only [sl_moeb, f']
    fun_prop
  have hf'_inv τ (g : SL(2, Int)) γ : f' (g • τ) (g • γ) = f' τ γ := by
    induction γ using QuotientGroup.induction_on
    simp [-sl_moeb, f', mul_smul]
  have hf'_infty γ : (f' · γ) =O[_] _ := γ.induction_on fun h => hf_infinity h⁻¹
  -- now take the sum over the quotient
  have : Fintype (SL(2, Int) ⧸ Γ) := Subgroup.fintypeQuotientOfFiniteIndex
  -- Now the conclusion is very simple.
  obtain ⟨C, hC⟩ := exists_bound_of_invariant_of_isBigO (by fun_prop) ht
    (.fun_sum fun i _ => (hf'_infty i).norm_left)
    (fun g τ => (Fintype.sum_equiv (MulAction.toPerm g) _ _ (by simp [-sl_moeb, hf'_inv])).symm)
  refine ⟨C, fun τ => le_trans ?_ (hC τ)⟩
  simpa [Real.norm_of_nonneg <| show 0 <= ∑ γ, ‖f' τ γ‖ by positivity, -sl_moeb, f'] using
    Finset.univ.single_le_sum (fun γ _ => norm_nonneg (f' τ γ)) (Finset.mem_univ ⟦1⟧)

/--
lemma `exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO` / 引理 `exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO`

English:
lemma exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO
  proof: exists_bound_of_subgroup_invariant_of_isBigO hf_cont ht hf_infinity (Γ := Γ.comap (mapGL Real))
    (hf_inv ·)

中文:
引理 存在_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO
  证明: exists_bound_of_subgroup_invariant_of_isBigO hf_cont ht hf_infinity (Γ := Γ.comap (mapGL Real))
    (hf_inv ·)

Depends on / 依赖: exists_bound_of_subgroup_invariant_of_isBigO, hf_cont, hf_infinity, hf_inv
-/
lemma exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO
    {f : ℍ -> E} (hf_cont : Continuous f) {t : Real} (ht : 0 <= t)
    (hf_infinity : forall (g : SL(2, Int)), (fun τ => f (g • τ)) =O[atImInfty] fun z => (im z) ^ t)
    {Γ : Subgroup (GL (Fin 2) Real)} [Γ.IsArithmetic] (hf_inv : forall g in Γ, forall τ, f (g • τ) = f τ) :
    exists C, forall τ, ‖f τ‖ <= C * max τ.im (1 / τ.im) ^ t :=
  exists_bound_of_subgroup_invariant_of_isBigO hf_cont ht hf_infinity (Γ := Γ.comap (mapGL Real))
    (hf_inv ·)

/--
lemma `exists_bound_of_invariant` / 引理 `exists_bound_of_invariant`

English:
lemma exists_bound_of_invariant
  proof: by
  simpa using! exists_bound_of_invariant_of_isBigO hf_cont le_rfl
    (by simpa only [Real.rpow_zero] using! hf_infinity) hf_inv

中文:
引理 存在_bound_of_invariant
  证明: by
  simpa using! exists_bound_of_invariant_of_isBigO hf_cont le_rfl
    (by simpa only [Real.rpow_zero] using! hf_infinity) hf_inv

Depends on / 依赖: Real.rpow_zero, exists_bound_of_invariant_of_isBigO, hf_cont, hf_infinity, hf_inv, le_rfl, rpow_zero
-/
lemma exists_bound_of_invariant
    {f : ℍ -> E} (hf_cont : Continuous f) (hf_infinity : IsBoundedAtImInfty f)
    (hf_inv : forall (g : SL(2, Int)) τ, f (g • τ) = f τ) :
    exists C, forall τ, ‖f τ‖ <= C := by
  simpa using! exists_bound_of_invariant_of_isBigO hf_cont le_rfl
    (by simpa only [Real.rpow_zero] using! hf_infinity) hf_inv

/--
lemma `exists_bound_of_subgroup_invariant` / 引理 `exists_bound_of_subgroup_invariant`

English:
lemma exists_bound_of_subgroup_invariant
  statement: {f : ℍ -> E} (hf_cont : Continuous f)
  proof: by
  simpa using! exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO hf_cont le_rfl
    (by simpa only [Real.rpow_zero] using! hf_infinity) hf_inv

中文:
引理 存在_bound_of_subgroup_invariant
  结论: {f : ℍ -> E} (hf_cont : 连续 f)
  证明: by
  simpa using! exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO hf_cont le_rfl
    (by simpa only [Real.rpow_zero] using! hf_infinity) hf_inv

Depends on / 依赖: Real.rpow_zero, exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO, hf_cont, hf_infinity, hf_inv, le_rfl, rpow_zero
-/
lemma exists_bound_of_subgroup_invariant {f : ℍ -> E} (hf_cont : Continuous f)
    (hf_infinity : forall (g : SL(2, Int)), IsBoundedAtImInfty fun τ => f (g • τ))
    {Γ : Subgroup (GL (Fin 2) Real)} [Γ.IsArithmetic] (hf_inv : forall g in Γ, forall τ, f (g • τ) = f τ) :
    exists C, forall τ, ‖f τ‖ <= C := by
  simpa using! exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO hf_cont le_rfl
    (by simpa only [Real.rpow_zero] using! hf_infinity) hf_inv

end ModularGroup

/--
lemma `ModularFormClass.exists_petersson_le` / 引理 `ModularFormClass.exists_petersson_le`

English:
lemma ModularFormClass.exists_petersson_le
  statement: {k : Int} (hk : 0 <= k) (Γ : Subgroup (GL (Fin 2) Real))
  proof: by
  conv => enter [1, C, τ, 1]; rw [← norm_norm]
  refine mod_cast ModularGroup.exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO
    (show Continuous (‖petersson k f f' ·‖) by fun_prop) (mod_cast hk : 0 <= (k : Real))
    (fun g => ?_) (fun g hg τ => SlashInvariantFormClass.norm_peterss

中文:
引理 模形式类.存在_petersson_le
  结论: {k : 整数} (hk : 0 <= k) (Γ : 子群 (GL (有限集 2) 实数))
  证明: by
  conv => enter [1, C, τ, 1]; rw [← norm_norm]
  refine mod_cast ModularGroup.exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO
    (show Continuous (‖petersson k f f' ·‖) by fun_prop) (mod_cast hk : 0 <= (k : Real))
    (fun g => ?_) (fun g hg τ => SlashInvariantFormClass.norm_peterss

Depends on / 依赖: Continuous, ModularGroup, ModularGroup.exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO, Real.norm_of_nonneg, Real.rpow_intCast, SlashInvariantFormClass, SlashInvariantFormClass.norm_petersson_smul, UpperHalfPlane, UpperHalfPlane.petersson_slash_SL, bdd_at_infty_slash, exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO, fun_prop, im_pos, im_pos.le, mod_cast, norm_le, norm_left, norm_left.mul, norm_norm, norm_of_nonneg
-/
lemma ModularFormClass.exists_petersson_le {k : Int} (hk : 0 <= k) (Γ : Subgroup (GL (Fin 2) Real))
    [Γ.IsArithmetic] {F F' : Type*} (f : F) (f' : F')
    [FunLike F ℍ Complex] [FunLike F' ℍ Complex] [ModularFormClass F Γ k] [ModularFormClass F' Γ k] :
    exists C, forall τ, ‖petersson k f f' τ‖ <= C * max τ.im (1 / τ.im) ^ k := by
  conv => enter [1, C, τ, 1]; rw [← norm_norm]
  refine mod_cast ModularGroup.exists_bound_of_subgroup_invariant_of_isArithmetic_of_isBigO
    (show Continuous (‖petersson k f f' ·‖) by fun_prop) (mod_cast hk : 0 <= (k : Real))
    (fun g => ?_) (fun g hg τ => SlashInvariantFormClass.norm_petersson_smul hg)
  simp_rw [← UpperHalfPlane.petersson_slash_SL, Real.rpow_intCast]
  simpa [petersson, Real.norm_of_nonneg (_ : ℍ).im_pos.le]
    using (bdd_at_infty_slash f g).norm_left.mul (bdd_at_infty_slash f' g).norm_left
.mul (isBigO_refl ..)

open ConjAct Pointwise in
/--
lemma `CuspFormClass.petersson_bounded_left` / 引理 `CuspFormClass.petersson_bounded_left`

English:
lemma CuspFormClass.petersson_bounded_left
  proof: by
  conv => enter [1, C, τ, 1]; rw [← norm_norm]
  refine ModularGroup.exists_bound_of_subgroup_invariant (by fun_prop) (fun g => ?_)
    fun g hg τ => SlashInvariantFormClass.norm_petersson_smul hg
  apply IsZeroAtImInfty.isBoundedAtImInfty
  rw [IsZeroAtImInfty]; rw [ZeroAtFilter]; rw [← tendsto_

中文:
引理 尖点形式类.petersson_bounded_left
  证明: by
  conv => enter [1, C, τ, 1]; rw [← norm_norm]
  refine ModularGroup.exists_bound_of_subgroup_invariant (by fun_prop) (fun g => ?_)
    fun g hg τ => SlashInvariantFormClass.norm_petersson_smul hg
  apply IsZeroAtImInfty.isBoundedAtImInfty
  rw [IsZeroAtImInfty]; rw [ZeroAtFilter]; rw [← tendsto_

Depends on / 依赖: IsArithmetic, IsZeroAtImInfty, IsZeroAtImInfty.isBoundedAtImInfty, ModularGroup, ModularGroup.exists_bound_of_subgroup_invariant, Rat.castHom, SlashInvariantFormClass, SlashInvariantFormClass.norm_petersson_smul, UpperHalfPlane, UpperHalfPlane.petersson_slash_SL, ZeroAtFilter, algebraMap, castHom, exists_bound_of_subgroup_invariant, fun_prop, isBoundedAtImInfty, map_inv, norm_norm, norm_petersson_smul, petersson_slash_SL
-/
lemma CuspFormClass.petersson_bounded_left
    (k : Int) (Γ : Subgroup (GL (Fin 2) Real)) [Γ.IsArithmetic] {F F' : Type*} (f : F) (f' : F')
    [FunLike F ℍ Complex] [FunLike F' ℍ Complex] [CuspFormClass F Γ k] [ModularFormClass F' Γ k] :
    exists C, forall τ, ‖petersson k f f' τ‖ <= C := by
  conv => enter [1, C, τ, 1]; rw [← norm_norm]
  refine ModularGroup.exists_bound_of_subgroup_invariant (by fun_prop) (fun g => ?_)
    fun g hg τ => SlashInvariantFormClass.norm_petersson_smul hg
  apply IsZeroAtImInfty.isBoundedAtImInfty
  rw [IsZeroAtImInfty]; rw [ZeroAtFilter]; rw [← tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← UpperHalfPlane.petersson_slash_SL]
  have : ((toConjAct (g : GL (Fin 2) Real)⁻¹) • Γ).IsArithmetic := by
    simpa [(show Rat.castHom Real = algebraMap Rat Real by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj Γ (mapGL Rat g)⁻¹
  exact (zero_at_infty <| CuspForm.translate f g).petersson_isZeroAtImInfty_left k _
    (ModularForm.translate f' g)

/--
lemma `CuspFormClass.petersson_bounded_right` / 引理 `CuspFormClass.petersson_bounded_right`

English:
lemma CuspFormClass.petersson_bounded_right
  proof: by
  simpa [petersson_norm_symm] using petersson_bounded_left k Γ f' f

中文:
引理 尖点形式类.petersson_bounded_right
  证明: by
  simpa [petersson_norm_symm] using petersson_bounded_left k Γ f' f

Depends on / 依赖: petersson_bounded_left, petersson_norm_symm
-/
lemma CuspFormClass.petersson_bounded_right
    (k : Int) (Γ : Subgroup (GL (Fin 2) Real)) [Γ.IsArithmetic] {F F' : Type*} (f : F) (f' : F')
    [FunLike F ℍ Complex] [FunLike F' ℍ Complex] [ModularFormClass F Γ k] [CuspFormClass F' Γ k] :
    exists C, forall τ, ‖petersson k f f' τ‖ <= C := by
  simpa [petersson_norm_symm] using petersson_bounded_left k Γ f' f

/--
lemma `CuspFormClass.exists_bound` / 引理 `CuspFormClass.exists_bound`

English:
lemma CuspFormClass.exists_bound
  statement: {k : Int} {Γ : Subgroup (GL (Fin 2) Real)} [Γ.IsArithmetic]
  proof: by
  obtain ⟨C, hC⟩ := petersson_bounded_left k Γ f f
  refine ⟨C.sqrt, fun τ => ?_⟩
  specialize hC τ
  rw [← sq_le_sq₀ (by positivity) (by positivity)]; rw [div_pow]; rw [Real.sq_sqrt ((norm_nonneg _).trans hC)]
  grw [← hC]
  rw [petersson]; rw [← Real.rpow_mul_natCast τ.im_pos.le]
  simp [abs_of

中文:
引理 尖点形式类.存在_bound
  结论: {k : 整数} {Γ : 子群 (GL (有限集 2) 实数)} [Γ.是Arithmetic]
  证明: by
  obtain ⟨C, hC⟩ := petersson_bounded_left k Γ f f
  refine ⟨C.sqrt, fun τ => ?_⟩
  specialize hC τ
  rw [← sq_le_sq₀ (by positivity) (by positivity)]; rw [div_pow]; rw [Real.sq_sqrt ((norm_nonneg _).trans hC)]
  grw [← hC]
  rw [petersson]; rw [← Real.rpow_mul_natCast τ.im_pos.le]
  simp [abs_of

Depends on / 依赖: C.sqrt, Real.rpow_mul_natCast, Real.sq_sqrt, abs_of_pos, div_pow, im_pos, im_pos.le, norm_nonneg, petersson, petersson_bounded_left, rpow_mul_natCast, specialize, sq_sqrt
-/
lemma CuspFormClass.exists_bound {k : Int} {Γ : Subgroup (GL (Fin 2) Real)} [Γ.IsArithmetic]
    {F : Type*} [FunLike F ℍ Complex] [CuspFormClass F Γ k] (f : F) :
    exists C, forall τ, ‖f τ‖ <= C / τ.im ^ (k / 2 : Real) := by
  obtain ⟨C, hC⟩ := petersson_bounded_left k Γ f f
  refine ⟨C.sqrt, fun τ => ?_⟩
  specialize hC τ
  rw [← sq_le_sq₀ (by positivity) (by positivity)]; rw [div_pow]; rw [Real.sq_sqrt ((norm_nonneg _).trans hC)]
  grw [← hC]
  rw [petersson]; rw [← Real.rpow_mul_natCast τ.im_pos.le]
  simp [abs_of_pos τ.im_pos, field]

open Real in
/--
lemma `ModularFormClass.exists_bound` / 引理 `ModularFormClass.exists_bound`

English:
lemma ModularFormClass.exists_bound
  statement: {k : Int} (hk : 0 <= k) {Γ : Subgroup (GL (Fin 2) Real)}
  proof: by
  obtain ⟨C, hC⟩ := ModularFormClass.exists_petersson_le hk Γ f f
  refine ⟨C.sqrt, fun τ => ?_⟩
  lift k to Nat using hk
  specialize hC τ
have hC' : 0 <= C := le_trans (by positivity) (div_le_iff₀ (by positivity)).mpr hC
  have h : 0 < ‖(τ.im : Complex) ^ (k : Int)‖ := mod_cast norm_pos_iff.mpr

中文:
引理 模形式类.存在_bound
  结论: {k : 整数} (hk : 0 <= k) {Γ : 子群 (GL (有限集 2) 实数)}
  证明: by
  obtain ⟨C, hC⟩ := ModularFormClass.exists_petersson_le hk Γ f f
  refine ⟨C.sqrt, fun τ => ?_⟩
  lift k to Nat using hk
  specialize hC τ
have hC' : 0 <= C := le_trans (by positivity) (div_le_iff₀ (by positivity)).mpr hC
  have h : 0 < ‖(τ.im : Complex) ^ (k : Int)‖ := mod_cast norm_pos_iff.mpr

Depends on / 依赖: C.sqrt, Complex.norm_conj, ModularFormClass, ModularFormClass.exists_petersson_le, exists_petersson_le, im_ne_zero, le_trans, mod_cast, mul_div_assoc, norm_conj, norm_mul, norm_pos_iff, norm_pos_iff.mpr, petersson, pow_ne_zero, specialize
-/
lemma ModularFormClass.exists_bound {k : Int} (hk : 0 <= k) {Γ : Subgroup (GL (Fin 2) Real)}
    [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ Complex] [ModularFormClass F Γ k] (f : F) :
    exists C, forall τ, ‖f τ‖ <= C * (max 1 (1 / (τ.im) ^ k)) := by
  obtain ⟨C, hC⟩ := ModularFormClass.exists_petersson_le hk Γ f f
  refine ⟨C.sqrt, fun τ => ?_⟩
  lift k to Nat using hk
  specialize hC τ
have hC' : 0 <= C := le_trans (by positivity) (div_le_iff₀ (by positivity)).mpr hC
  have h : 0 < ‖(τ.im : Complex) ^ (k : Int)‖ := mod_cast norm_pos_iff.mpr (pow_ne_zero _ τ.im_ne_zero)
  rw [petersson]; rw [norm_mul]; rw [norm_mul]; rw [Complex.norm_conj]; rw [← sq]; rw [← le_div_iff₀ h]; rw [mul_div_assoc] at hC
  rw [← sq_le_sq₀ (by positivity) (by positivity)]; rw [mul_pow]; rw [sq_sqrt hC']
  refine hC.trans (congrArg (C * ·) ?_).le
  -- remains to show `(max τ.im (1 / τ.im)) ^ k / ‖τ.im ^ k‖ = (max 1 (1 / τ.im ^ k)) ^ 2`,
  -- which is easier after lifting to `NNReal`
  generalize h : τ.im = t
  have ht : 0 < t := h ▸ τ.im_pos
  lift t to NNReal using ht.le
  rw [← coe_nnnorm]
  norm_cast at ⊢ ht
  rw [(pow_left_mono k).map_max]; rw [(pow_left_mono 2).map_max]; rw [← max_div_div_right (by positivity)]
  congr <;> simp [field, ht.ne']

local notation "𝕢" => Function.Periodic.qParam

open Complex ModularFormClass

/--
lemma `qExpansion_coeff_isBigO_of_norm_isBigO` / 引理 `qExpansion_coeff_isBigO_of_norm_isBigO`

English:
lemma qExpansion_coeff_isBigO_of_norm_isBigO
  statement: {k : Int} {Γ : Subgroup (GL (Fin 2) Real)}
  proof: by
  let h := Γ.strictWidthInfty
  have hh : 0 < h := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have : NeZero h := ⟨hh.ne'⟩
  have hΓ : h in Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  obtain ⟨C, Cpos, hC⟩ := hF.exists_pos
  rw [isBigO_iff]
  rw [IsBigOWith]; rw [eventually_comap] at h

中文:
引理 qExpansion_coeff_isBigO_of_norm_isBigO
  结论: {k : 整数} {Γ : 子群 (GL (有限集 2) 实数)}
  证明: by
  let h := Γ.strictWidthInfty
  have hh : 0 < h := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have : NeZero h := ⟨hh.ne'⟩
  have hΓ : h in Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  obtain ⟨C, Cpos, hC⟩ := hF.exists_pos
  rw [isBigO_iff]
  rw [IsBigOWith]; rw [eventually_comap] at h

Depends on / 依赖: Fact.out, IsBigOWith, ModularFormClass, ModularFormClass.qExpansion_coeff_eq_in, NeZero, Real.exp, Real.pi, eventually, eventually_comap, eventually_gt_atTop, exists_pos, filter_upwards, hF.exists_pos, hh.ne, isBigO_iff, qExpansion_coeff_eq_in, strictPeriods, strictWidthInfty, strictWidthInfty_mem_strictPeriods, strictWidthInfty_pos_iff
-/
lemma qExpansion_coeff_isBigO_of_norm_isBigO {k : Int} {Γ : Subgroup (GL (Fin 2) Real)}
    [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ Complex] [ModularFormClass F Γ k] (f : F) (e : Real)
    (hF : IsBigO (comap UpperHalfPlane.im (𝓝 0)) f (fun τ => τ.im ^ (-e))) :
    (fun n => (qExpansion Γ.strictWidthInfty f).coeff n) =O[atTop] fun n => (n : Real) ^ e := by
  let h := Γ.strictWidthInfty
  have hh : 0 < h := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have : NeZero h := ⟨hh.ne'⟩
  have hΓ : h in Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  obtain ⟨C, Cpos, hC⟩ := hF.exists_pos
  rw [isBigO_iff]
  rw [IsBigOWith]; rw [eventually_comap] at hC
  use (1 / Real.exp (-2 * Real.pi / ↑h)) * C
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).eventually hC] with n hn hn'
  rw [ModularFormClass.qExpansion_coeff_eq_intervalIntegral (t := 1 / n) f hh hΓ _ (by positivity)]; rw [← intervalIntegral.integral_const_mul]
  simp only [ofReal_div, ofReal_one, ofReal_natCast]
.trans ?_ refine intervalIntegral.norm_integral_le_integral_norm (by positivity)
  let F (x : Real) : Real := ‖1 / ↑h * (1 / 𝕢 h ((x : Complex) + 1 / n * I) ^ n
      * f ⟨(x : Complex) + 1 / n * Complex.I, by simp [hn]⟩)‖
  have hne : ‖(n : Real) ^ e‖ = n ^ e := Real.norm_of_nonneg (by positivity)
  have (x : Real) : F x <= 1 / h * (1 / Real.exp (-2 * Real.pi / ↑h)) * (C * n ^ e) := by
    simp only [F, norm_mul, norm_div, norm_real, norm_one, norm_pow, mul_assoc]
    rw [Real.norm_of_nonneg hh.le]; rw [Function.Periodic.norm_qParam]; rw [← Real.exp_nat_mul]
    gcongr
    · simp [field]
    · grw [hn' _ (by simp [← UpperHalfPlane.coe_im])]
      simp [← UpperHalfPlane.coe_im, Real.rpow_neg_eq_inv_rpow, hne]
  refine (intervalIntegral.integral_mono (by positivity) ?_ ?_ this).trans (le_of_eq ?_)
  · apply Continuous.intervalIntegrable
    fun_prop (disch := simp [Function.Periodic.qParam_ne_zero])
  · exact continuous_const.intervalIntegrable ..
  · simp [field, intervalIntegral.integral_const, hne]

/--
lemma `ModularFormClass.qExpansion_isBigO` / 引理 `ModularFormClass.qExpansion_isBigO`

English:
lemma ModularFormClass.qExpansion_isBigO
  statement: {k : Int} (hk : 0 <= k) {Γ : Subgroup (GL (Fin 2) Real)}
  proof: by
  simp only [← Real.rpow_intCast]
  apply qExpansion_coeff_isBigO_of_norm_isBigO
  obtain ⟨C, hC⟩ := exists_bound hk f
  simp_rw [IsBigO, ← Int.cast_neg, Real.rpow_intCast, IsBigOWith, eventually_comap]
  use C
  filter_upwards [eventually_le_nhds zero_lt_one] with _ hτ τ rfl
  refine (hC τ).tran

中文:
引理 模形式类.qExpansion_isBigO
  结论: {k : 整数} (hk : 0 <= k) {Γ : 子群 (GL (有限集 2) 实数)}
  证明: by
  simp only [← Real.rpow_intCast]
  apply qExpansion_coeff_isBigO_of_norm_isBigO
  obtain ⟨C, hC⟩ := exists_bound hk f
  simp_rw [IsBigO, ← Int.cast_neg, Real.rpow_intCast, IsBigOWith, eventually_comap]
  use C
  filter_upwards [eventually_le_nhds zero_lt_one] with _ hτ τ rfl
  refine (hC τ).tran

Depends on / 依赖: Int.cast_neg, IsBigO, IsBigOWith, Real.norm_of_nonneg, Real.rpow_intCast, cast_neg, eventually_comap, eventually_le_nhds, exists_bound, filter_upwards, im_pos, le_of_eq, max_eq_right, norm_of_nonneg, one_div, one_le_one_div, qExpansion_coeff_isBigO_of_norm_isBigO, rpow_intCast, simp_rw, zero_lt_one
-/
lemma ModularFormClass.qExpansion_isBigO {k : Int} (hk : 0 <= k) {Γ : Subgroup (GL (Fin 2) Real)}
    [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ Complex] [ModularFormClass F Γ k] (f : F) :
    (fun n => (qExpansion Γ.strictWidthInfty f).coeff n) =O[atTop] fun n => (n : Real) ^ k := by
  simp only [← Real.rpow_intCast]
  apply qExpansion_coeff_isBigO_of_norm_isBigO
  obtain ⟨C, hC⟩ := exists_bound hk f
  simp_rw [IsBigO, ← Int.cast_neg, Real.rpow_intCast, IsBigOWith, eventually_comap]
  use C
  filter_upwards [eventually_le_nhds zero_lt_one] with _ hτ τ rfl
  refine (hC τ).trans (le_of_eq ?_)
  rw [max_eq_right]; rw [zpow_neg]; rw [Real.norm_of_nonneg (by positivity)]; rw [one_div]
  exact one_le_one_div (by positivity) (zpow_le_one₀ τ.im_pos hτ hk)

/--
lemma `CuspFormClass.qExpansion_isBigO` / 引理 `CuspFormClass.qExpansion_isBigO`

English:
lemma CuspFormClass.qExpansion_isBigO
  statement: {k : Int} {Γ : Subgroup (GL (Fin 2) Real)}
  proof: by
  apply qExpansion_coeff_isBigO_of_norm_isBigO
  obtain ⟨C, hC⟩ := exists_bound f
  refine isBigO_of_le' (c := C) _ fun τ => (hC τ).trans (of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]; rw [Real.rpow_neg τ.im_pos.le]; rw [div_eq_mul_inv]

中文:
引理 尖点形式类.qExpansion_isBigO
  结论: {k : 整数} {Γ : 子群 (GL (有限集 2) 实数)}
  证明: by
  apply qExpansion_coeff_isBigO_of_norm_isBigO
  obtain ⟨C, hC⟩ := exists_bound f
  refine isBigO_of_le' (c := C) _ fun τ => (hC τ).trans (of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]; rw [Real.rpow_neg τ.im_pos.le]; rw [div_eq_mul_inv]

Depends on / 依赖: Real.norm_of_nonneg, Real.rpow_neg, div_eq_mul_inv, exists_bound, im_pos, im_pos.le, isBigO_of_le, norm_of_nonneg, of_eq, qExpansion_coeff_isBigO_of_norm_isBigO, rpow_neg
-/
lemma CuspFormClass.qExpansion_isBigO {k : Int} {Γ : Subgroup (GL (Fin 2) Real)}
    [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ Complex] [CuspFormClass F Γ k] (f : F) :
    (fun n => (UpperHalfPlane.qExpansion Γ.strictWidthInfty f).coeff n)
      =O[atTop] fun n => (n : Real) ^ ((k : Real) / 2) := by
  apply qExpansion_coeff_isBigO_of_norm_isBigO
  obtain ⟨C, hC⟩ := exists_bound f
  refine isBigO_of_le' (c := C) _ fun τ => (hC τ).trans (of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]; rw [Real.rpow_neg τ.im_pos.le]; rw [div_eq_mul_inv]
