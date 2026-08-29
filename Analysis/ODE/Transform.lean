/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Translation and scaling of integral curves

New integral curves may be constructed by translating or scaling the domain of an existing integral
curve.

## Tags

integral curve, vector field
-/

public section

open Function Set Pointwise

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {γ γ' : Real -> E} {v : Real -> E -> E} {s s' : Set Real} {t₀ : Real}

/-! ### Translation lemmas -/

section Translation

/--
lemma `IsIntegralCurveOn.comp_add` / 引理 `IsIntegralCurveOn.comp_add`

English:
lemma IsIntegralCurveOn.comp_add
  given: (hγ : IsIntegralCurveOn γ v s) (dt : Real)
  proof: by
  intros t ht
  rw [comp_apply]; rw [hasDerivWithinAt_iff_hasFDerivWithinAt]; rw [Function.comp_def]; rw [hasFDerivWithinAt_comp_add_right]; rw [← hasDerivWithinAt_iff_hasFDerivWithinAt]; rw [vadd_neg_vadd]
  apply hγ (t + dt)
  rwa [mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, add_comm] 

中文:
引理 Is整数egralCurveOn.comp_add
  条件: (hγ : Is整数egralCurveOn γ v s) (dt : 实数)
  证明: by
  intros t ht
  rw [comp_apply]; rw [hasDerivWithinAt_iff_hasFDerivWithinAt]; rw [Function.comp_def]; rw [hasFDerivWithinAt_comp_add_right]; rw [← hasDerivWithinAt_iff_hasFDerivWithinAt]; rw [vadd_neg_vadd]
  apply hγ (t + dt)
  rwa [mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, add_comm] 

Depends on / 依赖: Function, Function.comp_def, add_comm, comp_apply, comp_def, hasDerivWithinAt_iff_hasFDerivWithinAt, hasFDerivWithinAt_comp_add_right, intros, mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, vadd_neg_vadd
-/
lemma IsIntegralCurveOn.comp_add (hγ : IsIntegralCurveOn γ v s) (dt : Real) :
    IsIntegralCurveOn (γ ∘ (· + dt)) (v ∘ (· + dt)) (-dt +ᵥ s) := by
  intros t ht
  rw [comp_apply]; rw [hasDerivWithinAt_iff_hasFDerivWithinAt]; rw [Function.comp_def]; rw [hasFDerivWithinAt_comp_add_right]; rw [← hasDerivWithinAt_iff_hasFDerivWithinAt]; rw [vadd_neg_vadd]
  apply hγ (t + dt)
  rwa [mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, add_comm] at ht

/--
lemma `isIntegralCurveOn_comp_add` / 引理 `isIntegralCurveOn_comp_add`

English:
lemma isIntegralCurveOn_comp_add
  given: {dt : Real}
  proof: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  · ext t
    simp only [comp_apply, neg_add_cancel_right]
  · ext t
    simp only [comp_apply, neg_add_cancel_right]
  · simp only [neg_neg, vadd_neg_vadd]

中文:
引理 is整数egralCurveOn_comp_add
  条件: {dt : 实数}
  证明: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  · ext t
    simp only [comp_apply, neg_add_cancel_right]
  · ext t
    simp only [comp_apply, neg_add_cancel_right]
  · simp only [neg_neg, vadd_neg_vadd]

Depends on / 依赖: comp_add, comp_apply, convert, neg_add_cancel_right, neg_neg, vadd_neg_vadd
-/
lemma isIntegralCurveOn_comp_add {dt : Real} :
    IsIntegralCurveOn (γ ∘ (· + dt)) (v ∘ (· + dt)) (-dt +ᵥ s) ↔ IsIntegralCurveOn γ v s := by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  · ext t
    simp only [comp_apply, neg_add_cancel_right]
  · ext t
    simp only [comp_apply, neg_add_cancel_right]
  · simp only [neg_neg, vadd_neg_vadd]

/--
lemma `isIntegralCurveOn_comp_sub` / 引理 `isIntegralCurveOn_comp_sub`

English:
lemma isIntegralCurveOn_comp_sub
  given: {dt : Real}
  proof: by
  simpa using! isIntegralCurveOn_comp_add (dt := -dt)

中文:
引理 is整数egralCurveOn_comp_sub
  条件: {dt : 实数}
  证明: by
  simpa using! isIntegralCurveOn_comp_add (dt := -dt)

Depends on / 依赖: isIntegralCurveOn_comp_add
-/
lemma isIntegralCurveOn_comp_sub {dt : Real} :
    IsIntegralCurveOn (γ ∘ (· - dt)) (v ∘ (· - dt)) (dt +ᵥ s) ↔ IsIntegralCurveOn γ v s := by
  simpa using! isIntegralCurveOn_comp_add (dt := -dt)

/--
lemma `IsIntegralCurveOn.comp_sub` / 引理 `IsIntegralCurveOn.comp_sub`

English:
lemma IsIntegralCurveOn.comp_sub
  given: (hγ : IsIntegralCurveOn γ v s) (dt : Real)
  proof: isIntegralCurveOn_comp_sub.mpr hγ

中文:
引理 Is整数egralCurveOn.comp_sub
  条件: (hγ : Is整数egralCurveOn γ v s) (dt : 实数)
  证明: isIntegralCurveOn_comp_sub.mpr hγ

Depends on / 依赖: isIntegralCurveOn_comp_sub, isIntegralCurveOn_comp_sub.mpr
-/
lemma IsIntegralCurveOn.comp_sub (hγ : IsIntegralCurveOn γ v s) (dt : Real) :
    IsIntegralCurveOn (γ ∘ (· - dt)) (v ∘ (· - dt)) (dt +ᵥ s) :=
  isIntegralCurveOn_comp_sub.mpr hγ

/--
lemma `isIntegralCurveAt_comp_add` / 引理 `isIntegralCurveAt_comp_add`

English:
lemma isIntegralCurveAt_comp_add
  given: {dt : Real}
  proof: by
  simp_rw [isIntegralCurveAt_iff_exists_pos]
  congrm exists ε > 0, ?_
  convert! isIntegralCurveOn_comp_add
  simp [neg_add_eq_sub]

中文:
引理 is整数egralCurveAt_comp_add
  条件: {dt : 实数}
  证明: by
  simp_rw [isIntegralCurveAt_iff_exists_pos]
  congrm exists ε > 0, ?_
  convert! isIntegralCurveOn_comp_add
  simp [neg_add_eq_sub]

Depends on / 依赖: congrm, convert, isIntegralCurveAt_iff_exists_pos, isIntegralCurveOn_comp_add, neg_add_eq_sub, simp_rw
-/
lemma isIntegralCurveAt_comp_add {dt : Real} :
    IsIntegralCurveAt (γ ∘ (· + dt)) (v ∘ (· + dt)) (t₀ - dt) ↔ IsIntegralCurveAt γ v t₀ := by
  simp_rw [isIntegralCurveAt_iff_exists_pos]
  congrm exists ε > 0, ?_
  convert! isIntegralCurveOn_comp_add
  simp [neg_add_eq_sub]

/--
lemma `IsIntegralCurveAt.comp_add` / 引理 `IsIntegralCurveAt.comp_add`

English:
lemma IsIntegralCurveAt.comp_add
  given: (hγ : IsIntegralCurveAt γ v t₀) (dt : Real)
  proof: isIntegralCurveAt_comp_add.mpr hγ

中文:
引理 Is整数egralCurveAt.comp_add
  条件: (hγ : Is整数egralCurveAt γ v t₀) (dt : 实数)
  证明: isIntegralCurveAt_comp_add.mpr hγ

Depends on / 依赖: isIntegralCurveAt_comp_add, isIntegralCurveAt_comp_add.mpr
-/
lemma IsIntegralCurveAt.comp_add (hγ : IsIntegralCurveAt γ v t₀) (dt : Real) :
    IsIntegralCurveAt (γ ∘ (· + dt)) (v ∘ (· + dt)) (t₀ - dt) :=
  isIntegralCurveAt_comp_add.mpr hγ

/--
lemma `isIntegralCurveAt_comp_sub` / 引理 `isIntegralCurveAt_comp_sub`

English:
lemma isIntegralCurveAt_comp_sub
  given: {dt : Real}
  proof: by
  simpa using! isIntegralCurveAt_comp_add (dt := -dt)

中文:
引理 is整数egralCurveAt_comp_sub
  条件: {dt : 实数}
  证明: by
  simpa using! isIntegralCurveAt_comp_add (dt := -dt)

Depends on / 依赖: isIntegralCurveAt_comp_add
-/
lemma isIntegralCurveAt_comp_sub {dt : Real} :
    IsIntegralCurveAt (γ ∘ (· - dt)) (v ∘ (· - dt)) (t₀ + dt) ↔ IsIntegralCurveAt γ v t₀ := by
  simpa using! isIntegralCurveAt_comp_add (dt := -dt)

/--
lemma `IsIntegralCurveAt.comp_sub` / 引理 `IsIntegralCurveAt.comp_sub`

English:
lemma IsIntegralCurveAt.comp_sub
  given: (hγ : IsIntegralCurveAt γ v t₀) (dt : Real)
  proof: isIntegralCurveAt_comp_sub.mpr hγ

中文:
引理 Is整数egralCurveAt.comp_sub
  条件: (hγ : Is整数egralCurveAt γ v t₀) (dt : 实数)
  证明: isIntegralCurveAt_comp_sub.mpr hγ

Depends on / 依赖: isIntegralCurveAt_comp_sub, isIntegralCurveAt_comp_sub.mpr
-/
lemma IsIntegralCurveAt.comp_sub (hγ : IsIntegralCurveAt γ v t₀) (dt : Real) :
    IsIntegralCurveAt (γ ∘ (· - dt)) (v ∘ (· - dt)) (t₀ + dt) :=
  isIntegralCurveAt_comp_sub.mpr hγ

/--
lemma `IsIntegralCurve.comp_add` / 引理 `IsIntegralCurve.comp_add`

English:
lemma IsIntegralCurve.comp_add
  given: (hγ : IsIntegralCurve γ v) (dt : Real)
  proof: by
  rw [← isIntegralCurveOn_univ] at *
  simpa using hγ.comp_add dt

中文:
引理 Is整数egralCurve.comp_add
  条件: (hγ : Is整数egralCurve γ v) (dt : 实数)
  证明: by
  rw [← isIntegralCurveOn_univ] at *
  simpa using hγ.comp_add dt

Depends on / 依赖: comp_add, isIntegralCurveOn_univ
-/
lemma IsIntegralCurve.comp_add (hγ : IsIntegralCurve γ v) (dt : Real) :
    IsIntegralCurve (γ ∘ (· + dt)) (v ∘ (· + dt)) := by
  rw [← isIntegralCurveOn_univ] at *
  simpa using hγ.comp_add dt

/--
lemma `isIntegralCurve_comp_add` / 引理 `isIntegralCurve_comp_add`

English:
lemma isIntegralCurve_comp_add
  given: {dt : Real}
  proof: by
  simp_rw [← isIntegralCurveOn_univ]
  convert! isIntegralCurveOn_comp_add
  simp

中文:
引理 is整数egralCurve_comp_add
  条件: {dt : 实数}
  证明: by
  simp_rw [← isIntegralCurveOn_univ]
  convert! isIntegralCurveOn_comp_add
  simp

Depends on / 依赖: convert, isIntegralCurveOn_comp_add, isIntegralCurveOn_univ, simp_rw
-/
lemma isIntegralCurve_comp_add {dt : Real} :
    IsIntegralCurve (γ ∘ (· + dt)) (v ∘ (· + dt)) ↔ IsIntegralCurve γ v := by
  simp_rw [← isIntegralCurveOn_univ]
  convert! isIntegralCurveOn_comp_add
  simp

/--
lemma `isIntegralCurve_comp_sub` / 引理 `isIntegralCurve_comp_sub`

English:
lemma isIntegralCurve_comp_sub
  given: {dt : Real}
  proof: by
  simpa using! isIntegralCurve_comp_add (dt := -dt)

中文:
引理 is整数egralCurve_comp_sub
  条件: {dt : 实数}
  证明: by
  simpa using! isIntegralCurve_comp_add (dt := -dt)

Depends on / 依赖: isIntegralCurve_comp_add
-/
lemma isIntegralCurve_comp_sub {dt : Real} :
    IsIntegralCurve (γ ∘ (· - dt)) (v ∘ (· - dt)) ↔ IsIntegralCurve γ v := by
  simpa using! isIntegralCurve_comp_add (dt := -dt)

/--
lemma `IsIntegralCurve.comp_sub` / 引理 `IsIntegralCurve.comp_sub`

English:
lemma IsIntegralCurve.comp_sub
  given: (hγ : IsIntegralCurve γ v) (dt : Real)
  proof: isIntegralCurve_comp_sub.mpr hγ

中文:
引理 Is整数egralCurve.comp_sub
  条件: (hγ : Is整数egralCurve γ v) (dt : 实数)
  证明: isIntegralCurve_comp_sub.mpr hγ

Depends on / 依赖: isIntegralCurve_comp_sub, isIntegralCurve_comp_sub.mpr
-/
lemma IsIntegralCurve.comp_sub (hγ : IsIntegralCurve γ v) (dt : Real) :
    IsIntegralCurve (γ ∘ (· - dt)) (v ∘ (· - dt)) :=
  isIntegralCurve_comp_sub.mpr hγ

end Translation

/-! ### Scaling lemmas -/

section Scaling

/--
lemma `IsIntegralCurveOn.comp_mul` / 引理 `IsIntegralCurveOn.comp_mul`

English:
lemma IsIntegralCurveOn.comp_mul
  given: (hγ : IsIntegralCurveOn γ v s) (a : Real)
  proof: fun t ht => by
  simp only [comp_apply, Pi.smul_apply]
  exact HasDerivWithinAt.scomp t (hγ (t * a) ht) (hasDerivAt_mul_const a).hasDerivWithinAt
    fun _ ht' => ht'

中文:
引理 Is整数egralCurveOn.comp_mul
  条件: (hγ : Is整数egralCurveOn γ v s) (a : 实数)
  证明: fun t ht => by
  simp only [comp_apply, Pi.smul_apply]
  exact HasDerivWithinAt.scomp t (hγ (t * a) ht) (hasDerivAt_mul_const a).hasDerivWithinAt
    fun _ ht' => ht'

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.scomp, Pi.smul_apply, comp_apply, hasDerivAt_mul_const, hasDerivWithinAt, smul_apply
-/
lemma IsIntegralCurveOn.comp_mul (hγ : IsIntegralCurveOn γ v s) (a : Real) :
    IsIntegralCurveOn (γ ∘ (· * a)) (a • v ∘ (· * a)) { t | t * a in s } := fun t ht => by
  simp only [comp_apply, Pi.smul_apply]
  exact HasDerivWithinAt.scomp t (hγ (t * a) ht) (hasDerivAt_mul_const a).hasDerivWithinAt
    fun _ ht' => ht'

/--
lemma `isIntegralCurveOn_comp_mul_ne_zero` / 引理 `isIntegralCurveOn_comp_mul_ne_zero`

English:
lemma isIntegralCurveOn_comp_mul_ne_zero
  given: {a : Real} (ha : a != 0)
  proof: by
  have heq : a⁻¹ • s = { t | t * a in s } := by
    ext t
    rw [mem_inv_smul_set_iff₀ ha]; rw [smul_eq_mul]; rw [mul_comm]
    rfl
  refine ⟨fun hγ => ?_, heq ▸ fun hγ => hγ.comp_mul a⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_o

中文:
引理 is整数egralCurveOn_comp_mul_ne_zero
  条件: {a : 实数} (ha : a != 0)
  证明: by
  have heq : a⁻¹ • s = { t | t * a in s } := by
    ext t
    rw [mem_inv_smul_set_iff₀ ha]; rw [smul_eq_mul]; rw [mul_comm]
    rfl
  refine ⟨fun hγ => ?_, heq ▸ fun hγ => hγ.comp_mul a⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_o

Depends on / 依赖: Pi.smul_apply, comp_apply, comp_mul, convert, div_self, inv_mul_eq_div, mul_assoc, mul_comm, mul_one, ofPred_mem_eq, one_smul, smul_apply, smul_eq_mul, smul_smul
-/
lemma isIntegralCurveOn_comp_mul_ne_zero {a : Real} (ha : a != 0) :
    IsIntegralCurveOn (γ ∘ (· * a)) (a • v ∘ (· * a)) (a⁻¹ • s) ↔ IsIntegralCurveOn γ v s := by
  have heq : a⁻¹ • s = { t | t * a in s } := by
    ext t
    rw [mem_inv_smul_set_iff₀ ha]; rw [smul_eq_mul]; rw [mul_comm]
    rfl
  refine ⟨fun hγ => ?_, heq ▸ fun hγ => hγ.comp_mul a⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · ext t
    simp only [comp_apply, Pi.smul_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one,
      smul_smul, one_smul]
  · simp only [mul_comm _ a⁻¹, ← smul_eq_mul, mem_inv_smul_set_iff₀ ha, smul_inv_smul₀ ha,
      ofPred_mem_eq]

/--
lemma `IsIntegralCurveAt.comp_mul_ne_zero` / 引理 `IsIntegralCurveAt.comp_mul_ne_zero`

English:
lemma IsIntegralCurveAt.comp_mul_ne_zero
  given: (hγ : IsIntegralCurveAt γ v t₀) {a : Real} (ha : a != 0)
  proof: by
  rw [isIntegralCurveAt_iff_exists_pos] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε / |a|, by positivity, ?_⟩
  convert! h.comp_mul a
  ext t
  rw [mem_ofPred_eq]; rw [Metric.mem_ball]; rw [Metric.mem_ball]; rw [Real.dist_eq]; rw [Real.dist_eq]; rw [lt_div_iff₀ (abs_pos.mpr ha)]; rw [← abs_mul]; r

中文:
引理 Is整数egralCurveAt.comp_mul_ne_zero
  条件: (hγ : Is整数egralCurveAt γ v t₀) {a : 实数} (ha : a != 0)
  证明: by
  rw [isIntegralCurveAt_iff_exists_pos] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε / |a|, by positivity, ?_⟩
  convert! h.comp_mul a
  ext t
  rw [mem_ofPred_eq]; rw [Metric.mem_ball]; rw [Metric.mem_ball]; rw [Real.dist_eq]; rw [Real.dist_eq]; rw [lt_div_iff₀ (abs_pos.mpr ha)]; rw [← abs_mul]; r

Depends on / 依赖: Metric, Metric.mem_ball, Real.dist_eq, abs_mul, abs_pos, abs_pos.mpr, comp_mul, convert, dist_eq, h.comp_mul, isIntegralCurveAt_iff_exists_pos, mem_ball, mem_ofPred_eq, sub_mul
-/
lemma IsIntegralCurveAt.comp_mul_ne_zero (hγ : IsIntegralCurveAt γ v t₀) {a : Real} (ha : a != 0) :
    IsIntegralCurveAt (γ ∘ (· * a)) (a • v ∘ (· * a)) (t₀ / a) := by
  rw [isIntegralCurveAt_iff_exists_pos] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε / |a|, by positivity, ?_⟩
  convert! h.comp_mul a
  ext t
  rw [mem_ofPred_eq]; rw [Metric.mem_ball]; rw [Metric.mem_ball]; rw [Real.dist_eq]; rw [Real.dist_eq]; rw [lt_div_iff₀ (abs_pos.mpr ha)]; rw [← abs_mul]; rw [sub_mul]; rw [div_mul_cancel₀ _ ha]

/--
lemma `isIntegralCurveAt_comp_mul_ne_zero` / 引理 `isIntegralCurveAt_comp_mul_ne_zero`

English:
lemma isIntegralCurveAt_comp_mul_ne_zero
  given: {a : Real} (ha : a != 0)
  proof: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul_ne_zero ha⟩
  convert! hγ.comp_mul_ne_zero (inv_ne_zero ha)
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · ext t
    simp only [comp_apply, Pi.smul_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one,
    

中文:
引理 is整数egralCurveAt_comp_mul_ne_zero
  条件: {a : 实数} (ha : a != 0)
  证明: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul_ne_zero ha⟩
  convert! hγ.comp_mul_ne_zero (inv_ne_zero ha)
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · ext t
    simp only [comp_apply, Pi.smul_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one,
    

Depends on / 依赖: Pi.smul_apply, comp_apply, comp_mul_ne_zero, convert, div_inv_eq_mul, div_self, inv_mul_eq_div, inv_ne_zero, mul_assoc, mul_one, one_smul, smul_apply, smul_smul
-/
lemma isIntegralCurveAt_comp_mul_ne_zero {a : Real} (ha : a != 0) :
    IsIntegralCurveAt (γ ∘ (· * a)) (a • v ∘ (· * a)) (t₀ / a) ↔ IsIntegralCurveAt γ v t₀ := by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul_ne_zero ha⟩
  convert! hγ.comp_mul_ne_zero (inv_ne_zero ha)
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · ext t
    simp only [comp_apply, Pi.smul_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one,
      smul_smul, one_smul]
  · simp only [div_inv_eq_mul, div_mul_cancel₀ _ ha]

/--
lemma `IsIntegralCurve.comp_mul` / 引理 `IsIntegralCurve.comp_mul`

English:
lemma IsIntegralCurve.comp_mul
  given: (hγ : IsIntegralCurve γ v) (a : Real)
  proof: by
  rw [← isIntegralCurveOn_univ] at *
  exact hγ.comp_mul _

中文:
引理 Is整数egralCurve.comp_mul
  条件: (hγ : Is整数egralCurve γ v) (a : 实数)
  证明: by
  rw [← isIntegralCurveOn_univ] at *
  exact hγ.comp_mul _

Depends on / 依赖: comp_mul, isIntegralCurveOn_univ
-/
lemma IsIntegralCurve.comp_mul (hγ : IsIntegralCurve γ v) (a : Real) :
    IsIntegralCurve (γ ∘ (· * a)) (a • v ∘ (· * a)) := by
  rw [← isIntegralCurveOn_univ] at *
  exact hγ.comp_mul _

/--
lemma `isIntegralCurve_comp_mul_ne_zero` / 引理 `isIntegralCurve_comp_mul_ne_zero`

English:
lemma isIntegralCurve_comp_mul_ne_zero
  given: {a : Real} (ha : a != 0)
  proof: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul _⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · ext t
    simp only [comp_apply, Pi.smul_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one,
      smul_smul, one_smul]

中文:
引理 is整数egralCurve_comp_mul_ne_zero
  条件: {a : 实数} (ha : a != 0)
  证明: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul _⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · ext t
    simp only [comp_apply, Pi.smul_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one,
      smul_smul, one_smul]

Depends on / 依赖: Pi.smul_apply, comp_apply, comp_mul, convert, div_self, inv_mul_eq_div, mul_assoc, mul_one, one_smul, smul_apply, smul_smul
-/
lemma isIntegralCurve_comp_mul_ne_zero {a : Real} (ha : a != 0) :
    IsIntegralCurve (γ ∘ (· * a)) (a • v ∘ (· * a)) ↔ IsIntegralCurve γ v := by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul _⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · ext t
    simp only [comp_apply, Pi.smul_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one,
      smul_smul, one_smul]

/--
lemma `isIntegralCurve_const` / 引理 `isIntegralCurve_const`

English:
lemma isIntegralCurve_const
  given: {x : E} (h : forall t, v t x = 0)
  statement: IsIntegralCurve (fun _ => x) v
  proof: fun t => (h t) ▸ hasDerivAt_const _ _

中文:
引理 is整数egralCurve_const
  条件: {x : E} (h : 对任意 t, v t x = 0)
  结论: Is整数egralCurve (fun _ => x) v
  证明: fun t => (h t) ▸ hasDerivAt_const _ _

Depends on / 依赖: hasDerivAt_const
-/
lemma isIntegralCurve_const {x : E} (h : forall t, v t x = 0) : IsIntegralCurve (fun _ => x) v :=
  fun t => (h t) ▸ hasDerivAt_const _ _

end Scaling
