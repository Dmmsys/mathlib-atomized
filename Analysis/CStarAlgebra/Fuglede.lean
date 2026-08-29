/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Complex.Liouville


/-! # The Fuglede–Putnam–Rosenblum theorem

Let `A` be a C⋆-algebra, and let `a b x : A`. The Fuglede–Putnam–Rosenblum theorem states that
if `a` and `b` are normal and `x` intertwines `a` and `b` (i.e., `SemiconjBy x a b`, that is,
`x * a = b * x`), then `x` also intertwines `star a` and `star b`. Fuglede's original result
[fuglede1950] was for `a = b` (i.e., if `x` commutes with `a`, then `x` also commutes with
`star a`), and Putnam [putnam1951] extended it to intertwining elements.

Rosenblum [rosenblum1958] later gave the elementary proof formalized here using Liouville's theorem
which proceeds as follows. Consider the map `f : ℂ → A` given by
`z ↦ exp (z • star b) * x * exp (z • star (-a))`.
When `x` intertwines `a` and `b` (i.e., `SemiconjBy x a b`), then it also intertwines
`exp (star z • a)` and `exp (star z • b)`. Then the map `f` can be realized as `z ↦ u * x * v` for
fixed unitaries `u` and `v`. In fact, `u = exp (I • 2 • ℑ (z • star b))` and
`v = exp (I • 2 • ℑ (star z • a))`; it is here that normality of `a` and `b` is used to ensure that
`exp (star z • a) * exp (- star (z • a)) = exp (I • 2 • ℑ (star z • a))` and likewise for `b`.
Therefore `‖f z‖ = ‖x‖` for all `z`, and since `f` is clearly entire, by Liouville's theorem,
`f` is constant. Evaluating at `z = 0` proves that `f z = x` for all `z`. Therefore,
`exp (z • star b) * x = x * exp (z • star a)`. Differentiating both sides and evaluating at `z = 0`
proves that `star b * x = x * star a`, as desired.

In a follow-up paper, Cater [cater1961] proved a number of related results using similar techniques.
We include one of these below, `isStarNormal_iff_forall_exp_mul_exp_mem_unitary`,
but the proof is independent of the Fuglede–Putnam–Rosenblum theorem.

## Main results

+ `fuglede_putnam_rosenblum`: If `a` and `b` are normal elements in a C⋆-algebra `A` which
  are interwined by `x` (i.e., `SemiconjBy x a b`, that is, `x * a = b * x`), then `star a` and
  `star b` are also intertwined by `x`.
+ `isStarNormal_iff_forall_exp_mul_exp_mem_unitary`: A characterization of normal elements in a
  C⋆-algebra in terms of exponentials.

## References

+ [fuglede1950] Bent Fuglede, "A commutativity theorem for normal operators"
+ [putnam1951] C. R. Putnam, "On normal operators in Hilbert space"
+ [rosenblum1958] M. Rosenblum, "On a theorem of Fuglede and Putnam"
+ [cater1961] S. Cater, "Observations on a paper by Rosenblum"

-/


open NormedSpace selfAdjoint Bornology Complex
open scoped ComplexStarModule

variable {A : Type*} [CStarAlgebra A] {a b x : A} [IsStarNormal a] [IsStarNormal b]

/--
Definition of `expMulMulExp` / `expMulMulExp` 的定义

English:
definition expMulMulExp
  signature: (a b x : A) (z : Complex)
  body: exp (z • star b) * x * exp (z • star (-a))

中文:
定义 expMulMulExp
  签名: (a b x : A) (z : Complex)
  定义体: exp (z • star b) * x * exp (z • star (-a))
-/
noncomputable def expMulMulExp (a b x : A) (z : Complex) : A := exp (z • star b) * x * exp (z • star (-a))

/--
lemma `expMulMulExp_eq_expUnitary_mul_mul_expUnitary` / 引理 `expMulMulExp_eq_expUnitary_mul_mul_expUnitary`

English:
lemma expMulMulExp_eq_expUnitary_mul_mul_expUnitary
  given: (h : SemiconjBy x a b) (z : Complex)
  proof: by
  let _ : NormedAlgebra Rat A := .restrictScalars Rat Complex A
  nth_rw 1 [expMulMulExp, ← (h.smul_right (star z)).exp_neg_mul_mul_exp_eq_self]
  simp_rw [← mul_assoc, mul_assoc (_ * _ * x)]
  congr!
  all_goals
    simp [imaginaryPart_apply_coe, smul_comm (2 : Real) I, smul_smul I I, sub_eq_add

中文:
引理 expMulMulExp_eq_expUnitary_mul_mul_expUnitary
  条件: (h : SemiconjBy x a b) (z : Complex)
  证明: by
  let _ : NormedAlgebra Rat A := .restrictScalars Rat Complex A
  nth_rw 1 [expMulMulExp, ← (h.smul_right (star z)).exp_neg_mul_mul_exp_eq_self]
  simp_rw [← mul_assoc, mul_assoc (_ * _ * x)]
  congr!
  all_goals
    simp [imaginaryPart_apply_coe, smul_comm (2 : Real) I, smul_smul I I, sub_eq_add

Depends on / 依赖: Commute, Commute.neg_right, Commute.smul_right, NormedAlgebra, all_goals, expMulMulExp, exp_add_of_commute, exp_neg_mul_mul_exp_eq_self, h.smul_right, imaginaryPart_apply_coe, mul_assoc, neg_right, nth_rw, restrictScalars, simp_rw, smul_comm, smul_right, smul_smul, sub_eq_add_neg
-/
lemma expMulMulExp_eq_expUnitary_mul_mul_expUnitary (h : SemiconjBy x a b) (z : Complex) :
    expMulMulExp a b x z =
      expUnitary ((2 : Real) • ℑ (z • star b)) * x * expUnitary ((2 : Real) • ℑ (star z • a)) := by
  let _ : NormedAlgebra Rat A := .restrictScalars Rat Complex A
  nth_rw 1 [expMulMulExp, ← (h.smul_right (star z)).exp_neg_mul_mul_exp_eq_self]
  simp_rw [← mul_assoc, mul_assoc (_ * _ * x)]
  congr!
  all_goals
    simp [imaginaryPart_apply_coe, smul_comm (2 : Real) I, smul_smul I I, sub_eq_add_neg]
    grind [exp_add_of_commute, Commute.smul_right, Commute.neg_right]

/--
lemma `expMulMulExp_const` / 引理 `expMulMulExp_const`

English:
lemma expMulMulExp_const
  given: (h : SemiconjBy x a b) (z : Complex)
  statement: expMulMulExp a b x z = x
  proof: by
  have hf : Differentiable Complex (expMulMulExp a b x : Complex -> A) := by unfold expMulMulExp; fun_prop
  have : IsBounded (Set.range (expMulMulExp a b x)) := by
.subset apply Metric.isBounded_sphere (x := (0 : A)) (r := ‖x‖)
    rintro - ⟨z, hz, rfl⟩
    rw [mem_sphere_iff_norm]; rw [sub_zero

中文:
引理 expMulMulExp_const
  条件: (h : SemiconjBy x a b) (z : Complex)
  结论: expMulMulExp a b x z = x
  证明: by
  have hf : Differentiable Complex (expMulMulExp a b x : Complex -> A) := by unfold expMulMulExp; fun_prop
  have : IsBounded (Set.range (expMulMulExp a b x)) := by
.subset apply Metric.isBounded_sphere (x := (0 : A)) (r := ‖x‖)
    rintro - ⟨z, hz, rfl⟩
    rw [mem_sphere_iff_norm]; rw [sub_zero

Depends on / 依赖: CStarRing, CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary, Differentiable, IsBounded, Metric, Metric.isBounded_sphere, Set.range, apply_eq_apply_of_bounded, expMulMulExp, expMulMulExp_eq_expUnitary_mul_mul_expUnitary, fun_prop, hf.apply_eq_apply_of_bounded, isBounded_sphere, mem_sphere_iff_norm, norm_coe_unitary_mul, norm_mul_coe_unitary, sub_zero, subset
-/
lemma expMulMulExp_const (h : SemiconjBy x a b) (z : Complex) : expMulMulExp a b x z = x := by
  have hf : Differentiable Complex (expMulMulExp a b x : Complex -> A) := by unfold expMulMulExp; fun_prop
  have : IsBounded (Set.range (expMulMulExp a b x)) := by
.subset apply Metric.isBounded_sphere (x := (0 : A)) (r := ‖x‖)
    rintro - ⟨z, hz, rfl⟩
    rw [mem_sphere_iff_norm]; rw [sub_zero]; rw [expMulMulExp_eq_expUnitary_mul_mul_expUnitary h z]; rw [CStarRing.norm_mul_coe_unitary]; rw [CStarRing.norm_coe_unitary_mul]
  simpa [expMulMulExp] using hf.apply_eq_apply_of_bounded this z 0

/--
lemma `SemiconjBy.star_right_of_unital` / 引理 `SemiconjBy.star_right_of_unital`

English:
lemma SemiconjBy.star_right_of_unital
  given: (h : SemiconjBy x a b)
  proof: by
  suffices key : forall z : Complex, x * exp (z • star a) = exp (z • star b) * x by
    have (a : A) : HasDerivAt (fun z : Complex => exp (z • a)) a 0 := by
      simpa using hasDerivAt_exp_smul_const a (0 : Complex)
.unique apply (this (star a)).const_mul x
    simpa [key] using (this (star b)).

中文:
引理 SemiconjBy.star_right_of_unital
  条件: (h : SemiconjBy x a b)
  证明: by
  suffices key : forall z : Complex, x * exp (z • star a) = exp (z • star b) * x by
    have (a : A) : HasDerivAt (fun z : Complex => exp (z • a)) a 0 := by
      simpa using hasDerivAt_exp_smul_const a (0 : Complex)
.unique apply (this (star a)).const_mul x
    simpa [key] using (this (star b)).

Depends on / 依赖: HasDerivAt, NormedAlgebra, const_mul, expMulMulExp, expMulMulExp_const, hasDerivAt_exp_smul_const, invOf_exp, invertibleExp, mul_assoc, mul_const, restrictScalars, unique
-/
lemma SemiconjBy.star_right_of_unital (h : SemiconjBy x a b) :
    SemiconjBy x (star a) (star b) := by
  suffices key : forall z : Complex, x * exp (z • star a) = exp (z • star b) * x by
    have (a : A) : HasDerivAt (fun z : Complex => exp (z • a)) a 0 := by
      simpa using hasDerivAt_exp_smul_const a (0 : Complex)
.unique apply (this (star a)).const_mul x
    simpa [key] using (this (star b)).mul_const x
  intro z
  let _ : NormedAlgebra Rat A := .restrictScalars Rat Complex A
  let _ := invertibleExp (z • star a)
  simpa [← mul_assoc, ← invOf_exp, expMulMulExp] using
    congr($(expMulMulExp_const h z) * exp (z • star a)).symm

/-- **Fuglede–Putnam–Rosenblum**: If `a` and `b` are normal elements in a C⋆-algebra `A` which
are interwined by `x`, then `star a` and `star b` are also intertwined by `x`. -/
public lemma SemiconjBy.star_right {A : Type*} [NonUnitalCStarAlgebra A] {a b x : A}
    (ha : IsStarNormal a) (hb : IsStarNormal b) (h : SemiconjBy x a b) :
    SemiconjBy x (star a) (star b) := by
  apply Unitization.inr_injective (R := Complex)
  simp only [Unitization.inr_mul, Unitization.inr_star]
  apply SemiconjBy.star_right_of_unital
  simpa [SemiconjBy] using mod_cast h.eq

public alias fuglede_putnam_rosenblum := SemiconjBy.star_right

/-- **Fuglede–Putnam–Rosenblum**: If `a` is a normal element in a C⋆-algebra `A` which
commutes with `x`, then `star a` commutes with `x`. -/
public lemma IsStarNormal.commute_star_right {A : Type*} [NonUnitalCStarAlgebra A] {a x : A}
    (ha : IsStarNormal a) (h : Commute x a) :
    Commute x (star a) :=
  h.semiconjBy.star_right ha ha

/-- **Fuglede–Putnam–Rosenblum**: If `a` is a normal element in a C⋆-algebra `A` which
commutes with `x`, then `star a` commutes with `x`. -/
public lemma IsStarNormal.commute_star_left {A : Type*} [NonUnitalCStarAlgebra A] {a x : A}
    (ha : IsStarNormal a) (h : Commute a x) :
    Commute (star a) x :=
.symm ha.commute_star_right h.symm

/-- A characterization of normal elements in a C⋆-algebra in terms of exponentials. -/
public lemma isStarNormal_iff_forall_exp_mul_exp_mem_unitary {a : A} :
    IsStarNormal a ↔ forall x : Real, exp (x • a) * exp (-x • star a) in unitary A := by
  let _ : NormedAlgebra Rat A := .restrictScalars Rat Complex A
  have : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat A
  refine ⟨fun ha x => ?_, fun ha => ?_⟩
  /- If `a` is normal, then clearly `exp (x • a) * exp (- x • star a) = exp (I • x • 2 • ℑ a)`
  and the latter is clearly an exponential unitary. -/
  · convert! (selfAdjoint.expUnitary (x • (2 : Real) • ℑ a)).2
.smul_right (-x) .symm.smul_left x have hcomm := star_comm_self (x := a)
    rw [← exp_add_of_commute hcomm]
    simp [imaginaryPart_apply_coe, smul_comm (2 : Real) I, smul_comm x I, smul_smul I I, smul_add x,
      sub_eq_add_neg]
  /- Take any `x : ℝ` and suppose `u := exp (x • a) * exp (- x • a)` is unitary. Then
  `exp (- x • a) * exp (x • star a) = star u = u⁻¹ = exp (x • star a) * exp (- x • a)`. -/
  · have key : forall x : Real, exp (- x • a) * exp (x • star a) = exp (x • star a) * exp (- x • a) := by
      intro x
      let u : unitary A := ⟨_, ha x⟩
      convert! congr(($(Unitary.star_eq_inv u) : A))
      · simp [u, star_exp]
      · simp_rw [u, ← Unitary.val_inv_toUnits_apply, neg_smul, ← Units.mul_eq_one_iff_eq_inv,
          Unitary.val_toUnits_apply]
        let _ := invertibleExp (𝔸 := A)
        rw [mul_assoc]
        simp [← invOf_exp]
    /- Compute the second derivative with respect to `x` of each side of this expression and
    evaluate at `x = 0`. -/
    have h_deriv (a b c : A) (y : Real) :
        deriv (fun x : Real => exp (x • a) * c * exp (x • b)) y =
          exp (y • a) * (a * c + c * b) * exp (y • b) := by
      rw [mul_add]; rw [add_mul]; rw [← mul_assoc _ a]; rw [← mul_assoc _ c b]; rw [mul_assoc _ b]
.mul exact (hasDerivAt_exp_smul_const a y).mul_const c
.deriv (hasDerivAt_exp_smul_const' b y)
    have h_deriv₂ (a b : A) :
        deriv (fun y => deriv (fun x : Real => exp (x • a) * exp (x • b)) y) 0 =
          a ^ 2 + 2 • (a * b) + b ^ 2 := by
      conv => enter [1, 1, y, 1, x, 1]; rw [← mul_one (exp (x • a))]
      simp_rw [h_deriv, zero_smul, NormedSpace.exp_zero, mul_one, one_mul]
      noncomm_ring
    have h₃ := h_deriv₂ (-a) (star a)
    have h₄ := h_deriv₂ (star a) (-a)
    simp only [smul_neg, even_two, Even.neg_pow, neg_smul] at h₃ h₄ key
    /- By `key`, these second derivatives evaluated at zero must be equal, so we find
    `a ^ 2 + 2 • (- a * star a) + (star a) ^ 2 = star ^ 2 + 2 • (star a * a) + a ^ 2`,
    and then elementary algebra shows `star a * a = a * star a`, so `a` is normal. -/
    simp_rw [key] at h₃
    rw [h₃] at h₄
    rw [isStarNormal_iff]; rw [commute_iff_eq]
    apply nsmul_right_injective two_ne_zero
    rw [← sub_eq_zero] at h₄ ⊢
    rw [← h₄]
    noncomm_ring
