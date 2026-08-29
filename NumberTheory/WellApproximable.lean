/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Dynamics.Ergodic.AddCircle
public import Mathlib.MeasureTheory.Covering.LiminfLimsup

/-!
# Well-approximable numbers and Gallagher's ergodic theorem

Gallagher's ergodic theorem is a result in metric number theory. It thus belongs to that branch of
mathematics concerning arithmetic properties of real numbers which hold almost everywhere with
respect to the Lebesgue measure.

Gallagher's theorem concerns the approximation of real numbers by rational numbers. The input is a
sequence of distances `δ₁, δ₂, ...`, and the theorem concerns the set of real numbers `x` for which
there are infinitely many solutions to:
$$
  |x - m/n| < δₙ,
$$
where the rational number `m/n` is in lowest terms. The result is that for any `δ`, this set is
either almost all `x` or almost no `x`.

This result was proved by Gallagher in 1959
[P. Gallagher, *Approximation by reduced fractions*][Gallagher1961]. It is formalised here as
`AddCircle.addWellApproximable_ae_empty_or_univ` except with `x` belonging to the circle `ℝ ⧸ ℤ`
since this turns out to be more natural.

Given a particular `δ`, the Duffin-Schaeffer conjecture (now a theorem) gives a criterion for
deciding which of the two cases in the conclusion of Gallagher's theorem actually occurs. It was
proved by Koukoulopoulos and Maynard in 2019
[D. Koukoulopoulos, J. Maynard, *On the Duffin-Schaeffer conjecture*][KoukoulopoulosMaynard2020].
We do *not* include a formalisation of the Koukoulopoulos-Maynard result here.

## Main definitions and results:

* `approxOrderOf`: in a seminormed group `A`, given `n : ℕ` and `δ : ℝ`, `approxOrderOf A n δ`
  is the set of elements within a distance `δ` of a point of order `n`.
* `wellApproximable`: in a seminormed group `A`, given a sequence of distances `δ₁, δ₂, ...`,
  `wellApproximable A δ` is the limsup as `n → ∞` of the sets `approxOrderOf A n δₙ`. Thus, it
  is the set of points that lie in infinitely many of the sets `approxOrderOf A n δₙ`.
* `AddCircle.addWellApproximable_ae_empty_or_univ`: *Gallagher's ergodic theorem* says that for
  the (additive) circle `𝕊`, for any sequence of distances `δ`, the set
  `addWellApproximable 𝕊 δ` is almost empty or almost full.
* `NormedAddCommGroup.exists_norm_nsmul_le`: a general version of Dirichlet's approximation theorem
* `AddCircle.exists_norm_nsmul_le`: Dirichlet's approximation theorem

## TODO

The hypothesis `hδ` in `AddCircle.addWellApproximable_ae_empty_or_univ` can be dropped.
An elementary (non-measure-theoretic) argument shows that if `¬ hδ` holds then
`addWellApproximable 𝕊 δ = univ` (provided `δ` is non-negative).

Use `AddCircle.exists_norm_nsmul_le` to prove:
`addWellApproximable 𝕊 (fun n ↦ 1 / n^2) = { ξ | ¬ IsOfFinAddOrder ξ }`
(which is equivalent to `Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational`).
-/

@[expose] public section


open Set Filter Function Metric MeasureTheory

open scoped MeasureTheory Topology Pointwise

/-- In a seminormed group `A`, given `n : ℕ` and `δ : ℝ`, `approxOrderOf A n δ` is the set of
elements within a distance `δ` of a point of order `n`. -/
@[to_additive /-- In a seminormed additive group `A`, given `n : ℕ` and `δ : ℝ`,
`approxAddOrderOf A n δ` is the set of elements within a distance `δ` of a point of order `n`. -/]
/--
Definition of `approxOrderOf` / `approxOrderOf` 的定义

English:
definition approxOrderOf
  signature: (A : Type*) [SeminormedGroup A] (n : Nat) (δ : Real)
  body: thickening δ {y | orderOf y = n}

@[to_additive mem_approx_add_orderOf_iff]

中文:
定义 approxOrderOf
  签名: (A : 类型) [半赋范群 A] (n : 自然数) (δ : 实数)
  定义体: thickening δ {y | orderOf y = n}

@[to_additive mem_approx_add_orderOf_iff]

Depends on / 依赖: orderOf, thickening
-/
def approxOrderOf (A : Type*) [SeminormedGroup A] (n : Nat) (δ : Real) : Set A :=
  thickening δ {y | orderOf y = n}

@[to_additive mem_approx_add_orderOf_iff]
/--
theorem `mem_approxOrderOf_iff` / 定理 `mem_approxOrderOf_iff`

English:
theorem mem_approxOrderOf_iff
  given: {A : Type*} [SeminormedGroup A] {n : Nat} {δ : Real} {a : A}
  proof: by
  simp only [approxOrderOf, thickening_eq_biUnion_ball, mem_iUnion₂, mem_ofPred_eq, exists_prop]

中文:
定理 mem_approxOrderOf_iff
  条件: {A : 类型} [半赋范群 A] {n : 自然数} {δ : 实数} {a : A}
  证明: by
  simp only [approxOrderOf, thickening_eq_biUnion_ball, mem_iUnion₂, mem_ofPred_eq, exists_prop]

Depends on / 依赖: approxOrderOf, exists_prop, mem_ofPred_eq, thickening_eq_biUnion_ball
-/
theorem mem_approxOrderOf_iff {A : Type*} [SeminormedGroup A] {n : Nat} {δ : Real} {a : A} :
    a in approxOrderOf A n δ ↔ exists b : A, orderOf b = n ∧ a in ball b δ := by
  simp only [approxOrderOf, thickening_eq_biUnion_ball, mem_iUnion₂, mem_ofPred_eq, exists_prop]

/-- In a seminormed group `A`, given a sequence of distances `δ₁, δ₂, ...`, `wellApproximable A δ`
is the limsup as `n → ∞` of the sets `approxOrderOf A n δₙ`. Thus, it is the set of points that
lie in infinitely many of the sets `approxOrderOf A n δₙ`. -/
@[to_additive addWellApproximable /-- In a seminormed additive group `A`, given a sequence of
distances `δ₁, δ₂, ...`, `addWellApproximable A δ` is the limsup as `n → ∞` of the sets
`approxAddOrderOf A n δₙ`. Thus, it is the set of points that lie in infinitely many of the sets
`approxAddOrderOf A n δₙ`. -/]
/--
Definition of `wellApproximable` / `wellApproximable` 的定义

English:
definition wellApproximable
  signature: (A : Type*) [SeminormedGroup A] (δ : Nat -> Real)
  body: blimsup (fun n => approxOrderOf A n (δ n)) atTop fun n => 0 < n

@[to_additive mem_add_wellApproximable_iff]

中文:
定义 wellApproximable
  签名: (A : 类型) [半赋范群 A] (δ : 自然数 -> 实数)
  定义体: blimsup (fun n => approxOrderOf A n (δ n)) atTop fun n => 0 < n

@[to_additive mem_add_wellApproximable_iff]

Depends on / 依赖: approxOrderOf, blimsup
-/
def wellApproximable (A : Type*) [SeminormedGroup A] (δ : Nat -> Real) : Set A :=
  blimsup (fun n => approxOrderOf A n (δ n)) atTop fun n => 0 < n

@[to_additive mem_add_wellApproximable_iff]
/--
theorem `mem_wellApproximable_iff` / 定理 `mem_wellApproximable_iff`

English:
theorem mem_wellApproximable_iff
  given: {A : Type*} [SeminormedGroup A] {δ : Nat -> Real} {a : A}
  proof: Iff.rfl

中文:
定理 mem_wellApproximable_iff
  条件: {A : 类型} [半赋范群 A] {δ : 自然数 -> 实数} {a : A}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_wellApproximable_iff {A : Type*} [SeminormedGroup A] {δ : Nat -> Real} {a : A} :
    a in wellApproximable A δ ↔
      a in blimsup (fun n => approxOrderOf A n (δ n)) atTop fun n => 0 < n :=
  Iff.rfl

namespace approxOrderOf

variable {A : Type*} [SeminormedCommGroup A] {a : A} {m n : Nat} (δ : Real)

@[to_additive]
/--
theorem `image_pow_subset_of_coprime` / 定理 `image_pow_subset_of_coprime`

English:
theorem image_pow_subset_of_coprime
  given: (hm : 0 < m) (hmn : n.Coprime m)
  proof: by
  rintro - ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hab⟩ := mem_approxOrderOf_iff.mp ha
  replace hb : b ^ m in {u : A | orderOf u = n} := by
    rw [← hb] at hmn ⊢; exact hmn.orderOf_pow
  apply ball_subset_thickening hb ((m : Real) • δ)
  convert! pow_mem_ball hm hab using 1
  simp only [nsmul_eq_mul, smu

中文:
定理 image_pow_subset_of_coprime
  条件: (hm : 0 < m) (hmn : n.Coprime m)
  证明: by
  rintro - ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hab⟩ := mem_approxOrderOf_iff.mp ha
  replace hb : b ^ m in {u : A | orderOf u = n} := by
    rw [← hb] at hmn ⊢; exact hmn.orderOf_pow
  apply ball_subset_thickening hb ((m : Real) • δ)
  convert! pow_mem_ball hm hab using 1
  simp only [nsmul_eq_mul, smu

Depends on / 依赖: ball_subset_thickening, convert, hmn.orderOf_pow, mem_approxOrderOf_iff, mem_approxOrderOf_iff.mp, nsmul_eq_mul, orderOf, orderOf_pow, pow_mem_ball, replace, smul_eq_mul
-/
theorem image_pow_subset_of_coprime (hm : 0 < m) (hmn : n.Coprime m) :
    (fun (y : A) => y ^ m) '' approxOrderOf A n δ subseteq approxOrderOf A n (m * δ) := by
  rintro - ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hab⟩ := mem_approxOrderOf_iff.mp ha
  replace hb : b ^ m in {u : A | orderOf u = n} := by
    rw [← hb] at hmn ⊢; exact hmn.orderOf_pow
  apply ball_subset_thickening hb ((m : Real) • δ)
  convert! pow_mem_ball hm hab using 1
  simp only [nsmul_eq_mul, smul_eq_mul]

@[to_additive]
/--
theorem `image_pow_subset` / 定理 `image_pow_subset`

English:
theorem image_pow_subset
  given: (n : Nat) (hm : 0 < m)
  proof: by
  rintro - ⟨a, ha, rfl⟩
  obtain ⟨b, hb : orderOf b = n * m, hab : a in ball b δ⟩ := mem_approxOrderOf_iff.mp ha
  replace hb : b ^ m in {y : A | orderOf y = n} := by
    rw [mem_ofPred_eq]; rw [orderOf_pow' b hm.ne']; rw [hb]; rw [Nat.gcd_mul_left_left]; rw [n.mul_div_cancel hm]
  apply ball_sub

中文:
定理 image_pow_subset
  条件: (n : 自然数) (hm : 0 < m)
  证明: by
  rintro - ⟨a, ha, rfl⟩
  obtain ⟨b, hb : orderOf b = n * m, hab : a in ball b δ⟩ := mem_approxOrderOf_iff.mp ha
  replace hb : b ^ m in {y : A | orderOf y = n} := by
    rw [mem_ofPred_eq]; rw [orderOf_pow' b hm.ne']; rw [hb]; rw [Nat.gcd_mul_left_left]; rw [n.mul_div_cancel hm]
  apply ball_sub

Depends on / 依赖: Nat.gcd_mul_left_left, ball_subset_thickening, convert, gcd_mul_left_left, hm.ne, mem_approxOrderOf_iff, mem_approxOrderOf_iff.mp, mem_ofPred_eq, mul_div_cancel, n.mul_div_cancel, nsmul_eq_mul, orderOf, orderOf_pow, pow_mem_ball, replace
-/
theorem image_pow_subset (n : Nat) (hm : 0 < m) :
    (fun (y : A) => y ^ m) '' approxOrderOf A (n * m) δ subseteq approxOrderOf A n (m * δ) := by
  rintro - ⟨a, ha, rfl⟩
  obtain ⟨b, hb : orderOf b = n * m, hab : a in ball b δ⟩ := mem_approxOrderOf_iff.mp ha
  replace hb : b ^ m in {y : A | orderOf y = n} := by
    rw [mem_ofPred_eq]; rw [orderOf_pow' b hm.ne']; rw [hb]; rw [Nat.gcd_mul_left_left]; rw [n.mul_div_cancel hm]
  apply ball_subset_thickening hb (m * δ)
  convert! pow_mem_ball hm hab using 1
  simp only [nsmul_eq_mul]

@[to_additive]
/--
theorem `smul_subset_of_coprime` / 定理 `smul_subset_of_coprime`

English:
theorem smul_subset_of_coprime
  given: (han : (orderOf a).Coprime n)
  proof: by
  simp_rw [approxOrderOf, thickening_eq_biUnion_ball, ← image_smul, image_iUnion₂, image_smul,
    smul_ball'', smul_eq_mul, mem_ofPred_eq]
  refine iUnion₂_subset_iff.mpr fun b hb c hc => ?_
  simp only [mem_iUnion, exists_prop]
  refine ⟨a * b, ?_, hc⟩
  rw [← hb] at han ⊢
  exact (Commute.all 

中文:
定理 smul_subset_of_coprime
  条件: (han : (orderOf a).Coprime n)
  证明: by
  simp_rw [approxOrderOf, thickening_eq_biUnion_ball, ← image_smul, image_iUnion₂, image_smul,
    smul_ball'', smul_eq_mul, mem_ofPred_eq]
  refine iUnion₂_subset_iff.mpr fun b hb c hc => ?_
  simp only [mem_iUnion, exists_prop]
  refine ⟨a * b, ?_, hc⟩
  rw [← hb] at han ⊢
  exact (Commute.all 

Depends on / 依赖: Commute, Commute.all, _subset_iff.mpr, approxOrderOf, exists_prop, image_smul, mem_iUnion, mem_ofPred_eq, orderOf_mul_eq_mul_orderOf_of_coprime, simp_rw, smul_ball, smul_eq_mul, thickening_eq_biUnion_ball
-/
theorem smul_subset_of_coprime (han : (orderOf a).Coprime n) :
    a • approxOrderOf A n δ subseteq approxOrderOf A (orderOf a * n) δ := by
  simp_rw [approxOrderOf, thickening_eq_biUnion_ball, ← image_smul, image_iUnion₂, image_smul,
    smul_ball'', smul_eq_mul, mem_ofPred_eq]
  refine iUnion₂_subset_iff.mpr fun b hb c hc => ?_
  simp only [mem_iUnion, exists_prop]
  refine ⟨a * b, ?_, hc⟩
  rw [← hb] at han ⊢
  exact (Commute.all a b).orderOf_mul_eq_mul_orderOf_of_coprime han

@[to_additive vadd_eq_of_mul_dvd]
/--
theorem `smul_eq_of_mul_dvd` / 定理 `smul_eq_of_mul_dvd`

English:
theorem smul_eq_of_mul_dvd
  given: (hn : 0 < n) (han : orderOf a ^ 2 ∣ n)
  proof: by
  simp_rw [approxOrderOf, thickening_eq_biUnion_ball, ← image_smul, image_iUnion₂, image_smul,
    smul_ball'', smul_eq_mul, mem_ofPred_eq]
  replace han : forall {b : A}, orderOf b = n -> orderOf (a * b) = n := by
    intro b hb
    rw [← hb] at han hn
    rw [sq] at han
    rwa [(Commute.all a 

中文:
定理 smul_eq_of_mul_dvd
  条件: (hn : 0 < n) (han : orderOf a ^ 2 ∣ n)
  证明: by
  simp_rw [approxOrderOf, thickening_eq_biUnion_ball, ← image_smul, image_iUnion₂, image_smul,
    smul_ball'', smul_eq_mul, mem_ofPred_eq]
  replace han : forall {b : A}, orderOf b = n -> orderOf (a * b) = n := by
    intro b hb
    rw [← hb] at han hn
    rw [sq] at han
    rwa [(Commute.all a 

Depends on / 依赖: Commute, Commute.all, approxOrderOf, dvd_trans, image_smul, mem_ofPred_eq, mul_dvd_mul_right, orderOf, orderOf_mul_eq_right_of_forall_prime_mul_dvd, orderOf_pos_iff, orderOf_pos_iff.mp, replace, simp_rw, smul_ball, smul_eq_mul, thickening_eq_biUnion_ball
-/
theorem smul_eq_of_mul_dvd (hn : 0 < n) (han : orderOf a ^ 2 ∣ n) :
    a • approxOrderOf A n δ = approxOrderOf A n δ := by
  simp_rw [approxOrderOf, thickening_eq_biUnion_ball, ← image_smul, image_iUnion₂, image_smul,
    smul_ball'', smul_eq_mul, mem_ofPred_eq]
  replace han : forall {b : A}, orderOf b = n -> orderOf (a * b) = n := by
    intro b hb
    rw [← hb] at han hn
    rw [sq] at han
    rwa [(Commute.all a b).orderOf_mul_eq_right_of_forall_prime_mul_dvd (orderOf_pos_iff.mp hn)
      fun p _ hp' => dvd_trans (mul_dvd_mul_right hp' <| orderOf a) han]
  let f : {b : A | orderOf b = n} -> {b : A | orderOf b = n} := fun b => ⟨a * b, han b.property⟩
  have hf : Surjective f := by
    rintro ⟨b, hb⟩
    refine ⟨⟨a⁻¹ * b, ?_⟩, ?_⟩
    · rw [mem_ofPred_eq, ← orderOf_inv, mul_inv_rev, inv_inv, mul_comm]
      apply han
      simpa
    · simp only [f, mul_inv_cancel_left]
  simpa only [mem_ofPred_eq, Subtype.coe_mk, iUnion_coe_set] using
    hf.iUnion_comp fun b => ball (b : A) δ

end approxOrderOf

namespace UnitAddCircle

/--
theorem `mem_approxAddOrderOf_iff` / 定理 `mem_approxAddOrderOf_iff`

English:
theorem mem_approxAddOrderOf_iff
  given: {δ : Real} {x : UnitAddCircle} {n : Nat} (hn : 0 < n)
  proof: by
  simp only [mem_approx_add_orderOf_iff, mem_ofPred_eq, ball, dist_eq_norm,
    AddCircle.addOrderOf_eq_pos_iff hn, mul_one]
  constructor
  · rintro ⟨y, ⟨m, hm₁, hm₂, rfl⟩, hx⟩; exact ⟨m, hm₁, hm₂, hx⟩
  · rintro ⟨m, hm₁, hm₂, hx⟩; exact ⟨↑((m : Real) / n), ⟨m, hm₁, hm₂, rfl⟩, hx⟩

中文:
定理 mem_approxAddOrderOf_iff
  条件: {δ : 实数} {x : UnitAddCircle} {n : 自然数} (hn : 0 < n)
  证明: by
  simp only [mem_approx_add_orderOf_iff, mem_ofPred_eq, ball, dist_eq_norm,
    AddCircle.addOrderOf_eq_pos_iff hn, mul_one]
  constructor
  · rintro ⟨y, ⟨m, hm₁, hm₂, rfl⟩, hx⟩; exact ⟨m, hm₁, hm₂, hx⟩
  · rintro ⟨m, hm₁, hm₂, hx⟩; exact ⟨↑((m : Real) / n), ⟨m, hm₁, hm₂, rfl⟩, hx⟩

Depends on / 依赖: AddCircle, AddCircle.addOrderOf_eq_pos_iff, addOrderOf_eq_pos_iff, dist_eq_norm, mem_approx_add_orderOf_iff, mem_ofPred_eq, mul_one
-/
theorem mem_approxAddOrderOf_iff {δ : Real} {x : UnitAddCircle} {n : Nat} (hn : 0 < n) :
    x in approxAddOrderOf UnitAddCircle n δ ↔ exists m < n, gcd m n = 1 ∧ ‖x - ↑((m : Real) / n)‖ < δ := by
  simp only [mem_approx_add_orderOf_iff, mem_ofPred_eq, ball, dist_eq_norm,
    AddCircle.addOrderOf_eq_pos_iff hn, mul_one]
  constructor
  · rintro ⟨y, ⟨m, hm₁, hm₂, rfl⟩, hx⟩; exact ⟨m, hm₁, hm₂, hx⟩
  · rintro ⟨m, hm₁, hm₂, hx⟩; exact ⟨↑((m : Real) / n), ⟨m, hm₁, hm₂, rfl⟩, hx⟩

/--
theorem `mem_addWellApproximable_iff` / 定理 `mem_addWellApproximable_iff`

English:
theorem mem_addWellApproximable_iff
  given: (δ : Nat -> Real) (x : UnitAddCircle)
  proof: by
  simp only [mem_add_wellApproximable_iff, ← Nat.cofinite_eq_atTop, cofinite.blimsup_set_eq,
    mem_ofPred_eq]
  refine iff_of_eq (congr_arg Set.Infinite <| ext fun n => ⟨fun hn => ?_, fun hn => ?_⟩)
  · exact (mem_approxAddOrderOf_iff hn.1).mp hn.2
  · have h : 0 < n := by obtain ⟨m, hm₁, _, _⟩

中文:
定理 mem_addWellApproximable_iff
  条件: (δ : 自然数 -> 实数) (x : UnitAddCircle)
  证明: by
  simp only [mem_add_wellApproximable_iff, ← Nat.cofinite_eq_atTop, cofinite.blimsup_set_eq,
    mem_ofPred_eq]
  refine iff_of_eq (congr_arg Set.Infinite <| ext fun n => ⟨fun hn => ?_, fun hn => ?_⟩)
  · exact (mem_approxAddOrderOf_iff hn.1).mp hn.2
  · have h : 0 < n := by obtain ⟨m, hm₁, _, _⟩

Depends on / 依赖: Infinite, Nat.cofinite_eq_atTop, Set.Infinite, blimsup_set_eq, cofinite, cofinite.blimsup_set_eq, cofinite_eq_atTop, congr_arg, iff_of_eq, mem_add_wellApproximable_iff, mem_approxAddOrderOf_iff, mem_ofPred_eq, pos_of_gt
-/
theorem mem_addWellApproximable_iff (δ : Nat -> Real) (x : UnitAddCircle) :
    x in addWellApproximable UnitAddCircle δ ↔
      {n : Nat | exists m < n, gcd m n = 1 ∧ ‖x - ↑((m : Real) / n)‖ < δ n}.Infinite := by
  simp only [mem_add_wellApproximable_iff, ← Nat.cofinite_eq_atTop, cofinite.blimsup_set_eq,
    mem_ofPred_eq]
  refine iff_of_eq (congr_arg Set.Infinite <| ext fun n => ⟨fun hn => ?_, fun hn => ?_⟩)
  · exact (mem_approxAddOrderOf_iff hn.1).mp hn.2
  · have h : 0 < n := by obtain ⟨m, hm₁, _, _⟩ := hn; exact pos_of_gt hm₁
    exact ⟨h, (mem_approxAddOrderOf_iff h).mpr hn⟩

end UnitAddCircle

namespace AddCircle

variable {T : Real} [hT : Fact (0 < T)]

local notation a "∤" b => ¬a ∣ b

local notation a "∣∣" b => a ∣ b ∧ (a * a)∤b

local notation "𝕊" => AddCircle T

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `addWellApproximable_ae_empty_or_univ` / 定理 `addWellApproximable_ae_empty_or_univ`

English:
theorem addWellApproximable_ae_empty_or_univ
  given: (δ : Nat -> Real) (hδ : Tendsto δ atTop (𝓝 0))
  proof: by
  /- Sketch of proof:

    Let `E := addWellApproximable 𝕊 δ`. For each prime `p : ℕ`, we can partition `E` into three
    pieces `E = (A p) ∪ (B p) ∪ (C p)` where:
      `A p = blimsup (approxAddOrderOf 𝕊 n (δ n)) atTop (fun n => 0 < n ∧ (p ∤ n))`
      `B p = blimsup (approxAddOrderOf 𝕊 n (δ n)

中文:
定理 addWellApproximable_ae_empty_or_univ
  条件: (δ : 自然数 -> 实数) (hδ : 收敛 δ atTop (𝓝 0))
  证明: by
  /- Sketch of proof:

    Let `E := addWellApproximable 𝕊 δ`. For each prime `p : ℕ`, we can partition `E` into three
    pieces `E = (A p) ∪ (B p) ∪ (C p)` where:
      `A p = blimsup (approxAddOrderOf 𝕊 n (δ n)) atTop (fun n => 0 < n ∧ (p ∤ n))`
      `B p = blimsup (approxAddOrderOf 𝕊 n (δ n)
-/
theorem addWellApproximable_ae_empty_or_univ (δ : Nat -> Real) (hδ : Tendsto δ atTop (𝓝 0)) :
    (forallᵐ x, x ∉ addWellApproximable 𝕊 δ) ∨ forallᵐ x, x in addWellApproximable 𝕊 δ := by
  /- Sketch of proof:

    Let `E := addWellApproximable 𝕊 δ`. For each prime `p : ℕ`, we can partition `E` into three
    pieces `E = (A p) ∪ (B p) ∪ (C p)` where:
      `A p = blimsup (approxAddOrderOf 𝕊 n (δ n)) atTop (fun n => 0 < n ∧ (p ∤ n))`
      `B p = blimsup (approxAddOrderOf 𝕊 n (δ n)) atTop (fun n => 0 < n ∧ (p ∣∣ n))`
      `C p = blimsup (approxAddOrderOf 𝕊 n (δ n)) atTop (fun n => 0 < n ∧ (p*p ∣ n))`.
    In other words, `A p` is the set of points `x` for which there exist infinitely many `n` such
    that `x` is within a distance `δ n` of a point of order `n` and `p ∤ n`. Similarly for `B`, `C`.

    These sets have the following key properties:
      1. `A p` is almost invariant under the ergodic map `y ↦ p • y`
      2. `B p` is almost invariant under the ergodic map `y ↦ p • y + 1/p`
      3. `C p` is invariant under the map `y ↦ y + 1/p`
    To prove 1 and 2 we need the key result `blimsup_thickening_mul_ae_eq` but 3 is elementary.

    It follows from `AddCircle.ergodic_nsmul_add` and `Ergodic.ae_empty_or_univ_of_image_ae_le` that
    if either `A p` or `B p` is not almost empty for any `p`, then it is almost full and thus so is
    `E`. We may therefore assume that `A p` and `B p` are almost empty for all `p`. We thus have
    `E` is almost equal to `C p` for every prime. Combining this with 3 we find that `E` is almost
    invariant under the map `y ↦ y + 1/p` for every prime `p`. The required result then follows from
    `AddCircle.ae_empty_or_univ_of_forall_vadd_ae_eq_self`. -/
  let : SemilatticeSup Nat.Primes := Nat.Subtype.semilatticeSup _
  set μ : Measure 𝕊 := volume
  set u : Nat.Primes -> 𝕊 := fun p => ↑((↑(1 : Nat) : Real) / ((p : Nat) : Real) * T)
  have hu₀ : forall p : Nat.Primes, addOrderOf (u p) = (p : Nat) := by
    rintro ⟨p, hp⟩; exact addOrderOf_div_of_gcd_eq_one hp.pos (gcd_one_left p)
  have hu : Tendsto (addOrderOf ∘ u) atTop atTop := by
    rw [(funext hu₀ : addOrderOf ∘ u = (↑))]
    have h_mono : Monotone ((↑) : Nat.Primes -> Nat) := fun p q hpq => hpq
    refine h_mono.tendsto_atTop_atTop fun n => ?_
    obtain ⟨p, hp, hp'⟩ := n.exists_infinite_primes
    exact ⟨⟨p, hp'⟩, hp⟩
  set E := addWellApproximable 𝕊 δ
  set X : Nat -> Set 𝕊 := fun n => approxAddOrderOf 𝕊 n (δ n)
  set A : Nat -> Set 𝕊 := fun p => blimsup X atTop fun n => 0 < n ∧ p∤n
  set B : Nat -> Set 𝕊 := fun p => blimsup X atTop fun n => 0 < n ∧ p∣∣n
  set C : Nat -> Set 𝕊 := fun p => blimsup X atTop fun n => 0 < n ∧ p ^ 2 ∣ n
  have hA₀ : forall p, MeasurableSet (A p) := fun p =>
    MeasurableSet.measurableSet_blimsup fun n _ => isOpen_thickening.measurableSet
  have hB₀ : forall p, MeasurableSet (B p) := fun p =>
    MeasurableSet.measurableSet_blimsup fun n _ => isOpen_thickening.measurableSet
  have hE₀ : NullMeasurableSet E μ := by
    refine (MeasurableSet.measurableSet_blimsup fun n hn =>
      IsOpen.measurableSet ?_).nullMeasurableSet
    exact isOpen_thickening
  have hE₁ : forall p, E = A p union B p union C p := by
    intro p
    simp only [E, A, B, C, addWellApproximable, ← blimsup_or_eq_sup, ← and_or_left, ← sup_eq_union,
      sq]
    congr
    ext n
    tauto
  have hE₂ : forall p : Nat.Primes, A p =ᵐ[μ] (∅ : Set 𝕊) ∧ B p =ᵐ[μ] (∅ : Set 𝕊) -> E =ᵐ[μ] C p := by
    rintro p ⟨hA, hB⟩
    rw [hE₁ p]
    exact union_ae_eq_right_of_ae_eq_empty ((union_ae_eq_right_of_ae_eq_empty hA).trans hB)
  have hA : forall p : Nat.Primes, A p =ᵐ[μ] (∅ : Set 𝕊) ∨ A p =ᵐ[μ] univ := by
    rintro ⟨p, hp⟩
    let f : 𝕊 -> 𝕊 := fun y => (p : Nat) • y
    suffices
      f '' A p subseteq blimsup (fun n => approxAddOrderOf 𝕊 n (p * δ n)) atTop fun n => 0 < n ∧ p∤n by
      apply (ergodic_nsmul hp.one_lt).ae_empty_or_univ_of_image_ae_le (hA₀ p).nullMeasurableSet
      apply (LE.le.eventuallyLE this).congr EventuallyEq.rfl
      exact blimsup_thickening_mul_ae_eq μ (fun n => 0 < n ∧ p∤n) (fun n => {y | addOrderOf y = n})
        (Nat.cast_pos.mpr hp.pos) _ hδ
    refine (sSupHom.setImage f).apply_blimsup_le.trans (mono_blimsup fun n hn => ?_)
    replace hn := Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.2 hn.2)
    exact approxAddOrderOf.image_nsmul_subset_of_coprime (δ n) hp.pos hn
  have hB : forall p : Nat.Primes, B p =ᵐ[μ] (∅ : Set 𝕊) ∨ B p =ᵐ[μ] univ := by
    rintro ⟨p, hp⟩
    let x := u ⟨p, hp⟩
    let f : 𝕊 -> 𝕊 := fun y => p • y + x
    suffices
      f '' B p subseteq blimsup (fun n => approxAddOrderOf 𝕊 n (p * δ n)) atTop fun n => 0 < n ∧ p∣∣n by
      apply (ergodic_nsmul_add x hp.one_lt).ae_empty_or_univ_of_image_ae_le
        (hB₀ p).nullMeasurableSet
      apply (LE.le.eventuallyLE this).congr EventuallyEq.rfl
      exact blimsup_thickening_mul_ae_eq μ (fun n => 0 < n ∧ p∣∣n) (fun n => {y | addOrderOf y = n})
        (Nat.cast_pos.mpr hp.pos) _ hδ
    refine (sSupHom.setImage f).apply_blimsup_le.trans (mono_blimsup ?_)
    rintro n ⟨hn, h_div, h_ndiv⟩
    have h_cop : (addOrderOf x).Coprime (n / p) := by
      obtain ⟨q, rfl⟩ := h_div
      rw [hu₀]; rw [Subtype.coe_mk]; rw [hp.coprime_iff_not_dvd]; rw [q.mul_div_cancel_left hp.pos]
      exact fun contra => h_ndiv (mul_dvd_mul_left p contra)
    replace h_div : n / p * p = n := Nat.div_mul_cancel h_div
    have hf : f = (fun y => x + y) ∘ fun y => p • y := by
      ext; simp [f, add_comm x]
    simp_rw [Function.comp_apply]
    rw [sSupHom.setImage_toFun]; rw [hf]; rw [image_comp]
    have := @monotone_image 𝕊 𝕊 fun y => x + y
    specialize this (approxAddOrderOf.image_nsmul_subset (δ n) (n / p) hp.pos)
    simp only [h_div] at this ⊢
    refine this.trans ?_
    convert! approxAddOrderOf.vadd_subset_of_coprime (p * δ n) h_cop
    rw [hu₀]; rw [Subtype.coe_mk]; rw [mul_comm p]; rw [h_div]
  change (forallᵐ x, x ∉ E) ∨ E in ae volume
  rw [← eventuallyEq_empty]; rw [← eventuallyEq_univ]
  have hC : forall p : Nat.Primes, u p +ᵥ C p = C p := by
    intro p
    let e := (AddAction.toPerm (u p) : Equiv.Perm 𝕊).toOrderIsoSet
    change e (C p) = C p
    rw [OrderIso.apply_blimsup e]; rw [← hu₀ p]
    exact blimsup_congr (Eventually.of_forall fun n hn =>
      approxAddOrderOf.vadd_eq_of_mul_dvd (δ n) hn.1 hn.2)
  by_cases! +distrib h : forall p : Nat.Primes, A p =ᵐ[μ] (∅ : Set 𝕊) ∧ B p =ᵐ[μ] (∅ : Set 𝕊)
  · replace h : forall p : Nat.Primes, (u p +ᵥ E : Set _) =ᵐ[μ] E := by
      intro p
      replace hE₂ : E =ᵐ[μ] C p := hE₂ p (h p)
      have h_qmp : Measure.QuasiMeasurePreserving (-u p +ᵥ ·) μ μ :=
        (measurePreserving_vadd _ μ).quasiMeasurePreserving
      refine (h_qmp.vadd_ae_eq_of_ae_eq (u p) hE₂).trans (ae_eq_trans ?_ hE₂.symm)
      rw [hC]
    exact ae_empty_or_univ_of_forall_vadd_ae_eq_self hE₀ h hu
  · right
    obtain ⟨p, hp⟩ := h
    rw [hE₁ p]
    cases hp
    · rcases hA p with _ | h; · contradiction
      simp only [μ, h, union_ae_eq_univ_of_ae_eq_univ_left]
    · rcases hB p with _ | h; · contradiction
      simp only [μ, h, union_ae_eq_univ_of_ae_eq_univ_left,
        union_ae_eq_univ_of_ae_eq_univ_right]

/--
lemma `_root_.NormedAddCommGroup.exists_norm_nsmul_le` / 引理 `_root_.NormedAddCommGroup.exists_norm_nsmul_le`

English:
lemma _root_.NormedAddCommGroup.exists_norm_nsmul_le
  statement: {A : Type*}
  proof: by
  let B : Icc 0 n -> Set A := fun j => closedBall ((j : Nat) • ξ) (δ / 2)
  have hB : forall j, IsClosed (B j) := fun j => isClosed_closedBall
  suffices ¬ Pairwise (Disjoint on B) by
    obtain ⟨i, j, hij, x, hx⟩ := exists_lt_mem_inter_of_not_pairwise_disjoint this
    refine ⟨j - i, ⟨le_tsub_of

中文:
引理 _root_.赋范交换加群.存在_norm_nsmul_le
  结论: {A : 类型}
  证明: by
  let B : Icc 0 n -> Set A := fun j => closedBall ((j : Nat) • ξ) (δ / 2)
  have hB : forall j, IsClosed (B j) := fun j => isClosed_closedBall
  suffices ¬ Pairwise (Disjoint on B) by
    obtain ⟨i, j, hij, x, hx⟩ := exists_lt_mem_inter_of_not_pairwise_disjoint this
    refine ⟨j - i, ⟨le_tsub_of

Depends on / 依赖: Disjoint, IsClosed, Pairwise, Subtype, Subtype.coe_le_coe.mpr, closedBall, coe_le_coe, dist_eq_norm, dist_triangle, exists_lt_mem_inter_of_not_pairwise_disjoint, hij.le, isClosed_closedBall, j.property, le_self_add, le_tsub_of_add_le_left, property, sub_eq_add_neg, sub_nsmul, tsub_le_iff_right
-/
lemma _root_.NormedAddCommGroup.exists_norm_nsmul_le {A : Type*}
    [NormedAddCommGroup A] [CompactSpace A] [PreconnectedSpace A]
    [MeasurableSpace A] [BorelSpace A] {μ : Measure A} [μ.IsAddHaarMeasure]
    (ξ : A) {n : Nat} (hn : 0 < n) (δ : Real) (hδ : μ univ <= (n + 1) • μ (closedBall (0 : A) (δ / 2))) :
    exists j in Icc 1 n, ‖j • ξ‖ <= δ := by
  let B : Icc 0 n -> Set A := fun j => closedBall ((j : Nat) • ξ) (δ / 2)
  have hB : forall j, IsClosed (B j) := fun j => isClosed_closedBall
  suffices ¬ Pairwise (Disjoint on B) by
    obtain ⟨i, j, hij, x, hx⟩ := exists_lt_mem_inter_of_not_pairwise_disjoint this
    refine ⟨j - i, ⟨le_tsub_of_add_le_left hij, ?_⟩, ?_⟩
    · simpa only [tsub_le_iff_right] using j.property.2.trans le_self_add
    · rw [sub_nsmul _ (Subtype.coe_le_coe.mpr hij.le), ← sub_eq_add_neg, ← dist_eq_norm]
      exact (dist_triangle ((j : Nat) • ξ) x ((i : Nat) • ξ)).trans (by
        linarith [mem_closedBall.mp hx.1, mem_closedBall'.mp hx.2])
  by_contra h
  apply hn.ne'
  have h' : ⋃ j, B j = univ := by
    rw [← (isClosed_iUnion_of_finite hB).measure_eq_univ_iff_eq (μ := μ)]
    refine le_antisymm (μ.mono (subset_univ _)) ?_
    simp_rw [measure_iUnion h (fun _ => measurableSet_closedBall), tsum_fintype,
      B, μ.addHaar_closedBall_center, Finset.sum_const, Finset.card_univ, Fintype.card_Icc,
      Nat.card_Icc, tsub_zero]
    exact hδ
  replace hδ : 0 <= δ / 2 := by
    by_contra contra
refine (isOpen_univ.measure_pos μ univ_nonempty).not_ge hδ.trans ?_
    suffices μ (closedBall 0 (δ / 2)) = 0 by simp [this]
    rw [not_le]; rw [← closedBall_eq_empty (x := (0 : A))] at contra
    simp [contra]
  have h'' : forall j, (B j).Nonempty := by intro j; rwa [nonempty_closedBall]
  simpa using subsingleton_of_disjoint_isClosed_iUnion_eq_univ h'' h hB h'

/--
lemma `exists_norm_nsmul_le` / 引理 `exists_norm_nsmul_le`

English:
lemma exists_norm_nsmul_le
  given: (ξ : 𝕊) {n : Nat} (hn : 0 < n)
  proof: by
  apply NormedAddCommGroup.exists_norm_nsmul_le (μ := volume) ξ hn
  rw [AddCircle.measure_univ]; rw [volume_closedBall]; rw [← ENNReal.ofReal_nsmul]; rw [mul_div_cancel₀ _ two_ne_zero]; rw [min_eq_right (div_le_self hT.out.le <| by simp)]; rw [nsmul_eq_mul]; rw [mul_div_cancel₀ _ (Nat.cast_ne_ze

中文:
引理 存在_norm_nsmul_le
  条件: (ξ : 𝕊) {n : 自然数} (hn : 0 < n)
  证明: by
  apply NormedAddCommGroup.exists_norm_nsmul_le (μ := volume) ξ hn
  rw [AddCircle.measure_univ]; rw [volume_closedBall]; rw [← ENNReal.ofReal_nsmul]; rw [mul_div_cancel₀ _ two_ne_zero]; rw [min_eq_right (div_le_self hT.out.le <| by simp)]; rw [nsmul_eq_mul]; rw [mul_div_cancel₀ _ (Nat.cast_ne_ze

Depends on / 依赖: AddCircle, AddCircle.measure_univ, ENNReal, ENNReal.ofReal_nsmul, Nat.cast_ne_zero.mpr, NormedAddCommGroup, NormedAddCommGroup.exists_norm_nsmul_le, cast_ne_zero, div_le_self, exists_norm_nsmul_le, hT.out.le, measure_univ, min_eq_right, n.succ_ne_zero, nsmul_eq_mul, ofReal_nsmul, succ_ne_zero, two_ne_zero, volume, volume_closedBall
-/
lemma exists_norm_nsmul_le (ξ : 𝕊) {n : Nat} (hn : 0 < n) :
    exists j in Icc 1 n, ‖j • ξ‖ <= T / ↑(n + 1) := by
  apply NormedAddCommGroup.exists_norm_nsmul_le (μ := volume) ξ hn
  rw [AddCircle.measure_univ]; rw [volume_closedBall]; rw [← ENNReal.ofReal_nsmul]; rw [mul_div_cancel₀ _ two_ne_zero]; rw [min_eq_right (div_le_self hT.out.le <| by simp)]; rw [nsmul_eq_mul]; rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr n.succ_ne_zero)]

end AddCircle
