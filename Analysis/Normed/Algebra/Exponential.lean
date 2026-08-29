/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# Exponential in a Banach algebra

In this file, we define `NormedSpace.exp : 𝔸 → 𝔸`,
the exponential map in a topological algebra `𝔸`.

While for most interesting results we need `𝔸` to be normed algebra, we do not require this in the
definition in order to make `NormedSpace.exp` independent of a particular choice of norm. The
definition also does not require that `𝔸` be complete, but we need to assume it for most results.

We then prove some basic results, but we avoid importing derivatives here to minimize dependencies.
Results involving derivatives and comparisons with `Real.exp` and `Complex.exp` can be found in
`Analysis.SpecialFunctions.Exponential`.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `NormedSpace.exp_add_of_commute_of_mem_ball` : if `𝕂` has characteristic zero,
  then given two commuting elements `x` and `y` in the disk of convergence, we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
- `NormedSpace.exp_add_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is commutative,
  then given two elements `x` and `y` in the disk of convergence, we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
- `NormedSpace.exp_neg_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is a division ring,
  then given an element `x` in the disk of convergence,
  we have `NormedSpace.exp (-x) = (NormedSpace.exp x)⁻¹`.

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `expSeries_radius_eq_top` : the `FormalMultilinearSeries` defining `NormedSpace.exp`
  has infinite radius of convergence
- `NormedSpace.exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
- `NormedSpace.exp_add` : if `𝔸` is commutative, then we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)` for any `x` and `y`
- `NormedSpace.exp_neg` : if `𝔸` is a division ring, then we have
  `NormedSpace.exp (-x) = (NormedSpace.exp x)⁻¹`.
- `NormedSpace.exp_sum_of_commute` : the analogous result to `NormedSpace.exp_add_of_commute`
  for `Finset.sum`.
- `NormedSpace.exp_sum` : the analogous result to `NormedSpace.exp_add` for `Finset.sum`.
- `NormedSpace.exp_nsmul` : repeated addition in the domain corresponds to
  repeated multiplication in the codomain.
- `NormedSpace.exp_zsmul` : repeated addition in the domain corresponds to
  repeated multiplication in the codomain.

### Notes

We put nearly all the statements in this file in the `NormedSpace` namespace,
to avoid collisions with the `Real` or `Complex` namespaces.

As of 2023-11-16 due to bad instances in Mathlib
```
import Mathlib

open Real

#time example (x : ℝ) : 0 < exp x := exp_pos _ -- 250ms
#time example (x : ℝ) : 0 < Real.exp x := exp_pos _ -- 2ms
```
This is because `exp x` tries the `NormedSpace.exp 𝕂 : 𝔸 → 𝔸` function previously defined here,
and generates a slow coercion search from `Real` to `Type`, to fit the first argument here.
We will resolve this slow coercion separately,
but we want to move `exp` out of the root namespace in any case to avoid this ambiguity.

To avoid explicitly passing the base field `𝕂`, we currently fix `𝕂 = ℚ` in the definition of
`NormedSpace.exp : 𝔸 → 𝔸`. If `𝔸` can be equipped with a `ℚ`-algebra structure, we use
`Classical.choice` to pick the unique `Algebra ℚ 𝔸` instead of requiring an instance argument.
This eliminates the need to provide `Algebra ℚ 𝔸` every time `exp` is used. If `𝔸` can't be equipped
with a `ℚ`-algebra structure, we use the junk value `1`.

In the long term it may be possible to replace `Real.exp` and `Complex.exp` with `NormedSpace.exp`
and move it back to the root namespace.
-/

@[expose] public section


namespace NormedSpace

open Filter RCLike ContinuousMultilinearMap NormedField Asymptotics FormalMultilinearSeries

open scoped Nat Topology ENNReal Ring

section TopologicalAlgebra

variable (𝕂 𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

/--
Definition of `expSeries` / `expSeries` 的定义

English:
definition expSeries
  signature: : FormalMultilinearSeries 𝕂 𝔸 𝔸
  body: fun n =>
  (n !⁻¹ : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

中文:
定义 expSeries
  签名: : FormalMultilinearSeries 𝕂 𝔸 𝔸
  定义体: fun n =>
  (n !⁻¹ : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸
-/
def expSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n =>
  (n !⁻¹ : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

/--
theorem `expSeries_eq_ofScalars` / 定理 `expSeries_eq_ofScalars`

English:
theorem expSeries_eq_ofScalars
  statement: expSeries 𝕂 𝔸 = ofScalars 𝔸 fun n => (n !⁻¹ : 𝕂)
  proof: by
  simp_rw [FormalMultilinearSeries.ext_iff, expSeries, ofScalars, implies_true]

中文:
定理 expSeries_eq_ofScalars
  结论: expSeries 𝕂 𝔸 = ofScalars 𝔸 fun n => (n !⁻¹ : 𝕂)
  证明: by
  simp_rw [FormalMultilinearSeries.ext_iff, expSeries, ofScalars, implies_true]

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.ext_iff, expSeries, ext_iff, implies_true, ofScalars, simp_rw
-/
theorem expSeries_eq_ofScalars : expSeries 𝕂 𝔸 = ofScalars 𝔸 fun n => (n !⁻¹ : 𝕂) := by
  simp_rw [FormalMultilinearSeries.ext_iff, expSeries, ofScalars, implies_true]

variable {𝕂 𝔸}

open scoped Classical in
/-- `NormedSpace.exp : 𝔸 → 𝔸` is the exponential map. It is defined as the sum of the
`FormalMultilinearSeries` `expSeries ℚ 𝔸`.

If `𝔸` can't be equipped with a `ℚ`-algebra structure, we use the junk value `1`. For details on why
this approach is taken, see the module documentation for
`Mathlib/Analysis/Normed/Algebra/Exponential.lean`.

Note that when `𝔸 = Matrix n n 𝕂`, this is the **Matrix Exponential**; see
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` for lemmas
specific to that case. -/
noncomputable irreducible_def exp (x : 𝔸) : 𝔸 :=
  if h : Nonempty (Algebra Rat 𝔸) then
    letI _ := h.some
    (NormedSpace.expSeries Rat 𝔸).sum x
  else
    1

/-- The junk value when `𝔸` can't be equipped with a `ℚ`-algebra structure. -/
@[simp]
/--
theorem `exp_of_isEmpty_algebra_rat` / 定理 `exp_of_isEmpty_algebra_rat`

English:
theorem exp_of_isEmpty_algebra_rat
  given: [IsEmpty (Algebra Rat 𝔸)] (x : 𝔸)
  statement: exp x = 1
  proof: by
  rw [exp]; rw [dif_neg (not_nonempty_iff.mpr ‹_›)]

中文:
定理 exp_of_isEmpty_algebra_rat
  条件: [IsEmpty (Algebra Rat 𝔸)] (x : 𝔸)
  结论: exp x = 1
  证明: by
  rw [exp]; rw [dif_neg (not_nonempty_iff.mpr ‹_›)]

Depends on / 依赖: dif_neg, not_nonempty_iff, not_nonempty_iff.mpr
-/
theorem exp_of_isEmpty_algebra_rat [IsEmpty (Algebra Rat 𝔸)] (x : 𝔸) : exp x = 1 := by
  rw [exp]; rw [dif_neg (not_nonempty_iff.mpr ‹_›)]

/--
theorem `expSeries_apply_eq` / 定理 `expSeries_apply_eq`

English:
theorem expSeries_apply_eq
  given: (x : 𝔸) (n : Nat)
  proof: by simp [expSeries]

中文:
定理 expSeries_apply_eq
  条件: (x : 𝔸) (n : 自然数)
  证明: by simp [expSeries]

Depends on / 依赖: expSeries
-/
theorem expSeries_apply_eq (x : 𝔸) (n : Nat) :
    (expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n := by simp [expSeries]

/--
theorem `expSeries_apply_eq'` / 定理 `expSeries_apply_eq'`

English:
theorem expSeries_apply_eq'
  given: (x : 𝔸)
  proof: funext (expSeries_apply_eq x)

中文:
定理 expSeries_apply_eq'
  条件: (x : 𝔸)
  证明: funext (expSeries_apply_eq x)

Depends on / 依赖: expSeries_apply_eq
-/
theorem expSeries_apply_eq' (x : 𝔸) :
    (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  funext (expSeries_apply_eq x)

/--
theorem `expSeries_sum_eq` / 定理 `expSeries_sum_eq`

English:
theorem expSeries_sum_eq
  given: (x : 𝔸)
  statement: (expSeries 𝕂 𝔸).sum x = ∑' n : Nat, (n !⁻¹ : 𝕂) • x ^ n
  proof: tsum_congr fun n => expSeries_apply_eq x n

中文:
定理 expSeries_sum_eq
  条件: (x : 𝔸)
  结论: (expSeries 𝕂 𝔸).sum x = ∑' n : 自然数, (n !⁻¹ : 𝕂) • x ^ n
  证明: tsum_congr fun n => expSeries_apply_eq x n

Depends on / 依赖: expSeries_apply_eq, tsum_congr
-/
theorem expSeries_sum_eq (x : 𝔸) : (expSeries 𝕂 𝔸).sum x = ∑' n : Nat, (n !⁻¹ : 𝕂) • x ^ n :=
  tsum_congr fun n => expSeries_apply_eq x n

/--
theorem `expSeries_sum_eq_rat` / 定理 `expSeries_sum_eq_rat`

English:
theorem expSeries_sum_eq_rat
  given: [Algebra Rat 𝔸]
  statement: (expSeries 𝕂 𝔸).sum = (expSeries Rat 𝔸).sum
  proof: by
  ext; simp_rw [expSeries_sum_eq, inv_natCast_smul_eq 𝕂 Rat]

中文:
定理 expSeries_sum_eq_rat
  条件: [Algebra Rat 𝔸]
  结论: (expSeries 𝕂 𝔸).sum = (expSeries Rat 𝔸).sum
  证明: by
  ext; simp_rw [expSeries_sum_eq, inv_natCast_smul_eq 𝕂 Rat]

Depends on / 依赖: expSeries_sum_eq, inv_natCast_smul_eq, simp_rw
-/
theorem expSeries_sum_eq_rat [Algebra Rat 𝔸] : (expSeries 𝕂 𝔸).sum = (expSeries Rat 𝔸).sum := by
  ext; simp_rw [expSeries_sum_eq, inv_natCast_smul_eq 𝕂 Rat]

/--
theorem `expSeries_eq_expSeries_rat` / 定理 `expSeries_eq_expSeries_rat`

English:
theorem expSeries_eq_expSeries_rat
  given: [Algebra Rat 𝔸] (n : Nat)
  proof: by
  ext c
  simp [expSeries, inv_natCast_smul_eq 𝕂 Rat]

中文:
定理 expSeries_eq_expSeries_rat
  条件: [Algebra Rat 𝔸] (n : 自然数)
  证明: by
  ext c
  simp [expSeries, inv_natCast_smul_eq 𝕂 Rat]

Depends on / 依赖: expSeries, inv_natCast_smul_eq
-/
theorem expSeries_eq_expSeries_rat [Algebra Rat 𝔸] (n : Nat) :
    ⇑(expSeries 𝕂 𝔸 n) = expSeries Rat 𝔸 n := by
  ext c
  simp [expSeries, inv_natCast_smul_eq 𝕂 Rat]

variable (𝕂) in
/--
theorem `exp_eq_expSeries_sum` / 定理 `exp_eq_expSeries_sum`

English:
theorem exp_eq_expSeries_sum
  given: [CharZero 𝕂]
  statement: exp = (expSeries 𝕂 𝔸).sum
  proof: by
  ext x
  rw [exp]; rw [dif_pos ⟨RestrictScalars.algebra Rat 𝕂 𝔸⟩]; rw [← @expSeries_sum_eq_rat (𝕂 := 𝕂)]

中文:
定理 exp_eq_expSeries_sum
  条件: [CharZero 𝕂]
  结论: exp = (expSeries 𝕂 𝔸).sum
  证明: by
  ext x
  rw [exp]; rw [dif_pos ⟨RestrictScalars.algebra Rat 𝕂 𝔸⟩]; rw [← @expSeries_sum_eq_rat (𝕂 := 𝕂)]

Depends on / 依赖: RestrictScalars, RestrictScalars.algebra, algebra, dif_pos, expSeries_sum_eq_rat
-/
theorem exp_eq_expSeries_sum [CharZero 𝕂] : exp = (expSeries 𝕂 𝔸).sum := by
  ext x
  rw [exp]; rw [dif_pos ⟨RestrictScalars.algebra Rat 𝕂 𝔸⟩]; rw [← @expSeries_sum_eq_rat (𝕂 := 𝕂)]

variable (𝕂) in
/--
theorem `exp_eq_tsum` / 定理 `exp_eq_tsum`

English:
theorem exp_eq_tsum
  given: [CharZero 𝕂]
  statement: exp = fun x : 𝔸 => ∑' n : Nat, (n !⁻¹ : 𝕂) • x ^ n
  proof: by
  rw [exp_eq_expSeries_sum 𝕂]
  ext x
  exact expSeries_sum_eq x

中文:
定理 exp_eq_tsum
  条件: [CharZero 𝕂]
  结论: exp = fun x : 𝔸 => ∑' n : 自然数, (n !⁻¹ : 𝕂) • x ^ n
  证明: by
  rw [exp_eq_expSeries_sum 𝕂]
  ext x
  exact expSeries_sum_eq x

Depends on / 依赖: expSeries_sum_eq, exp_eq_expSeries_sum
-/
theorem exp_eq_tsum [CharZero 𝕂] : exp = fun x : 𝔸 => ∑' n : Nat, (n !⁻¹ : 𝕂) • x ^ n := by
  rw [exp_eq_expSeries_sum 𝕂]
  ext x
  exact expSeries_sum_eq x

/--
theorem `exp_eq_tsum_rat` / 定理 `exp_eq_tsum_rat`

English:
theorem exp_eq_tsum_rat
  given: [Algebra Rat 𝔸]
  statement: exp = fun x : 𝔸 => ∑' n : Nat, (n !⁻¹ : Rat) • x ^ n
  proof: exp_eq_tsum Rat

中文:
定理 exp_eq_tsum_rat
  条件: [Algebra Rat 𝔸]
  结论: exp = fun x : 𝔸 => ∑' n : 自然数, (n !⁻¹ : Rat) • x ^ n
  证明: exp_eq_tsum Rat

Depends on / 依赖: exp_eq_tsum
-/
theorem exp_eq_tsum_rat [Algebra Rat 𝔸] : exp = fun x : 𝔸 => ∑' n : Nat, (n !⁻¹ : Rat) • x ^ n :=
  exp_eq_tsum Rat

variable (𝕂) in
/--
theorem `exp_eq_ofScalarsSum` / 定理 `exp_eq_ofScalarsSum`

English:
theorem exp_eq_ofScalarsSum
  given: [CharZero 𝕂]
  proof: by
  rw [exp_eq_tsum 𝕂]; rw [ofScalarsSum_eq_tsum]

中文:
定理 exp_eq_ofScalarsSum
  条件: [CharZero 𝕂]
  证明: by
  rw [exp_eq_tsum 𝕂]; rw [ofScalarsSum_eq_tsum]

Depends on / 依赖: exp_eq_tsum, ofScalarsSum_eq_tsum
-/
theorem exp_eq_ofScalarsSum [CharZero 𝕂] :
    exp = ofScalarsSum (E := 𝔸) fun n => (n !⁻¹ : 𝕂) := by
  rw [exp_eq_tsum 𝕂]; rw [ofScalarsSum_eq_tsum]

/--
theorem `expSeries_apply_zero` / 定理 `expSeries_apply_zero`

English:
theorem expSeries_apply_zero
  given: (n : Nat)
  proof: by
  rw [expSeries_apply_eq]
  rcases n with - | n
  · simp
  · rw [zero_pow (Nat.succ_ne_zero _), smul_zero, Pi.single_eq_of_ne n.succ_ne_zero]

@[simp]

中文:
定理 expSeries_apply_zero
  条件: (n : 自然数)
  证明: by
  rw [expSeries_apply_eq]
  rcases n with - | n
  · simp
  · rw [zero_pow (Nat.succ_ne_zero _), smul_zero, Pi.single_eq_of_ne n.succ_ne_zero]

@[simp]

Depends on / 依赖: Nat.succ_ne_zero, Pi.single_eq_of_ne, expSeries_apply_eq, n.succ_ne_zero, single_eq_of_ne, smul_zero, succ_ne_zero, zero_pow
-/
theorem expSeries_apply_zero (n : Nat) :
    expSeries 𝕂 𝔸 n (fun _ => (0 : 𝔸)) = Pi.single (M := fun _ => 𝔸) 0 1 n := by
  rw [expSeries_apply_eq]
  rcases n with - | n
  · simp
  · rw [zero_pow (Nat.succ_ne_zero _), smul_zero, Pi.single_eq_of_ne n.succ_ne_zero]

@[simp]
/--
theorem `exp_zero` / 定理 `exp_zero`

English:
theorem exp_zero
  statement: exp (0 : 𝔸) = 1
  proof: by
  rw [exp]
  split_ifs
  · simp_rw [expSeries_sum_eq, ← expSeries_apply_eq, expSeries_apply_zero, tsum_pi_single]
  · rfl

@[simp]

中文:
定理 exp_zero
  结论: exp (0 : 𝔸) = 1
  证明: by
  rw [exp]
  split_ifs
  · simp_rw [expSeries_sum_eq, ← expSeries_apply_eq, expSeries_apply_zero, tsum_pi_single]
  · rfl

@[simp]

Depends on / 依赖: expSeries_apply_eq, expSeries_apply_zero, expSeries_sum_eq, simp_rw, split_ifs, tsum_pi_single
-/
theorem exp_zero : exp (0 : 𝔸) = 1 := by
  rw [exp]
  split_ifs
  · simp_rw [expSeries_sum_eq, ← expSeries_apply_eq, expSeries_apply_zero, tsum_pi_single]
  · rfl

@[simp]
/--
theorem `exp_op` / 定理 `exp_op`

English:
theorem exp_op
  given: [T2Space 𝔸] (x : 𝔸)
  proof: by
  obtain h | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra Rat 𝔸)
· have : IsEmpty (Algebra Rat 𝔸ᵐᵒᵖ) := ⟨fun _ => h.elim (RingEquiv.opOp 𝔸).algebra Rat⟩
    simp
  · rw [exp_eq_tsum Rat, exp_eq_tsum Rat]
    simp_rw [← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]

@[simp]

中文:
定理 exp_op
  条件: [T2Space 𝔸] (x : 𝔸)
  证明: by
  obtain h | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra Rat 𝔸)
· have : IsEmpty (Algebra Rat 𝔸ᵐᵒᵖ) := ⟨fun _ => h.elim (RingEquiv.opOp 𝔸).algebra Rat⟩
    simp
  · rw [exp_eq_tsum Rat, exp_eq_tsum Rat]
    simp_rw [← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]

@[simp]

Depends on / 依赖: Algebra, IsEmpty, MulOpposite, MulOpposite.op_pow, MulOpposite.op_smul, RingEquiv, RingEquiv.opOp, algebra, exp_eq_tsum, h.elim, isEmpty_or_nonempty, op_pow, op_smul, simp_rw, tsum_op
-/
theorem exp_op [T2Space 𝔸] (x : 𝔸) :
    exp (MulOpposite.op x) = MulOpposite.op (exp x) := by
  obtain h | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra Rat 𝔸)
· have : IsEmpty (Algebra Rat 𝔸ᵐᵒᵖ) := ⟨fun _ => h.elim (RingEquiv.opOp 𝔸).algebra Rat⟩
    simp
  · rw [exp_eq_tsum Rat, exp_eq_tsum Rat]
    simp_rw [← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]

@[simp]
/--
theorem `exp_unop` / 定理 `exp_unop`

English:
theorem exp_unop
  given: [T2Space 𝔸] (x : 𝔸ᵐᵒᵖ)
  proof: by
  induction x; simp

中文:
定理 exp_unop
  条件: [T2Space 𝔸] (x : 𝔸ᵐᵒᵖ)
  证明: by
  induction x; simp
-/
theorem exp_unop [T2Space 𝔸] (x : 𝔸ᵐᵒᵖ) :
    exp (MulOpposite.unop x) = MulOpposite.unop (exp x) := by
  induction x; simp

/--
theorem `star_exp` / 定理 `star_exp`

English:
theorem star_exp
  given: [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] (x : 𝔸)
  proof: by
  obtain _ | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra Rat 𝔸)
  · simp
  · simp_rw [exp_eq_tsum Rat, ← star_pow, ← star_inv_natCast_smul, ← tsum_star]

中文:
定理 star_exp
  条件: [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] (x : 𝔸)
  证明: by
  obtain _ | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra Rat 𝔸)
  · simp
  · simp_rw [exp_eq_tsum Rat, ← star_pow, ← star_inv_natCast_smul, ← tsum_star]

Depends on / 依赖: Algebra, exp_eq_tsum, isEmpty_or_nonempty, simp_rw, star_inv_natCast_smul, star_pow, tsum_star
-/
theorem star_exp [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] (x : 𝔸) :
    star (exp x) = exp (star x) := by
  obtain _ | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra Rat 𝔸)
  · simp
  · simp_rw [exp_eq_tsum Rat, ← star_pow, ← star_inv_natCast_smul, ← tsum_star]

/--
theorem `exp_mem` / 定理 `exp_mem`

English:
theorem exp_mem
  proof: by
  have := SMulMemClass.ofIsScalarTower S Rat R 𝔸
  rw [exp_eq_tsum Rat]
exact tsum_mem h_closed fun i => SMulMemClass.smul_mem _ pow_mem h _

中文:
定理 exp_mem
  证明: by
  have := SMulMemClass.ofIsScalarTower S Rat R 𝔸
  rw [exp_eq_tsum Rat]
exact tsum_mem h_closed fun i => SMulMemClass.smul_mem _ pow_mem h _

Depends on / 依赖: SMulMemClass, SMulMemClass.ofIsScalarTower, SMulMemClass.smul_mem, exp_eq_tsum, h_closed, ofIsScalarTower, pow_mem, smul_mem, tsum_mem
-/
theorem exp_mem
    {R S : Type*} [Monoid R] [SMul Rat R] [MulAction R 𝔸] [Algebra Rat 𝔸] [IsScalarTower Rat R 𝔸]
    [SetLike S 𝔸] [SubsemiringClass S 𝔸] [SMulMemClass S R 𝔸] {s : S}
    (h_closed : IsClosed (s : Set 𝔸)) {x : 𝔸} (h : x in s) :
    exp x in s := by
  have := SMulMemClass.ofIsScalarTower S Rat R 𝔸
  rw [exp_eq_tsum Rat]
exact tsum_mem h_closed fun i => SMulMemClass.smul_mem _ pow_mem h _

variable (𝕂)

@[aesop safe apply]
/--
theorem `_root_.IsSelfAdjoint.exp` / 定理 `_root_.IsSelfAdjoint.exp`

English:
theorem _root_.IsSelfAdjoint.exp
  statement: [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
  proof: (star_exp x).trans h.symm ▸ rfl

中文:
定理 _root_.IsSelfAdjoint.exp
  结论: [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
  证明: (star_exp x).trans h.symm ▸ rfl

Depends on / 依赖: h.symm, star_exp
-/
theorem _root_.IsSelfAdjoint.exp [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
    (h : IsSelfAdjoint x) : IsSelfAdjoint (exp x) :=
(star_exp x).trans h.symm ▸ rfl

/--
theorem `_root_.Commute.exp_right` / 定理 `_root_.Commute.exp_right`

English:
theorem _root_.Commute.exp_right
  given: [T2Space 𝔸] {x y : 𝔸} (h : Commute x y)
  proof: by
  obtain _ | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra Rat 𝔸)
  · simp
  · rw [exp_eq_tsum Rat]
    exact Commute.tsum_right x fun n => (h.pow_right n).smul_right _

中文:
定理 _root_.Commute.exp_right
  条件: [T2Space 𝔸] {x y : 𝔸} (h : Commute x y)
  证明: by
  obtain _ | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra Rat 𝔸)
  · simp
  · rw [exp_eq_tsum Rat]
    exact Commute.tsum_right x fun n => (h.pow_right n).smul_right _

Depends on / 依赖: Algebra, Commute, Commute.tsum_right, exp_eq_tsum, h.pow_right, isEmpty_or_nonempty, pow_right, smul_right, tsum_right
-/
theorem _root_.Commute.exp_right [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute x (exp y) := by
  obtain _ | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra Rat 𝔸)
  · simp
  · rw [exp_eq_tsum Rat]
    exact Commute.tsum_right x fun n => (h.pow_right n).smul_right _

/--
theorem `_root_.Commute.exp_left` / 定理 `_root_.Commute.exp_left`

English:
theorem _root_.Commute.exp_left
  given: [T2Space 𝔸] {x y : 𝔸} (h : Commute x y)
  proof: h.symm.exp_right.symm

中文:
定理 _root_.Commute.exp_left
  条件: [T2Space 𝔸] {x y : 𝔸} (h : Commute x y)
  证明: h.symm.exp_right.symm

Depends on / 依赖: exp_right, h.symm.exp_right.symm
-/
theorem _root_.Commute.exp_left [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (exp x) y :=
  h.symm.exp_right.symm

/--
theorem `_root_.Commute.exp` / 定理 `_root_.Commute.exp`

English:
theorem _root_.Commute.exp
  given: [T2Space 𝔸] {x y : 𝔸} (h : Commute x y)
  proof: h.exp_left.exp_right

中文:
定理 _root_.Commute.exp
  条件: [T2Space 𝔸] {x y : 𝔸} (h : Commute x y)
  证明: h.exp_left.exp_right

Depends on / 依赖: exp_left, exp_right, h.exp_left.exp_right
-/
theorem _root_.Commute.exp [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (exp x) (exp y) :=
  h.exp_left.exp_right

end TopologicalAlgebra

section TopologicalDivisionAlgebra

variable {𝕂 𝔸 : Type*} [Field 𝕂] [DivisionRing 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

/--
theorem `expSeries_apply_eq_div` / 定理 `expSeries_apply_eq_div`

English:
theorem expSeries_apply_eq_div
  given: (x : 𝔸) (n : Nat)
  statement: (expSeries 𝕂 𝔸 n fun _ => x) = x ^ n / n !
  proof: by
  rw [div_eq_mul_inv]; rw [← (Nat.cast_commute n ! (x ^ n)).inv_left₀.eq]; rw [← smul_eq_mul]; rw [expSeries_apply_eq]; rw [inv_natCast_smul_eq 𝕂 𝔸]

中文:
定理 expSeries_apply_eq_div
  条件: (x : 𝔸) (n : 自然数)
  结论: (expSeries 𝕂 𝔸 n fun _ => x) = x ^ n / n !
  证明: by
  rw [div_eq_mul_inv]; rw [← (Nat.cast_commute n ! (x ^ n)).inv_left₀.eq]; rw [← smul_eq_mul]; rw [expSeries_apply_eq]; rw [inv_natCast_smul_eq 𝕂 𝔸]

Depends on / 依赖: Nat.cast_commute, cast_commute, div_eq_mul_inv, expSeries_apply_eq, inv_natCast_smul_eq, smul_eq_mul
-/
theorem expSeries_apply_eq_div (x : 𝔸) (n : Nat) : (expSeries 𝕂 𝔸 n fun _ => x) = x ^ n / n ! := by
  rw [div_eq_mul_inv]; rw [← (Nat.cast_commute n ! (x ^ n)).inv_left₀.eq]; rw [← smul_eq_mul]; rw [expSeries_apply_eq]; rw [inv_natCast_smul_eq 𝕂 𝔸]

/--
theorem `expSeries_apply_eq_div'` / 定理 `expSeries_apply_eq_div'`

English:
theorem expSeries_apply_eq_div'
  given: (x : 𝔸)
  proof: funext (expSeries_apply_eq_div x)

中文:
定理 expSeries_apply_eq_div'
  条件: (x : 𝔸)
  证明: funext (expSeries_apply_eq_div x)

Depends on / 依赖: expSeries_apply_eq_div
-/
theorem expSeries_apply_eq_div' (x : 𝔸) :
    (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => x ^ n / n ! :=
  funext (expSeries_apply_eq_div x)

/--
theorem `expSeries_sum_eq_div` / 定理 `expSeries_sum_eq_div`

English:
theorem expSeries_sum_eq_div
  given: (x : 𝔸)
  statement: (expSeries 𝕂 𝔸).sum x = ∑' n : Nat, x ^ n / n !
  proof: tsum_congr (expSeries_apply_eq_div x)

中文:
定理 expSeries_sum_eq_div
  条件: (x : 𝔸)
  结论: (expSeries 𝕂 𝔸).sum x = ∑' n : 自然数, x ^ n / n !
  证明: tsum_congr (expSeries_apply_eq_div x)

Depends on / 依赖: expSeries_apply_eq_div, tsum_congr
-/
theorem expSeries_sum_eq_div (x : 𝔸) : (expSeries 𝕂 𝔸).sum x = ∑' n : Nat, x ^ n / n ! :=
  tsum_congr (expSeries_apply_eq_div x)

/--
theorem `exp_eq_tsum_div` / 定理 `exp_eq_tsum_div`

English:
theorem exp_eq_tsum_div
  given: [CharZero 𝔸]
  statement: exp = fun x : 𝔸 => ∑' n : Nat, x ^ n / n !
  proof: by
  rw [exp_eq_expSeries_sum Rat]
  ext x
  exact expSeries_sum_eq_div x

中文:
定理 exp_eq_tsum_div
  条件: [CharZero 𝔸]
  结论: exp = fun x : 𝔸 => ∑' n : 自然数, x ^ n / n !
  证明: by
  rw [exp_eq_expSeries_sum Rat]
  ext x
  exact expSeries_sum_eq_div x

Depends on / 依赖: expSeries_sum_eq_div, exp_eq_expSeries_sum
-/
theorem exp_eq_tsum_div [CharZero 𝔸] : exp = fun x : 𝔸 => ∑' n : Nat, x ^ n / n ! := by
  rw [exp_eq_expSeries_sum Rat]
  ext x
  exact expSeries_sum_eq_div x

end TopologicalDivisionAlgebra

section Normed

section AnyFieldAnyAlgebra

variable {𝕂 𝔸 𝔹 : Type*} [NontriviallyNormedField 𝕂]
variable [NormedRing 𝔸] [NormedRing 𝔹] [NormedAlgebra 𝕂 𝔸]

/--
theorem `norm_expSeries_summable_of_mem_ball` / 定理 `norm_expSeries_summable_of_mem_ball`

English:
theorem norm_expSeries_summable_of_mem_ball
  statement: (x : 𝔸)
  proof: (expSeries 𝕂 𝔸).summable_norm_apply hx

中文:
定理 norm_expSeries_summable_of_mem_ball
  结论: (x : 𝔸)
  证明: (expSeries 𝕂 𝔸).summable_norm_apply hx

Depends on / 依赖: expSeries, summable_norm_apply
-/
theorem norm_expSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖ :=
  (expSeries 𝕂 𝔸).summable_norm_apply hx

/--
theorem `norm_expSeries_summable_of_mem_ball'` / 定理 `norm_expSeries_summable_of_mem_ball'`

English:
theorem norm_expSeries_summable_of_mem_ball'
  statement: (x : 𝔸)
  proof: by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq']
  exact norm_expSeries_summable_of_mem_ball x hx

中文:
定理 norm_expSeries_summable_of_mem_ball'
  结论: (x : 𝔸)
  证明: by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq']
  exact norm_expSeries_summable_of_mem_ball x hx

Depends on / 依赖: Summable, expSeries_apply_eq, norm_expSeries_summable_of_mem_ball
-/
theorem norm_expSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖ := by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq']
  exact norm_expSeries_summable_of_mem_ball x hx

section CompleteAlgebra

variable [CompleteSpace 𝔸]

/--
theorem `expSeries_summable_of_mem_ball` / 定理 `expSeries_summable_of_mem_ball`

English:
theorem expSeries_summable_of_mem_ball
  statement: (x : 𝔸)
  proof: (norm_expSeries_summable_of_mem_ball x hx).of_norm

中文:
定理 expSeries_summable_of_mem_ball
  结论: (x : 𝔸)
  证明: (norm_expSeries_summable_of_mem_ball x hx).of_norm

Depends on / 依赖: norm_expSeries_summable_of_mem_ball, of_norm
-/
theorem expSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  (norm_expSeries_summable_of_mem_ball x hx).of_norm

/--
theorem `expSeries_summable_of_mem_ball'` / 定理 `expSeries_summable_of_mem_ball'`

English:
theorem expSeries_summable_of_mem_ball'
  statement: (x : 𝔸)
  proof: (norm_expSeries_summable_of_mem_ball' x hx).of_norm

中文:
定理 expSeries_summable_of_mem_ball'
  结论: (x : 𝔸)
  证明: (norm_expSeries_summable_of_mem_ball' x hx).of_norm

Depends on / 依赖: norm_expSeries_summable_of_mem_ball, of_norm
-/
theorem expSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  (norm_expSeries_summable_of_mem_ball' x hx).of_norm

/--
theorem `expSeries_hasSum_exp_of_mem_ball` / 定理 `expSeries_hasSum_exp_of_mem_ball`

English:
theorem expSeries_hasSum_exp_of_mem_ball
  statement: [CharZero 𝕂] (x : 𝔸)
  proof: by
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using
    FormalMultilinearSeries.hasSum (expSeries 𝕂 𝔸) hx

中文:
定理 expSeries_hasSum_exp_of_mem_ball
  结论: [CharZero 𝕂] (x : 𝔸)
  证明: by
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using
    FormalMultilinearSeries.hasSum (expSeries 𝕂 𝔸) hx

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.hasSum, expSeries, expSeries_sum_eq_rat, exp_eq_expSeries_sum, hasSum
-/
theorem expSeries_hasSum_exp_of_mem_ball [CharZero 𝕂] (x : 𝔸)
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp x) := by
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using
    FormalMultilinearSeries.hasSum (expSeries 𝕂 𝔸) hx

/--
theorem `expSeries_hasSum_exp_of_mem_ball'` / 定理 `expSeries_hasSum_exp_of_mem_ball'`

English:
theorem expSeries_hasSum_exp_of_mem_ball'
  statement: [CharZero 𝕂] (x : 𝔸)
  proof: by
  rw [← expSeries_apply_eq']
  exact expSeries_hasSum_exp_of_mem_ball x hx

中文:
定理 expSeries_hasSum_exp_of_mem_ball'
  结论: [CharZero 𝕂] (x : 𝔸)
  证明: by
  rw [← expSeries_apply_eq']
  exact expSeries_hasSum_exp_of_mem_ball x hx

Depends on / 依赖: expSeries_apply_eq, expSeries_hasSum_exp_of_mem_ball
-/
theorem expSeries_hasSum_exp_of_mem_ball' [CharZero 𝕂] (x : 𝔸)
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (exp x) := by
  rw [← expSeries_apply_eq']
  exact expSeries_hasSum_exp_of_mem_ball x hx

/--
theorem `hasFPowerSeriesOnBall_exp_of_radius_pos` / 定理 `hasFPowerSeriesOnBall_exp_of_radius_pos`

English:
theorem hasFPowerSeriesOnBall_exp_of_radius_pos
  given: [CharZero 𝕂] (h : 0 < (expSeries 𝕂 𝔸).radius)
  proof: by
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using
    (expSeries 𝕂 𝔸).hasFPowerSeriesOnBall h

中文:
定理 hasFPowerSeriesOnBall_exp_of_radius_pos
  条件: [CharZero 𝕂] (h : 0 < (expSeries 𝕂 𝔸).radius)
  证明: by
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using
    (expSeries 𝕂 𝔸).hasFPowerSeriesOnBall h

Depends on / 依赖: expSeries, expSeries_sum_eq_rat, exp_eq_expSeries_sum, hasFPowerSeriesOnBall
-/
theorem hasFPowerSeriesOnBall_exp_of_radius_pos [CharZero 𝕂] (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesOnBall exp (expSeries 𝕂 𝔸) 0 (expSeries 𝕂 𝔸).radius := by
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using
    (expSeries 𝕂 𝔸).hasFPowerSeriesOnBall h

/--
theorem `hasFPowerSeriesAt_exp_zero_of_radius_pos` / 定理 `hasFPowerSeriesAt_exp_zero_of_radius_pos`

English:
theorem hasFPowerSeriesAt_exp_zero_of_radius_pos
  given: [CharZero 𝕂] (h : 0 < (expSeries 𝕂 𝔸).radius)
  proof: by
  simpa only [exp, expSeries_sum_eq_rat] using
    (hasFPowerSeriesOnBall_exp_of_radius_pos h).hasFPowerSeriesAt

中文:
定理 hasFPowerSeriesAt_exp_zero_of_radius_pos
  条件: [CharZero 𝕂] (h : 0 < (expSeries 𝕂 𝔸).radius)
  证明: by
  simpa only [exp, expSeries_sum_eq_rat] using
    (hasFPowerSeriesOnBall_exp_of_radius_pos h).hasFPowerSeriesAt

Depends on / 依赖: expSeries_sum_eq_rat, hasFPowerSeriesAt, hasFPowerSeriesOnBall_exp_of_radius_pos
-/
theorem hasFPowerSeriesAt_exp_zero_of_radius_pos [CharZero 𝕂] (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesAt exp (expSeries 𝕂 𝔸) 0 := by
  simpa only [exp, expSeries_sum_eq_rat] using
    (hasFPowerSeriesOnBall_exp_of_radius_pos h).hasFPowerSeriesAt

/--
theorem `continuousOn_exp` / 定理 `continuousOn_exp`

English:
theorem continuousOn_exp
  given: [CharZero 𝕂]
  proof: by
  have := FormalMultilinearSeries.continuousOn (p := expSeries 𝕂 𝔸)
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using this

中文:
定理 continuousOn_exp
  条件: [CharZero 𝕂]
  证明: by
  have := FormalMultilinearSeries.continuousOn (p := expSeries 𝕂 𝔸)
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using this

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.continuousOn, continuousOn, expSeries, expSeries_sum_eq_rat, exp_eq_expSeries_sum
-/
theorem continuousOn_exp [CharZero 𝕂] :
    ContinuousOn (exp : 𝔸 -> 𝔸) (Metric.eball 0 (expSeries 𝕂 𝔸).radius) := by
  have := FormalMultilinearSeries.continuousOn (p := expSeries 𝕂 𝔸)
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using this

/--
theorem `analyticAt_exp_of_mem_ball` / 定理 `analyticAt_exp_of_mem_ball`

English:
theorem analyticAt_exp_of_mem_ball
  statement: [CharZero 𝕂] (x : 𝔸)
  proof: by
  by_cases h : (expSeries 𝕂 𝔸).radius = 0
  · rw [h] at hx; exact (ENNReal.not_lt_zero hx).elim
  · have h := pos_iff_ne_zero.mpr h
    exact (hasFPowerSeriesOnBall_exp_of_radius_pos h).analyticAt_of_mem hx

中文:
定理 analyticAt_exp_of_mem_ball
  结论: [CharZero 𝕂] (x : 𝔸)
  证明: by
  by_cases h : (expSeries 𝕂 𝔸).radius = 0
  · rw [h] at hx; exact (ENNReal.not_lt_zero hx).elim
  · have h := pos_iff_ne_zero.mpr h
    exact (hasFPowerSeriesOnBall_exp_of_radius_pos h).analyticAt_of_mem hx

Depends on / 依赖: ENNReal, ENNReal.not_lt_zero, analyticAt_of_mem, expSeries, hasFPowerSeriesOnBall_exp_of_radius_pos, not_lt_zero, pos_iff_ne_zero, pos_iff_ne_zero.mpr, radius
-/
theorem analyticAt_exp_of_mem_ball [CharZero 𝕂] (x : 𝔸)
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : AnalyticAt 𝕂 exp x := by
  by_cases h : (expSeries 𝕂 𝔸).radius = 0
  · rw [h] at hx; exact (ENNReal.not_lt_zero hx).elim
  · have h := pos_iff_ne_zero.mpr h
    exact (hasFPowerSeriesOnBall_exp_of_radius_pos h).analyticAt_of_mem hx

/--
theorem `exp_add_of_commute_of_mem_ball` / 定理 `exp_add_of_commute_of_mem_ball`

English:
theorem exp_add_of_commute_of_mem_ball
  statement: [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y)
  proof: by
  rw [exp_eq_tsum 𝕂]; rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (norm_expSeries_summable_of_mem_ball' x hx) (norm_expSeries_summable_of_mem_ball' y hy)]
  dsimp only
  conv_lhs =>
    congr
    ext
    rw [hxy.add_pow' _]; rw [Finset.smul_sum]
  refine tsum_congr fun n => 

中文:
定理 exp_add_of_commute_of_mem_ball
  结论: [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y)
  证明: by
  rw [exp_eq_tsum 𝕂]; rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (norm_expSeries_summable_of_mem_ball' x hx) (norm_expSeries_summable_of_mem_ball' y hy)]
  dsimp only
  conv_lhs =>
    congr
    ext
    rw [hxy.add_pow' _]; rw [Finset.smul_sum]
  refine tsum_congr fun n => 

Depends on / 依赖: Finset, Finset.mem_antidiagonal.mp, Finset.smul_sum, Finset.sum_congr, Nat.cast_add_choose, Nat.cast_smul_eq_nsmul, add_pow, cast_add_choose, cast_smul_eq_nsmul, conv_lhs, exp_eq_tsum, hxy.add_pow, mem_antidiagonal, norm_expSeries_summable_of_mem_ball, smul_mul_smul_comm, smul_smul, smul_sum, sum_congr, tsum_congr, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
-/
theorem exp_add_of_commute_of_mem_ball [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y)
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
    (hy : y in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp (x + y) = exp x * exp y := by
  rw [exp_eq_tsum 𝕂]; rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (norm_expSeries_summable_of_mem_ball' x hx) (norm_expSeries_summable_of_mem_ball' y hy)]
  dsimp only
  conv_lhs =>
    congr
    ext
    rw [hxy.add_pow' _]; rw [Finset.smul_sum]
  refine tsum_congr fun n => Finset.sum_congr rfl fun kl hkl => ?_
  rw [← Nat.cast_smul_eq_nsmul 𝕂]; rw [smul_smul]; rw [smul_mul_smul_comm]; rw [← Finset.mem_antidiagonal.mp hkl]; rw [Nat.cast_add_choose]; rw [Finset.mem_antidiagonal.mp hkl]
  field_simp [n.factorial_ne_zero]

/-- `NormedSpace.exp x` has explicit two-sided inverse `NormedSpace.exp (-x)`. -/
@[instance_reducible]
/--
Definition of `invertibleExpOfMemBall` / `invertibleExpOfMemBall` 的定义

English:
definition invertibleExpOfMemBall
  signature: [CharZero 𝕂] {x : 𝔸}
  body: exp (-x)
  invOf_mul_self := by
    have hnx : -x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius := by
      rw [Metric.mem_eball]; rw [← neg_zero]; rw [edist_neg_neg]
      exact hx
    rw [← exp_add_of_commute_of_mem_ball (Commute.neg_left <| Commute.refl x) hnx hx]; rw [neg_add_cancel]; rw [exp_z

中文:
定义 invertibleExpOfMemBall
  签名: [CharZero 𝕂] {x : 𝔸}
  定义体: exp (-x)
  invOf_mul_self := by
    have hnx : -x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius := by
      rw [Metric.mem_eball]; rw [← neg_zero]; rw [edist_neg_neg]
      exact hx
    rw [← exp_add_of_commute_of_mem_ball (Commute.neg_left <| Commute.refl x) hnx hx]; rw [neg_add_cancel]; rw [exp_z
-/
noncomputable def invertibleExpOfMemBall [CharZero 𝕂] {x : 𝔸}
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Invertible (exp x)
    where
  invOf := exp (-x)
  invOf_mul_self := by
    have hnx : -x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius := by
      rw [Metric.mem_eball]; rw [← neg_zero]; rw [edist_neg_neg]
      exact hx
    rw [← exp_add_of_commute_of_mem_ball (Commute.neg_left <| Commute.refl x) hnx hx]; rw [neg_add_cancel]; rw [exp_zero]
  mul_invOf_self := by
    have hnx : -x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius := by
      rw [Metric.mem_eball]; rw [← neg_zero]; rw [edist_neg_neg]
      exact hx
    rw [← exp_add_of_commute_of_mem_ball (Commute.neg_right <| Commute.refl x) hx hnx]; rw [add_neg_cancel]; rw [exp_zero]

/--
theorem `isUnit_exp_of_mem_ball` / 定理 `isUnit_exp_of_mem_ball`

English:
theorem isUnit_exp_of_mem_ball
  statement: [CharZero 𝕂] {x : 𝔸}
  proof: @isUnit_of_invertible _ _ _ (invertibleExpOfMemBall hx)

中文:
定理 isUnit_exp_of_mem_ball
  结论: [CharZero 𝕂] {x : 𝔸}
  证明: @isUnit_of_invertible _ _ _ (invertibleExpOfMemBall hx)

Depends on / 依赖: invertibleExpOfMemBall, isUnit_of_invertible
-/
theorem isUnit_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : IsUnit (exp x) :=
  @isUnit_of_invertible _ _ _ (invertibleExpOfMemBall hx)

/--
theorem `invOf_exp_of_mem_ball` / 定理 `invOf_exp_of_mem_ball`

English:
theorem invOf_exp_of_mem_ball
  statement: [CharZero 𝕂] {x : 𝔸}
  proof: by
  let := invertibleExpOfMemBall hx; convert! (rfl : ⅟(exp x) = _)

中文:
定理 invOf_exp_of_mem_ball
  结论: [CharZero 𝕂] {x : 𝔸}
  证明: by
  let := invertibleExpOfMemBall hx; convert! (rfl : ⅟(exp x) = _)

Depends on / 依赖: convert, invertibleExpOfMemBall
-/
theorem invOf_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) [Invertible (exp x)] :
    ⅟(exp x) = exp (-x) := by
  let := invertibleExpOfMemBall hx; convert! (rfl : ⅟(exp x) = _)

/--
theorem `map_exp_of_mem_ball` / 定理 `map_exp_of_mem_ball`

English:
theorem map_exp_of_mem_ball
  statement: [Algebra 𝕂 𝔹] [CharZero 𝕂] {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹]
  proof: by
  rw [exp_eq_tsum 𝕂]; rw [exp_eq_tsum 𝕂]
  refine ((expSeries_summable_of_mem_ball' _ hx).hasSum.map f hf).tsum_eq.symm.trans ?_
  dsimp only [Function.comp_def]
  simp_rw [map_inv_natCast_smul f 𝕂 𝕂, map_pow]

中文:
定理 map_exp_of_mem_ball
  结论: [Algebra 𝕂 𝔹] [CharZero 𝕂] {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹]
  证明: by
  rw [exp_eq_tsum 𝕂]; rw [exp_eq_tsum 𝕂]
  refine ((expSeries_summable_of_mem_ball' _ hx).hasSum.map f hf).tsum_eq.symm.trans ?_
  dsimp only [Function.comp_def]
  simp_rw [map_inv_natCast_smul f 𝕂 𝕂, map_pow]

Depends on / 依赖: Function, Function.comp_def, comp_def, expSeries_summable_of_mem_ball, exp_eq_tsum, hasSum, hasSum.map, map_inv_natCast_smul, map_pow, simp_rw, tsum_eq, tsum_eq.symm.trans
-/
theorem map_exp_of_mem_ball [Algebra 𝕂 𝔹] [CharZero 𝕂] {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹]
    (f : F) (hf : Continuous f) (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    f (exp x) = exp (f x) := by
  rw [exp_eq_tsum 𝕂]; rw [exp_eq_tsum 𝕂]
  refine ((expSeries_summable_of_mem_ball' _ hx).hasSum.map f hf).tsum_eq.symm.trans ?_
  dsimp only [Function.comp_def]
  simp_rw [map_inv_natCast_smul f 𝕂 𝕂, map_pow]

end CompleteAlgebra

/--
theorem `algebraMap_exp_comm_of_mem_ball` / 定理 `algebraMap_exp_comm_of_mem_ball`

English:
theorem algebraMap_exp_comm_of_mem_ball
  statement: [CharZero 𝕂] [CompleteSpace 𝕂] (x : 𝕂)
  proof: map_exp_of_mem_ball (algebraMap _ _) (algebraMapCLM _ _).continuous _ hx

中文:
定理 algebraMap_exp_comm_of_mem_ball
  结论: [CharZero 𝕂] [CompleteSpace 𝕂] (x : 𝕂)
  证明: map_exp_of_mem_ball (algebraMap _ _) (algebraMapCLM _ _).continuous _ hx

Depends on / 依赖: algebraMap, algebraMapCLM, continuous, map_exp_of_mem_ball
-/
theorem algebraMap_exp_comm_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝕂] (x : 𝕂)
    (hx : x in Metric.eball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) :
    algebraMap 𝕂 𝔸 (exp x) = exp (algebraMap 𝕂 𝔸 x) :=
  map_exp_of_mem_ball (algebraMap _ _) (algebraMapCLM _ _).continuous _ hx

end AnyFieldAnyAlgebra

section AnyFieldDivisionAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
variable (𝕂)

/--
theorem `norm_expSeries_div_summable_of_mem_ball` / 定理 `norm_expSeries_div_summable_of_mem_ball`

English:
theorem norm_expSeries_div_summable_of_mem_ball
  statement: (x : 𝔸)
  proof: by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq_div' (𝕂 := 𝕂) x]
  exact norm_expSeries_summable_of_mem_ball x hx

中文:
定理 norm_expSeries_div_summable_of_mem_ball
  结论: (x : 𝔸)
  证明: by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq_div' (𝕂 := 𝕂) x]
  exact norm_expSeries_summable_of_mem_ball x hx

Depends on / 依赖: Summable, expSeries_apply_eq_div, norm_expSeries_summable_of_mem_ball
-/
theorem norm_expSeries_div_summable_of_mem_ball (x : 𝔸)
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖x ^ n / (n !)‖ := by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq_div' (𝕂 := 𝕂) x]
  exact norm_expSeries_summable_of_mem_ball x hx

/--
theorem `expSeries_div_summable_of_mem_ball` / 定理 `expSeries_div_summable_of_mem_ball`

English:
theorem expSeries_div_summable_of_mem_ball
  statement: [CompleteSpace 𝔸] (x : 𝔸)
  proof: (norm_expSeries_div_summable_of_mem_ball 𝕂 x hx).of_norm

中文:
定理 expSeries_div_summable_of_mem_ball
  结论: [CompleteSpace 𝔸] (x : 𝔸)
  证明: (norm_expSeries_div_summable_of_mem_ball 𝕂 x hx).of_norm

Depends on / 依赖: norm_expSeries_div_summable_of_mem_ball, of_norm
-/
theorem expSeries_div_summable_of_mem_ball [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Summable fun n => x ^ n / n ! :=
  (norm_expSeries_div_summable_of_mem_ball 𝕂 x hx).of_norm

/--
theorem `expSeries_div_hasSum_exp_of_mem_ball` / 定理 `expSeries_div_hasSum_exp_of_mem_ball`

English:
theorem expSeries_div_hasSum_exp_of_mem_ball
  statement: [CharZero 𝕂] [CompleteSpace 𝔸] (x : 𝔸)
  proof: by
  rw [← expSeries_apply_eq_div' (𝕂 := 𝕂) x]
  exact expSeries_hasSum_exp_of_mem_ball x hx

中文:
定理 expSeries_div_hasSum_exp_of_mem_ball
  结论: [CharZero 𝕂] [CompleteSpace 𝔸] (x : 𝔸)
  证明: by
  rw [← expSeries_apply_eq_div' (𝕂 := 𝕂) x]
  exact expSeries_hasSum_exp_of_mem_ball x hx

Depends on / 依赖: expSeries_apply_eq_div, expSeries_hasSum_exp_of_mem_ball
-/
theorem expSeries_div_hasSum_exp_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => x ^ n / n !) (exp x) := by
  rw [← expSeries_apply_eq_div' (𝕂 := 𝕂) x]
  exact expSeries_hasSum_exp_of_mem_ball x hx

/--
theorem `exp_neg_of_mem_ball` / 定理 `exp_neg_of_mem_ball`

English:
theorem exp_neg_of_mem_ball
  statement: [CharZero 𝕂] [CompleteSpace 𝔸] {x : 𝔸}
  proof: letI := invertibleExpOfMemBall hx
  invOf_eq_inv (exp x)

中文:
定理 exp_neg_of_mem_ball
  结论: [CharZero 𝕂] [CompleteSpace 𝔸] {x : 𝔸}
  证明: letI := invertibleExpOfMemBall hx
  invOf_eq_inv (exp x)

Depends on / 依赖: invOf_eq_inv, invertibleExpOfMemBall
-/
theorem exp_neg_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝔸] {x : 𝔸}
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp (-x) = (exp x)⁻¹ :=
  letI := invertibleExpOfMemBall hx
  invOf_eq_inv (exp x)

end AnyFieldDivisionAlgebra

section AnyFieldCommAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

/--
theorem `exp_add_of_mem_ball` / 定理 `exp_add_of_mem_ball`

English:
theorem exp_add_of_mem_ball
  statement: [CharZero 𝕂] {x y : 𝔸}
  proof: exp_add_of_commute_of_mem_ball (Commute.all x y) hx hy

中文:
定理 exp_add_of_mem_ball
  结论: [CharZero 𝕂] {x y : 𝔸}
  证明: exp_add_of_commute_of_mem_ball (Commute.all x y) hx hy

Depends on / 依赖: Commute, Commute.all, exp_add_of_commute_of_mem_ball
-/
theorem exp_add_of_mem_ball [CharZero 𝕂] {x y : 𝔸}
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
    (hy : y in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (Commute.all x y) hx hy

end AnyFieldCommAlgebra

section AnyAlgebra

variable (𝕂 𝔸 : Type*) [NontriviallyNormedField 𝕂] [CharZero 𝕂] [ContinuousSMul Rat 𝕂]
variable [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/--
theorem `expSeries_radius_eq_top` / 定理 `expSeries_radius_eq_top`

English:
theorem expSeries_radius_eq_top
  statement: (expSeries 𝕂 𝔸).radius = ∞
  proof: by
  have {n : Nat} : (Nat.factorial n : 𝕂) != 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply expSeries_eq_ofScalars 𝕂 𝔸 ▸
    ofScalars_radius_eq_top_of_tendsto 𝔸 _ (Eventually.of_forall fun n => ?_)
  · simp_rw [← norm_div, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_div_right_

中文:
定理 expSeries_radius_eq_top
  结论: (expSeries 𝕂 𝔸).radius = ∞
  证明: by
  have {n : Nat} : (Nat.factorial n : 𝕂) != 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply expSeries_eq_ofScalars 𝕂 𝔸 ▸
    ofScalars_radius_eq_top_of_tendsto 𝔸 _ (Eventually.of_forall fun n => ?_)
  · simp_rw [← norm_div, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_div_right_

Depends on / 依赖: Eventually, Eventually.of_forall, Filter, Filter.Tendsto.norm, Filter.tendsto_add_atTop_iff_nat, Nat.cast_mul, Nat.cast_ne_zero.mpr, Nat.factorial, Nat.factorial_ne_zero, Nat.factorial_succ, Tendsto, cast_mul, cast_ne_zero, div_self, expSeries_eq_ofScalars, factorial, factorial_ne_zero, factorial_succ, inv_div_inv, mul_div_right_comm
-/
theorem expSeries_radius_eq_top : (expSeries 𝕂 𝔸).radius = ∞ := by
  have {n : Nat} : (Nat.factorial n : 𝕂) != 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply expSeries_eq_ofScalars 𝕂 𝔸 ▸
    ofScalars_radius_eq_top_of_tendsto 𝔸 _ (Eventually.of_forall fun n => ?_)
  · simp_rw [← norm_div, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_div_right_comm,
      inv_div_inv, norm_mul, div_self this, norm_one, one_mul]
    apply norm_zero (E := 𝕂) ▸ Filter.Tendsto.norm
    apply (Filter.tendsto_add_atTop_iff_nat (f := fun n => (n : 𝕂)⁻¹) 1).mpr
    exact tendsto_inv_atTop_nhds_zero_nat
  · simp [this]

/--
theorem `expSeries_radius_pos` / 定理 `expSeries_radius_pos`

English:
theorem expSeries_radius_pos
  statement: 0 < (expSeries 𝕂 𝔸).radius
  proof: by
  rw [expSeries_radius_eq_top]
  exact WithTop.top_pos

中文:
定理 expSeries_radius_pos
  结论: 0 < (expSeries 𝕂 𝔸).radius
  证明: by
  rw [expSeries_radius_eq_top]
  exact WithTop.top_pos

Depends on / 依赖: WithTop, WithTop.top_pos, expSeries_radius_eq_top, top_pos
-/
theorem expSeries_radius_pos : 0 < (expSeries 𝕂 𝔸).radius := by
  rw [expSeries_radius_eq_top]
  exact WithTop.top_pos

variable {𝕂 𝔸}

/--
theorem `norm_expSeries_summable` / 定理 `norm_expSeries_summable`

English:
theorem norm_expSeries_summable
  given: (x : 𝔸)
  statement: Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖
  proof: norm_expSeries_summable_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

中文:
定理 norm_expSeries_summable
  条件: (x : 𝔸)
  结论: Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖
  证明: norm_expSeries_summable_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, norm_expSeries_summable_of_mem_ball
-/
theorem norm_expSeries_summable (x : 𝔸) : Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖ :=
  norm_expSeries_summable_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/--
theorem `norm_expSeries_summable'` / 定理 `norm_expSeries_summable'`

English:
theorem norm_expSeries_summable'
  given: (x : 𝔸)
  statement: Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖
  proof: norm_expSeries_summable_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

中文:
定理 norm_expSeries_summable'
  条件: (x : 𝔸)
  结论: Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖
  证明: norm_expSeries_summable_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, norm_expSeries_summable_of_mem_ball
-/
theorem norm_expSeries_summable' (x : 𝔸) : Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖ :=
  norm_expSeries_summable_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/--
theorem `algebraMap_exp_comm` / 定理 `algebraMap_exp_comm`

English:
theorem algebraMap_exp_comm
  given: [CompleteSpace 𝕂] (x : 𝕂)
  proof: algebraMap_exp_comm_of_mem_ball x (expSeries_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _

中文:
定理 algebraMap_exp_comm
  条件: [CompleteSpace 𝕂] (x : 𝕂)
  证明: algebraMap_exp_comm_of_mem_ball x (expSeries_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _

Depends on / 依赖: algebraMap_exp_comm_of_mem_ball, edist_lt_top, expSeries_radius_eq_top
-/
theorem algebraMap_exp_comm [CompleteSpace 𝕂] (x : 𝕂) :
    algebraMap 𝕂 𝔸 (exp x) = exp (algebraMap 𝕂 𝔸 x) :=
algebraMap_exp_comm_of_mem_ball x (expSeries_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _

variable [CompleteSpace 𝔸]

/--
theorem `expSeries_summable` / 定理 `expSeries_summable`

English:
theorem expSeries_summable
  given: (x : 𝔸)
  statement: Summable fun n => expSeries 𝕂 𝔸 n fun _ => x
  proof: (norm_expSeries_summable x).of_norm

中文:
定理 expSeries_summable
  条件: (x : 𝔸)
  结论: Summable fun n => expSeries 𝕂 𝔸 n fun _ => x
  证明: (norm_expSeries_summable x).of_norm

Depends on / 依赖: norm_expSeries_summable, of_norm
-/
theorem expSeries_summable (x : 𝔸) : Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  (norm_expSeries_summable x).of_norm

/--
theorem `expSeries_summable'` / 定理 `expSeries_summable'`

English:
theorem expSeries_summable'
  given: (x : 𝔸)
  statement: Summable fun n => (n !⁻¹ : 𝕂) • x ^ n
  proof: (norm_expSeries_summable' x).of_norm

中文:
定理 expSeries_summable'
  条件: (x : 𝔸)
  结论: Summable fun n => (n !⁻¹ : 𝕂) • x ^ n
  证明: (norm_expSeries_summable' x).of_norm

Depends on / 依赖: norm_expSeries_summable, of_norm
-/
theorem expSeries_summable' (x : 𝔸) : Summable fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  (norm_expSeries_summable' x).of_norm

/--
theorem `expSeries_hasSum_exp` / 定理 `expSeries_hasSum_exp`

English:
theorem expSeries_hasSum_exp
  given: (x : 𝔸)
  statement: HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp x)
  proof: expSeries_hasSum_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

中文:
定理 expSeries_hasSum_exp
  条件: (x : 𝔸)
  结论: HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp x)
  证明: expSeries_hasSum_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

Depends on / 依赖: edist_lt_top, expSeries_hasSum_exp_of_mem_ball, expSeries_radius_eq_top
-/
theorem expSeries_hasSum_exp (x : 𝔸) : HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp x) :=
  expSeries_hasSum_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/--
theorem `exp_series_hasSum_exp'` / 定理 `exp_series_hasSum_exp'`

English:
theorem exp_series_hasSum_exp'
  given: (x : 𝔸)
  statement: HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (exp x)
  proof: expSeries_hasSum_exp_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

中文:
定理 exp_series_hasSum_exp'
  条件: (x : 𝔸)
  结论: HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (exp x)
  证明: expSeries_hasSum_exp_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

Depends on / 依赖: edist_lt_top, expSeries_hasSum_exp_of_mem_ball, expSeries_radius_eq_top
-/
theorem exp_series_hasSum_exp' (x : 𝔸) : HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (exp x) :=
  expSeries_hasSum_exp_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/--
theorem `exp_hasFPowerSeriesOnBall` / 定理 `exp_hasFPowerSeriesOnBall`

English:
theorem exp_hasFPowerSeriesOnBall
  statement: HasFPowerSeriesOnBall exp (expSeries 𝕂 𝔸) 0 ∞
  proof: expSeries_radius_eq_top 𝕂 𝔸 ▸ hasFPowerSeriesOnBall_exp_of_radius_pos (expSeries_radius_pos _ _)

中文:
定理 exp_hasFPowerSeriesOnBall
  结论: HasFPowerSeriesOnBall exp (expSeries 𝕂 𝔸) 0 ∞
  证明: expSeries_radius_eq_top 𝕂 𝔸 ▸ hasFPowerSeriesOnBall_exp_of_radius_pos (expSeries_radius_pos _ _)

Depends on / 依赖: expSeries_radius_eq_top, expSeries_radius_pos, hasFPowerSeriesOnBall_exp_of_radius_pos
-/
theorem exp_hasFPowerSeriesOnBall : HasFPowerSeriesOnBall exp (expSeries 𝕂 𝔸) 0 ∞ :=
  expSeries_radius_eq_top 𝕂 𝔸 ▸ hasFPowerSeriesOnBall_exp_of_radius_pos (expSeries_radius_pos _ _)

/--
theorem `exp_hasFPowerSeriesAt_zero` / 定理 `exp_hasFPowerSeriesAt_zero`

English:
theorem exp_hasFPowerSeriesAt_zero
  statement: HasFPowerSeriesAt exp (expSeries 𝕂 𝔸) 0
  proof: exp_hasFPowerSeriesOnBall.hasFPowerSeriesAt

中文:
定理 exp_hasFPowerSeriesAt_zero
  结论: HasFPowerSeriesAt exp (expSeries 𝕂 𝔸) 0
  证明: exp_hasFPowerSeriesOnBall.hasFPowerSeriesAt

Depends on / 依赖: exp_hasFPowerSeriesOnBall, exp_hasFPowerSeriesOnBall.hasFPowerSeriesAt, hasFPowerSeriesAt
-/
theorem exp_hasFPowerSeriesAt_zero : HasFPowerSeriesAt exp (expSeries 𝕂 𝔸) 0 :=
  exp_hasFPowerSeriesOnBall.hasFPowerSeriesAt

/--
theorem `exp_analytic` / 定理 `exp_analytic`

English:
theorem exp_analytic
  given: (x : 𝔸)
  statement: AnalyticAt 𝕂 exp x
  proof: analyticAt_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

中文:
定理 exp_analytic
  条件: (x : 𝔸)
  结论: AnalyticAt 𝕂 exp x
  证明: analyticAt_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

Depends on / 依赖: analyticAt_exp_of_mem_ball, edist_lt_top, expSeries_radius_eq_top
-/
theorem exp_analytic (x : 𝔸) : AnalyticAt 𝕂 exp x :=
  analyticAt_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end AnyAlgebra

section Rat
variable {𝔸 𝔹 : Type*} [NormedRing 𝔸] [NormedAlgebra Rat 𝔸] [CompleteSpace 𝔸] [NormedRing 𝔹]

@[continuity, fun_prop]
/--
theorem `exp_continuous` / 定理 `exp_continuous`

English:
theorem exp_continuous
  statement: Continuous (exp : 𝔸 -> 𝔸)
  proof: by
  rw [← continuousOn_univ]; rw [← Metric.eball_top_eq_univ (0 : 𝔸)]; rw [←
    expSeries_radius_eq_top Rat 𝔸]
  exact continuousOn_exp

中文:
定理 exp_continuous
  结论: Continuous (exp : 𝔸 -> 𝔸)
  证明: by
  rw [← continuousOn_univ]; rw [← Metric.eball_top_eq_univ (0 : 𝔸)]; rw [←
    expSeries_radius_eq_top Rat 𝔸]
  exact continuousOn_exp

Depends on / 依赖: Metric, Metric.eball_top_eq_univ, continuousOn_exp, continuousOn_univ, eball_top_eq_univ, expSeries_radius_eq_top
-/
theorem exp_continuous : Continuous (exp : 𝔸 -> 𝔸) := by
  rw [← continuousOn_univ]; rw [← Metric.eball_top_eq_univ (0 : 𝔸)]; rw [←
    expSeries_radius_eq_top Rat 𝔸]
  exact continuousOn_exp

open Topology in
/--
lemma `_root_.Filter.Tendsto.exp` / 引理 `_root_.Filter.Tendsto.exp`

English:
lemma _root_.Filter.Tendsto.exp
  statement: {α : Type*} {l : Filter α} {f : α -> 𝔸} {a : 𝔸}
  proof: (exp_continuous.tendsto _).comp hf

中文:
引理 _root_.Filter.Tendsto.exp
  结论: {α : 类型} {l : Filter α} {f : α -> 𝔸} {a : 𝔸}
  证明: (exp_continuous.tendsto _).comp hf

Depends on / 依赖: exp_continuous, exp_continuous.tendsto, tendsto
-/
lemma _root_.Filter.Tendsto.exp {α : Type*} {l : Filter α} {f : α -> 𝔸} {a : 𝔸}
    (hf : Tendsto f l (𝓝 a)) :
    Tendsto (fun x => exp (f x)) l (𝓝 (exp a)) :=
  (exp_continuous.tendsto _).comp hf

/--
theorem `exp_add_of_commute` / 定理 `exp_add_of_commute`

English:
theorem exp_add_of_commute
  given: {x y : 𝔸} (hxy : Commute x y)
  statement: exp (x + y) = exp x * exp y
  proof: exp_add_of_commute_of_mem_ball hxy ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)

中文:
定理 exp_add_of_commute
  条件: {x y : 𝔸} (hxy : Commute x y)
  结论: exp (x + y) = exp x * exp y
  证明: exp_add_of_commute_of_mem_ball hxy ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, exp_add_of_commute_of_mem_ball
-/
theorem exp_add_of_commute {x y : 𝔸} (hxy : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball hxy ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)

/-- `NormedSpace.exp x` has explicit two-sided inverse `NormedSpace.exp (-x)`. -/
@[instance_reducible]
/--
Definition of `invertibleExp` / `invertibleExp` 的定义

English:
definition invertibleExp
  signature: (x : 𝔸)
  body: invertibleExpOfMemBall (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

中文:
定义 invertibleExp
  签名: (x : 𝔸)
  定义体: invertibleExpOfMemBall (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, invertibleExpOfMemBall
-/
noncomputable def invertibleExp (x : 𝔸) : Invertible (exp x) :=
invertibleExpOfMemBall (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

/--
theorem `isUnit_exp` / 定理 `isUnit_exp`

English:
theorem isUnit_exp
  given: (x : 𝔸)
  statement: IsUnit (exp x)
  proof: isUnit_exp_of_mem_ball (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

中文:
定理 isUnit_exp
  条件: (x : 𝔸)
  结论: IsUnit (exp x)
  证明: isUnit_exp_of_mem_ball (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, isUnit_exp_of_mem_ball
-/
theorem isUnit_exp (x : 𝔸) : IsUnit (exp x) :=
isUnit_exp_of_mem_ball (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

/--
theorem `invOf_exp` / 定理 `invOf_exp`

English:
theorem invOf_exp
  given: (x : 𝔸) [Invertible (exp x)]
  statement: ⅟(exp x) = exp (-x)
  proof: invOf_exp_of_mem_ball (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

中文:
定理 invOf_exp
  条件: (x : 𝔸) [Invertible (exp x)]
  结论: ⅟(exp x) = exp (-x)
  证明: invOf_exp_of_mem_ball (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, invOf_exp_of_mem_ball
-/
theorem invOf_exp (x : 𝔸) [Invertible (exp x)] : ⅟(exp x) = exp (-x) :=
invOf_exp_of_mem_ball (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

/--
theorem `_root_.Ring.inverse_exp` / 定理 `_root_.Ring.inverse_exp`

English:
theorem _root_.Ring.inverse_exp
  given: (x : 𝔸)
  statement: (exp x)⁻¹ʳ = exp (-x)
  proof: letI := invertibleExp x
  Ring.inverse_invertible _

中文:
定理 _root_.Ring.inverse_exp
  条件: (x : 𝔸)
  结论: (exp x)⁻¹ʳ = exp (-x)
  证明: letI := invertibleExp x
  Ring.inverse_invertible _

Depends on / 依赖: Ring.inverse_invertible, inverse_invertible, invertibleExp
-/
theorem _root_.Ring.inverse_exp (x : 𝔸) : (exp x)⁻¹ʳ = exp (-x) :=
  letI := invertibleExp x
  Ring.inverse_invertible _

/--
theorem `exp_mem_unitary_of_mem_skewAdjoint` / 定理 `exp_mem_unitary_of_mem_skewAdjoint`

English:
theorem exp_mem_unitary_of_mem_skewAdjoint
  statement: [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
  proof: by
  rw [Unitary.mem_iff]; rw [star_exp]; rw [skewAdjoint.mem_iff.mp h]; rw [←
    exp_add_of_commute (Commute.refl x).neg_left]; rw [← exp_add_of_commute (Commute.refl x).neg_right]; rw [neg_add_cancel]; rw [add_neg_cancel]; rw [exp_zero]; rw [and_self_iff]

中文:
定理 exp_mem_unitary_of_mem_skewAdjoint
  结论: [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
  证明: by
  rw [Unitary.mem_iff]; rw [star_exp]; rw [skewAdjoint.mem_iff.mp h]; rw [←
    exp_add_of_commute (Commute.refl x).neg_left]; rw [← exp_add_of_commute (Commute.refl x).neg_right]; rw [neg_add_cancel]; rw [add_neg_cancel]; rw [exp_zero]; rw [and_self_iff]

Depends on / 依赖: Commute, Commute.refl, Unitary, Unitary.mem_iff, add_neg_cancel, and_self_iff, exp_add_of_commute, exp_zero, mem_iff, neg_add_cancel, neg_left, neg_right, skewAdjoint, skewAdjoint.mem_iff.mp, star_exp
-/
theorem exp_mem_unitary_of_mem_skewAdjoint [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
    (h : x in skewAdjoint 𝔸) : exp x in unitary 𝔸 := by
  rw [Unitary.mem_iff]; rw [star_exp]; rw [skewAdjoint.mem_iff.mp h]; rw [←
    exp_add_of_commute (Commute.refl x).neg_left]; rw [← exp_add_of_commute (Commute.refl x).neg_right]; rw [neg_add_cancel]; rw [add_neg_cancel]; rw [exp_zero]; rw [and_self_iff]

/--
lemma `_root_.SemiconjBy.exp_right` / 引理 `_root_.SemiconjBy.exp_right`

English:
lemma _root_.SemiconjBy.exp_right
  given: {x a b : 𝔸} (h : SemiconjBy x a b)
  proof: by
  rw [exp_eq_tsum Rat]
  apply SemiconjBy.tsum_right x (expSeries_summable' _) (expSeries_summable' _)
.smul_right _ exact fun _ => h.pow_right _

中文:
引理 _root_.SemiconjBy.exp_right
  条件: {x a b : 𝔸} (h : SemiconjBy x a b)
  证明: by
  rw [exp_eq_tsum Rat]
  apply SemiconjBy.tsum_right x (expSeries_summable' _) (expSeries_summable' _)
.smul_right _ exact fun _ => h.pow_right _

Depends on / 依赖: SemiconjBy, SemiconjBy.tsum_right, expSeries_summable, exp_eq_tsum, h.pow_right, pow_right, smul_right, tsum_right
-/
lemma _root_.SemiconjBy.exp_right {x a b : 𝔸} (h : SemiconjBy x a b) :
    SemiconjBy x (exp a) (exp b) := by
  rw [exp_eq_tsum Rat]
  apply SemiconjBy.tsum_right x (expSeries_summable' _) (expSeries_summable' _)
.smul_right _ exact fun _ => h.pow_right _

/--
lemma `_root_.SemiconjBy.exp_neg_mul_mul_exp_eq_self` / 引理 `_root_.SemiconjBy.exp_neg_mul_mul_exp_eq_self`

English:
lemma _root_.SemiconjBy.exp_neg_mul_mul_exp_eq_self
  given: {x a b : 𝔸} (h : SemiconjBy x a b)
  proof: by
  let := invertibleExp b
  simpa [← invOf_exp, mul_assoc, invOf_mul_eq_iff_eq_mul_left] using! h.exp_right

中文:
引理 _root_.SemiconjBy.exp_neg_mul_mul_exp_eq_self
  条件: {x a b : 𝔸} (h : SemiconjBy x a b)
  证明: by
  let := invertibleExp b
  simpa [← invOf_exp, mul_assoc, invOf_mul_eq_iff_eq_mul_left] using! h.exp_right

Depends on / 依赖: exp_right, h.exp_right, invOf_exp, invOf_mul_eq_iff_eq_mul_left, invertibleExp, mul_assoc
-/
lemma _root_.SemiconjBy.exp_neg_mul_mul_exp_eq_self {x a b : 𝔸} (h : SemiconjBy x a b) :
    exp (-b) * x * exp a = x := by
  let := invertibleExp b
  simpa [← invOf_exp, mul_assoc, invOf_mul_eq_iff_eq_mul_left] using! h.exp_right

set_option backward.isDefEq.respectTransparency false in
open scoped Function in -- required for scoped `on` notation
/--
theorem `exp_sum_of_commute` / 定理 `exp_sum_of_commute`

English:
theorem exp_sum_of_commute
  statement: {ι} (s : Finset ι) (f : ι -> 𝔸)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]; rw [Finset.sum_insert ha]; rw [exp_add_of_commute]; rw [ih (h.mono <| Finset.subset_insert _ _)]
    refine Commute.sum_right _ _ _ fun i hi 

中文:
定理 exp_sum_of_commute
  结论: {ι} (s : Finset ι) (f : ι -> 𝔸)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]; rw [Finset.sum_insert ha]; rw [exp_add_of_commute]; rw [ih (h.mono <| Finset.subset_insert _ _)]
    refine Commute.sum_right _ _ _ fun i hi 

Depends on / 依赖: Commute, Commute.sum_right, Finset, Finset.induction_on, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.noncommProd_insert_of_notMem, Finset.subset_insert, Finset.sum_insert, classical, exp_add_of_commute, h.mono, h.of_refl, induction_on, insert, mem_insert_of_mem, mem_insert_self, noncommProd_insert_of_notMem, of_refl, subset_insert
-/
theorem exp_sum_of_commute {ι} (s : Finset ι) (f : ι -> 𝔸)
    (h : (s : Set ι).Pairwise (Commute on f)) :
    exp (∑ i in s, f i) =
      s.noncommProd (fun i => exp (f i)) fun _ hi _ hj _ => (h.of_refl hi hj).exp := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]; rw [Finset.sum_insert ha]; rw [exp_add_of_commute]; rw [ih (h.mono <| Finset.subset_insert _ _)]
    refine Commute.sum_right _ _ _ fun i hi => ?_
    exact h.of_refl (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi)

/--
theorem `exp_nsmul` / 定理 `exp_nsmul`

English:
theorem exp_nsmul
  given: (n : Nat) (x : 𝔸)
  statement: exp (n • x) = exp x ^ n
  proof: by
  induction n with
  | zero => rw [zero_smul, pow_zero, exp_zero]
  | succ n ih => rw [succ_nsmul, pow_succ, exp_add_of_commute ((Commute.refl x).smul_left n), ih]

中文:
定理 exp_nsmul
  条件: (n : 自然数) (x : 𝔸)
  结论: exp (n • x) = exp x ^ n
  证明: by
  induction n with
  | zero => rw [zero_smul, pow_zero, exp_zero]
  | succ n ih => rw [succ_nsmul, pow_succ, exp_add_of_commute ((Commute.refl x).smul_left n), ih]

Depends on / 依赖: Commute, Commute.refl, exp_add_of_commute, exp_zero, pow_succ, pow_zero, smul_left, succ_nsmul, zero_smul
-/
theorem exp_nsmul (n : Nat) (x : 𝔸) : exp (n • x) = exp x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, exp_zero]
  | succ n ih => rw [succ_nsmul, pow_succ, exp_add_of_commute ((Commute.refl x).smul_left n), ih]

/--
theorem `map_exp` / 定理 `map_exp`

English:
theorem map_exp
  statement: [Algebra Rat 𝔹]
  proof: map_exp_of_mem_ball f hf x (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

中文:
定理 map_exp
  结论: [Algebra Rat 𝔹]
  证明: map_exp_of_mem_ball f hf x (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, map_exp_of_mem_ball
-/
theorem map_exp [Algebra Rat 𝔹]
    {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x : 𝔸) :
    f (exp x) = exp (f x) :=
map_exp_of_mem_ball f hf x (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

/--
theorem `exp_smul` / 定理 `exp_smul`

English:
theorem exp_smul
  given: {G} [Monoid G] [MulSemiringAction G 𝔸] [ContinuousConstSMul G 𝔸] (g : G) (x : 𝔸)
  proof: (map_exp (MulSemiringAction.toRingHom G 𝔸 g) (continuous_const_smul g) x).symm

中文:
定理 exp_smul
  条件: {G} [Monoid G] [MulSemiringAction G 𝔸] [ContinuousConstSMul G 𝔸] (g : G) (x : 𝔸)
  证明: (map_exp (MulSemiringAction.toRingHom G 𝔸 g) (continuous_const_smul g) x).symm

Depends on / 依赖: MulSemiringAction, MulSemiringAction.toRingHom, continuous_const_smul, map_exp, toRingHom
-/
theorem exp_smul {G} [Monoid G] [MulSemiringAction G 𝔸] [ContinuousConstSMul G 𝔸] (g : G) (x : 𝔸) :
    exp (g • x) = g • exp x :=
  (map_exp (MulSemiringAction.toRingHom G 𝔸 g) (continuous_const_smul g) x).symm

/--
theorem `exp_units_conj` / 定理 `exp_units_conj`

English:
theorem exp_units_conj
  given: (y : 𝔸ˣ) (x : 𝔸)
  statement: exp (y * x * ↑y⁻¹ : 𝔸) = y * exp x * ↑y⁻¹
  proof: exp_smul (ConjAct.toConjAct y) x

中文:
定理 exp_units_conj
  条件: (y : 𝔸ˣ) (x : 𝔸)
  结论: exp (y * x * ↑y⁻¹ : 𝔸) = y * exp x * ↑y⁻¹
  证明: exp_smul (ConjAct.toConjAct y) x

Depends on / 依赖: ConjAct, ConjAct.toConjAct, exp_smul, toConjAct
-/
theorem exp_units_conj (y : 𝔸ˣ) (x : 𝔸) : exp (y * x * ↑y⁻¹ : 𝔸) = y * exp x * ↑y⁻¹ :=
  exp_smul (ConjAct.toConjAct y) x

/--
theorem `exp_units_conj'` / 定理 `exp_units_conj'`

English:
theorem exp_units_conj'
  given: (y : 𝔸ˣ) (x : 𝔸)
  statement: exp (↑y⁻¹ * x * y) = ↑y⁻¹ * exp x * y
  proof: exp_units_conj _ _

@[simp]

中文:
定理 exp_units_conj'
  条件: (y : 𝔸ˣ) (x : 𝔸)
  结论: exp (↑y⁻¹ * x * y) = ↑y⁻¹ * exp x * y
  证明: exp_units_conj _ _

@[simp]

Depends on / 依赖: exp_units_conj
-/
theorem exp_units_conj' (y : 𝔸ˣ) (x : 𝔸) : exp (↑y⁻¹ * x * y) = ↑y⁻¹ * exp x * y :=
  exp_units_conj _ _

@[simp]
/--
theorem `_root_.Prod.fst_exp` / 定理 `_root_.Prod.fst_exp`

English:
theorem _root_.Prod.fst_exp
  given: [NormedAlgebra Rat 𝔹] [CompleteSpace 𝔹] (x : 𝔸 × 𝔹)
  proof: map_exp (RingHom.fst 𝔸 𝔹) continuous_fst x

@[simp]

中文:
定理 _root_.Prod.fst_exp
  条件: [NormedAlgebra Rat 𝔹] [CompleteSpace 𝔹] (x : 𝔸 × 𝔹)
  证明: map_exp (RingHom.fst 𝔸 𝔹) continuous_fst x

@[simp]

Depends on / 依赖: RingHom, RingHom.fst, continuous_fst, map_exp
-/
theorem _root_.Prod.fst_exp [NormedAlgebra Rat 𝔹] [CompleteSpace 𝔹] (x : 𝔸 × 𝔹) :
    (exp x).fst = exp x.fst :=
  map_exp (RingHom.fst 𝔸 𝔹) continuous_fst x

@[simp]
/--
theorem `_root_.Prod.snd_exp` / 定理 `_root_.Prod.snd_exp`

English:
theorem _root_.Prod.snd_exp
  given: [NormedAlgebra Rat 𝔹] [CompleteSpace 𝔹] (x : 𝔸 × 𝔹)
  proof: map_exp (RingHom.snd 𝔸 𝔹) continuous_snd x

@[simp]

中文:
定理 _root_.Prod.snd_exp
  条件: [NormedAlgebra Rat 𝔹] [CompleteSpace 𝔹] (x : 𝔸 × 𝔹)
  证明: map_exp (RingHom.snd 𝔸 𝔹) continuous_snd x

@[simp]

Depends on / 依赖: RingHom, RingHom.snd, continuous_snd, map_exp
-/
theorem _root_.Prod.snd_exp [NormedAlgebra Rat 𝔹] [CompleteSpace 𝔹] (x : 𝔸 × 𝔹) :
    (exp x).snd = exp x.snd :=
  map_exp (RingHom.snd 𝔸 𝔹) continuous_snd x

@[simp]
/--
theorem `_root_.Pi.coe_exp` / 定理 `_root_.Pi.coe_exp`

English:
theorem _root_.Pi.coe_exp
  statement: {ι : Type*} {𝔸 : ι -> Type*} [Finite ι] [forall i, NormedRing (𝔸 i)]
  proof: let ⟨_⟩ := nonempty_fintype ι
  map_exp (Pi.evalRingHom 𝔸 i) (continuous_apply _) x

中文:
定理 _root_.Pi.coe_exp
  结论: {ι : 类型} {𝔸 : ι -> 类型} [Finite ι] [对任意 i, NormedRing (𝔸 i)]
  证明: let ⟨_⟩ := nonempty_fintype ι
  map_exp (Pi.evalRingHom 𝔸 i) (continuous_apply _) x

Depends on / 依赖: Pi.evalRingHom, continuous_apply, evalRingHom, map_exp, nonempty_fintype
-/
theorem _root_.Pi.coe_exp {ι : Type*} {𝔸 : ι -> Type*} [Finite ι] [forall i, NormedRing (𝔸 i)]
    [forall i, NormedAlgebra Rat (𝔸 i)] [forall i, CompleteSpace (𝔸 i)] (x : forall i, 𝔸 i) (i : ι) :
    exp x i = exp (x i) :=
  let ⟨_⟩ := nonempty_fintype ι
  map_exp (Pi.evalRingHom 𝔸 i) (continuous_apply _) x

/--
theorem `_root_.Pi.exp_def` / 定理 `_root_.Pi.exp_def`

English:
theorem _root_.Pi.exp_def
  statement: {ι : Type*} {𝔸 : ι -> Type*} [Finite ι] [forall i, NormedRing (𝔸 i)]
  proof: funext Pi.coe_exp x

中文:
定理 _root_.Pi.exp_def
  结论: {ι : 类型} {𝔸 : ι -> 类型} [Finite ι] [对任意 i, NormedRing (𝔸 i)]
  证明: funext Pi.coe_exp x

Depends on / 依赖: Pi.coe_exp, coe_exp
-/
theorem _root_.Pi.exp_def {ι : Type*} {𝔸 : ι -> Type*} [Finite ι] [forall i, NormedRing (𝔸 i)]
    [forall i, NormedAlgebra Rat (𝔸 i)] [forall i, CompleteSpace (𝔸 i)] (x : forall i, 𝔸 i) :
    exp x = fun i => exp (x i) :=
funext Pi.coe_exp x

/--
theorem `_root_.Function.update_exp` / 定理 `_root_.Function.update_exp`

English:
theorem _root_.Function.update_exp
  statement: {ι : Type*} {𝔸 : ι -> Type*} [Finite ι] [DecidableEq ι]
  proof: by
  ext i
  simp_rw [Pi.exp_def]
  exact (Function.apply_update (fun i => exp) x j xj i).symm

中文:
定理 _root_.Function.update_exp
  结论: {ι : 类型} {𝔸 : ι -> 类型} [Finite ι] [DecidableEq ι]
  证明: by
  ext i
  simp_rw [Pi.exp_def]
  exact (Function.apply_update (fun i => exp) x j xj i).symm

Depends on / 依赖: Function, Function.apply_update, Pi.exp_def, apply_update, exp_def, simp_rw
-/
theorem _root_.Function.update_exp {ι : Type*} {𝔸 : ι -> Type*} [Finite ι] [DecidableEq ι]
    [forall i, NormedRing (𝔸 i)] [forall i, NormedAlgebra Rat (𝔸 i)] [forall i, CompleteSpace (𝔸 i)] (x : forall i, 𝔸 i)
    (j : ι) (xj : 𝔸 j) :
    Function.update (exp x) j (exp xj) = exp (Function.update x j xj) := by
  ext i
  simp_rw [Pi.exp_def]
  exact (Function.apply_update (fun i => exp) x j xj i).symm

end Rat

section DivisionAlgebra

variable {𝔸 : Type*} [NormedDivisionRing 𝔸] [NormedAlgebra Rat 𝔸]

/--
theorem `norm_expSeries_div_summable` / 定理 `norm_expSeries_div_summable`

English:
theorem norm_expSeries_div_summable
  given: (x : 𝔸)
  statement: Summable fun n => ‖(x ^ n / n ! : 𝔸)‖
  proof: norm_expSeries_div_summable_of_mem_ball Rat x
    ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)

中文:
定理 norm_expSeries_div_summable
  条件: (x : 𝔸)
  结论: Summable fun n => ‖(x ^ n / n ! : 𝔸)‖
  证明: norm_expSeries_div_summable_of_mem_ball Rat x
    ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, norm_expSeries_div_summable_of_mem_ball
-/
theorem norm_expSeries_div_summable (x : 𝔸) : Summable fun n => ‖(x ^ n / n ! : 𝔸)‖ :=
  norm_expSeries_div_summable_of_mem_ball Rat x
    ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)

variable [CompleteSpace 𝔸]

/--
theorem `expSeries_div_summable` / 定理 `expSeries_div_summable`

English:
theorem expSeries_div_summable
  given: (x : 𝔸)
  statement: Summable fun n => x ^ n / n !
  proof: (norm_expSeries_div_summable x).of_norm

中文:
定理 expSeries_div_summable
  条件: (x : 𝔸)
  结论: Summable fun n => x ^ n / n !
  证明: (norm_expSeries_div_summable x).of_norm

Depends on / 依赖: norm_expSeries_div_summable, of_norm
-/
theorem expSeries_div_summable (x : 𝔸) : Summable fun n => x ^ n / n ! :=
  (norm_expSeries_div_summable x).of_norm

/--
theorem `expSeries_div_hasSum_exp` / 定理 `expSeries_div_hasSum_exp`

English:
theorem expSeries_div_hasSum_exp
  given: (x : 𝔸)
  statement: HasSum (fun n => x ^ n / n !) (exp x)
  proof: expSeries_div_hasSum_exp_of_mem_ball Rat x ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)

中文:
定理 expSeries_div_hasSum_exp
  条件: (x : 𝔸)
  结论: HasSum (fun n => x ^ n / n !) (exp x)
  证明: expSeries_div_hasSum_exp_of_mem_ball Rat x ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)

Depends on / 依赖: edist_lt_top, expSeries_div_hasSum_exp_of_mem_ball, expSeries_radius_eq_top
-/
theorem expSeries_div_hasSum_exp (x : 𝔸) : HasSum (fun n => x ^ n / n !) (exp x) :=
  expSeries_div_hasSum_exp_of_mem_ball Rat x ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)

/--
theorem `exp_neg` / 定理 `exp_neg`

English:
theorem exp_neg
  given: (x : 𝔸)
  statement: exp (-x) = (exp x)⁻¹
  proof: exp_neg_of_mem_ball Rat (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

中文:
定理 exp_neg
  条件: (x : 𝔸)
  结论: exp (-x) = (exp x)⁻¹
  证明: exp_neg_of_mem_ball Rat (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, exp_neg_of_mem_ball
-/
theorem exp_neg (x : 𝔸) : exp (-x) = (exp x)⁻¹ :=
exp_neg_of_mem_ball Rat (expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _

/--
theorem `exp_zsmul` / 定理 `exp_zsmul`

English:
theorem exp_zsmul
  given: (z : Int) (x : 𝔸)
  statement: exp (z • x) = exp x ^ z
  proof: by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [zpow_natCast, natCast_zsmul, exp_nsmul]
  · rw [zpow_neg, zpow_natCast, neg_smul, exp_neg, natCast_zsmul, exp_nsmul]

中文:
定理 exp_zsmul
  条件: (z : 整数) (x : 𝔸)
  结论: exp (z • x) = exp x ^ z
  证明: by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [zpow_natCast, natCast_zsmul, exp_nsmul]
  · rw [zpow_neg, zpow_natCast, neg_smul, exp_neg, natCast_zsmul, exp_nsmul]

Depends on / 依赖: eq_nat_or_neg, exp_neg, exp_nsmul, natCast_zsmul, neg_smul, z.eq_nat_or_neg, zpow_natCast, zpow_neg
-/
theorem exp_zsmul (z : Int) (x : 𝔸) : exp (z • x) = exp x ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [zpow_natCast, natCast_zsmul, exp_nsmul]
  · rw [zpow_neg, zpow_natCast, neg_smul, exp_neg, natCast_zsmul, exp_nsmul]

/--
theorem `exp_conj` / 定理 `exp_conj`

English:
theorem exp_conj
  given: (y : 𝔸) (x : 𝔸) (hy : y != 0)
  statement: exp (y * x * y⁻¹) = y * exp x * y⁻¹
  proof: exp_units_conj (Units.mk0 y hy) x

中文:
定理 exp_conj
  条件: (y : 𝔸) (x : 𝔸) (hy : y != 0)
  结论: exp (y * x * y⁻¹) = y * exp x * y⁻¹
  证明: exp_units_conj (Units.mk0 y hy) x

Depends on / 依赖: Units.mk0, exp_units_conj
-/
theorem exp_conj (y : 𝔸) (x : 𝔸) (hy : y != 0) : exp (y * x * y⁻¹) = y * exp x * y⁻¹ :=
  exp_units_conj (Units.mk0 y hy) x

/--
theorem `exp_conj'` / 定理 `exp_conj'`

English:
theorem exp_conj'
  given: (y : 𝔸) (x : 𝔸) (hy : y != 0)
  statement: exp (y⁻¹ * x * y) = y⁻¹ * exp x * y
  proof: exp_units_conj' (Units.mk0 y hy) x

中文:
定理 exp_conj'
  条件: (y : 𝔸) (x : 𝔸) (hy : y != 0)
  结论: exp (y⁻¹ * x * y) = y⁻¹ * exp x * y
  证明: exp_units_conj' (Units.mk0 y hy) x

Depends on / 依赖: Units.mk0, exp_units_conj
-/
theorem exp_conj' (y : 𝔸) (x : 𝔸) (hy : y != 0) : exp (y⁻¹ * x * y) = y⁻¹ * exp x * y :=
  exp_units_conj' (Units.mk0 y hy) x

end DivisionAlgebra

section CommAlgebra

variable {𝕂 𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra Rat 𝔸] [CompleteSpace 𝔸]

/--
theorem `exp_add` / 定理 `exp_add`

English:
theorem exp_add
  given: {x y : 𝔸}
  statement: exp (x + y) = exp x * exp y
  proof: exp_add_of_mem_ball ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)

中文:
定理 exp_add
  条件: {x y : 𝔸}
  结论: exp (x + y) = exp x * exp y
  证明: exp_add_of_mem_ball ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, exp_add_of_mem_ball
-/
theorem exp_add {x y : 𝔸} : exp (x + y) = exp x * exp y :=
  exp_add_of_mem_ball ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top Rat 𝔸).symm ▸ edist_lt_top _ _)

/--
theorem `exp_sum` / 定理 `exp_sum`

English:
theorem exp_sum
  given: {ι} (s : Finset ι) (f : ι -> 𝔸)
  statement: exp (∑ i in s, f i) = ∏ i in s, exp (f i)
  proof: by
  rw [exp_sum_of_commute]; rw [Finset.noncommProd_eq_prod]
  exact fun i _hi j _hj _ => Commute.all _ _

中文:
定理 exp_sum
  条件: {ι} (s : Finset ι) (f : ι -> 𝔸)
  结论: exp (∑ i in s, f i) = ∏ i in s, exp (f i)
  证明: by
  rw [exp_sum_of_commute]; rw [Finset.noncommProd_eq_prod]
  exact fun i _hi j _hj _ => Commute.all _ _

Depends on / 依赖: Commute, Commute.all, Finset, Finset.noncommProd_eq_prod, exp_sum_of_commute, noncommProd_eq_prod
-/
theorem exp_sum {ι} (s : Finset ι) (f : ι -> 𝔸) : exp (∑ i in s, f i) = ∏ i in s, exp (f i) := by
  rw [exp_sum_of_commute]; rw [Finset.noncommProd_eq_prod]
  exact fun i _hi j _hj _ => Commute.all _ _

end CommAlgebra

end Normed

section ScalarTower

variable (𝕂 𝕂' 𝔸 : Type*) [Field 𝕂] [Field 𝕂'] [Ring 𝔸] [Algebra 𝕂 𝔸] [Algebra 𝕂' 𝔸]
  [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

/--
theorem `expSeries_eq_expSeries` / 定理 `expSeries_eq_expSeries`

English:
theorem expSeries_eq_expSeries
  given: (n : Nat) (x : 𝔸)
  proof: by
  rw [expSeries_apply_eq]; rw [expSeries_apply_eq]; rw [inv_natCast_smul_eq 𝕂 𝕂']

中文:
定理 expSeries_eq_expSeries
  条件: (n : 自然数) (x : 𝔸)
  证明: by
  rw [expSeries_apply_eq]; rw [expSeries_apply_eq]; rw [inv_natCast_smul_eq 𝕂 𝕂']

Depends on / 依赖: expSeries_apply_eq, inv_natCast_smul_eq
-/
theorem expSeries_eq_expSeries (n : Nat) (x : 𝔸) :
    (expSeries 𝕂 𝔸 n fun _ => x) = expSeries 𝕂' 𝔸 n fun _ => x := by
  rw [expSeries_apply_eq]; rw [expSeries_apply_eq]; rw [inv_natCast_smul_eq 𝕂 𝕂']

/-- A version of `Complex.ofReal_exp` for `NormedSpace.exp` instead of `Complex.exp` -/
@[simp, norm_cast]
/--
theorem `ofReal_exp_Real_Real` / 定理 `ofReal_exp_Real_Real`

English:
theorem ofReal_exp_Real_Real
  given: (r : Real)
  statement: ↑(exp r) = exp (r : Complex)
  proof: map_exp (algebraMap Real Complex) (continuous_algebraMap _ _) r

中文:
定理 ofReal_exp_Real_Real
  条件: (r : 实数)
  结论: ↑(exp r) = exp (r : Complex)
  证明: map_exp (algebraMap Real Complex) (continuous_algebraMap _ _) r

Depends on / 依赖: algebraMap, continuous_algebraMap, map_exp
-/
theorem ofReal_exp_Real_Real (r : Real) : ↑(exp r) = exp (r : Complex) :=
  map_exp (algebraMap Real Complex) (continuous_algebraMap _ _) r

end ScalarTower

end NormedSpace
