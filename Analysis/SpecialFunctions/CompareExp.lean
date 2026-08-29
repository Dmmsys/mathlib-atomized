/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Growth estimates on `x ^ y` for complex `x`, `y`

Let `l` be a filter on `ℂ` such that `Complex.re` tends to infinity along `l` and `Complex.im z`
grows at a subexponential rate compared to `Complex.re z`. Then

- `Complex.isLittleO_log_abs_re`: `Real.log ∘ Complex.abs` is `o`-small of
  `Complex.re` along `l`;

- `Complex.isLittleO_cpow_mul_exp`: $z^{a_1}e^{b_1 * z} = o\left(z^{a_1}e^{b_1 * z}\right)$
  along `l` for any complex `a₁`, `a₂` and real `b₁ < b₂`.

We use these assumptions on `l` for two reasons. First, these are the assumptions that naturally
appear in the proof. Second, in some applications (e.g., in Ilyashenko's proof of the individual
finiteness theorem for limit cycles of polynomial ODEs with hyperbolic singularities only) natural
stronger assumptions (e.g., `im z` is bounded from below and from above) are not available.

-/

public section


open Asymptotics Filter Function
open scoped Topology

namespace Complex

/--
Definition of `IsExpCmpFilter` / `IsExpCmpFilter` 的定义

English:
structure IsExpCmpFilter
  parameters: (l : Filter Complex)
  axioms and operations (2):
    - tendsto_re : Tendsto re l atTop
    - isBigO_im_pow_re : forall n : Nat, (fun z : Complex => z.im ^ n) =O[l] fun z => Real.exp z.re

中文:
结构 是ExpCmpFilter
  参数: (l : 滤子 复形)
  公理与运算 (2 个):
    - tendsto_re : 收敛 re l atTop
    - isBigO_im_pow_re : 对任意 n : 自然数, (fun z : 复形 => z.im ^ n) =O[l] fun z => 实数.exp z.re
-/
structure IsExpCmpFilter (l : Filter Complex) : Prop where
  tendsto_re : Tendsto re l atTop
  isBigO_im_pow_re : forall n : Nat, (fun z : Complex => z.im ^ n) =O[l] fun z => Real.exp z.re

namespace IsExpCmpFilter

variable {l : Filter Complex}


/--
theorem `of_isBigO_im_re_rpow` / 定理 `of_isBigO_im_re_rpow`

English:
theorem of_isBigO_im_re_rpow
  given: (hre : Tendsto re l atTop) (r : Real) (hr : im =O[l] fun z => z.re ^ r)
  proof: ⟨hre, fun n =>
IsLittleO.isBigO
      calc
        (fun z : Complex => z.im ^ n) =O[l] fun z => (z.re ^ r) ^ n := hr.pow n
        _ =ᶠ[l] fun z => z.re ^ (r * n) :=
          ((hre.eventually_ge_atTop 0).mono fun z hz => by
            simp only [Real.rpow_mul hz r n, Real.rpow_natCast])
        _ 

中文:
定理 of_isBigO_im_re_rpow
  条件: (hre : 收敛 re l atTop) (r : 实数) (hr : im =O[l] fun z => z.re ^ r)
  证明: ⟨hre, fun n =>
IsLittleO.isBigO
      calc
        (fun z : Complex => z.im ^ n) =O[l] fun z => (z.re ^ r) ^ n := hr.pow n
        _ =ᶠ[l] fun z => z.re ^ (r * n) :=
          ((hre.eventually_ge_atTop 0).mono fun z hz => by
            simp only [Real.rpow_mul hz r n, Real.rpow_natCast])
        _ 

Depends on / 依赖: IsLittleO, IsLittleO.isBigO, Real.exp, Real.rpow_mul, Real.rpow_natCast, comp_tendsto, eventually_ge_atTop, hr.pow, hre.eventually_ge_atTop, isBigO, isLittleO_rpow_exp_atTop, rpow_mul, rpow_natCast, z.im, z.re
-/
theorem of_isBigO_im_re_rpow (hre : Tendsto re l atTop) (r : Real) (hr : im =O[l] fun z => z.re ^ r) :
    IsExpCmpFilter l :=
  ⟨hre, fun n =>
IsLittleO.isBigO
      calc
        (fun z : Complex => z.im ^ n) =O[l] fun z => (z.re ^ r) ^ n := hr.pow n
        _ =ᶠ[l] fun z => z.re ^ (r * n) :=
          ((hre.eventually_ge_atTop 0).mono fun z hz => by
            simp only [Real.rpow_mul hz r n, Real.rpow_natCast])
        _ =o[l] fun z => Real.exp z.re := (isLittleO_rpow_exp_atTop _).comp_tendsto hre ⟩

/--
theorem `of_isBigO_im_re_pow` / 定理 `of_isBigO_im_re_pow`

English:
theorem of_isBigO_im_re_pow
  given: (hre : Tendsto re l atTop) (n : Nat) (hr : im =O[l] fun z => z.re ^ n)
  proof: of_isBigO_im_re_rpow hre n mod_cast hr

中文:
定理 of_isBigO_im_re_pow
  条件: (hre : 收敛 re l atTop) (n : 自然数) (hr : im =O[l] fun z => z.re ^ n)
  证明: of_isBigO_im_re_rpow hre n mod_cast hr

Depends on / 依赖: mod_cast, of_isBigO_im_re_rpow
-/
theorem of_isBigO_im_re_pow (hre : Tendsto re l atTop) (n : Nat) (hr : im =O[l] fun z => z.re ^ n) :
    IsExpCmpFilter l :=
of_isBigO_im_re_rpow hre n mod_cast hr

/--
theorem `of_boundedUnder_abs_im` / 定理 `of_boundedUnder_abs_im`

English:
theorem of_boundedUnder_abs_im
  statement: (hre : Tendsto re l atTop)
  proof: of_isBigO_im_re_pow hre 0 by
    simpa only [pow_zero] using him.isBigO_const (f := im) one_ne_zero

中文:
定理 of_boundedUnder_abs_im
  结论: (hre : 收敛 re l atTop)
  证明: of_isBigO_im_re_pow hre 0 by
    simpa only [pow_zero] using him.isBigO_const (f := im) one_ne_zero

Depends on / 依赖: him.isBigO_const, isBigO_const, of_isBigO_im_re_pow, one_ne_zero, pow_zero
-/
theorem of_boundedUnder_abs_im (hre : Tendsto re l atTop)
    (him : IsBoundedUnder (· <= ·) l fun z => |z.im|) : IsExpCmpFilter l :=
of_isBigO_im_re_pow hre 0 by
    simpa only [pow_zero] using him.isBigO_const (f := im) one_ne_zero

/--
theorem `of_boundedUnder_im` / 定理 `of_boundedUnder_im`

English:
theorem of_boundedUnder_im
  statement: (hre : Tendsto re l atTop) (him_le : IsBoundedUnder (· <= ·) l im)
  proof: of_boundedUnder_abs_im hre isBoundedUnder_le_abs.2 ⟨him_le, him_ge⟩

中文:
定理 of_boundedUnder_im
  结论: (hre : 收敛 re l atTop) (him_le : IsBoundedUnder (· <= ·) l im)
  证明: of_boundedUnder_abs_im hre isBoundedUnder_le_abs.2 ⟨him_le, him_ge⟩

Depends on / 依赖: him_ge, him_le, isBoundedUnder_le_abs, of_boundedUnder_abs_im
-/
theorem of_boundedUnder_im (hre : Tendsto re l atTop) (him_le : IsBoundedUnder (· <= ·) l im)
    (him_ge : IsBoundedUnder (· >= ·) l im) : IsExpCmpFilter l :=
of_boundedUnder_abs_im hre isBoundedUnder_le_abs.2 ⟨him_le, him_ge⟩


/--
theorem `eventually_ne` / 定理 `eventually_ne`

English:
theorem eventually_ne
  given: (hl : IsExpCmpFilter l)
  statement: forallᶠ w : Complex in l, w != 0
  proof: hl.tendsto_re.eventually_ne_atTop' _

中文:
定理 eventually_ne
  条件: (hl : 是ExpCmpFilter l)
  结论: 对任意ᶠ w : 复形 in l, w != 0
  证明: hl.tendsto_re.eventually_ne_atTop' _

Depends on / 依赖: eventually_ne_atTop, hl.tendsto_re.eventually_ne_atTop, tendsto_re
-/
theorem eventually_ne (hl : IsExpCmpFilter l) : forallᶠ w : Complex in l, w != 0 :=
  hl.tendsto_re.eventually_ne_atTop' _

/--
theorem `tendsto_abs_re` / 定理 `tendsto_abs_re`

English:
theorem tendsto_abs_re
  given: (hl : IsExpCmpFilter l)
  statement: Tendsto (fun z : Complex => |z.re|) l atTop
  proof: tendsto_abs_atTop_atTop.comp hl.tendsto_re

中文:
定理 tendsto_abs_re
  条件: (hl : 是ExpCmpFilter l)
  结论: 收敛 (fun z : 复形 => |z.re|) l atTop
  证明: tendsto_abs_atTop_atTop.comp hl.tendsto_re

Depends on / 依赖: hl.tendsto_re, tendsto_abs_atTop_atTop, tendsto_abs_atTop_atTop.comp, tendsto_re
-/
theorem tendsto_abs_re (hl : IsExpCmpFilter l) : Tendsto (fun z : Complex => |z.re|) l atTop :=
  tendsto_abs_atTop_atTop.comp hl.tendsto_re

/--
theorem `tendsto_norm` / 定理 `tendsto_norm`

English:
theorem tendsto_norm
  given: (hl : IsExpCmpFilter l)
  statement: Tendsto norm l atTop
  proof: tendsto_atTop_mono abs_re_le_norm hl.tendsto_abs_re

中文:
定理 tendsto_norm
  条件: (hl : 是ExpCmpFilter l)
  结论: 收敛 norm l atTop
  证明: tendsto_atTop_mono abs_re_le_norm hl.tendsto_abs_re

Depends on / 依赖: abs_re_le_norm, hl.tendsto_abs_re, tendsto_abs_re, tendsto_atTop_mono
-/
theorem tendsto_norm (hl : IsExpCmpFilter l) : Tendsto norm l atTop :=
  tendsto_atTop_mono abs_re_le_norm hl.tendsto_abs_re

/--
theorem `isLittleO_log_re_re` / 定理 `isLittleO_log_re_re`

English:
theorem isLittleO_log_re_re
  given: (hl : IsExpCmpFilter l)
  statement: (fun z => Real.log z.re) =o[l] re
  proof: Real.isLittleO_log_id_atTop.comp_tendsto hl.tendsto_re

中文:
定理 isLittleO_log_re_re
  条件: (hl : 是ExpCmpFilter l)
  结论: (fun z => 实数.log z.re) =o[l] re
  证明: Real.isLittleO_log_id_atTop.comp_tendsto hl.tendsto_re

Depends on / 依赖: Real.isLittleO_log_id_atTop.comp_tendsto, comp_tendsto, hl.tendsto_re, isLittleO_log_id_atTop, tendsto_re
-/
theorem isLittleO_log_re_re (hl : IsExpCmpFilter l) : (fun z => Real.log z.re) =o[l] re :=
  Real.isLittleO_log_id_atTop.comp_tendsto hl.tendsto_re

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
theorem `isLittleO_im_pow_exp_re` / 定理 `isLittleO_im_pow_exp_re`

English:
theorem isLittleO_im_pow_exp_re
  given: (hl : IsExpCmpFilter l) (n : Nat)
  proof: flip IsLittleO.of_pow two_ne_zero
    calc
      (fun z : Complex => (z.im ^ n) ^ 2) = (fun z => z.im ^ (2 * n)) := by simp only [pow_mul']
      _ =O[l] fun z => Real.exp z.re := hl.isBigO_im_pow_re _
      _ = fun z => (Real.exp z.re) ^ 1 := by simp only [pow_one]
      _ =o[l] fun z => (Real.exp 

中文:
定理 isLittleO_im_pow_exp_re
  条件: (hl : 是ExpCmpFilter l) (n : 自然数)
  证明: flip IsLittleO.of_pow two_ne_zero
    calc
      (fun z : Complex => (z.im ^ n) ^ 2) = (fun z => z.im ^ (2 * n)) := by simp only [pow_mul']
      _ =O[l] fun z => Real.exp z.re := hl.isBigO_im_pow_re _
      _ = fun z => (Real.exp z.re) ^ 1 := by simp only [pow_one]
      _ =o[l] fun z => (Real.exp 

Depends on / 依赖: IsLittleO, IsLittleO.of_pow, Real.exp, Real.tendsto_exp_atTop.comp, comp_tendsto, hl.isBigO_im_pow_re, hl.tendsto_re, isBigO_im_pow_re, isLittleO_pow_pow_atTop_of_lt, of_pow, one_lt_two, pow_mul, pow_one, tendsto_exp_atTop, tendsto_re, two_ne_zero, z.im, z.re
-/
theorem isLittleO_im_pow_exp_re (hl : IsExpCmpFilter l) (n : Nat) :
    (fun z : Complex => z.im ^ n) =o[l] fun z => Real.exp z.re :=
flip IsLittleO.of_pow two_ne_zero
    calc
      (fun z : Complex => (z.im ^ n) ^ 2) = (fun z => z.im ^ (2 * n)) := by simp only [pow_mul']
      _ =O[l] fun z => Real.exp z.re := hl.isBigO_im_pow_re _
      _ = fun z => (Real.exp z.re) ^ 1 := by simp only [pow_one]
      _ =o[l] fun z => (Real.exp z.re) ^ 2 :=
(isLittleO_pow_pow_atTop_of_lt one_lt_two).comp_tendsto
          Real.tendsto_exp_atTop.comp hl.tendsto_re

/--
theorem `abs_im_pow_eventuallyLE_exp_re` / 定理 `abs_im_pow_eventuallyLE_exp_re`

English:
theorem abs_im_pow_eventuallyLE_exp_re
  given: (hl : IsExpCmpFilter l) (n : Nat)
  proof: by
  simpa using! (hl.isLittleO_im_pow_exp_re n).bound zero_lt_one

中文:
定理 abs_im_pow_eventuallyLE_exp_re
  条件: (hl : 是ExpCmpFilter l) (n : 自然数)
  证明: by
  simpa using! (hl.isLittleO_im_pow_exp_re n).bound zero_lt_one

Depends on / 依赖: hl.isLittleO_im_pow_exp_re, isLittleO_im_pow_exp_re, zero_lt_one
-/
theorem abs_im_pow_eventuallyLE_exp_re (hl : IsExpCmpFilter l) (n : Nat) :
    (fun z : Complex => |z.im| ^ n) <=ᶠ[l] fun z => Real.exp z.re := by
  simpa using! (hl.isLittleO_im_pow_exp_re n).bound zero_lt_one

/--
theorem `isLittleO_log_norm_re` / 定理 `isLittleO_log_norm_re`

English:
theorem isLittleO_log_norm_re
  given: (hl : IsExpCmpFilter l)
  statement: (fun z => Real.log ‖z‖) =o[l] re
  proof: calc
    (fun z => Real.log ‖z‖) =O[l] fun z => Real.log (√2) + Real.log (max z.re |z.im|) :=
.of_norm_eventuallyLE
        (hl.tendsto_re.eventually_ge_atTop 1).mono fun z hz => by
          have h2 : 0 < √2 := by simp
          have hz' : 1 <= ‖z‖ := hz.trans (re_le_norm z)
          have hm₀ : 0 

中文:
定理 isLittleO_log_norm_re
  条件: (hl : 是ExpCmpFilter l)
  结论: (fun z => 实数.log ‖z‖) =o[l] re
  证明: calc
    (fun z => Real.log ‖z‖) =O[l] fun z => Real.log (√2) + Real.log (max z.re |z.im|) :=
.of_norm_eventuallyLE
        (hl.tendsto_re.eventually_ge_atTop 1).mono fun z hz => by
          have h2 : 0 < √2 := by simp
          have hz' : 1 <= ‖z‖ := hz.trans (re_le_norm z)
          have hm₀ : 0 

Depends on / 依赖: Or.inl, Real.log, Real.log_le_log_iff, Real.log_mul, Real.log_nonneg, Real.norm_of_nonneg, abs_of_nonneg, eventually_ge_atTop, exacts, hl.tendsto_re.eventually_ge_atTop, hz.trans, le_trans, log_le_log_iff, log_mul, log_nonneg, lt_max_iff, norm_le_sqrt_two_mul, norm_of_nonneg, of_norm_eventuallyLE, one_pos
-/
theorem isLittleO_log_norm_re (hl : IsExpCmpFilter l) : (fun z => Real.log ‖z‖) =o[l] re :=
  calc
    (fun z => Real.log ‖z‖) =O[l] fun z => Real.log (√2) + Real.log (max z.re |z.im|) :=
.of_norm_eventuallyLE
        (hl.tendsto_re.eventually_ge_atTop 1).mono fun z hz => by
          have h2 : 0 < √2 := by simp
          have hz' : 1 <= ‖z‖ := hz.trans (re_le_norm z)
          have hm₀ : 0 < max z.re |z.im| := lt_max_iff.2 (Or.inl <| one_pos.trans_le hz)
          simp only [Real.norm_of_nonneg (Real.log_nonneg hz')]
          rw [← Real.log_mul]; rw [Real.log_le_log_iff]; rw [← abs_of_nonneg (le_trans zero_le_one hz)]
          exacts [norm_le_sqrt_two_mul_max z, one_pos.trans_le hz', mul_pos h2 hm₀, h2.ne', hm₀.ne']
    _ =o[l] re :=
IsLittleO.add (isLittleO_const_left.2 <| Or.inr <| hl.tendsto_abs_re)
        isLittleO_iff_nat_mul_le.2 fun n => by
          filter_upwards [isLittleO_iff_nat_mul_le'.1 hl.isLittleO_log_re_re n,
            hl.abs_im_pow_eventuallyLE_exp_re n,
            hl.tendsto_re.eventually_gt_atTop 1] with z hre him h₁
          rcases le_total |z.im| z.re with hle | hle
          · rwa [max_eq_left hle]
          · have H : 1 < |z.im| := h₁.trans_le hle
            norm_cast at *
            rwa [max_eq_right hle, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.log_pos H),
              ← Real.log_pow, Real.log_le_iff_le_exp (pow_pos (one_pos.trans H) _),
              abs_of_pos (one_pos.trans h₁)]


/--
lemma `isTheta_cpow_exp_re_mul_log` / 引理 `isTheta_cpow_exp_re_mul_log`

English:
lemma isTheta_cpow_exp_re_mul_log
  given: (hl : IsExpCmpFilter l) (a : Complex)
  proof: calc
    (fun z => z ^ a) =Θ[l] (fun z : Complex => ‖z‖ ^ re a) :=
      isTheta_cpow_const_rpow fun _ _ => hl.eventually_ne
    _ =ᶠ[l] fun z => Real.exp (re a * Real.log ‖z‖) :=
      (hl.eventually_ne.mono fun z hz => by simp
        [Real.rpow_def_of_pos, norm_pos_iff.mpr hz, mul_comm])

中文:
引理 isTheta_cpow_exp_re_mul_log
  条件: (hl : 是ExpCmpFilter l) (a : 复形)
  证明: calc
    (fun z => z ^ a) =Θ[l] (fun z : Complex => ‖z‖ ^ re a) :=
      isTheta_cpow_const_rpow fun _ _ => hl.eventually_ne
    _ =ᶠ[l] fun z => Real.exp (re a * Real.log ‖z‖) :=
      (hl.eventually_ne.mono fun z hz => by simp
        [Real.rpow_def_of_pos, norm_pos_iff.mpr hz, mul_comm])

Depends on / 依赖: Real.exp, Real.log, Real.rpow_def_of_pos, eventually_ne, hl.eventually_ne, hl.eventually_ne.mono, isTheta_cpow_const_rpow, mul_comm, norm_pos_iff, norm_pos_iff.mpr, rpow_def_of_pos
-/
lemma isTheta_cpow_exp_re_mul_log (hl : IsExpCmpFilter l) (a : Complex) :
    (· ^ a) =Θ[l] fun z => Real.exp (re a * Real.log ‖z‖) :=
  calc
    (fun z => z ^ a) =Θ[l] (fun z : Complex => ‖z‖ ^ re a) :=
      isTheta_cpow_const_rpow fun _ _ => hl.eventually_ne
    _ =ᶠ[l] fun z => Real.exp (re a * Real.log ‖z‖) :=
      (hl.eventually_ne.mono fun z hz => by simp
        [Real.rpow_def_of_pos, norm_pos_iff.mpr hz, mul_comm])

/--
theorem `isLittleO_cpow_exp` / 定理 `isLittleO_cpow_exp`

English:
theorem isLittleO_cpow_exp
  given: (hl : IsExpCmpFilter l) (a : Complex) {b : Real} (hb : 0 < b)
  proof: calc
    (fun z => z ^ a) =Θ[l] fun z => Real.exp (re a * Real.log ‖z‖) :=
      hl.isTheta_cpow_exp_re_mul_log a
    _ =o[l] fun z => exp (b * z) :=
IsLittleO.of_norm_right by
        simp only [norm_exp, re_ofReal_mul, Real.isLittleO_exp_comp_exp_comp]
        refine (IsEquivalent.refl.sub_isLittl

中文:
定理 isLittleO_cpow_exp
  条件: (hl : 是ExpCmpFilter l) (a : 复形) {b : 实数} (hb : 0 < b)
  证明: calc
    (fun z => z ^ a) =Θ[l] fun z => Real.exp (re a * Real.log ‖z‖) :=
      hl.isTheta_cpow_exp_re_mul_log a
    _ =o[l] fun z => exp (b * z) :=
IsLittleO.of_norm_right by
        simp only [norm_exp, re_ofReal_mul, Real.isLittleO_exp_comp_exp_comp]
        refine (IsEquivalent.refl.sub_isLittl

Depends on / 依赖: IsEquivalent, IsEquivalent.refl.sub_isLittleO, IsLittleO, IsLittleO.of_norm_right, Real.exp, Real.isLittleO_exp_comp_exp_comp, Real.log, const_mul_atTop, const_mul_left, const_mul_right, hb.ne, hl.isLittleO_log_norm_re.const_mul_left, hl.isTheta_cpow_exp_re_mul_log, hl.tendsto_re.const_mul_atTop, isLittleO_exp_comp_exp_comp, isLittleO_log_norm_re, isTheta_cpow_exp_re_mul_log, norm_exp, of_norm_right, re_ofReal_mul
-/
theorem isLittleO_cpow_exp (hl : IsExpCmpFilter l) (a : Complex) {b : Real} (hb : 0 < b) :
    (fun z => z ^ a) =o[l] fun z => exp (b * z) :=
  calc
    (fun z => z ^ a) =Θ[l] fun z => Real.exp (re a * Real.log ‖z‖) :=
      hl.isTheta_cpow_exp_re_mul_log a
    _ =o[l] fun z => exp (b * z) :=
IsLittleO.of_norm_right by
        simp only [norm_exp, re_ofReal_mul, Real.isLittleO_exp_comp_exp_comp]
        refine (IsEquivalent.refl.sub_isLittleO ?_).symm.tendsto_atTop
          (hl.tendsto_re.const_mul_atTop hb)
        exact (hl.isLittleO_log_norm_re.const_mul_left _).const_mul_right hb.ne'

/--
theorem `isLittleO_cpow_mul_exp` / 定理 `isLittleO_cpow_mul_exp`

English:
theorem isLittleO_cpow_mul_exp
  given: {b₁ b₂ : Real} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (a₁ a₂ : Complex)
  proof: calc
    (fun z => z ^ a₁ * exp (b₁ * z)) =ᶠ[l] fun z => z ^ a₂ * exp (b₁ * z) * z ^ (a₁ - a₂) :=
      hl.eventually_ne.mono fun z hz => by
        simp only
        rw [mul_right_comm]; rw [← cpow_add _ _ hz]; rw [add_sub_cancel]
    _ =o[l] fun z => z ^ a₂ * exp (b₁ * z) * exp (↑(b₂ - b₁) * z) :=

中文:
定理 isLittleO_cpow_mul_exp
  条件: {b₁ b₂ : 实数} (hl : 是ExpCmpFilter l) (hb : b₁ < b₂) (a₁ a₂ : 复形)
  证明: calc
    (fun z => z ^ a₁ * exp (b₁ * z)) =ᶠ[l] fun z => z ^ a₂ * exp (b₁ * z) * z ^ (a₁ - a₂) :=
      hl.eventually_ne.mono fun z hz => by
        simp only
        rw [mul_right_comm]; rw [← cpow_add _ _ hz]; rw [add_sub_cancel]
    _ =o[l] fun z => z ^ a₂ * exp (b₁ * z) * exp (↑(b₂ - b₁) * z) :=

Depends on / 依赖: add_sub_cancel, cpow_add, eventually_ne, exp_add, hl.eventually_ne.mono, hl.isLittleO_cpow_exp, isBigO_refl, isLittleO_cpow_exp, mul_assoc, mul_isLittleO, mul_right_comm, norm_ca, ofReal_sub, sub_mul, sub_pos
-/
theorem isLittleO_cpow_mul_exp {b₁ b₂ : Real} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (a₁ a₂ : Complex) :
    (fun z => z ^ a₁ * exp (b₁ * z)) =o[l] fun z => z ^ a₂ * exp (b₂ * z) :=
  calc
    (fun z => z ^ a₁ * exp (b₁ * z)) =ᶠ[l] fun z => z ^ a₂ * exp (b₁ * z) * z ^ (a₁ - a₂) :=
      hl.eventually_ne.mono fun z hz => by
        simp only
        rw [mul_right_comm]; rw [← cpow_add _ _ hz]; rw [add_sub_cancel]
    _ =o[l] fun z => z ^ a₂ * exp (b₁ * z) * exp (↑(b₂ - b₁) * z) :=
      ((isBigO_refl (fun z => z ^ a₂ * exp (b₁ * z)) l).mul_isLittleO <|
        hl.isLittleO_cpow_exp _ (sub_pos.2 hb))
    _ =ᶠ[l] fun z => z ^ a₂ * exp (b₂ * z) := by
      simp only [ofReal_sub, sub_mul, mul_assoc, ← exp_add, add_sub_cancel]
      norm_cast

/--
theorem `isLittleO_exp_cpow` / 定理 `isLittleO_exp_cpow`

English:
theorem isLittleO_exp_cpow
  given: (hl : IsExpCmpFilter l) (a : Complex) {b : Real} (hb : b < 0)
  proof: by simpa using hl.isLittleO_cpow_mul_exp hb 0 a

中文:
定理 isLittleO_exp_cpow
  条件: (hl : 是ExpCmpFilter l) (a : 复形) {b : 实数} (hb : b < 0)
  证明: by simpa using hl.isLittleO_cpow_mul_exp hb 0 a

Depends on / 依赖: hl.isLittleO_cpow_mul_exp, isLittleO_cpow_mul_exp
-/
theorem isLittleO_exp_cpow (hl : IsExpCmpFilter l) (a : Complex) {b : Real} (hb : b < 0) :
    (fun z => exp (b * z)) =o[l] fun z => z ^ a := by simpa using hl.isLittleO_cpow_mul_exp hb 0 a

/--
theorem `isLittleO_pow_mul_exp` / 定理 `isLittleO_pow_mul_exp`

English:
theorem isLittleO_pow_mul_exp
  given: {b₁ b₂ : Real} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (m n : Nat)
  proof: by
  simpa only [cpow_natCast] using hl.isLittleO_cpow_mul_exp hb m n

中文:
定理 isLittleO_pow_mul_exp
  条件: {b₁ b₂ : 实数} (hl : 是ExpCmpFilter l) (hb : b₁ < b₂) (m n : 自然数)
  证明: by
  simpa only [cpow_natCast] using hl.isLittleO_cpow_mul_exp hb m n

Depends on / 依赖: cpow_natCast, hl.isLittleO_cpow_mul_exp, isLittleO_cpow_mul_exp
-/
theorem isLittleO_pow_mul_exp {b₁ b₂ : Real} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (m n : Nat) :
    (fun z => z ^ m * exp (b₁ * z)) =o[l] fun z => z ^ n * exp (b₂ * z) := by
  simpa only [cpow_natCast] using hl.isLittleO_cpow_mul_exp hb m n

/--
theorem `isLittleO_zpow_mul_exp` / 定理 `isLittleO_zpow_mul_exp`

English:
theorem isLittleO_zpow_mul_exp
  given: {b₁ b₂ : Real} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (m n : Int)
  proof: by
  simpa only [cpow_intCast] using hl.isLittleO_cpow_mul_exp hb m n

中文:
定理 isLittleO_zpow_mul_exp
  条件: {b₁ b₂ : 实数} (hl : 是ExpCmpFilter l) (hb : b₁ < b₂) (m n : 整数)
  证明: by
  simpa only [cpow_intCast] using hl.isLittleO_cpow_mul_exp hb m n

Depends on / 依赖: cpow_intCast, hl.isLittleO_cpow_mul_exp, isLittleO_cpow_mul_exp
-/
theorem isLittleO_zpow_mul_exp {b₁ b₂ : Real} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (m n : Int) :
    (fun z => z ^ m * exp (b₁ * z)) =o[l] fun z => z ^ n * exp (b₂ * z) := by
  simpa only [cpow_intCast] using hl.isLittleO_cpow_mul_exp hb m n

end IsExpCmpFilter

end Complex
