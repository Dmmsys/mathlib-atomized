/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Analysis.Asymptotics.LinearGrowth
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Exponential growth

This file defines the exponential growth of a sequence `u : ℕ → ℝ≥0∞`. This notion comes in two
versions, using a `liminf` and a `limsup` respectively.

## Main definitions

- `expGrowthInf`, `expGrowthSup`: respectively, `liminf` and `limsup` of `log (u n) / n`.
- `expGrowthInfTopHom`, `expGrowthSupBotHom`: the functions `expGrowthInf`, `expGrowthSup`
  as homomorphisms preserving finitary `Inf`/`Sup` respectively.

## Tags

asymptotics, exponential
-/

@[expose] public section

namespace ExpGrowth

open ENNReal EReal Filter Function LinearGrowth
open scoped Topology

/-! ### Definition -/

/--
Definition of `expGrowthInf` / `expGrowthInf` 的定义

English:
definition expGrowthInf
  signature: (u : Nat -> Real>=0∞)
  body: liminf (fun n => log (u n) / n) atTop

中文:
定义 expGrowthInf
  签名: (u : 自然数 -> 实数>=0∞)
  定义体: liminf (fun n => log (u n) / n) atTop

Depends on / 依赖: liminf
-/
noncomputable def expGrowthInf (u : Nat -> Real>=0∞) : EReal := liminf (fun n => log (u n) / n) atTop

/--
Definition of `expGrowthSup` / `expGrowthSup` 的定义

English:
definition expGrowthSup
  signature: (u : Nat -> Real>=0∞)
  body: limsup (fun n => log (u n) / n) atTop

中文:
定义 expGrowthSup
  签名: (u : 自然数 -> 实数>=0∞)
  定义体: limsup (fun n => log (u n) / n) atTop

Depends on / 依赖: limsup
-/
noncomputable def expGrowthSup (u : Nat -> Real>=0∞) : EReal := limsup (fun n => log (u n) / n) atTop

/--
lemma `expGrowthInf_def` / 引理 `expGrowthInf_def`

English:
lemma expGrowthInf_def
  given: {u : Nat -> Real>=0∞}
  proof: by
  rfl

中文:
引理 expGrowthInf_def
  条件: {u : 自然数 -> 实数>=0∞}
  证明: by
  rfl
-/
lemma expGrowthInf_def {u : Nat -> Real>=0∞} :
    expGrowthInf u = linearGrowthInf (log ∘ u) := by
  rfl

/--
lemma `expGrowthSup_def` / 引理 `expGrowthSup_def`

English:
lemma expGrowthSup_def
  given: {u : Nat -> Real>=0∞}
  proof: by
  rfl

中文:
引理 expGrowthSup_def
  条件: {u : 自然数 -> 实数>=0∞}
  证明: by
  rfl
-/
lemma expGrowthSup_def {u : Nat -> Real>=0∞} :
    expGrowthSup u = linearGrowthSup (log ∘ u) := by
  rfl

/-! ### Basic properties -/

section basic_properties

variable {u v : Nat -> Real>=0∞} {a : EReal} {b : Real>=0∞}

/--
lemma `expGrowthInf_congr` / 引理 `expGrowthInf_congr`

English:
lemma expGrowthInf_congr
  given: (h : u =ᶠ[atTop] v)
  proof: liminf_congr (h.mono fun _ uv => uv ▸ rfl)

中文:
引理 expGrowthInf_congr
  条件: (h : u =ᶠ[atTop] v)
  证明: liminf_congr (h.mono fun _ uv => uv ▸ rfl)

Depends on / 依赖: h.mono, liminf_congr
-/
lemma expGrowthInf_congr (h : u =ᶠ[atTop] v) :
    expGrowthInf u = expGrowthInf v :=
  liminf_congr (h.mono fun _ uv => uv ▸ rfl)

/--
lemma `expGrowthSup_congr` / 引理 `expGrowthSup_congr`

English:
lemma expGrowthSup_congr
  given: (h : u =ᶠ[atTop] v)
  proof: limsup_congr (h.mono fun _ uv => uv ▸ rfl)

中文:
引理 expGrowthSup_congr
  条件: (h : u =ᶠ[atTop] v)
  证明: limsup_congr (h.mono fun _ uv => uv ▸ rfl)

Depends on / 依赖: h.mono, limsup_congr
-/
lemma expGrowthSup_congr (h : u =ᶠ[atTop] v) :
    expGrowthSup u = expGrowthSup v :=
  limsup_congr (h.mono fun _ uv => uv ▸ rfl)

/--
lemma `expGrowthInf_eventually_monotone` / 引理 `expGrowthInf_eventually_monotone`

English:
lemma expGrowthInf_eventually_monotone
  given: (h : u <=ᶠ[atTop] v)
  proof: liminf_le_liminf (h.mono fun n uv => monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone uv))

中文:
引理 expGrowthInf_eventually_monotone
  条件: (h : u <=ᶠ[atTop] v)
  证明: liminf_le_liminf (h.mono fun n uv => monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone uv))

Depends on / 依赖: cast_nonneg, h.mono, liminf_le_liminf, log_monotone, monotone_div_right_of_nonneg, n.cast_nonneg
-/
lemma expGrowthInf_eventually_monotone (h : u <=ᶠ[atTop] v) :
    expGrowthInf u <= expGrowthInf v :=
  liminf_le_liminf (h.mono fun n uv => monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone uv))

/--
lemma `expGrowthInf_monotone` / 引理 `expGrowthInf_monotone`

English:
lemma expGrowthInf_monotone
  statement: Monotone expGrowthInf
  proof: fun _ _ uv => expGrowthInf_eventually_monotone (Eventually.of_forall uv)

中文:
引理 expGrowthInf_monotone
  结论: Monotone expGrowthInf
  证明: fun _ _ uv => expGrowthInf_eventually_monotone (Eventually.of_forall uv)

Depends on / 依赖: Eventually, Eventually.of_forall, expGrowthInf_eventually_monotone, of_forall
-/
lemma expGrowthInf_monotone : Monotone expGrowthInf :=
  fun _ _ uv => expGrowthInf_eventually_monotone (Eventually.of_forall uv)

/--
lemma `expGrowthSup_eventually_monotone` / 引理 `expGrowthSup_eventually_monotone`

English:
lemma expGrowthSup_eventually_monotone
  given: (h : u <=ᶠ[atTop] v)
  proof: limsup_le_limsup (h.mono fun n uv => monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone uv))

中文:
引理 expGrowthSup_eventually_monotone
  条件: (h : u <=ᶠ[atTop] v)
  证明: limsup_le_limsup (h.mono fun n uv => monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone uv))

Depends on / 依赖: cast_nonneg, h.mono, limsup_le_limsup, log_monotone, monotone_div_right_of_nonneg, n.cast_nonneg
-/
lemma expGrowthSup_eventually_monotone (h : u <=ᶠ[atTop] v) :
    expGrowthSup u <= expGrowthSup v :=
  limsup_le_limsup (h.mono fun n uv => monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone uv))

/--
lemma `expGrowthSup_monotone` / 引理 `expGrowthSup_monotone`

English:
lemma expGrowthSup_monotone
  statement: Monotone expGrowthSup
  proof: fun _ _ uv => expGrowthSup_eventually_monotone (Eventually.of_forall uv)

中文:
引理 expGrowthSup_monotone
  结论: Monotone expGrowthSup
  证明: fun _ _ uv => expGrowthSup_eventually_monotone (Eventually.of_forall uv)

Depends on / 依赖: Eventually, Eventually.of_forall, expGrowthSup_eventually_monotone, of_forall
-/
lemma expGrowthSup_monotone : Monotone expGrowthSup :=
  fun _ _ uv => expGrowthSup_eventually_monotone (Eventually.of_forall uv)

/--
lemma `expGrowthInf_le_expGrowthSup` / 引理 `expGrowthInf_le_expGrowthSup`

English:
lemma expGrowthInf_le_expGrowthSup
  statement: expGrowthInf u <= expGrowthSup u
  proof: liminf_le_limsup

中文:
引理 expGrowthInf_le_expGrowthSup
  结论: expGrowthInf u <= expGrowthSup u
  证明: liminf_le_limsup

Depends on / 依赖: liminf_le_limsup
-/
lemma expGrowthInf_le_expGrowthSup : expGrowthInf u <= expGrowthSup u := liminf_le_limsup

/--
lemma `expGrowthInf_le_expGrowthSup_of_frequently_le` / 引理 `expGrowthInf_le_expGrowthSup_of_frequently_le`

English:
lemma expGrowthInf_le_expGrowthSup_of_frequently_le
  given: (h : existsᶠ n in atTop, u n <= v n)
  proof: liminf_le_limsup_of_frequently_le h.mono fun n u_v => by gcongr

中文:
引理 expGrowthInf_le_expGrowthSup_of_frequently_le
  条件: (h : 存在ᶠ n in atTop, u n <= v n)
  证明: liminf_le_limsup_of_frequently_le h.mono fun n u_v => by gcongr

Depends on / 依赖: h.mono, liminf_le_limsup_of_frequently_le
-/
lemma expGrowthInf_le_expGrowthSup_of_frequently_le (h : existsᶠ n in atTop, u n <= v n) :
    expGrowthInf u <= expGrowthSup v :=
liminf_le_limsup_of_frequently_le h.mono fun n u_v => by gcongr

/--
lemma `expGrowthInf_le_iff` / 引理 `expGrowthInf_le_iff`

English:
lemma expGrowthInf_le_iff
  proof: by
  rw [expGrowthInf]; rw [liminf_le_iff']
  refine forall₂_congr fun b _ => frequently_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n)]; rw [← log_exp (n * b)]; rw [mul_comm _ b]
  exact logOrderIso.le_iff_le

中文:
引理 expGrowthInf_le_iff
  证明: by
  rw [expGrowthInf]; rw [liminf_le_iff']
  refine forall₂_congr fun b _ => frequently_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n)]; rw [← log_exp (n * b)]; rw [mul_comm _ b]
  exact logOrderIso.le_iff_le

Depends on / 依赖: div_le_iff_le_mul, eventually_atTop, expGrowthInf, frequently_congr, le_iff_le, liminf_le_iff, logOrderIso, logOrderIso.le_iff_le, log_exp, mul_comm, natCast_ne_top
-/
lemma expGrowthInf_le_iff :
    expGrowthInf u <= a ↔ forall b > a, existsᶠ n : Nat in atTop, u n <= exp (b * n) := by
  rw [expGrowthInf]; rw [liminf_le_iff']
  refine forall₂_congr fun b _ => frequently_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n)]; rw [← log_exp (n * b)]; rw [mul_comm _ b]
  exact logOrderIso.le_iff_le

/--
lemma `le_expGrowthInf_iff` / 引理 `le_expGrowthInf_iff`

English:
lemma le_expGrowthInf_iff
  proof: by
  rw [expGrowthInf]; rw [le_liminf_iff']
  refine forall₂_congr fun b _ => eventually_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n), ← log_exp (b * n)]
  exact logOrderIso.le_iff_le

中文:
引理 le_expGrowthInf_iff
  证明: by
  rw [expGrowthInf]; rw [le_liminf_iff']
  refine forall₂_congr fun b _ => eventually_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n), ← log_exp (b * n)]
  exact logOrderIso.le_iff_le

Depends on / 依赖: eventually_atTop, eventually_congr, expGrowthInf, le_div_iff_mul_le, le_iff_le, le_liminf_iff, logOrderIso, logOrderIso.le_iff_le, log_exp, natCast_ne_top, nth_rw
-/
lemma le_expGrowthInf_iff :
    a <= expGrowthInf u ↔ forall b < a, forallᶠ n : Nat in atTop, exp (b * n) <= u n := by
  rw [expGrowthInf]; rw [le_liminf_iff']
  refine forall₂_congr fun b _ => eventually_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n), ← log_exp (b * n)]
  exact logOrderIso.le_iff_le

/--
lemma `expGrowthSup_le_iff` / 引理 `expGrowthSup_le_iff`

English:
lemma expGrowthSup_le_iff
  proof: by
  rw [expGrowthSup]; rw [limsup_le_iff']
  refine forall₂_congr fun b _ => eventually_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n)]; rw [← log_exp (n * b)]; rw [mul_comm _ b]
  exact logOrderIso.le_iff_le

中文:
引理 expGrowthSup_le_iff
  证明: by
  rw [expGrowthSup]; rw [limsup_le_iff']
  refine forall₂_congr fun b _ => eventually_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n)]; rw [← log_exp (n * b)]; rw [mul_comm _ b]
  exact logOrderIso.le_iff_le

Depends on / 依赖: div_le_iff_le_mul, eventually_atTop, eventually_congr, expGrowthSup, le_iff_le, limsup_le_iff, logOrderIso, logOrderIso.le_iff_le, log_exp, mul_comm, natCast_ne_top
-/
lemma expGrowthSup_le_iff :
    expGrowthSup u <= a ↔ forall b > a, forallᶠ n : Nat in atTop, u n <= exp (b * n) := by
  rw [expGrowthSup]; rw [limsup_le_iff']
  refine forall₂_congr fun b _ => eventually_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n)]; rw [← log_exp (n * b)]; rw [mul_comm _ b]
  exact logOrderIso.le_iff_le

/--
lemma `le_expGrowthSup_iff` / 引理 `le_expGrowthSup_iff`

English:
lemma le_expGrowthSup_iff
  proof: by
  rw [expGrowthSup]; rw [le_limsup_iff']
  refine forall₂_congr fun b _ => frequently_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n), ← log_exp (b * n)]
  exact logOrderIso.le_iff_le

中文:
引理 le_expGrowthSup_iff
  证明: by
  rw [expGrowthSup]; rw [le_limsup_iff']
  refine forall₂_congr fun b _ => frequently_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n), ← log_exp (b * n)]
  exact logOrderIso.le_iff_le

Depends on / 依赖: eventually_atTop, expGrowthSup, frequently_congr, le_div_iff_mul_le, le_iff_le, le_limsup_iff, logOrderIso, logOrderIso.le_iff_le, log_exp, natCast_ne_top, nth_rw
-/
lemma le_expGrowthSup_iff :
    a <= expGrowthSup u ↔ forall b < a, existsᶠ n : Nat in atTop, exp (b * n) <= u n := by
  rw [expGrowthSup]; rw [le_limsup_iff']
  refine forall₂_congr fun b _ => frequently_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n), ← log_exp (b * n)]
  exact logOrderIso.le_iff_le

/--
lemma `frequently_le_exp` / 引理 `frequently_le_exp`

English:
lemma frequently_le_exp
  given: (h : expGrowthInf u < a)
  proof: expGrowthInf_le_iff.1 (le_refl (expGrowthInf u)) a h

中文:
引理 frequently_le_exp
  条件: (h : expGrowthInf u < a)
  证明: expGrowthInf_le_iff.1 (le_refl (expGrowthInf u)) a h

Depends on / 依赖: expGrowthInf, expGrowthInf_le_iff, le_refl
-/
lemma frequently_le_exp (h : expGrowthInf u < a) :
    existsᶠ n : Nat in atTop, u n <= exp (a * n) :=
  expGrowthInf_le_iff.1 (le_refl (expGrowthInf u)) a h

/--
lemma `eventually_exp_le` / 引理 `eventually_exp_le`

English:
lemma eventually_exp_le
  given: (h : a < expGrowthInf u)
  proof: le_expGrowthInf_iff.1 (le_refl (expGrowthInf u)) a h

中文:
引理 eventually_exp_le
  条件: (h : a < expGrowthInf u)
  证明: le_expGrowthInf_iff.1 (le_refl (expGrowthInf u)) a h

Depends on / 依赖: expGrowthInf, le_expGrowthInf_iff, le_refl
-/
lemma eventually_exp_le (h : a < expGrowthInf u) :
    forallᶠ n : Nat in atTop, exp (a * n) <= u n :=
  le_expGrowthInf_iff.1 (le_refl (expGrowthInf u)) a h

/--
lemma `eventually_le_exp` / 引理 `eventually_le_exp`

English:
lemma eventually_le_exp
  given: (h : expGrowthSup u < a)
  proof: expGrowthSup_le_iff.1 (le_refl (expGrowthSup u)) a h

中文:
引理 eventually_le_exp
  条件: (h : expGrowthSup u < a)
  证明: expGrowthSup_le_iff.1 (le_refl (expGrowthSup u)) a h

Depends on / 依赖: expGrowthSup, expGrowthSup_le_iff, le_refl
-/
lemma eventually_le_exp (h : expGrowthSup u < a) :
    forallᶠ n : Nat in atTop, u n <= exp (a * n) :=
  expGrowthSup_le_iff.1 (le_refl (expGrowthSup u)) a h

/--
lemma `frequently_exp_le` / 引理 `frequently_exp_le`

English:
lemma frequently_exp_le
  given: (h : a < expGrowthSup u)
  proof: le_expGrowthSup_iff.1 (le_refl (expGrowthSup u)) a h

中文:
引理 frequently_exp_le
  条件: (h : a < expGrowthSup u)
  证明: le_expGrowthSup_iff.1 (le_refl (expGrowthSup u)) a h

Depends on / 依赖: expGrowthSup, le_expGrowthSup_iff, le_refl
-/
lemma frequently_exp_le (h : a < expGrowthSup u) :
    existsᶠ n : Nat in atTop, exp (a * n) <= u n :=
  le_expGrowthSup_iff.1 (le_refl (expGrowthSup u)) a h

/--
lemma `_root_.Frequently.expGrowthInf_le` / 引理 `_root_.Frequently.expGrowthInf_le`

English:
lemma _root_.Frequently.expGrowthInf_le
  given: (h : existsᶠ n : Nat in atTop, u n <= exp (a * n))
  proof: by
  apply expGrowthInf_le_iff.2 fun c c_u => h.mono fun n hn => hn.trans ?_
  gcongr

中文:
引理 _root_.Frequently.expGrowthInf_le
  条件: (h : 存在ᶠ n : 自然数 in atTop, u n <= exp (a * n))
  证明: by
  apply expGrowthInf_le_iff.2 fun c c_u => h.mono fun n hn => hn.trans ?_
  gcongr

Depends on / 依赖: expGrowthInf_le_iff, h.mono, hn.trans
-/
lemma _root_.Frequently.expGrowthInf_le (h : existsᶠ n : Nat in atTop, u n <= exp (a * n)) :
    expGrowthInf u <= a := by
  apply expGrowthInf_le_iff.2 fun c c_u => h.mono fun n hn => hn.trans ?_
  gcongr

/--
lemma `_root_.Eventually.le_expGrowthInf` / 引理 `_root_.Eventually.le_expGrowthInf`

English:
lemma _root_.Eventually.le_expGrowthInf
  given: (h : forallᶠ n : Nat in atTop, exp (a * n) <= u n)
  proof: le_expGrowthInf_iff.2 fun c c_u => h.mono fun n hn => hn.trans' by gcongr

中文:
引理 _root_.Eventually.le_expGrowthInf
  条件: (h : 对任意ᶠ n : 自然数 in atTop, exp (a * n) <= u n)
  证明: le_expGrowthInf_iff.2 fun c c_u => h.mono fun n hn => hn.trans' by gcongr

Depends on / 依赖: h.mono, hn.trans, le_expGrowthInf_iff
-/
lemma _root_.Eventually.le_expGrowthInf (h : forallᶠ n : Nat in atTop, exp (a * n) <= u n) :
    a <= expGrowthInf u :=
le_expGrowthInf_iff.2 fun c c_u => h.mono fun n hn => hn.trans' by gcongr

/--
lemma `_root_.Eventually.expGrowthSup_le` / 引理 `_root_.Eventually.expGrowthSup_le`

English:
lemma _root_.Eventually.expGrowthSup_le
  given: (h : forallᶠ n : Nat in atTop, u n <= exp (a * n))
  proof: expGrowthSup_le_iff.2 fun c c_u => h.mono fun n hn => hn.trans by gcongr

中文:
引理 _root_.Eventually.expGrowthSup_le
  条件: (h : 对任意ᶠ n : 自然数 in atTop, u n <= exp (a * n))
  证明: expGrowthSup_le_iff.2 fun c c_u => h.mono fun n hn => hn.trans by gcongr

Depends on / 依赖: expGrowthSup_le_iff, h.mono, hn.trans
-/
lemma _root_.Eventually.expGrowthSup_le (h : forallᶠ n : Nat in atTop, u n <= exp (a * n)) :
    expGrowthSup u <= a :=
expGrowthSup_le_iff.2 fun c c_u => h.mono fun n hn => hn.trans by gcongr

/--
lemma `_root_.Frequently.le_expGrowthSup` / 引理 `_root_.Frequently.le_expGrowthSup`

English:
lemma _root_.Frequently.le_expGrowthSup
  given: (h : existsᶠ n : Nat in atTop, exp (a * n) <= u n)
  proof: le_expGrowthSup_iff.2 fun c c_u => h.mono fun n hn => hn.trans' by gcongr

中文:
引理 _root_.Frequently.le_expGrowthSup
  条件: (h : 存在ᶠ n : 自然数 in atTop, exp (a * n) <= u n)
  证明: le_expGrowthSup_iff.2 fun c c_u => h.mono fun n hn => hn.trans' by gcongr

Depends on / 依赖: h.mono, hn.trans, le_expGrowthSup_iff
-/
lemma _root_.Frequently.le_expGrowthSup (h : existsᶠ n : Nat in atTop, exp (a * n) <= u n) :
    a <= expGrowthSup u :=
le_expGrowthSup_iff.2 fun c c_u => h.mono fun n hn => hn.trans' by gcongr


/--
lemma `expGrowthSup_zero` / 引理 `expGrowthSup_zero`

English:
lemma expGrowthSup_zero
  statement: expGrowthSup 0 = ⊥
  proof: by
  rw [← linearGrowthSup_bot]; rw [expGrowthSup_def]
  congr 1
  ext _
  rw [comp_apply]; rw [Pi.zero_apply]; rw [Pi.bot_apply]; rw [log_zero]

中文:
引理 expGrowthSup_zero
  结论: expGrowthSup 0 = ⊥
  证明: by
  rw [← linearGrowthSup_bot]; rw [expGrowthSup_def]
  congr 1
  ext _
  rw [comp_apply]; rw [Pi.zero_apply]; rw [Pi.bot_apply]; rw [log_zero]

Depends on / 依赖: Pi.bot_apply, Pi.zero_apply, bot_apply, comp_apply, expGrowthSup_def, linearGrowthSup_bot, log_zero, zero_apply
-/
lemma expGrowthSup_zero : expGrowthSup 0 = ⊥ := by
  rw [← linearGrowthSup_bot]; rw [expGrowthSup_def]
  congr 1
  ext _
  rw [comp_apply]; rw [Pi.zero_apply]; rw [Pi.bot_apply]; rw [log_zero]

/--
lemma `expGrowthInf_zero` / 引理 `expGrowthInf_zero`

English:
lemma expGrowthInf_zero
  statement: expGrowthInf 0 = ⊥
  proof: by
  apply le_bot_iff.1
  rw [← expGrowthSup_zero]
  exact expGrowthInf_le_expGrowthSup

中文:
引理 expGrowthInf_zero
  结论: expGrowthInf 0 = ⊥
  证明: by
  apply le_bot_iff.1
  rw [← expGrowthSup_zero]
  exact expGrowthInf_le_expGrowthSup

Depends on / 依赖: expGrowthInf_le_expGrowthSup, expGrowthSup_zero, le_bot_iff
-/
lemma expGrowthInf_zero : expGrowthInf 0 = ⊥ := by
  apply le_bot_iff.1
  rw [← expGrowthSup_zero]
  exact expGrowthInf_le_expGrowthSup

/--
lemma `expGrowthInf_top` / 引理 `expGrowthInf_top`

English:
lemma expGrowthInf_top
  statement: expGrowthInf ⊤ = ⊤
  proof: by
  rw [← linearGrowthInf_top]; rw [expGrowthInf_def]
  rfl

中文:
引理 expGrowthInf_top
  结论: expGrowthInf ⊤ = ⊤
  证明: by
  rw [← linearGrowthInf_top]; rw [expGrowthInf_def]
  rfl

Depends on / 依赖: expGrowthInf_def, linearGrowthInf_top
-/
lemma expGrowthInf_top : expGrowthInf ⊤ = ⊤ := by
  rw [← linearGrowthInf_top]; rw [expGrowthInf_def]
  rfl

/--
lemma `expGrowthSup_top` / 引理 `expGrowthSup_top`

English:
lemma expGrowthSup_top
  statement: expGrowthSup ⊤ = ⊤
  proof: by
  apply top_le_iff.1
  rw [← expGrowthInf_top]
  exact expGrowthInf_le_expGrowthSup

中文:
引理 expGrowthSup_top
  结论: expGrowthSup ⊤ = ⊤
  证明: by
  apply top_le_iff.1
  rw [← expGrowthInf_top]
  exact expGrowthInf_le_expGrowthSup

Depends on / 依赖: expGrowthInf_le_expGrowthSup, expGrowthInf_top, top_le_iff
-/
lemma expGrowthSup_top : expGrowthSup ⊤ = ⊤ := by
  apply top_le_iff.1
  rw [← expGrowthInf_top]
  exact expGrowthInf_le_expGrowthSup

/--
lemma `expGrowthInf_const` / 引理 `expGrowthInf_const`

English:
lemma expGrowthInf_const
  given: (h : b != 0) (h' : b != ∞)
  statement: expGrowthInf (fun _ => b) = 0
  proof: (tendsto_const_div_atTop_nhds_zero_nat (fun k => h (log_eq_bot_iff.1 k))
    (fun k => h' (log_eq_top_iff.1 k))).liminf_eq

中文:
引理 expGrowthInf_const
  条件: (h : b != 0) (h' : b != ∞)
  结论: expGrowthInf (fun _ => b) = 0
  证明: (tendsto_const_div_atTop_nhds_zero_nat (fun k => h (log_eq_bot_iff.1 k))
    (fun k => h' (log_eq_top_iff.1 k))).liminf_eq

Depends on / 依赖: liminf_eq, log_eq_bot_iff, log_eq_top_iff, tendsto_const_div_atTop_nhds_zero_nat
-/
lemma expGrowthInf_const (h : b != 0) (h' : b != ∞) : expGrowthInf (fun _ => b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat (fun k => h (log_eq_bot_iff.1 k))
    (fun k => h' (log_eq_top_iff.1 k))).liminf_eq

/--
lemma `expGrowthSup_const` / 引理 `expGrowthSup_const`

English:
lemma expGrowthSup_const
  given: (h : b != 0) (h' : b != ∞)
  statement: expGrowthSup (fun _ => b) = 0
  proof: (tendsto_const_div_atTop_nhds_zero_nat (fun k => h (log_eq_bot_iff.1 k))
    (fun k => h' (log_eq_top_iff.1 k))).limsup_eq

中文:
引理 expGrowthSup_const
  条件: (h : b != 0) (h' : b != ∞)
  结论: expGrowthSup (fun _ => b) = 0
  证明: (tendsto_const_div_atTop_nhds_zero_nat (fun k => h (log_eq_bot_iff.1 k))
    (fun k => h' (log_eq_top_iff.1 k))).limsup_eq

Depends on / 依赖: limsup_eq, log_eq_bot_iff, log_eq_top_iff, tendsto_const_div_atTop_nhds_zero_nat
-/
lemma expGrowthSup_const (h : b != 0) (h' : b != ∞) : expGrowthSup (fun _ => b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat (fun k => h (log_eq_bot_iff.1 k))
    (fun k => h' (log_eq_top_iff.1 k))).limsup_eq

/--
lemma `expGrowthInf_pow` / 引理 `expGrowthInf_pow`

English:
lemma expGrowthInf_pow
  statement: expGrowthInf (fun n => b ^ n) = log b
  proof: by
  rw [expGrowthInf]; rw [← liminf_const (f := atTop (α := Nat)) (log b)]
  refine liminf_congr (eventually_atTop.2 ⟨1, fun n n_1 => ?_⟩)
  rw [EReal.div_eq_iff (natCast_ne_bot n) (natCast_ne_top n)
    (zero_lt_one.trans_le (Nat.one_le_cast.2 n_1)).ne.symm]; rw [log_pow]; rw [mul_comm]

中文:
引理 expGrowthInf_pow
  结论: expGrowthInf (fun n => b ^ n) = log b
  证明: by
  rw [expGrowthInf]; rw [← liminf_const (f := atTop (α := Nat)) (log b)]
  refine liminf_congr (eventually_atTop.2 ⟨1, fun n n_1 => ?_⟩)
  rw [EReal.div_eq_iff (natCast_ne_bot n) (natCast_ne_top n)
    (zero_lt_one.trans_le (Nat.one_le_cast.2 n_1)).ne.symm]; rw [log_pow]; rw [mul_comm]

Depends on / 依赖: EReal.div_eq_iff, Nat.one_le_cast, div_eq_iff, eventually_atTop, expGrowthInf, liminf_congr, liminf_const, log_pow, mul_comm, natCast_ne_bot, natCast_ne_top, ne.symm, one_le_cast, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
lemma expGrowthInf_pow : expGrowthInf (fun n => b ^ n) = log b := by
  rw [expGrowthInf]; rw [← liminf_const (f := atTop (α := Nat)) (log b)]
  refine liminf_congr (eventually_atTop.2 ⟨1, fun n n_1 => ?_⟩)
  rw [EReal.div_eq_iff (natCast_ne_bot n) (natCast_ne_top n)
    (zero_lt_one.trans_le (Nat.one_le_cast.2 n_1)).ne.symm]; rw [log_pow]; rw [mul_comm]

/--
lemma `expGrowthSup_pow` / 引理 `expGrowthSup_pow`

English:
lemma expGrowthSup_pow
  statement: expGrowthSup (fun n => b ^ n) = log b
  proof: by
  rw [expGrowthSup]; rw [← limsup_const (f := atTop (α := Nat)) (log b)]
  refine limsup_congr (eventually_atTop.2 ⟨1, fun n n_1 => ?_⟩)
  rw [EReal.div_eq_iff (natCast_ne_bot n) (natCast_ne_top n)
    (zero_lt_one.trans_le (Nat.one_le_cast.2 n_1)).ne.symm]; rw [log_pow]; rw [mul_comm]

中文:
引理 expGrowthSup_pow
  结论: expGrowthSup (fun n => b ^ n) = log b
  证明: by
  rw [expGrowthSup]; rw [← limsup_const (f := atTop (α := Nat)) (log b)]
  refine limsup_congr (eventually_atTop.2 ⟨1, fun n n_1 => ?_⟩)
  rw [EReal.div_eq_iff (natCast_ne_bot n) (natCast_ne_top n)
    (zero_lt_one.trans_le (Nat.one_le_cast.2 n_1)).ne.symm]; rw [log_pow]; rw [mul_comm]

Depends on / 依赖: EReal.div_eq_iff, Nat.one_le_cast, div_eq_iff, eventually_atTop, expGrowthSup, limsup_congr, limsup_const, log_pow, mul_comm, natCast_ne_bot, natCast_ne_top, ne.symm, one_le_cast, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
lemma expGrowthSup_pow : expGrowthSup (fun n => b ^ n) = log b := by
  rw [expGrowthSup]; rw [← limsup_const (f := atTop (α := Nat)) (log b)]
  refine limsup_congr (eventually_atTop.2 ⟨1, fun n n_1 => ?_⟩)
  rw [EReal.div_eq_iff (natCast_ne_bot n) (natCast_ne_top n)
    (zero_lt_one.trans_le (Nat.one_le_cast.2 n_1)).ne.symm]; rw [log_pow]; rw [mul_comm]

/--
lemma `expGrowthInf_exp` / 引理 `expGrowthInf_exp`

English:
lemma expGrowthInf_exp
  statement: expGrowthInf (fun n => exp (a * n)) = a
  proof: le_antisymm (Frequently.expGrowthInf_le (Frequently.of_forall fun _ => le_refl _))
    (Eventually.le_expGrowthInf (Eventually.of_forall fun _ => le_refl _))

中文:
引理 expGrowthInf_exp
  结论: expGrowthInf (fun n => exp (a * n)) = a
  证明: le_antisymm (Frequently.expGrowthInf_le (Frequently.of_forall fun _ => le_refl _))
    (Eventually.le_expGrowthInf (Eventually.of_forall fun _ => le_refl _))

Depends on / 依赖: Eventually, Eventually.le_expGrowthInf, Eventually.of_forall, Frequently, Frequently.expGrowthInf_le, Frequently.of_forall, expGrowthInf_le, le_antisymm, le_expGrowthInf, le_refl, of_forall
-/
lemma expGrowthInf_exp : expGrowthInf (fun n => exp (a * n)) = a :=
  le_antisymm (Frequently.expGrowthInf_le (Frequently.of_forall fun _ => le_refl _))
    (Eventually.le_expGrowthInf (Eventually.of_forall fun _ => le_refl _))

/--
lemma `expGrowthSup_exp` / 引理 `expGrowthSup_exp`

English:
lemma expGrowthSup_exp
  statement: expGrowthSup (fun n => exp (a * n)) = a
  proof: le_antisymm (Eventually.expGrowthSup_le (Eventually.of_forall fun _ => le_refl _))
    (Frequently.le_expGrowthSup (Frequently.of_forall fun _ => le_refl _))

中文:
引理 expGrowthSup_exp
  结论: expGrowthSup (fun n => exp (a * n)) = a
  证明: le_antisymm (Eventually.expGrowthSup_le (Eventually.of_forall fun _ => le_refl _))
    (Frequently.le_expGrowthSup (Frequently.of_forall fun _ => le_refl _))

Depends on / 依赖: Eventually, Eventually.expGrowthSup_le, Eventually.of_forall, Frequently, Frequently.le_expGrowthSup, Frequently.of_forall, expGrowthSup_le, le_antisymm, le_expGrowthSup, le_refl, of_forall
-/
lemma expGrowthSup_exp : expGrowthSup (fun n => exp (a * n)) = a :=
  le_antisymm (Eventually.expGrowthSup_le (Eventually.of_forall fun _ => le_refl _))
    (Frequently.le_expGrowthSup (Frequently.of_forall fun _ => le_refl _))


/--
lemma `le_expGrowthInf_mul` / 引理 `le_expGrowthInf_mul`

English:
lemma le_expGrowthInf_mul
  proof: by
  refine le_liminf_add.trans_eq (liminf_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [← add_div_of_nonneg_right n.cast_nonneg']; rw [log_mul_add]

中文:
引理 le_expGrowthInf_mul
  证明: by
  refine le_liminf_add.trans_eq (liminf_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [← add_div_of_nonneg_right n.cast_nonneg']; rw [log_mul_add]

Depends on / 依赖: Eventually, Eventually.of_forall, Pi.add_apply, Pi.mul_apply, add_apply, add_div_of_nonneg_right, cast_nonneg, le_liminf_add, le_liminf_add.trans_eq, liminf_congr, log_mul_add, mul_apply, n.cast_nonneg, of_forall, trans_eq
-/
lemma le_expGrowthInf_mul :
    expGrowthInf u + expGrowthInf v <= expGrowthInf (u * v) := by
  refine le_liminf_add.trans_eq (liminf_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [← add_div_of_nonneg_right n.cast_nonneg']; rw [log_mul_add]

/--
lemma `expGrowthInf_mul_le` / 引理 `expGrowthInf_mul_le`

English:
lemma expGrowthInf_mul_le
  statement: (h : expGrowthSup u != ⊥ ∨ expGrowthInf v != ⊤)
  proof: by
  refine (liminf_add_le h h').trans_eq' (liminf_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [← add_div_of_nonneg_right n.cast_nonneg']; rw [log_mul_add]

中文:
引理 expGrowthInf_mul_le
  结论: (h : expGrowthSup u != ⊥ ∨ expGrowthInf v != ⊤)
  证明: by
  refine (liminf_add_le h h').trans_eq' (liminf_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [← add_div_of_nonneg_right n.cast_nonneg']; rw [log_mul_add]

Depends on / 依赖: Eventually, Eventually.of_forall, Pi.add_apply, Pi.mul_apply, add_apply, add_div_of_nonneg_right, cast_nonneg, liminf_add_le, liminf_congr, log_mul_add, mul_apply, n.cast_nonneg, of_forall, trans_eq
-/
lemma expGrowthInf_mul_le (h : expGrowthSup u != ⊥ ∨ expGrowthInf v != ⊤)
    (h' : expGrowthSup u != ⊤ ∨ expGrowthInf v != ⊥) :
    expGrowthInf (u * v) <= expGrowthSup u + expGrowthInf v := by
  refine (liminf_add_le h h').trans_eq' (liminf_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [← add_div_of_nonneg_right n.cast_nonneg']; rw [log_mul_add]

/--
lemma `expGrowthInf_mul_le'` / 引理 `expGrowthInf_mul_le'`

English:
lemma expGrowthInf_mul_le'
  statement: (h : expGrowthInf u != ⊥ ∨ expGrowthSup v != ⊤)
  proof: by
  rw [mul_comm]; rw [add_comm]
  exact expGrowthInf_mul_le h'.symm h.symm

中文:
引理 expGrowthInf_mul_le'
  结论: (h : expGrowthInf u != ⊥ ∨ expGrowthSup v != ⊤)
  证明: by
  rw [mul_comm]; rw [add_comm]
  exact expGrowthInf_mul_le h'.symm h.symm

Depends on / 依赖: add_comm, expGrowthInf_mul_le, h.symm, mul_comm
-/
lemma expGrowthInf_mul_le' (h : expGrowthInf u != ⊥ ∨ expGrowthSup v != ⊤)
    (h' : expGrowthInf u != ⊤ ∨ expGrowthSup v != ⊥) :
    expGrowthInf (u * v) <= expGrowthInf u + expGrowthSup v := by
  rw [mul_comm]; rw [add_comm]
  exact expGrowthInf_mul_le h'.symm h.symm

/--
lemma `le_expGrowthSup_mul` / 引理 `le_expGrowthSup_mul`

English:
lemma le_expGrowthSup_mul
  statement: expGrowthSup u + expGrowthInf v <= expGrowthSup (u * v)
  proof: by
  refine le_limsup_add.trans_eq (limsup_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [log_mul_add]; rw [add_div_of_nonneg_right n.cast_nonneg']

中文:
引理 le_expGrowthSup_mul
  结论: expGrowthSup u + expGrowthInf v <= expGrowthSup (u * v)
  证明: by
  refine le_limsup_add.trans_eq (limsup_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [log_mul_add]; rw [add_div_of_nonneg_right n.cast_nonneg']

Depends on / 依赖: Eventually, Eventually.of_forall, Pi.add_apply, Pi.mul_apply, add_apply, add_div_of_nonneg_right, cast_nonneg, le_limsup_add, le_limsup_add.trans_eq, limsup_congr, log_mul_add, mul_apply, n.cast_nonneg, of_forall, trans_eq
-/
lemma le_expGrowthSup_mul : expGrowthSup u + expGrowthInf v <= expGrowthSup (u * v) := by
  refine le_limsup_add.trans_eq (limsup_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [log_mul_add]; rw [add_div_of_nonneg_right n.cast_nonneg']

/--
lemma `le_expGrowthSup_mul'` / 引理 `le_expGrowthSup_mul'`

English:
lemma le_expGrowthSup_mul'
  statement: expGrowthInf u + expGrowthSup v <= expGrowthSup (u * v)
  proof: by
  rw [mul_comm]; rw [add_comm]
  exact le_expGrowthSup_mul

中文:
引理 le_expGrowthSup_mul'
  结论: expGrowthInf u + expGrowthSup v <= expGrowthSup (u * v)
  证明: by
  rw [mul_comm]; rw [add_comm]
  exact le_expGrowthSup_mul

Depends on / 依赖: add_comm, le_expGrowthSup_mul, mul_comm
-/
lemma le_expGrowthSup_mul' : expGrowthInf u + expGrowthSup v <= expGrowthSup (u * v) := by
  rw [mul_comm]; rw [add_comm]
  exact le_expGrowthSup_mul

/--
lemma `expGrowthSup_mul_le` / 引理 `expGrowthSup_mul_le`

English:
lemma expGrowthSup_mul_le
  statement: (h : expGrowthSup u != ⊥ ∨ expGrowthSup v != ⊤)
  proof: by
  refine (limsup_add_le h h').trans_eq' (limsup_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [log_mul_add]; rw [add_div_of_nonneg_right n.cast_nonneg']

中文:
引理 expGrowthSup_mul_le
  结论: (h : expGrowthSup u != ⊥ ∨ expGrowthSup v != ⊤)
  证明: by
  refine (limsup_add_le h h').trans_eq' (limsup_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [log_mul_add]; rw [add_div_of_nonneg_right n.cast_nonneg']

Depends on / 依赖: Eventually, Eventually.of_forall, Pi.add_apply, Pi.mul_apply, add_apply, add_div_of_nonneg_right, cast_nonneg, limsup_add_le, limsup_congr, log_mul_add, mul_apply, n.cast_nonneg, of_forall, trans_eq
-/
lemma expGrowthSup_mul_le (h : expGrowthSup u != ⊥ ∨ expGrowthSup v != ⊤)
    (h' : expGrowthSup u != ⊤ ∨ expGrowthSup v != ⊥) :
    expGrowthSup (u * v) <= expGrowthSup u + expGrowthSup v := by
  refine (limsup_add_le h h').trans_eq' (limsup_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [log_mul_add]; rw [add_div_of_nonneg_right n.cast_nonneg']

/--
lemma `expGrowthInf_inv` / 引理 `expGrowthInf_inv`

English:
lemma expGrowthInf_inv
  statement: expGrowthInf u⁻¹ = - expGrowthSup u
  proof: by
  rw [expGrowthSup]; rw [← liminf_neg]
  refine liminf_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.neg_apply]; rw [Pi.inv_apply]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← EReal.neg_mul]; rw [log_inv]

中文:
引理 expGrowthInf_inv
  结论: expGrowthInf u⁻¹ = - expGrowthSup u
  证明: by
  rw [expGrowthSup]; rw [← liminf_neg]
  refine liminf_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.neg_apply]; rw [Pi.inv_apply]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← EReal.neg_mul]; rw [log_inv]

Depends on / 依赖: EReal.neg_mul, Eventually, Eventually.of_forall, Pi.inv_apply, Pi.neg_apply, div_eq_mul_inv, expGrowthSup, inv_apply, liminf_congr, liminf_neg, log_inv, neg_apply, neg_mul, of_forall
-/
lemma expGrowthInf_inv : expGrowthInf u⁻¹ = - expGrowthSup u := by
  rw [expGrowthSup]; rw [← liminf_neg]
  refine liminf_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.neg_apply]; rw [Pi.inv_apply]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← EReal.neg_mul]; rw [log_inv]

/--
lemma `expGrowthSup_inv` / 引理 `expGrowthSup_inv`

English:
lemma expGrowthSup_inv
  statement: expGrowthSup u⁻¹ = - expGrowthInf u
  proof: by
  rw [expGrowthInf]; rw [← limsup_neg]
  refine limsup_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.neg_apply]; rw [Pi.inv_apply]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← EReal.neg_mul]; rw [log_inv]

中文:
引理 expGrowthSup_inv
  结论: expGrowthSup u⁻¹ = - expGrowthInf u
  证明: by
  rw [expGrowthInf]; rw [← limsup_neg]
  refine limsup_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.neg_apply]; rw [Pi.inv_apply]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← EReal.neg_mul]; rw [log_inv]

Depends on / 依赖: EReal.neg_mul, Eventually, Eventually.of_forall, Pi.inv_apply, Pi.neg_apply, div_eq_mul_inv, expGrowthInf, inv_apply, limsup_congr, limsup_neg, log_inv, neg_apply, neg_mul, of_forall
-/
lemma expGrowthSup_inv : expGrowthSup u⁻¹ = - expGrowthInf u := by
  rw [expGrowthInf]; rw [← limsup_neg]
  refine limsup_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.neg_apply]; rw [Pi.inv_apply]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← EReal.neg_mul]; rw [log_inv]


-- Bound on `expGrowthInf` under a `IsBigO` hypothesis. However, `ℝ≥0∞` is not normed, so the
-- `IsBigO` property is spelt out.
/--
lemma `expGrowthInf_le_of_eventually_le` / 引理 `expGrowthInf_le_of_eventually_le`

English:
lemma expGrowthInf_le_of_eventually_le
  given: (hb : b != ∞) (h : forallᶠ n in atTop, u n <= b * v n)
  proof: by
  apply (expGrowthInf_eventually_monotone h).trans
  rcases eq_zero_or_pos b with rfl | b_pos
  · simp only [zero_mul, ← Pi.zero_def, expGrowthInf_zero, bot_le]
  · apply (expGrowthInf_mul_le _ _).trans_eq <;> rw [expGrowthSup_const b_pos.ne' hb]
    · exact zero_add (expGrowthInf v)
    · exact 

中文:
引理 expGrowthInf_le_of_eventually_le
  条件: (hb : b != ∞) (h : 对任意ᶠ n in atTop, u n <= b * v n)
  证明: by
  apply (expGrowthInf_eventually_monotone h).trans
  rcases eq_zero_or_pos b with rfl | b_pos
  · simp only [zero_mul, ← Pi.zero_def, expGrowthInf_zero, bot_le]
  · apply (expGrowthInf_mul_le _ _).trans_eq <;> rw [expGrowthSup_const b_pos.ne' hb]
    · exact zero_add (expGrowthInf v)
    · exact 

Depends on / 依赖: Pi.zero_def, b_pos, b_pos.ne, bot_le, eq_zero_or_pos, expGrowthInf, expGrowthInf_eventually_monotone, expGrowthInf_mul_le, expGrowthInf_zero, expGrowthSup_const, trans_eq, zero_add, zero_def, zero_mul, zero_ne_bot, zero_ne_top
-/
lemma expGrowthInf_le_of_eventually_le (hb : b != ∞) (h : forallᶠ n in atTop, u n <= b * v n) :
    expGrowthInf u <= expGrowthInf v := by
  apply (expGrowthInf_eventually_monotone h).trans
  rcases eq_zero_or_pos b with rfl | b_pos
  · simp only [zero_mul, ← Pi.zero_def, expGrowthInf_zero, bot_le]
  · apply (expGrowthInf_mul_le _ _).trans_eq <;> rw [expGrowthSup_const b_pos.ne' hb]
    · exact zero_add (expGrowthInf v)
    · exact .inl zero_ne_bot
    · exact .inl zero_ne_top

-- Bound on `expGrowthSup` under a `IsBigO` hypothesis. However, `ℝ≥0∞` is not normed, so the
-- `IsBigO` property is spelt out.
/--
lemma `expGrowthSup_le_of_eventually_le` / 引理 `expGrowthSup_le_of_eventually_le`

English:
lemma expGrowthSup_le_of_eventually_le
  given: (hb : b != ∞) (h : forallᶠ n in atTop, u n <= b * v n)
  proof: by
  apply (expGrowthSup_eventually_monotone h).trans
  rcases eq_zero_or_pos b with rfl | b_pos
  · simp only [zero_mul, ← Pi.zero_def, expGrowthSup_zero, bot_le]
  · apply (expGrowthSup_mul_le _ _).trans_eq <;> rw [expGrowthSup_const b_pos.ne' hb]
    · exact zero_add (expGrowthSup v)
    · exact 

中文:
引理 expGrowthSup_le_of_eventually_le
  条件: (hb : b != ∞) (h : 对任意ᶠ n in atTop, u n <= b * v n)
  证明: by
  apply (expGrowthSup_eventually_monotone h).trans
  rcases eq_zero_or_pos b with rfl | b_pos
  · simp only [zero_mul, ← Pi.zero_def, expGrowthSup_zero, bot_le]
  · apply (expGrowthSup_mul_le _ _).trans_eq <;> rw [expGrowthSup_const b_pos.ne' hb]
    · exact zero_add (expGrowthSup v)
    · exact 

Depends on / 依赖: Pi.zero_def, b_pos, b_pos.ne, bot_le, eq_zero_or_pos, expGrowthSup, expGrowthSup_const, expGrowthSup_eventually_monotone, expGrowthSup_mul_le, expGrowthSup_zero, trans_eq, zero_add, zero_def, zero_mul, zero_ne_bot, zero_ne_top
-/
lemma expGrowthSup_le_of_eventually_le (hb : b != ∞) (h : forallᶠ n in atTop, u n <= b * v n) :
    expGrowthSup u <= expGrowthSup v := by
  apply (expGrowthSup_eventually_monotone h).trans
  rcases eq_zero_or_pos b with rfl | b_pos
  · simp only [zero_mul, ← Pi.zero_def, expGrowthSup_zero, bot_le]
  · apply (expGrowthSup_mul_le _ _).trans_eq <;> rw [expGrowthSup_const b_pos.ne' hb]
    · exact zero_add (expGrowthSup v)
    · exact .inl zero_ne_bot
    · exact .inl zero_ne_top

/--
lemma `expGrowthInf_of_eventually_ge` / 引理 `expGrowthInf_of_eventually_ge`

English:
lemma expGrowthInf_of_eventually_ge
  given: (hb : b != 0) (h : forallᶠ n in atTop, b * u n <= v n)
  proof: by
  apply (expGrowthInf_eventually_monotone h).trans' (le_expGrowthInf_mul.trans' _)
  rcases eq_top_or_lt_top b with rfl | b_top
  · rw [← Pi.top_def, expGrowthInf_top]
    exact le_add_of_nonneg_left le_top
  · rw [expGrowthInf_const hb b_top.ne, zero_add]

中文:
引理 expGrowthInf_of_eventually_ge
  条件: (hb : b != 0) (h : 对任意ᶠ n in atTop, b * u n <= v n)
  证明: by
  apply (expGrowthInf_eventually_monotone h).trans' (le_expGrowthInf_mul.trans' _)
  rcases eq_top_or_lt_top b with rfl | b_top
  · rw [← Pi.top_def, expGrowthInf_top]
    exact le_add_of_nonneg_left le_top
  · rw [expGrowthInf_const hb b_top.ne, zero_add]

Depends on / 依赖: Pi.top_def, b_top, b_top.ne, eq_top_or_lt_top, expGrowthInf_const, expGrowthInf_eventually_monotone, expGrowthInf_top, le_add_of_nonneg_left, le_expGrowthInf_mul, le_expGrowthInf_mul.trans, le_top, top_def, zero_add
-/
lemma expGrowthInf_of_eventually_ge (hb : b != 0) (h : forallᶠ n in atTop, b * u n <= v n) :
    expGrowthInf u <= expGrowthInf v := by
  apply (expGrowthInf_eventually_monotone h).trans' (le_expGrowthInf_mul.trans' _)
  rcases eq_top_or_lt_top b with rfl | b_top
  · rw [← Pi.top_def, expGrowthInf_top]
    exact le_add_of_nonneg_left le_top
  · rw [expGrowthInf_const hb b_top.ne, zero_add]

/--
lemma `expGrowthSup_of_eventually_ge` / 引理 `expGrowthSup_of_eventually_ge`

English:
lemma expGrowthSup_of_eventually_ge
  given: (hb : b != 0) (h : forallᶠ n in atTop, b * u n <= v n)
  proof: by
  apply (expGrowthSup_eventually_monotone h).trans' (le_expGrowthSup_mul'.trans' _)
  rcases eq_top_or_lt_top b with rfl | b_top
  · exact expGrowthInf_top ▸ le_add_of_nonneg_left le_top
  · rw [expGrowthInf_const hb b_top.ne, zero_add]

中文:
引理 expGrowthSup_of_eventually_ge
  条件: (hb : b != 0) (h : 对任意ᶠ n in atTop, b * u n <= v n)
  证明: by
  apply (expGrowthSup_eventually_monotone h).trans' (le_expGrowthSup_mul'.trans' _)
  rcases eq_top_or_lt_top b with rfl | b_top
  · exact expGrowthInf_top ▸ le_add_of_nonneg_left le_top
  · rw [expGrowthInf_const hb b_top.ne, zero_add]

Depends on / 依赖: b_top, b_top.ne, eq_top_or_lt_top, expGrowthInf_const, expGrowthInf_top, expGrowthSup_eventually_monotone, le_add_of_nonneg_left, le_expGrowthSup_mul, le_top, zero_add
-/
lemma expGrowthSup_of_eventually_ge (hb : b != 0) (h : forallᶠ n in atTop, b * u n <= v n) :
    expGrowthSup u <= expGrowthSup v := by
  apply (expGrowthSup_eventually_monotone h).trans' (le_expGrowthSup_mul'.trans' _)
  rcases eq_top_or_lt_top b with rfl | b_top
  · exact expGrowthInf_top ▸ le_add_of_nonneg_left le_top
  · rw [expGrowthInf_const hb b_top.ne, zero_add]


/--
lemma `expGrowthInf_inf` / 引理 `expGrowthInf_inf`

English:
lemma expGrowthInf_inf
  statement: expGrowthInf (u ⊓ v) = expGrowthInf u ⊓ expGrowthInf v
  proof: by
  rw [expGrowthInf]; rw [expGrowthInf]; rw [expGrowthInf]; rw [← liminf_min]
  refine liminf_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.inf_apply]; rw [log_monotone.map_min]
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_min

中文:
引理 expGrowthInf_inf
  结论: expGrowthInf (u ⊓ v) = expGrowthInf u ⊓ expGrowthInf v
  证明: by
  rw [expGrowthInf]; rw [expGrowthInf]; rw [expGrowthInf]; rw [← liminf_min]
  refine liminf_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.inf_apply]; rw [log_monotone.map_min]
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_min

Depends on / 依赖: Eventually, Eventually.of_forall, Pi.inf_apply, cast_nonneg, expGrowthInf, inf_apply, liminf_congr, liminf_min, log_monotone, log_monotone.map_min, map_min, monotone_div_right_of_nonneg, n.cast_nonneg, of_forall
-/
lemma expGrowthInf_inf : expGrowthInf (u ⊓ v) = expGrowthInf u ⊓ expGrowthInf v := by
  rw [expGrowthInf]; rw [expGrowthInf]; rw [expGrowthInf]; rw [← liminf_min]
  refine liminf_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.inf_apply]; rw [log_monotone.map_min]
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_min

/--
Definition of `expGrowthInfTopHom` / `expGrowthInfTopHom` 的定义

English:
definition expGrowthInfTopHom
  signature: : InfTopHom (Nat -> Real>=0∞) EReal where
  body: expGrowthInf
  map_inf' _ _ := expGrowthInf_inf
  map_top' := expGrowthInf_top

中文:
定义 expGrowthInfTopHom
  签名: : InfTopHom (自然数 -> 实数>=0∞) E实数 where
  定义体: expGrowthInf
  map_inf' _ _ := expGrowthInf_inf
  map_top' := expGrowthInf_top

Depends on / 依赖: expGrowthInf
-/
noncomputable def expGrowthInfTopHom : InfTopHom (Nat -> Real>=0∞) EReal where
  toFun := expGrowthInf
  map_inf' _ _ := expGrowthInf_inf
  map_top' := expGrowthInf_top

/--
lemma `expGrowthInf_biInf` / 引理 `expGrowthInf_biInf`

English:
lemma expGrowthInf_biInf
  given: {α : Type*} (u : α -> Nat -> Real>=0∞) {s : Set α} (hs : s.Finite)
  proof: by
  have := map_finset_inf expGrowthInfTopHom hs.toFinset u
  simpa only [expGrowthInfTopHom, InfTopHom.coe_mk, InfHom.coe_mk, Finset.inf_eq_iInf,
    hs.mem_toFinset, comp_apply]

中文:
引理 expGrowthInf_biInf
  条件: {α : 类型} (u : α -> 自然数 -> 实数>=0∞) {s : Set α} (hs : s.Finite)
  证明: by
  have := map_finset_inf expGrowthInfTopHom hs.toFinset u
  simpa only [expGrowthInfTopHom, InfTopHom.coe_mk, InfHom.coe_mk, Finset.inf_eq_iInf,
    hs.mem_toFinset, comp_apply]

Depends on / 依赖: Finset, Finset.inf_eq_iInf, InfHom, InfHom.coe_mk, InfTopHom, InfTopHom.coe_mk, coe_mk, comp_apply, expGrowthInfTopHom, hs.mem_toFinset, hs.toFinset, inf_eq_iInf, map_finset_inf, mem_toFinset, toFinset
-/
lemma expGrowthInf_biInf {α : Type*} (u : α -> Nat -> Real>=0∞) {s : Set α} (hs : s.Finite) :
    expGrowthInf (⨅ x in s, u x) = ⨅ x in s, expGrowthInf (u x) := by
  have := map_finset_inf expGrowthInfTopHom hs.toFinset u
  simpa only [expGrowthInfTopHom, InfTopHom.coe_mk, InfHom.coe_mk, Finset.inf_eq_iInf,
    hs.mem_toFinset, comp_apply]

/--
lemma `expGrowthInf_iInf` / 引理 `expGrowthInf_iInf`

English:
lemma expGrowthInf_iInf
  given: {ι : Type*} [Finite ι] (u : ι -> Nat -> Real>=0∞)
  proof: by
  rw [← iInf_univ]; rw [expGrowthInf_biInf u Set.finite_univ]; rw [iInf_univ]

中文:
引理 expGrowthInf_iInf
  条件: {ι : 类型} [Finite ι] (u : ι -> 自然数 -> 实数>=0∞)
  证明: by
  rw [← iInf_univ]; rw [expGrowthInf_biInf u Set.finite_univ]; rw [iInf_univ]

Depends on / 依赖: Set.finite_univ, expGrowthInf_biInf, finite_univ, iInf_univ
-/
lemma expGrowthInf_iInf {ι : Type*} [Finite ι] (u : ι -> Nat -> Real>=0∞) :
    expGrowthInf (⨅ i, u i) = ⨅ i, expGrowthInf (u i) := by
  rw [← iInf_univ]; rw [expGrowthInf_biInf u Set.finite_univ]; rw [iInf_univ]

/--
lemma `expGrowthSup_sup` / 引理 `expGrowthSup_sup`

English:
lemma expGrowthSup_sup
  statement: expGrowthSup (u ⊔ v) = expGrowthSup u ⊔ expGrowthSup v
  proof: by
  rw [expGrowthSup]; rw [expGrowthSup]; rw [expGrowthSup]; rw [← limsup_max]
  refine limsup_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.sup_apply]; rw [log_monotone.map_max]
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_max

中文:
引理 expGrowthSup_sup
  结论: expGrowthSup (u ⊔ v) = expGrowthSup u ⊔ expGrowthSup v
  证明: by
  rw [expGrowthSup]; rw [expGrowthSup]; rw [expGrowthSup]; rw [← limsup_max]
  refine limsup_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.sup_apply]; rw [log_monotone.map_max]
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_max

Depends on / 依赖: Eventually, Eventually.of_forall, Pi.sup_apply, cast_nonneg, expGrowthSup, limsup_congr, limsup_max, log_monotone, log_monotone.map_max, map_max, monotone_div_right_of_nonneg, n.cast_nonneg, of_forall, sup_apply
-/
lemma expGrowthSup_sup : expGrowthSup (u ⊔ v) = expGrowthSup u ⊔ expGrowthSup v := by
  rw [expGrowthSup]; rw [expGrowthSup]; rw [expGrowthSup]; rw [← limsup_max]
  refine limsup_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.sup_apply]; rw [log_monotone.map_max]
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_max

/--
Definition of `expGrowthSupBotHom` / `expGrowthSupBotHom` 的定义

English:
definition expGrowthSupBotHom
  signature: : SupBotHom (Nat -> Real>=0∞) EReal where
  body: expGrowthSup
  map_sup' _ _ := expGrowthSup_sup
  map_bot' := expGrowthSup_zero

中文:
定义 expGrowthSupBotHom
  签名: : SupBotHom (自然数 -> 实数>=0∞) E实数 where
  定义体: expGrowthSup
  map_sup' _ _ := expGrowthSup_sup
  map_bot' := expGrowthSup_zero

Depends on / 依赖: expGrowthSup
-/
noncomputable def expGrowthSupBotHom : SupBotHom (Nat -> Real>=0∞) EReal where
  toFun := expGrowthSup
  map_sup' _ _ := expGrowthSup_sup
  map_bot' := expGrowthSup_zero

/--
lemma `expGrowthSup_biSup` / 引理 `expGrowthSup_biSup`

English:
lemma expGrowthSup_biSup
  given: {α : Type*} (u : α -> Nat -> Real>=0∞) {s : Set α} (hs : s.Finite)
  proof: by
  have := map_finset_sup expGrowthSupBotHom hs.toFinset u
  simpa only [expGrowthSupBotHom, SupBotHom.coe_mk, SupHom.coe_mk, Finset.sup_eq_iSup,
    hs.mem_toFinset, comp_apply]

中文:
引理 expGrowthSup_biSup
  条件: {α : 类型} (u : α -> 自然数 -> 实数>=0∞) {s : Set α} (hs : s.Finite)
  证明: by
  have := map_finset_sup expGrowthSupBotHom hs.toFinset u
  simpa only [expGrowthSupBotHom, SupBotHom.coe_mk, SupHom.coe_mk, Finset.sup_eq_iSup,
    hs.mem_toFinset, comp_apply]

Depends on / 依赖: Finset, Finset.sup_eq_iSup, SupBotHom, SupBotHom.coe_mk, SupHom, SupHom.coe_mk, coe_mk, comp_apply, expGrowthSupBotHom, hs.mem_toFinset, hs.toFinset, map_finset_sup, mem_toFinset, sup_eq_iSup, toFinset
-/
lemma expGrowthSup_biSup {α : Type*} (u : α -> Nat -> Real>=0∞) {s : Set α} (hs : s.Finite) :
    expGrowthSup (⨆ x in s, u x) = ⨆ x in s, expGrowthSup (u x) := by
  have := map_finset_sup expGrowthSupBotHom hs.toFinset u
  simpa only [expGrowthSupBotHom, SupBotHom.coe_mk, SupHom.coe_mk, Finset.sup_eq_iSup,
    hs.mem_toFinset, comp_apply]

/--
lemma `expGrowthSup_iSup` / 引理 `expGrowthSup_iSup`

English:
lemma expGrowthSup_iSup
  given: {ι : Type*} [Finite ι] (u : ι -> Nat -> Real>=0∞)
  proof: by
  rw [← iSup_univ]; rw [expGrowthSup_biSup u Set.finite_univ]; rw [iSup_univ]

中文:
引理 expGrowthSup_iSup
  条件: {ι : 类型} [Finite ι] (u : ι -> 自然数 -> 实数>=0∞)
  证明: by
  rw [← iSup_univ]; rw [expGrowthSup_biSup u Set.finite_univ]; rw [iSup_univ]

Depends on / 依赖: Set.finite_univ, expGrowthSup_biSup, finite_univ, iSup_univ
-/
lemma expGrowthSup_iSup {ι : Type*} [Finite ι] (u : ι -> Nat -> Real>=0∞) :
    expGrowthSup (⨆ i, u i) = ⨆ i, expGrowthSup (u i) := by
  rw [← iSup_univ]; rw [expGrowthSup_biSup u Set.finite_univ]; rw [iSup_univ]


/--
lemma `le_expGrowthInf_add` / 引理 `le_expGrowthInf_add`

English:
lemma le_expGrowthInf_add
  statement: expGrowthInf u ⊔ expGrowthInf v <= expGrowthInf (u + v)
  proof: sup_le (expGrowthInf_monotone le_self_add) (expGrowthInf_monotone le_add_self)

中文:
引理 le_expGrowthInf_add
  结论: expGrowthInf u ⊔ expGrowthInf v <= expGrowthInf (u + v)
  证明: sup_le (expGrowthInf_monotone le_self_add) (expGrowthInf_monotone le_add_self)

Depends on / 依赖: expGrowthInf_monotone, le_add_self, le_self_add, sup_le
-/
lemma le_expGrowthInf_add : expGrowthInf u ⊔ expGrowthInf v <= expGrowthInf (u + v) :=
  sup_le (expGrowthInf_monotone le_self_add) (expGrowthInf_monotone le_add_self)

/--
lemma `expGrowthSup_add` / 引理 `expGrowthSup_add`

English:
lemma expGrowthSup_add
  statement: expGrowthSup (u + v) = expGrowthSup u ⊔ expGrowthSup v
  proof: by
  rw [← expGrowthSup_sup]
  apply le_antisymm
  · refine expGrowthSup_le_of_eventually_le (b := 2) ofNat_ne_top (Eventually.of_forall fun n => ?_)
    rw [Pi.sup_apply u v n]; rw [Pi.add_apply u v n]; rw [two_mul]
    exact add_le_add (le_max_left (u n) (v n)) (le_max_right (u n) (v n))
  · refin

中文:
引理 expGrowthSup_add
  结论: expGrowthSup (u + v) = expGrowthSup u ⊔ expGrowthSup v
  证明: by
  rw [← expGrowthSup_sup]
  apply le_antisymm
  · refine expGrowthSup_le_of_eventually_le (b := 2) ofNat_ne_top (Eventually.of_forall fun n => ?_)
    rw [Pi.sup_apply u v n]; rw [Pi.add_apply u v n]; rw [two_mul]
    exact add_le_add (le_max_left (u n) (v n)) (le_max_right (u n) (v n))
  · refin

Depends on / 依赖: Eventually, Eventually.of_forall, Pi.add_apply, Pi.sup_apply, add_apply, add_le_add, expGrowthSup_le_of_eventually_le, expGrowthSup_monotone, expGrowthSup_sup, le_antisymm, le_max_left, le_max_right, ofNat_ne_top, of_forall, self_le_add_left, self_le_add_right, sup_apply, sup_le, two_mul
-/
lemma expGrowthSup_add : expGrowthSup (u + v) = expGrowthSup u ⊔ expGrowthSup v := by
  rw [← expGrowthSup_sup]
  apply le_antisymm
  · refine expGrowthSup_le_of_eventually_le (b := 2) ofNat_ne_top (Eventually.of_forall fun n => ?_)
    rw [Pi.sup_apply u v n]; rw [Pi.add_apply u v n]; rw [two_mul]
    exact add_le_add (le_max_left (u n) (v n)) (le_max_right (u n) (v n))
  · refine expGrowthSup_monotone fun n => ?_
    exact sup_le (self_le_add_right (u n) (v n)) (self_le_add_left (v n) (u n))

-- By lemma `expGrowthSup_add`, `expGrowthSup` is an `AddMonoidHom` from `ℕ → ℝ≥0∞` to
-- `Tropical ERealᵒᵈ`. Lemma `expGrowthSup_sum` is exactly `Finset.trop_inf`. We prove it from
-- scratch to reduce imports.
/--
lemma `expGrowthSup_sum` / 引理 `expGrowthSup_sum`

English:
lemma expGrowthSup_sum
  given: {α : Type*} (u : α -> Nat -> Real>=0∞) (s : Finset α)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, ← Finset.iSup_coe, Finset.coe_empty, iSup_emptyset,
    expGrowthSup_zero]
  | insert a t a_t ha => rw [Finset.sum_insert a_t, expGrowthSup_add, ← Finset.iSup_coe,
    Finset.coe_insert a t, iSup_insert, F

中文:
引理 expGrowthSup_sum
  条件: {α : 类型} (u : α -> 自然数 -> 实数>=0∞) (s : Finset α)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, ← Finset.iSup_coe, Finset.coe_empty, iSup_emptyset,
    expGrowthSup_zero]
  | insert a t a_t ha => rw [Finset.sum_insert a_t, expGrowthSup_add, ← Finset.iSup_coe,
    Finset.coe_insert a t, iSup_insert, F

Depends on / 依赖: Finset, Finset.coe_empty, Finset.coe_insert, Finset.iSup_coe, Finset.induction_on, Finset.sum_empty, Finset.sum_insert, classical, coe_empty, coe_insert, expGrowthSup_add, expGrowthSup_zero, iSup_coe, iSup_emptyset, iSup_insert, induction_on, insert, sum_empty, sum_insert
-/
lemma expGrowthSup_sum {α : Type*} (u : α -> Nat -> Real>=0∞) (s : Finset α) :
    expGrowthSup (∑ x in s, u x) = ⨆ x in s, expGrowthSup (u x) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, ← Finset.iSup_coe, Finset.coe_empty, iSup_emptyset,
    expGrowthSup_zero]
  | insert a t a_t ha => rw [Finset.sum_insert a_t, expGrowthSup_add, ← Finset.iSup_coe,
    Finset.coe_insert a t, iSup_insert, Finset.iSup_coe, ha]

end basic_properties

/-! ### Composition -/

section composition

variable {u : Nat -> Real>=0∞} {v : Nat -> Nat}

/--
lemma `le_expGrowthInf_comp` / 引理 `le_expGrowthInf_comp`

English:
lemma le_expGrowthInf_comp
  given: (hu : 1 <=ᶠ[atTop] u) (hv : Tendsto v atTop atTop)
  proof: by
  apply le_linearGrowthInf_comp (hu.mono fun n h => ?_) hv
  rw [Pi.one_apply] at h
  rwa [Pi.zero_apply, zero_le_log_iff]

中文:
引理 le_expGrowthInf_comp
  条件: (hu : 1 <=ᶠ[atTop] u) (hv : Tendsto v atTop atTop)
  证明: by
  apply le_linearGrowthInf_comp (hu.mono fun n h => ?_) hv
  rw [Pi.one_apply] at h
  rwa [Pi.zero_apply, zero_le_log_iff]

Depends on / 依赖: Pi.one_apply, Pi.zero_apply, hu.mono, le_linearGrowthInf_comp, one_apply, zero_apply, zero_le_log_iff
-/
lemma le_expGrowthInf_comp (hu : 1 <=ᶠ[atTop] u) (hv : Tendsto v atTop atTop) :
    (linearGrowthInf fun n => v n : EReal) * expGrowthInf u <= expGrowthInf (u ∘ v) := by
  apply le_linearGrowthInf_comp (hu.mono fun n h => ?_) hv
  rw [Pi.one_apply] at h
  rwa [Pi.zero_apply, zero_le_log_iff]

/--
lemma `expGrowthSup_comp_le` / 引理 `expGrowthSup_comp_le`

English:
lemma expGrowthSup_comp_le
  statement: (hu : existsᶠ n in atTop, 1 <= u n)
  proof: by
  apply linearGrowthSup_comp_le (u := log ∘ u) (hu.mono fun n h => ?_) hv₀ hv₁ hv₂
  rwa [comp_apply, zero_le_log_iff]

中文:
引理 expGrowthSup_comp_le
  结论: (hu : 存在ᶠ n in atTop, 1 <= u n)
  证明: by
  apply linearGrowthSup_comp_le (u := log ∘ u) (hu.mono fun n h => ?_) hv₀ hv₁ hv₂
  rwa [comp_apply, zero_le_log_iff]

Depends on / 依赖: comp_apply, hu.mono, linearGrowthSup_comp_le, zero_le_log_iff
-/
lemma expGrowthSup_comp_le (hu : existsᶠ n in atTop, 1 <= u n)
    (hv₀ : (linearGrowthSup fun n => v n : EReal) != 0)
    (hv₁ : (linearGrowthSup fun n => v n : EReal) != ⊤) (hv₂ : Tendsto v atTop atTop) :
    expGrowthSup (u ∘ v) <= (linearGrowthSup fun n => v n : EReal) * expGrowthSup u := by
  apply linearGrowthSup_comp_le (u := log ∘ u) (hu.mono fun n h => ?_) hv₀ hv₁ hv₂
  rwa [comp_apply, zero_le_log_iff]


/--
lemma `_root_.Monotone.expGrowthInf_nonneg` / 引理 `_root_.Monotone.expGrowthInf_nonneg`

English:
lemma _root_.Monotone.expGrowthInf_nonneg
  given: (h : Monotone u) (h' : u != 0)
  proof: by
  apply (log_monotone.comp h).linearGrowthInf_nonneg
  simp only [ne_eq, funext_iff, comp_apply, Pi.bot_apply, log_eq_bot_iff, Pi.zero_apply] at h' ⊢
  exact h'

中文:
引理 _root_.Monotone.expGrowthInf_nonneg
  条件: (h : Monotone u) (h' : u != 0)
  证明: by
  apply (log_monotone.comp h).linearGrowthInf_nonneg
  simp only [ne_eq, funext_iff, comp_apply, Pi.bot_apply, log_eq_bot_iff, Pi.zero_apply] at h' ⊢
  exact h'

Depends on / 依赖: Pi.bot_apply, Pi.zero_apply, bot_apply, comp_apply, funext_iff, linearGrowthInf_nonneg, log_eq_bot_iff, log_monotone, log_monotone.comp, ne_eq, zero_apply
-/
lemma _root_.Monotone.expGrowthInf_nonneg (h : Monotone u) (h' : u != 0) :
    0 <= expGrowthInf u := by
  apply (log_monotone.comp h).linearGrowthInf_nonneg
  simp only [ne_eq, funext_iff, comp_apply, Pi.bot_apply, log_eq_bot_iff, Pi.zero_apply] at h' ⊢
  exact h'

/--
lemma `_root_.Monotone.expGrowthSup_nonneg` / 引理 `_root_.Monotone.expGrowthSup_nonneg`

English:
lemma _root_.Monotone.expGrowthSup_nonneg
  given: (h : Monotone u) (h' : u != 0)
  proof: (h.expGrowthInf_nonneg h').trans expGrowthInf_le_expGrowthSup

中文:
引理 _root_.Monotone.expGrowthSup_nonneg
  条件: (h : Monotone u) (h' : u != 0)
  证明: (h.expGrowthInf_nonneg h').trans expGrowthInf_le_expGrowthSup

Depends on / 依赖: expGrowthInf_le_expGrowthSup, expGrowthInf_nonneg, h.expGrowthInf_nonneg
-/
lemma _root_.Monotone.expGrowthSup_nonneg (h : Monotone u) (h' : u != 0) :
    0 <= expGrowthSup u :=
  (h.expGrowthInf_nonneg h').trans expGrowthInf_le_expGrowthSup

/--
lemma `expGrowthInf_comp_nonneg` / 引理 `expGrowthInf_comp_nonneg`

English:
lemma expGrowthInf_comp_nonneg
  given: (h : Monotone u) (h' : u != 0) (hv : Tendsto v atTop atTop)
  proof: by
  apply linearGrowthInf_comp_nonneg (u := log ∘ u) (log_monotone.comp h) _ hv
  simp only [ne_eq, funext_iff, comp_apply, Pi.bot_apply, log_eq_bot_iff, Pi.zero_apply] at h' ⊢
  exact h'

中文:
引理 expGrowthInf_comp_nonneg
  条件: (h : Monotone u) (h' : u != 0) (hv : Tendsto v atTop atTop)
  证明: by
  apply linearGrowthInf_comp_nonneg (u := log ∘ u) (log_monotone.comp h) _ hv
  simp only [ne_eq, funext_iff, comp_apply, Pi.bot_apply, log_eq_bot_iff, Pi.zero_apply] at h' ⊢
  exact h'

Depends on / 依赖: Pi.bot_apply, Pi.zero_apply, bot_apply, comp_apply, funext_iff, linearGrowthInf_comp_nonneg, log_eq_bot_iff, log_monotone, log_monotone.comp, ne_eq, zero_apply
-/
lemma expGrowthInf_comp_nonneg (h : Monotone u) (h' : u != 0) (hv : Tendsto v atTop atTop) :
    0 <= expGrowthInf (u ∘ v) := by
  apply linearGrowthInf_comp_nonneg (u := log ∘ u) (log_monotone.comp h) _ hv
  simp only [ne_eq, funext_iff, comp_apply, Pi.bot_apply, log_eq_bot_iff, Pi.zero_apply] at h' ⊢
  exact h'

/--
lemma `expGrowthSup_comp_nonneg` / 引理 `expGrowthSup_comp_nonneg`

English:
lemma expGrowthSup_comp_nonneg
  given: (h : Monotone u) (h' : u != 0) (hv : Tendsto v atTop atTop)
  proof: (expGrowthInf_comp_nonneg h h' hv).trans expGrowthInf_le_expGrowthSup

中文:
引理 expGrowthSup_comp_nonneg
  条件: (h : Monotone u) (h' : u != 0) (hv : Tendsto v atTop atTop)
  证明: (expGrowthInf_comp_nonneg h h' hv).trans expGrowthInf_le_expGrowthSup

Depends on / 依赖: expGrowthInf_comp_nonneg, expGrowthInf_le_expGrowthSup
-/
lemma expGrowthSup_comp_nonneg (h : Monotone u) (h' : u != 0) (hv : Tendsto v atTop atTop) :
    0 <= expGrowthSup (u ∘ v) :=
  (expGrowthInf_comp_nonneg h h' hv).trans expGrowthInf_le_expGrowthSup

/--
lemma `_root_.Monotone.expGrowthInf_comp_le` / 引理 `_root_.Monotone.expGrowthInf_comp_le`

English:
lemma _root_.Monotone.expGrowthInf_comp_le
  statement: (h : Monotone u)
  proof: (log_monotone.comp h).linearGrowthInf_comp_le hv₀ hv₁

中文:
引理 _root_.Monotone.expGrowthInf_comp_le
  结论: (h : Monotone u)
  证明: (log_monotone.comp h).linearGrowthInf_comp_le hv₀ hv₁

Depends on / 依赖: linearGrowthInf_comp_le, log_monotone, log_monotone.comp
-/
lemma _root_.Monotone.expGrowthInf_comp_le (h : Monotone u)
    (hv₀ : (linearGrowthSup fun n => v n : EReal) != 0)
    (hv₁ : (linearGrowthSup fun n => v n : EReal) != ⊤) :
    expGrowthInf (u ∘ v) <= (linearGrowthSup fun n => v n : EReal) * expGrowthInf u :=
  (log_monotone.comp h).linearGrowthInf_comp_le hv₀ hv₁

/--
lemma `_root_.Monotone.le_expGrowthSup_comp` / 引理 `_root_.Monotone.le_expGrowthSup_comp`

English:
lemma _root_.Monotone.le_expGrowthSup_comp
  statement: (h : Monotone u)
  proof: (log_monotone.comp h).le_linearGrowthSup_comp hv

中文:
引理 _root_.Monotone.le_expGrowthSup_comp
  结论: (h : Monotone u)
  证明: (log_monotone.comp h).le_linearGrowthSup_comp hv

Depends on / 依赖: le_linearGrowthSup_comp, log_monotone, log_monotone.comp
-/
lemma _root_.Monotone.le_expGrowthSup_comp (h : Monotone u)
    (hv : (linearGrowthInf fun n => v n : EReal) != 0) :
    (linearGrowthInf fun n => v n : EReal) * expGrowthSup u <= expGrowthSup (u ∘ v) :=
  (log_monotone.comp h).le_linearGrowthSup_comp hv

/--
lemma `_root_.Monotone.expGrowthInf_comp` / 引理 `_root_.Monotone.expGrowthInf_comp`

English:
lemma _root_.Monotone.expGrowthInf_comp
  statement: {a : EReal} (h : Monotone u)
  proof: (log_monotone.comp h).linearGrowthInf_comp hv ha ha'

中文:
引理 _root_.Monotone.expGrowthInf_comp
  结论: {a : E实数} (h : Monotone u)
  证明: (log_monotone.comp h).linearGrowthInf_comp hv ha ha'

Depends on / 依赖: linearGrowthInf_comp, log_monotone, log_monotone.comp
-/
lemma _root_.Monotone.expGrowthInf_comp {a : EReal} (h : Monotone u)
    (hv : Tendsto (fun n => (v n : EReal) / n) atTop (𝓝 a)) (ha : a != 0) (ha' : a != ⊤) :
    expGrowthInf (u ∘ v) = a * expGrowthInf u :=
  (log_monotone.comp h).linearGrowthInf_comp hv ha ha'

/--
lemma `_root_.Monotone.expGrowthSup_comp` / 引理 `_root_.Monotone.expGrowthSup_comp`

English:
lemma _root_.Monotone.expGrowthSup_comp
  statement: {a : EReal} (h : Monotone u)
  proof: (log_monotone.comp h).linearGrowthSup_comp hv ha ha'

中文:
引理 _root_.Monotone.expGrowthSup_comp
  结论: {a : E实数} (h : Monotone u)
  证明: (log_monotone.comp h).linearGrowthSup_comp hv ha ha'

Depends on / 依赖: linearGrowthSup_comp, log_monotone, log_monotone.comp
-/
lemma _root_.Monotone.expGrowthSup_comp {a : EReal} (h : Monotone u)
    (hv : Tendsto (fun n => (v n : EReal) / n) atTop (𝓝 a)) (ha : a != 0) (ha' : a != ⊤) :
    expGrowthSup (u ∘ v) = a * expGrowthSup u :=
  (log_monotone.comp h).linearGrowthSup_comp hv ha ha'

/--
lemma `_root_.Monotone.expGrowthInf_comp_mul` / 引理 `_root_.Monotone.expGrowthInf_comp_mul`

English:
lemma _root_.Monotone.expGrowthInf_comp_mul
  given: {m : Nat} (h : Monotone u) (hm : m != 0)
  proof: (log_monotone.comp h).linearGrowthInf_comp_mul hm

中文:
引理 _root_.Monotone.expGrowthInf_comp_mul
  条件: {m : 自然数} (h : Monotone u) (hm : m != 0)
  证明: (log_monotone.comp h).linearGrowthInf_comp_mul hm

Depends on / 依赖: linearGrowthInf_comp_mul, log_monotone, log_monotone.comp
-/
lemma _root_.Monotone.expGrowthInf_comp_mul {m : Nat} (h : Monotone u) (hm : m != 0) :
    expGrowthInf (fun n => u (m * n)) = m * expGrowthInf u :=
  (log_monotone.comp h).linearGrowthInf_comp_mul hm

/--
lemma `_root_.Monotone.expGrowthSup_comp_mul` / 引理 `_root_.Monotone.expGrowthSup_comp_mul`

English:
lemma _root_.Monotone.expGrowthSup_comp_mul
  given: {m : Nat} (h : Monotone u) (hm : m != 0)
  proof: (log_monotone.comp h).linearGrowthSup_comp_mul hm

中文:
引理 _root_.Monotone.expGrowthSup_comp_mul
  条件: {m : 自然数} (h : Monotone u) (hm : m != 0)
  证明: (log_monotone.comp h).linearGrowthSup_comp_mul hm

Depends on / 依赖: linearGrowthSup_comp_mul, log_monotone, log_monotone.comp
-/
lemma _root_.Monotone.expGrowthSup_comp_mul {m : Nat} (h : Monotone u) (hm : m != 0) :
    expGrowthSup (fun n => u (m * n)) = m * expGrowthSup u :=
  (log_monotone.comp h).linearGrowthSup_comp_mul hm

end composition

end ExpGrowth
