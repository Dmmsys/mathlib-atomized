/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Linear growth

This file defines the linear growth of a sequence `u : ℕ → R`. This notion comes in two
versions, using a `liminf` and a `limsup` respectively. Most properties are developed for
`R = EReal`.

## Main definitions

- `linearGrowthInf`, `linearGrowthSup`: respectively, `liminf` and `limsup` of `(u n) / n`.
- `linearGrowthInfTopHom`, `linearGrowthSupBotHom`: the functions `linearGrowthInf`,
  `linearGrowthSup` as homomorphisms preserving finitary `Inf`/`Sup` respectively.

## TODO

Generalize statements from `EReal` to `ENNReal` (or others). This may need additional typeclasses.

Lemma about coercion from `ENNReal` to `EReal`. This needs additional lemmas about
`ENNReal.toEReal`.
-/

@[expose] public section

namespace LinearGrowth

open EReal Filter Function
open scoped Topology

/-! ### Definition -/

section definition

variable {R : Type*} [ConditionallyCompleteLattice R] [Div R] [NatCast R]

/--
Definition of `linearGrowthInf` / `linearGrowthInf` 的定义

English:
definition linearGrowthInf
  signature: (u : Nat -> R)
  body: liminf (fun n => u n / n) atTop

中文:
定义 linearGrowthInf
  签名: (u : 自然数 -> R)
  定义体: liminf (fun n => u n / n) atTop

Depends on / 依赖: liminf
-/
noncomputable def linearGrowthInf (u : Nat -> R) : R := liminf (fun n => u n / n) atTop

/--
Definition of `linearGrowthSup` / `linearGrowthSup` 的定义

English:
definition linearGrowthSup
  signature: (u : Nat -> R)
  body: limsup (fun n => u n / n) atTop

中文:
定义 linearGrowthSup
  签名: (u : 自然数 -> R)
  定义体: limsup (fun n => u n / n) atTop

Depends on / 依赖: limsup
-/
noncomputable def linearGrowthSup (u : Nat -> R) : R := limsup (fun n => u n / n) atTop

end definition

/-! ### Basic properties -/

section basic_properties

variable {R : Type*} [ConditionallyCompleteLattice R] [Div R] [NatCast R] {u v : Nat -> R}

/--
lemma `linearGrowthInf_congr` / 引理 `linearGrowthInf_congr`

English:
lemma linearGrowthInf_congr
  given: (h : u =ᶠ[atTop] v)
  proof: liminf_congr (h.mono fun _ uv => uv ▸ rfl)

中文:
引理 linearGrowthInf_congr
  条件: (h : u =ᶠ[atTop] v)
  证明: liminf_congr (h.mono fun _ uv => uv ▸ rfl)

Depends on / 依赖: h.mono, liminf_congr
-/
lemma linearGrowthInf_congr (h : u =ᶠ[atTop] v) :
    linearGrowthInf u = linearGrowthInf v :=
  liminf_congr (h.mono fun _ uv => uv ▸ rfl)

/--
lemma `linearGrowthSup_congr` / 引理 `linearGrowthSup_congr`

English:
lemma linearGrowthSup_congr
  given: (h : u =ᶠ[atTop] v)
  proof: limsup_congr (h.mono fun _ uv => uv ▸ rfl)

中文:
引理 linearGrowthSup_congr
  条件: (h : u =ᶠ[atTop] v)
  证明: limsup_congr (h.mono fun _ uv => uv ▸ rfl)

Depends on / 依赖: h.mono, limsup_congr
-/
lemma linearGrowthSup_congr (h : u =ᶠ[atTop] v) :
    linearGrowthSup u = linearGrowthSup v :=
  limsup_congr (h.mono fun _ uv => uv ▸ rfl)

/--
lemma `linearGrowthInf_le_linearGrowthSup` / 引理 `linearGrowthInf_le_linearGrowthSup`

English:
lemma linearGrowthInf_le_linearGrowthSup
  proof: liminf_le_limsup h h'

中文:
引理 linearGrowthInf_le_linearGrowthSup
  证明: liminf_le_limsup h h'

Depends on / 依赖: IsBoundedUnder, isBoundedDefault, liminf_le_limsup, linearGrowthInf, linearGrowthSup
-/
lemma linearGrowthInf_le_linearGrowthSup
    (h : IsBoundedUnder (· <= ·) atTop fun n => u n / n := by isBoundedDefault)
    (h' : IsBoundedUnder (· >= ·) atTop fun n => u n / n := by isBoundedDefault) :
    linearGrowthInf u <= linearGrowthSup u :=
  liminf_le_limsup h h'

end basic_properties

section basic_properties

variable {u v : Nat -> EReal} {a b : EReal}

/--
lemma `linearGrowthInf_eventually_monotone` / 引理 `linearGrowthInf_eventually_monotone`

English:
lemma linearGrowthInf_eventually_monotone
  given: (h : u <=ᶠ[atTop] v)
  proof: liminf_le_liminf (h.mono fun n u_v => EReal.monotone_div_right_of_nonneg n.cast_nonneg' u_v)

中文:
引理 linearGrowthInf_eventually_monotone
  条件: (h : u <=ᶠ[atTop] v)
  证明: liminf_le_liminf (h.mono fun n u_v => EReal.monotone_div_right_of_nonneg n.cast_nonneg' u_v)

Depends on / 依赖: EReal.monotone_div_right_of_nonneg, cast_nonneg, h.mono, liminf_le_liminf, monotone_div_right_of_nonneg, n.cast_nonneg
-/
lemma linearGrowthInf_eventually_monotone (h : u <=ᶠ[atTop] v) :
    linearGrowthInf u <= linearGrowthInf v :=
  liminf_le_liminf (h.mono fun n u_v => EReal.monotone_div_right_of_nonneg n.cast_nonneg' u_v)

/--
lemma `linearGrowthInf_monotone` / 引理 `linearGrowthInf_monotone`

English:
lemma linearGrowthInf_monotone
  given: (h : u <= v)
  statement: linearGrowthInf u <= linearGrowthInf v
  proof: linearGrowthInf_eventually_monotone (Eventually.of_forall h)

中文:
引理 linearGrowthInf_monotone
  条件: (h : u <= v)
  结论: linearGrowthInf u <= linearGrowthInf v
  证明: linearGrowthInf_eventually_monotone (Eventually.of_forall h)

Depends on / 依赖: Eventually, Eventually.of_forall, linearGrowthInf_eventually_monotone, of_forall
-/
lemma linearGrowthInf_monotone (h : u <= v) : linearGrowthInf u <= linearGrowthInf v :=
  linearGrowthInf_eventually_monotone (Eventually.of_forall h)

/--
lemma `linearGrowthSup_eventually_monotone` / 引理 `linearGrowthSup_eventually_monotone`

English:
lemma linearGrowthSup_eventually_monotone
  given: (h : u <=ᶠ[atTop] v)
  proof: limsup_le_limsup (h.mono fun n u_v => monotone_div_right_of_nonneg n.cast_nonneg' u_v)

中文:
引理 linearGrowthSup_eventually_monotone
  条件: (h : u <=ᶠ[atTop] v)
  证明: limsup_le_limsup (h.mono fun n u_v => monotone_div_right_of_nonneg n.cast_nonneg' u_v)

Depends on / 依赖: cast_nonneg, h.mono, limsup_le_limsup, monotone_div_right_of_nonneg, n.cast_nonneg
-/
lemma linearGrowthSup_eventually_monotone (h : u <=ᶠ[atTop] v) :
    linearGrowthSup u <= linearGrowthSup v :=
  limsup_le_limsup (h.mono fun n u_v => monotone_div_right_of_nonneg n.cast_nonneg' u_v)

/--
lemma `linearGrowthSup_monotone` / 引理 `linearGrowthSup_monotone`

English:
lemma linearGrowthSup_monotone
  given: (h : u <= v)
  statement: linearGrowthSup u <= linearGrowthSup v
  proof: linearGrowthSup_eventually_monotone (Eventually.of_forall h)

中文:
引理 linearGrowthSup_monotone
  条件: (h : u <= v)
  结论: linearGrowthSup u <= linearGrowthSup v
  证明: linearGrowthSup_eventually_monotone (Eventually.of_forall h)

Depends on / 依赖: Eventually, Eventually.of_forall, linearGrowthSup_eventually_monotone, of_forall
-/
lemma linearGrowthSup_monotone (h : u <= v) : linearGrowthSup u <= linearGrowthSup v :=
  linearGrowthSup_eventually_monotone (Eventually.of_forall h)

/--
lemma `linearGrowthInf_le_linearGrowthSup_of_frequently_le` / 引理 `linearGrowthInf_le_linearGrowthSup_of_frequently_le`

English:
lemma linearGrowthInf_le_linearGrowthSup_of_frequently_le
  given: (h : existsᶠ n in atTop, u n <= v n)
  proof: (liminf_le_limsup_of_frequently_le) h.mono fun n u_v => by gcongr

中文:
引理 linearGrowthInf_le_linearGrowthSup_of_frequently_le
  条件: (h : 存在ᶠ n in atTop, u n <= v n)
  证明: (liminf_le_limsup_of_frequently_le) h.mono fun n u_v => by gcongr

Depends on / 依赖: h.mono, liminf_le_limsup_of_frequently_le
-/
lemma linearGrowthInf_le_linearGrowthSup_of_frequently_le (h : existsᶠ n in atTop, u n <= v n) :
    linearGrowthInf u <= linearGrowthSup v :=
(liminf_le_limsup_of_frequently_le) h.mono fun n u_v => by gcongr

/--
lemma `linearGrowthInf_le_iff` / 引理 `linearGrowthInf_le_iff`

English:
lemma linearGrowthInf_le_iff
  proof: by
  rw [linearGrowthInf]; rw [liminf_le_iff']
  refine forall₂_congr fun b _ => frequently_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n)]; rw [mul_comm _ b]

中文:
引理 linearGrowthInf_le_iff
  证明: by
  rw [linearGrowthInf]; rw [liminf_le_iff']
  refine forall₂_congr fun b _ => frequently_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n)]; rw [mul_comm _ b]

Depends on / 依赖: div_le_iff_le_mul, eventually_atTop, frequently_congr, liminf_le_iff, linearGrowthInf, mul_comm, natCast_ne_top
-/
lemma linearGrowthInf_le_iff :
    linearGrowthInf u <= a ↔ forall b > a, existsᶠ n : Nat in atTop, u n <= b * n := by
  rw [linearGrowthInf]; rw [liminf_le_iff']
  refine forall₂_congr fun b _ => frequently_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n)]; rw [mul_comm _ b]

/--
lemma `le_linearGrowthInf_iff` / 引理 `le_linearGrowthInf_iff`

English:
lemma le_linearGrowthInf_iff
  proof: by
  rw [linearGrowthInf]; rw [le_liminf_iff']
  refine forall₂_congr fun b _ => eventually_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n)]

中文:
引理 le_linearGrowthInf_iff
  证明: by
  rw [linearGrowthInf]; rw [le_liminf_iff']
  refine forall₂_congr fun b _ => eventually_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n)]

Depends on / 依赖: eventually_atTop, eventually_congr, le_div_iff_mul_le, le_liminf_iff, linearGrowthInf, natCast_ne_top, nth_rw
-/
lemma le_linearGrowthInf_iff :
    a <= linearGrowthInf u ↔ forall b < a, forallᶠ n : Nat in atTop, b * n <= u n := by
  rw [linearGrowthInf]; rw [le_liminf_iff']
  refine forall₂_congr fun b _ => eventually_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n)]

/--
lemma `linearGrowthSup_le_iff` / 引理 `linearGrowthSup_le_iff`

English:
lemma linearGrowthSup_le_iff
  proof: by
  rw [linearGrowthSup]; rw [limsup_le_iff']
  refine forall₂_congr fun b _ => eventually_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n)]; rw [mul_comm _ b]

中文:
引理 linearGrowthSup_le_iff
  证明: by
  rw [linearGrowthSup]; rw [limsup_le_iff']
  refine forall₂_congr fun b _ => eventually_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n)]; rw [mul_comm _ b]

Depends on / 依赖: div_le_iff_le_mul, eventually_atTop, eventually_congr, limsup_le_iff, linearGrowthSup, mul_comm, natCast_ne_top
-/
lemma linearGrowthSup_le_iff :
    linearGrowthSup u <= a ↔ forall b > a, forallᶠ n : Nat in atTop, u n <= b * n := by
  rw [linearGrowthSup]; rw [limsup_le_iff']
  refine forall₂_congr fun b _ => eventually_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n)]; rw [mul_comm _ b]

/--
lemma `le_linearGrowthSup_iff` / 引理 `le_linearGrowthSup_iff`

English:
lemma le_linearGrowthSup_iff
  proof: by
  rw [linearGrowthSup]; rw [le_limsup_iff']
  refine forall₂_congr fun b _ => frequently_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n)]

中文:
引理 le_linearGrowthSup_iff
  证明: by
  rw [linearGrowthSup]; rw [le_limsup_iff']
  refine forall₂_congr fun b _ => frequently_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n)]

Depends on / 依赖: eventually_atTop, frequently_congr, le_div_iff_mul_le, le_limsup_iff, linearGrowthSup, natCast_ne_top, nth_rw
-/
lemma le_linearGrowthSup_iff :
    a <= linearGrowthSup u ↔ forall b < a, existsᶠ n : Nat in atTop, b * n <= u n := by
  rw [linearGrowthSup]; rw [le_limsup_iff']
  refine forall₂_congr fun b _ => frequently_congr (eventually_atTop.2 ⟨1, fun n _ => ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n)]

/--
lemma `frequently_le_mul` / 引理 `frequently_le_mul`

English:
lemma frequently_le_mul
  given: (h : linearGrowthInf u < a)
  proof: linearGrowthInf_le_iff.1 (le_refl (linearGrowthInf u)) a h

中文:
引理 frequently_le_mul
  条件: (h : linearGrowthInf u < a)
  证明: linearGrowthInf_le_iff.1 (le_refl (linearGrowthInf u)) a h

Depends on / 依赖: le_refl, linearGrowthInf, linearGrowthInf_le_iff
-/
lemma frequently_le_mul (h : linearGrowthInf u < a) :
    existsᶠ n : Nat in atTop, u n <= a * n :=
  linearGrowthInf_le_iff.1 (le_refl (linearGrowthInf u)) a h

/--
lemma `eventually_mul_le` / 引理 `eventually_mul_le`

English:
lemma eventually_mul_le
  given: (h : a < linearGrowthInf u)
  proof: le_linearGrowthInf_iff.1 (le_refl (linearGrowthInf u)) a h

中文:
引理 eventually_mul_le
  条件: (h : a < linearGrowthInf u)
  证明: le_linearGrowthInf_iff.1 (le_refl (linearGrowthInf u)) a h

Depends on / 依赖: le_linearGrowthInf_iff, le_refl, linearGrowthInf
-/
lemma eventually_mul_le (h : a < linearGrowthInf u) :
    forallᶠ n : Nat in atTop, a * n <= u n :=
  le_linearGrowthInf_iff.1 (le_refl (linearGrowthInf u)) a h

/--
lemma `eventually_le_mul` / 引理 `eventually_le_mul`

English:
lemma eventually_le_mul
  given: (h : linearGrowthSup u < a)
  proof: linearGrowthSup_le_iff.1 (le_refl (linearGrowthSup u)) a h

中文:
引理 eventually_le_mul
  条件: (h : linearGrowthSup u < a)
  证明: linearGrowthSup_le_iff.1 (le_refl (linearGrowthSup u)) a h

Depends on / 依赖: le_refl, linearGrowthSup, linearGrowthSup_le_iff
-/
lemma eventually_le_mul (h : linearGrowthSup u < a) :
    forallᶠ n : Nat in atTop, u n <= a * n :=
  linearGrowthSup_le_iff.1 (le_refl (linearGrowthSup u)) a h

/--
lemma `frequently_mul_le` / 引理 `frequently_mul_le`

English:
lemma frequently_mul_le
  given: (h : a < linearGrowthSup u)
  proof: le_linearGrowthSup_iff.1 (le_refl (linearGrowthSup u)) a h

中文:
引理 frequently_mul_le
  条件: (h : a < linearGrowthSup u)
  证明: le_linearGrowthSup_iff.1 (le_refl (linearGrowthSup u)) a h

Depends on / 依赖: le_linearGrowthSup_iff, le_refl, linearGrowthSup
-/
lemma frequently_mul_le (h : a < linearGrowthSup u) :
    existsᶠ n : Nat in atTop, a * n <= u n :=
  le_linearGrowthSup_iff.1 (le_refl (linearGrowthSup u)) a h

/--
lemma `_root_.Frequently.linearGrowthInf_le` / 引理 `_root_.Frequently.linearGrowthInf_le`

English:
lemma _root_.Frequently.linearGrowthInf_le
  given: (h : existsᶠ n : Nat in atTop, u n <= a * n)
  proof: linearGrowthInf_le_iff.2 fun c c_u => h.mono fun n hn => hn.trans by gcongr

中文:
引理 _root_.Frequently.linearGrowthInf_le
  条件: (h : 存在ᶠ n : 自然数 in atTop, u n <= a * n)
  证明: linearGrowthInf_le_iff.2 fun c c_u => h.mono fun n hn => hn.trans by gcongr

Depends on / 依赖: h.mono, hn.trans, linearGrowthInf_le_iff
-/
lemma _root_.Frequently.linearGrowthInf_le (h : existsᶠ n : Nat in atTop, u n <= a * n) :
    linearGrowthInf u <= a :=
linearGrowthInf_le_iff.2 fun c c_u => h.mono fun n hn => hn.trans by gcongr

/--
lemma `_root_.Eventually.le_linearGrowthInf` / 引理 `_root_.Eventually.le_linearGrowthInf`

English:
lemma _root_.Eventually.le_linearGrowthInf
  given: (h : forallᶠ n : Nat in atTop, a * n <= u n)
  proof: le_linearGrowthInf_iff.2 fun c c_u => h.mono fun n hn => hn.trans' by gcongr

中文:
引理 _root_.Eventually.le_linearGrowthInf
  条件: (h : 对任意ᶠ n : 自然数 in atTop, a * n <= u n)
  证明: le_linearGrowthInf_iff.2 fun c c_u => h.mono fun n hn => hn.trans' by gcongr

Depends on / 依赖: h.mono, hn.trans, le_linearGrowthInf_iff
-/
lemma _root_.Eventually.le_linearGrowthInf (h : forallᶠ n : Nat in atTop, a * n <= u n) :
    a <= linearGrowthInf u :=
le_linearGrowthInf_iff.2 fun c c_u => h.mono fun n hn => hn.trans' by gcongr

/--
lemma `_root_.Eventually.linearGrowthSup_le` / 引理 `_root_.Eventually.linearGrowthSup_le`

English:
lemma _root_.Eventually.linearGrowthSup_le
  given: (h : forallᶠ n : Nat in atTop, u n <= a * n)
  proof: linearGrowthSup_le_iff.2 fun c c_u => h.mono fun n hn => hn.trans by gcongr

中文:
引理 _root_.Eventually.linearGrowthSup_le
  条件: (h : 对任意ᶠ n : 自然数 in atTop, u n <= a * n)
  证明: linearGrowthSup_le_iff.2 fun c c_u => h.mono fun n hn => hn.trans by gcongr

Depends on / 依赖: h.mono, hn.trans, linearGrowthSup_le_iff
-/
lemma _root_.Eventually.linearGrowthSup_le (h : forallᶠ n : Nat in atTop, u n <= a * n) :
    linearGrowthSup u <= a :=
linearGrowthSup_le_iff.2 fun c c_u => h.mono fun n hn => hn.trans by gcongr

/--
lemma `_root_.Frequently.le_linearGrowthSup` / 引理 `_root_.Frequently.le_linearGrowthSup`

English:
lemma _root_.Frequently.le_linearGrowthSup
  given: (h : existsᶠ n : Nat in atTop, a * n <= u n)
  proof: le_linearGrowthSup_iff.2 fun c c_u => h.mono fun n hn => hn.trans' by gcongr

中文:
引理 _root_.Frequently.le_linearGrowthSup
  条件: (h : 存在ᶠ n : 自然数 in atTop, a * n <= u n)
  证明: le_linearGrowthSup_iff.2 fun c c_u => h.mono fun n hn => hn.trans' by gcongr

Depends on / 依赖: h.mono, hn.trans, le_linearGrowthSup_iff
-/
lemma _root_.Frequently.le_linearGrowthSup (h : existsᶠ n : Nat in atTop, a * n <= u n) :
    a <= linearGrowthSup u :=
le_linearGrowthSup_iff.2 fun c c_u => h.mono fun n hn => hn.trans' by gcongr


/--
lemma `linearGrowthSup_bot` / 引理 `linearGrowthSup_bot`

English:
lemma linearGrowthSup_bot
  statement: linearGrowthSup (⊥ : Nat -> EReal) = (⊥ : EReal)
  proof: by
  nth_rw 2 [← limsup_const (f := atTop (α := Nat)) ⊥]
refine limsup_congr (eventually_gt_atTop 0).mono fun n n_pos => ?_
  exact bot_div_of_pos_ne_top (by positivity) (natCast_ne_top n)

中文:
引理 linearGrowthSup_bot
  结论: linearGrowthSup (⊥ : 自然数 -> E实数) = (⊥ : E实数)
  证明: by
  nth_rw 2 [← limsup_const (f := atTop (α := Nat)) ⊥]
refine limsup_congr (eventually_gt_atTop 0).mono fun n n_pos => ?_
  exact bot_div_of_pos_ne_top (by positivity) (natCast_ne_top n)

Depends on / 依赖: bot_div_of_pos_ne_top, eventually_gt_atTop, limsup_congr, limsup_const, n_pos, natCast_ne_top, nth_rw
-/
lemma linearGrowthSup_bot : linearGrowthSup (⊥ : Nat -> EReal) = (⊥ : EReal) := by
  nth_rw 2 [← limsup_const (f := atTop (α := Nat)) ⊥]
refine limsup_congr (eventually_gt_atTop 0).mono fun n n_pos => ?_
  exact bot_div_of_pos_ne_top (by positivity) (natCast_ne_top n)

/--
lemma `linearGrowthInf_bot` / 引理 `linearGrowthInf_bot`

English:
lemma linearGrowthInf_bot
  statement: linearGrowthInf (⊥ : Nat -> EReal) = (⊥ : EReal)
  proof: by
  apply le_bot_iff.1
  rw [← linearGrowthSup_bot]
  exact linearGrowthInf_le_linearGrowthSup

中文:
引理 linearGrowthInf_bot
  结论: linearGrowthInf (⊥ : 自然数 -> E实数) = (⊥ : E实数)
  证明: by
  apply le_bot_iff.1
  rw [← linearGrowthSup_bot]
  exact linearGrowthInf_le_linearGrowthSup

Depends on / 依赖: le_bot_iff, linearGrowthInf_le_linearGrowthSup, linearGrowthSup_bot
-/
lemma linearGrowthInf_bot : linearGrowthInf (⊥ : Nat -> EReal) = (⊥ : EReal) := by
  apply le_bot_iff.1
  rw [← linearGrowthSup_bot]
  exact linearGrowthInf_le_linearGrowthSup

/--
lemma `linearGrowthInf_top` / 引理 `linearGrowthInf_top`

English:
lemma linearGrowthInf_top
  statement: linearGrowthInf ⊤ = (⊤ : EReal)
  proof: by
  nth_rw 2 [← liminf_const (f := atTop (α := Nat)) ⊤]
  refine liminf_congr (eventually_atTop.2 ?_)
  exact ⟨1, fun n n_pos => top_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)⟩

中文:
引理 linearGrowthInf_top
  结论: linearGrowthInf ⊤ = (⊤ : E实数)
  证明: by
  nth_rw 2 [← liminf_const (f := atTop (α := Nat)) ⊤]
  refine liminf_congr (eventually_atTop.2 ?_)
  exact ⟨1, fun n n_pos => top_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)⟩

Depends on / 依赖: Nat.cast_pos, cast_pos, eventually_atTop, liminf_congr, liminf_const, n_pos, natCast_ne_top, nth_rw, top_div_of_pos_ne_top
-/
lemma linearGrowthInf_top : linearGrowthInf ⊤ = (⊤ : EReal) := by
  nth_rw 2 [← liminf_const (f := atTop (α := Nat)) ⊤]
  refine liminf_congr (eventually_atTop.2 ?_)
  exact ⟨1, fun n n_pos => top_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)⟩

/--
lemma `linearGrowthSup_top` / 引理 `linearGrowthSup_top`

English:
lemma linearGrowthSup_top
  statement: linearGrowthSup (⊤ : Nat -> EReal) = (⊤ : EReal)
  proof: by
  apply top_le_iff.1
  rw [← linearGrowthInf_top]
  exact linearGrowthInf_le_linearGrowthSup

中文:
引理 linearGrowthSup_top
  结论: linearGrowthSup (⊤ : 自然数 -> E实数) = (⊤ : E实数)
  证明: by
  apply top_le_iff.1
  rw [← linearGrowthInf_top]
  exact linearGrowthInf_le_linearGrowthSup

Depends on / 依赖: linearGrowthInf_le_linearGrowthSup, linearGrowthInf_top, top_le_iff
-/
lemma linearGrowthSup_top : linearGrowthSup (⊤ : Nat -> EReal) = (⊤ : EReal) := by
  apply top_le_iff.1
  rw [← linearGrowthInf_top]
  exact linearGrowthInf_le_linearGrowthSup

/--
lemma `linearGrowthInf_const` / 引理 `linearGrowthInf_const`

English:
lemma linearGrowthInf_const
  given: (h : b != ⊥) (h' : b != ⊤)
  statement: linearGrowthInf (fun _ => b) = 0
  proof: (tendsto_const_div_atTop_nhds_zero_nat h h').liminf_eq

中文:
引理 linearGrowthInf_const
  条件: (h : b != ⊥) (h' : b != ⊤)
  结论: linearGrowthInf (fun _ => b) = 0
  证明: (tendsto_const_div_atTop_nhds_zero_nat h h').liminf_eq

Depends on / 依赖: liminf_eq, tendsto_const_div_atTop_nhds_zero_nat
-/
lemma linearGrowthInf_const (h : b != ⊥) (h' : b != ⊤) : linearGrowthInf (fun _ => b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat h h').liminf_eq

/--
lemma `linearGrowthSup_const` / 引理 `linearGrowthSup_const`

English:
lemma linearGrowthSup_const
  given: (h : b != ⊥) (h' : b != ⊤)
  statement: linearGrowthSup (fun _ => b) = 0
  proof: (tendsto_const_div_atTop_nhds_zero_nat h h').limsup_eq

中文:
引理 linearGrowthSup_const
  条件: (h : b != ⊥) (h' : b != ⊤)
  结论: linearGrowthSup (fun _ => b) = 0
  证明: (tendsto_const_div_atTop_nhds_zero_nat h h').limsup_eq

Depends on / 依赖: limsup_eq, tendsto_const_div_atTop_nhds_zero_nat
-/
lemma linearGrowthSup_const (h : b != ⊥) (h' : b != ⊤) : linearGrowthSup (fun _ => b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat h h').limsup_eq

/--
lemma `linearGrowthInf_zero` / 引理 `linearGrowthInf_zero`

English:
lemma linearGrowthInf_zero
  statement: linearGrowthInf 0 = (0 : EReal)
  proof: linearGrowthInf_const zero_ne_bot zero_ne_top

中文:
引理 linearGrowthInf_zero
  结论: linearGrowthInf 0 = (0 : E实数)
  证明: linearGrowthInf_const zero_ne_bot zero_ne_top

Depends on / 依赖: linearGrowthInf_const, zero_ne_bot, zero_ne_top
-/
lemma linearGrowthInf_zero : linearGrowthInf 0 = (0 : EReal) :=
  linearGrowthInf_const zero_ne_bot zero_ne_top

/--
lemma `linearGrowthSup_zero` / 引理 `linearGrowthSup_zero`

English:
lemma linearGrowthSup_zero
  statement: linearGrowthSup 0 = (0 : EReal)
  proof: linearGrowthSup_const zero_ne_bot zero_ne_top

中文:
引理 linearGrowthSup_zero
  结论: linearGrowthSup 0 = (0 : E实数)
  证明: linearGrowthSup_const zero_ne_bot zero_ne_top

Depends on / 依赖: linearGrowthSup_const, zero_ne_bot, zero_ne_top
-/
lemma linearGrowthSup_zero : linearGrowthSup 0 = (0 : EReal) :=
  linearGrowthSup_const zero_ne_bot zero_ne_top

/--
lemma `linearGrowthInf_const_mul_self` / 引理 `linearGrowthInf_const_mul_self`

English:
lemma linearGrowthInf_const_mul_self
  statement: linearGrowthInf (fun n => a * n) = a
  proof: le_antisymm (Frequently.linearGrowthInf_le (Frequently.of_forall fun _ => le_refl _))
    (Eventually.le_linearGrowthInf (Eventually.of_forall fun _ => le_refl _))

中文:
引理 linearGrowthInf_const_mul_self
  结论: linearGrowthInf (fun n => a * n) = a
  证明: le_antisymm (Frequently.linearGrowthInf_le (Frequently.of_forall fun _ => le_refl _))
    (Eventually.le_linearGrowthInf (Eventually.of_forall fun _ => le_refl _))

Depends on / 依赖: Eventually, Eventually.le_linearGrowthInf, Eventually.of_forall, Frequently, Frequently.linearGrowthInf_le, Frequently.of_forall, le_antisymm, le_linearGrowthInf, le_refl, linearGrowthInf_le, of_forall
-/
lemma linearGrowthInf_const_mul_self : linearGrowthInf (fun n => a * n) = a :=
  le_antisymm (Frequently.linearGrowthInf_le (Frequently.of_forall fun _ => le_refl _))
    (Eventually.le_linearGrowthInf (Eventually.of_forall fun _ => le_refl _))

/--
lemma `linearGrowthSup_const_mul_self` / 引理 `linearGrowthSup_const_mul_self`

English:
lemma linearGrowthSup_const_mul_self
  statement: linearGrowthSup (fun n => a * n) = a
  proof: le_antisymm (Eventually.linearGrowthSup_le (Eventually.of_forall fun _ => le_refl _))
    (Frequently.le_linearGrowthSup (Frequently.of_forall fun _ => le_refl _))

中文:
引理 linearGrowthSup_const_mul_self
  结论: linearGrowthSup (fun n => a * n) = a
  证明: le_antisymm (Eventually.linearGrowthSup_le (Eventually.of_forall fun _ => le_refl _))
    (Frequently.le_linearGrowthSup (Frequently.of_forall fun _ => le_refl _))

Depends on / 依赖: Eventually, Eventually.linearGrowthSup_le, Eventually.of_forall, Frequently, Frequently.le_linearGrowthSup, Frequently.of_forall, le_antisymm, le_linearGrowthSup, le_refl, linearGrowthSup_le, of_forall
-/
lemma linearGrowthSup_const_mul_self : linearGrowthSup (fun n => a * n) = a :=
  le_antisymm (Eventually.linearGrowthSup_le (Eventually.of_forall fun _ => le_refl _))
    (Frequently.le_linearGrowthSup (Frequently.of_forall fun _ => le_refl _))

/--
lemma `linearGrowthInf_natCast_nonneg` / 引理 `linearGrowthInf_natCast_nonneg`

English:
lemma linearGrowthInf_natCast_nonneg
  given: (v : Nat -> Nat)
  proof: (le_liminf_of_le) (Eventually.of_forall fun n => div_nonneg (v n).cast_nonneg' n.cast_nonneg')

中文:
引理 linearGrowthInf_natCast_nonneg
  条件: (v : 自然数 -> 自然数)
  证明: (le_liminf_of_le) (Eventually.of_forall fun n => div_nonneg (v n).cast_nonneg' n.cast_nonneg')

Depends on / 依赖: Eventually, Eventually.of_forall, cast_nonneg, div_nonneg, le_liminf_of_le, n.cast_nonneg, of_forall
-/
lemma linearGrowthInf_natCast_nonneg (v : Nat -> Nat) :
    0 <= linearGrowthInf fun n => (v n : EReal) :=
  (le_liminf_of_le) (Eventually.of_forall fun n => div_nonneg (v n).cast_nonneg' n.cast_nonneg')

/--
lemma `tendsto_atTop_of_linearGrowthInf_pos` / 引理 `tendsto_atTop_of_linearGrowthInf_pos`

English:
lemma tendsto_atTop_of_linearGrowthInf_pos
  given: (h : 0 < linearGrowthInf u)
  proof: by
  obtain ⟨a, a_0, a_v⟩ := exists_between h
  apply tendsto_nhds_top_mono _ ((le_linearGrowthInf_iff (u := u)).1 (le_refl _) a a_v)
  refine tendsto_nhds_top_iff_real.2 fun M => eventually_atTop.2 ?_
  lift a to Real using ⟨ne_top_of_lt a_v, ne_bot_of_gt a_0⟩
  rw [EReal.coe_pos] at a_0
  obtain ⟨

中文:
引理 tendsto_atTop_of_linearGrowthInf_pos
  条件: (h : 0 < linearGrowthInf u)
  证明: by
  obtain ⟨a, a_0, a_v⟩ := exists_between h
  apply tendsto_nhds_top_mono _ ((le_linearGrowthInf_iff (u := u)).1 (le_refl _) a a_v)
  refine tendsto_nhds_top_iff_real.2 fun M => eventually_atTop.2 ?_
  lift a to Real using ⟨ne_top_of_lt a_v, ne_bot_of_gt a_0⟩
  rw [EReal.coe_pos] at a_0
  obtain ⟨

Depends on / 依赖: EReal.coe_lt_coe_iff, EReal.coe_pos, Nat.cast_lt, cast_lt, coe_coe_eq_natCast, coe_lt_coe_iff, coe_mul, coe_pos, eventually_atTop, exists_between, exists_nat_ge, hn.trans_lt, le_linearGrowthInf_iff, le_refl, mul_comm, ne_bot_of_gt, ne_top_of_lt, tendsto_nhds_top_iff_real, tendsto_nhds_top_mono, trans_lt
-/
lemma tendsto_atTop_of_linearGrowthInf_pos (h : 0 < linearGrowthInf u) :
    Tendsto u atTop (𝓝 ⊤) := by
  obtain ⟨a, a_0, a_v⟩ := exists_between h
  apply tendsto_nhds_top_mono _ ((le_linearGrowthInf_iff (u := u)).1 (le_refl _) a a_v)
  refine tendsto_nhds_top_iff_real.2 fun M => eventually_atTop.2 ?_
  lift a to Real using ⟨ne_top_of_lt a_v, ne_bot_of_gt a_0⟩
  rw [EReal.coe_pos] at a_0
  obtain ⟨n, hn⟩ := exists_nat_ge (M / a)
  refine ⟨n + 1, fun k k_n => ?_⟩
  rw [← coe_coe_eq_natCast]; rw [← coe_mul]; rw [EReal.coe_lt_coe_iff]; rw [mul_comm]
  exact (div_lt_iff₀ a_0).1 (hn.trans_lt (Nat.cast_lt.2 k_n))


/--
lemma `le_linearGrowthInf_add` / 引理 `le_linearGrowthInf_add`

English:
lemma le_linearGrowthInf_add
  proof: by
  refine le_liminf_add.trans_eq (liminf_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [← add_div_of_nonneg_right n.cast_nonneg']

中文:
引理 le_linearGrowthInf_add
  证明: by
  refine le_liminf_add.trans_eq (liminf_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [← add_div_of_nonneg_right n.cast_nonneg']

Depends on / 依赖: Eventually, Eventually.of_forall, Pi.add_apply, add_apply, add_div_of_nonneg_right, cast_nonneg, le_liminf_add, le_liminf_add.trans_eq, liminf_congr, n.cast_nonneg, of_forall, trans_eq
-/
lemma le_linearGrowthInf_add :
    linearGrowthInf u + linearGrowthInf v <= linearGrowthInf (u + v) := by
  refine le_liminf_add.trans_eq (liminf_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [← add_div_of_nonneg_right n.cast_nonneg']

/--
lemma `linearGrowthInf_add_le` / 引理 `linearGrowthInf_add_le`

English:
lemma linearGrowthInf_add_le
  statement: (h : linearGrowthSup u != ⊥ ∨ linearGrowthInf v != ⊤)
  proof: by
  refine (liminf_add_le h h').trans_eq' (liminf_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [← add_div_of_nonneg_right n.cast_nonneg']

中文:
引理 linearGrowthInf_add_le
  结论: (h : linearGrowthSup u != ⊥ ∨ linearGrowthInf v != ⊤)
  证明: by
  refine (liminf_add_le h h').trans_eq' (liminf_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [← add_div_of_nonneg_right n.cast_nonneg']

Depends on / 依赖: Eventually, Eventually.of_forall, Pi.add_apply, add_apply, add_div_of_nonneg_right, cast_nonneg, liminf_add_le, liminf_congr, n.cast_nonneg, of_forall, trans_eq
-/
lemma linearGrowthInf_add_le (h : linearGrowthSup u != ⊥ ∨ linearGrowthInf v != ⊤)
    (h' : linearGrowthSup u != ⊤ ∨ linearGrowthInf v != ⊥) :
    linearGrowthInf (u + v) <= linearGrowthSup u + linearGrowthInf v := by
  refine (liminf_add_le h h').trans_eq' (liminf_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [← add_div_of_nonneg_right n.cast_nonneg']

/--
lemma `linearGrowthInf_add_le'` / 引理 `linearGrowthInf_add_le'`

English:
lemma linearGrowthInf_add_le'
  statement: (h : linearGrowthInf u != ⊥ ∨ linearGrowthSup v != ⊤)
  proof: by
  rw [add_comm u v]; rw [add_comm (linearGrowthInf u) (linearGrowthSup v)]
  exact linearGrowthInf_add_le h'.symm h.symm

中文:
引理 linearGrowthInf_add_le'
  结论: (h : linearGrowthInf u != ⊥ ∨ linearGrowthSup v != ⊤)
  证明: by
  rw [add_comm u v]; rw [add_comm (linearGrowthInf u) (linearGrowthSup v)]
  exact linearGrowthInf_add_le h'.symm h.symm

Depends on / 依赖: add_comm, h.symm, linearGrowthInf, linearGrowthInf_add_le, linearGrowthSup
-/
lemma linearGrowthInf_add_le' (h : linearGrowthInf u != ⊥ ∨ linearGrowthSup v != ⊤)
    (h' : linearGrowthInf u != ⊤ ∨ linearGrowthSup v != ⊥) :
    linearGrowthInf (u + v) <= linearGrowthInf u + linearGrowthSup v := by
  rw [add_comm u v]; rw [add_comm (linearGrowthInf u) (linearGrowthSup v)]
  exact linearGrowthInf_add_le h'.symm h.symm

/--
lemma `le_linearGrowthSup_add` / 引理 `le_linearGrowthSup_add`

English:
lemma le_linearGrowthSup_add
  statement: linearGrowthSup u + linearGrowthInf v <= linearGrowthSup (u + v)
  proof: by
  refine le_limsup_add.trans_eq (limsup_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [add_div_of_nonneg_right n.cast_nonneg']

中文:
引理 le_linearGrowthSup_add
  结论: linearGrowthSup u + linearGrowthInf v <= linearGrowthSup (u + v)
  证明: by
  refine le_limsup_add.trans_eq (limsup_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [add_div_of_nonneg_right n.cast_nonneg']

Depends on / 依赖: Eventually, Eventually.of_forall, Pi.add_apply, add_apply, add_div_of_nonneg_right, cast_nonneg, le_limsup_add, le_limsup_add.trans_eq, limsup_congr, n.cast_nonneg, of_forall, trans_eq
-/
lemma le_linearGrowthSup_add : linearGrowthSup u + linearGrowthInf v <= linearGrowthSup (u + v) := by
  refine le_limsup_add.trans_eq (limsup_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [add_div_of_nonneg_right n.cast_nonneg']

/--
lemma `le_linearGrowthSup_add'` / 引理 `le_linearGrowthSup_add'`

English:
lemma le_linearGrowthSup_add'
  proof: by
  rw [add_comm u v]; rw [add_comm (linearGrowthInf u) (linearGrowthSup v)]
  exact le_linearGrowthSup_add

中文:
引理 le_linearGrowthSup_add'
  证明: by
  rw [add_comm u v]; rw [add_comm (linearGrowthInf u) (linearGrowthSup v)]
  exact le_linearGrowthSup_add

Depends on / 依赖: add_comm, le_linearGrowthSup_add, linearGrowthInf, linearGrowthSup
-/
lemma le_linearGrowthSup_add' :
    linearGrowthInf u + linearGrowthSup v <= linearGrowthSup (u + v) := by
  rw [add_comm u v]; rw [add_comm (linearGrowthInf u) (linearGrowthSup v)]
  exact le_linearGrowthSup_add

/--
lemma `linearGrowthSup_add_le` / 引理 `linearGrowthSup_add_le`

English:
lemma linearGrowthSup_add_le
  statement: (h : linearGrowthSup u != ⊥ ∨ linearGrowthSup v != ⊤)
  proof: by
  refine (limsup_add_le h h').trans_eq' (limsup_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [add_div_of_nonneg_right n.cast_nonneg']

中文:
引理 linearGrowthSup_add_le
  结论: (h : linearGrowthSup u != ⊥ ∨ linearGrowthSup v != ⊤)
  证明: by
  refine (limsup_add_le h h').trans_eq' (limsup_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [add_div_of_nonneg_right n.cast_nonneg']

Depends on / 依赖: Eventually, Eventually.of_forall, Pi.add_apply, add_apply, add_div_of_nonneg_right, cast_nonneg, limsup_add_le, limsup_congr, n.cast_nonneg, of_forall, trans_eq
-/
lemma linearGrowthSup_add_le (h : linearGrowthSup u != ⊥ ∨ linearGrowthSup v != ⊤)
    (h' : linearGrowthSup u != ⊤ ∨ linearGrowthSup v != ⊥) :
    linearGrowthSup (u + v) <= linearGrowthSup u + linearGrowthSup v := by
  refine (limsup_add_le h h').trans_eq' (limsup_congr (Eventually.of_forall fun n => ?_))
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [add_div_of_nonneg_right n.cast_nonneg']

/--
lemma `linearGrowthInf_neg` / 引理 `linearGrowthInf_neg`

English:
lemma linearGrowthInf_neg
  statement: linearGrowthInf (-u) = - linearGrowthSup u
  proof: by
  rw [linearGrowthSup]; rw [← liminf_neg]
  refine liminf_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.neg_apply]; rw [Pi.neg_apply]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← neg_mul]

中文:
引理 linearGrowthInf_neg
  结论: linearGrowthInf (-u) = - linearGrowthSup u
  证明: by
  rw [linearGrowthSup]; rw [← liminf_neg]
  refine liminf_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.neg_apply]; rw [Pi.neg_apply]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← neg_mul]

Depends on / 依赖: Eventually, Eventually.of_forall, Pi.neg_apply, div_eq_mul_inv, liminf_congr, liminf_neg, linearGrowthSup, neg_apply, neg_mul, of_forall
-/
lemma linearGrowthInf_neg : linearGrowthInf (-u) = - linearGrowthSup u := by
  rw [linearGrowthSup]; rw [← liminf_neg]
  refine liminf_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.neg_apply]; rw [Pi.neg_apply]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← neg_mul]

/--
lemma `linearGrowthSup_inv` / 引理 `linearGrowthSup_inv`

English:
lemma linearGrowthSup_inv
  statement: linearGrowthSup (-u) = - linearGrowthInf u
  proof: by
  rw [linearGrowthInf]; rw [← limsup_neg]
  refine limsup_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.neg_apply]; rw [Pi.neg_apply]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← neg_mul]

中文:
引理 linearGrowthSup_inv
  结论: linearGrowthSup (-u) = - linearGrowthInf u
  证明: by
  rw [linearGrowthInf]; rw [← limsup_neg]
  refine limsup_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.neg_apply]; rw [Pi.neg_apply]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← neg_mul]

Depends on / 依赖: Eventually, Eventually.of_forall, Pi.neg_apply, div_eq_mul_inv, limsup_congr, limsup_neg, linearGrowthInf, neg_apply, neg_mul, of_forall
-/
lemma linearGrowthSup_inv : linearGrowthSup (-u) = - linearGrowthInf u := by
  rw [linearGrowthInf]; rw [← limsup_neg]
  refine limsup_congr (Eventually.of_forall fun n => ?_)
  rw [Pi.neg_apply]; rw [Pi.neg_apply]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← neg_mul]


/--
lemma `linearGrowthInf_le_of_eventually_le` / 引理 `linearGrowthInf_le_of_eventually_le`

English:
lemma linearGrowthInf_le_of_eventually_le
  given: (hb : b != ⊤) (h : forallᶠ n in atTop, u n <= v n + b)
  proof: by
  apply (linearGrowthInf_eventually_monotone h).trans
  rcases eq_bot_or_bot_lt b with rfl | b_bot
  · simp only [add_bot, ← Pi.bot_def, linearGrowthInf_bot, bot_le]
  · apply (linearGrowthInf_add_le' _ _).trans_eq <;> rw [linearGrowthSup_const b_bot.ne' hb]
    · exact add_zero (linearGrowthInf 

中文:
引理 linearGrowthInf_le_of_eventually_le
  条件: (hb : b != ⊤) (h : 对任意ᶠ n in atTop, u n <= v n + b)
  证明: by
  apply (linearGrowthInf_eventually_monotone h).trans
  rcases eq_bot_or_bot_lt b with rfl | b_bot
  · simp only [add_bot, ← Pi.bot_def, linearGrowthInf_bot, bot_le]
  · apply (linearGrowthInf_add_le' _ _).trans_eq <;> rw [linearGrowthSup_const b_bot.ne' hb]
    · exact add_zero (linearGrowthInf 

Depends on / 依赖: EReal.zero_ne_bot, EReal.zero_ne_top, Or.inr, Pi.bot_def, add_bot, add_zero, b_bot, b_bot.ne, bot_def, bot_le, eq_bot_or_bot_lt, linearGrowthInf, linearGrowthInf_add_le, linearGrowthInf_bot, linearGrowthInf_eventually_monotone, linearGrowthSup_const, trans_eq, zero_ne_bot, zero_ne_top
-/
lemma linearGrowthInf_le_of_eventually_le (hb : b != ⊤) (h : forallᶠ n in atTop, u n <= v n + b) :
    linearGrowthInf u <= linearGrowthInf v := by
  apply (linearGrowthInf_eventually_monotone h).trans
  rcases eq_bot_or_bot_lt b with rfl | b_bot
  · simp only [add_bot, ← Pi.bot_def, linearGrowthInf_bot, bot_le]
  · apply (linearGrowthInf_add_le' _ _).trans_eq <;> rw [linearGrowthSup_const b_bot.ne' hb]
    · exact add_zero (linearGrowthInf v)
    · exact Or.inr EReal.zero_ne_top
    · exact Or.inr EReal.zero_ne_bot

/--
lemma `linearGrowthSup_le_of_eventually_le` / 引理 `linearGrowthSup_le_of_eventually_le`

English:
lemma linearGrowthSup_le_of_eventually_le
  given: (hb : b != ⊤) (h : forallᶠ n in atTop, u n <= v n + b)
  proof: by
  apply (linearGrowthSup_eventually_monotone h).trans
  rcases eq_bot_or_bot_lt b with rfl | b_bot
  · simp only [add_bot, ← Pi.bot_def, linearGrowthSup_bot, bot_le]
  · apply (linearGrowthSup_add_le _ _).trans_eq <;> rw [linearGrowthSup_const b_bot.ne' hb]
    · exact add_zero (linearGrowthSup v

中文:
引理 linearGrowthSup_le_of_eventually_le
  条件: (hb : b != ⊤) (h : 对任意ᶠ n in atTop, u n <= v n + b)
  证明: by
  apply (linearGrowthSup_eventually_monotone h).trans
  rcases eq_bot_or_bot_lt b with rfl | b_bot
  · simp only [add_bot, ← Pi.bot_def, linearGrowthSup_bot, bot_le]
  · apply (linearGrowthSup_add_le _ _).trans_eq <;> rw [linearGrowthSup_const b_bot.ne' hb]
    · exact add_zero (linearGrowthSup v

Depends on / 依赖: EReal.zero_ne_bot, EReal.zero_ne_top, Or.inr, Pi.bot_def, add_bot, add_zero, b_bot, b_bot.ne, bot_def, bot_le, eq_bot_or_bot_lt, linearGrowthSup, linearGrowthSup_add_le, linearGrowthSup_bot, linearGrowthSup_const, linearGrowthSup_eventually_monotone, trans_eq, zero_ne_bot, zero_ne_top
-/
lemma linearGrowthSup_le_of_eventually_le (hb : b != ⊤) (h : forallᶠ n in atTop, u n <= v n + b) :
    linearGrowthSup u <= linearGrowthSup v := by
  apply (linearGrowthSup_eventually_monotone h).trans
  rcases eq_bot_or_bot_lt b with rfl | b_bot
  · simp only [add_bot, ← Pi.bot_def, linearGrowthSup_bot, bot_le]
  · apply (linearGrowthSup_add_le _ _).trans_eq <;> rw [linearGrowthSup_const b_bot.ne' hb]
    · exact add_zero (linearGrowthSup v)
    · exact Or.inr EReal.zero_ne_top
    · exact Or.inr EReal.zero_ne_bot


/--
lemma `linearGrowthInf_inf` / 引理 `linearGrowthInf_inf`

English:
lemma linearGrowthInf_inf
  proof: by
  rw [linearGrowthInf]; rw [linearGrowthInf]; rw [linearGrowthInf]; rw [← liminf_min]
  refine liminf_congr (Eventually.of_forall fun n => ?_)
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_min

中文:
引理 linearGrowthInf_inf
  证明: by
  rw [linearGrowthInf]; rw [linearGrowthInf]; rw [linearGrowthInf]; rw [← liminf_min]
  refine liminf_congr (Eventually.of_forall fun n => ?_)
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_min

Depends on / 依赖: Eventually, Eventually.of_forall, cast_nonneg, liminf_congr, liminf_min, linearGrowthInf, map_min, monotone_div_right_of_nonneg, n.cast_nonneg, of_forall
-/
lemma linearGrowthInf_inf :
    linearGrowthInf (u ⊓ v) = min (linearGrowthInf u) (linearGrowthInf v) := by
  rw [linearGrowthInf]; rw [linearGrowthInf]; rw [linearGrowthInf]; rw [← liminf_min]
  refine liminf_congr (Eventually.of_forall fun n => ?_)
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_min

/--
Definition of `linearGrowthInfTopHom` / `linearGrowthInfTopHom` 的定义

English:
definition linearGrowthInfTopHom
  signature: : InfTopHom (Nat -> EReal) EReal where
  body: linearGrowthInf
  map_inf' _ _ := linearGrowthInf_inf
  map_top' := linearGrowthInf_top

中文:
定义 linearGrowthInfTopHom
  签名: : InfTopHom (自然数 -> E实数) E实数 where
  定义体: linearGrowthInf
  map_inf' _ _ := linearGrowthInf_inf
  map_top' := linearGrowthInf_top

Depends on / 依赖: linearGrowthInf
-/
noncomputable def linearGrowthInfTopHom : InfTopHom (Nat -> EReal) EReal where
  toFun := linearGrowthInf
  map_inf' _ _ := linearGrowthInf_inf
  map_top' := linearGrowthInf_top

/--
lemma `linearGrowthInf_biInf` / 引理 `linearGrowthInf_biInf`

English:
lemma linearGrowthInf_biInf
  given: {α : Type*} (u : α -> Nat -> EReal) {s : Set α} (hs : s.Finite)
  proof: by
  have := map_finset_inf linearGrowthInfTopHom hs.toFinset u
  simpa only [linearGrowthInfTopHom, InfTopHom.coe_mk, InfHom.coe_mk, Finset.inf_eq_iInf,
    hs.mem_toFinset, comp_apply]

中文:
引理 linearGrowthInf_biInf
  条件: {α : 类型} (u : α -> 自然数 -> E实数) {s : Set α} (hs : s.Finite)
  证明: by
  have := map_finset_inf linearGrowthInfTopHom hs.toFinset u
  simpa only [linearGrowthInfTopHom, InfTopHom.coe_mk, InfHom.coe_mk, Finset.inf_eq_iInf,
    hs.mem_toFinset, comp_apply]

Depends on / 依赖: Finset, Finset.inf_eq_iInf, InfHom, InfHom.coe_mk, InfTopHom, InfTopHom.coe_mk, coe_mk, comp_apply, hs.mem_toFinset, hs.toFinset, inf_eq_iInf, linearGrowthInfTopHom, map_finset_inf, mem_toFinset, toFinset
-/
lemma linearGrowthInf_biInf {α : Type*} (u : α -> Nat -> EReal) {s : Set α} (hs : s.Finite) :
    linearGrowthInf (⨅ x in s, u x) = ⨅ x in s, linearGrowthInf (u x) := by
  have := map_finset_inf linearGrowthInfTopHom hs.toFinset u
  simpa only [linearGrowthInfTopHom, InfTopHom.coe_mk, InfHom.coe_mk, Finset.inf_eq_iInf,
    hs.mem_toFinset, comp_apply]

/--
lemma `linearGrowthInf_iInf` / 引理 `linearGrowthInf_iInf`

English:
lemma linearGrowthInf_iInf
  given: {ι : Type*} [Finite ι] (u : ι -> Nat -> EReal)
  proof: by
  rw [← iInf_univ]; rw [linearGrowthInf_biInf u Set.finite_univ]; rw [iInf_univ]

中文:
引理 linearGrowthInf_iInf
  条件: {ι : 类型} [Finite ι] (u : ι -> 自然数 -> E实数)
  证明: by
  rw [← iInf_univ]; rw [linearGrowthInf_biInf u Set.finite_univ]; rw [iInf_univ]

Depends on / 依赖: Set.finite_univ, finite_univ, iInf_univ, linearGrowthInf_biInf
-/
lemma linearGrowthInf_iInf {ι : Type*} [Finite ι] (u : ι -> Nat -> EReal) :
    linearGrowthInf (⨅ i, u i) = ⨅ i, linearGrowthInf (u i) := by
  rw [← iInf_univ]; rw [linearGrowthInf_biInf u Set.finite_univ]; rw [iInf_univ]

/--
lemma `linearGrowthSup_sup` / 引理 `linearGrowthSup_sup`

English:
lemma linearGrowthSup_sup
  proof: by
  rw [linearGrowthSup]; rw [linearGrowthSup]; rw [linearGrowthSup]; rw [← limsup_max]
  refine limsup_congr (Eventually.of_forall fun n => ?_)
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_max

中文:
引理 linearGrowthSup_sup
  证明: by
  rw [linearGrowthSup]; rw [linearGrowthSup]; rw [linearGrowthSup]; rw [← limsup_max]
  refine limsup_congr (Eventually.of_forall fun n => ?_)
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_max

Depends on / 依赖: Eventually, Eventually.of_forall, cast_nonneg, limsup_congr, limsup_max, linearGrowthSup, map_max, monotone_div_right_of_nonneg, n.cast_nonneg, of_forall
-/
lemma linearGrowthSup_sup :
    linearGrowthSup (u ⊔ v) = max (linearGrowthSup u) (linearGrowthSup v) := by
  rw [linearGrowthSup]; rw [linearGrowthSup]; rw [linearGrowthSup]; rw [← limsup_max]
  refine limsup_congr (Eventually.of_forall fun n => ?_)
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_max

/--
Definition of `linearGrowthSupBotHom` / `linearGrowthSupBotHom` 的定义

English:
definition linearGrowthSupBotHom
  signature: : SupBotHom (Nat -> EReal) EReal where
  body: linearGrowthSup
  map_sup' _ _ := linearGrowthSup_sup
  map_bot' := linearGrowthSup_bot

中文:
定义 linearGrowthSupBotHom
  签名: : SupBotHom (自然数 -> E实数) E实数 where
  定义体: linearGrowthSup
  map_sup' _ _ := linearGrowthSup_sup
  map_bot' := linearGrowthSup_bot

Depends on / 依赖: linearGrowthSup
-/
noncomputable def linearGrowthSupBotHom : SupBotHom (Nat -> EReal) EReal where
  toFun := linearGrowthSup
  map_sup' _ _ := linearGrowthSup_sup
  map_bot' := linearGrowthSup_bot

/--
lemma `linearGrowthSup_biSup` / 引理 `linearGrowthSup_biSup`

English:
lemma linearGrowthSup_biSup
  given: {α : Type*} (u : α -> Nat -> EReal) {s : Set α} (hs : s.Finite)
  proof: by
  have := map_finset_sup linearGrowthSupBotHom hs.toFinset u
  simpa only [linearGrowthSupBotHom, SupBotHom.coe_mk, SupHom.coe_mk, Finset.sup_eq_iSup,
    hs.mem_toFinset, comp_apply]

中文:
引理 linearGrowthSup_biSup
  条件: {α : 类型} (u : α -> 自然数 -> E实数) {s : Set α} (hs : s.Finite)
  证明: by
  have := map_finset_sup linearGrowthSupBotHom hs.toFinset u
  simpa only [linearGrowthSupBotHom, SupBotHom.coe_mk, SupHom.coe_mk, Finset.sup_eq_iSup,
    hs.mem_toFinset, comp_apply]

Depends on / 依赖: Finset, Finset.sup_eq_iSup, SupBotHom, SupBotHom.coe_mk, SupHom, SupHom.coe_mk, coe_mk, comp_apply, hs.mem_toFinset, hs.toFinset, linearGrowthSupBotHom, map_finset_sup, mem_toFinset, sup_eq_iSup, toFinset
-/
lemma linearGrowthSup_biSup {α : Type*} (u : α -> Nat -> EReal) {s : Set α} (hs : s.Finite) :
    linearGrowthSup (⨆ x in s, u x) = ⨆ x in s, linearGrowthSup (u x) := by
  have := map_finset_sup linearGrowthSupBotHom hs.toFinset u
  simpa only [linearGrowthSupBotHom, SupBotHom.coe_mk, SupHom.coe_mk, Finset.sup_eq_iSup,
    hs.mem_toFinset, comp_apply]

/--
lemma `linearGrowthSup_iSup` / 引理 `linearGrowthSup_iSup`

English:
lemma linearGrowthSup_iSup
  given: {ι : Type*} [Finite ι] (u : ι -> Nat -> EReal)
  proof: by
  rw [← iSup_univ]; rw [linearGrowthSup_biSup u Set.finite_univ]; rw [iSup_univ]

中文:
引理 linearGrowthSup_iSup
  条件: {ι : 类型} [Finite ι] (u : ι -> 自然数 -> E实数)
  证明: by
  rw [← iSup_univ]; rw [linearGrowthSup_biSup u Set.finite_univ]; rw [iSup_univ]

Depends on / 依赖: Set.finite_univ, finite_univ, iSup_univ, linearGrowthSup_biSup
-/
lemma linearGrowthSup_iSup {ι : Type*} [Finite ι] (u : ι -> Nat -> EReal) :
    linearGrowthSup (⨆ i, u i) = ⨆ i, linearGrowthSup (u i) := by
  rw [← iSup_univ]; rw [linearGrowthSup_biSup u Set.finite_univ]; rw [iSup_univ]

end basic_properties

/-! ### Composition -/

section composition

variable {u : Nat -> EReal} {v : Nat -> Nat}

/--
lemma `Real.eventually_atTop_exists_int_between` / 引理 `Real.eventually_atTop_exists_int_between`

English:
lemma Real.eventually_atTop_exists_int_between
  given: {a b : Real} (h : a < b)
  proof: by
  refine (eventually_ge_atTop (b - a)⁻¹).mono fun x ab_x => ?_
  rw [inv_le_iff_one_le_mul₀ (sub_pos_of_lt h)]; rw [mul_comm]; rw [sub_mul]; rw [le_sub_iff_add_le'] at ab_x
  exact ⟨_, le_of_add_le_add_right (ab_x.trans (Int.lt_floor_add_one _).le), Int.floor_le _⟩

中文:
引理 Real.eventually_atTop_exists_int_between
  条件: {a b : 实数} (h : a < b)
  证明: by
  refine (eventually_ge_atTop (b - a)⁻¹).mono fun x ab_x => ?_
  rw [inv_le_iff_one_le_mul₀ (sub_pos_of_lt h)]; rw [mul_comm]; rw [sub_mul]; rw [le_sub_iff_add_le'] at ab_x
  exact ⟨_, le_of_add_le_add_right (ab_x.trans (Int.lt_floor_add_one _).le), Int.floor_le _⟩

Depends on / 依赖: Int.floor_le, Int.lt_floor_add_one, ab_x, ab_x.trans, eventually_ge_atTop, floor_le, le_of_add_le_add_right, le_sub_iff_add_le, lt_floor_add_one, mul_comm, sub_mul, sub_pos_of_lt
-/
lemma Real.eventually_atTop_exists_int_between {a b : Real} (h : a < b) :
    forallᶠ x : Real in atTop, exists n : Int, a * x <= n ∧ n <= b * x := by
  refine (eventually_ge_atTop (b - a)⁻¹).mono fun x ab_x => ?_
  rw [inv_le_iff_one_le_mul₀ (sub_pos_of_lt h)]; rw [mul_comm]; rw [sub_mul]; rw [le_sub_iff_add_le'] at ab_x
  exact ⟨_, le_of_add_le_add_right (ab_x.trans (Int.lt_floor_add_one _).le), Int.floor_le _⟩

/--
lemma `Real.eventually_atTop_exists_nat_between` / 引理 `Real.eventually_atTop_exists_nat_between`

English:
lemma Real.eventually_atTop_exists_nat_between
  given: {a b : Real} (h : a < b) (hb : 0 <= b)
  proof: by
  filter_upwards [eventually_ge_atTop 0, Real.eventually_atTop_exists_int_between h]
    with x x_0 ⟨m, m_a, m_b⟩
  refine ⟨m.toNat, m_a.trans (Int.cast_le.2 m.self_le_toNat), ?_⟩
  apply le_of_eq_of_le _ (max_le m_b (mul_nonneg hb x_0))
  exact_mod_cast Int.toNat_eq_max m

中文:
引理 Real.eventually_atTop_exists_nat_between
  条件: {a b : 实数} (h : a < b) (hb : 0 <= b)
  证明: by
  filter_upwards [eventually_ge_atTop 0, Real.eventually_atTop_exists_int_between h]
    with x x_0 ⟨m, m_a, m_b⟩
  refine ⟨m.toNat, m_a.trans (Int.cast_le.2 m.self_le_toNat), ?_⟩
  apply le_of_eq_of_le _ (max_le m_b (mul_nonneg hb x_0))
  exact_mod_cast Int.toNat_eq_max m

Depends on / 依赖: Int.cast_le, Int.toNat_eq_max, Real.eventually_atTop_exists_int_between, cast_le, eventually_atTop_exists_int_between, eventually_ge_atTop, filter_upwards, le_of_eq_of_le, m.self_le_toNat, m.toNat, m_a.trans, max_le, mul_nonneg, self_le_toNat, toNat_eq_max
-/
lemma Real.eventually_atTop_exists_nat_between {a b : Real} (h : a < b) (hb : 0 <= b) :
    forallᶠ x : Real in atTop, exists n : Nat, a * x <= n ∧ n <= b * x := by
  filter_upwards [eventually_ge_atTop 0, Real.eventually_atTop_exists_int_between h]
    with x x_0 ⟨m, m_a, m_b⟩
  refine ⟨m.toNat, m_a.trans (Int.cast_le.2 m.self_le_toNat), ?_⟩
  apply le_of_eq_of_le _ (max_le m_b (mul_nonneg hb x_0))
  exact_mod_cast Int.toNat_eq_max m

/--
lemma `EReal.eventually_atTop_exists_nat_between` / 引理 `EReal.eventually_atTop_exists_nat_between`

English:
lemma EReal.eventually_atTop_exists_nat_between
  given: {a b : EReal} (h : a < b) (hb : 0 <= b)
  proof: match a with
  | ⊤ => (not_top_lt h).rec
  | ⊥ => by
    refine Eventually.of_forall fun n => ⟨0, ?_, ?_⟩ <;> rw [Nat.cast_zero]
    · apply mul_nonpos_iff.2 -- Split apply and exact for a 0.5s. gain
      exact .inr ⟨bot_le, n.cast_nonneg'⟩
    · positivity
  | (a : Real) =>
    match b with
    | 

中文:
引理 EReal.eventually_atTop_exists_nat_between
  条件: {a b : E实数} (h : a < b) (hb : 0 <= b)
  证明: match a with
  | ⊤ => (not_top_lt h).rec
  | ⊥ => by
    refine Eventually.of_forall fun n => ⟨0, ?_, ?_⟩ <;> rw [Nat.cast_zero]
    · apply mul_nonpos_iff.2 -- Split apply and exact for a 0.5s. gain
      exact .inr ⟨bot_le, n.cast_nonneg'⟩
    · positivity
  | (a : Real) =>
    match b with
    | 

Depends on / 依赖: Eventually, Eventually.of_forall, Nat.cast_pos, Nat.cast_zero, bot_le, cast_nonneg, cast_pos, cast_zero, eventually_gt_atTop, exists_nat_ge_mul, h.ne, le_of_le_of_eq, le_top, mul_nonpos_iff, n.cast_nonneg, not_lt_bot, not_top_lt, of_forall, top_mul_of_pos
-/
lemma EReal.eventually_atTop_exists_nat_between {a b : EReal} (h : a < b) (hb : 0 <= b) :
    forallᶠ n : Nat in atTop, exists m : Nat, a * n <= m ∧ m <= b * n :=
  match a with
  | ⊤ => (not_top_lt h).rec
  | ⊥ => by
    refine Eventually.of_forall fun n => ⟨0, ?_, ?_⟩ <;> rw [Nat.cast_zero]
    · apply mul_nonpos_iff.2 -- Split apply and exact for a 0.5s. gain
      exact .inr ⟨bot_le, n.cast_nonneg'⟩
    · positivity
  | (a : Real) =>
    match b with
    | ⊤ => by
      refine (eventually_gt_atTop 0).mono fun n n_0 => ?_
      obtain ⟨m, hm⟩ := exists_nat_ge_mul h.ne n
      exact ⟨m, hm, le_of_le_of_eq le_top (top_mul_of_pos (Nat.cast_pos'.2 n_0)).symm⟩
    | ⊥ => (not_lt_bot h).rec
    | (b : Real) => by
obtain ⟨x, hx⟩ := eventually_atTop.1 Real.eventually_atTop_exists_nat_between
        (EReal.coe_lt_coe_iff.1 h) (EReal.coe_nonneg.1 hb)
      obtain ⟨n, x_n⟩ := exists_nat_ge x
      refine eventually_atTop.2 ⟨n, fun k n_k => ?_⟩
      simp only [← coe_coe_eq_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      exact hx k (x_n.trans (Nat.cast_le.2 n_k))

/--
lemma `tendsto_atTop_of_linearGrowthInf_natCast_pos` / 引理 `tendsto_atTop_of_linearGrowthInf_natCast_pos`

English:
lemma tendsto_atTop_of_linearGrowthInf_natCast_pos
  given: (h : (linearGrowthInf fun n => v n : EReal) != 0)
  proof: by
  refine tendsto_atTop.2 fun M => ?_
  have := tendsto_atTop_of_linearGrowthInf_pos (h.lt_of_le' (linearGrowthInf_natCast_nonneg v))
  exact (tendsto_nhds_top_iff_real.1 this M).mono fun n => by exact_mod_cast le_of_lt

中文:
引理 tendsto_atTop_of_linearGrowthInf_natCast_pos
  条件: (h : (linearGrowthInf fun n => v n : E实数) != 0)
  证明: by
  refine tendsto_atTop.2 fun M => ?_
  have := tendsto_atTop_of_linearGrowthInf_pos (h.lt_of_le' (linearGrowthInf_natCast_nonneg v))
  exact (tendsto_nhds_top_iff_real.1 this M).mono fun n => by exact_mod_cast le_of_lt

Depends on / 依赖: h.lt_of_le, le_of_lt, linearGrowthInf_natCast_nonneg, lt_of_le, tendsto_atTop, tendsto_atTop_of_linearGrowthInf_pos, tendsto_nhds_top_iff_real
-/
lemma tendsto_atTop_of_linearGrowthInf_natCast_pos (h : (linearGrowthInf fun n => v n : EReal) != 0) :
    Tendsto v atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  have := tendsto_atTop_of_linearGrowthInf_pos (h.lt_of_le' (linearGrowthInf_natCast_nonneg v))
  exact (tendsto_nhds_top_iff_real.1 this M).mono fun n => by exact_mod_cast le_of_lt

/--
lemma `le_linearGrowthInf_comp` / 引理 `le_linearGrowthInf_comp`

English:
lemma le_linearGrowthInf_comp
  given: (hu : 0 <=ᶠ[atTop] u) (hv : Tendsto v atTop atTop)
  proof: by
  have uv_0 : 0 <= linearGrowthInf (u ∘ v) := by
    rw [← linearGrowthInf_const zero_ne_bot zero_ne_top]
    exact linearGrowthInf_eventually_monotone (hv.eventually hu)
  apply EReal.mul_le_of_forall_lt_of_nonneg (linearGrowthInf_natCast_nonneg v) uv_0
  refine fun a ⟨_, a_v⟩ b ⟨b_0, b_u⟩ => Ev

中文:
引理 le_linearGrowthInf_comp
  条件: (hu : 0 <=ᶠ[atTop] u) (hv : Tendsto v atTop atTop)
  证明: by
  have uv_0 : 0 <= linearGrowthInf (u ∘ v) := by
    rw [← linearGrowthInf_const zero_ne_bot zero_ne_top]
    exact linearGrowthInf_eventually_monotone (hv.eventually hu)
  apply EReal.mul_le_of_forall_lt_of_nonneg (linearGrowthInf_natCast_nonneg v) uv_0
  refine fun a ⟨_, a_v⟩ b ⟨b_0, b_u⟩ => Ev

Depends on / 依赖: EReal.mul_le_of_forall_lt_of_nonneg, Eventually, Eventually.le_linearGrowthInf, a_vn, b_uv, b_uvn, eventually, eventually_gt_atTop, eventually_lt_of_lt_liminf, eventually_map, eventually_mul_le, filter_mono, filter_upwards, hv.eventually, le_linearGrowthInf, linearGrowthInf, linearGrowthInf_const, linearGrowthInf_eventually_monotone, linearGrowthInf_natCast_nonneg, mul_le_of_forall_lt_of_nonneg
-/
lemma le_linearGrowthInf_comp (hu : 0 <=ᶠ[atTop] u) (hv : Tendsto v atTop atTop) :
    (linearGrowthInf fun n => v n : EReal) * linearGrowthInf u <= linearGrowthInf (u ∘ v) := by
  have uv_0 : 0 <= linearGrowthInf (u ∘ v) := by
    rw [← linearGrowthInf_const zero_ne_bot zero_ne_top]
    exact linearGrowthInf_eventually_monotone (hv.eventually hu)
  apply EReal.mul_le_of_forall_lt_of_nonneg (linearGrowthInf_natCast_nonneg v) uv_0
  refine fun a ⟨_, a_v⟩ b ⟨b_0, b_u⟩ => Eventually.le_linearGrowthInf ?_
  have b_uv := eventually_map.1 ((eventually_mul_le b_u).filter_mono hv)
  filter_upwards [b_uv, eventually_lt_of_lt_liminf a_v, eventually_gt_atTop 0]
    with n b_uvn a_vn n_0
  replace a_vn := ((lt_div_iff (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 a_vn).le
  rw [comp_apply]; rw [mul_comm a b]; rw [mul_assoc b a]
exact b_uvn.trans' by gcongr

/--
lemma `linearGrowthSup_comp_le` / 引理 `linearGrowthSup_comp_le`

English:
lemma linearGrowthSup_comp_le
  statement: (hu : existsᶠ n in atTop, 0 <= u n)
  proof: by
have v_0 := hv₀.symm.lt_of_le (linearGrowthInf_natCast_nonneg v).trans (liminf_le_limsup)
  refine le_mul_of_forall_lt (.inl v_0) (.inl hv₁) ?_
  refine fun a v_a b u_b => Eventually.linearGrowthSup_le ?_
  have b_0 : 0 <= b := by
    rw [← linearGrowthInf_const zero_ne_bot zero_ne_top]
    exact

中文:
引理 linearGrowthSup_comp_le
  结论: (hu : 存在ᶠ n in atTop, 0 <= u n)
  证明: by
have v_0 := hv₀.symm.lt_of_le (linearGrowthInf_natCast_nonneg v).trans (liminf_le_limsup)
  refine le_mul_of_forall_lt (.inl v_0) (.inl hv₁) ?_
  refine fun a v_a b u_b => Eventually.linearGrowthSup_le ?_
  have b_0 : 0 <= b := by
    rw [← linearGrowthInf_const zero_ne_bot zero_ne_top]
    exact

Depends on / 依赖: Eventually, Eventually.linearGrowthSup_le, eventual, eventually_le_mul, eventually_map, filter_mono, filter_upwards, le_mul_of_forall_lt, liminf_le_limsup, linearGrowthInf_const, linearGrowthInf_le_linearGrowthSup_of_frequently_le, linearGrowthInf_natCast_nonneg, linearGrowthSup_le, lt_of_le, symm.lt_of_le, u_b.le, uv_b, zero_ne_bot, zero_ne_top
-/
lemma linearGrowthSup_comp_le (hu : existsᶠ n in atTop, 0 <= u n)
    (hv₀ : (linearGrowthSup fun n => v n : EReal) != 0)
    (hv₁ : (linearGrowthSup fun n => v n : EReal) != ⊤) (hv₂ : Tendsto v atTop atTop) :
    linearGrowthSup (u ∘ v) <= (linearGrowthSup fun n => v n : EReal) * linearGrowthSup u := by
have v_0 := hv₀.symm.lt_of_le (linearGrowthInf_natCast_nonneg v).trans (liminf_le_limsup)
  refine le_mul_of_forall_lt (.inl v_0) (.inl hv₁) ?_
  refine fun a v_a b u_b => Eventually.linearGrowthSup_le ?_
  have b_0 : 0 <= b := by
    rw [← linearGrowthInf_const zero_ne_bot zero_ne_top]
    exact (linearGrowthInf_le_linearGrowthSup_of_frequently_le hu).trans u_b.le
  have uv_b : forallᶠ n in atTop, u (v n) <= b * v n :=
    eventually_map.1 ((eventually_le_mul u_b).filter_mono hv₂)
  filter_upwards [uv_b, eventually_lt_of_limsup_lt v_a, eventually_gt_atTop 0]
    with n uvn_b vn_a n_0
  replace vn_a := ((div_lt_iff (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 vn_a).le
  rw [comp_apply]; rw [mul_comm a b]; rw [mul_assoc b a]
exact uvn_b.trans by gcongr


/--
lemma `_root_.Monotone.linearGrowthInf_nonneg` / 引理 `_root_.Monotone.linearGrowthInf_nonneg`

English:
lemma _root_.Monotone.linearGrowthInf_nonneg
  given: (h : Monotone u) (h' : u != ⊥)
  proof: by
  simp only [ne_eq, funext_iff, not_forall] at h'
  obtain ⟨m, hm⟩ := h'
  have m_n : forallᶠ n in atTop, u m <= u n := eventually_atTop.2 ⟨m, fun _ hb => h hb⟩
  rcases eq_or_ne (u m) ⊤ with hm' | hm'
  · rw [hm'] at m_n
    exact le_top.trans (linearGrowthInf_top.symm.trans_le (linearGrowthInf_

中文:
引理 _root_.Monotone.linearGrowthInf_nonneg
  条件: (h : Monotone u) (h' : u != ⊥)
  证明: by
  simp only [ne_eq, funext_iff, not_forall] at h'
  obtain ⟨m, hm⟩ := h'
  have m_n : forallᶠ n in atTop, u m <= u n := eventually_atTop.2 ⟨m, fun _ hb => h hb⟩
  rcases eq_or_ne (u m) ⊤ with hm' | hm'
  · rw [hm'] at m_n
    exact le_top.trans (linearGrowthInf_top.symm.trans_le (linearGrowthInf_

Depends on / 依赖: eq_or_ne, eventually_atTop, funext_iff, le_top, le_top.trans, linearGrowthInf_const, linearGrowthInf_eventually_monotone, linearGrowthInf_top, linearGrowthInf_top.symm.trans_le, ne_eq, not_forall, trans_le
-/
lemma _root_.Monotone.linearGrowthInf_nonneg (h : Monotone u) (h' : u != ⊥) :
    0 <= linearGrowthInf u := by
  simp only [ne_eq, funext_iff, not_forall] at h'
  obtain ⟨m, hm⟩ := h'
  have m_n : forallᶠ n in atTop, u m <= u n := eventually_atTop.2 ⟨m, fun _ hb => h hb⟩
  rcases eq_or_ne (u m) ⊤ with hm' | hm'
  · rw [hm'] at m_n
    exact le_top.trans (linearGrowthInf_top.symm.trans_le (linearGrowthInf_eventually_monotone m_n))
  · rw [← linearGrowthInf_const hm hm']
    exact linearGrowthInf_eventually_monotone m_n

/--
lemma `_root_.Monotone.linearGrowthSup_nonneg` / 引理 `_root_.Monotone.linearGrowthSup_nonneg`

English:
lemma _root_.Monotone.linearGrowthSup_nonneg
  given: (h : Monotone u) (h' : u != ⊥)
  proof: (h.linearGrowthInf_nonneg h').trans (linearGrowthInf_le_linearGrowthSup)

中文:
引理 _root_.Monotone.linearGrowthSup_nonneg
  条件: (h : Monotone u) (h' : u != ⊥)
  证明: (h.linearGrowthInf_nonneg h').trans (linearGrowthInf_le_linearGrowthSup)

Depends on / 依赖: h.linearGrowthInf_nonneg, linearGrowthInf_le_linearGrowthSup, linearGrowthInf_nonneg
-/
lemma _root_.Monotone.linearGrowthSup_nonneg (h : Monotone u) (h' : u != ⊥) :
    0 <= linearGrowthSup u :=
  (h.linearGrowthInf_nonneg h').trans (linearGrowthInf_le_linearGrowthSup)

/--
lemma `linearGrowthInf_comp_nonneg` / 引理 `linearGrowthInf_comp_nonneg`

English:
lemma linearGrowthInf_comp_nonneg
  given: (h : Monotone u) (h' : u != ⊥) (hv : Tendsto v atTop atTop)
  proof: by
  simp only [ne_eq, funext_iff, not_forall] at h'
  obtain ⟨m, hum⟩ := h'
  have um_uvn : forallᶠ n in atTop, u m <= (u ∘ v) n :=
    (eventually_atTop.2 ⟨m, fun n m_n => h m_n⟩).filter_mono hv
  apply (linearGrowthInf_eventually_monotone um_uvn).trans'
  rcases eq_or_ne (u m) ⊤ with hum' | hum'


中文:
引理 linearGrowthInf_comp_nonneg
  条件: (h : Monotone u) (h' : u != ⊥) (hv : Tendsto v atTop atTop)
  证明: by
  simp only [ne_eq, funext_iff, not_forall] at h'
  obtain ⟨m, hum⟩ := h'
  have um_uvn : forallᶠ n in atTop, u m <= (u ∘ v) n :=
    (eventually_atTop.2 ⟨m, fun n m_n => h m_n⟩).filter_mono hv
  apply (linearGrowthInf_eventually_monotone um_uvn).trans'
  rcases eq_or_ne (u m) ⊤ with hum' | hum'


Depends on / 依赖: Pi.top_def, eq_or_ne, eventually_atTop, filter_mono, funext_iff, le_top, linearGrowthInf_const, linearGrowthInf_eventually_monotone, linearGrowthInf_top, ne_eq, not_forall, top_def, um_uvn
-/
lemma linearGrowthInf_comp_nonneg (h : Monotone u) (h' : u != ⊥) (hv : Tendsto v atTop atTop) :
    0 <= linearGrowthInf (u ∘ v) := by
  simp only [ne_eq, funext_iff, not_forall] at h'
  obtain ⟨m, hum⟩ := h'
  have um_uvn : forallᶠ n in atTop, u m <= (u ∘ v) n :=
    (eventually_atTop.2 ⟨m, fun n m_n => h m_n⟩).filter_mono hv
  apply (linearGrowthInf_eventually_monotone um_uvn).trans'
  rcases eq_or_ne (u m) ⊤ with hum' | hum'
  · rw [hum', ← Pi.top_def, linearGrowthInf_top]; exact le_top
  · rw [linearGrowthInf_const hum hum']

/--
lemma `linearGrowthSup_comp_nonneg` / 引理 `linearGrowthSup_comp_nonneg`

English:
lemma linearGrowthSup_comp_nonneg
  given: (h : Monotone u) (h' : u != ⊥) (hv : Tendsto v atTop atTop)
  proof: (linearGrowthInf_comp_nonneg h h' hv).trans linearGrowthInf_le_linearGrowthSup

中文:
引理 linearGrowthSup_comp_nonneg
  条件: (h : Monotone u) (h' : u != ⊥) (hv : Tendsto v atTop atTop)
  证明: (linearGrowthInf_comp_nonneg h h' hv).trans linearGrowthInf_le_linearGrowthSup

Depends on / 依赖: linearGrowthInf_comp_nonneg, linearGrowthInf_le_linearGrowthSup
-/
lemma linearGrowthSup_comp_nonneg (h : Monotone u) (h' : u != ⊥) (hv : Tendsto v atTop atTop) :
    0 <= linearGrowthSup (u ∘ v) :=
  (linearGrowthInf_comp_nonneg h h' hv).trans linearGrowthInf_le_linearGrowthSup

/--
lemma `_root_.Monotone.linearGrowthInf_comp_le` / 引理 `_root_.Monotone.linearGrowthInf_comp_le`

English:
lemma _root_.Monotone.linearGrowthInf_comp_le
  statement: (h : Monotone u)
  proof: by
  -- First we apply `le_mul_of_forall_lt`.
  by_cases u_0 : u = ⊥
  · rw [u_0, Pi.bot_comp, linearGrowthInf_bot]; exact bot_le
have v_0 := hv₀.symm.lt_of_le (linearGrowthInf_natCast_nonneg v).trans (liminf_le_limsup)
  refine le_mul_of_forall_lt (.inl v_0) (.inl hv₁) fun a v_a b u_b => ?_
  have 

中文:
引理 _root_.Monotone.linearGrowthInf_comp_le
  结论: (h : Monotone u)
  证明: by
  -- First we apply `le_mul_of_forall_lt`.
  by_cases u_0 : u = ⊥
  · rw [u_0, Pi.bot_comp, linearGrowthInf_bot]; exact bot_le
have v_0 := hv₀.symm.lt_of_le (linearGrowthInf_natCast_nonneg v).trans (liminf_le_limsup)
  refine le_mul_of_forall_lt (.inl v_0) (.inl hv₁) fun a v_a b u_b => ?_
  have 
-/
lemma _root_.Monotone.linearGrowthInf_comp_le (h : Monotone u)
    (hv₀ : (linearGrowthSup fun n => v n : EReal) != 0)
    (hv₁ : (linearGrowthSup fun n => v n : EReal) != ⊤) :
    linearGrowthInf (u ∘ v) <= (linearGrowthSup fun n => v n : EReal) * linearGrowthInf u := by
  -- First we apply `le_mul_of_forall_lt`.
  by_cases u_0 : u = ⊥
  · rw [u_0, Pi.bot_comp, linearGrowthInf_bot]; exact bot_le
have v_0 := hv₀.symm.lt_of_le (linearGrowthInf_natCast_nonneg v).trans (liminf_le_limsup)
  refine le_mul_of_forall_lt (.inl v_0) (.inl hv₁) fun a v_a b u_b => ?_
  have a_0 := v_0.trans v_a
  have b_0 := (h.linearGrowthInf_nonneg u_0).trans_lt u_b
  rcases eq_or_ne a ⊤ with rfl | a_top
  · rw [top_mul_of_pos b_0]; exact le_top
  apply Frequently.linearGrowthInf_le
  obtain ⟨a', v_a', a_a'⟩ := exists_between v_a
  -- We get an epsilon of room: if `m` is large enough, then `v n ≤ a' * n < a * n`.
  -- Using `u_b`, we can find arbitrarily large values `n` such that `u n ≤ b * n`.
  -- If such an `n` is large enough, then we can find an integer `k` such that
  -- `a⁻¹ * n ≤ k ≤ a'⁻¹ * n`, or, in other words, `a' * k ≤ n ≤ a * k`.
  -- Then `v k ≤ a' * k ≤ n`, so `u (v k) ≤ u n ≤ b * n ≤ b * a * k`.
  have a_0' := v_0.trans v_a'
  have a_a_inv' : a⁻¹ < a'⁻¹ := inv_strictAntiOn (Set.mem_Ioi.2 a_0') (Set.mem_Ioi.2 a_0) a_a'
  replace v_a' : forallᶠ n : Nat in atTop, v n <= a' * n := by
    filter_upwards [eventually_lt_of_limsup_lt v_a', eventually_gt_atTop 0] with n vn_a' n_0
    rw [mul_comm]
    exact (div_le_iff_le_mul (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 vn_a'.le
  suffices h : (forallᶠ n : Nat in atTop, v n <= a' * n) -> existsᶠ n : Nat in atTop, (u ∘ v) n <= a * b * n
    from h v_a'
  rw [← frequently_imp_distrib]
  replace u_b := ((frequently_le_mul u_b).and_eventually (eventually_gt_atTop 0)).and_eventually
 EReal.eventually_atTop_exists_nat_between a_a_inv' (inv_nonneg_of_nonneg a_0'.le)
  refine frequently_atTop.2 fun M => ?_
  obtain ⟨M', aM_M'⟩ := exists_nat_ge_mul a_top M
  obtain ⟨n, n_M', ⟨un_bn, _⟩, k, an_k, k_an'⟩ := frequently_atTop.1 u_b M'
  refine ⟨k, ?_, fun vk_ak' => ?_⟩
  · rw [mul_comm a, ← le_div_iff_mul_le a_0 a_top, EReal.div_eq_inv_mul] at aM_M'
apply Nat.cast_le.1 aM_M'.trans an_k.trans' _
    gcongr
  · rw [comp_apply, mul_comm a b, mul_assoc b a]
    rw [← EReal.div_eq_inv_mul]; rw [le_div_iff_mul_le a_0' (ne_top_of_lt a_a')]; rw [mul_comm] at k_an'
    rw [← EReal.div_eq_inv_mul]; rw [div_le_iff_le_mul a_0 a_top] at an_k
    have vk_n := Nat.cast_le.1 (vk_ak'.trans k_an')
exact (h vk_n).trans un_bn.trans by gcongr

/--
lemma `_root_.Monotone.le_linearGrowthSup_comp` / 引理 `_root_.Monotone.le_linearGrowthSup_comp`

English:
lemma _root_.Monotone.le_linearGrowthSup_comp
  statement: (h : Monotone u)
  proof: by
  have v_0 := hv.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  -- WLOG, `u` is non-bot, and we can apply `mul_le_of_forall_lt_of_nonneg`.
  by_cases u_0 : u = ⊥
  · rw [u_0, linearGrowthSup_bot, mul_bot_of_pos v_0]; exact bot_le
  apply EReal.mul_le_of_forall_lt_of_nonneg v_0.le
    (linearG

中文:
引理 _root_.Monotone.le_linearGrowthSup_comp
  结论: (h : Monotone u)
  证明: by
  have v_0 := hv.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  -- WLOG, `u` is non-bot, and we can apply `mul_le_of_forall_lt_of_nonneg`.
  by_cases u_0 : u = ⊥
  · rw [u_0, linearGrowthSup_bot, mul_bot_of_pos v_0]; exact bot_le
  apply EReal.mul_le_of_forall_lt_of_nonneg v_0.le
    (linearG

Depends on / 依赖: hv.symm.lt_of_le, linearGrowthInf_natCast_nonneg, lt_of_le
-/
lemma _root_.Monotone.le_linearGrowthSup_comp (h : Monotone u)
    (hv : (linearGrowthInf fun n => v n : EReal) != 0) :
    (linearGrowthInf fun n => v n : EReal) * linearGrowthSup u <= linearGrowthSup (u ∘ v) := by
  have v_0 := hv.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  -- WLOG, `u` is non-bot, and we can apply `mul_le_of_forall_lt_of_nonneg`.
  by_cases u_0 : u = ⊥
  · rw [u_0, linearGrowthSup_bot, mul_bot_of_pos v_0]; exact bot_le
  apply EReal.mul_le_of_forall_lt_of_nonneg v_0.le
    (linearGrowthSup_comp_nonneg h u_0 (tendsto_atTop_of_linearGrowthInf_natCast_pos hv))
  intro a ⟨a_0, a_v⟩ b ⟨b_0, b_u⟩
  apply Frequently.le_linearGrowthSup
  obtain ⟨a', a_a', a_v'⟩ := exists_between a_v
  -- We get an epsilon of room: if `m` is large enough, then `a * n < a' * n ≤ v n`.
  -- Using `b_u`, we can find arbitrarily large values `n` such that `b * n ≤ u n`.
  -- If such an `n` is large enough, then we can find an integer `k` such that
  -- `a'⁻¹ * n ≤ k ≤ a⁻¹ * n`, or, in other words, `a * k ≤ n ≤ a' * k`.
  -- Then `v k ≥ a' * k ≥ n`, so `u (v k) ≥ u n ≥ b * n ≥ b * a * k`.
  have a_top' := ne_top_of_lt a_v'
  have a_0' := a_0.trans a_a'
  have a_a_inv' : a'⁻¹ < a⁻¹ := inv_strictAntiOn (Set.mem_Ioi.2 a_0) (Set.mem_Ioi.2 a_0') a_a'
  replace a_v' : forallᶠ n : Nat in atTop, a' * n <= v n := by
    filter_upwards [eventually_lt_of_lt_liminf a_v', eventually_gt_atTop 0] with n a_vn' n_0
    exact (le_div_iff_mul_le (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 a_vn'.le
  suffices h : (forallᶠ n : Nat in atTop, a' * n <= v n) -> existsᶠ n : Nat in atTop, a * b * n <= (u ∘ v) n
    from h a_v'
  rw [← frequently_imp_distrib]
  replace b_u := ((frequently_mul_le b_u).and_eventually (eventually_gt_atTop 0)).and_eventually
 EReal.eventually_atTop_exists_nat_between a_a_inv' (inv_nonneg_of_nonneg a_0.le)
  refine frequently_atTop.2 fun M => ?_
  obtain ⟨M', aM_M'⟩ := exists_nat_ge_mul a_top' M
  obtain ⟨n, n_M', ⟨bn_un, _⟩, k, an_k', k_an⟩ := frequently_atTop.1 b_u M'
  refine ⟨k, ?_, fun ak_vk' => ?_⟩
  · rw [mul_comm a', ← le_div_iff_mul_le a_0' a_top', EReal.div_eq_inv_mul] at aM_M'
apply Nat.cast_le.1 aM_M'.trans an_k'.trans' _
    gcongr
  · rw [comp_apply, mul_comm a b, mul_assoc b a]
    rw [← EReal.div_eq_inv_mul]; rw [div_le_iff_le_mul a_0' a_top'] at an_k'
    rw [← EReal.div_eq_inv_mul]; rw [le_div_iff_mul_le a_0 (ne_top_of_lt a_a')]; rw [mul_comm] at k_an
    have n_vk := Nat.cast_le.1 (an_k'.trans ak_vk')
exact le_trans (by gcongr) bn_un.trans (h n_vk)

/--
lemma `_root_.Monotone.linearGrowthInf_comp` / 引理 `_root_.Monotone.linearGrowthInf_comp`

English:
lemma _root_.Monotone.linearGrowthInf_comp
  statement: {a : EReal} (h : Monotone u)
  proof: by
  have hv₁ : 0 < liminf (fun n => (v n : EReal) / n) atTop := by
    rw [← hv.liminf_eq] at ha
    exact ha.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  have v_top := tendsto_atTop_of_linearGrowthInf_natCast_pos hv₁.ne.symm
  -- Either `u = 0`, or `u` is non-zero and bounded by `1`, or `u` 

中文:
引理 _root_.Monotone.linearGrowthInf_comp
  结论: {a : E实数} (h : Monotone u)
  证明: by
  have hv₁ : 0 < liminf (fun n => (v n : EReal) / n) atTop := by
    rw [← hv.liminf_eq] at ha
    exact ha.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  have v_top := tendsto_atTop_of_linearGrowthInf_natCast_pos hv₁.ne.symm
  -- Either `u = 0`, or `u` is non-zero and bounded by `1`, or `u` 

Depends on / 依赖: ha.symm.lt_of_le, hv.liminf_eq, liminf, liminf_eq, linearGrowthInf_natCast_nonneg, lt_of_le, ne.symm, tendsto_atTop_of_linearGrowthInf_natCast_pos, v_top
-/
lemma _root_.Monotone.linearGrowthInf_comp {a : EReal} (h : Monotone u)
    (hv : Tendsto (fun n => (v n : EReal) / n) atTop (𝓝 a)) (ha : a != 0) (ha' : a != ⊤) :
    linearGrowthInf (u ∘ v) = a * linearGrowthInf u := by
  have hv₁ : 0 < liminf (fun n => (v n : EReal) / n) atTop := by
    rw [← hv.liminf_eq] at ha
    exact ha.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  have v_top := tendsto_atTop_of_linearGrowthInf_natCast_pos hv₁.ne.symm
  -- Either `u = 0`, or `u` is non-zero and bounded by `1`, or `u` is eventually larger than one.
  -- In the latter case, we apply `le_linearGrowthInf_comp` and `linearGrowthInf_comp_le`.
  by_cases u_0 : u = ⊥
  · rw [u_0, Pi.bot_comp, linearGrowthInf_bot, ← hv.liminf_eq, mul_bot_of_pos hv₁]
  by_cases! h' : existsᶠ n : Nat in atTop, u n <= 0
  · replace h' (n : Nat) : u n <= 0 := by
      obtain ⟨m, n_m, um_1⟩ := (frequently_atTop.1 h') n
      exact (h n_m).trans um_1
    have u_0' : linearGrowthInf u = 0 := by
      apply le_antisymm _ (h.linearGrowthInf_nonneg u_0)
      exact (linearGrowthInf_monotone h').trans_eq (linearGrowthInf_const zero_ne_bot zero_ne_top)
    rw [u_0']; rw [mul_zero]
    apply le_antisymm _ (linearGrowthInf_comp_nonneg h u_0 v_top)
    apply (linearGrowthInf_monotone fun n => h' (v n)).trans_eq
    exact linearGrowthInf_const zero_ne_bot zero_ne_top
  · replace h' := h'.mono fun _ hn => hn.le
    apply le_antisymm
    · rw [← hv.limsup_eq] at ha ha' ⊢
      exact h.linearGrowthInf_comp_le ha ha'
    · rw [← hv.liminf_eq]
      exact le_linearGrowthInf_comp h' v_top

/--
lemma `_root_.Monotone.linearGrowthSup_comp` / 引理 `_root_.Monotone.linearGrowthSup_comp`

English:
lemma _root_.Monotone.linearGrowthSup_comp
  statement: {a : EReal} (h : Monotone u)
  proof: by
  have hv₁ : 0 < liminf (fun n => (v n : EReal) / n) atTop := by
    rw [← hv.liminf_eq] at ha
    exact ha.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  have v_top := tendsto_atTop_of_linearGrowthInf_natCast_pos hv₁.ne.symm
  -- Either `u = 0`, or `u` is non-zero and bounded by `1`, or `u` 

中文:
引理 _root_.Monotone.linearGrowthSup_comp
  结论: {a : E实数} (h : Monotone u)
  证明: by
  have hv₁ : 0 < liminf (fun n => (v n : EReal) / n) atTop := by
    rw [← hv.liminf_eq] at ha
    exact ha.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  have v_top := tendsto_atTop_of_linearGrowthInf_natCast_pos hv₁.ne.symm
  -- Either `u = 0`, or `u` is non-zero and bounded by `1`, or `u` 

Depends on / 依赖: ha.symm.lt_of_le, hv.liminf_eq, liminf, liminf_eq, linearGrowthInf_natCast_nonneg, lt_of_le, ne.symm, tendsto_atTop_of_linearGrowthInf_natCast_pos, v_top
-/
lemma _root_.Monotone.linearGrowthSup_comp {a : EReal} (h : Monotone u)
    (hv : Tendsto (fun n => (v n : EReal) / n) atTop (𝓝 a)) (ha : a != 0) (ha' : a != ⊤) :
    linearGrowthSup (u ∘ v) = a * linearGrowthSup u := by
  have hv₁ : 0 < liminf (fun n => (v n : EReal) / n) atTop := by
    rw [← hv.liminf_eq] at ha
    exact ha.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  have v_top := tendsto_atTop_of_linearGrowthInf_natCast_pos hv₁.ne.symm
  -- Either `u = 0`, or `u` is non-zero and bounded by `1`, or `u` is eventually larger than one.
  -- In the latter case, we apply `le_linearGrowthSup_comp` and `linearGrowthSup_comp_le`.
  by_cases u_0 : u = ⊥
  · rw [u_0, Pi.bot_comp, linearGrowthSup_bot, ← hv.liminf_eq, mul_bot_of_pos hv₁]
  by_cases! u_1 : forallᶠ n : Nat in atTop, u n <= 0
  · have u_0' : linearGrowthSup u = 0 := by
      apply le_antisymm _ (h.linearGrowthSup_nonneg u_0)
      apply (linearGrowthSup_eventually_monotone u_1).trans_eq
      exact (linearGrowthSup_const zero_ne_bot zero_ne_top)
    rw [u_0']; rw [mul_zero]
    apply le_antisymm _ (linearGrowthSup_comp_nonneg h u_0 v_top)
    apply (linearGrowthSup_eventually_monotone (v_top.eventually u_1)).trans_eq
    exact linearGrowthSup_const zero_ne_bot zero_ne_top
  · replace u_1 := u_1.mono fun x hx => hx.le
    apply le_antisymm
    · rw [← hv.limsup_eq] at ha ha' ⊢
      exact linearGrowthSup_comp_le u_1 ha ha' v_top
    · rw [← hv.liminf_eq]
      exact h.le_linearGrowthSup_comp hv₁.ne.symm

/--
lemma `_root_.Monotone.linearGrowthInf_comp_mul` / 引理 `_root_.Monotone.linearGrowthInf_comp_mul`

English:
lemma _root_.Monotone.linearGrowthInf_comp_mul
  given: {m : Nat} (h : Monotone u) (hm : m != 0)
  proof: by
  have : Tendsto (fun n : Nat => ((m * n : Nat) : EReal) / n) atTop (𝓝 m) := by
    refine tendsto_nhds_of_eventually_eq ((eventually_gt_atTop 0).mono fun x hx => ?_)
    rw [mul_comm]; rw [natCast_mul x m]; rw [← mul_div]
    exact mul_div_cancel (natCast_ne_bot x) (natCast_ne_top x) (Nat.cast_n

中文:
引理 _root_.Monotone.linearGrowthInf_comp_mul
  条件: {m : 自然数} (h : Monotone u) (hm : m != 0)
  证明: by
  have : Tendsto (fun n : Nat => ((m * n : Nat) : EReal) / n) atTop (𝓝 m) := by
    refine tendsto_nhds_of_eventually_eq ((eventually_gt_atTop 0).mono fun x hx => ?_)
    rw [mul_comm]; rw [natCast_mul x m]; rw [← mul_div]
    exact mul_div_cancel (natCast_ne_bot x) (natCast_ne_top x) (Nat.cast_n

Depends on / 依赖: Nat.cast_ne_zero, Tendsto, cast_ne_zero, eventually_gt_atTop, h.linearGrowthInf_comp, hx.ne.symm, linearGrowthInf_comp, mul_comm, mul_div, mul_div_cancel, natCast_mul, natCast_ne_bot, natCast_ne_top, tendsto_nhds_of_eventually_eq
-/
lemma _root_.Monotone.linearGrowthInf_comp_mul {m : Nat} (h : Monotone u) (hm : m != 0) :
    linearGrowthInf (fun n => u (m * n)) = m * linearGrowthInf u := by
  have : Tendsto (fun n : Nat => ((m * n : Nat) : EReal) / n) atTop (𝓝 m) := by
    refine tendsto_nhds_of_eventually_eq ((eventually_gt_atTop 0).mono fun x hx => ?_)
    rw [mul_comm]; rw [natCast_mul x m]; rw [← mul_div]
    exact mul_div_cancel (natCast_ne_bot x) (natCast_ne_top x) (Nat.cast_ne_zero.2 hx.ne.symm)
  exact h.linearGrowthInf_comp this (Nat.cast_ne_zero.2 hm) (natCast_ne_top m)

/--
lemma `_root_.Monotone.linearGrowthSup_comp_mul` / 引理 `_root_.Monotone.linearGrowthSup_comp_mul`

English:
lemma _root_.Monotone.linearGrowthSup_comp_mul
  given: {m : Nat} (h : Monotone u) (hm : m != 0)
  proof: by
  have : Tendsto (fun n : Nat => ((m * n : Nat) : EReal) / n) atTop (𝓝 m) := by
    refine tendsto_nhds_of_eventually_eq ((eventually_gt_atTop 0).mono fun x hx => ?_)
    rw [mul_comm]; rw [natCast_mul x m]; rw [← mul_div]
    exact mul_div_cancel (natCast_ne_bot x) (natCast_ne_top x) (Nat.cast_n

中文:
引理 _root_.Monotone.linearGrowthSup_comp_mul
  条件: {m : 自然数} (h : Monotone u) (hm : m != 0)
  证明: by
  have : Tendsto (fun n : Nat => ((m * n : Nat) : EReal) / n) atTop (𝓝 m) := by
    refine tendsto_nhds_of_eventually_eq ((eventually_gt_atTop 0).mono fun x hx => ?_)
    rw [mul_comm]; rw [natCast_mul x m]; rw [← mul_div]
    exact mul_div_cancel (natCast_ne_bot x) (natCast_ne_top x) (Nat.cast_n

Depends on / 依赖: Nat.cast_ne_zero, Tendsto, cast_ne_zero, eventually_gt_atTop, h.linearGrowthSup_comp, hx.ne.symm, linearGrowthSup_comp, mul_comm, mul_div, mul_div_cancel, natCast_mul, natCast_ne_bot, natCast_ne_top, tendsto_nhds_of_eventually_eq
-/
lemma _root_.Monotone.linearGrowthSup_comp_mul {m : Nat} (h : Monotone u) (hm : m != 0) :
    linearGrowthSup (fun n => u (m * n)) = m * linearGrowthSup u := by
  have : Tendsto (fun n : Nat => ((m * n : Nat) : EReal) / n) atTop (𝓝 m) := by
    refine tendsto_nhds_of_eventually_eq ((eventually_gt_atTop 0).mono fun x hx => ?_)
    rw [mul_comm]; rw [natCast_mul x m]; rw [← mul_div]
    exact mul_div_cancel (natCast_ne_bot x) (natCast_ne_top x) (Nat.cast_ne_zero.2 hx.ne.symm)
  exact h.linearGrowthSup_comp this (Nat.cast_ne_zero.2 hm) (natCast_ne_top m)

end composition

end LinearGrowth
