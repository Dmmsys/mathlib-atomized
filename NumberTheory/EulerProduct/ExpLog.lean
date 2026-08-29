/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Logarithms of Euler Products

We consider `f : ℕ →*₀ ℂ` and show that `exp (∑ p in Primes, log (1 - f p)⁻¹) = ∑ n : ℕ, f n`
under suitable conditions on `f`. This can be seen as a logarithmic version of the
Euler product for `f`.
-/

public section

open Complex

open Topology in
/--
lemma `Summable.clog_one_sub` / 引理 `Summable.clog_one_sub`

English:
lemma Summable.clog_one_sub
  given: {α : Type*} {f : α -> Complex} (hsum : Summable f)
  proof: by
  have hg : DifferentiableAt Complex (fun z => log (1 - z)) 0 := by
    have : 1 - 0 in slitPlane := (sub_zero (1 : Complex)).symm ▸ one_mem_slitPlane
    fun_prop
  have : (fun z => log (1 - z)) =O[𝓝 0] id := by
    simpa only [sub_zero, log_one] using! hg.isBigO_sub
  exact this.comp_summable h

中文:
引理 Summable.clog_one_sub
  条件: {α : 类型} {f : α -> Complex} (hsum : Summable f)
  证明: by
  have hg : DifferentiableAt Complex (fun z => log (1 - z)) 0 := by
    have : 1 - 0 in slitPlane := (sub_zero (1 : Complex)).symm ▸ one_mem_slitPlane
    fun_prop
  have : (fun z => log (1 - z)) =O[𝓝 0] id := by
    simpa only [sub_zero, log_one] using! hg.isBigO_sub
  exact this.comp_summable h

Depends on / 依赖: DifferentiableAt, comp_summable, fun_prop, hg.isBigO_sub, isBigO_sub, log_one, one_mem_slitPlane, slitPlane, sub_zero, this.comp_summable
-/
lemma Summable.clog_one_sub {α : Type*} {f : α -> Complex} (hsum : Summable f) :
    Summable fun n => log (1 - f n) := by
  have hg : DifferentiableAt Complex (fun z => log (1 - z)) 0 := by
    have : 1 - 0 in slitPlane := (sub_zero (1 : Complex)).symm ▸ one_mem_slitPlane
    fun_prop
  have : (fun z => log (1 - z)) =O[𝓝 0] id := by
    simpa only [sub_zero, log_one] using! hg.isBigO_sub
  exact this.comp_summable hsum

namespace EulerProduct

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exp_tsum_primes_log_eq_tsum` / 定理 `exp_tsum_primes_log_eq_tsum`

English:
theorem exp_tsum_primes_log_eq_tsum
  given: {f : Nat ->*₀ Complex} (hsum : Summable (‖f ·‖))
  proof: by
  have hs {p : Nat} (hp : 1 < p) : ‖f p‖ < 1 := hsum.of_norm.norm_lt_one (f := f.toMonoidHom) hp
  have hp (p : Nat.Primes) : 1 - f p != 0 :=
    fun h => (norm_one (α := Complex) ▸ (sub_eq_zero.mp h) ▸ hs p.prop.one_lt).false
.hasSum.cexp.tprod_eq have H := hsum.of_norm.clog_one_sub.neg.subtype 

中文:
定理 exp_tsum_primes_log_eq_tsum
  条件: {f : 自然数 ->*₀ Complex} (hsum : Summable (‖f ·‖))
  证明: by
  have hs {p : Nat} (hp : 1 < p) : ‖f p‖ < 1 := hsum.of_norm.norm_lt_one (f := f.toMonoidHom) hp
  have hp (p : Nat.Primes) : 1 - f p != 0 :=
    fun h => (norm_one (α := Complex) ▸ (sub_eq_zero.mp h) ▸ hs p.prop.one_lt).false
.hasSum.cexp.tprod_eq have H := hsum.of_norm.clog_one_sub.neg.subtype 

Depends on / 依赖: Function, Function.comp_apply, H.symm.trans, Nat.Prime, Nat.Primes, Primes, clog_one_sub, comp_apply, eulerProduct_completely_multiplicative_tprod, exp_log, exp_neg, f.toMonoidHom, hasSum, hasSum.cexp.tprod_eq, hsum.of_norm.clog_one_sub.neg.subtype, hsum.of_norm.norm_lt_one, norm_lt_one, norm_one, of_norm, one_lt
-/
theorem exp_tsum_primes_log_eq_tsum {f : Nat ->*₀ Complex} (hsum : Summable (‖f ·‖)) :
    exp (∑' p : Nat.Primes, -log (1 - f p)) = ∑' n : Nat, f n := by
  have hs {p : Nat} (hp : 1 < p) : ‖f p‖ < 1 := hsum.of_norm.norm_lt_one (f := f.toMonoidHom) hp
  have hp (p : Nat.Primes) : 1 - f p != 0 :=
    fun h => (norm_one (α := Complex) ▸ (sub_eq_zero.mp h) ▸ hs p.prop.one_lt).false
.hasSum.cexp.tprod_eq have H := hsum.of_norm.clog_one_sub.neg.subtype Nat.Prime
  simp only [Function.comp_apply, exp_neg, exp_log (hp _)] at H
exact H.symm.trans eulerProduct_completely_multiplicative_tprod hsum

end EulerProduct
