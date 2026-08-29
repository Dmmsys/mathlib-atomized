/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.Teichmuller

/-!
# Untilt Function

In this file, we define the untilt function from the pretilt of a
`p`-adically complete ring to the ring itself. Note that this
is not the untilt *functor*.

## Main definition
* `PreTilt.untilt` : Given a `p`-adically complete ring `O`, this is the
  multiplicative map from `PreTilt O p` to `O` itself. Specifically, it is
  defined as the limit of `p^n`-th powers of arbitrary lifts in `O` of the
  `n`-th component from the perfection of `O/p`.

## Main theorem
* `PreTilt.mk_untilt_eq_coeff_zero` : The composition of the mod `p` map
  with the untilt function equals taking the zeroth component of the perfection.

## Reference
* [Berkeley Lectures on \( p \)-adic Geometry][MR4446467]

## Tags
Perfectoid, Tilting equivalence, Untilt
-/

@[expose] public section

open Ideal Perfection

namespace PreTilt

variable {O : Type*} [CommRing O] {p : Nat} [Fact (Nat.Prime p)] [Fact ¬IsUnit (p : O)]
variable [IsAdicComplete (span {(p : O)}) O]

/--
Definition of `untilt` / `untilt` 的定义

English:
definition untilt
  signature: : PreTilt O p ->* O
  body: teichmuller p _

中文:
定义 untilt
  签名: : PreTilt O p ->* O
  定义体: teichmuller p _

Depends on / 依赖: teichmuller
-/
noncomputable def untilt : PreTilt O p ->* O :=
  teichmuller p _

/--
The composition of the mod `p` map
with the untilt function equals taking the zeroth component of the perfection.
-/
@[simp]
/--
theorem `mk_untilt_eq_coeff_zero` / 定理 `mk_untilt_eq_coeff_zero`

English:
theorem mk_untilt_eq_coeff_zero
  given: (x : PreTilt O p)
  proof: mk_teichmuller x

中文:
定理 mk_untilt_eq_coeff_zero
  条件: (x : PreTilt O p)
  证明: mk_teichmuller x

Depends on / 依赖: mk_teichmuller
-/
theorem mk_untilt_eq_coeff_zero (x : PreTilt O p) :
    Ideal.Quotient.mk (Ideal.span {(p : O)}) (x.untilt) = coeff 0 x :=
  mk_teichmuller x

/--
The composition of the mod `p` map
with the untilt function equals taking the zeroth component of the perfection.
A variation of `PreTilt.mk_untilt_eq_coeff_zero`.
-/
@[simp]
/--
theorem `mk_comp_untilt_eq_coeff_zero` / 定理 `mk_comp_untilt_eq_coeff_zero`

English:
theorem mk_comp_untilt_eq_coeff_zero
  proof: mk_comp_teichmuller' ..

@[simp]

中文:
定理 mk_comp_untilt_eq_coeff_zero
  证明: mk_comp_teichmuller' ..

@[simp]

Depends on / 依赖: mk_comp_teichmuller
-/
theorem mk_comp_untilt_eq_coeff_zero :
    Ideal.Quotient.mk (Ideal.span {(p : O)}) ∘ untilt = coeff 0 :=
  mk_comp_teichmuller' ..

@[simp]
/--
theorem `untilt_iterate_frobeniusEquiv_symm_pow` / 定理 `untilt_iterate_frobeniusEquiv_symm_pow`

English:
theorem untilt_iterate_frobeniusEquiv_symm_pow
  given: (x : PreTilt O p) (n : Nat)
  proof: by
  simp only [← map_pow]
  congr
  simp

中文:
定理 untilt_iterate_frobeniusEquiv_symm_pow
  条件: (x : PreTilt O p) (n : 自然数)
  证明: by
  simp only [← map_pow]
  congr
  simp

Depends on / 依赖: map_pow
-/
theorem untilt_iterate_frobeniusEquiv_symm_pow (x : PreTilt O p) (n : Nat) :
    untilt (((frobeniusEquiv (PreTilt O p) p).symm^[n]) x) ^ p ^ n = x.untilt := by
  simp only [← map_pow]
  congr
  simp

end PreTilt
