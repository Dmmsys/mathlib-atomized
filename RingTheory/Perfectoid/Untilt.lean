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

variable {O : Type*} [CommRing O] {p : ℕ} [Fact (Nat.Prime p)] [Fact ¬IsUnit (p : O)]
variable [IsAdicComplete (span {(p : O)}) O]

/--
Given a `p`-adically complete ring `O`, this is the
multiplicative map from `PreTilt O p` to `O` itself. Specifically, it is
defined as the limit of `p^n`-th powers of arbitrary lifts in `O` of the
`n`-th component from the perfection of `O/p`.
-/
/-
**PreTilt.untilt** 是 Mathlib 中的一个定义，位于命名空间 `PreTilt`。
形式化陈述：untilt : PreTilt O p ->* O
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModP.instCharPOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : CommRi
ng O] (p : ℕ) [Fact (Nat.Prime p)] [hvp : Fact ¬IsUnit ↑p], CharP (ModP O p) p

--- 原说明 ---
Given a `p`-adically complete ring `O`, this is the
multiplicative map from `PreTilt O p` to `O` itself. Specifically, it is
defined as the limit of `p^n`-th powers of arbitrary lifts in `O` of the
`n`-th component from the perfection of `O/p`.
-/
noncomputable def untilt : PreTilt O p →* O :=
  teichmuller p _

/--
The composition of the mod `p` map
with the untilt function equals taking the zeroth component of the perfection.
-/
@[simp]
/-
**PreTilt.mk_untilt_eq_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：mk_untilt_eq_coeff_zero (x : PreTilt O p) : Ideal.Quotient.mk (Ideal.span 
{(p : O)}) (x.untilt) = coeff 0 x
参数：x : PreTilt O p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.mk_teichmuller`：mk_teichmuller (x : Perfection (R ⧸ I) p) : I
deal.Quotient.mk I (teichmuller p I x) = coeff _ p 0 x
· 使用定理 `ModP.instCharPOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : CommRi
ng O] (p : ℕ) [Fact (Nat.Prime p)] [hvp : Fact ¬IsUnit ↑p], CharP (ModP O p) p

--- 原说明 ---
The composition of the mod `p` map
with the untilt function equals taking the zeroth component of the perfection.
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
/-
**PreTilt.mk_comp_untilt_eq_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：mk_comp_untilt_eq_coeff_zero : Ideal.Quotient.mk (Ideal.span {(p : O)}) ∘ 
untilt = coeff 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.mk_comp_teichmuller'`：mk_comp_teichmuller' : Ideal.Quotient.m
k I ∘ (teichmuller p I) = coeff (R ⧸ I) p 0
· 使用定理 `ModP.instCharPOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : CommRi
ng O] (p : ℕ) [Fact (Nat.Prime p)] [hvp : Fact ¬IsUnit ↑p], CharP (ModP O p) p

--- 原说明 ---
The composition of the mod `p` map
with the untilt function equals taking the zeroth component of the perfection.
A variation of `PreTilt.mk_untilt_eq_coeff_zero`.
-/
theorem mk_comp_untilt_eq_coeff_zero :
    Ideal.Quotient.mk (Ideal.span {(p : O)}) ∘ untilt = coeff 0 :=
  mk_comp_teichmuller' ..

@[simp]
/-
**PreTilt.untilt_iterate_frobeniusEquiv_symm_pow** 是 Mathlib 中的一个定理，位于命名空间 `PreT
ilt`。
形式化陈述：untilt_iterate_frobeniusEquiv_symm_pow (x : PreTilt O p) (n : Nat) : until
t (((frobeniusEquiv (PreTilt O p) p).symm^[n]) x) ^ p ^ n = x.untilt
参数：x : PreTilt O p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PreTilt.instCharP`：∀ (O : Type u₂) [inst : CommRing O] (p : ℕ) [inst_1 :
 Fact (Nat.Prime p)] [inst_2 : Fact ¬IsUnit ↑p],   CharP (PreTilt O p) p
· 使用定理 `PreTilt.instPerfectRing`：∀ (O : Type u₂) [inst : CommRing O] (p : ℕ) [in
st_1 : Fact (Nat.Prime p)] [inst_2 : Fact ¬IsUnit ↑p],   PerfectRing (PreTilt O 
p) p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iterate_frobeniusEquiv_symm_pow_p_pow`：iterate_frobeniusEquiv_symm_pow_p
_pow (x : R) (n : Nat) : ((frobeniusEquiv R p).symm^[n]) x ^ (p ^ n) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem untilt_iterate_frobeniusEquiv_symm_pow (x : PreTilt O p) (n : ℕ) :
    untilt (((frobeniusEquiv (PreTilt O p) p).symm^[n]) x) ^ p ^ n = x.untilt := by
  simp only [← map_pow]
  congr
  simp

end PreTilt

