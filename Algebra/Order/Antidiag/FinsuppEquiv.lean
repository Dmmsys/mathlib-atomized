/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

/-!

# Equivalence between `Finset.finsuppAntidiag` and `Sym`

This file collects further results about equivalence and cardinality related to
`Finset.finsuppAntidiag`. This file is separated from `Mathlib.Algebra.Order.Antidiag.Finsupp` to
reduce imports.

## Main declarations
* `Finset.finsuppAntidiagEquivSubtype`: `Finset.finsuppAntidiag s n` is equivalent to subtype of
  `s →₀ μ` whose sum is `n`.
* `Finset.finsuppAntidiagEquiv`: `Finset.finsuppAntidiag s n` is equivalent to `Sym s n` for
  natural number `n`.
* `Finset.card_finsuppAntidiag_nat_eq_choose` and `Finset.card_finsuppAntidiag_nat_eq_multichoose`:
  cardinality formula for `Finset.finsuppAntidiag s n` for natural number `n`.
-/

@[expose] public section

open Finsupp Function

variable {ι μ μ' : Type*}

namespace Finset
variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ}

set_option backward.isDefEq.respectTransparency false in
variable (s n) in
/-- The equivalence between `Finset.finsuppAntidiag s n` and the subtype of `s →₀ μ` whose sum is
`n`. -/
@[simps]
/--
Definition of `finsuppAntidiagEquivSubtype` / `finsuppAntidiagEquivSubtype` 的定义

English:
definition finsuppAntidiagEquivSubtype
  signature: :
  body: ⟨subtypeDomain (· in s) f.val, by
    have hf := f.2
    rw [mem_finsuppAntidiag'] at hf
    simpa [sum, filter_mem_eq_inter, inter_eq_left.mpr hf.2] using hf.1⟩
  invFun f := ⟨extendDomain f.val, mem_finsuppAntidiag'.mpr
    ⟨by simpa [sum] using f.2, by simp [map_eq_image, image_subset_iff]⟩⟩
  le

中文:
定义 finsuppAntidiagEquivSubtype
  签名: :
  定义体: ⟨subtypeDomain (· in s) f.val, by
    have hf := f.2
    rw [mem_finsuppAntidiag'] at hf
    simpa [sum, filter_mem_eq_inter, inter_eq_left.mpr hf.2] using hf.1⟩
  invFun f := ⟨extendDomain f.val, mem_finsuppAntidiag'.mpr
    ⟨by simpa [sum] using f.2, by simp [map_eq_image, image_subset_iff]⟩⟩
  le

Depends on / 依赖: extendDomain, extendDomain_subtypeDomain, f.prop, f.val, filter_mem_eq_inter, image_subset_iff, inter_eq_left, inter_eq_left.mpr, invFun, left_inv, map_eq_image, mem_finsuppAntidiag, mem_finsuppAntidiag.mp, right_inv, subtypeDomain
-/
noncomputable def finsuppAntidiagEquivSubtype :
    s.finsuppAntidiag n ≃ { P : s ->₀ μ // (P.sum fun (_ : s) => id) = n } where
  toFun f := ⟨subtypeDomain (· in s) f.val, by
    have hf := f.2
    rw [mem_finsuppAntidiag'] at hf
    simpa [sum, filter_mem_eq_inter, inter_eq_left.mpr hf.2] using hf.1⟩
  invFun f := ⟨extendDomain f.val, mem_finsuppAntidiag'.mpr
    ⟨by simpa [sum] using f.2, by simp [map_eq_image, image_subset_iff]⟩⟩
  left_inv f := by
    obtain ⟨hsum, hs⟩ := mem_finsuppAntidiag.mp f.prop
    ext1
    exact extendDomain_subtypeDomain _ hs
  right_inv f := by simp

variable (s) in
/--
Definition of `finsuppAntidiagEquiv` / `finsuppAntidiagEquiv` 的定义

English:
definition finsuppAntidiagEquiv
  signature: (n : Nat)
  body: (finsuppAntidiagEquivSubtype s n).trans (Sym.equivNatSum s n).symm

@[simp]

中文:
定义 finsuppAntidiagEquiv
  签名: (n : 自然数)
  定义体: (finsuppAntidiagEquivSubtype s n).trans (Sym.equivNatSum s n).symm

@[simp]

Depends on / 依赖: Sym.equivNatSum, equivNatSum, finsuppAntidiagEquivSubtype
-/
noncomputable def finsuppAntidiagEquiv (n : Nat) : s.finsuppAntidiag n ≃ Sym s n :=
  (finsuppAntidiagEquivSubtype s n).trans (Sym.equivNatSum s n).symm

@[simp]
/--
theorem `finsuppAntidiagEquiv_symm_apply_apply` / 定理 `finsuppAntidiagEquiv_symm_apply_apply`

English:
theorem finsuppAntidiagEquiv_symm_apply_apply
  given: (n : Nat) (f : Sym s n) (a : s)
  proof: by
  simp [finsuppAntidiagEquiv]

@[simp]

中文:
定理 finsuppAntidiagEquiv_symm_apply_apply
  条件: (n : 自然数) (f : Sym s n) (a : s)
  证明: by
  simp [finsuppAntidiagEquiv]

@[simp]

Depends on / 依赖: finsuppAntidiagEquiv
-/
theorem finsuppAntidiagEquiv_symm_apply_apply (n : Nat) (f : Sym s n) (a : s) :
    ((finsuppAntidiagEquiv s n).symm f).val a.val = f.toMultiset.count a := by
  simp [finsuppAntidiagEquiv]

@[simp]
/--
theorem `count_coe_finsuppAntidiagEquiv_apply` / 定理 `count_coe_finsuppAntidiagEquiv_apply`

English:
theorem count_coe_finsuppAntidiagEquiv_apply
  given: (n : Nat) (f : s.finsuppAntidiag n) (a : s)
  proof: by
  simp [finsuppAntidiagEquiv]

中文:
定理 count_coe_finsuppAntidiagEquiv_apply
  条件: (n : 自然数) (f : s.finsuppAntidiag n) (a : s)
  证明: by
  simp [finsuppAntidiagEquiv]

Depends on / 依赖: finsuppAntidiagEquiv
-/
theorem count_coe_finsuppAntidiagEquiv_apply (n : Nat) (f : s.finsuppAntidiag n) (a : s) :
    (finsuppAntidiagEquiv s n f).toMultiset.count a = f.val a := by
  simp [finsuppAntidiagEquiv]

/--
theorem `card_finsuppAntidiag_nat_eq_choose` / 定理 `card_finsuppAntidiag_nat_eq_choose`

English:
theorem card_finsuppAntidiag_nat_eq_choose
  given: (n : Nat)
  proof: by
  simp [card_eq_of_equiv_fintype (finsuppAntidiagEquiv s n), Sym.card_sym_eq_choose]

中文:
定理 card_finsuppAntidiag_nat_eq_choose
  条件: (n : 自然数)
  证明: by
  simp [card_eq_of_equiv_fintype (finsuppAntidiagEquiv s n), Sym.card_sym_eq_choose]

Depends on / 依赖: IsOrderedMonoid, IsOrderedMonoid.toIsOrderedCancelMonoid, Sym.card_sym_eq_choose, card_eq_of_equiv_fintype, card_sym_eq_choose, finsuppAntidiagEquiv, toIsOrderedCancelMonoid
-/
theorem card_finsuppAntidiag_nat_eq_choose (n : Nat) :
    #(s.finsuppAntidiag n) = (#s + n - 1).choose n := by
  simp [card_eq_of_equiv_fintype (finsuppAntidiagEquiv s n), Sym.card_sym_eq_choose]

/--
theorem `card_finsuppAntidiag_nat_eq_multichoose` / 定理 `card_finsuppAntidiag_nat_eq_multichoose`

English:
theorem card_finsuppAntidiag_nat_eq_multichoose
  given: (n : Nat)
  proof: by
  simp [card_eq_of_equiv_fintype (finsuppAntidiagEquiv s n), Sym.card_sym_eq_multichoose]

中文:
定理 card_finsuppAntidiag_nat_eq_multichoose
  条件: (n : 自然数)
  证明: by
  simp [card_eq_of_equiv_fintype (finsuppAntidiagEquiv s n), Sym.card_sym_eq_multichoose]

Depends on / 依赖: Sym.card_sym_eq_multichoose, card_eq_of_equiv_fintype, card_sym_eq_multichoose, finsuppAntidiagEquiv
-/
theorem card_finsuppAntidiag_nat_eq_multichoose (n : Nat) :
    #(s.finsuppAntidiag n) = (#s).multichoose n := by
  simp [card_eq_of_equiv_fintype (finsuppAntidiagEquiv s n), Sym.card_sym_eq_multichoose]

end Finset
