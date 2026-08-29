/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.RingTheory.FreeCommRing

/-!

# Constructing Ring terms from MvPolynomial

This file provides tools for constructing ring terms that can be evaluated to particular
`MvPolynomial`s. The main motivation is in model theory. It can be used to construct first-order
formulas whose realization is a property of an `MvPolynomial`

## Main definitions

* `FirstOrder.Ring.genericPolyMap` is a function that given a finite set of monomials
  `monoms : ι → Finset (κ →₀ ℕ)` returns a function `ι → FreeCommRing ((Σ i : ι, monoms i) ⊕ κ)`
  such that `genericPolyMap monoms i` is a ring term that can be evaluated to a polynomial
  `p : MvPolynomial κ R` such that `p.support ⊆ monoms i`.

-/

@[expose] public section

assert_not_exists Cardinal

variable {ι κ R : Type*}

namespace FirstOrder

namespace Ring

open MvPolynomial FreeCommRing

/--
Definition of `genericPolyMap` / `genericPolyMap` 的定义

English:
definition genericPolyMap
  signature: (monoms : ι -> Finset (κ ->₀ Nat))
  body: fun i => (monoms i).attach.sum
    (fun m => FreeCommRing.of (Sum.inl ⟨i, m⟩) *
      Finsupp.prod m.1 (fun j n => FreeCommRing.of (Sum.inr j) ^ n))

中文:
定义 genericPolyMap
  签名: (monoms : ι -> 有限集 (κ ->₀ 自然数))
  定义体: fun i => (monoms i).attach.sum
    (fun m => FreeCommRing.of (Sum.inl ⟨i, m⟩) *
      Finsupp.prod m.1 (fun j n => FreeCommRing.of (Sum.inr j) ^ n))

Depends on / 依赖: Finsupp, Finsupp.prod, FreeCommRing, FreeCommRing.of, Sum.inl, Sum.inr, attach, attach.sum, monoms
-/
noncomputable def genericPolyMap (monoms : ι -> Finset (κ ->₀ Nat)) :
    ι -> FreeCommRing ((Σ i : ι, monoms i) oplus κ) :=
  fun i => (monoms i).attach.sum
    (fun m => FreeCommRing.of (Sum.inl ⟨i, m⟩) *
      Finsupp.prod m.1 (fun j n => FreeCommRing.of (Sum.inr j) ^ n))

/--
Definition of `mvPolynomialSupportLEEquiv` / `mvPolynomialSupportLEEquiv` 的定义

English:
definition mvPolynomialSupportLEEquiv
  body: { toFun := fun p i => (p.1 i.1).coeff i.2,
    invFun p := ⟨fun i => .ofCoeff
      { toFun := fun m => if hm : m in monoms i then p ⟨i, ⟨m, hm⟩⟩ else 0
        support := {m in monoms i | exists hm : m in monoms i, p ⟨i, ⟨m, hm⟩⟩ != 0},
        mem_support_toFun := by simp },
      fun i => Finset.

中文:
定义 mvPolynomialSupportLEEquiv
  定义体: { toFun := fun p i => (p.1 i.1).coeff i.2,
    invFun p := ⟨fun i => .ofCoeff
      { toFun := fun m => if hm : m in monoms i then p ⟨i, ⟨m, hm⟩⟩ else 0
        support := {m in monoms i | exists hm : m in monoms i, p ⟨i, ⟨m, hm⟩⟩ != 0},
        mem_support_toFun := by simp },
      fun i => Finset.

Depends on / 依赖: Finset, Finset.filter_subset, Finsupp, Finsupp.coe_mk, MvPolynomial, coe_mk, dite_eq_ite, eq_comm, exists_prop, filter_subset, invFun, ite_eq_left_iff, left_inv, mem_support_toFun, monoms, ne_eq, ofCoeff, support
-/
noncomputable def mvPolynomialSupportLEEquiv
    [DecidableEq κ] [CommRing R] [DecidableEq R]
    (monoms : ι -> Finset (κ ->₀ Nat)) :
    { p : ι -> MvPolynomial κ R // forall i, (p i).support subseteq monoms i } ≃
      ((Σ i, monoms i) -> R) :=
  { toFun := fun p i => (p.1 i.1).coeff i.2,
    invFun p := ⟨fun i => .ofCoeff
      { toFun := fun m => if hm : m in monoms i then p ⟨i, ⟨m, hm⟩⟩ else 0
        support := {m in monoms i | exists hm : m in monoms i, p ⟨i, ⟨m, hm⟩⟩ != 0},
        mem_support_toFun := by simp },
      fun i => Finset.filter_subset _ _⟩,
    left_inv := fun p => by
      ext i m
      simp only [coeff, ne_eq, exists_prop, dite_eq_ite, Finsupp.coe_mk, ite_eq_left_iff]
      intro hm
      have : m ∉ (p.1 i).support := fun h => hm (p.2 i h)
      simpa [coeff, eq_comm, MvPolynomial.mem_support_iff] using this
    right_inv := fun p => by ext; simp [coeff] }

@[simp]
/--
theorem `MvPolynomialSupportLEEquiv_symm_apply_coeff` / 定理 `MvPolynomialSupportLEEquiv_symm_apply_coeff`

English:
theorem MvPolynomialSupportLEEquiv_symm_apply_coeff
  statement: [DecidableEq κ] [CommRing R] [DecidableEq R]
  proof: (mvPolynomialSupportLEEquiv (R := R) (fun i : ι => (p i).support)).symm_apply_apply
    ⟨p, fun _ => Finset.Subset.refl _⟩

中文:
定理 MvPolynomialSupportLEEquiv_symm_apply_coeff
  结论: [DecidableEq κ] [交换环 R] [DecidableEq R]
  证明: (mvPolynomialSupportLEEquiv (R := R) (fun i : ι => (p i).support)).symm_apply_apply
    ⟨p, fun _ => Finset.Subset.refl _⟩

Depends on / 依赖: Finset, Finset.Subset.refl, Subset, mvPolynomialSupportLEEquiv, support, symm_apply_apply
-/
theorem MvPolynomialSupportLEEquiv_symm_apply_coeff [DecidableEq κ] [CommRing R] [DecidableEq R]
    (p : ι -> MvPolynomial κ R) : (mvPolynomialSupportLEEquiv (fun i => (p i).support)).symm
      (fun i => (p i.1).coeff i.2.1) = ⟨p, fun _ => Finset.Subset.refl _⟩ :=
  (mvPolynomialSupportLEEquiv (R := R) (fun i : ι => (p i).support)).symm_apply_apply
    ⟨p, fun _ => Finset.Subset.refl _⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lift_genericPolyMap` / 定理 `lift_genericPolyMap`

English:
theorem lift_genericPolyMap
  statement: [DecidableEq κ] [CommRing R]
  proof: by
  simp only [genericPolyMap, map_sum, map_mul, lift_of, support,
    mvPolynomialSupportLEEquiv, coeff, Finset.sum_filter, MvPolynomial.eval_eq,
    ne_eq, Function.comp, Equiv.coe_fn_symm_mk, Finsupp.coe_mk]
  conv_rhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl ?_
  intro m _
  si

中文:
定理 lift_genericPolyMap
  结论: [DecidableEq κ] [交换环 R]
  证明: by
  simp only [genericPolyMap, map_sum, map_mul, lift_of, support,
    mvPolynomialSupportLEEquiv, coeff, Finset.sum_filter, MvPolynomial.eval_eq,
    ne_eq, Function.comp, Equiv.coe_fn_symm_mk, Finsupp.coe_mk]
  conv_rhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl ?_
  intro m _
  si

Depends on / 依赖: Equiv.coe_fn_symm_mk, Finset, Finset.coe_mem, Finset.sum_attach, Finset.sum_congr, Finset.sum_filter, Finsupp, Finsupp.coe_mk, Finsupp.prod, Function, Function.comp, MvPolynomial, MvPolynomial.eval_eq, Subtype, Subtype.coe_eta, coe_eta, coe_fn_symm_mk, coe_mem, coe_mk, conv_rhs
-/
theorem lift_genericPolyMap [DecidableEq κ] [CommRing R]
    [DecidableEq R] (monoms : ι -> Finset (κ ->₀ Nat))
    (f : (i : ι) × { x // x in monoms i } oplus κ -> R) (i : ι) :
    FreeCommRing.lift f (genericPolyMap monoms i) =
      MvPolynomial.eval (f ∘ Sum.inr)
        (((mvPolynomialSupportLEEquiv monoms).symm
          (f ∘ Sum.inl)).1 i) := by
  simp only [genericPolyMap, map_sum, map_mul, lift_of, support,
    mvPolynomialSupportLEEquiv, coeff, Finset.sum_filter, MvPolynomial.eval_eq,
    ne_eq, Function.comp, Equiv.coe_fn_symm_mk, Finsupp.coe_mk]
  conv_rhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl ?_
  intro m _
  simp only [Finsupp.prod, map_prod, map_pow, lift_of, Subtype.coe_eta, Finset.coe_mem,
    exists_prop, true_and, dite_eq_ite, ite_true, ite_not]
  split_ifs with h0 <;> simp_all

end Ring

end FirstOrder
