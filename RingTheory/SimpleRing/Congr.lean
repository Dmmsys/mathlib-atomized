/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Simplicity is preserved by ring isomorphisms/surjective ring homomorphisms

If `R` is a simple (non-assoc) ring and there exists surjective `f : R →+* S` where `S` is
nontrivial, then `S` is also simple.
If `R` is a simple (non-unital non-assoc) ring then any ring isomorphic to `R` is also simple.
-/

public section

namespace IsSimpleRing

/--
lemma `of_surjective` / 引理 `of_surjective`

English:
lemma of_surjective
  statement: {R S : Type*} [NonAssocRing R] [NonAssocRing S] [Nontrivial S]
  proof: OrderIso.isSimpleOrder (RingEquiv.ofBijective f
    ⟨RingHom.injective f, hf⟩).symm.mapTwoSidedIdeal

中文:
引理 of_surjective
  结论: {R S : 类型} [非结合环 R] [非结合环 S] [非平凡 S]
  证明: OrderIso.isSimpleOrder (RingEquiv.ofBijective f
    ⟨RingHom.injective f, hf⟩).symm.mapTwoSidedIdeal

Depends on / 依赖: OrderIso, OrderIso.isSimpleOrder, RingEquiv, RingEquiv.ofBijective, isSimpleOrder, ofBijective
-/
lemma of_surjective {R S : Type*} [NonAssocRing R] [NonAssocRing S] [Nontrivial S]
    (f : R ->+* S) (h : IsSimpleRing R) (hf : Function.Surjective f) : IsSimpleRing S where
  simple := OrderIso.isSimpleOrder (RingEquiv.ofBijective f
    ⟨RingHom.injective f, hf⟩).symm.mapTwoSidedIdeal

/--
lemma `of_ringEquiv` / 引理 `of_ringEquiv`

English:
lemma of_ringEquiv
  statement: {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  proof: OrderIso.isSimpleOrder f.symm.mapTwoSidedIdeal

中文:
引理 of_ringEquiv
  结论: {R S : 类型} [非幺非结合环 R] [非幺非结合环 S]
  证明: OrderIso.isSimpleOrder f.symm.mapTwoSidedIdeal

Depends on / 依赖: OrderIso, OrderIso.isSimpleOrder, f.symm.mapTwoSidedIdeal, isSimpleOrder, mapTwoSidedIdeal
-/
lemma of_ringEquiv {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    (f : R ≃+* S) (h : IsSimpleRing R) : IsSimpleRing S where
  simple := OrderIso.isSimpleOrder f.symm.mapTwoSidedIdeal

end IsSimpleRing

open TwoSidedIdeal in
/--
theorem `isSimpleRing_iff_isTwoSided_imp` / 定理 `isSimpleRing_iff_isTwoSided_imp`

English:
theorem isSimpleRing_iff_isTwoSided_imp
  given: {R : Type*} [Ring R]
  proof: by
  let e := orderIsoIsTwoSided (R := R)
  simp_rw [isSimpleRing_iff, isSimpleOrder_iff, orderIsoRingCon.toEquiv.nontrivial_congr,
    RingCon.nontrivial_iff, e.forall_congr_left, Subtype.forall, ← e.injective.eq_iff]
  simp [e, Subtype.ext_iff]

中文:
定理 isSimpleRing_iff_isTwoSided_imp
  条件: {R : 类型} [环 R]
  证明: by
  let e := orderIsoIsTwoSided (R := R)
  simp_rw [isSimpleRing_iff, isSimpleOrder_iff, orderIsoRingCon.toEquiv.nontrivial_congr,
    RingCon.nontrivial_iff, e.forall_congr_left, Subtype.forall, ← e.injective.eq_iff]
  simp [e, Subtype.ext_iff]

Depends on / 依赖: RingCon, RingCon.nontrivial_iff, Subtype, Subtype.ext_iff, Subtype.forall, e.forall_congr_left, e.injective.eq_iff, eq_iff, ext_iff, forall_congr_left, injective, isSimpleOrder_iff, isSimpleRing_iff, nontrivial_congr, nontrivial_iff, orderIsoIsTwoSided, orderIsoRingCon, orderIsoRingCon.toEquiv.nontrivial_congr, simp_rw, toEquiv
-/
theorem isSimpleRing_iff_isTwoSided_imp {R : Type*} [Ring R] :
    IsSimpleRing R ↔ Nontrivial R ∧ forall I : Ideal R, I.IsTwoSided -> I = ⊥ ∨ I = ⊤ := by
  let e := orderIsoIsTwoSided (R := R)
  simp_rw [isSimpleRing_iff, isSimpleOrder_iff, orderIsoRingCon.toEquiv.nontrivial_congr,
    RingCon.nontrivial_iff, e.forall_congr_left, Subtype.forall, ← e.injective.eq_iff]
  simp [e, Subtype.ext_iff]
