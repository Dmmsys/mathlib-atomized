/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.ModelTheory.Arithmetic.Presburger.Basic
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Basic
public import Mathlib.ModelTheory.Definability

import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Presburger definability and semilinear sets

This file formalizes the classical result that Presburger definable sets are the same as semilinear
sets. As an application of this result, we show that the graph of multiplication is not Presburger
definable.

## Main Results

- `presburger.definable_iff_isSemilinearSet`: a set is Presburger definable in `ℕ` if and only if it
  is semilinear.
- `presburger.definable₁_iff_ultimately_periodic`: in the 1-dimensional case, a set is Presburger
  arithmetic definable in `ℕ` if and only if it is ultimately periodic, i.e. periodic after some
  number `k`.
- `presburger.mul_not_definable`: the graph of multiplication is not Presburger definable in `ℕ`.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Seymour Ginsburg and Edwin H. Spanier, *Semigroups, Presburger Formulas, and
  Languages*][ginsburg1966]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

public section

variable {α : Type*} {s : Set (α -> Nat)} {A : Set Nat}

open Set FirstOrder Language

/--
theorem `IsLinearSet.definable` / 定理 `IsLinearSet.definable`

English:
theorem IsLinearSet.definable
  given: [Finite α] (hs : IsLinearSet s)
  statement: A.Definable presburger s
  proof: by
  rw [isLinearSet_iff] at hs
  rcases hs with ⟨v, t, rfl⟩
  refine ⟨Formula.iExs t (Formula.iInf fun i : α =>
    (Term.var (Sum.inl i)).equal
      (Term.varsToConstants
        ((v i : presburger.Term _) + presburger.sum Finset.univ fun x : t =>
          x.1 i • Term.var (Sum.inr (Sum.inr x))))), ?_⟩
  ext x
  simp only [mem_vadd_set, SetLike.mem_coe, AddSubmonoid.mem_closure_finset', Finset.univ_eq_attach,
    nsmul_eq_mul, vadd_eq_add, ↓existsAndEq, true_and, mem_ofPred_eq, Formula.realize_iExs,
    Formula.realize_iInf, Formula.realize_equal, Term.realize_var, Sum.elim_inl,
    Term.realize_varsToConstants, coe_con, presburger.realize_add, presburger.realize_natCast,
    Nat.cast_id, presburger.realize_sum, presburger.realize_nsmul, Sum.elim_inr, smul_eq_mul]
  congr! with a
  simp_rw [Eq.comm (b := x), fun x : t => mul_comm (a x : α -> Nat) x, funext_iff]
  congr! 1 with i
  simp

中文:
定理 IsLinearSet.definable
  条件: [有限 α] (hs : IsLinearSet s)
  结论: A.Definable presburger s
  证明: by
  rw [isLinearSet_iff] at hs
  rcases hs with ⟨v, t, rfl⟩
  refine ⟨Formula.iExs t (Formula.iInf fun i : α =>
    (Term.var (Sum.inl i)).equal
      (Term.varsToConstants
        ((v i : presburger.Term _) + presburger.sum Finset.univ fun x : t =>
          x.1 i • Term.var (Sum.inr (Sum.inr x))))), ?_⟩
  ext x
  simp only [mem_vadd_set, SetLike.mem_coe, AddSubmonoid.mem_closure_finset', Finset.univ_eq_attach,
    nsmul_eq_mul, vadd_eq_add, ↓existsAndEq, true_and, mem_ofPred_eq, Formula.realize_iExs,
    Formula.realize_iInf, Formula.realize_equal, Term.realize_var, Sum.elim_inl,
    Term.realize_varsToConstants, coe_con, presburger.realize_add, presburger.realize_natCast,
    Nat.cast_id, presburger.realize_sum, presburger.realize_nsmul, Sum.elim_inr, smul_eq_mul]
  congr! with a
  simp_rw [Eq.comm (b := x), fun x : t => mul_comm (a x : α -> Nat) x, funext_iff]
  congr! 1 with i
  simp

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_closure_finset, Finset, Finset.univ, Finset.univ_eq_attach, Formula, Formula.iExs, Formula.iInf, Formula.rea, Formula.realize_iExs, Formula.realize_iInf, SetLike, SetLike.mem_coe, Sum.inl, Sum.inr, Term.var, Term.varsToConstants, existsAndEq, isLinearSet_iff, mem_closure_finset
-/
theorem IsLinearSet.definable [Finite α] (hs : IsLinearSet s) : A.Definable presburger s := by
  rw [isLinearSet_iff] at hs
  rcases hs with ⟨v, t, rfl⟩
  refine ⟨Formula.iExs t (Formula.iInf fun i : α =>
    (Term.var (Sum.inl i)).equal
      (Term.varsToConstants
        ((v i : presburger.Term _) + presburger.sum Finset.univ fun x : t =>
          x.1 i • Term.var (Sum.inr (Sum.inr x))))), ?_⟩
  ext x
  simp only [mem_vadd_set, SetLike.mem_coe, AddSubmonoid.mem_closure_finset', Finset.univ_eq_attach,
    nsmul_eq_mul, vadd_eq_add, ↓existsAndEq, true_and, mem_ofPred_eq, Formula.realize_iExs,
    Formula.realize_iInf, Formula.realize_equal, Term.realize_var, Sum.elim_inl,
    Term.realize_varsToConstants, coe_con, presburger.realize_add, presburger.realize_natCast,
    Nat.cast_id, presburger.realize_sum, presburger.realize_nsmul, Sum.elim_inr, smul_eq_mul]
  congr! with a
  simp_rw [Eq.comm (b := x), fun x : t => mul_comm (a x : α -> Nat) x, funext_iff]
  congr! 1 with i
  simp

/--
theorem `IsSemilinearSet.definable` / 定理 `IsSemilinearSet.definable`

English:
theorem IsSemilinearSet.definable
  given: [Finite α] (hs : IsSemilinearSet s)
  proof: by
  rw [isSemilinearSet_iff] at hs
  rcases hs with ⟨S, hS, rfl⟩
  choose φ hφ using fun s : S => (hS s.1 s.2).definable
  refine ⟨Formula.iSup φ, ?_⟩
  ext x
  have := fun s hs x => Set.ext_iff.1 (hφ ⟨s, hs⟩).symm x
  simp only [mem_ofPred_eq] at this
  simp [this]

中文:
定理 IsSemilinearSet.definable
  条件: [有限 α] (hs : IsSemilinearSet s)
  证明: by
  rw [isSemilinearSet_iff] at hs
  rcases hs with ⟨S, hS, rfl⟩
  choose φ hφ using fun s : S => (hS s.1 s.2).definable
  refine ⟨Formula.iSup φ, ?_⟩
  ext x
  have := fun s hs x => Set.ext_iff.1 (hφ ⟨s, hs⟩).symm x
  simp only [mem_ofPred_eq] at this
  simp [this]

Depends on / 依赖: Formula, Formula.iSup, Set.ext_iff, definable, ext_iff, isSemilinearSet_iff, mem_ofPred_eq
-/
theorem IsSemilinearSet.definable [Finite α] (hs : IsSemilinearSet s) :
    A.Definable presburger s := by
  rw [isSemilinearSet_iff] at hs
  rcases hs with ⟨S, hS, rfl⟩
  choose φ hφ using fun s : S => (hS s.1 s.2).definable
  refine ⟨Formula.iSup φ, ?_⟩
  ext x
  have := fun s hs x => Set.ext_iff.1 (hφ ⟨s, hs⟩).symm x
  simp only [mem_ofPred_eq] at this
  simp [this]

namespace FirstOrder.Language.presburger

set_option backward.isDefEq.respectTransparency false in
/--
lemma `term_realize_eq_add_dotProduct` / 引理 `term_realize_eq_add_dotProduct`

English:
lemma term_realize_eq_add_dotProduct
  given: [Fintype α] (t : presburger[[A]].Term α)
  proof: by
  classical
  induction t with simp only [Term.realize]
  | var i =>
    exact ⟨0, Pi.single i 1, by simp⟩
  | @func l f ts ih =>
    cases f with
    | inl f =>
      choose k u ih using ih
      cases f with
      | zero =>
        refine ⟨0, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        simp
      | one =>
        refine ⟨1, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        simp [ih]
      | add =>
        refine ⟨k 0 + k 1, u 0 + u 1, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]; rw [add_dotProduct]; rw [add_left_comm]; rw [add_assoc]; rw [add_left_comm]; rw [← add_assoc]
        simp [ih]
    | inr f =>
      cases l with
      | zero =>
        refine ⟨f, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInr]; rw [zero_dotProduct]; rw [add_zero]
        rfl
      | succ => nomatch f

中文:
引理 term_realize_eq_add_dotProduct
  条件: [有限类型 α] (t : presburger[[A]].项 α)
  证明: by
  classical
  induction t with simp only [Term.realize]
  | var i =>
    exact ⟨0, Pi.single i 1, by simp⟩
  | @func l f ts ih =>
    cases f with
    | inl f =>
      choose k u ih using ih
      cases f with
      | zero =>
        refine ⟨0, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        simp
      | one =>
        refine ⟨1, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        simp [ih]
      | add =>
        refine ⟨k 0 + k 1, u 0 + u 1, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]; rw [add_dotProduct]; rw [add_left_comm]; rw [add_assoc]; rw [add_left_comm]; rw [← add_assoc]
        simp [ih]
    | inr f =>
      cases l with
      | zero =>
        refine ⟨f, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInr]; rw [zero_dotProduct]; rw [add_zero]
        rfl
      | succ => nomatch f

Depends on / 依赖: Pi.single, Term.realize, add_assoc, add_dotProduct, add_left_comm, classical, realize, single, withConstants_funMap_sumInl
-/
lemma term_realize_eq_add_dotProduct [Fintype α] (t : presburger[[A]].Term α) :
    exists (k : Nat) (u : α -> Nat), forall (v : α -> Nat), t.realize v = k + u ⬝ᵥ v := by
  classical
  induction t with simp only [Term.realize]
  | var i =>
    exact ⟨0, Pi.single i 1, by simp⟩
  | @func l f ts ih =>
    cases f with
    | inl f =>
      choose k u ih using ih
      cases f with
      | zero =>
        refine ⟨0, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        simp
      | one =>
        refine ⟨1, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        simp [ih]
      | add =>
        refine ⟨k 0 + k 1, u 0 + u 1, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]; rw [add_dotProduct]; rw [add_left_comm]; rw [add_assoc]; rw [add_left_comm]; rw [← add_assoc]
        simp [ih]
    | inr f =>
      cases l with
      | zero =>
        refine ⟨f, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInr]; rw [zero_dotProduct]; rw [add_zero]
        rfl
      | succ => nomatch f

variable [Finite α]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isSemilinearSet_boundedFormula_realize` / 引理 `isSemilinearSet_boundedFormula_realize`

English:
lemma isSemilinearSet_boundedFormula_realize
  given: {n} (φ : presburger[[A]].BoundedFormula α n)
  proof: by
  have := Fintype.ofFinite α
  induction φ with simp only [BoundedFormula.Realize]
  | equal t₁ t₂ =>
    rcases term_realize_eq_add_dotProduct t₁ with ⟨k₁, u₁, ht₁⟩
    rcases term_realize_eq_add_dotProduct t₂ with ⟨k₂, u₂, ht₂⟩
    convert! Nat.isSemilinearSet_setOfPred_mulVec_eq ![k₁] ![k₂] (.of ![u₁]) (.of ![u₂])
    simp [ht₁, ht₂]
  | rel f => nomatch f
  | falsum => exact .empty
  | imp _ _ ih₁ ih₂ =>
    convert! (ih₂.compl.inter ih₁).compl using 1
    simp [ofPred_inter_eq_sep, imp_iff_not_or, compl_ofPred]
  | @all n φ ih =>
    let e := (Equiv.sumAssoc α (Fin n) (Fin 1)).trans (Equiv.sumCongr (.refl α) finSumFinEquiv)
    rw [← isSemilinearSet_image_iff (LinearEquiv.funCongrLeft Nat Nat e)] at ih
    convert! ih.compl.proj.compl using 1
    simp_rw [compl_ofPred, not_exists, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi,
      mem_compl_iff, mem_image, not_not, ← LinearEquiv.eq_symm_apply, LinearEquiv.funCongrLeft_symm,
      exists_eq_right, mem_ofPred, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr! 4
    ext i
    cases i using Fin.lastCases <;> simp [e]

中文:
引理 isSemilinearSet_boundedFormula_realize
  条件: {n} (φ : presburger[[A]].BoundedFormula α n)
  证明: by
  have := Fintype.ofFinite α
  induction φ with simp only [BoundedFormula.Realize]
  | equal t₁ t₂ =>
    rcases term_realize_eq_add_dotProduct t₁ with ⟨k₁, u₁, ht₁⟩
    rcases term_realize_eq_add_dotProduct t₂ with ⟨k₂, u₂, ht₂⟩
    convert! Nat.isSemilinearSet_setOfPred_mulVec_eq ![k₁] ![k₂] (.of ![u₁]) (.of ![u₂])
    simp [ht₁, ht₂]
  | rel f => nomatch f
  | falsum => exact .empty
  | imp _ _ ih₁ ih₂ =>
    convert! (ih₂.compl.inter ih₁).compl using 1
    simp [ofPred_inter_eq_sep, imp_iff_not_or, compl_ofPred]
  | @all n φ ih =>
    let e := (Equiv.sumAssoc α (Fin n) (Fin 1)).trans (Equiv.sumCongr (.refl α) finSumFinEquiv)
    rw [← isSemilinearSet_image_iff (LinearEquiv.funCongrLeft Nat Nat e)] at ih
    convert! ih.compl.proj.compl using 1
    simp_rw [compl_ofPred, not_exists, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi,
      mem_compl_iff, mem_image, not_not, ← LinearEquiv.eq_symm_apply, LinearEquiv.funCongrLeft_symm,
      exists_eq_right, mem_ofPred, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr! 4
    ext i
    cases i using Fin.lastCases <;> simp [e]

Depends on / 依赖: BoundedFormula, BoundedFormula.Realize, Fintype, Fintype.ofFinite, Nat.isSemilinearSet_setOfPred_mulVec_eq, Realize, compl.inter, compl_ofPred, convert, falsum, imp_iff_not_or, isSemilinearSet_setOfPred_mulVec_eq, nomatch, ofFinite, ofPred_inter_eq_sep, term_realize_eq_add_dotProduct
-/
lemma isSemilinearSet_boundedFormula_realize {n} (φ : presburger[[A]].BoundedFormula α n) :
    IsSemilinearSet {v : α oplus Fin n -> Nat | φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr)} := by
  have := Fintype.ofFinite α
  induction φ with simp only [BoundedFormula.Realize]
  | equal t₁ t₂ =>
    rcases term_realize_eq_add_dotProduct t₁ with ⟨k₁, u₁, ht₁⟩
    rcases term_realize_eq_add_dotProduct t₂ with ⟨k₂, u₂, ht₂⟩
    convert! Nat.isSemilinearSet_setOfPred_mulVec_eq ![k₁] ![k₂] (.of ![u₁]) (.of ![u₂])
    simp [ht₁, ht₂]
  | rel f => nomatch f
  | falsum => exact .empty
  | imp _ _ ih₁ ih₂ =>
    convert! (ih₂.compl.inter ih₁).compl using 1
    simp [ofPred_inter_eq_sep, imp_iff_not_or, compl_ofPred]
  | @all n φ ih =>
    let e := (Equiv.sumAssoc α (Fin n) (Fin 1)).trans (Equiv.sumCongr (.refl α) finSumFinEquiv)
    rw [← isSemilinearSet_image_iff (LinearEquiv.funCongrLeft Nat Nat e)] at ih
    convert! ih.compl.proj.compl using 1
    simp_rw [compl_ofPred, not_exists, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi,
      mem_compl_iff, mem_image, not_not, ← LinearEquiv.eq_symm_apply, LinearEquiv.funCongrLeft_symm,
      exists_eq_right, mem_ofPred, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr! 4
    ext i
    cases i using Fin.lastCases <;> simp [e]

/--
lemma `isSemilinearSet_formula_realize_semilinear` / 引理 `isSemilinearSet_formula_realize_semilinear`

English:
lemma isSemilinearSet_formula_realize_semilinear
  given: (φ : presburger[[A]].Formula α)
  proof: by
  let e := Equiv.sumEmpty α (Fin 0)
  convert! (isSemilinearSet_boundedFormula_realize φ).image (LinearMap.funLeft Nat Nat e.symm)
  ext x
  simp only [mem_ofPred_eq, mem_image]
  rw [(e.arrowCongr (.refl Nat)).exists_congr_left]
  simp [Formula.Realize, Unique.eq_default, Function.comp_def, LinearMap.funLeft, e]

中文:
引理 isSemilinearSet_formula_realize_semilinear
  条件: (φ : presburger[[A]].公式 α)
  证明: by
  let e := Equiv.sumEmpty α (Fin 0)
  convert! (isSemilinearSet_boundedFormula_realize φ).image (LinearMap.funLeft Nat Nat e.symm)
  ext x
  simp only [mem_ofPred_eq, mem_image]
  rw [(e.arrowCongr (.refl Nat)).exists_congr_left]
  simp [Formula.Realize, Unique.eq_default, Function.comp_def, LinearMap.funLeft, e]

Depends on / 依赖: Equiv.sumEmpty, Formula, Formula.Realize, Function, Function.comp_def, LinearMap, LinearMap.funLeft, Realize, Unique, Unique.eq_default, arrowCongr, comp_def, convert, e.arrowCongr, e.symm, eq_default, exists_congr_left, funLeft, isSemilinearSet_boundedFormula_realize, mem_image
-/
lemma isSemilinearSet_formula_realize_semilinear (φ : presburger[[A]].Formula α) :
    IsSemilinearSet (Set.ofPred φ.Realize : Set (α -> Nat)) := by
  let e := Equiv.sumEmpty α (Fin 0)
  convert! (isSemilinearSet_boundedFormula_realize φ).image (LinearMap.funLeft Nat Nat e.symm)
  ext x
  simp only [mem_ofPred_eq, mem_image]
  rw [(e.arrowCongr (.refl Nat)).exists_congr_left]
  simp [Formula.Realize, Unique.eq_default, Function.comp_def, LinearMap.funLeft, e]

/--
theorem `definable_iff_isSemilinearSet` / 定理 `definable_iff_isSemilinearSet`

English:
theorem definable_iff_isSemilinearSet
  given: {s : Set (α -> Nat)}
  proof: ⟨fun ⟨φ, hφ⟩ => hφ ▸ isSemilinearSet_formula_realize_semilinear φ, IsSemilinearSet.definable⟩

中文:
定理 definable_iff_isSemilinearSet
  条件: {s : 集合 (α -> 自然数)}
  证明: ⟨fun ⟨φ, hφ⟩ => hφ ▸ isSemilinearSet_formula_realize_semilinear φ, IsSemilinearSet.definable⟩

Depends on / 依赖: IsSemilinearSet, IsSemilinearSet.definable, definable, isSemilinearSet_formula_realize_semilinear
-/
theorem definable_iff_isSemilinearSet {s : Set (α -> Nat)} :
    A.Definable presburger s ↔ IsSemilinearSet s :=
  ⟨fun ⟨φ, hφ⟩ => hφ ▸ isSemilinearSet_formula_realize_semilinear φ, IsSemilinearSet.definable⟩

/--
theorem `definable₁_iff_ultimately_periodic` / 定理 `definable₁_iff_ultimately_periodic`

English:
theorem definable₁_iff_ultimately_periodic
  given: {s : Set Nat}
  proof: by
  rw [Definable₁]; rw [definable_iff_isSemilinearSet]; rw [← isSemilinearSet_image_iff (LinearEquiv.funUnique (Fin 1) Nat Nat)]; rw [← preimage_ofPred_eq]
  simp only [LinearEquiv.funUnique_apply, Function.eval, Fin.default_eq_zero, ofPred_mem_eq]
  rw [image_preimage_eq s fun x => ⟨![x], rfl⟩, Nat.isSemilinearSet_iff_ultimately_periodic]

中文:
定理 definable₁_iff_ultimately_periodic
  条件: {s : 集合 自然数}
  证明: by
  rw [Definable₁]; rw [definable_iff_isSemilinearSet]; rw [← isSemilinearSet_image_iff (LinearEquiv.funUnique (Fin 1) Nat Nat)]; rw [← preimage_ofPred_eq]
  simp only [LinearEquiv.funUnique_apply, Function.eval, Fin.default_eq_zero, ofPred_mem_eq]
  rw [image_preimage_eq s fun x => ⟨![x], rfl⟩, Nat.isSemilinearSet_iff_ultimately_periodic]

Depends on / 依赖: Fin.default_eq_zero, Function, Function.eval, LinearEquiv, LinearEquiv.funUnique, LinearEquiv.funUnique_apply, Nat.isSemilinearSet_iff_ultimately_periodic, default_eq_zero, definable_iff_isSemilinearSet, funUnique, funUnique_apply, image_preimage_eq, isSemilinearSet_iff_ultimately_periodic, isSemilinearSet_image_iff, ofPred_mem_eq, preimage_ofPred_eq
-/
theorem definable₁_iff_ultimately_periodic {s : Set Nat} :
    A.Definable₁ presburger s ↔ exists k, exists p > 0, forall x >= k, x in s ↔ x + p in s := by
  rw [Definable₁]; rw [definable_iff_isSemilinearSet]; rw [← isSemilinearSet_image_iff (LinearEquiv.funUnique (Fin 1) Nat Nat)]; rw [← preimage_ofPred_eq]
  simp only [LinearEquiv.funUnique_apply, Function.eval, Fin.default_eq_zero, ofPred_mem_eq]
  rw [image_preimage_eq s fun x => ⟨![x], rfl⟩, Nat.isSemilinearSet_iff_ultimately_periodic]

/--
theorem `mul_not_definable` / 定理 `mul_not_definable`

English:
theorem mul_not_definable
  statement: ¬ A.Definable presburger {v : Fin 3 -> Nat | v 0 = v 1 * v 2}
  proof: by
  intro hmul
  have hsqr : A.Definable₁ presburger {x * x | x : Nat} := by
    rw [Definable₁]
    convert! (hmul.preimage_comp (β := Fin 2) ![0, 1, 1]).image_comp ![0]
    ext
    simpa [funext_iff, Fin.exists_fin_succ_pi] using exists_congr fun _ => Eq.comm
  rw [definable₁_iff_ultimately_periodic] at hsqr
  rcases hsqr with ⟨k, p, hp, h⟩
  specialize h ((max k p) * (max k p)) ((Nat.le_mul_self _).trans' (le_max_left _ _))
  simp only [mem_ofPred_eq, exists_apply_eq_apply, true_iff] at h
  rcases h with ⟨x, h₁⟩
  by_cases h₂ : x <= max k p
  · apply Nat.mul_self_le_mul_self at h₂
    grind
  · simp only [not_le, Nat.lt_iff_add_one_le] at h₂
    apply Nat.mul_self_le_mul_self at h₂
    grind

中文:
定理 mul_not_definable
  结论: ¬ A.Definable presburger {v : 有限集 3 -> 自然数 | v 0 = v 1 * v 2}
  证明: by
  intro hmul
  have hsqr : A.Definable₁ presburger {x * x | x : Nat} := by
    rw [Definable₁]
    convert! (hmul.preimage_comp (β := Fin 2) ![0, 1, 1]).image_comp ![0]
    ext
    simpa [funext_iff, Fin.exists_fin_succ_pi] using exists_congr fun _ => Eq.comm
  rw [definable₁_iff_ultimately_periodic] at hsqr
  rcases hsqr with ⟨k, p, hp, h⟩
  specialize h ((max k p) * (max k p)) ((Nat.le_mul_self _).trans' (le_max_left _ _))
  simp only [mem_ofPred_eq, exists_apply_eq_apply, true_iff] at h
  rcases h with ⟨x, h₁⟩
  by_cases h₂ : x <= max k p
  · apply Nat.mul_self_le_mul_self at h₂
    grind
  · simp only [not_le, Nat.lt_iff_add_one_le] at h₂
    apply Nat.mul_self_le_mul_self at h₂
    grind

Depends on / 依赖: A.Definable, Eq.comm, Fin.exists_fin_succ_pi, Nat.le_mul_self, convert, exists_apply_eq_apply, exists_congr, exists_fin_succ_pi, funext_iff, hmul.preimage_comp, image_comp, le_max_left, le_mul_self, mem_ofPred_eq, preimage_comp, presburger, specialize, true_iff
-/
theorem mul_not_definable : ¬ A.Definable presburger {v : Fin 3 -> Nat | v 0 = v 1 * v 2} := by
  intro hmul
  have hsqr : A.Definable₁ presburger {x * x | x : Nat} := by
    rw [Definable₁]
    convert! (hmul.preimage_comp (β := Fin 2) ![0, 1, 1]).image_comp ![0]
    ext
    simpa [funext_iff, Fin.exists_fin_succ_pi] using exists_congr fun _ => Eq.comm
  rw [definable₁_iff_ultimately_periodic] at hsqr
  rcases hsqr with ⟨k, p, hp, h⟩
  specialize h ((max k p) * (max k p)) ((Nat.le_mul_self _).trans' (le_max_left _ _))
  simp only [mem_ofPred_eq, exists_apply_eq_apply, true_iff] at h
  rcases h with ⟨x, h₁⟩
  by_cases h₂ : x <= max k p
  · apply Nat.mul_self_le_mul_self at h₂
    grind
  · simp only [not_le, Nat.lt_iff_add_one_le] at h₂
    apply Nat.mul_self_le_mul_self at h₂
    grind

end FirstOrder.Language.presburger
