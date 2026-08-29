/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Quotients
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.Ultrafilter.Defs

/-!
# Ultraproducts and Łoś's Theorem

## Main Definitions

- `FirstOrder.Language.Ultraproduct.Structure` is the ultraproduct structure on `Filter.Product`.

## Main Results

- Łoś's Theorem: `FirstOrder.Language.Ultraproduct.sentence_realize`. An ultraproduct models a
  sentence `φ` if and only if the set of structures in the product that model `φ` is in the
  ultrafilter.

## Tags

ultraproduct, Los's theorem
-/

public section

universe u v

variable {α : Type*} (M : α -> Type*) (u : Ultrafilter α)

open FirstOrder Filter

namespace FirstOrder

namespace Language

open Structure

variable {L : Language.{u, v}} [forall a, L.Structure (M a)]

namespace Ultraproduct

/--
Instance `setoidPrestructure` / 实例 `setoidPrestructure`

English:
instance setoidPrestructure
  signature: : L.Prestructure ((u : Filter α).productSetoid M)
  body: { (u : Filter α).productSetoid M with
    toStructure :=
      { funMap := fun {_} f x a => funMap f fun i => x i a
        RelMap := fun {_} r x => forallᶠ a : α in u, RelMap r fun i => x i a }
    fun_equiv := fun {n} f x y xy => by
      refine mem_of_superset (iInter_mem.2 xy) fun a ha => ?_
   

中文:
实例 setoidPrestructure
  签名: : L.Prestructure ((u : Filter α).productSetoid M)
  定义体: { (u : Filter α).productSetoid M with
    toStructure :=
      { funMap := fun {_} f x a => funMap f fun i => x i a
        RelMap := fun {_} r x => forallᶠ a : α in u, RelMap r fun i => x i a }
    fun_equiv := fun {n} f x y xy => by
      refine mem_of_superset (iInter_mem.2 xy) fun a ha => ?_
   

Depends on / 依赖: Filter, RelMap, Set.mem_iInter, Set.mem_ofPred_eq, funMap, fun_equiv, iInter_mem, iff_eq_eq, inter_mem, mem_iInter, mem_ofPred_eq, mem_of_superset, productSetoid, rel_equiv, toStructure
-/
instance setoidPrestructure : L.Prestructure ((u : Filter α).productSetoid M) :=
  { (u : Filter α).productSetoid M with
    toStructure :=
      { funMap := fun {_} f x a => funMap f fun i => x i a
        RelMap := fun {_} r x => forallᶠ a : α in u, RelMap r fun i => x i a }
    fun_equiv := fun {n} f x y xy => by
      refine mem_of_superset (iInter_mem.2 xy) fun a ha => ?_
      simp only [Set.mem_iInter, Set.mem_ofPred_eq] at ha
      simp only [Set.mem_ofPred_eq, ha]
    rel_equiv := fun {n} r x y xy => by
      rw [← iff_eq_eq]
      refine ⟨fun hx => ?_, fun hy => ?_⟩
      · refine mem_of_superset (inter_mem hx (iInter_mem.2 xy)) ?_
        rintro a ⟨ha1, ha2⟩
        simp only [Set.mem_iInter, Set.mem_ofPred_eq] at *
        rw [← funext ha2]
        exact ha1
      · refine mem_of_superset (inter_mem hy (iInter_mem.2 xy)) ?_
        rintro a ⟨ha1, ha2⟩
        simp only [Set.mem_iInter, Set.mem_ofPred_eq] at *
        rw [funext ha2]
        exact ha1 }

variable {M} {u}

/--
Instance `«structure»` / 实例 `«structure»`

English:
instance «structure»
  signature: : L.Structure ((u : Filter α).Product M)
  body: inferInstanceAs L.Structure (Quotient _)

中文:
实例 «structure»
  签名: : L.Structure ((u : Filter α).Product M)
  定义体: inferInstanceAs L.Structure (Quotient _)

Depends on / 依赖: L.Structure, Quotient, Structure
-/
instance «structure» : L.Structure ((u : Filter α).Product M) :=
inferInstanceAs L.Structure (Quotient _)

/--
theorem `funMap_cast` / 定理 `funMap_cast`

English:
theorem funMap_cast
  given: {n : Nat} (f : L.Functions n) (x : Fin n -> forall a, M a)
  proof: by
  apply funMap_quotient_mk'

中文:
定理 funMap_cast
  条件: {n : 自然数} (f : L.Functions n) (x : Fin n -> 对任意 a, M a)
  证明: by
  apply funMap_quotient_mk'

Depends on / 依赖: funMap_quotient_mk
-/
theorem funMap_cast {n : Nat} (f : L.Functions n) (x : Fin n -> forall a, M a) :
    (funMap f fun i => (x i : (u : Filter α).Product M)) =
      (fun a => funMap f fun i => x i a : (u : Filter α).Product M) := by
  apply funMap_quotient_mk'

/--
theorem `term_realize_cast` / 定理 `term_realize_cast`

English:
theorem term_realize_cast
  given: {β : Type*} (x : β -> forall a, M a) (t : L.Term β)
  proof: by
  convert!
    @Term.realize_quotient_mk' L _ ((u : Filter α).productSetoid M)
      (Ultraproduct.setoidPrestructure M u) _ t x using 2
  ext a
  induction t with
  | var => rfl
  | func _ _ t_ih => simp only [Term.realize, t_ih]; rfl

中文:
定理 term_realize_cast
  条件: {β : 类型} (x : β -> 对任意 a, M a) (t : L.Term β)
  证明: by
  convert!
    @Term.realize_quotient_mk' L _ ((u : Filter α).productSetoid M)
      (Ultraproduct.setoidPrestructure M u) _ t x using 2
  ext a
  induction t with
  | var => rfl
  | func _ _ t_ih => simp only [Term.realize, t_ih]; rfl

Depends on / 依赖: Filter, Term.realize, Term.realize_quotient_mk, Ultraproduct, Ultraproduct.setoidPrestructure, convert, productSetoid, realize, realize_quotient_mk, setoidPrestructure, t_ih
-/
theorem term_realize_cast {β : Type*} (x : β -> forall a, M a) (t : L.Term β) :
    (t.realize fun i => (x i : (u : Filter α).Product M)) =
      (fun a => t.realize fun i => x i a : (u : Filter α).Product M) := by
  convert!
    @Term.realize_quotient_mk' L _ ((u : Filter α).productSetoid M)
      (Ultraproduct.setoidPrestructure M u) _ t x using 2
  ext a
  induction t with
  | var => rfl
  | func _ _ t_ih => simp only [Term.realize, t_ih]; rfl

variable [forall a : α, Nonempty (M a)]

/--
theorem `boundedFormula_realize_cast` / 定理 `boundedFormula_realize_cast`

English:
theorem boundedFormula_realize_cast
  statement: {β : Type*} {n : Nat} (φ : L.BoundedFormula β n)
  proof: by
  induction φ with
  | falsum => simp only [BoundedFormula.Realize, eventually_const]
  | equal =>
    have h2 : forall a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [Boun

中文:
定理 boundedFormula_realize_cast
  结论: {β : 类型} {n : 自然数} (φ : L.BoundedFormula β n)
  证明: by
  induction φ with
  | falsum => simp only [BoundedFormula.Realize, eventually_const]
  | equal =>
    have h2 : forall a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [Boun

Depends on / 依赖: BoundedFormula, BoundedFormula.Realize, Filter, Product, Quotient, Quotient.eq, Realize, Sum.casesOn, Sum.comp_elim, Sum.elim, casesOn, comp_elim, eventually_const, falsum, term_realize_cast
-/
theorem boundedFormula_realize_cast {β : Type*} {n : Nat} (φ : L.BoundedFormula β n)
    (x : β -> forall a, M a) (v : Fin n -> forall a, M a) :
    (φ.Realize (fun i : β => (x i : (u : Filter α).Product M))
        (fun i => (v i : (u : Filter α).Product M))) ↔
      forallᶠ a : α in u, φ.Realize (fun i : β => x i a) fun i => v i a := by
  induction φ with
  | falsum => simp only [BoundedFormula.Realize, eventually_const]
  | equal =>
    have h2 : forall a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [BoundedFormula.Realize, h2]
    erw [(Sum.comp_elim ((↑) : (forall a, M a) -> (u : Filter α).Product M) x v).symm,
      term_realize_cast, term_realize_cast]
    exact Quotient.eq''
  | rel =>
    have h2 : forall a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [BoundedFormula.Realize, h2]
    erw [(Sum.comp_elim ((↑) : (forall a, M a) -> (u : Filter α).Product M) x v).symm]
    conv_lhs => enter [2, i]; erw [term_realize_cast]
    apply relMap_quotient_mk'
  | imp _ _ ih ih' =>
    simp only [BoundedFormula.Realize, ih v, ih' v]
    rw [Ultrafilter.eventually_imp]
  | @all k φ ih =>
    simp only [BoundedFormula.Realize]
    apply Iff.trans (b := forall m : forall a : α, M a,
      φ.Realize (fun i : β => (x i : (u : Filter α).Product M))
        (Fin.snoc (((↑) : (forall a, M a) -> (u : Filter α).Product M) ∘ v)
          (m : (u : Filter α).Product M)))
    · exact Quotient.forall
    have h' :
      forall (m : forall a, M a) (a : α),
        (fun i : Fin (k + 1) => (Fin.snoc v m : _ -> forall a, M a) i a) =
          Fin.snoc (fun i : Fin k => v i a) (m a) := by
      refine fun m a => funext (Fin.reverseInduction ?_ fun i _ => ?_)
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc]
    simp only [← Fin.comp_snoc]
    simp only [Function.comp_def, ih, h']
    refine ⟨fun h => ?_, fun h m => ?_⟩
    · contrapose! h
      refine
        ⟨fun a : α =>
          Classical.epsilon fun m : M a =>
            ¬φ.Realize (fun i => x i a) (Fin.snoc (fun i => v i a) m),
          ?_⟩
      exact Filter.mem_of_superset h fun a ha => Classical.epsilon_spec ha
    · rw [Filter.eventually_iff] at *
      exact Filter.mem_of_superset h fun a ha => ha (m a)

/--
theorem `realize_formula_cast` / 定理 `realize_formula_cast`

English:
theorem realize_formula_cast
  given: {β : Type*} (φ : L.Formula β) (x : β -> forall a, M a)
  proof: by
  simp_rw [Formula.Realize, ← boundedFormula_realize_cast φ x, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)

中文:
定理 realize_formula_cast
  条件: {β : 类型} (φ : L.Formula β) (x : β -> 对任意 a, M a)
  证明: by
  simp_rw [Formula.Realize, ← boundedFormula_realize_cast φ x, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)

Depends on / 依赖: Formula, Formula.Realize, Realize, Subsingleton, Subsingleton.elim, boundedFormula_realize_cast, iff_eq_eq, simp_rw
-/
theorem realize_formula_cast {β : Type*} (φ : L.Formula β) (x : β -> forall a, M a) :
    (φ.Realize fun i => (x i : (u : Filter α).Product M)) ↔
      forallᶠ a : α in u, φ.Realize fun i => x i a := by
  simp_rw [Formula.Realize, ← boundedFormula_realize_cast φ x, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)

/--
theorem `sentence_realize` / 定理 `sentence_realize`

English:
theorem sentence_realize
  given: (φ : L.Sentence)
  proof: by
  simp_rw [Sentence.Realize]
  rw [← realize_formula_cast φ]; rw [iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)

nonrec instance Product.instNonempty : Nonempty ((u : Filter α).Product M) :=
  letI : forall a, Inhabited (M a) := fun _ => Classical.inhabited_of_nonempty'
  inferInstance

中文:
定理 sentence_realize
  条件: (φ : L.Sentence)
  证明: by
  simp_rw [Sentence.Realize]
  rw [← realize_formula_cast φ]; rw [iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)

nonrec instance Product.instNonempty : Nonempty ((u : Filter α).Product M) :=
  letI : forall a, Inhabited (M a) := fun _ => Classical.inhabited_of_nonempty'
  inferInstance

Depends on / 依赖: Realize, Sentence, Sentence.Realize, Subsingleton, Subsingleton.elim, iff_eq_eq, realize_formula_cast, simp_rw
-/
theorem sentence_realize (φ : L.Sentence) :
    (u : Filter α).Product M ⊨ φ ↔ forallᶠ a : α in u, M a ⊨ φ := by
  simp_rw [Sentence.Realize]
  rw [← realize_formula_cast φ]; rw [iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)

nonrec instance Product.instNonempty : Nonempty ((u : Filter α).Product M) :=
  letI : forall a, Inhabited (M a) := fun _ => Classical.inhabited_of_nonempty'
  inferInstance

end Ultraproduct

end Language

end FirstOrder
