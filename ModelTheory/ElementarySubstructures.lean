/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.ElementaryMaps
public import Mathlib.ModelTheory.Definability

/-!
# Elementary Substructures

## Main Definitions

- A `FirstOrder.Language.ElementarySubstructure` is a substructure where the realization of each
  formula agrees with the realization in the larger model.

## Main Results

- The Tarski-Vaught Test for substructures:
  `FirstOrder.Language.Substructure.isElementary_of_exists` gives a simple criterion for a
  substructure to be elementary.
-/

@[expose] public section


open FirstOrder

namespace FirstOrder

namespace Language

open Structure

variable {L : Language} {M : Type*} [L.Structure M]

/--
Definition of `Substructure.IsElementary` / `Substructure.IsElementary` 的定义

English:
definition Substructure.IsElementary
  signature: (S : L.Substructure M)
  body: forall ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n -> S), φ.Realize (((↑) : _ -> M) ∘ x) ↔ φ.Realize x

中文:
定义 子结构.IsElementary
  签名: (S : L.子结构 M)
  定义体: forall ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n -> S), φ.Realize (((↑) : _ -> M) ∘ x) ↔ φ.Realize x

Depends on / 依赖: Formula, L.Formula, Realize
-/
def Substructure.IsElementary (S : L.Substructure M) : Prop :=
  forall ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n -> S), φ.Realize (((↑) : _ -> M) ∘ x) ↔ φ.Realize x

variable (L M)

/--
Definition of `ElementarySubstructure` / `ElementarySubstructure` 的定义

English:
structure ElementarySubstructure
  parameters: where
  axioms and operations (2):
    - toSubstructure : L.Substructure M
    - isElementary' : toSubstructure.IsElementary

中文:
结构 ElementarySubstructure
  参数: where
  公理与运算 (2 个):
    - toSubstructure : L.子结构 M
    - isElementary' : toSubstructure.IsElementary
-/
structure ElementarySubstructure where
  /-- The underlying substructure -/
  toSubstructure : L.Substructure M
  isElementary' : toSubstructure.IsElementary

variable {L M}

namespace ElementarySubstructure

attribute [coe] toSubstructure

/--
Instance `instCoe` / 实例 `instCoe`

English:
instance instCoe
  signature: : Coe (L.ElementarySubstructure M) (L.Substructure M)
  body: ⟨ElementarySubstructure.toSubstructure⟩

中文:
实例 instCoe
  签名: : Coe (L.ElementarySubstructure M) (L.子结构 M)
  定义体: ⟨ElementarySubstructure.toSubstructure⟩

Depends on / 依赖: ElementarySubstructure, ElementarySubstructure.toSubstructure, toSubstructure
-/
instance instCoe : Coe (L.ElementarySubstructure M) (L.Substructure M) :=
  ⟨ElementarySubstructure.toSubstructure⟩

/--
Instance `instSetLike` / 实例 `instSetLike`

English:
instance instSetLike
  signature: : SetLike (L.ElementarySubstructure M) M
  body: ⟨fun x => x.toSubstructure.carrier, fun ⟨⟨s, hs1⟩, hs2⟩ ⟨⟨t, ht1⟩, _⟩ _ => by
    congr⟩

中文:
实例 instSetLike
  签名: : 集合状 (L.ElementarySubstructure M) M
  定义体: ⟨fun x => x.toSubstructure.carrier, fun ⟨⟨s, hs1⟩, hs2⟩ ⟨⟨t, ht1⟩, _⟩ _ => by
    congr⟩

Depends on / 依赖: carrier, toSubstructure, x.toSubstructure.carrier
-/
instance instSetLike : SetLike (L.ElementarySubstructure M) M :=
  ⟨fun x => x.toSubstructure.carrier, fun ⟨⟨s, hs1⟩, hs2⟩ ⟨⟨t, ht1⟩, _⟩ _ => by
    congr⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (L.ElementarySubstructure M)
  body: .ofSetLike (L.ElementarySubstructure M) M

中文:
实例 :
  签名: 偏序 (L.ElementarySubstructure M)
  定义体: .ofSetLike (L.ElementarySubstructure M) M

Depends on / 依赖: ElementarySubstructure, L.ElementarySubstructure, ofSetLike
-/
instance : PartialOrder (L.ElementarySubstructure M) := .ofSetLike (L.ElementarySubstructure M) M

/--
Instance `inducedStructure` / 实例 `inducedStructure`

English:
instance inducedStructure
  signature: (S : L.ElementarySubstructure M)
  body: Substructure.inducedStructure

@[simp]

中文:
实例 inducedStructure
  签名: (S : L.ElementarySubstructure M)
  定义体: Substructure.inducedStructure

@[simp]

Depends on / 依赖: Substructure, Substructure.inducedStructure, inducedStructure
-/
instance inducedStructure (S : L.ElementarySubstructure M) : L.Structure S :=
  Substructure.inducedStructure

@[simp]
/--
theorem `isElementary` / 定理 `isElementary`

English:
theorem isElementary
  given: (S : L.ElementarySubstructure M)
  statement: (S : L.Substructure M).IsElementary
  proof: S.isElementary'

中文:
定理 isElementary
  条件: (S : L.ElementarySubstructure M)
  结论: (S : L.子结构 M).IsElementary
  证明: S.isElementary'

Depends on / 依赖: S.isElementary, isElementary
-/
theorem isElementary (S : L.ElementarySubstructure M) : (S : L.Substructure M).IsElementary :=
  S.isElementary'

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (S : L.ElementarySubstructure M)
  body: (↑)
  map_formula' := S.isElementary

@[simp]

中文:
定义 subtype
  签名: (S : L.ElementarySubstructure M)
  定义体: (↑)
  map_formula' := S.isElementary

@[simp]
-/
def subtype (S : L.ElementarySubstructure M) : S ↪ₑ[L] M where
  toFun := (↑)
  map_formula' := S.isElementary

@[simp]
/--
theorem `subtype_apply` / 定理 `subtype_apply`

English:
theorem subtype_apply
  given: {S : L.ElementarySubstructure M} {x : S}
  statement: subtype S x = x
  proof: rfl

中文:
定理 subtype_apply
  条件: {S : L.ElementarySubstructure M} {x : S}
  结论: subtype S x = x
  证明: rfl
-/
theorem subtype_apply {S : L.ElementarySubstructure M} {x : S} : subtype S x = x :=
  rfl

/--
theorem `subtype_injective` / 定理 `subtype_injective`

English:
theorem subtype_injective
  given: (S : L.ElementarySubstructure M)
  statement: Function.Injective (subtype S)
  proof: Subtype.coe_injective

@[simp]

中文:
定理 subtype_injective
  条件: (S : L.ElementarySubstructure M)
  结论: 函数.单射 (subtype S)
  证明: Subtype.coe_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem subtype_injective (S : L.ElementarySubstructure M) : Function.Injective (subtype S) :=
  Subtype.coe_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  given: (S : L.ElementarySubstructure M)
  statement: ⇑S.subtype = Subtype.val
  proof: rfl

中文:
定理 coe_subtype
  条件: (S : L.ElementarySubstructure M)
  结论: ⇑S.subtype = 子类型.val
  证明: rfl
-/
theorem coe_subtype (S : L.ElementarySubstructure M) : ⇑S.subtype = Subtype.val :=
  rfl

/--
Instance `instTop` / 实例 `instTop`

English:
instance instTop
  signature: : Top (L.ElementarySubstructure M)
  body: ⟨⟨⊤, fun _ _ _ => Substructure.realize_formula_top.symm⟩⟩

中文:
实例 instTop
  签名: : 顶元素 (L.ElementarySubstructure M)
  定义体: ⟨⟨⊤, fun _ _ _ => Substructure.realize_formula_top.symm⟩⟩

Depends on / 依赖: Substructure, Substructure.realize_formula_top.symm, realize_formula_top
-/
instance instTop : Top (L.ElementarySubstructure M) :=
  ⟨⟨⊤, fun _ _ _ => Substructure.realize_formula_top.symm⟩⟩

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (L.ElementarySubstructure M)
  body: ⟨⊤⟩

@[simp]

中文:
实例 instInhabited
  签名: : 可居 (L.ElementarySubstructure M)
  定义体: ⟨⊤⟩

@[simp]

Depends on / 依赖: Filter, Filter.ext, Set.Subset.rfl, SetRel, SetRel.preimage_comp, SetRel.preimage_mono, Subset, mem_rcomap, preimage, preimage_comp, preimage_mono, s.preimage
-/
instance instInhabited : Inhabited (L.ElementarySubstructure M) :=
  ⟨⊤⟩

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: (x : M)
  statement: x in (⊤ : L.ElementarySubstructure M)
  proof: Set.mem_univ x

@[simp]

中文:
定理 mem_top
  条件: (x : M)
  结论: x in (⊤ : L.ElementarySubstructure M)
  证明: Set.mem_univ x

@[simp]

Depends on / 依赖: Set.mem_univ, _rcomap, mem_univ, rcomap
-/
theorem mem_top (x : M) : x in (⊤ : L.ElementarySubstructure M) :=
  Set.mem_univ x

@[simp]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : L.ElementarySubstructure M) : Set M) = Set.univ
  proof: rfl

@[simp]

中文:
定理 coe_top
  结论: ((⊤ : L.ElementarySubstructure M) : 集合 M) = 集合.univ
  证明: rfl

@[simp]
-/
theorem coe_top : ((⊤ : L.ElementarySubstructure M) : Set M) = Set.univ :=
  rfl

@[simp]
/--
theorem `realize_sentence` / 定理 `realize_sentence`

English:
theorem realize_sentence
  given: (S : L.ElementarySubstructure M) (φ : L.Sentence)
  statement: S ⊨ φ ↔ M ⊨ φ
  proof: S.subtype.map_sentence φ

@[simp]

中文:
定理 realize_sentence
  条件: (S : L.ElementarySubstructure M) (φ : L.Sentence)
  结论: S ⊨ φ ↔ M ⊨ φ
  证明: S.subtype.map_sentence φ

@[simp]

Depends on / 依赖: S.subtype.map_sentence, map_sentence, subtype
-/
theorem realize_sentence (S : L.ElementarySubstructure M) (φ : L.Sentence) : S ⊨ φ ↔ M ⊨ φ :=
  S.subtype.map_sentence φ

@[simp]
/--
theorem `theory_model_iff` / 定理 `theory_model_iff`

English:
theorem theory_model_iff
  given: (S : L.ElementarySubstructure M) (T : L.Theory)
  statement: S ⊨ T ↔ M ⊨ T
  proof: by
  simp only [Theory.model_iff, realize_sentence]

中文:
定理 theory_model_iff
  条件: (S : L.ElementarySubstructure M) (T : L.Theory)
  结论: S ⊨ T ↔ M ⊨ T
  证明: by
  simp only [Theory.model_iff, realize_sentence]

Depends on / 依赖: Theory, Theory.model_iff, model_iff, realize_sentence
-/
theorem theory_model_iff (S : L.ElementarySubstructure M) (T : L.Theory) : S ⊨ T ↔ M ⊨ T := by
  simp only [Theory.model_iff, realize_sentence]

/--
Instance `theory_model` / 实例 `theory_model`

English:
instance theory_model
  signature: {T : L.Theory} [h : M ⊨ T] {S : L.ElementarySubstructure M}
  body: (theory_model_iff S T).2 h

中文:
实例 theory_model
  签名: {T : L.Theory} [h : M ⊨ T] {S : L.ElementarySubstructure M}
  定义体: (theory_model_iff S T).2 h

Depends on / 依赖: theory_model_iff
-/
instance theory_model {T : L.Theory} [h : M ⊨ T] {S : L.ElementarySubstructure M} : S ⊨ T :=
  (theory_model_iff S T).2 h

/--
Instance `instNonempty` / 实例 `instNonempty`

English:
instance instNonempty
  signature: [Nonempty M] {S : L.ElementarySubstructure M}
  body: (model_nonemptyTheory_iff L).1 inferInstance

中文:
实例 instNonempty
  签名: [非空 M] {S : L.ElementarySubstructure M}
  定义体: (model_nonemptyTheory_iff L).1 inferInstance

Depends on / 依赖: model_nonemptyTheory_iff
-/
instance instNonempty [Nonempty M] {S : L.ElementarySubstructure M} : Nonempty S :=
  (model_nonemptyTheory_iff L).1 inferInstance

/--
theorem `elementarilyEquivalent` / 定理 `elementarilyEquivalent`

English:
theorem elementarilyEquivalent
  given: (S : L.ElementarySubstructure M)
  statement: S ≅[L] M
  proof: S.subtype.elementarilyEquivalent

中文:
定理 elementarilyEquivalent
  条件: (S : L.ElementarySubstructure M)
  结论: S ≅[L] M
  证明: S.subtype.elementarilyEquivalent

Depends on / 依赖: S.subtype.elementarilyEquivalent, elementarilyEquivalent, subtype
-/
theorem elementarilyEquivalent (S : L.ElementarySubstructure M) : S ≅[L] M :=
  S.subtype.elementarilyEquivalent

end ElementarySubstructure

namespace Substructure

/--
theorem `isElementary_of_exists` / 定理 `isElementary_of_exists`

English:
theorem isElementary_of_exists
  statement: (S : L.Substructure M)
  proof: fun _ => S.subtype.isElementary_of_exists htv

中文:
定理 isElementary_of_存在
  结论: (S : L.子结构 M)
  证明: fun _ => S.subtype.isElementary_of_exists htv

Depends on / 依赖: S.subtype.isElementary_of_exists, isElementary_of_exists, subtype
-/
theorem isElementary_of_exists (S : L.Substructure M)
    (htv :
      forall (n : Nat) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n -> S) (a : M),
        φ.Realize default (Fin.snoc ((↑) ∘ x) a : _ -> M) ->
          exists b : S, φ.Realize default (Fin.snoc ((↑) ∘ x) b : _ -> M)) :
    S.IsElementary := fun _ => S.subtype.isElementary_of_exists htv

/-- Bundles a substructure satisfying the Tarski-Vaught test as an elementary substructure. -/
@[simps]
/--
Definition of `toElementarySubstructure` / `toElementarySubstructure` 的定义

English:
definition toElementarySubstructure
  signature: (S : L.Substructure M)
  body: ⟨S, S.isElementary_of_exists htv⟩

中文:
定义 toElementarySubstructure
  签名: (S : L.子结构 M)
  定义体: ⟨S, S.isElementary_of_exists htv⟩

Depends on / 依赖: S.isElementary_of_exists, isElementary_of_exists
-/
def toElementarySubstructure (S : L.Substructure M)
    (htv :
      forall (n : Nat) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n -> S) (a : M),
        φ.Realize default (Fin.snoc ((↑) ∘ x) a : _ -> M) ->
          exists b : S, φ.Realize default (Fin.snoc ((↑) ∘ x) b : _ -> M)) :
    L.ElementarySubstructure M :=
  ⟨S, S.isElementary_of_exists htv⟩

end Substructure

/--
Definition of `MeetsDefinable` / `MeetsDefinable` 的定义

English:
definition MeetsDefinable
  signature: (A : Set M)
  body: forall (D : Set M), D.Nonempty -> A.Definable₁ L D -> (D inter A).Nonempty

中文:
定义 MeetsDefinable
  签名: (A : 集合 M)
  定义体: forall (D : Set M), D.Nonempty -> A.Definable₁ L D -> (D inter A).Nonempty

Depends on / 依赖: A.Definable, D.Nonempty, Nonempty
-/
def MeetsDefinable (A : Set M) : Prop :=
  forall (D : Set M), D.Nonempty -> A.Definable₁ L D -> (D inter A).Nonempty

namespace MeetsDefinable

open Set Substructure

variable {A : Set M}

/--
theorem `closure_eq_self` / 定理 `closure_eq_self`

English:
theorem closure_eq_self
  given: (hA : L.MeetsDefinable A)
  proof: by
  refine Subset.antisymm ?_ subset_closure
  rw [coe_closure_eq_range_term_realize]
  intro x hx
  have : A.Definable₁ L {x} := by
    obtain ⟨t, rfl⟩ := hx
    use (Term.var 0).equal (t.relabel Sum.inl).varsToConstants
    simp [Set.ext_iff]
exact singleton_inter_nonempty.mp hA _ (singleton_nonempty x) this

中文:
定理 closure_eq_self
  条件: (hA : L.MeetsDefinable A)
  证明: by
  refine Subset.antisymm ?_ subset_closure
  rw [coe_closure_eq_range_term_realize]
  intro x hx
  have : A.Definable₁ L {x} := by
    obtain ⟨t, rfl⟩ := hx
    use (Term.var 0).equal (t.relabel Sum.inl).varsToConstants
    simp [Set.ext_iff]
exact singleton_inter_nonempty.mp hA _ (singleton_nonempty x) this

Depends on / 依赖: A.Definable, Set.ext_iff, Subset, Subset.antisymm, Sum.inl, Term.var, antisymm, coe_closure_eq_range_term_realize, ext_iff, relabel, singleton_inter_nonempty, singleton_inter_nonempty.mp, singleton_nonempty, subset_closure, t.relabel, varsToConstants
-/
theorem closure_eq_self (hA : L.MeetsDefinable A) :
    closure L A = A := by
  refine Subset.antisymm ?_ subset_closure
  rw [coe_closure_eq_range_term_realize]
  intro x hx
  have : A.Definable₁ L {x} := by
    obtain ⟨t, rfl⟩ := hx
    use (Term.var 0).equal (t.relabel Sum.inl).varsToConstants
    simp [Set.ext_iff]
exact singleton_inter_nonempty.mp hA _ (singleton_nonempty x) this

/--
theorem `isElementary_closure` / 定理 `isElementary_closure`

English:
theorem isElementary_closure
  given: (hA : L.MeetsDefinable A)
  proof: by
  refine isElementary_of_exists ((closure L).toFun A) ?_
  intro n φ x a hφ
  let D : Set M := {y : M | φ.Realize default (Fin.snoc (Subtype.val ∘ x) y)}
  have hD_ne : D.Nonempty := ⟨a,hφ⟩
  have hD : A.Definable₁ L D := by
    simp only [Definable₁, Definable, Fin.isValue]
    refine ⟨((L.lhomWithConstants A).onBoundedFormula φ).toFormula.relabel
.subst fun i => Fin.lastCases (Term.var 0) (Sum.elim Empty.elim id)
        (fun j => (L.con ⟨x j, by
        nth_rw 1 [← hA.closure_eq_self]
        simp only [Subtype.coe_prop]
        ⟩).term) i, ?_⟩
    ext v
    simp only [Fin.isValue, mem_ofPred_eq, Formula.relabel, Formula.Realize,
      BoundedFormula.realize_subst, BoundedFormula.realize_relabel, Nat.add_zero, Fin.castAdd_zero,
      Fin.cast_refl, Function.comp_id, Fin.natAdd_zero, D]
    rw [← Formula.Realize]; rw [BoundedFormula.realize_toFormula]; rw [LHom.realize_onBoundedFormula]
    congr! 1
    ext i; cases i using Fin.lastCases <;> simp
  obtain ⟨b, hbD, hbA⟩ := hA D hD_ne hD
  exact ⟨⟨b, by rwa [← hA.closure_eq_self] at hbA⟩, hbD⟩

中文:
定理 isElementary_closure
  条件: (hA : L.MeetsDefinable A)
  证明: by
  refine isElementary_of_exists ((closure L).toFun A) ?_
  intro n φ x a hφ
  let D : Set M := {y : M | φ.Realize default (Fin.snoc (Subtype.val ∘ x) y)}
  have hD_ne : D.Nonempty := ⟨a,hφ⟩
  have hD : A.Definable₁ L D := by
    simp only [Definable₁, Definable, Fin.isValue]
    refine ⟨((L.lhomWithConstants A).onBoundedFormula φ).toFormula.relabel
.subst fun i => Fin.lastCases (Term.var 0) (Sum.elim Empty.elim id)
        (fun j => (L.con ⟨x j, by
        nth_rw 1 [← hA.closure_eq_self]
        simp only [Subtype.coe_prop]
        ⟩).term) i, ?_⟩
    ext v
    simp only [Fin.isValue, mem_ofPred_eq, Formula.relabel, Formula.Realize,
      BoundedFormula.realize_subst, BoundedFormula.realize_relabel, Nat.add_zero, Fin.castAdd_zero,
      Fin.cast_refl, Function.comp_id, Fin.natAdd_zero, D]
    rw [← Formula.Realize]; rw [BoundedFormula.realize_toFormula]; rw [LHom.realize_onBoundedFormula]
    congr! 1
    ext i; cases i using Fin.lastCases <;> simp
  obtain ⟨b, hbD, hbA⟩ := hA D hD_ne hD
  exact ⟨⟨b, by rwa [← hA.closure_eq_self] at hbA⟩, hbD⟩

Depends on / 依赖: A.Definable, D.Nonempty, Definable, Empty.elim, Fin.isValue, Fin.lastCases, Fin.snoc, L.con, L.lhomWithConstants, Nonempty, Realize, Subtype, Subtype.coe_prop, Subtype.val, Sum.elim, Term.var, closure, closure_eq_self, coe_prop, hA.closure_eq_self
-/
theorem isElementary_closure (hA : L.MeetsDefinable A) :
    (closure L A).IsElementary := by
  refine isElementary_of_exists ((closure L).toFun A) ?_
  intro n φ x a hφ
  let D : Set M := {y : M | φ.Realize default (Fin.snoc (Subtype.val ∘ x) y)}
  have hD_ne : D.Nonempty := ⟨a,hφ⟩
  have hD : A.Definable₁ L D := by
    simp only [Definable₁, Definable, Fin.isValue]
    refine ⟨((L.lhomWithConstants A).onBoundedFormula φ).toFormula.relabel
.subst fun i => Fin.lastCases (Term.var 0) (Sum.elim Empty.elim id)
        (fun j => (L.con ⟨x j, by
        nth_rw 1 [← hA.closure_eq_self]
        simp only [Subtype.coe_prop]
        ⟩).term) i, ?_⟩
    ext v
    simp only [Fin.isValue, mem_ofPred_eq, Formula.relabel, Formula.Realize,
      BoundedFormula.realize_subst, BoundedFormula.realize_relabel, Nat.add_zero, Fin.castAdd_zero,
      Fin.cast_refl, Function.comp_id, Fin.natAdd_zero, D]
    rw [← Formula.Realize]; rw [BoundedFormula.realize_toFormula]; rw [LHom.realize_onBoundedFormula]
    congr! 1
    ext i; cases i using Fin.lastCases <;> simp
  obtain ⟨b, hbD, hbA⟩ := hA D hD_ne hD
  exact ⟨⟨b, by rwa [← hA.closure_eq_self] at hbA⟩, hbD⟩

/--
Definition of `toElementarySubstructure` / `toElementarySubstructure` 的定义

English:
definition toElementarySubstructure
  signature: (hA : L.MeetsDefinable A)
  body: ⟨closure L A, hA.isElementary_closure⟩

中文:
定义 toElementarySubstructure
  签名: (hA : L.MeetsDefinable A)
  定义体: ⟨closure L A, hA.isElementary_closure⟩

Depends on / 依赖: closure, hA.isElementary_closure, isElementary_closure
-/
def toElementarySubstructure (hA : L.MeetsDefinable A) :
    L.ElementarySubstructure M :=
  ⟨closure L A, hA.isElementary_closure⟩

end MeetsDefinable

namespace ElementarySubstructure

open Set Formula

/--
theorem `meetsDefinable` / 定理 `meetsDefinable`

English:
theorem meetsDefinable
  given: (S : L.ElementarySubstructure M)
  statement: L.MeetsDefinable (S : Set M)
  proof: by
  rintro D ⟨x, hx⟩ ⟨φ, hφ⟩
  have hφx : φ.Realize ![x] := by
    simp [Set.ext_iff] at hφ
    simp [← hφ, hx]
  let ψ : L[[(S : Set M)]].Sentence := (φ.relabel Sum.inr).iExs
  have hψM : ψ.Realize M := by
    simpa only [Sentence.Realize, SetLike.coe_sort_coe, Formula.realize_iExs,
      Formula.realize_relabel, Sum.elim_comp_inr, ψ] using
        (⟨![x], hφx⟩ : exists w : Fin 1 -> M, φ.Realize w)
  have hψS : ψ.Realize S := by
    rwa [← Formula.realize_equivSentence_symm_con, ← S.subtype.map_formula,
      Formula.realize_equivSentence_symm]
  simp only [Sentence.Realize, SetLike.coe_sort_coe, Formula.realize_iExs,
    Formula.realize_relabel, Sum.elim_comp_inr, ψ] at hψS
  obtain ⟨v', hv'⟩ := hψS
  refine ⟨v' 0, ?_, by simp⟩
  have hv'' : φ.Realize (Subtype.val ∘ v') := by
    simp only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv,
      ← S.subtype.map_boundedFormula] at hv'
    simp only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv]
    convert! hv' using 1
    funext i
    cases i <;> rfl
  change (Subtype.val ∘ v') in {x | x 0 in D}
  simpa [hφ] using hv''

中文:
定理 meetsDefinable
  条件: (S : L.ElementarySubstructure M)
  结论: L.MeetsDefinable (S : 集合 M)
  证明: by
  rintro D ⟨x, hx⟩ ⟨φ, hφ⟩
  have hφx : φ.Realize ![x] := by
    simp [Set.ext_iff] at hφ
    simp [← hφ, hx]
  let ψ : L[[(S : Set M)]].Sentence := (φ.relabel Sum.inr).iExs
  have hψM : ψ.Realize M := by
    simpa only [Sentence.Realize, SetLike.coe_sort_coe, Formula.realize_iExs,
      Formula.realize_relabel, Sum.elim_comp_inr, ψ] using
        (⟨![x], hφx⟩ : exists w : Fin 1 -> M, φ.Realize w)
  have hψS : ψ.Realize S := by
    rwa [← Formula.realize_equivSentence_symm_con, ← S.subtype.map_formula,
      Formula.realize_equivSentence_symm]
  simp only [Sentence.Realize, SetLike.coe_sort_coe, Formula.realize_iExs,
    Formula.realize_relabel, Sum.elim_comp_inr, ψ] at hψS
  obtain ⟨v', hv'⟩ := hψS
  refine ⟨v' 0, ?_, by simp⟩
  have hv'' : φ.Realize (Subtype.val ∘ v') := by
    simp only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv,
      ← S.subtype.map_boundedFormula] at hv'
    simp only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv]
    convert! hv' using 1
    funext i
    cases i <;> rfl
  change (Subtype.val ∘ v') in {x | x 0 in D}
  simpa [hφ] using hv''

Depends on / 依赖: Formula, Formula.realize_equivSentence, Formula.realize_equivSentence_symm_con, Formula.realize_iExs, Formula.realize_relabel, Realize, S.subtype.map_formula, Sentence, Sentence.Realize, Set.ext_iff, SetLike, SetLike.coe_sort_coe, Sum.elim_comp_inr, Sum.inr, coe_sort_coe, elim_comp_inr, ext_iff, map_formula, realize_equivSentence, realize_equivSentence_symm_con
-/
theorem meetsDefinable (S : L.ElementarySubstructure M) : L.MeetsDefinable (S : Set M) := by
  rintro D ⟨x, hx⟩ ⟨φ, hφ⟩
  have hφx : φ.Realize ![x] := by
    simp [Set.ext_iff] at hφ
    simp [← hφ, hx]
  let ψ : L[[(S : Set M)]].Sentence := (φ.relabel Sum.inr).iExs
  have hψM : ψ.Realize M := by
    simpa only [Sentence.Realize, SetLike.coe_sort_coe, Formula.realize_iExs,
      Formula.realize_relabel, Sum.elim_comp_inr, ψ] using
        (⟨![x], hφx⟩ : exists w : Fin 1 -> M, φ.Realize w)
  have hψS : ψ.Realize S := by
    rwa [← Formula.realize_equivSentence_symm_con, ← S.subtype.map_formula,
      Formula.realize_equivSentence_symm]
  simp only [Sentence.Realize, SetLike.coe_sort_coe, Formula.realize_iExs,
    Formula.realize_relabel, Sum.elim_comp_inr, ψ] at hψS
  obtain ⟨v', hv'⟩ := hψS
  refine ⟨v' 0, ?_, by simp⟩
  have hv'' : φ.Realize (Subtype.val ∘ v') := by
    simp only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv,
      ← S.subtype.map_boundedFormula] at hv'
    simp only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv]
    convert! hv' using 1
    funext i
    cases i <;> rfl
  change (Subtype.val ∘ v') in {x | x 0 in D}
  simpa [hφ] using hv''

end ElementarySubstructure

end Language

end FirstOrder
