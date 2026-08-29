/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.ElementarySubstructures
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled

/-!
# Bundled First-Order Structures

This file bundles types together with their first-order structure.

## Main Definitions

- `FirstOrder.Language.Theory.ModelType` is the type of nonempty models of a particular theory.
- `FirstOrder.Language.equivSetoid` is the isomorphism equivalence relation on bundled structures.

## TODO

- Define category structures on bundled structures and models.
-/

@[expose] public section


universe u v w w' x

variable {L : FirstOrder.Language.{u, v}}

/--
Instance `CategoryTheory.Bundled.structure` / 实例 `CategoryTheory.Bundled.structure`

English:
instance CategoryTheory.Bundled.structure
  signature: {L : FirstOrder.Language.{u, v}}
  body: M.str

中文:
实例 CategoryTheory.Bundled.structure
  签名: {L : FirstOrder.Language.{u, v}}
  定义体: M.str
-/
protected instance CategoryTheory.Bundled.structure {L : FirstOrder.Language.{u, v}}
    (M : CategoryTheory.Bundled.{w} L.Structure) : L.Structure M :=
  M.str

open FirstOrder Cardinal

namespace Equiv

variable (L) {M : Type w}
variable [L.Structure M] {N : Type w'} (g : M ≃ N)

/-- A type bundled with the structure induced by an equivalence. -/
@[simps]
/--
Definition of `bundledInduced` / `bundledInduced` 的定义

English:
definition bundledInduced
  signature: : CategoryTheory.Bundled.{w'} L.Structure
  body: ⟨N, g.inducedStructure⟩

中文:
定义 bundledInduced
  签名: : CategoryTheory.Bundled.{w'} L.Structure
  定义体: ⟨N, g.inducedStructure⟩

Depends on / 依赖: g.inducedStructure, inducedStructure
-/
def bundledInduced : CategoryTheory.Bundled.{w'} L.Structure :=
  ⟨N, g.inducedStructure⟩

/-- An equivalence of types as a first-order equivalence to the bundled structure on the codomain.
-/
@[simp]
/--
Definition of `bundledInducedEquiv` / `bundledInducedEquiv` 的定义

English:
definition bundledInducedEquiv
  signature: : M ≃[L] g.bundledInduced L
  body: g.inducedStructureEquiv

中文:
定义 bundledInducedEquiv
  签名: : M ≃[L] g.bundledInduced L
  定义体: g.inducedStructureEquiv

Depends on / 依赖: g.inducedStructureEquiv, inducedStructureEquiv
-/
def bundledInducedEquiv : M ≃[L] g.bundledInduced L :=
  g.inducedStructureEquiv

end Equiv

namespace FirstOrder

namespace Language

/--
Instance `equivSetoid` / 实例 `equivSetoid`

English:
instance equivSetoid
  signature: : Setoid (CategoryTheory.Bundled L.Structure) where
  body: Nonempty (M ≃[L] N)
  iseqv :=
    ⟨fun M => ⟨Equiv.refl L M⟩, fun {_ _} => Nonempty.map Equiv.symm, fun {_ _} _ =>
      Nonempty.map2 fun MN NP => NP.comp MN⟩

中文:
实例 equivSetoid
  签名: : Setoid (CategoryTheory.Bundled L.Structure) where
  定义体: Nonempty (M ≃[L] N)
  iseqv :=
    ⟨fun M => ⟨Equiv.refl L M⟩, fun {_ _} => Nonempty.map Equiv.symm, fun {_ _} _ =>
      Nonempty.map2 fun MN NP => NP.comp MN⟩

Depends on / 依赖: Nonempty
-/
instance equivSetoid : Setoid (CategoryTheory.Bundled L.Structure) where
  r M N := Nonempty (M ≃[L] N)
  iseqv :=
    ⟨fun M => ⟨Equiv.refl L M⟩, fun {_ _} => Nonempty.map Equiv.symm, fun {_ _} _ =>
      Nonempty.map2 fun MN NP => NP.comp MN⟩

variable (T : L.Theory)

namespace Theory

/--
Definition of `ModelType` / `ModelType` 的定义

English:
structure ModelType
  parameters: where
  axioms and operations (4):
    - Carrier : Type w
    - [struc : L.Structure Carrier]
    - [is_model : T.Model Carrier]
    - [nonempty' : Nonempty Carrier]

中文:
结构 ModelType
  参数: where
  公理与运算 (4 个):
    - Carrier : Type w
    - [struc : L.Structure Carrier]
    - [is_model : T.Model Carrier]
    - [nonempty' : Nonempty Carrier]

Depends on / 依赖: _assoc, lift_lift, monotone_principal, monotone_principal.comp
-/
structure ModelType where
  /-- The underlying type for the models -/
  Carrier : Type w
  [struc : L.Structure Carrier]
  [is_model : T.Model Carrier]
  [nonempty' : Nonempty Carrier]

-- Porting note: In Lean4, other instances precedes `FirstOrder.Language.Theory.ModelType.struc`,
-- it's issues in `ModelTheory.Satisfiability`. So, we increase these priorities.
attribute [instance 2000] ModelType.struc ModelType.is_model ModelType.nonempty'

namespace ModelType

attribute [coe] ModelType.Carrier

/--
Instance `instCoeSort` / 实例 `instCoeSort`

English:
instance instCoeSort
  signature: : CoeSort T.ModelType (Type w)
  body: ⟨ModelType.Carrier⟩

中文:
实例 instCoeSort
  签名: : CoeSort T.ModelType (Type w)
  定义体: ⟨ModelType.Carrier⟩

Depends on / 依赖: Carrier, ModelType, ModelType.Carrier, lift_assoc
-/
instance instCoeSort : CoeSort T.ModelType (Type w) :=
  ⟨ModelType.Carrier⟩

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M]
  body: ⟨M⟩

@[simp]

中文:
定义 of
  签名: (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M]
  定义体: ⟨M⟩

@[simp]

Depends on / 依赖: lift_lift_same_le_lift
-/
def of (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M] : T.ModelType :=
  ⟨M⟩

@[simp]
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M]
  statement: (of T M : Type w) = M
  proof: rfl

中文:
定理 coe_of
  条件: (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M]
  结论: (of T M : Type w) = M
  证明: rfl

Depends on / 依赖: lift_lift_same_eq_lift, monotone_principal, monotone_principal.comp
-/
theorem coe_of (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M] : (of T M : Type w) = M :=
  rfl

/--
Instance `instNonempty` / 实例 `instNonempty`

English:
instance instNonempty
  signature: (M : T.ModelType)
  body: inferInstance

中文:
实例 instNonempty
  签名: (M : T.ModelType)
  定义体: inferInstance

Depends on / 依赖: Filter, Filter.lift, iInf_inf, iInf_subtype, inf_principal
-/
instance instNonempty (M : T.ModelType) : Nonempty M :=
  inferInstance

section Inhabited

attribute [local instance] Inhabited.trivialStructure

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (ModelType.{u, v, w} (∅ : L.Theory))
  body: ⟨ModelType.of _ PUnit⟩

中文:
实例 instInhabited
  签名: : Inhabited (ModelType.{u, v, w} (∅ : L.Theory))
  定义体: ⟨ModelType.of _ PUnit⟩

Depends on / 依赖: ModelType, ModelType.of, Nonempty, f.lift, lift_neBot_iff, monotone_principal, monotone_principal.comp, principal_neBot_iff
-/
instance instInhabited : Inhabited (ModelType.{u, v, w} (∅ : L.Theory)) :=
  ⟨ModelType.of _ PUnit⟩

end Inhabited

variable {T}

/--
Definition of `equivInduced` / `equivInduced` 的定义

English:
definition equivInduced
  signature: {M : ModelType.{u, v, w} T} {N : Type w'} (e : M ≃ N)
  body: N
  struc := e.inducedStructure
  is_model := @StrongHomClass.theory_model L M N _ e.inducedStructure T
    _ _ _ e.inducedStructureEquiv _
  nonempty' := e.symm.nonempty

中文:
定义 equivInduced
  签名: {M : ModelType.{u, v, w} T} {N : Type w'} (e : M ≃ N)
  定义体: N
  struc := e.inducedStructure
  is_model := @StrongHomClass.theory_model L M N _ e.inducedStructure T
    _ _ _ e.inducedStructureEquiv _
  nonempty' := e.symm.nonempty

Depends on / 依赖: lift_principal2
-/
def equivInduced {M : ModelType.{u, v, w} T} {N : Type w'} (e : M ≃ N) :
    ModelType.{u, v, w'} T where
  Carrier := N
  struc := e.inducedStructure
  is_model := @StrongHomClass.theory_model L M N _ e.inducedStructure T
    _ _ _ e.inducedStructureEquiv _
  nonempty' := e.symm.nonempty

/--
Instance `of_small` / 实例 `of_small`

English:
instance of_small
  signature: (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T] [h : Small.{w'} M]
  body: h

中文:
实例 of_small
  签名: (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T] [h : Small.{w'} M]
  定义体: h

Depends on / 依赖: inf_principal, lift_iInf
-/
instance of_small (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T] [h : Small.{w'} M] :
    Small.{w'} (ModelType.of T M) :=
  h

/--
Definition of `shrink` / `shrink` 的定义

English:
definition shrink
  signature: (M : ModelType.{u, v, w} T) [Small.{w'} M]
  body: equivInduced (equivShrink M)

中文:
定义 shrink
  签名: (M : ModelType.{u, v, w} T) [Small.{w'} M]
  定义体: equivInduced (equivShrink M)

Depends on / 依赖: Function, Function.comp_apply, comp_apply, equivInduced, equivShrink, inf_principal, lift_iInf_of_map_univ, principal_univ
-/
noncomputable def shrink (M : ModelType.{u, v, w} T) [Small.{w'} M] : ModelType.{u, v, w'} T :=
  equivInduced (equivShrink M)

/--
Definition of `ulift` / `ulift` 的定义

English:
definition ulift
  signature: (M : ModelType.{u, v, w} T)
  body: equivInduced (Equiv.ulift.{w', w}.symm : M ≃ _)

中文:
定义 ulift
  签名: (M : ModelType.{u, v, w} T)
  定义体: equivInduced (Equiv.ulift.{w', w}.symm : M ≃ _)

Depends on / 依赖: Equiv.ulift, _iInf, equivInduced, iInf_congr, inf_eq_iInf
-/
def ulift (M : ModelType.{u, v, w} T) : ModelType.{u, v, max w w'} T :=
  equivInduced (Equiv.ulift.{w', w}.symm : M ≃ _)

/-- The reduct of any model of `φ.onTheory T` is a model of `T`. -/
@[simps]
/--
Definition of `reduct` / `reduct` 的定义

English:
definition reduct
  signature: {L' : Language} (φ : L ->ᴸ L') (M : (φ.onTheory T).ModelType)
  body: M
  struc := φ.reduct M
  nonempty' := M.nonempty'
  is_model := (@LHom.onTheory_model L L' M (φ.reduct M) _ φ _ T).1 M.is_model

中文:
定义 reduct
  签名: {L' : Language} (φ : L ->ᴸ L') (M : (φ.onTheory T).ModelType)
  定义体: M
  struc := φ.reduct M
  nonempty' := M.nonempty'
  is_model := (@LHom.onTheory_model L L' M (φ.reduct M) _ φ _ T).1 M.is_model

Depends on / 依赖: _mono, inf_le_left, inf_le_right, le_inf, le_rfl
-/
def reduct {L' : Language} (φ : L ->ᴸ L') (M : (φ.onTheory T).ModelType) : T.ModelType where
  Carrier := M
  struc := φ.reduct M
  nonempty' := M.nonempty'
  is_model := (@LHom.onTheory_model L L' M (φ.reduct M) _ φ _ T).1 M.is_model

/-- When `φ` is injective, `defaultExpansion` expands a model of `T` to a model of `φ.onTheory T`
  arbitrarily. -/
@[simps]
/--
Definition of `defaultExpansion` / `defaultExpansion` 的定义

English:
definition defaultExpansion
  signature: {L' : Language} {φ : L ->ᴸ L'} (h : φ.Injective)
  body: M
  struc := φ.defaultExpansion M
  nonempty' := M.nonempty'
  is_model :=
    (@LHom.onTheory_model L L' M _ (φ.defaultExpansion M) φ (h.isExpansionOn_default M) T).2
      M.is_model

中文:
定义 defaultExpansion
  签名: {L' : Language} {φ : L ->ᴸ L'} (h : φ.Injective)
  定义体: M
  struc := φ.defaultExpansion M
  nonempty' := M.nonempty'
  is_model :=
    (@LHom.onTheory_model L L' M _ (φ.defaultExpansion M) φ (h.isExpansionOn_default M) T).2
      M.is_model
-/
noncomputable def defaultExpansion {L' : Language} {φ : L ->ᴸ L'} (h : φ.Injective)
    [forall (n) (f : L'.Functions n), Decidable (f in Set.range fun f : L.Functions n => φ.onFunction f)]
    [forall (n) (r : L'.Relations n), Decidable (r in Set.range fun r : L.Relations n => φ.onRelation r)]
    (M : T.ModelType) [Inhabited M] : (φ.onTheory T).ModelType where
  Carrier := M
  struc := φ.defaultExpansion M
  nonempty' := M.nonempty'
  is_model :=
    (@LHom.onTheory_model L L' M _ (φ.defaultExpansion M) φ (h.isExpansionOn_default M) T).2
      M.is_model

/--
Instance `leftStructure` / 实例 `leftStructure`

English:
instance leftStructure
  signature: {L' : Language} {T : (L.sum L').Theory} (M : T.ModelType)
  body: (LHom.sumInl : L ->ᴸ L.sum L').reduct M

中文:
实例 leftStructure
  签名: {L' : Language} {T : (L.sum L').Theory} (M : T.ModelType)
  定义体: (LHom.sumInl : L ->ᴸ L.sum L').reduct M

Depends on / 依赖: L.sum, LHom.sumInl, reduct, sumInl
-/
instance leftStructure {L' : Language} {T : (L.sum L').Theory} (M : T.ModelType) : L.Structure M :=
  (LHom.sumInl : L ->ᴸ L.sum L').reduct M

/--
Instance `rightStructure` / 实例 `rightStructure`

English:
instance rightStructure
  signature: {L' : Language} {T : (L.sum L').Theory} (M : T.ModelType)
  body: (LHom.sumInr : L' ->ᴸ L.sum L').reduct M

中文:
实例 rightStructure
  签名: {L' : Language} {T : (L.sum L').Theory} (M : T.ModelType)
  定义体: (LHom.sumInr : L' ->ᴸ L.sum L').reduct M

Depends on / 依赖: L.sum, LHom.sumInr, reduct, sumInr
-/
instance rightStructure {L' : Language} {T : (L.sum L').Theory} (M : T.ModelType) :
    L'.Structure M :=
  (LHom.sumInr : L' ->ᴸ L.sum L').reduct M

/-- A model of a theory is also a model of any subtheory. -/
@[simps]
/--
Definition of `subtheoryModel` / `subtheoryModel` 的定义

English:
definition subtheoryModel
  signature: (M : T.ModelType) {T' : L.Theory} (h : T' subseteq T)
  body: M
  is_model := ⟨fun _φ hφ => realize_sentence_of_mem T (h hφ)⟩

中文:
定义 subtheoryModel
  签名: (M : T.ModelType) {T' : L.Theory} (h : T' subseteq T)
  定义体: M
  is_model := ⟨fun _φ hφ => realize_sentence_of_mem T (h hφ)⟩
-/
def subtheoryModel (M : T.ModelType) {T' : L.Theory} (h : T' subseteq T) : T'.ModelType where
  Carrier := M
  is_model := ⟨fun _φ hφ => realize_sentence_of_mem T (h hφ)⟩

/--
Instance `subtheoryModel_models` / 实例 `subtheoryModel_models`

English:
instance subtheoryModel_models
  signature: (M : T.ModelType) {T' : L.Theory} (h : T' subseteq T)
  body: M.is_model

中文:
实例 subtheoryModel_models
  签名: (M : T.ModelType) {T' : L.Theory} (h : T' subseteq T)
  定义体: M.is_model

Depends on / 依赖: M.is_model, is_model
-/
instance subtheoryModel_models (M : T.ModelType) {T' : L.Theory} (h : T' subseteq T) :
    M.subtheoryModel h ⊨ T :=
  M.is_model

end ModelType

variable {T}

/--
Definition of `Model.bundled` / `Model.bundled` 的定义

English:
definition Model.bundled
  signature: {M : Type w} [LM : L.Structure M] [ne : Nonempty M] (h : M ⊨ T)
  body: @ModelType.of L T M LM h ne

@[simp]

中文:
定义 Model.bundled
  签名: {M : Type w} [LM : L.Structure M] [ne : Nonempty M] (h : M ⊨ T)
  定义体: @ModelType.of L T M LM h ne

@[simp]

Depends on / 依赖: ModelType, ModelType.of
-/
def Model.bundled {M : Type w} [LM : L.Structure M] [ne : Nonempty M] (h : M ⊨ T) : T.ModelType :=
  @ModelType.of L T M LM h ne

@[simp]
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: {M : Type w} [L.Structure M] [Nonempty M] (h : M ⊨ T)
  statement: (h.bundled : Type w) = M
  proof: rfl

中文:
定理 coe_of
  条件: {M : Type w} [L.Structure M] [Nonempty M] (h : M ⊨ T)
  结论: (h.bundled : Type w) = M
  证明: rfl
-/
theorem coe_of {M : Type w} [L.Structure M] [Nonempty M] (h : M ⊨ T) : (h.bundled : Type w) = M :=
  rfl

end Theory

/--
Definition of `ElementarilyEquivalent.toModel` / `ElementarilyEquivalent.toModel` 的定义

English:
definition ElementarilyEquivalent.toModel
  signature: {M : T.ModelType} {N : Type*} [LN : L.Structure N]
  body: N
  struc := LN
  nonempty' := h.nonempty
  is_model := h.theory_model

中文:
定义 ElementarilyEquivalent.toModel
  签名: {M : T.ModelType} {N : 类型} [LN : L.Structure N]
  定义体: N
  struc := LN
  nonempty' := h.nonempty
  is_model := h.theory_model
-/
def ElementarilyEquivalent.toModel {M : T.ModelType} {N : Type*} [LN : L.Structure N]
    (h : M ≅[L] N) : T.ModelType where
  Carrier := N
  struc := LN
  nonempty' := h.nonempty
  is_model := h.theory_model

/--
Definition of `ElementarySubstructure.toModel` / `ElementarySubstructure.toModel` 的定义

English:
definition ElementarySubstructure.toModel
  signature: {M : T.ModelType} (S : L.ElementarySubstructure M)
  body: S.elementarilyEquivalent.symm.toModel T

中文:
定义 ElementarySubstructure.toModel
  签名: {M : T.ModelType} (S : L.ElementarySubstructure M)
  定义体: S.elementarilyEquivalent.symm.toModel T

Depends on / 依赖: S.elementarilyEquivalent.symm.toModel, elementarilyEquivalent, toModel
-/
def ElementarySubstructure.toModel {M : T.ModelType} (S : L.ElementarySubstructure M) :
    T.ModelType :=
  S.elementarilyEquivalent.symm.toModel T

/--
Instance `ElementarySubstructure.toModel.instSmall` / 实例 `ElementarySubstructure.toModel.instSmall`

English:
instance ElementarySubstructure.toModel.instSmall
  signature: {M : T.ModelType}
  body: h

中文:
实例 ElementarySubstructure.toModel.instSmall
  签名: {M : T.ModelType}
  定义体: h
-/
instance ElementarySubstructure.toModel.instSmall {M : T.ModelType}
    (S : L.ElementarySubstructure M) [h : Small.{w, x} S] : Small.{w, x} (S.toModel T) :=
  h

end Language

end FirstOrder
