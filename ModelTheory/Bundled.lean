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

/-
**CategoryTheory.Bundled.structure** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bun
dled`。
形式化陈述：{L : FirstOrder.Language} → (M : CategoryTheory.Bundled L.Structure) → L.S
tructure ↑M
参数：M : CategoryTheory.Bundled L.Structure。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**Equiv.bundledInduced** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：bundledInduced : CategoryTheory.Bundled.{w'} L.Structure
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type bundled with the structure induced by an equivalence.
-/
def bundledInduced : CategoryTheory.Bundled.{w'} L.Structure :=
  ⟨N, g.inducedStructure⟩

/-- An equivalence of types as a first-order equivalence to the bundled structure on the codomain.
-/
@[simp]
/-
**Equiv.bundledInducedEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：bundledInducedEquiv : M ≃[L] g.bundledInduced L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of types as a first-order equivalence to the bundled structure on
 the codomain.
-/
def bundledInducedEquiv : M ≃[L] g.bundledInduced L :=
  g.inducedStructureEquiv

end Equiv

namespace FirstOrder

namespace Language

/-- The equivalence relation on bundled `L.Structure`s indicating that they are isomorphic. -/
/-
**FirstOrder.Language.equivSetoid** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language
`。
形式化陈述：equivSetoid : Setoid (CategoryTheory.Bundled L.Structure) where r M N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence relation on bundled `L.Structure`s indicating that they are isom
orphic.
-/
instance equivSetoid : Setoid (CategoryTheory.Bundled L.Structure) where
  r M N := Nonempty (M ≃[L] N)
  iseqv :=
    ⟨fun M => ⟨Equiv.refl L M⟩, fun {_ _} => Nonempty.map Equiv.symm, fun {_ _} _ =>
      Nonempty.map2 fun MN NP => NP.comp MN⟩

variable (T : L.Theory)

namespace Theory

/-- The type of nonempty models of a first-order theory. -/
/-
**FirstOrder.Language.Theory.ModelType** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.L
anguage.Theory`。
形式化陈述：{L : FirstOrder.Language} → L.Theory → Type (max (max u v) (w + 1))
参数：max (max u v) (w + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of nonempty models of a first-order theory.
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

/-
**FirstOrder.Language.Theory.ModelType.instCoeSort** 是 Mathlib 中的一个实例，位于命名空间 `Fi
rstOrder.Language.Theory.ModelType`。
形式化陈述：instCoeSort : CoeSort T.ModelType (Type w)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeSort : CoeSort T.ModelType (Type w) :=
  ⟨ModelType.Carrier⟩

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
/-
**FirstOrder.Language.Theory.ModelType.of** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.
Language.Theory.ModelType`。
形式化陈述：of (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M] : T.ModelType
参数：M : Type w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in the category of R-algebras associated to a type equipped with the 
appropriate
typeclasses.
-/
def of (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M] : T.ModelType :=
  ⟨M⟩

@[simp]
/-
**FirstOrder.Language.Theory.ModelType.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Theory.ModelType`。
形式化陈述：coe_of (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M] : (of T M : Type 
w) = M
参数：M : Type w。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M] : (of T M : Type w) = M :=
  rfl
/-
**FirstOrder.Language.Theory.ModelType.instNonempty** 是 Mathlib 中的一个实例，位于命名空间 `F
irstOrder.Language.Theory.ModelType`。
形式化陈述：instNonempty (M : T.ModelType) : Nonempty M
参数：M : T.ModelType。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
-/
instance instNonempty (M : T.ModelType) : Nonempty M :=
  inferInstance

section Inhabited

attribute [local instance] Inhabited.trivialStructure

/-
**FirstOrder.Language.Theory.ModelType.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `
FirstOrder.Language.Theory.ModelType`。
形式化陈述：instInhabited : Inhabited (ModelType.{u, v, w} (∅ : L.Theory))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
instance instInhabited : Inhabited (ModelType.{u, v, w} (∅ : L.Theory)) :=
  ⟨ModelType.of _ PUnit⟩

end Inhabited

variable {T}

/-- Maps a bundled model along a bijection. -/
/-
**FirstOrder.Language.Theory.ModelType.equivInduced** 是 Mathlib 中的一个定义，位于命名空间 `F
irstOrder.Language.Theory.ModelType`。
形式化陈述：equivInduced {M : ModelType.{u, v, w} T} {N : Type w'} (e : M ≃ N) : Model
Type.{u, v, w'} T where Carrier
参数：e : M ≃ N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps a bundled model along a bijection.
-/
def equivInduced {M : ModelType.{u, v, w} T} {N : Type w'} (e : M ≃ N) :
    ModelType.{u, v, w'} T where
  Carrier := N
  struc := e.inducedStructure
  is_model := @StrongHomClass.theory_model L M N _ e.inducedStructure T
    _ _ _ e.inducedStructureEquiv _
  nonempty' := e.symm.nonempty
/-
**FirstOrder.Language.Theory.ModelType.of_small** 是 Mathlib 中的一个实例，位于命名空间 `First
Order.Language.Theory.ModelType`。
形式化陈述：of_small (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T] [h : Small.{w'}
 M] : Small.{w'} (ModelType.of T M)
参数：M : Type w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance of_small (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T] [h : Small.{w'} M] :
    Small.{w'} (ModelType.of T M) :=
  h

/-- Shrinks a small model to a particular universe. -/
/-
**FirstOrder.Language.Theory.ModelType.shrink** 是 Mathlib 中的一个定义，位于命名空间 `FirstOr
der.Language.Theory.ModelType`。
形式化陈述：shrink (M : ModelType.{u, v, w} T) [Small.{w'} M] : ModelType.{u, v, w'} T
参数：M : ModelType.{u, v, w} T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shrinks a small model to a particular universe.
-/
noncomputable def shrink (M : ModelType.{u, v, w} T) [Small.{w'} M] : ModelType.{u, v, w'} T :=
  equivInduced (equivShrink M)

/-- Lifts a model to a particular universe. -/
/-
**FirstOrder.Language.Theory.ModelType.ulift** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrd
er.Language.Theory.ModelType`。
形式化陈述：ulift (M : ModelType.{u, v, w} T) : ModelType.{u, v, max w w'} T
参数：M : ModelType.{u, v, w} T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Lifts a model to a particular universe.
-/
def ulift (M : ModelType.{u, v, w} T) : ModelType.{u, v, max w w'} T :=
  equivInduced (Equiv.ulift.{w', w}.symm : M ≃ _)

/-- The reduct of any model of `φ.onTheory T` is a model of `T`. -/
@[simps]
/-
**FirstOrder.Language.Theory.ModelType.reduct** 是 Mathlib 中的一个定义，位于命名空间 `FirstOr
der.Language.Theory.ModelType`。
形式化陈述：reduct {L' : Language} (φ : L ->ᴸ L') (M : (φ.onTheory T).ModelType) : T.M
odelType where Carrier
参数：φ : L ->ᴸ L'；M : (φ.onTheory T).ModelType。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reduct of any model of `φ.onTheory T` is a model of `T`.
-/
def reduct {L' : Language} (φ : L →ᴸ L') (M : (φ.onTheory T).ModelType) : T.ModelType where
  Carrier := M
  struc := φ.reduct M
  nonempty' := M.nonempty'
  is_model := (@LHom.onTheory_model L L' M (φ.reduct M) _ φ _ T).1 M.is_model

/-- When `φ` is injective, `defaultExpansion` expands a model of `T` to a model of `φ.onTheory T`
  arbitrarily. -/
@[simps]
/-
**FirstOrder.Language.Theory.ModelType.defaultExpansion** 是 Mathlib 中的一个定义，位于命名空
间 `FirstOrder.Language.Theory.ModelType`。
形式化陈述：defaultExpansion {L' : Language} {φ : L ->ᴸ L'} (h : φ.Injective) [forall 
(n) (f : L'.Functions n), Decidable (f in Set.range fun f : L.Functions n => φ.o
nFunction f)] [forall (n) (r : L'.Relations n), Decidable (r in Set.range fun r 
: L.Relations n => φ.onRelation r)] (M : T.ModelType) [Inhabited M] : (φ.onTheor
y T).ModelType where Carrier
参数：h : φ.Injective；n；f : L'.Functions n；f in Set.range fun f : L.Functions n => 
φ.onFunction f；n；r : L'.Relations n；r in Set.range fun r : L.Relations n => φ.on
Relation r；M : T.ModelType。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self

--- 原说明 ---
When `φ` is injective, `defaultExpansion` expands a model of `T` to a model of `
φ.onTheory T`
  arbitrarily.
-/
noncomputable def defaultExpansion {L' : Language} {φ : L →ᴸ L'} (h : φ.Injective)
    [∀ (n) (f : L'.Functions n), Decidable (f ∈ Set.range fun f : L.Functions n => φ.onFunction f)]
    [∀ (n) (r : L'.Relations n), Decidable (r ∈ Set.range fun r : L.Relations n => φ.onRelation r)]
    (M : T.ModelType) [Inhabited M] : (φ.onTheory T).ModelType where
  Carrier := M
  struc := φ.defaultExpansion M
  nonempty' := M.nonempty'
  is_model :=
    (@LHom.onTheory_model L L' M _ (φ.defaultExpansion M) φ (h.isExpansionOn_default M) T).2
      M.is_model
/-
**FirstOrder.Language.Theory.ModelType.leftStructure** 是 Mathlib 中的一个实例，位于命名空间 `
FirstOrder.Language.Theory.ModelType`。
形式化陈述：leftStructure {L' : Language} {T : (L.sum L').Theory} (M : T.ModelType) : 
L.Structure M
参数：L.sum L'；M : T.ModelType。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance leftStructure {L' : Language} {T : (L.sum L').Theory} (M : T.ModelType) : L.Structure M :=
  (LHom.sumInl : L →ᴸ L.sum L').reduct M
/-
**FirstOrder.Language.Theory.ModelType.rightStructure** 是 Mathlib 中的一个实例，位于命名空间 
`FirstOrder.Language.Theory.ModelType`。
形式化陈述：rightStructure {L' : Language} {T : (L.sum L').Theory} (M : T.ModelType) :
 L'.Structure M
参数：L.sum L'；M : T.ModelType。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rightStructure {L' : Language} {T : (L.sum L').Theory} (M : T.ModelType) :
    L'.Structure M :=
  (LHom.sumInr : L' →ᴸ L.sum L').reduct M

/-- A model of a theory is also a model of any subtheory. -/
@[simps]
/-
**FirstOrder.Language.Theory.ModelType.subtheoryModel** 是 Mathlib 中的一个定义，位于命名空间 
`FirstOrder.Language.Theory.ModelType`。
形式化陈述：subtheoryModel (M : T.ModelType) {T' : L.Theory} (h : T' subseteq T) : T'.
ModelType where Carrier
参数：M : T.ModelType；h : T' subseteq T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self

--- 原说明 ---
A model of a theory is also a model of any subtheory.
-/
def subtheoryModel (M : T.ModelType) {T' : L.Theory} (h : T' ⊆ T) : T'.ModelType where
  Carrier := M
  is_model := ⟨fun _φ hφ => realize_sentence_of_mem T (h hφ)⟩
/-
**FirstOrder.Language.Theory.ModelType.subtheoryModel_models** 是 Mathlib 中的一个实例，
位于命名空间 `FirstOrder.Language.Theory.ModelType`。
形式化陈述：subtheoryModel_models (M : T.ModelType) {T' : L.Theory} (h : T' subseteq T
) : M.subtheoryModel h ⊨ T
参数：M : T.ModelType；h : T' subseteq T。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
-/
instance subtheoryModel_models (M : T.ModelType) {T' : L.Theory} (h : T' ⊆ T) :
    M.subtheoryModel h ⊨ T :=
  M.is_model

end ModelType

variable {T}

/-- Bundles `M ⊨ T` as a `T.ModelType`. -/
/-
**FirstOrder.Language.Theory.Model.bundled** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder
.Language.Theory.Model`。
形式化陈述：{L : FirstOrder.Language} →   {T : L.Theory} → {M : Type w} → [LM : L.Stru
cture M] → [ne : Nonempty M] → M ⊨ T → T.ModelType
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundles `M ⊨ T` as a `T.ModelType`.
-/
def Model.bundled {M : Type w} [LM : L.Structure M] [ne : Nonempty M] (h : M ⊨ T) : T.ModelType :=
  @ModelType.of L T M LM h ne

@[simp]
/-
**FirstOrder.Language.Theory.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langua
ge.Theory`。
形式化陈述：coe_of {M : Type w} [L.Structure M] [Nonempty M] (h : M ⊨ T) : (h.bundled 
: Type w) = M
参数：h : M ⊨ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of {M : Type w} [L.Structure M] [Nonempty M] (h : M ⊨ T) : (h.bundled : Type w) = M :=
  rfl

end Theory

/-- A structure that is elementarily equivalent to a model, bundled as a model. -/
/-
**FirstOrder.Language.ElementarilyEquivalent.toModel** 是 Mathlib 中的一个定义，位于命名空间 `
FirstOrder.Language.ElementarilyEquivalent`。
形式化陈述：{L : FirstOrder.Language} →   (T : L.Theory) →     {M : T.ModelType} → {N 
: Type u_1} → [LN : L.Structure N] → L.ElementarilyEquivalent (↑M) N → T.ModelTy
pe
参数：T : L.Theory；↑M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure that is elementarily equivalent to a model, bundled as a model.
-/
def ElementarilyEquivalent.toModel {M : T.ModelType} {N : Type*} [LN : L.Structure N]
    (h : M ≅[L] N) : T.ModelType where
  Carrier := N
  struc := LN
  nonempty' := h.nonempty
  is_model := h.theory_model

/-- An elementary substructure of a bundled model as a bundled model. -/
/-
**FirstOrder.Language.ElementarySubstructure.toModel** 是 Mathlib 中的一个定义，位于命名空间 `
FirstOrder.Language.ElementarySubstructure`。
形式化陈述：{L : FirstOrder.Language} → (T : L.Theory) → {M : T.ModelType} → L.Element
arySubstructure ↑M → T.ModelType
参数：T : L.Theory。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An elementary substructure of a bundled model as a bundled model.
-/
def ElementarySubstructure.toModel {M : T.ModelType} (S : L.ElementarySubstructure M) :
    T.ModelType :=
  S.elementarilyEquivalent.symm.toModel T
/-
**FirstOrder.Language.ElementarySubstructure.toModel.instSmall** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.ElementarySubstructure.toModel`。
形式化陈述：∀ {L : FirstOrder.Language} (T : L.Theory) {M : T.ModelType} (S : L.Elemen
tarySubstructure ↑M) [h : Small.{w, x} ↥S],   Small.{w, x} ↑(FirstOrder.Language
.ElementarySubstructure.toModel T S)
参数：T : L.Theory；S : L.ElementarySubstructure ↑M；FirstOrder.Language.ElementarySu
bstructure.toModel T S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ElementarySubstructure.toModel.instSmall {M : T.ModelType}
    (S : L.ElementarySubstructure M) [h : Small.{w, x} S] : Small.{w, x} (S.toModel T) :=
  h

end Language

end FirstOrder

