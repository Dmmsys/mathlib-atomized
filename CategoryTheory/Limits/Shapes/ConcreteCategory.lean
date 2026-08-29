/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Limits in concrete categories

In this file, we combine the description of limits in `Types` and the API about
the preservation of products and pullbacks in order to describe these limits in a
concrete category `C`.

If `F : J → C` is a family of objects in `C`, we define a bijection
`Limits.Concrete.productEquiv F : ToType (∏ᶜ F) ≃ ∀ j, ToType (F j)`.

Similarly, if `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S` are two morphisms, the elements
in `pullback f₁ f₂` are identified by `Limits.Concrete.pullbackEquiv`
to compatible tuples of elements in `X₁ × X₂`.

Some results are also obtained for the terminal object, binary products,
wide-pullbacks, wide-pushouts, multiequalizers and cokernels.

-/

@[expose] public section

universe s w w' v u t r

namespace CategoryTheory.Limits.Concrete

open ConcreteCategory

variable {C : Type u} [Category.{v} C]

section Products

section ProductEquiv

variable {FC : C -> C -> Type*} {CC : C -> Type max w v} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{max w v} C FC] {J : Type w} (F : J -> C)
  [HasProduct F] [PreservesLimit (Discrete.functor F) (forget C)]

/--
Definition of `productEquiv` / `productEquiv` 的定义

English:
definition productEquiv
  signature: : ToType (∏ᶜ F) ≃ forall j, ToType (F j)
  body: ((PreservesProduct.iso (forget C) F) ≪≫ (Types.productIso.{w, v} fun j =>
    (ToType (F j)))).toEquiv

@[simp]

中文:
定义 productEquiv
  签名: : ToType (∏ᶜ F) ≃ 对任意 j, ToType (F j)
  定义体: ((PreservesProduct.iso (forget C) F) ≪≫ (Types.productIso.{w, v} fun j =>
    (ToType (F j)))).toEquiv

@[simp]

Depends on / 依赖: PreservesProduct, PreservesProduct.iso, ToType, Types.productIso, forget, productIso, toEquiv
-/
noncomputable def productEquiv : ToType (∏ᶜ F) ≃ forall j, ToType (F j) :=
  ((PreservesProduct.iso (forget C) F) ≪≫ (Types.productIso.{w, v} fun j =>
    (ToType (F j)))).toEquiv

@[simp]
/--
lemma `productEquiv_apply_apply` / 引理 `productEquiv_apply_apply`

English:
lemma productEquiv_apply_apply
  given: (x : ToType (∏ᶜ F)) (j : J)
  proof: congr_hom (piComparison_comp_π (forget C) F j) x

@[simp]

中文:
引理 productEquiv_apply_apply
  条件: (x : ToType (∏ᶜ F)) (j : J)
  证明: congr_hom (piComparison_comp_π (forget C) F j) x

@[simp]

Depends on / 依赖: congr_hom, forget
-/
lemma productEquiv_apply_apply (x : ToType (∏ᶜ F)) (j : J) :
    productEquiv F x j = Pi.π F j x :=
  congr_hom (piComparison_comp_π (forget C) F j) x

@[simp]
/--
lemma `productEquiv_symm_apply_π` / 引理 `productEquiv_symm_apply_π`

English:
lemma productEquiv_symm_apply_π
  given: (x : forall j, ToType (F j)) (j : J)
  proof: by
  rw [← productEquiv_apply_apply]; rw [Equiv.apply_symm_apply]

中文:
引理 productEquiv_symm_apply_π
  条件: (x : 对任意 j, ToType (F j)) (j : J)
  证明: by
  rw [← productEquiv_apply_apply]; rw [Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, productEquiv_apply_apply
-/
lemma productEquiv_symm_apply_π (x : forall j, ToType (F j)) (j : J) :
    Pi.π F j ((productEquiv F).symm x) = x j := by
  rw [← productEquiv_apply_apply]; rw [Equiv.apply_symm_apply]

end ProductEquiv

section ProductExt

variable {J : Type w} (f : J -> C) [HasProduct f] {D : Type t} [Category.{r} D]
variable {FD : D -> D -> Type*} {DD : D -> Type max w r} [forall X Y, FunLike (FD X Y) (DD X) (DD Y)]
variable [ConcreteCategory.{max w r} D FD] (F : C ⥤ D)
  [PreservesLimit (Discrete.functor f) F]
  [HasProduct fun j => F.obj (f j)]
  [PreservesLimitsOfShape WalkingCospan (forget D)]
  [PreservesLimit (Discrete.functor fun b => F.obj (f b)) (forget D)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Pi.map_ext` / 引理 `Pi.map_ext`

English:
lemma Pi.map_ext
  statement: (x y : ToType (F.obj (∏ᶜ f : C)))
  proof: by
  apply ConcreteCategory.injective_of_mono_of_preservesPullback (PreservesProduct.iso F f).hom
  apply Concrete.limit_ext _ (piComparison F _ x) (piComparison F _ y)
  intro ⟨j⟩
  rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [piComparison_comp_π]
  exact h j

中文:
引理 依赖函数类型.map_ext
  结论: (x y : ToType (F.obj (∏ᶜ f : C)))
  证明: by
  apply ConcreteCategory.injective_of_mono_of_preservesPullback (PreservesProduct.iso F f).hom
  apply Concrete.limit_ext _ (piComparison F _ x) (piComparison F _ y)
  intro ⟨j⟩
  rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [piComparison_comp_π]
  exact h j

Depends on / 依赖: Concrete, Concrete.limit_ext, ConcreteCategory, ConcreteCategory.comp_apply, ConcreteCategory.injective_of_mono_of_preservesPullback, PreservesProduct, PreservesProduct.iso, comp_apply, injective_of_mono_of_preservesPullback, limit_ext, piComparison
-/
lemma Pi.map_ext (x y : ToType (F.obj (∏ᶜ f : C)))
    (h : forall i, F.map (Pi.π f i) x = F.map (Pi.π f i) y) : x = y := by
  apply ConcreteCategory.injective_of_mono_of_preservesPullback (PreservesProduct.iso F f).hom
  apply Concrete.limit_ext _ (piComparison F _ x) (piComparison F _ y)
  intro ⟨j⟩
  rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [piComparison_comp_π]
  exact h j

end ProductExt

end Products

section Terminal

variable {FC : C -> C -> Type*} {CC : C -> Type w} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{w} C FC]

/-- If `forget C` preserves terminals and `X` is terminal, then `ToType X` is a
singleton. -/
@[instance_reducible]
/--
Definition of `uniqueOfTerminalOfPreserves` / `uniqueOfTerminalOfPreserves` 的定义

English:
definition uniqueOfTerminalOfPreserves
  signature: [PreservesLimit (Functor.empty.{0} C) (forget C)]
  body: Types.isTerminalEquivUnique (ToType X) IsTerminal.isTerminalObj (forget C) X h

中文:
定义 uniqueOfTerminalOfPreserves
  签名: [保持极限 (函子.empty.{0} C) (forget C)]
  定义体: Types.isTerminalEquivUnique (ToType X) IsTerminal.isTerminalObj (forget C) X h

Depends on / 依赖: IsTerminal, IsTerminal.isTerminalObj, ToType, Types.isTerminalEquivUnique, forget, isTerminalEquivUnique, isTerminalObj
-/
noncomputable def uniqueOfTerminalOfPreserves [PreservesLimit (Functor.empty.{0} C) (forget C)]
    (X : C) (h : IsTerminal X) : Unique (ToType X) :=
Types.isTerminalEquivUnique (ToType X) IsTerminal.isTerminalObj (forget C) X h

/--
Definition of `terminalOfUniqueOfReflects` / `terminalOfUniqueOfReflects` 的定义

English:
definition terminalOfUniqueOfReflects
  signature: [ReflectsLimit (Functor.empty.{0} C) (forget C)]
  body: IsTerminal.isTerminalOfObj (forget C) X
    (Types.isTerminalEquivUnique (ToType X)).symm h

中文:
定义 terminalOfUniqueOfReflects
  签名: [反映极限 (函子.empty.{0} C) (forget C)]
  定义体: IsTerminal.isTerminalOfObj (forget C) X
    (Types.isTerminalEquivUnique (ToType X)).symm h

Depends on / 依赖: IsTerminal, IsTerminal.isTerminalOfObj, ToType, Types.isTerminalEquivUnique, forget, isTerminalEquivUnique, isTerminalOfObj
-/
noncomputable def terminalOfUniqueOfReflects [ReflectsLimit (Functor.empty.{0} C) (forget C)]
    (X : C) (h : Unique (ToType X)) : IsTerminal X :=
IsTerminal.isTerminalOfObj (forget C) X
    (Types.isTerminalEquivUnique (ToType X)).symm h

/--
Definition of `terminalIffUnique` / `terminalIffUnique` 的定义

English:
definition terminalIffUnique
  signature: [PreservesLimit (Functor.empty.{0} C) (forget C)]
  body: (IsTerminal.isTerminalIffObj (forget C) X).trans Types.isTerminalEquivUnique _

中文:
定义 terminalIffUnique
  签名: [保持极限 (函子.empty.{0} C) (forget C)]
  定义体: (IsTerminal.isTerminalIffObj (forget C) X).trans Types.isTerminalEquivUnique _

Depends on / 依赖: IsTerminal, IsTerminal.isTerminalIffObj, Types.isTerminalEquivUnique, forget, isTerminalEquivUnique, isTerminalIffObj
-/
noncomputable def terminalIffUnique [PreservesLimit (Functor.empty.{0} C) (forget C)]
    [ReflectsLimit (Functor.empty.{0} C) (forget C)] (X : C) :
    IsTerminal X ≃ Unique (ToType X) :=
(IsTerminal.isTerminalIffObj (forget C) X).trans Types.isTerminalEquivUnique _

variable (C)
variable [HasTerminal C] [PreservesLimit (Functor.empty.{0} C) (forget C)]

/--
Definition of `terminalEquiv` / `terminalEquiv` 的定义

English:
definition terminalEquiv
  signature: : ToType (⊤_ C) ≃ PUnit
  body: (PreservesTerminal.iso (forget C) ≪≫ Types.terminalIso).toEquiv

中文:
定义 terminalEquiv
  签名: : ToType (⊤_ C) ≃ 命题单元
  定义体: (PreservesTerminal.iso (forget C) ≪≫ Types.terminalIso).toEquiv

Depends on / 依赖: PreservesTerminal, PreservesTerminal.iso, Types.terminalIso, forget, terminalIso, toEquiv
-/
noncomputable def terminalEquiv : ToType (⊤_ C) ≃ PUnit :=
  (PreservesTerminal.iso (forget C) ≪≫ Types.terminalIso).toEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (ToType (⊤_ C))
  body: (terminalEquiv C).symm PUnit.unit
  uniq _ := (terminalEquiv C).injective (Subsingleton.elim _ _)

中文:
实例 :
  签名: 唯一 (ToType (⊤_ C))
  定义体: (terminalEquiv C).symm PUnit.unit
  uniq _ := (terminalEquiv C).injective (Subsingleton.elim _ _)

Depends on / 依赖: PUnit.unit, terminalEquiv
-/
noncomputable instance : Unique (ToType (⊤_ C)) where
  default := (terminalEquiv C).symm PUnit.unit
  uniq _ := (terminalEquiv C).injective (Subsingleton.elim _ _)

end Terminal

section Initial

variable {FC : C -> C -> Type*} {CC : C -> Type w} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{w} C FC]

/--
lemma `empty_of_initial_of_preserves` / 引理 `empty_of_initial_of_preserves`

English:
lemma empty_of_initial_of_preserves
  statement: [PreservesColimit (Functor.empty.{0} C) (forget C)] (X : C)
  proof: by
  rw [← Types.initial_iff_empty]
  exact Nonempty.map (IsInitial.isInitialObj (forget C) _) h

中文:
引理 empty_of_initial_of_preserves
  结论: [保持余极限 (函子.empty.{0} C) (forget C)] (X : C)
  证明: by
  rw [← Types.initial_iff_empty]
  exact Nonempty.map (IsInitial.isInitialObj (forget C) _) h

Depends on / 依赖: IsInitial, IsInitial.isInitialObj, Nonempty, Nonempty.map, Types.initial_iff_empty, forget, initial_iff_empty, isInitialObj
-/
lemma empty_of_initial_of_preserves [PreservesColimit (Functor.empty.{0} C) (forget C)] (X : C)
    (h : Nonempty (IsInitial X)) : IsEmpty (ToType X) := by
  rw [← Types.initial_iff_empty]
  exact Nonempty.map (IsInitial.isInitialObj (forget C) _) h

/--
lemma `initial_of_empty_of_reflects` / 引理 `initial_of_empty_of_reflects`

English:
lemma initial_of_empty_of_reflects
  statement: [ReflectsColimit (Functor.empty.{0} C) (forget C)] (X : C)
  proof: Nonempty.map (IsInitial.isInitialOfObj (forget C) _)
    (Types.initial_iff_empty (ToType X)).mpr h

中文:
引理 initial_of_empty_of_reflects
  结论: [反映余极限 (函子.empty.{0} C) (forget C)] (X : C)
  证明: Nonempty.map (IsInitial.isInitialOfObj (forget C) _)
    (Types.initial_iff_empty (ToType X)).mpr h

Depends on / 依赖: IsInitial, IsInitial.isInitialOfObj, Nonempty, Nonempty.map, ToType, Types.initial_iff_empty, forget, initial_iff_empty, isInitialOfObj
-/
lemma initial_of_empty_of_reflects [ReflectsColimit (Functor.empty.{0} C) (forget C)] (X : C)
    (h : IsEmpty (ToType X)) : Nonempty (IsInitial X) :=
Nonempty.map (IsInitial.isInitialOfObj (forget C) _)
    (Types.initial_iff_empty (ToType X)).mpr h

/--
lemma `initial_iff_empty_of_preserves_of_reflects` / 引理 `initial_iff_empty_of_preserves_of_reflects`

English:
lemma initial_iff_empty_of_preserves_of_reflects
  statement: [PreservesColimit (Functor.empty.{0} C) (forget C)]
  proof: by
  rw [← Types.initial_iff_empty]; rw [(IsInitial.isInitialIffObj (forget C) X).nonempty_congr]

中文:
引理 initial_iff_empty_of_preserves_of_reflects
  结论: [保持余极限 (函子.empty.{0} C) (forget C)]
  证明: by
  rw [← Types.initial_iff_empty]; rw [(IsInitial.isInitialIffObj (forget C) X).nonempty_congr]

Depends on / 依赖: IsInitial, IsInitial.isInitialIffObj, Types.initial_iff_empty, forget, initial_iff_empty, isInitialIffObj, nonempty_congr
-/
lemma initial_iff_empty_of_preserves_of_reflects [PreservesColimit (Functor.empty.{0} C) (forget C)]
    [ReflectsColimit (Functor.empty.{0} C) (forget C)] (X : C) :
    Nonempty (IsInitial X) ↔ IsEmpty (ToType X) := by
  rw [← Types.initial_iff_empty]; rw [(IsInitial.isInitialIffObj (forget C) X).nonempty_congr]

end Initial

section BinaryProducts

variable {FC : C -> C -> Type*} {CC : C -> Type w} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{w} C FC] (X₁ X₂ : C) [HasBinaryProduct X₁ X₂]
  [PreservesLimit (pair X₁ X₂) (forget C)]

/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: : ToType (X₁ ⨯ X₂) ≃ ToType X₁ × ToType X₂
  body: (PreservesLimitPair.iso (forget C) X₁ X₂ ≪≫ Types.binaryProductIso _ _).toEquiv

@[simp]

中文:
定义 prodEquiv
  签名: : ToType (X₁ ⨯ X₂) ≃ ToType X₁ × ToType X₂
  定义体: (PreservesLimitPair.iso (forget C) X₁ X₂ ≪≫ Types.binaryProductIso _ _).toEquiv

@[simp]

Depends on / 依赖: Category, Category.comp_id, IsBilimit, IsBilimit.total, PreservesLimitPair, PreservesLimitPair.iso, Types.binaryProductIso, binaryProductIso, comp_id, forget, id_tensorHom, id_tensorHom_id, isBilimitOfTotal, nonempty_fintype, preserves, simp_rw, tensorHom_comp_tensorHom, tensor_sum, toEquiv
-/
noncomputable def prodEquiv : ToType (X₁ ⨯ X₂) ≃ ToType X₁ × ToType X₂ :=
  (PreservesLimitPair.iso (forget C) X₁ X₂ ≪≫ Types.binaryProductIso _ _).toEquiv

@[simp]
/--
lemma `prodEquiv_apply_fst` / 引理 `prodEquiv_apply_fst`

English:
lemma prodEquiv_apply_fst
  given: (x : ToType (X₁ ⨯ X₂))
  proof: by
  simpa using! congr_hom (prodComparison_fst (forget C) X₁ X₂) x

@[simp]

中文:
引理 prodEquiv_apply_fst
  条件: (x : ToType (X₁ ⨯ X₂))
  证明: by
  simpa using! congr_hom (prodComparison_fst (forget C) X₁ X₂) x

@[simp]

Depends on / 依赖: Category, Category.comp_id, IsBilimit, IsBilimit.total, comp_id, congr_hom, forget, id_tensorHom_id, isBilimitOfTotal, nonempty_fintype, preserves, prodComparison_fst, simp_rw, sum_tensor, tensorHom_comp_tensorHom, tensorHom_id
-/
lemma prodEquiv_apply_fst (x : ToType (X₁ ⨯ X₂)) :
    (prodEquiv X₁ X₂ x).fst = (Limits.prod.fst : X₁ ⨯ X₂ ⟶ X₁) x := by
  simpa using! congr_hom (prodComparison_fst (forget C) X₁ X₂) x

@[simp]
/--
lemma `prodEquiv_apply_snd` / 引理 `prodEquiv_apply_snd`

English:
lemma prodEquiv_apply_snd
  given: (x : ToType (X₁ ⨯ X₂))
  proof: by
  simpa using! congr_hom (prodComparison_snd (forget C) X₁ X₂) x

@[simp]

中文:
引理 prodEquiv_apply_snd
  条件: (x : ToType (X₁ ⨯ X₂))
  证明: by
  simpa using! congr_hom (prodComparison_snd (forget C) X₁ X₂) x

@[simp]

Depends on / 依赖: congr_hom, forget, prodComparison_snd
-/
lemma prodEquiv_apply_snd (x : ToType (X₁ ⨯ X₂)) :
    (prodEquiv X₁ X₂ x).snd = (Limits.prod.snd : X₁ ⨯ X₂ ⟶ X₂) x := by
  simpa using! congr_hom (prodComparison_snd (forget C) X₁ X₂) x

@[simp]
/--
lemma `prodEquiv_symm_apply_fst` / 引理 `prodEquiv_symm_apply_fst`

English:
lemma prodEquiv_symm_apply_fst
  given: (x : ToType X₁ × ToType X₂)
  proof: by
  obtain ⟨y, rfl⟩ := (prodEquiv X₁ X₂).surjective x
  simp

@[simp]

中文:
引理 prodEquiv_symm_apply_fst
  条件: (x : ToType X₁ × ToType X₂)
  证明: by
  obtain ⟨y, rfl⟩ := (prodEquiv X₁ X₂).surjective x
  simp

@[simp]

Depends on / 依赖: prodEquiv, surjective
-/
lemma prodEquiv_symm_apply_fst (x : ToType X₁ × ToType X₂) :
    (Limits.prod.fst : X₁ ⨯ X₂ ⟶ X₁) ((prodEquiv X₁ X₂).symm x) = x.1 := by
  obtain ⟨y, rfl⟩ := (prodEquiv X₁ X₂).surjective x
  simp

@[simp]
/--
lemma `prodEquiv_symm_apply_snd` / 引理 `prodEquiv_symm_apply_snd`

English:
lemma prodEquiv_symm_apply_snd
  given: (x : ToType X₁ × ToType X₂)
  proof: by
  obtain ⟨y, rfl⟩ := (prodEquiv X₁ X₂).surjective x
  simp

中文:
引理 prodEquiv_symm_apply_snd
  条件: (x : ToType X₁ × ToType X₂)
  证明: by
  obtain ⟨y, rfl⟩ := (prodEquiv X₁ X₂).surjective x
  simp

Depends on / 依赖: prodEquiv, surjective
-/
lemma prodEquiv_symm_apply_snd (x : ToType X₁ × ToType X₂) :
    (Limits.prod.snd : X₁ ⨯ X₂ ⟶ X₂) ((prodEquiv X₁ X₂).symm x) = x.2 := by
  obtain ⟨y, rfl⟩ := (prodEquiv X₁ X₂).surjective x
  simp

end BinaryProducts

section Pullbacks

variable {FC : C -> C -> Type*} {CC : C -> Type v} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{v} C FC]
variable {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    [HasPullback f₁ f₂] [PreservesLimit (cospan f₁ f₂) (forget C)]

/--
Definition of `pullbackEquiv` / `pullbackEquiv` 的定义

English:
definition pullbackEquiv
  signature: :
  body: (PreservesPullback.iso (forget C) f₁ f₂ ≪≫
    Types.pullbackIsoPullback (↾f₁) (↾f₂)).toEquiv

中文:
定义 pullbackEquiv
  签名: :
  定义体: (PreservesPullback.iso (forget C) f₁ f₂ ≪≫
    Types.pullbackIsoPullback (↾f₁) (↾f₂)).toEquiv

Depends on / 依赖: PreservesPullback, PreservesPullback.iso, Types.pullbackIsoPullback, forget, pullbackIsoPullback, toEquiv
-/
noncomputable def pullbackEquiv :
    ToType (pullback f₁ f₂) ≃ { p : ToType X₁ × ToType X₂ // f₁ p.1 = f₂ p.2 } :=
  (PreservesPullback.iso (forget C) f₁ f₂ ≪≫
    Types.pullbackIsoPullback (↾f₁) (↾f₂)).toEquiv

/--
Definition of `pullbackMk` / `pullbackMk` 的定义

English:
definition pullbackMk
  signature: (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂)
  body: (pullbackEquiv f₁ f₂).symm ⟨⟨x₁, x₂⟩, h⟩

中文:
定义 pullbackMk
  签名: (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂)
  定义体: (pullbackEquiv f₁ f₂).symm ⟨⟨x₁, x₂⟩, h⟩

Depends on / 依赖: pullbackEquiv
-/
noncomputable def pullbackMk (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂) :
    ToType (pullback f₁ f₂) :=
  (pullbackEquiv f₁ f₂).symm ⟨⟨x₁, x₂⟩, h⟩

/--
lemma `pullbackMk_surjective` / 引理 `pullbackMk_surjective`

English:
lemma pullbackMk_surjective
  given: (x : ToType (pullback f₁ f₂))
  proof: by
  obtain ⟨⟨⟨x₁, x₂⟩, h⟩, rfl⟩ := (pullbackEquiv f₁ f₂).symm.surjective x
  exact ⟨x₁, x₂, h, rfl⟩

@[simp]

中文:
引理 pullbackMk_surjective
  条件: (x : ToType (pullback f₁ f₂))
  证明: by
  obtain ⟨⟨⟨x₁, x₂⟩, h⟩, rfl⟩ := (pullbackEquiv f₁ f₂).symm.surjective x
  exact ⟨x₁, x₂, h, rfl⟩

@[simp]

Depends on / 依赖: pullbackEquiv, surjective, symm.surjective
-/
lemma pullbackMk_surjective (x : ToType (pullback f₁ f₂)) :
    exists (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂), x = pullbackMk f₁ f₂ x₁ x₂ h := by
  obtain ⟨⟨⟨x₁, x₂⟩, h⟩, rfl⟩ := (pullbackEquiv f₁ f₂).symm.surjective x
  exact ⟨x₁, x₂, h, rfl⟩

@[simp]
/--
lemma `pullbackMk_fst` / 引理 `pullbackMk_fst`

English:
lemma pullbackMk_fst
  given: (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂)
  proof: (congr_hom (PreservesPullback.iso_inv_fst (forget C) f₁ f₂) _).trans
    (congr_hom (Types.pullbackIsoPullback_inv_fst (↾f₁) (↾f₂)) _)

@[simp]

中文:
引理 pullbackMk_fst
  条件: (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂)
  证明: (congr_hom (PreservesPullback.iso_inv_fst (forget C) f₁ f₂) _).trans
    (congr_hom (Types.pullbackIsoPullback_inv_fst (↾f₁) (↾f₂)) _)

@[simp]

Depends on / 依赖: PreservesPullback, PreservesPullback.iso_inv_fst, Types.pullbackIsoPullback_inv_fst, congr_hom, forget, iso_inv_fst, pullbackIsoPullback_inv_fst
-/
lemma pullbackMk_fst (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂) :
    pullback.fst f₁ f₂ (pullbackMk f₁ f₂ x₁ x₂ h) = x₁ :=
  (congr_hom (PreservesPullback.iso_inv_fst (forget C) f₁ f₂) _).trans
    (congr_hom (Types.pullbackIsoPullback_inv_fst (↾f₁) (↾f₂)) _)

@[simp]
/--
lemma `pullbackMk_snd` / 引理 `pullbackMk_snd`

English:
lemma pullbackMk_snd
  given: (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂)
  proof: (congr_hom (PreservesPullback.iso_inv_snd (forget C) f₁ f₂) _).trans
    (congr_hom (Types.pullbackIsoPullback_inv_snd (↾f₁) (↾f₂)) _)

中文:
引理 pullbackMk_snd
  条件: (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂)
  证明: (congr_hom (PreservesPullback.iso_inv_snd (forget C) f₁ f₂) _).trans
    (congr_hom (Types.pullbackIsoPullback_inv_snd (↾f₁) (↾f₂)) _)

Depends on / 依赖: PreservesPullback, PreservesPullback.iso_inv_snd, Types.pullbackIsoPullback_inv_snd, congr_hom, forget, iso_inv_snd, pullbackIsoPullback_inv_snd
-/
lemma pullbackMk_snd (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂) :
    pullback.snd f₁ f₂ (pullbackMk f₁ f₂ x₁ x₂ h) = x₂ :=
  (congr_hom (PreservesPullback.iso_inv_snd (forget C) f₁ f₂) _).trans
    (congr_hom (Types.pullbackIsoPullback_inv_snd (↾f₁) (↾f₂)) _)

end Pullbacks

section WidePullback

variable {FC : C -> C -> Type*} {CC : C -> Type (max v w)} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{max v w} C FC]

open WidePullback

open WidePullbackShape

/--
theorem `widePullback_ext` / 定理 `widePullback_ext`

English:
theorem widePullback_ext
  statement: {B : C} {ι : Type w} {X : ι -> C} (f : forall j : ι, X j ⟶ B)
  proof: by
  apply Concrete.limit_ext
  rintro (_ | j)
  · exact h₀
  · apply h

中文:
定理 widePullback_ext
  结论: {B : C} {ι : 类型 w} {X : ι -> C} (f : 对任意 j : ι, X j ⟶ B)
  证明: by
  apply Concrete.limit_ext
  rintro (_ | j)
  · exact h₀
  · apply h

Depends on / 依赖: Concrete, Concrete.limit_ext, limit_ext
-/
theorem widePullback_ext {B : C} {ι : Type w} {X : ι -> C} (f : forall j : ι, X j ⟶ B)
    [HasWidePullback B X f] [PreservesLimit (wideCospan B X f) (forget C)]
    (x y : ToType (widePullback B X f)) (h₀ : base f x = base f y) (h : forall j, π f j x = π f j y) :
    x = y := by
  apply Concrete.limit_ext
  rintro (_ | j)
  · exact h₀
  · apply h

/--
theorem `widePullback_ext'` / 定理 `widePullback_ext'`

English:
theorem widePullback_ext'
  statement: {B : C} {ι : Type w} [Nonempty ι] {X : ι -> C}
  proof: by
  apply Concrete.widePullback_ext _ _ _ _ h
  inhabit ι
  simp only [← π_arrow f default, ConcreteCategory.comp_apply, h]

中文:
定理 widePullback_ext'
  结论: {B : C} {ι : 类型 w} [非空 ι] {X : ι -> C}
  证明: by
  apply Concrete.widePullback_ext _ _ _ _ h
  inhabit ι
  simp only [← π_arrow f default, ConcreteCategory.comp_apply, h]

Depends on / 依赖: Concrete, Concrete.widePullback_ext, ConcreteCategory, ConcreteCategory.comp_apply, comp_apply, inhabit, widePullback_ext
-/
theorem widePullback_ext' {B : C} {ι : Type w} [Nonempty ι] {X : ι -> C}
    (f : forall j : ι, X j ⟶ B) [HasWidePullback.{w} B X f]
    [PreservesLimit (wideCospan B X f) (forget C)] (x y : ToType (widePullback B X f))
    (h : forall j, π f j x = π f j y) : x = y := by
  apply Concrete.widePullback_ext _ _ _ _ h
  inhabit ι
  simp only [← π_arrow f default, ConcreteCategory.comp_apply, h]

end WidePullback

section Multiequalizer

variable {FC : C -> C -> Type*} {CC : C -> Type s} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{s} C FC]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `multiequalizer_ext` / 定理 `multiequalizer_ext`

English:
theorem multiequalizer_ext
  statement: {J : MulticospanShape.{w, w'}}
  proof: by
  apply Concrete.limit_ext
  rintro (a | b)
  · apply h
  · rw [← limit.w I.multicospan (WalkingMulticospan.Hom.fst b), ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply]
    simp [h]

中文:
定理 multiequalizer_ext
  结论: {J : MulticospanShape.{w, w'}}
  证明: by
  apply Concrete.limit_ext
  rintro (a | b)
  · apply h
  · rw [← limit.w I.multicospan (WalkingMulticospan.Hom.fst b), ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply]
    simp [h]

Depends on / 依赖: Concrete, Concrete.limit_ext, ConcreteCategory, ConcreteCategory.comp_apply, I.multicospan, WalkingMulticospan, WalkingMulticospan.Hom.fst, comp_apply, limit.w, limit_ext, multicospan
-/
theorem multiequalizer_ext {J : MulticospanShape.{w, w'}}
    {I : MulticospanIndex J C} [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] (x y : ToType (multiequalizer I))
    (h : forall t : J.L, Multiequalizer.ι I t x = Multiequalizer.ι I t y) : x = y := by
  apply Concrete.limit_ext
  rintro (a | b)
  · apply h
  · rw [← limit.w I.multicospan (WalkingMulticospan.Hom.fst b), ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply]
    simp [h]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `multiequalizerEquivAux` / `multiequalizerEquivAux` 的定义

English:
definition multiequalizerEquivAux
  signature: {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
  body: ⟨fun _ => x.1 (WalkingMulticospan.left _), fun i => by
      have a := x.2 (WalkingMulticospan.Hom.fst i)
      have b := x.2 (WalkingMulticospan.Hom.snd i)
      rw [← b] at a
      exact a⟩
  invFun x :=
    { val := fun j =>
        match j with
        | WalkingMulticospan.left _ => x.1 _
      

中文:
定义 multiequalizerEquivAux
  签名: {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
  定义体: ⟨fun _ => x.1 (WalkingMulticospan.left _), fun i => by
      have a := x.2 (WalkingMulticospan.Hom.fst i)
      have b := x.2 (WalkingMulticospan.Hom.snd i)
      rw [← b] at a
      exact a⟩
  invFun x :=
    { val := fun j =>
        match j with
        | WalkingMulticospan.left _ => x.1 _
      

Depends on / 依赖: Functor, Functor.map_id, I.fst, WalkingMulticospan, WalkingMulticospan.Hom.fst, WalkingMulticospan.Hom.id_eq_id, WalkingMulticospan.Hom.snd, WalkingMulticospan.left, WalkingMulticospan.right, id_eq_id, invFun, map_id, property
-/
def multiequalizerEquivAux {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C) :
    (I.multicospan ⋙ forget C).sections ≃
    { x : forall i : J.L, ToType (I.left i) // forall i : J.R, I.fst i (x _) = I.snd i (x _) } where
  toFun x :=
    ⟨fun _ => x.1 (WalkingMulticospan.left _), fun i => by
      have a := x.2 (WalkingMulticospan.Hom.fst i)
      have b := x.2 (WalkingMulticospan.Hom.snd i)
      rw [← b] at a
      exact a⟩
  invFun x :=
    { val := fun j =>
        match j with
        | WalkingMulticospan.left _ => x.1 _
        | WalkingMulticospan.right b => I.fst b (x.1 _)
      property := by
        rintro (a | b) (a' | b') (f | f | f)
        · simp only [WalkingMulticospan.Hom.id_eq_id, Functor.map_id]; rfl
        · rfl
        · dsimp
          exact (x.2 b').symm
        · simp only [WalkingMulticospan.Hom.id_eq_id, Functor.map_id]; rfl }
  left_inv := by
    intro x; ext (a | b)
    · rfl
    · rw [← x.2 (WalkingMulticospan.Hom.fst b)]
      rfl
  right_inv := by
    intro x
    ext i
    rfl

/--
Definition of `multiequalizerEquiv` / `multiequalizerEquiv` 的定义

English:
definition multiequalizerEquiv
  signature: {J : MulticospanShape.{w, w'}}
  body: letI h1 := limit.isLimit I.multicospan
  letI h2 := isLimitOfPreserves (forget C) h1
  (Types.isLimitEquivSections h2).trans (Concrete.multiequalizerEquivAux I)

@[simp]

中文:
定义 multiequalizerEquiv
  签名: {J : MulticospanShape.{w, w'}}
  定义体: letI h1 := limit.isLimit I.multicospan
  letI h2 := isLimitOfPreserves (forget C) h1
  (Types.isLimitEquivSections h2).trans (Concrete.multiequalizerEquivAux I)

@[simp]

Depends on / 依赖: Concrete, Concrete.multiequalizerEquivAux, I.multicospan, Types.isLimitEquivSections, forget, isLimit, isLimitEquivSections, isLimitOfPreserves, limit.isLimit, multicospan, multiequalizerEquivAux
-/
noncomputable def multiequalizerEquiv {J : MulticospanShape.{w, w'}}
    (I : MulticospanIndex J C) [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] :
    ToType (multiequalizer I) ≃
      { x : forall i : J.L, ToType (I.left i) // forall i : J.R, I.fst i (x _) = I.snd i (x _) } :=
  letI h1 := limit.isLimit I.multicospan
  letI h2 := isLimitOfPreserves (forget C) h1
  (Types.isLimitEquivSections h2).trans (Concrete.multiequalizerEquivAux I)

@[simp]
/--
theorem `multiequalizerEquiv_apply` / 定理 `multiequalizerEquiv_apply`

English:
theorem multiequalizerEquiv_apply
  statement: {J : MulticospanShape.{w, w'}}
  proof: rfl

中文:
定理 multiequalizerEquiv_apply
  结论: {J : MulticospanShape.{w, w'}}
  证明: rfl
-/
theorem multiequalizerEquiv_apply {J : MulticospanShape.{w, w'}}
    (I : MulticospanIndex J C) [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] (x : ToType (multiequalizer I)) (i : J.L) :
    ((Concrete.multiequalizerEquiv I) x : forall i : J.L, ToType (I.left i)) i =
      Multiequalizer.ι I i x :=
  rfl

end Multiequalizer

section WidePushout

open WidePushout

open WidePushoutShape

variable {FC : C -> C -> Type*} {CC : C -> Type v} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{v} C FC]

/--
theorem `widePushout_exists_rep` / 定理 `widePushout_exists_rep`

English:
theorem widePushout_exists_rep
  statement: {B : C} {α : Type _} {X : α -> C} (f : forall j : α, B ⟶ X j)
  proof: by
  obtain ⟨_ | j, y, rfl⟩ := Concrete.colimit_exists_rep _ x
  · left
    use y
    rfl
  · right
    use j, y
    rfl

中文:
定理 widePushout_存在_rep
  结论: {B : C} {α : 类型 _} {X : α -> C} (f : 对任意 j : α, B ⟶ X j)
  证明: by
  obtain ⟨_ | j, y, rfl⟩ := Concrete.colimit_exists_rep _ x
  · left
    use y
    rfl
  · right
    use j, y
    rfl

Depends on / 依赖: Concrete, Concrete.colimit_exists_rep, colimit_exists_rep
-/
theorem widePushout_exists_rep {B : C} {α : Type _} {X : α -> C} (f : forall j : α, B ⟶ X j)
    [HasWidePushout.{v} B X f] [PreservesColimit (wideSpan B X f) (forget C)]
    (x : ToType (widePushout B X f)) :
    (exists y : ToType B, head f y = x) ∨ exists (i : α) (y : ToType (X i)), ι f i y = x := by
  obtain ⟨_ | j, y, rfl⟩ := Concrete.colimit_exists_rep _ x
  · left
    use y
    rfl
  · right
    use j, y
    rfl

/--
theorem `widePushout_exists_rep'` / 定理 `widePushout_exists_rep'`

English:
theorem widePushout_exists_rep'
  statement: {B : C} {α : Type _} [Nonempty α] {X : α -> C}
  proof: by
  rcases Concrete.widePushout_exists_rep f x with (⟨y, rfl⟩ | ⟨i, y, rfl⟩)
  · inhabit α
    use default, f _ y
    simp only [← arrow_ι _ default, ConcreteCategory.comp_apply]
  · use i, y

中文:
定理 widePushout_存在_rep'
  结论: {B : C} {α : 类型 _} [非空 α] {X : α -> C}
  证明: by
  rcases Concrete.widePushout_exists_rep f x with (⟨y, rfl⟩ | ⟨i, y, rfl⟩)
  · inhabit α
    use default, f _ y
    simp only [← arrow_ι _ default, ConcreteCategory.comp_apply]
  · use i, y

Depends on / 依赖: Concrete, Concrete.widePushout_exists_rep, ConcreteCategory, ConcreteCategory.comp_apply, comp_apply, inhabit, widePushout_exists_rep
-/
theorem widePushout_exists_rep' {B : C} {α : Type _} [Nonempty α] {X : α -> C}
    (f : forall j : α, B ⟶ X j) [HasWidePushout.{v} B X f] [PreservesColimit (wideSpan B X f) (forget C)]
    (x : ToType (widePushout B X f)) : exists (i : α) (y : ToType (X i)), ι f i y = x := by
  rcases Concrete.widePushout_exists_rep f x with (⟨y, rfl⟩ | ⟨i, y, rfl⟩)
  · inhabit α
    use default, f _ y
    simp only [← arrow_ι _ default, ConcreteCategory.comp_apply]
  · use i, y

end WidePushout

attribute [local ext] ConcreteCategory.hom_ext in
-- We don't mark this as an `@[ext]` lemma as we don't always want to work elementwise.
/--
theorem `cokernel_funext` / 定理 `cokernel_funext`

English:
theorem cokernel_funext
  statement: {C : Type*} [Category* C] [HasZeroMorphisms C] {FC : C -> C -> Type*}
  proof: by
  ext x
  simpa using w x

中文:
定理 cokernel_funext
  结论: {C : 类型} [范畴* C] [有ZeroMorphisms C] {FC : C -> C -> 类型}
  证明: by
  ext x
  simpa using w x
-/
theorem cokernel_funext {C : Type*} [Category* C] [HasZeroMorphisms C] {FC : C -> C -> Type*}
    {CC : C -> Type*} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {M N K : C} {f : M ⟶ N} [HasCokernel f] {g h : cokernel f ⟶ K}
    (w : forall n : ToType N, g (cokernel.π f n) = h (cokernel.π f n)) : g = h := by
  ext x
  simpa using w x

-- TODO: Add analogous lemmas about coproducts and coequalizers.

end CategoryTheory.Limits.Concrete
