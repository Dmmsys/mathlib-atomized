/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.DayConvolution

/-!
# Day functors

In this file, given a monoidal category `C` and a monoidal category `V`,
we define a basic type synonym `DayFunctor C V` (denoted `C ⊛⥤ D`)
for the category `C ⥤ V` and endow it with the monoidal structure coming
from Day convolution. Such a setup is necessary as by default,
the `MonoidalCategory` instance on `C ⥤ V` is the "pointwise" one,
where the tensor product of `F` and `G` is the functor `x ↦ F.obj x ⊗ G.obj x`.

## TODOs
- Given a `LawfulDayConvolutionMonoidalCategoryStruct C V D`, show that
  ι induces a monoidal functor `D ⥤ (C ⊛⥤ V)`.
- Specialize to the case `V := Type _`, and prove a universal property stating
  that for every monoidal category `W` with suitable colimits,
  colimit-preserving monoidal functors `(Cᵒᵖ ⊛⥤ Type u) ⥤ W` are equivalent to
  monoidal functors `C ⥤ W`. Show that the Yoneda embedding is monoidal.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.MonoidalCategory
open scoped ExternalProduct

noncomputable section

/-- `DayFunctor C V` is a type synonym for `C ⥤ V`, implemented as a one-field
structure. -/
/-
**CategoryTheory.MonoidalCategory.DayFunctor** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.MonoidalCategory`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (V : T
ype u₂) →       [inst_1 : CategoryTheory.Category.{v₂, u₂} V] →         [Categor
yTheory.MonoidalCategory C] → [CategoryTheory.MonoidalCategory V] → Type (max (m
ax (max u₁ u₂) v₁) v₂)
参数：max (max u₁ u₂) v₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DayFunctor C V` is a type synonym for `C ⥤ V`, implemented as a one-field
structure.
-/
structure DayFunctor
    (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V] where
  /-- the underlying functor. -/
  functor : C ⥤ V

namespace DayFunctor

/-- Notation for `DayFunctor`. -/
scoped infixr:26 " ⊛⥤ " => DayFunctor

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]

/-
**CategoryTheory.MonoidalCategory.DayFunctor.mk_functor** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MonoidalCategory.DayFunctor`。
形式化陈述：mk_functor (F : C ⥤ V) : (mk F).functor = F
参数：F : C ⥤ V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_functor (F : C ⥤ V) : (mk F).functor = F := rfl

@[simp]
/-
**CategoryTheory.MonoidalCategory.DayFunctor.functor_mk** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MonoidalCategory.DayFunctor`。
形式化陈述：functor_mk (F : C ⊛⥤ V) : mk F.functor = F
参数：F : C ⊛⥤ V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functor_mk (F : C ⊛⥤ V) : mk F.functor = F := rfl

/-- Morphisms of Day functors are natural transformations of the underlying
functors. -/
/-
**CategoryTheory.MonoidalCategory.DayFunctor.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ca
tegoryTheory.MonoidalCategory.DayFunctor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {V : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} V] →         [inst_2 
: CategoryTheory.MonoidalCategory C] →           [inst_3 : CategoryTheory.Monoid
alCategory V] →             CategoryTheory.MonoidalCategory.DayFunctor C V →    
           CategoryTheory.MonoidalCategory.DayFunctor C V → Type (max u₁ v₂)
参数：max u₁ v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms of Day functors are natural transformations of the underlying
functors.
-/
structure Hom (F G : C ⊛⥤ V) where
  /-- the underlying natural transformation -/
  natTrans : F.functor ⟶ G.functor

@[simps id_natTrans comp_natTrans]
/-
**CategoryTheory.MonoidalCategory.DayFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.MonoidalCategory.DayFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (C ⊛⥤ V) where
  Hom := Hom
  id x := .mk <| 𝟙 x.functor
  comp α β := .mk <| α.natTrans ≫ β.natTrans

@[ext]
/-
**CategoryTheory.MonoidalCategory.DayFunctor.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MonoidalCategory.DayFunctor`。
形式化陈述：hom_ext {F G : C ⊛⥤ V} {α β : F ⟶ G} (h : α.natTrans = β.natTrans) : α = β
参数：h : α.natTrans = β.natTrans。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma hom_ext {F G : C ⊛⥤ V} {α β : F ⟶ G} (h : α.natTrans = β.natTrans) :
    α = β := by
  cases α
  cases β
  grind

variable (C V) in
/-- The tautological equivalence of categories between `C ⥤ V` and `C ⊛⥤ V`. -/
@[simps! functor_obj functor_map inverse_obj_functor inverse_map_natTrans
  unitIso_hom_app unitIso_inv_app counitIso_hom_app counitIso_inv_app]
/-
**CategoryTheory.MonoidalCategory.DayFunctor.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MonoidalCategory.DayFunctor`。
形式化陈述：equiv : (C ⊛⥤ V) ≌ (C ⥤ V) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equiv : (C ⊛⥤ V) ≌ (C ⥤ V) where
  functor :=
    { obj F := F.functor
      map α := α.natTrans }
  inverse :=
    { obj F := .mk F
      map α := .mk α }
  unitIso := .refl _
  counitIso := .refl _

variable
    [hasDayConvolution : ∀ (F G : C ⥤ V),
      (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [hasDayConvolutionUnit :
      (Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
        (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d)
        (tensorRight v)]
    [∀ (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]
/-
**CategoryTheory.MonoidalCategory.DayFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.MonoidalCategory.DayFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalCategory (C ⊛⥤ V) :=
  monoidalOfHasDayConvolutions
    (equiv C V).functor
    (equiv C V).fullyFaithfulFunctor
    (fun _ _ => ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩)
    ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩

@[simps! ι_obj ι_map]
/-
**CategoryTheory.MonoidalCategory.DayFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.MonoidalCategory.DayFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulDayConvolutionMonoidalCategoryStruct C V (C ⊛⥤ V) :=
  lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions
    (equiv C V).functor
    (equiv C V).fullyFaithfulFunctor
    (fun _ _ => ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩)
    ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩

/-- The unit transformation exhibiting `(F ⊗ G).functor` as a left Kan extension of
`F.functor ⊠ G.functor` along `tensor C`. -/
/-
**CategoryTheory.MonoidalCategory.DayFunctor.** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MonoidalCategory.DayFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit transformation exhibiting `(F ⊗ G).functor` as a left Kan extension of
`F.functor ⊠ G.functor` along `tensor C`.
-/
def η (F G : C ⊛⥤ V) :
    F.functor ⊠ G.functor ⟶ tensor C ⋙ (F ⊗ G).functor :=
  LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit
    C V F G

open LawfulDayConvolutionMonoidalCategoryStruct in
/-
**CategoryTheory.MonoidalCategory.DayFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.MonoidalCategory.DayFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F G : C ⊛⥤ V) : (F ⊗ G).functor.IsLeftKanExtension (η F G) :=
  (isPointwiseLeftKanExtensionConvolutionExtensionUnit F G).isLeftKanExtension

open LawfulDayConvolutionMonoidalCategoryStruct in
/-
**CategoryTheory.MonoidalCategory.DayFunctor.tensor_hom_ext** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.MonoidalCategory.DayFunctor`。
形式化陈述：tensor_hom_ext {F G H : C ⊛⥤ V} {α β : F otimes G ⟶ H} (h : forall (x y : 
C), (η F G).app (x, y) ≫ α.natTrans.app (x otimes y) = (η F G).app (x, y) ≫ β.na
tTrans.app (x otimes y)) : α = β
参数：h : forall (x y : C), (η F G).app (x, y) ≫ α.natTrans.app (x otimes y) = (η F
 G).app (x, y) ≫ β.natTrans.app (x otimes y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MonoidalCategory.DayFunctor.hom_ext`：hom_ext {F G : C ⊛⥤ 
V} {α β : F ⟶ G} (h : α.natTrans = β.natTrans) : α = β
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
· 使用定理 `CategoryTheory.MonoidalCategory.DayFunctor.instIsLeftKanExtensionProdFun
ctorTensorObjη`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V :
 Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem tensor_hom_ext {F G H : C ⊛⥤ V} {α β : F ⊗ G ⟶ H}
    (h : ∀ (x y : C),
      (η F G).app (x, y) ≫ α.natTrans.app (x ⊗ y) =
      (η F G).app (x, y) ≫ β.natTrans.app (x ⊗ y)) :
    α = β := by
  ext : 1
  apply Functor.hom_ext_of_isLeftKanExtension
    (F ⊗ G).functor (η F G) _
  ext ⟨x, y⟩
  exact h x y

/-- A natural transformation `F.functor ⊠ G.functor ⟶ tensor C ⋙ H.functor`
defines a morphism `F ⨂ G ⟶ H`. -/
/-
**CategoryTheory.MonoidalCategory.DayFunctor.tensorDesc** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.MonoidalCategory.DayFunctor`。
形式化陈述：tensorDesc {F G H : C ⊛⥤ V} (α : F.functor ⊠ G.functor ⟶ tensor C ⋙ H.func
tor) : F otimes G ⟶ H
参数：α : F.functor ⊠ G.functor ⟶ tensor C ⋙ H.functor。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalCategory.DayFunctor.instIsLeftKanExtensionProdFun
ctorTensorObjη`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V :
 Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…

--- 原说明 ---
A natural transformation `F.functor ⊠ G.functor ⟶ tensor C ⋙ H.functor`
defines a morphism `F ⨂ G ⟶ H`.
-/
def tensorDesc {F G H : C ⊛⥤ V}
    (α : F.functor ⊠ G.functor ⟶ tensor C ⋙ H.functor) :
    F ⊗ G ⟶ H :=
  .mk <| (F ⊗ G).functor.descOfIsLeftKanExtension (η F G) H.functor α
/-
**CategoryTheory.MonoidalCategory.DayFunctor.** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MonoidalCategory.DayFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma η_comp_tensorDec {F G H : C ⊛⥤ V}
    (α : F.functor ⊠ G.functor ⟶ tensor C ⋙ H.functor) :
    η F G ≫ Functor.whiskerLeft _ (tensorDesc α).natTrans = α :=
  Functor.descOfIsLeftKanExtension_fac _ _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayFunctor.** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MonoidalCategory.DayFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma η_comp_tensorDesc_app {F G H : C ⊛⥤ V}
    (α : F.functor ⊠ G.functor ⟶ tensor C ⋙ H.functor) (x y : C) :
    (η F G).app (x, y) ≫ (tensorDesc α).natTrans.app (x ⊗ y) = α.app (x, y) :=
  Functor.descOfIsLeftKanExtension_fac_app _ _ _ _ _

open LawfulDayConvolutionMonoidalCategoryStruct
/-- An abstract isomorphism between `(F ⊗ G).functor` and the generic pointwise
left Kan extension of `F.functor ⊠ G.functor` along the -/
/-
**CategoryTheory.MonoidalCategory.DayFunctor.isoPointwiseLeftKanExtension** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayFunctor`。
形式化陈述：isoPointwiseLeftKanExtension (F G : C ⊛⥤ V) : (F otimes G).functor ≅ (tens
or C).pointwiseLeftKanExtension (F.functor ⊠ G.functor)
参数：F G : C ⊛⥤ V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalCategory.DayFunctor.instIsLeftKanExtensionProdFun
ctorTensorObjη`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V :
 Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…

--- 原说明 ---
An abstract isomorphism between `(F ⊗ G).functor` and the generic pointwise
left Kan extension of `F.functor ⊠ G.functor` along the
-/
def isoPointwiseLeftKanExtension (F G : C ⊛⥤ V) :
    (F ⊗ G).functor ≅
    (tensor C).pointwiseLeftKanExtension (F.functor ⊠ G.functor) :=
  Functor.leftKanExtensionUnique
    (F ⊗ G).functor (η F G) _
    ((tensor C).pointwiseLeftKanExtensionUnit (F.functor ⊠ G.functor))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.MonoidalCategory.DayFunctor.** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MonoidalCategory.DayFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma η_comp_isoPointwiseLeftKanExtension_hom (F G : C ⊛⥤ V) (x y : C) :
    (η F G).app (x, y) ≫ (isoPointwiseLeftKanExtension F G).hom.app (x ⊗ y) =
    Limits.colimit.ι
      (CostructuredArrow.proj (tensor C) (x ⊗ y) ⋙ F.functor ⊠ G.functor)
      (.mk (Y := (x, y)) <| 𝟙 (x ⊗ y)) := by
  simpa [η, isoPointwiseLeftKanExtension] using!
    Functor.descOfIsLeftKanExtension_fac_app
      (F ⊗ G).functor (η F G) _
      ((tensor C).pointwiseLeftKanExtensionUnit (F.functor ⊠ G.functor)) (x, y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.MonoidalCategory.DayFunctor.** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MonoidalCategory.DayFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_comp_isoPointwiseLeftKanExtension_inv (F G : C ⊛⥤ V) (x y : C) :
    Limits.colimit.ι
      (CostructuredArrow.proj (tensor C) (x ⊗ y) ⋙ F.functor ⊠ G.functor)
        (.mk (Y := (x, y)) <| 𝟙 (x ⊗ y)) ≫
      (isoPointwiseLeftKanExtension F G).inv.app (x ⊗ y) =
    (η F G).app (x, y) := by
  simp [η, isoPointwiseLeftKanExtension]

variable (C V) in
/-- The canonical map `𝟙_ V ⟶ (𝟙_ (C ⊛⥤ V)).functor.obj (𝟙_ C)`
that exhibits `(𝟙_ (C ⊛⥤ V)).functor` as a Day convolution unit. -/
/-
**CategoryTheory.MonoidalCategory.DayFunctor.** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MonoidalCategory.DayFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `𝟙_ V ⟶ (𝟙_ (C ⊛⥤ V)).functor.obj (𝟙_ C)`
that exhibits `(𝟙_ (C ⊛⥤ V)).functor` as a Day convolution unit.
-/
def ν : 𝟙_ V ⟶ (𝟙_ (C ⊛⥤ V)).functor.obj (𝟙_ C) :=
  LawfulDayConvolutionMonoidalCategoryStruct.unitUnit C V (C ⊛⥤ V)

set_option backward.defeqAttrib.useBackward true in
variable (C V) in
/-- The reinterpretation of `ν` as a natural transformation. -/
@[simps]
/-
**CategoryTheory.MonoidalCategory.DayFunctor.** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MonoidalCategory.DayFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reinterpretation of `ν` as a natural transformation.
-/
def νNatTrans :
    Functor.fromPUnit.{0} (𝟙_ V) ⟶
      Functor.fromPUnit.{0} (𝟙_ C) ⋙ (𝟙_ (C ⊛⥤ V)).functor where
  app _ := ν C V

open LawfulDayConvolutionMonoidalCategoryStruct in
/-
**CategoryTheory.MonoidalCategory.DayFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.MonoidalCategory.DayFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (𝟙_ (C ⊛⥤ V)).functor.IsLeftKanExtension (νNatTrans C V) :=
  isPointwiseLeftKanExtensionUnitUnit C V (C ⊛⥤ V) |>.isLeftKanExtension
/-
**CategoryTheory.MonoidalCategory.DayFunctor.unit_hom_ext** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.MonoidalCategory.DayFunctor`。
形式化陈述：unit_hom_ext {F : C ⊛⥤ V} {α β : 𝟙_ (C ⊛⥤ V) ⟶ F} (h : ν C V ≫ α.natTrans.
app (𝟙_ C) = ν C V ≫ β.natTrans.app (𝟙_ C)) : α = β
参数：C ⊛⥤ V；h : ν C V ≫ α.natTrans.app (𝟙_ C) = ν C V ≫ β.natTrans.app (𝟙_ C)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MonoidalCategory.DayFunctor.hom_ext`：hom_ext {F G : C ⊛⥤ 
V} {α β : F ⟶ G} (h : α.natTrans = β.natTrans) : α = β
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
· 使用定理 `CategoryTheory.MonoidalCategory.DayFunctor.instIsLeftKanExtensionDiscret
ePUnitFunctorTensorUnitνNatTrans`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [ins
t_2 : Category…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma unit_hom_ext {F : C ⊛⥤ V} {α β : 𝟙_ (C ⊛⥤ V) ⟶ F}
    (h : ν C V ≫ α.natTrans.app (𝟙_ C) = ν C V ≫ β.natTrans.app (𝟙_ C)) :
    α = β := by
  ext1
  apply Functor.hom_ext_of_isLeftKanExtension
    (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
  ext
  exact h

set_option backward.defeqAttrib.useBackward true in
/-- Given `F : C ⊛⥤ V`, a morphism `𝟙_ V ⟶ F.functor.obj (𝟙_ C)` induces a
(unique) morphism `𝟙_ (C ⊛⥤ V) ⟶ F`. -/
/-
**CategoryTheory.MonoidalCategory.DayFunctor.unitDesc** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.MonoidalCategory.DayFunctor`。
形式化陈述：unitDesc {F : C ⊛⥤ V} (φ : 𝟙_ V ⟶ F.functor.obj (𝟙_ C)) : 𝟙_ (C ⊛⥤ V) ⟶ F
参数：φ : 𝟙_ V ⟶ F.functor.obj (𝟙_ C)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalCategory.DayFunctor.instIsLeftKanExtensionDiscret
ePUnitFunctorTensorUnitνNatTrans`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [ins
t_2 : Category…

--- 原说明 ---
Given `F : C ⊛⥤ V`, a morphism `𝟙_ V ⟶ F.functor.obj (𝟙_ C)` induces a
(unique) morphism `𝟙_ (C ⊛⥤ V) ⟶ F`.
-/
def unitDesc {F : C ⊛⥤ V} (φ : 𝟙_ V ⟶ F.functor.obj (𝟙_ C)) :
    𝟙_ (C ⊛⥤ V) ⟶ F :=
  .mk <| Functor.descOfIsLeftKanExtension (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
    F.functor { app _ := φ }

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayFunctor.** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MonoidalCategory.DayFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ν_comp_unitDesc {F : C ⊛⥤ V} (φ : 𝟙_ V ⟶ F.functor.obj (𝟙_ C)) :
    ν C V ≫ (unitDesc φ).natTrans.app (𝟙_ C) = φ :=
  Functor.descOfIsLeftKanExtension_fac_app (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
    F.functor { app _ := φ } default

end DayFunctor

end

end CategoryTheory.MonoidalCategory

