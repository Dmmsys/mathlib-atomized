/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Limits in the category of elements

We show that if `C` has limits of shape `I` and `A : C ⥤ Type w` preserves limits of shape `I`, then
the category of elements of `A` has limits of shape `I` and the forgetful functor
`π : A.Elements ⥤ C` creates them.

## Further results

- If `A` is (co)representable, then `A.Elements` has an initial object.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe w v₁ v u₁ u

namespace CategoryTheory

open Limits Opposite ConcreteCategory

variable {C : Type u} [Category.{v} C]

namespace CategoryOfElements

variable {A : C ⥤ Type w} {I : Type u₁} [Category.{v₁} I] [Small.{w} I]

namespace CreatesLimitsAux

variable (F : I ⥤ A.Elements)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (implementation) A system `(Fi, fi)_i` of elements induces an element in `lim_i A(Fi)`. -/
/-
**CategoryTheory.CategoryOfElements.CreatesLimitsAux.liftedConeElement'** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.CategoryOfElements.CreatesLimitsAux`。
形式化陈述：liftedConeElement' : limit ((F ⋙ π A) ⋙ A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) A system `(Fi, fi)_i` of elements induces an element in `lim_i 
A(Fi)`.
-/
noncomputable def liftedConeElement' : limit ((F ⋙ π A) ⋙ A) :=
  Types.Limit.mk _ (fun i => (F.obj i).2) (by simp)

@[simp]
/-
**CategoryTheory.CategoryOfElements.CreatesLimitsAux.** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.CategoryOfElements.CreatesLimitsAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_liftedConeElement' (i : I) :
    dsimp% limit.π ((F ⋙ π A) ⋙ A) i (liftedConeElement' F) = (F.obj i).2 :=
  Types.Limit.π_mk _ _ _ _

variable [HasLimitsOfShape I C] [PreservesLimitsOfShape I A]

/-- (implementation) A system `(Fi, fi)_i` of elements induces an element in `A(lim_i Fi)`. -/
/-
**CategoryTheory.CategoryOfElements.CreatesLimitsAux.liftedConeElement** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.CategoryOfElements.CreatesLimitsAux`。
形式化陈述：liftedConeElement : A.obj (limit (F ⋙ π A))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) A system `(Fi, fi)_i` of elements induces an element in `A(lim_
i Fi)`.
-/
noncomputable def liftedConeElement : A.obj (limit (F ⋙ π A)) :=
  (preservesLimitIso A (F ⋙ π A)).inv (liftedConeElement' F)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.CategoryOfElements.CreatesLimitsAux.map_lift_mapCone** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.CategoryOfElements.CreatesLimitsAux`。
形式化陈述：map_lift_mapCone (c : Cone F) : dsimp% A.map (limit.lift (F ⋙ π A) ((π A).
mapCone c)) c.pt.snd = liftedConeElement F
参数：c : Cone F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.Types.limit_ext`：limit_ext (x y : limit F) (w : fo
rall j, limit.π F j x = limit.π F j y) : x = y
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.preservesLimitIso_hom_π`：preservesLimitIso_hom_π (j) : (p
reservesLimitIso G F).hom ≫ limit.π _ j = G.map (limit.π F j)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.lift_comp_preservesLimitIso_hom`：lift_comp_preservesLimit
Iso_hom (t : Cone F) : G.map (limit.lift _ t) ≫ (preservesLimitIso G F).hom = li
mit.lift (F ⋙ G) (G.mapCone _)
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `CategoryTheory.Limits.Types.Limit.π_mk`：∀ {J : Type v} [inst : CategoryT
heory.Category.{w, v} J] (F : CategoryTheory.Functor J (Type u))   [inst_1 : Cat
egoryTheory.Limits.HasLimit …
-/
lemma map_lift_mapCone (c : Cone F) :
    dsimp% A.map (limit.lift (F ⋙ π A) ((π A).mapCone c)) c.pt.snd = liftedConeElement F := by
  apply (preservesLimitIso A (F ⋙ π A)).toEquiv.injective
  ext i
  have h₁ := congr_hom (preservesLimitIso_hom_π A (F ⋙ π A) i)
    (A.map (limit.lift (F ⋙ π A) ((π A).mapCone c)) c.pt.snd)
  have h₂ := (c.π.app i).property
  simpa [-Functor.comp_obj, ← comp_apply, ← Functor.map_comp, liftedConeElement, liftedConeElement']

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.CategoryOfElements.CreatesLimitsAux.map_** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.CategoryOfElements.CreatesLimitsAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_π_liftedConeElement (i : I) :
    dsimp% A.map (limit.π (F ⋙ π A) i) (liftedConeElement F) = (F.obj i).snd := by
  have := congr_hom
    (preservesLimitIso_inv_π A (F ⋙ π A) i) (liftedConeElement' F)
  simp [liftedConeElement, ← comp_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-- (implementation) The constructed limit cone. -/
@[simps]
/-
**CategoryTheory.CategoryOfElements.CreatesLimitsAux.liftedCone** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.CategoryOfElements.CreatesLimitsAux`。
形式化陈述：liftedCone : Cone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) The constructed limit cone.
-/
noncomputable def liftedCone : Cone F where
  pt := ⟨_, liftedConeElement F⟩
  π :=
    { app := fun i => ⟨limit.π (F ⋙ π A) i, by simpa using! map_π_liftedConeElement _ _⟩
      naturality := fun i i' f => by ext; simpa using! (limit.w _ _).symm }

set_option backward.isDefEq.respectTransparency.types false in
/-- (implementation) The constructed limit cone is a lift of the limit cone in `C`. -/
/-
**CategoryTheory.CategoryOfElements.CreatesLimitsAux.isValidLift** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.CategoryOfElements.CreatesLimitsAux`。
形式化陈述：isValidLift : (π A).mapCone (liftedCone F) ≅ limit.cone (F ⋙ π A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) The constructed limit cone is a lift of the limit cone in `C`.
-/
noncomputable def isValidLift : (π A).mapCone (liftedCone F) ≅ limit.cone (F ⋙ π A) :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- (implementation) The constructed limit cone is a limit cone. -/
/-
**CategoryTheory.CategoryOfElements.CreatesLimitsAux.isLimit** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.CategoryOfElements.CreatesLimitsAux`。
形式化陈述：isLimit : IsLimit (liftedCone F) where lift s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) The constructed limit cone is a limit cone.
-/
noncomputable def isLimit : IsLimit (liftedCone F) where
  lift s := ⟨limit.lift (F ⋙ π A) ((π A).mapCone s), by simp⟩
  uniq s m h := ext _ _ _ <| limit.hom_ext
    fun i => by simpa using congrArg Subtype.val (h i)

end CreatesLimitsAux

variable [HasLimitsOfShape I C] [PreservesLimitsOfShape I A]

section

open CreatesLimitsAux

/-
**CategoryTheory.CategoryOfElements.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
ategoryOfElements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (F : I ⥤ A.Elements) : CreatesLimit F (π A) :=
  createsLimitOfReflectsIso' (limit.isLimit _) ⟨⟨liftedCone F, isValidLift F⟩, isLimit F⟩

end

/-
**CategoryTheory.CategoryOfElements.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
ategoryOfElements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CreatesLimitsOfShape I (π A) where
/-
**CategoryTheory.CategoryOfElements.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
ategoryOfElements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasLimitsOfShape I A.Elements :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (π A)

section Initial

/-
**CategoryTheory.CategoryOfElements.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
ategoryOfElements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : Cᵒᵖ ⥤ Type*} [F.IsRepresentable] : HasInitial F.Elements :=
  (Functor.Elements.isInitialOfRepresentableBy F.representableBy).hasInitial
/-
**CategoryTheory.CategoryOfElements.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
ategoryOfElements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : C ⥤ Type*} [F.IsCorepresentable] : HasInitial F.Elements :=
  (Functor.Elements.isInitialOfCorepresentableBy F.corepresentableBy).hasInitial

end Initial

end CategoryOfElements

namespace Functor.Elements

/-- An initial object in the category `F.Elements` of a covariant functor defines a
corepresentation for that functor. -/
/-
**CategoryTheory.Functor.Elements.corepresentableByOfIsInitial** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Functor.Elements`。
形式化陈述：corepresentableByOfIsInitial {F : C ⥤ Type w} {E : Elements F} (he : IsIni
tial E) : CorepresentableBy F E.fst where homEquiv
参数：he : IsInitial E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An initial object in the category `F.Elements` of a covariant functor defines a
corepresentation for that functor.
-/
def corepresentableByOfIsInitial {F : C ⥤ Type w} {E : Elements F} (he : IsInitial E) :
    CorepresentableBy F E.fst where
  homEquiv :=
    { toFun f := F.map f E.snd
      invFun y := (he.to ⟨_, y⟩).val
      left_inv f := Subtype.ext_iff.mp (he.hom_ext (he.to ⟨_, F.map f E.snd⟩) ⟨f, rfl⟩)
      right_inv y := (he.to ⟨_, y⟩).prop }
/-
**CategoryTheory.Functor.Elements.isCorepresentable_of_hasInitial** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Functor.Elements`。
形式化陈述：isCorepresentable_of_hasInitial (F : C ⥤ Type w) [HasInitial (Elements F)]
 : IsCorepresentable F where has_corepresentation
参数：F : C ⥤ Type w；Elements F。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isCorepresentable_of_hasInitial (F : C ⥤ Type w) [HasInitial (Elements F)] :
    IsCorepresentable F where
  has_corepresentation :=
    ⟨(⊥_ F.Elements).fst,
      (Nonempty.intro (corepresentableByOfIsInitial initialIsInitial))⟩
/-
**CategoryTheory.Functor.Elements.hasInitial_iff_isCorepresentable** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Functor.Elements`。
形式化陈述：hasInitial_iff_isCorepresentable (F : C ⥤ Type w) : HasInitial (Elements F
) ↔ IsCorepresentable F where mp _
参数：F : C ⥤ Type w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.Elements.isCorepresentable_of_hasInitial`：isCorep
resentable_of_hasInitial (F : C ⥤ Type w) [HasInitial (Elements F)] : IsCorepres
entable F where has_corepresentation
· 使用定理 `CategoryTheory.CategoryOfElements.instHasInitialElementsOfIsCorepresenta
ble`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheor
y.Functor C (Type u_1)}   [F.IsCorepresentable], CategoryTheory.L…
-/
theorem hasInitial_iff_isCorepresentable (F : C ⥤ Type w) :
    HasInitial (Elements F) ↔ IsCorepresentable F where
  mp _ := isCorepresentable_of_hasInitial F
  mpr _ := inferInstance

/-- An initial object in the category `F.Elements` of a contravariant functor defines a
representation for that functor. -/
/-
**CategoryTheory.Functor.Elements.representableByOfIsInitial** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Functor.Elements`。
形式化陈述：representableByOfIsInitial {F : Cᵒᵖ ⥤ Type w} {E : Elements F} (he : IsIni
tial E) : RepresentableBy F (E.fst.unop) where homEquiv
参数：he : IsInitial E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An initial object in the category `F.Elements` of a contravariant functor define
s a
representation for that functor.
-/
def representableByOfIsInitial {F : Cᵒᵖ ⥤ Type w} {E : Elements F} (he : IsInitial E) :
    RepresentableBy F (E.fst.unop) where
  homEquiv :=
    { toFun f := F.map f.op E.snd
      invFun y := (he.to ⟨_, y⟩).val.unop
      left_inv f := by
        have :=
          Subtype.ext_iff.mp (he.hom_ext (he.to ⟨_, F.map f.op E.snd⟩) ⟨f.op, rfl⟩)
        simp only [this, Quiver.Hom.unop_op]
      right_inv y := (he.to ⟨_, y⟩).prop }
/-
**CategoryTheory.Functor.Elements.isRepresentable_of_hasInitial** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Functor.Elements`。
形式化陈述：isRepresentable_of_hasInitial (F : Cᵒᵖ ⥤ Type w) [HasInitial (Elements F)]
 : IsRepresentable F where has_representation
参数：F : Cᵒᵖ ⥤ Type w；Elements F。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isRepresentable_of_hasInitial (F : Cᵒᵖ ⥤ Type w) [HasInitial (Elements F)] :
    IsRepresentable F where
  has_representation :=
    ⟨(⊥_ F.Elements).fst.unop,
      (Nonempty.intro (representableByOfIsInitial initialIsInitial))⟩
/-
**CategoryTheory.Functor.Elements.hasInitial_iff_isRepresentable** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Functor.Elements`。
形式化陈述：hasInitial_iff_isRepresentable (F : Cᵒᵖ ⥤ Type w) : HasInitial (Elements F
) ↔ IsRepresentable F where mp _
参数：F : Cᵒᵖ ⥤ Type w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.Elements.isRepresentable_of_hasInitial`：isReprese
ntable_of_hasInitial (F : Cᵒᵖ ⥤ Type w) [HasInitial (Elements F)] : IsRepresenta
ble F where has_representation
· 使用定理 `CategoryTheory.CategoryOfElements.instHasInitialElementsOppositeOfIsRepr
esentable`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F : Categor
yTheory.Functor Cᵒᵖ (Type u_1)}   [F.IsRepresentable], CategoryTheory.L…
-/
theorem hasInitial_iff_isRepresentable (F : Cᵒᵖ ⥤ Type w) :
    HasInitial (Elements F) ↔ IsRepresentable F where
  mp _ := isRepresentable_of_hasInitial F
  mpr _ := inferInstance

end Functor.Elements

end CategoryTheory

