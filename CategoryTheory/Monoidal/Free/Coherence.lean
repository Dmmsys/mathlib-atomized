/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Monoidal.Free.Basic

/-!
# The monoidal coherence theorem

In this file, we prove the monoidal coherence theorem, stated in the following form: the free
monoidal category over any type `C` is thin.

We follow a proof described by Ilya Beylin and Peter Dybjer, which has been previously formalized
in the proof assistant ALF. The idea is to declare a normal form (with regard to association and
adding units) on objects of the free monoidal category and consider the discrete subcategory of
objects that are in normal form. A normalization procedure is then just a functor
`fullNormalize : FreeMonoidalCategory C ⥤ Discrete (NormalMonoidalObject C)`, where
functoriality says that two objects which are related by associators and unitors have the
same normal form. Another desirable property of a normalization procedure is that an object is
isomorphic (i.e., related via associators and unitors) to its normal form. In the case of the
specific normalization procedure we use we not only get these isomorphisms, but also that they
assemble into a natural isomorphism `𝟭 (FreeMonoidalCategory C) ≅ fullNormalize ⋙ inclusion`.
But this means that any two parallel morphisms in the free monoidal category factor through a
discrete category in the same way, so they must be equal, and hence the free monoidal category
is thin.

## References

* [Ilya Beylin and Peter Dybjer, Extracting a proof of coherence for monoidal categories from a
  proof of normalization for monoids][beylin1996]

-/

@[expose] public section


universe u

namespace CategoryTheory

open MonoidalCategory CategoryTheory.Functor

namespace FreeMonoidalCategory

variable {C : Type u}

section

variable (C)

/-- We say an object in the free monoidal category is in normal form if it is of the form
`(((𝟙_ C) ⊗ X₁) ⊗ X₂) ⊗ ⋯`. -/
/-
**CategoryTheory.FreeMonoidalCategory.NormalMonoidalObject** 是 Mathlib 中的一个归纳类型，
位于命名空间 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say an object in the free monoidal category is in normal form if it is of the
 form
`(((𝟙_ C) ⊗ X₁) ⊗ X₂) ⊗ ⋯`.
-/
inductive NormalMonoidalObject : Type u
  | unit : NormalMonoidalObject
  | tensor : NormalMonoidalObject → C → NormalMonoidalObject

end

local notation "F" => FreeMonoidalCategory

local notation "N" => Discrete ∘ NormalMonoidalObject

local infixr:10 " ⟶ᵐ " => Hom

/-
**CategoryTheory.FreeMonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.FreeMonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x y : N C) : Subsingleton (x ⟶ y) := Discrete.instSubsingletonDiscreteHom _ _

/-- Auxiliary definition for `inclusion`. -/
@[simp]
/-
**CategoryTheory.FreeMonoidalCategory.inclusionObj** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.FreeMonoidalCategory`。
形式化陈述：{C : Type u} → CategoryTheory.FreeMonoidalCategory.NormalMonoidalObject C 
→ CategoryTheory.FreeMonoidalCategory C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `inclusion`.
-/
def inclusionObj : NormalMonoidalObject C → F C
  | NormalMonoidalObject.unit => unit
  | NormalMonoidalObject.tensor n a => tensor (inclusionObj n) (of a)

/-- The discrete subcategory of objects in normal form includes into the free monoidal category. -/
/-
**CategoryTheory.FreeMonoidalCategory.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.FreeMonoidalCategory`。
形式化陈述：inclusion : N C ⥤ F C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete subcategory of objects in normal form includes into the free monoid
al category.
-/
def inclusion : N C ⥤ F C :=
  Discrete.functor inclusionObj

@[simp]
/-
**CategoryTheory.FreeMonoidalCategory.inclusion_obj** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.FreeMonoidalCategory`。
形式化陈述：inclusion_obj (X : N C) : inclusion.obj X = inclusionObj X.as
参数：X : N C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_obj (X : N C) :
    inclusion.obj X = inclusionObj X.as :=
  rfl

@[simp]
/-
**CategoryTheory.FreeMonoidalCategory.inclusion_map** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.FreeMonoidalCategory`。
形式化陈述：inclusion_map {X Y : N C} (f : X ⟶ Y) : inclusion.map f = eqToHom (congr_a
rg _ (Discrete.ext (Discrete.eq_of_hom f)))
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_map {X Y : N C} (f : X ⟶ Y) :
    inclusion.map f = eqToHom (congr_arg _ (Discrete.ext (Discrete.eq_of_hom f))) := rfl

/-- Auxiliary definition for `normalize`. -/
/-
**CategoryTheory.FreeMonoidalCategory.normalizeObj** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.FreeMonoidalCategory`。
形式化陈述：{C : Type u} →   CategoryTheory.FreeMonoidalCategory C →     CategoryTheor
y.FreeMonoidalCategory.NormalMonoidalObject C →       CategoryTheory.FreeMonoida
lCategory.NormalMonoidalObject C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `normalize`.
-/
def normalizeObj : F C → NormalMonoidalObject C → NormalMonoidalObject C
  | unit, n => n
  | of X, n => NormalMonoidalObject.tensor n X
  | tensor X Y, n => normalizeObj Y (normalizeObj X n)

@[simp]
/-
**CategoryTheory.FreeMonoidalCategory.normalizeObj_unitor** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：normalizeObj_unitor (n : NormalMonoidalObject C) : normalizeObj (𝟙_ (F C))
 n = n
参数：n : NormalMonoidalObject C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normalizeObj_unitor (n : NormalMonoidalObject C) : normalizeObj (𝟙_ (F C)) n = n :=
  rfl

@[simp]
/-
**CategoryTheory.FreeMonoidalCategory.normalizeObj_tensor** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：normalizeObj_tensor (X Y : F C) (n : NormalMonoidalObject C) : normalizeOb
j (X otimes Y) n = normalizeObj Y (normalizeObj X n)
参数：X Y : F C；n : NormalMonoidalObject C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normalizeObj_tensor (X Y : F C) (n : NormalMonoidalObject C) :
    normalizeObj (X ⊗ Y) n = normalizeObj Y (normalizeObj X n) :=
  rfl

/-- Auxiliary definition for `normalize`. -/
/-
**CategoryTheory.FreeMonoidalCategory.normalizeObj'** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.FreeMonoidalCategory`。
形式化陈述：normalizeObj' (X : F C) : N C ⥤ N C
参数：X : F C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `normalize`.
-/
def normalizeObj' (X : F C) : N C ⥤ N C := Discrete.functor fun n ↦ ⟨normalizeObj X n⟩

@[simp]
/-
**CategoryTheory.FreeMonoidalCategory.as_obj_normalizeObj'** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：as_obj_normalizeObj' (X : F C) (n : N C) : ((normalizeObj' X).obj n).as = 
normalizeObj X n.as
参数：X : F C；n : N C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem as_obj_normalizeObj' (X : F C) (n : N C) :
    ((normalizeObj' X).obj n).as = normalizeObj X n.as := rfl

section

open Hom

/-- Auxiliary definition for `normalize`. Here we prove that objects that are related by
associators and unitors map to the same normal form. -/
@[simp]
/-
**CategoryTheory.FreeMonoidalCategory.normalizeMapAux** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.FreeMonoidalCategory`。
形式化陈述：{C : Type u} → {X Y : CategoryTheory.FreeMonoidalCategory C} → X.Hom Y → (
X.normalizeObj' ⟶ Y.normalizeObj')
参数：X.normalizeObj' ⟶ Y.normalizeObj'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `normalize`. Here we prove that objects that are relate
d by
associators and unitors map to the same normal form.
-/
def normalizeMapAux : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (normalizeObj' X ⟶ normalizeObj' Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, α_hom X Y Z => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, α_inv _ _ _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, l_hom _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, l_inv _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, ρ_hom _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, ρ_inv _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, (@Hom.comp _ _ _ _ f g) => normalizeMapAux f ≫ normalizeMapAux g
  | _, _, (@Hom.tensor _ T _ _ W f g) =>
    Discrete.natTrans <| fun ⟨X⟩ => (normalizeMapAux g).app ⟨normalizeObj T X⟩ ≫
      (normalizeObj' W).map ((normalizeMapAux f).app ⟨X⟩)
  | _, _, (@Hom.whiskerLeft _ T _ W f) =>
    Discrete.natTrans <| fun ⟨X⟩ => (normalizeMapAux f).app ⟨normalizeObj T X⟩
  | _, _, (@Hom.whiskerRight _ T _ f W) =>
    Discrete.natTrans <| fun X => (normalizeObj' W).map <| (normalizeMapAux f).app X

end

section

variable (C)

set_option backward.isDefEq.respectTransparency false in
/-- Our normalization procedure works by first defining a functor `F C ⥤ (N C ⥤ N C)` (which turns
out to be very easy), and then obtain a functor `F C ⥤ N C` by plugging in the normal object
`𝟙_ C`. -/
@[simp]
/-
**CategoryTheory.FreeMonoidalCategory.normalize** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.FreeMonoidalCategory`。
形式化陈述：normalize : F C ⥤ N C ⥤ N C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Our normalization procedure works by first defining a functor `F C ⥤ (N C ⥤ N C)
` (which turns
out to be very easy), and then obtain a functor `F C ⥤ N C` by plugging in the n
ormal object
`𝟙_ C`.
-/
def normalize : F C ⥤ N C ⥤ N C where
  obj X := normalizeObj' X
  map {X Y} := Quotient.lift normalizeMapAux (by cat_disch)

/-- A variant of the normalization functor where we consider the result as an object in the free
monoidal category (rather than an object of the discrete subcategory of objects in normal form). -/
@[simp]
/-
**CategoryTheory.FreeMonoidalCategory.normalize'** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.FreeMonoidalCategory`。
形式化陈述：normalize' : F C ⥤ N C ⥤ F C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of the normalization functor where we consider the result as an object
 in the free
monoidal category (rather than an object of the discrete subcategory of objects 
in normal form).
-/
def normalize' : F C ⥤ N C ⥤ F C :=
  normalize C ⋙ (whiskeringRight _ _ _).obj inclusion

/-- The normalization functor for the free monoidal category over `C`. -/
/-
**CategoryTheory.FreeMonoidalCategory.fullNormalize** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.FreeMonoidalCategory`。
形式化陈述：fullNormalize : F C ⥤ N C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normalization functor for the free monoidal category over `C`.
-/
def fullNormalize : F C ⥤ N C where
  obj X := ((normalize C).obj X).obj ⟨NormalMonoidalObject.unit⟩
  map f := ((normalize C).map f).app ⟨NormalMonoidalObject.unit⟩

/-- Given an object `X` of the free monoidal category and an object `n` in normal form, taking
the tensor product `n ⊗ X` in the free monoidal category is functorial in both `X` and `n`. -/
@[simp]
/-
**CategoryTheory.FreeMonoidalCategory.tensorFunc** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.FreeMonoidalCategory`。
形式化陈述：tensorFunc : F C ⥤ N C ⥤ F C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an object `X` of the free monoidal category and an object `n` in normal fo
rm, taking
the tensor product `n ⊗ X` in the free monoidal category is functorial in both `
X` and `n`.
-/
def tensorFunc : F C ⥤ N C ⥤ F C where
  obj X := Discrete.functor fun n => inclusion.obj ⟨n⟩ ⊗ X
  map f := Discrete.natTrans (fun _ => _ ◁ f)
/-
**CategoryTheory.FreeMonoidalCategory.tensorFunc_map_app** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：tensorFunc_map_app {X Y : F C} (f : X ⟶ Y) (n) : ((tensorFunc C).map f).ap
p n = _ ◁ f
参数：f : X ⟶ Y；n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorFunc_map_app {X Y : F C} (f : X ⟶ Y) (n) : ((tensorFunc C).map f).app n = _ ◁ f :=
  rfl
/-
**CategoryTheory.FreeMonoidalCategory.tensorFunc_obj_map** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：tensorFunc_obj_map (Z : F C) {n n' : N C} (f : n ⟶ n') : ((tensorFunc C).o
bj Z).map f = inclusion.map f ▷ Z
参数：Z : F C；f : n ⟶ n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem tensorFunc_obj_map (Z : F C) {n n' : N C} (f : n ⟶ n') :
    ((tensorFunc C).obj Z).map f = inclusion.map f ▷ Z := by
  cases n
  cases n'
  rcases f with ⟨⟨h⟩⟩
  dsimp at h
  subst h
  simp

/-- Auxiliary definition for `normalizeIso`. Here we construct the isomorphism between
`n ⊗ X` and `normalize X n`. -/
@[simp]
/-
**CategoryTheory.FreeMonoidalCategory.normalizeIsoApp** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.FreeMonoidalCategory`。
形式化陈述：(C : Type u) →   (X : CategoryTheory.FreeMonoidalCategory C) →     (n : (C
ategoryTheory.Discrete ∘ CategoryTheory.FreeMonoidalCategory.NormalMonoidalObjec
t) C) →       ((CategoryTheory.FreeMonoidalCategory.tensorFunc C).obj X).obj n ≅
         ((CategoryTheory.FreeMonoidalCategory.normalize' C).obj X).obj n
参数：CategoryTheory.Discrete ∘ CategoryTheory.FreeMonoidalCategory.NormalMonoidalO
bject；CategoryTheory.FreeMonoidalCategory.tensorFunc C；CategoryTheory.FreeMonoid
alCategory.normalize' C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `normalizeIso`. Here we construct the isomorphism betwe
en
`n ⊗ X` and `normalize X n`.
-/
def normalizeIsoApp :
    ∀ (X : F C) (n : N C), ((tensorFunc C).obj X).obj n ≅ ((normalize' C).obj X).obj n
  | of _, _ => Iso.refl _
  | unit, _ => ρ_ _
  | tensor X a, n =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp X n) a ≪≫ normalizeIsoApp _ _

/-- Almost non-definitionally equal to `normalizeIsoApp`, but has a better definitional property
in the proof of `normalize_naturality`. -/
/-
**CategoryTheory.FreeMonoidalCategory.normalizeIsoApp'** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：(C : Type u) →   (X : CategoryTheory.FreeMonoidalCategory C) →     (n : Ca
tegoryTheory.FreeMonoidalCategory.NormalMonoidalObject C) →       CategoryTheory
.MonoidalCategoryStruct.tensorObj (CategoryTheory.FreeMonoidalCategory.inclusion
Obj n) X ≅         CategoryTheory.FreeMonoidalCategory.inclusionObj (X.normalize
Obj n)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Almost non-definitionally equal to `normalizeIsoApp`, but has a better definitio
nal property
in the proof of `normalize_naturality`.
-/
def normalizeIsoApp' :
    ∀ (X : F C) (n : NormalMonoidalObject C), inclusionObj n ⊗ X ≅ inclusionObj (normalizeObj X n)
  | of _, _ => Iso.refl _
  | unit, _ => ρ_ _
  | tensor X Y, n =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp' X n) Y ≪≫ normalizeIsoApp' _ _
/-
**CategoryTheory.FreeMonoidalCategory.normalizeIsoApp'_tensor** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：∀ (C : Type u) (X Y : CategoryTheory.FreeMonoidalCategory C)   (n : Catego
ryTheory.FreeMonoidalCategory.NormalMonoidalObject C),   CategoryTheory.FreeMono
idalCategory.normalizeIsoApp' C (CategoryTheory.MonoidalCategoryStruct.tensorObj
 X Y) n =     (CategoryTheory.MonoidalCategoryStruct.associator (CategoryTheory.
FreeMonoidalCategory.inclusionObj n) X Y).symm ≪≫       CategoryTheory.MonoidalC
ategory.whiskerRightIso (CategoryTheory.FreeMonoidalCategory.normalizeIsoApp' C 
X n) Y ≪≫         CategoryTheory.FreeMonoidalCategory.normalizeIsoApp' C Y (X.no
rmalizeObj n)
参数：C : Type u；X Y : CategoryTheory.FreeMonoidalCategory C；n : CategoryTheory.Fre
eMonoidalCategory.NormalMonoidalObject C；CategoryTheory.MonoidalCategoryStruct.t
ensorObj X Y；CategoryTheory.MonoidalCategoryStruct.associator (CategoryTheory.Fr
eeMonoidalCategory.inclusionObj n) X Y；CategoryTheory.FreeMonoidalCategory.norma
lizeIsoApp' C X n；X.normalizeObj n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem normalizeIsoApp'_tensor (X Y : F C) (n : NormalMonoidalObject C) :
    normalizeIsoApp' C (X ⊗ Y) n =
      (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp' C X n) Y ≪≫
        normalizeIsoApp' C Y _ := rfl
/-
**CategoryTheory.FreeMonoidalCategory.normalizeIsoApp'_unit** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：∀ (C : Type u) (n : CategoryTheory.FreeMonoidalCategory.NormalMonoidalObje
ct C),   CategoryTheory.FreeMonoidalCategory.normalizeIsoApp' C       (CategoryT
heory.MonoidalCategoryStruct.tensorUnit (CategoryTheory.FreeMonoidalCategory C))
 n =     CategoryTheory.MonoidalCategoryStruct.rightUnitor (CategoryTheory.FreeM
onoidalCategory.inclusionObj n)
参数：C : Type u；n : CategoryTheory.FreeMonoidalCategory.NormalMonoidalObject C；Cat
egoryTheory.MonoidalCategoryStruct.tensorUnit (CategoryTheory.FreeMonoidalCatego
ry C)；CategoryTheory.FreeMonoidalCategory.inclusionObj n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem normalizeIsoApp'_unit (n : NormalMonoidalObject C) :
    normalizeIsoApp' C (𝟙_ (F C)) n = ρ_ _ := rfl

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.FreeMonoidalCategory.normalizeIsoApp_eq** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：∀ (C : Type u) (X : CategoryTheory.FreeMonoidalCategory C)   (n : (Categor
yTheory.Discrete ∘ CategoryTheory.FreeMonoidalCategory.NormalMonoidalObject) C),
   CategoryTheory.FreeMonoidalCategory.normalizeIsoApp C X n =     CategoryTheor
y.FreeMonoidalCategory.normalizeIsoApp' C X n.as
参数：C : Type u；X : CategoryTheory.FreeMonoidalCategory C；n : (CategoryTheory.Disc
rete ∘ CategoryTheory.FreeMonoidalCategory.NormalMonoidalObject) C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normalizeIsoApp_eq :
    ∀ (X : F C) (n : N C), normalizeIsoApp C X n = normalizeIsoApp' C X n.as
  | of _, _ => rfl
  | unit, _ => rfl
  | tensor X Y, n => by
      rw [normalizeIsoApp, normalizeIsoApp']
      rw [normalizeIsoApp_eq X n]
      rw [normalizeIsoApp_eq Y ⟨normalizeObj X n.as⟩]
      simp

@[simp]
/-
**CategoryTheory.FreeMonoidalCategory.normalizeIsoApp_tensor** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：normalizeIsoApp_tensor (X Y : F C) (n : N C) : normalizeIsoApp C (X otimes
 Y) n = (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp C X n) Y ≪≫ normaliz
eIsoApp _ _ _
参数：X Y : F C；n : N C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normalizeIsoApp_tensor (X Y : F C) (n : N C) :
    normalizeIsoApp C (X ⊗ Y) n =
      (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp C X n) Y ≪≫ normalizeIsoApp _ _ _ :=
  rfl

@[simp]
/-
**CategoryTheory.FreeMonoidalCategory.normalizeIsoApp_unitor** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：normalizeIsoApp_unitor (n : N C) : normalizeIsoApp C (𝟙_ (F C)) n = ρ_ _
参数：n : N C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normalizeIsoApp_unitor (n : N C) : normalizeIsoApp C (𝟙_ (F C)) n = ρ_ _ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `normalizeIso`. -/
@[simps!]
/-
**CategoryTheory.FreeMonoidalCategory.normalizeIsoAux** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.FreeMonoidalCategory`。
形式化陈述：normalizeIsoAux (X : F C) : (tensorFunc C).obj X ≅ (normalize' C).obj X
参数：X : F C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `normalizeIso`.
-/
def normalizeIsoAux (X : F C) : (tensorFunc C).obj X ≅ (normalize' C).obj X :=
  NatIso.ofComponents (normalizeIsoApp C X)
    (by
      rintro ⟨X⟩ ⟨Y⟩ ⟨⟨f⟩⟩
      dsimp at f
      subst f
      dsimp
      simp)


section

variable {C}

/-
**CategoryTheory.FreeMonoidalCategory.normalizeObj_congr** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：normalizeObj_congr (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y) : 
normalizeObj X n = normalizeObj Y n
参数：n : NormalMonoidalObject C；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normalizeObj_congr (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y) :
    normalizeObj X n = normalizeObj Y n := by
  rcases f with ⟨f'⟩
  apply @congr_fun _ _ fun n => normalizeObj X n
  clear n f
  induction f' with
  | comp _ _ _ _ => apply Eq.trans <;> assumption
  | whiskerLeft _ _ ih => funext; apply congr_fun ih
  | whiskerRight _ _ ih => funext; apply congr_arg₂ _ rfl (congr_fun ih _)
  | @tensor W X Y Z _ _ ih₁ ih₂ =>
      funext n
      simp [congr_fun ih₁ n, congr_fun ih₂ (normalizeObj Y n)]
  | _ => funext; rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.FreeMonoidalCategory.normalize_naturality** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：normalize_naturality (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y) 
: inclusionObj n ◁ f ≫ (normalizeIsoApp' C Y n).hom = (normalizeIsoApp' C X n).h
om ≫ inclusion.map (eqToHom (Discrete.ext (normalizeObj_congr n f)))
参数：n : NormalMonoidalObject C；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FreeMonoidalCategory.Hom.inductionOn`：∀ {C : Type u} {mot
ive : {X Y : CategoryTheory.FreeMonoidalCategory C} → (X ⟶ Y) → Prop}   {X Y : C
ategoryTheory.FreeMonoidalCategory C} (t …
· 使用定理 `CategoryTheory.Discrete.ext`：∀ {α : Type u₁} {x y : CategoryTheory.Discr
ete α}, x.as = y.as → x = y
· 使用定理 `CategoryTheory.FreeMonoidalCategory.normalizeObj_congr`：normalizeObj_con
gr (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y) : normalizeObj X n = nor
malizeObj Y n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_hom_inv_inv_inv_inv_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mo
noidalCategory C] {W X Y Z Z_1 : C}   (h :     CategoryT…
· 使用引理 `CategoryTheory.MonoidalCategory.whiskerRightIso_trans`：whiskerRightIso_t
rans {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) (W : C) : whiskerRightIso (f ≪≫ g) W = 
whiskerRightIso f W ≪≫ whiskerRightIso g W
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv_assoc`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C
] {W X Y Z Z_1 : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.MonoidalCategory.triangle_assoc_comp_right_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Monoi
dalCategory C] (X Y : C) {Z : C}   (h : CategoryTheor…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_inv_hom_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCat
egory C] (X : C) {Y Z : C}   (f : Y ≅ Z) {Z_1 :…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor`：whiskerLeft_rig
htUnitor (X Y : C) : X ◁ (ρ_ Y).hom = (α_ X Y (𝟙_ C)).inv ≫ (ρ_ (X otimes Y)).ho
m
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor_inv`：whiskerLeft
_rightUnitor_inv (X Y : C) : X ◁ (ρ_ Y).inv = (ρ_ (X otimes Y)).inv ≫ (α_ X Y (𝟙
_ C)).hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
（共 43 条，此处仅展示前 30 条）
-/
theorem normalize_naturality (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y) :
    inclusionObj n ◁ f ≫ (normalizeIsoApp' C Y n).hom =
      (normalizeIsoApp' C X n).hom ≫
        inclusion.map (eqToHom (Discrete.ext (normalizeObj_congr n f))) := by
  revert n
  induction f using Hom.inductionOn
  case comp f g ihf ihg => simp [ihg, reassoc_of% (ihf _)]
  case whiskerLeft X' X Y f ih =>
    intro n
    dsimp only [normalizeObj_tensor, normalizeIsoApp'_tensor, Iso.trans_hom,
      Iso.symm_hom, whiskerRightIso_hom, Function.comp_apply, inclusion_obj]
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ih]
    simp
  case whiskerRight X Y h η' ih =>
    intro n
    dsimp only [normalizeObj_tensor, normalizeIsoApp'_tensor, Iso.trans_hom,
      Iso.symm_hom, whiskerRightIso_hom, Function.comp_apply, inclusion_obj]
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, ih]
    have := dcongr_arg (fun x => (normalizeIsoApp' C η' x).hom) (normalizeObj_congr n h)
    simp [this]
  all_goals simp

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism between `n ⊗ X` and `normalize X n` is natural (in both `X` and `n`, but
naturality in `n` is trivial and was "proved" in `normalizeIsoAux`). This is the real heart
of our proof of the coherence theorem. -/
/-
**CategoryTheory.FreeMonoidalCategory.normalizeIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.FreeMonoidalCategory`。
形式化陈述：normalizeIso : tensorFunc C ≅ normalize' C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `n ⊗ X` and `normalize X n` is natural (in both `X` and 
`n`, but
naturality in `n` is trivial and was "proved" in `normalizeIsoAux`). This is the
 real heart
of our proof of the coherence theorem.
-/
def normalizeIso : tensorFunc C ≅ normalize' C :=
  NatIso.ofComponents (normalizeIsoAux C) <| by
    intro X Y f
    ext ⟨n⟩
    convert! normalize_naturality n f using 1
    any_goals dsimp; rw [normalizeIsoApp_eq]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism between an object and its normal form is natural. -/
/-
**CategoryTheory.FreeMonoidalCategory.fullNormalizeIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：fullNormalizeIso : 𝟭 (F C) ≅ fullNormalize C ⋙ inclusion
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between an object and its normal form is natural.
-/
def fullNormalizeIso : 𝟭 (F C) ≅ fullNormalize C ⋙ inclusion :=
  NatIso.ofComponents
  (fun X => (λ_ X).symm ≪≫ ((normalizeIso C).app X).app ⟨NormalMonoidalObject.unit⟩)
    (by
      intro X Y f
      dsimp
      rw [leftUnitor_inv_naturality_assoc, Category.assoc, Iso.cancel_iso_inv_left]
      exact
        congr_arg (fun f => NatTrans.app f (Discrete.mk NormalMonoidalObject.unit))
          ((normalizeIso.{u} C).hom.naturality f))

end

/-- The monoidal coherence theorem. -/
/-
**CategoryTheory.FreeMonoidalCategory.subsingleton_hom** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.FreeMonoidalCategory`。
形式化陈述：subsingleton_hom : Quiver.IsThin (F C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.FreeMonoidalCategory.instSubsingletonHomCompDiscreteNorma
lMonoidalObject`：∀ {C : Type u} (x y : (CategoryTheory.Discrete ∘ CategoryTheory
.FreeMonoidalCategory.NormalMonoidalObject) C),   Subsingleton (x ⟶ y)
· 使用定理 `CategoryTheory.NatIso.naturality_2`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The monoidal coherence theorem.
-/
instance subsingleton_hom : Quiver.IsThin (F C) := fun X Y =>
  ⟨fun f g => by
    have hfg : (fullNormalize C).map f = (fullNormalize C).map g := Subsingleton.elim _ _
    have hf := NatIso.naturality_2 (fullNormalizeIso.{u} C) f
    have hg := NatIso.naturality_2 (fullNormalizeIso.{u} C) g
    exact hf.symm.trans (Eq.trans (by simp only [Functor.comp_map, hfg]) hg)⟩

section Groupoid

section

open Hom

/-- Auxiliary construction for showing that the free monoidal category is a groupoid. Do not use
this, use `IsIso.inv` instead. -/
/-
**CategoryTheory.FreeMonoidalCategory.inverseAux** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.FreeMonoidalCategory`。
形式化陈述：{C : Type u} → {X Y : CategoryTheory.FreeMonoidalCategory C} → X.Hom Y → Y
.Hom X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction for showing that the free monoidal category is a groupoid
. Do not use
this, use `IsIso.inv` instead.
-/
def inverseAux : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (Y ⟶ᵐ X)
  | _, _, Hom.id X => id X
  | _, _, α_hom _ _ _ => α_inv _ _ _
  | _, _, α_inv _ _ _ => α_hom _ _ _
  | _, _, ρ_hom _ => ρ_inv _
  | _, _, ρ_inv _ => ρ_hom _
  | _, _, l_hom _ => l_inv _
  | _, _, l_inv _ => l_hom _
  | _, _, Hom.comp f g => (inverseAux g).comp (inverseAux f)
  | _, _, Hom.whiskerLeft X f => (inverseAux f).whiskerLeft X
  | _, _, Hom.whiskerRight f X => (inverseAux f).whiskerRight X
  | _, _, Hom.tensor f g => (inverseAux f).tensor (inverseAux g)

end

/-
**CategoryTheory.FreeMonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.FreeMonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Groupoid.{u} (F C) :=
  { (inferInstance : Category (F C)) with
    inv := Quotient.lift (fun f => ⟦inverseAux f⟧) (by cat_disch) }

end Groupoid

end FreeMonoidalCategory

end CategoryTheory

