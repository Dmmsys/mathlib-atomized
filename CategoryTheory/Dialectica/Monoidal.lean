/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Dialectica.Basic

/-!
# The Dialectica category is symmetric monoidal

We show that the category `Dial` has a symmetric monoidal category structure.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory

open MonoidalCategory Limits

universe v u
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasPullbacks C]

namespace Dial

local notation "π₁" => prod.fst
local notation "π₂" => prod.snd
local notation "π(" a ", " b ")" => prod.lift a b

/-- The object `X ⊗ Y` in the `Dial C` category just tuples the left and right components. -/
/-
**CategoryTheory.Dial.tensorObjImpl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Di
al`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasFiniteProducts C] →       [CategoryTheory.Limits.HasPu
llbacks C] → CategoryTheory.Dial C → CategoryTheory.Dial C → CategoryTheory.Dial
 C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object `X ⊗ Y` in the `Dial C` category just tuples the left and right compo
nents.
-/
@[simps] def tensorObjImpl (X Y : Dial C) : Dial C where
  src := X.src ⨯ Y.src
  tgt := X.tgt ⨯ Y.tgt
  rel :=
    (Subobject.pullback (prod.map π₁ π₁)).obj X.rel ⊓
    (Subobject.pullback (prod.map π₂ π₂)).obj Y.rel

set_option backward.isDefEq.respectTransparency false in
/-- The functorial action of `X ⊗ Y` in `Dial C`. -/
/-
**CategoryTheory.Dial.tensorHomImpl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Di
al`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasFiniteProducts C] →       [inst_2 : CategoryTheory.Lim
its.HasPullbacks C] →         {X₁ X₂ Y₁ Y₂ : CategoryTheory.Dial C} → (X₁ ⟶ X₂) 
→ (Y₁ ⟶ Y₂) → (X₁.tensorObjImpl Y₁ ⟶ X₂.tensorObjImpl Y₂)
参数：X₁ ⟶ X₂；Y₁ ⟶ Y₂；X₁.tensorObjImpl Y₁ ⟶ X₂.tensorObjImpl Y₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functorial action of `X ⊗ Y` in `Dial C`.
-/
@[simps] def tensorHomImpl {X₁ X₂ Y₁ Y₂ : Dial C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    tensorObjImpl X₁ Y₁ ⟶ tensorObjImpl X₂ Y₂ where
  f := prod.map f.f g.f
  F := π(prod.map π₁ π₁ ≫ f.F, prod.map π₂ π₂ ≫ g.F)
  le := by
    simp only [tensorObjImpl, Subobject.inf_pullback]
    apply inf_le_inf <;> rw [← Subobject.pullback_comp, ← Subobject.pullback_comp]
    · have := (Subobject.pullback (prod.map π₁ π₁ :
        (X₁.src ⨯ Y₁.src) ⨯ X₂.tgt ⨯ Y₂.tgt ⟶ _)).monotone (Hom.le f)
      rw [← Subobject.pullback_comp, ← Subobject.pullback_comp] at this
      convert! this using 3 <;> simp
    · have := (Subobject.pullback (prod.map π₂ π₂ :
        (X₁.src ⨯ Y₁.src) ⨯ X₂.tgt ⨯ Y₂.tgt ⟶ _)).monotone (Hom.le g)
      rw [← Subobject.pullback_comp, ← Subobject.pullback_comp] at this
      convert! this using 3 <;> simp

/-- The unit for the tensor `X ⊗ Y` in `Dial C`. -/
/-
**CategoryTheory.Dial.tensorUnitImpl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.D
ial`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasFiniteProducts C] → CategoryTheory.Dial C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit for the tensor `X ⊗ Y` in `Dial C`.
-/
@[simps] def tensorUnitImpl : Dial C := { src := ⊤_ _, tgt := ⊤_ _, rel := ⊤ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Left unit cancellation `1 ⊗ X ≅ X` in `Dial C`. -/
/-
**CategoryTheory.Dial.leftUnitorImpl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.D
ial`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasFiniteProducts C] →       [inst_2 : CategoryTheory.Lim
its.HasPullbacks C] →         (X : CategoryTheory.Dial C) → CategoryTheory.Dial.
tensorUnitImpl.tensorObjImpl X ≅ X
参数：X : CategoryTheory.Dial C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left unit cancellation `1 ⊗ X ≅ X` in `Dial C`.
-/
@[simps!] def leftUnitorImpl (X : Dial C) : tensorObjImpl tensorUnitImpl X ≅ X :=
  isoMk (Limits.prod.leftUnitor _) (Limits.prod.leftUnitor _) <| by simp [Subobject.pullback_top]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Right unit cancellation `X ⊗ 1 ≅ X` in `Dial C`. -/
/-
**CategoryTheory.Dial.rightUnitorImpl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Dial`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasFiniteProducts C] →       [inst_2 : CategoryTheory.Lim
its.HasPullbacks C] →         (X : CategoryTheory.Dial C) → X.tensorObjImpl Cate
goryTheory.Dial.tensorUnitImpl ≅ X
参数：X : CategoryTheory.Dial C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right unit cancellation `X ⊗ 1 ≅ X` in `Dial C`.
-/
@[simps!] def rightUnitorImpl (X : Dial C) : tensorObjImpl X tensorUnitImpl ≅ X :=
  isoMk (Limits.prod.rightUnitor _) (Limits.prod.rightUnitor _) <| by simp [Subobject.pullback_top]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The associator for tensor, `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)` in `Dial C`. -/
@[simps!]
/-
**CategoryTheory.Dial.associatorImpl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.D
ial`。
形式化陈述：associatorImpl (X Y Z : Dial C) : tensorObjImpl (tensorObjImpl X Y) Z ≅ te
nsorObjImpl X (tensorObjImpl Y Z)
参数：X Y Z : Dial C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator for tensor, `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)` in `Dial C`.
-/
def associatorImpl (X Y Z : Dial C) :
    tensorObjImpl (tensorObjImpl X Y) Z ≅ tensorObjImpl X (tensorObjImpl Y Z) :=
  isoMk (prod.associator ..) (prod.associator ..) <| by
    simp [Subobject.inf_pullback, ← Subobject.pullback_comp, inf_assoc]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[simps!]
/-
**CategoryTheory.Dial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Dial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
instance : MonoidalCategoryStruct (Dial C) where
  tensorUnit := tensorUnitImpl
  tensorObj := tensorObjImpl
  whiskerLeft X _ _ f := tensorHomImpl (𝟙 X) f
  whiskerRight f Y := tensorHomImpl f (𝟙 Y)
  tensorHom := tensorHomImpl
  leftUnitor := leftUnitorImpl
  rightUnitor := rightUnitorImpl
  associator := associatorImpl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Dial.id_tensorHom_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Dial`。
形式化陈述：id_tensorHom_id (X₁ X₂ : Dial C) : (𝟙 X₁ otimesₘ 𝟙 X₂ : _ ⟶ _) = 𝟙 (X₁ oti
mes X₂ : Dial C)
参数：X₁ X₂ : Dial C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Dial.hom_ext`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst_2 : C
ategoryTheory.Lim…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.map_id_id`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y],   CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
theorem id_tensorHom_id (X₁ X₂ : Dial C) : (𝟙 X₁ ⊗ₘ 𝟙 X₂ : _ ⟶ _) = 𝟙 (X₁ ⊗ X₂ : Dial C) := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- TODO: fix the non-terminal simp
set_option linter.flexible false in
/-
**CategoryTheory.Dial.tensorHom_comp_tensorHom** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Dial`。
形式化陈述：tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Dial C} (f₁ : X₁ ⟶ Y₁) (f₂ :
 X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) : (f₁ otimesₘ f₂) ≫ (g₁ otimesₘ g₂) = (f
₁ ≫ g₁) otimesₘ (f₂ ≫ g₂)
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；g₁ : Y₁ ⟶ Z₁；g₂ : Y₂ ⟶ Z₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Dial.hom_ext`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst_2 : C
ategoryTheory.Lim…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.map_map`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}   [inst_1 : CategoryTheory.Limits.H
asBinaryProduct A₁ B₁] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.prod.map_map_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}   [inst_1 : CategoryTheory.Li
mits.HasBinaryProduct A₁ B₁] […
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.lift_map_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Ha
sBinaryProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Dial C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
  ext <;> simp; ext <;> simp <;> (rw [← Category.assoc]; congr 1; simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Dial.associator_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Dial`。
形式化陈述：associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Dial C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂
 ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) : tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).h
om = (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃)
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；f₃ : X₃ ⟶ Y₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Dial.hom_ext`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst_2 : C
ategoryTheory.Lim…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.prod.map_fst_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.lift_fst_comp_snd_comp`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Lim
its.HasBinaryProduct W Y] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Dial.associator_hom_F`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [i
nst_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.prod.map_snd_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.prod.map_map_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}   [inst_1 : CategoryTheory.Li
mits.HasBinaryProduct A₁ B₁] […
· 使用定理 `CategoryTheory.Limits.prod.lift_map_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Ha
sBinaryProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Dial C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
    (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- TODO: fix the non-terminal simp
set_option linter.flexible false in
/-
**CategoryTheory.Dial.leftUnitor_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Dial`。
形式化陈述：leftUnitor_naturality {X Y : Dial C} (f : X ⟶ Y) : (𝟙 (𝟙_ (Dial C)) otimes
ₘ f) ≫ (fun_ Y).hom = (fun_ X).hom ≫ f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Dial.hom_ext`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst_2 : C
ategoryTheory.Lim…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Dial.leftUnitor_hom_F`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [i
nst_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.lift_map_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Ha
sBinaryProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `CategoryTheory.Limits.terminal.hom_ext`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P : 
C}   (f g : P ⟶ ⊤_ C), f = g
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
-/
theorem leftUnitor_naturality {X Y : Dial C} (f : X ⟶ Y) :
    (𝟙 (𝟙_ (Dial C)) ⊗ₘ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  ext <;> simp; ext; simp; congr 1; ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- TODO: fix the non-terminal simp
set_option linter.flexible false in
/-
**CategoryTheory.Dial.rightUnitor_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Dial`。
形式化陈述：rightUnitor_naturality {X Y : Dial C} (f : X ⟶ Y) : (f otimesₘ 𝟙 (𝟙_ (Dial
 C))) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Dial.hom_ext`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst_2 : C
ategoryTheory.Lim…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Dial.rightUnitor_hom_F`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [
inst_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用定理 `CategoryTheory.Limits.prod.lift_map_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Ha
sBinaryProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `CategoryTheory.Limits.terminal.hom_ext`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P : 
C}   (f g : P ⟶ ⊤_ C), f = g
-/
theorem rightUnitor_naturality {X Y : Dial C} (f : X ⟶ Y) :
    (f ⊗ₘ 𝟙 (𝟙_ (Dial C))) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  ext <;> simp; ext; simp; congr 1; ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Dial.pentagon** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Dial`。
形式化陈述：pentagon (W X Y Z : Dial C) : (tensorHom (associator W X Y).hom (𝟙 Z)) ≫ (
associator W (tensorObj X Y) Z).hom ≫ (tensorHom (𝟙 W) (associator X Y Z).hom) =
 (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom
参数：W X Y Z : Dial C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Dial.hom_ext`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst_2 : C
ategoryTheory.Lim…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.map_fst_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Dial.associator_hom_F`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [i
nst_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.prod.map_snd_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem pentagon (W X Y Z : Dial C) :
    (tensorHom (associator W X Y).hom (𝟙 Z)) ≫ (associator W (tensorObj X Y) Z).hom ≫
      (tensorHom (𝟙 W) (associator X Y Z).hom) =
    (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
  ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Dial.triangle** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Dial`。
形式化陈述：triangle (X Y : Dial C) : (associator X (𝟙_ (Dial C)) Y).hom ≫ tensorHom (
𝟙 X) (leftUnitor Y).hom = tensorHom (rightUnitor X).hom (𝟙 Y)
参数：X Y : Dial C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Dial.hom_ext`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst_2 : C
ategoryTheory.Lim…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Dial.leftUnitor_hom_F`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [i
nst_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用定理 `CategoryTheory.Limits.prod.map_snd_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Dial.associator_hom_F`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [i
nst_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Dial.rightUnitor_hom_F`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [
inst_2 : CategoryTheory.Lim…
-/
theorem triangle (X Y : Dial C) :
    (associator X (𝟙_ (Dial C)) Y).hom ≫ tensorHom (𝟙 X) (leftUnitor Y).hom =
    tensorHom (rightUnitor X).hom (𝟙 Y) := by cat_disch
/-
**CategoryTheory.Dial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Dial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalCategory (Dial C) :=
  .ofTensorHom
    (id_tensorHom_id := id_tensorHom_id)
    (tensorHom_comp_tensorHom := tensorHom_comp_tensorHom)
    (associator_naturality := associator_naturality)
    (leftUnitor_naturality := leftUnitor_naturality)
    (rightUnitor_naturality := rightUnitor_naturality)
    (pentagon := pentagon)
    (triangle := triangle)

set_option backward.isDefEq.respectTransparency false in
/-- The braiding isomorphism `X ⊗ Y ≅ Y ⊗ X` in `Dial C`. -/
/-
**CategoryTheory.Dial.braiding** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Dial`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasFiniteProducts C] →       [inst_2 : CategoryTheory.Lim
its.HasPullbacks C] →         (X Y : CategoryTheory.Dial C) →           Category
Theory.MonoidalCategoryStruct.tensorObj X Y ≅ CategoryTheory.MonoidalCategoryStr
uct.tensorObj Y X
参数：X Y : CategoryTheory.Dial C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The braiding isomorphism `X ⊗ Y ≅ Y ⊗ X` in `Dial C`.
-/
@[simps!] def braiding (X Y : Dial C) : tensorObj X Y ≅ tensorObj Y X :=
  isoMk (prod.braiding ..) (prod.braiding ..) <| by
    simp [Subobject.inf_pullback, ← Subobject.pullback_comp, inf_comm]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Dial.symmetry** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Dial`。
形式化陈述：symmetry (X Y : Dial C) : (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 (ten
sorObj X Y)
参数：X Y : Dial C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Dial.hom_ext`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst_2 : C
ategoryTheory.Lim…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.lift_fst_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryP
roduct X Y],   CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Dial.braiding_hom_F`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [ins
t_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.prod.map_snd_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
-/
theorem symmetry (X Y : Dial C) :
    (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 (tensorObj X Y) := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Dial.braiding_naturality_right** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Dial`。
形式化陈述：braiding_naturality_right (X : Dial C) {Y Z : Dial C} (f : Y ⟶ Z) : tensor
Hom (𝟙 X) f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ tensorHom f (𝟙 X)
参数：X : Dial C；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.Dial.hom_ext`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst_2 : C
ategoryTheory.Lim…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Dial.braiding_hom_F`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [ins
t_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.prod.map_snd_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Dial.whiskerLeft_F`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst
_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.lift_map_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Ha
sBinaryProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.prod.lift_fst_comp_snd_comp`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Lim
its.HasBinaryProduct W Y] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Dial.whiskerRight_F`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [ins
t_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.prod.map_map_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}   [inst_1 : CategoryTheory.Li
mits.HasBinaryProduct A₁ B₁] […
-/
theorem braiding_naturality_right (X : Dial C) {Y Z : Dial C} (f : Y ⟶ Z) :
    tensorHom (𝟙 X) f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ tensorHom f (𝟙 X) := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Dial.braiding_naturality_left** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Dial`。
形式化陈述：braiding_naturality_left {X Y : Dial C} (f : X ⟶ Y) (Z : Dial C) : tensorH
om f (𝟙 Z) ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ tensorHom (𝟙 Z) f
参数：f : X ⟶ Y；Z : Dial C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.Dial.hom_ext`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst_2 : C
ategoryTheory.Lim…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Dial.braiding_hom_F`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [ins
t_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.prod.map_snd_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Dial.whiskerRight_F`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [ins
t_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.prod.lift_map_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Ha
sBinaryProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.lift_fst_comp_snd_comp`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Lim
its.HasBinaryProduct W Y] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Dial.whiskerLeft_F`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst
_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.prod.map_map_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}   [inst_1 : CategoryTheory.Li
mits.HasBinaryProduct A₁ B₁] […
-/
theorem braiding_naturality_left {X Y : Dial C} (f : X ⟶ Y) (Z : Dial C) :
    tensorHom f (𝟙 Z) ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ tensorHom (𝟙 Z) f := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Dial.hexagon_forward** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Dial`。
形式化陈述：hexagon_forward (X Y Z : Dial C) : (associator X Y Z).hom ≫ (braiding X (Y
 otimes Z)).hom ≫ (associator Y Z X).hom = tensorHom (braiding X Y).hom (𝟙 Z) ≫ 
(associator Y X Z).hom ≫ tensorHom (𝟙 Y) (braiding X Z).hom
参数：X Y Z : Dial C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.Dial.hom_ext`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst_2 : C
ategoryTheory.Lim…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.prod.map_fst_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Dial.associator_hom_F`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [i
nst_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.prod.map_snd_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Dial.braiding_hom_F`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [ins
t_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Dial.whiskerLeft_F`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst
_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Dial.whiskerRight_F`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [ins
t_2 : CategoryTheory.Lim…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem hexagon_forward (X Y Z : Dial C) :
    (associator X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (associator Y Z X).hom =
      tensorHom (braiding X Y).hom (𝟙 Z) ≫ (associator Y X Z).hom ≫
      tensorHom (𝟙 Y) (braiding X Z).hom := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Dial.hexagon_reverse** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Dial`。
形式化陈述：hexagon_reverse (X Y Z : Dial C) : (associator X Y Z).inv ≫ (braiding (X o
times Y) Z).hom ≫ (associator Z X Y).inv = tensorHom (𝟙 X) (braiding Y Z).hom ≫ 
(associator X Z Y).inv ≫ tensorHom (braiding X Z).hom (𝟙 Y)
参数：X Y Z : Dial C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.Dial.hom_ext`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst_2 : C
ategoryTheory.Lim…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.prod.map_snd_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Dial.associator_inv_F`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [i
nst_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Dial.braiding_hom_F`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [ins
t_2 : CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Dial.whiskerRight_F`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [ins
t_2 : CategoryTheory.Lim…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Dial.whiskerLeft_F`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst
_2 : CategoryTheory.Lim…
-/
theorem hexagon_reverse (X Y Z : Dial C) :
    (associator X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (associator Z X Y).inv =
      tensorHom (𝟙 X) (braiding Y Z).hom ≫ (associator X Z Y).inv ≫
      tensorHom (braiding X Z).hom (𝟙 Y) := by cat_disch
/-
**CategoryTheory.Dial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Dial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SymmetricCategory (Dial C) where
  braiding := braiding
  braiding_naturality_right := braiding_naturality_right
  braiding_naturality_left := braiding_naturality_left
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse
  symmetry := symmetry

end Dial

end CategoryTheory

