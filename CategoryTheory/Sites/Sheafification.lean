/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
/-!

# Sheafification

Given a site `(C, J)` we define a typeclass `HasSheafify J A` saying that the inclusion functor from
`A`-valued sheaves on `C` to presheaves admits a left exact left adjoint (sheafification).

Note: to access the `HasSheafify` instance for suitable concrete categories, import the file
`Mathlib/CategoryTheory/Sites/LeftExact.lean`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
variable (A : Type u₂) [Category.{v₂} A]

/--
A proposition saying that the inclusion functor from sheaves to presheaves admits a left adjoint.
-/
/-
**CategoryTheory.HasWeakSheafify** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：HasWeakSheafify : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A proposition saying that the inclusion functor from sheaves to presheaves admit
s a left adjoint.
-/
abbrev HasWeakSheafify : Prop := (sheafToPresheaf J A).IsRightAdjoint

/--
`HasSheafify` means that the inclusion functor from sheaves to presheaves admits a left exact
left adjoint (sheafification).

Given a functor, preserving finite limits, `F : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A` and an adjunction
`adj : F ⊣ sheafToPresheaf J A`, use `HasSheafify.mk'` to construct a `HasSheafify` instance.
-/
/-
**CategoryTheory.HasSheafify** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     Catego
ryTheory.GrothendieckTopology C → (A : Type u₂) → [CategoryTheory.Category.{v₂, 
u₂} A] → Prop
参数：A : Type u₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasSheafify` means that the inclusion functor from sheaves to presheaves admits
 a left exact
left adjoint (sheafification).

Given a functor, preserving finite limits, `F : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A` and an ad
junction
`adj : F ⊣ sheafToPresheaf J A`, use `HasSheafify.mk'` to construct a `HasSheafi
fy` instance.
-/
class HasSheafify : Prop where
  isRightAdjoint : HasWeakSheafify J A
  isLeftExact : PreservesFiniteLimits ((sheafToPresheaf J A).leftAdjoint)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasSheafify J A] : HasWeakSheafify J A := HasSheafify.isRightAdjoint

noncomputable section
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasSheafify J A] : PreservesFiniteLimits ((sheafToPresheaf J A).leftAdjoint) :=
  HasSheafify.isLeftExact
/-
**CategoryTheory.HasSheafify.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.HasSh
eafify`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryT
heory.GrothendieckTopology C) (A : Type u₂)   [inst_1 : CategoryTheory.Category.
{v₂, u₂} A]   {F : CategoryTheory.Functor (CategoryTheory.Functor Cᵒᵖ A) (Catego
ryTheory.Sheaf J A)}   (adj : F ⊣ CategoryTheory.sheafToPresheaf J A) [CategoryT
heory.Limits.PreservesFiniteLimits F],   CategoryTheory.HasSheafify J A
参数：J : CategoryTheory.GrothendieckTopology C；A : Type u₂；CategoryTheory.Functor 
Cᵒᵖ A；CategoryTheory.Sheaf J A；adj : F ⊣ CategoryTheory.sheafToPresheaf J A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_natIso`：preservesLimitsO
fShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] : Preser
vesLimitsOfShape J G where preservesLimit {K…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
theorem HasSheafify.mk' {F : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A} (adj : F ⊣ sheafToPresheaf J A)
    [PreservesFiniteLimits F] : HasSheafify J A where
  isRightAdjoint := ⟨F, ⟨adj⟩⟩
  isLeftExact := ⟨by
    have : (sheafToPresheaf J A).IsRightAdjoint := ⟨_, ⟨adj⟩⟩
    exact fun _ _ _ ↦ preservesLimitsOfShape_of_natIso
      (adj.leftAdjointUniq (Adjunction.ofIsRightAdjoint (sheafToPresheaf J A)))⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasSheafify (⊥ : GrothendieckTopology C) A :=
  HasSheafify.mk' _ _
    (sheafBotEquivalence A).symm.toAdjunction
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F G : Sheaf J A} [HasWeakSheafify J A] (f : F ⟶ G) [Mono f] : Mono f.hom :=
  inferInstanceAs (Mono ((sheafToPresheaf J A).map f))

/-- The sheafification functor, left adjoint to the inclusion. -/
/-
**CategoryTheory.presheafToSheaf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：presheafToSheaf [HasWeakSheafify J A] : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheafification functor, left adjoint to the inclusion.
-/
def presheafToSheaf [HasWeakSheafify J A] : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  (sheafToPresheaf J A).leftAdjoint
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasSheafify J A] : PreservesFiniteLimits (presheafToSheaf J A) :=
  HasSheafify.isLeftExact

/-- The sheafification-inclusion adjunction. -/
/-
**CategoryTheory.sheafificationAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory`。
形式化陈述：sheafificationAdjunction [HasWeakSheafify J A] : presheafToSheaf J A ⊣ she
afToPresheaf J A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheafification-inclusion adjunction.
-/
def sheafificationAdjunction [HasWeakSheafify J A] :
    presheafToSheaf J A ⊣ sheafToPresheaf J A := Adjunction.ofIsRightAdjoint _
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasWeakSheafify J A] : (presheafToSheaf J A).IsLeftAdjoint :=
  ⟨_, ⟨sheafificationAdjunction J A⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasWeakSheafify J A] : Reflective (sheafToPresheaf J A) where
  L := presheafToSheaf J A
  adj := sheafificationAdjunction _ _
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasSheafify J A] : PreservesFiniteLimits (reflector (sheafToPresheaf J A)) :=
  inferInstanceAs (PreservesFiniteLimits (presheafToSheaf _ _))

end

variable {D : Type*} [Category* D] [HasWeakSheafify J D]

/-- The sheafification of a presheaf `P`. -/
/-
**CategoryTheory.sheafify** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafify (P : Cᵒᵖ ⥤ D) : Cᵒᵖ ⥤ D
参数：P : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheafification of a presheaf `P`.
-/
noncomputable abbrev sheafify (P : Cᵒᵖ ⥤ D) : Cᵒᵖ ⥤ D :=
  presheafToSheaf J D |>.obj P |>.obj

/-- The canonical map from `P` to its sheafification. -/
/-
**CategoryTheory.toSheafify** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：toSheafify (P : Cᵒᵖ ⥤ D) : P ⟶ sheafify J P
参数：P : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `P` to its sheafification.
-/
noncomputable abbrev toSheafify (P : Cᵒᵖ ⥤ D) : P ⟶ sheafify J P :=
  sheafificationAdjunction J D |>.unit.app P

@[simp]
/-
**CategoryTheory.sheafificationAdjunction_unit_app** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：sheafificationAdjunction_unit_app (P : Cᵒᵖ ⥤ D) : (sheafificationAdjunctio
n J D).unit.app P = toSheafify J P
参数：P : Cᵒᵖ ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sheafificationAdjunction_unit_app (P : Cᵒᵖ ⥤ D) :
    (sheafificationAdjunction J D).unit.app P = toSheafify J P := rfl

/-- The canonical map on sheafifications induced by a morphism. -/
/-
**CategoryTheory.sheafifyMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafifyMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : sheafify J P ⟶ sheafify J Q
参数：η : P ⟶ Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map on sheafifications induced by a morphism.
-/
noncomputable abbrev sheafifyMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : sheafify J P ⟶ sheafify J Q :=
  presheafToSheaf J D |>.map η |>.hom

@[simp]
/-
**CategoryTheory.sheafifyMap_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：sheafifyMap_id (P : Cᵒᵖ ⥤ D) : sheafifyMap J (𝟙 P) = 𝟙 (sheafify J P)
参数：P : Cᵒᵖ ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sheafifyMap_id (P : Cᵒᵖ ⥤ D) : sheafifyMap J (𝟙 P) = 𝟙 (sheafify J P) := by
  simp [sheafifyMap, sheafify]

@[simp]
/-
**CategoryTheory.sheafifyMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：sheafifyMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) : sheafifyMap J
 (η ≫ γ) = sheafifyMap J η ≫ sheafifyMap J γ
参数：η : P ⟶ Q；γ : Q ⟶ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sheafifyMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    sheafifyMap J (η ≫ γ) = sheafifyMap J η ≫ sheafifyMap J γ := by
  simp [sheafifyMap, sheafify]

@[reassoc (attr := simp)]
/-
**CategoryTheory.toSheafify_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：toSheafify_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : η ≫ toSheafify J _ = t
oSheafify J _ ≫ sheafifyMap J η
参数：η : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem toSheafify_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η ≫ toSheafify J _ = toSheafify J _ ≫ sheafifyMap J η :=
  sheafificationAdjunction J D |>.unit.naturality η

variable (D)

/-- The sheafification of a presheaf `P`, as a functor. -/
/-
**CategoryTheory.sheafification** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafification : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheafification of a presheaf `P`, as a functor.
-/
noncomputable abbrev sheafification : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D :=
  presheafToSheaf J D ⋙ sheafToPresheaf J D
/-
**CategoryTheory.sheafification_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：sheafification_obj (P : Cᵒᵖ ⥤ D) : (sheafification J D).obj P = sheafify J
 P
参数：P : Cᵒᵖ ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sheafification_obj (P : Cᵒᵖ ⥤ D) : (sheafification J D).obj P = sheafify J P :=
  rfl
/-
**CategoryTheory.sheafification_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：sheafification_map {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : (sheafification J D).map 
η = sheafifyMap J η
参数：η : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sheafification_map {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    (sheafification J D).map η = sheafifyMap J η :=
  rfl

/-- The canonical map from `P` to its sheafification, as a natural transformation. -/
/-
**CategoryTheory.toSheafification** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：toSheafification : 𝟭 _ ⟶ sheafification J D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `P` to its sheafification, as a natural transformation.
-/
noncomputable abbrev toSheafification : 𝟭 _ ⟶ sheafification J D :=
  sheafificationAdjunction J D |>.unit
/-
**CategoryTheory.toSheafification_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：toSheafification_app (P : Cᵒᵖ ⥤ D) : (toSheafification J D).app P = toShea
fify J P
参数：P : Cᵒᵖ ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSheafification_app (P : Cᵒᵖ ⥤ D) : (toSheafification J D).app P = toSheafify J P :=
  rfl

variable {D}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.isIso_toSheafify** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isIso_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : IsIso (toShea
fify J P)
参数：hP : Presheaf.IsSheaf J P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.inv_counit_map`：inv_counit_map {X : D} [IsIso 
(h.counit.app X)] : inv (R.map (h.counit.app X)) = h.unit.app (R.obj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isIso_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : IsIso (toSheafify J P) := by
  refine ⟨(sheafificationAdjunction J D |>.counit.app ⟨P, hP⟩).hom, ?_, ?_⟩
  · exact sheafificationAdjunction J D |>.right_triangle_components ⟨P, hP⟩
  · change (sheafToPresheaf _ _).map _ ≫ _ = _
    change _ ≫ (sheafificationAdjunction J D).unit.app ((sheafToPresheaf J D).obj ⟨P, hP⟩) = _
    rw [← (sheafificationAdjunction J D).inv_counit_map (X := ⟨P, hP⟩)]
    simp

/-- If `P` is a sheaf, then `P` is isomorphic to `sheafify J P`. -/
/-
**CategoryTheory.isoSheafify** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：isoSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : P ≅ sheafify J P
参数：hP : Presheaf.IsSheaf J P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_toSheafify`：isIso_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Pr
esheaf.IsSheaf J P) : IsIso (toSheafify J P)

--- 原说明 ---
If `P` is a sheaf, then `P` is isomorphic to `sheafify J P`.
-/
noncomputable def isoSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : P ≅ sheafify J P :=
  letI := isIso_toSheafify J hP
  asIso (toSheafify J P)

@[simp]
/-
**CategoryTheory.isoSheafify_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isoSheafify_hom {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : (isoSheafify J
 hP).hom = toSheafify J P
参数：hP : Presheaf.IsSheaf J P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoSheafify_hom {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (isoSheafify J hP).hom = toSheafify J P :=
  rfl

/-- Given a sheaf `Q` and a morphism `P ⟶ Q`, construct a morphism from `sheafify J P` to `Q`. -/
/-
**CategoryTheory.sheafifyLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : she
afify J P ⟶ Q
参数：η : P ⟶ Q；hQ : Presheaf.IsSheaf J Q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a sheaf `Q` and a morphism `P ⟶ Q`, construct a morphism from `sheafify J 
P` to `Q`.
-/
noncomputable def sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    sheafify J P ⟶ Q :=
  (sheafificationAdjunction J D).homEquiv P ⟨Q, hQ⟩ |>.symm η |>.hom

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.sheafificationAdjunction_counit_app_val** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory`。
形式化陈述：sheafificationAdjunction_counit_app_val (P : Sheaf J D) : ((sheafification
Adjunction J D).counit.app P).hom = sheafifyLift J (𝟙 P.obj) P.property
参数：P : Sheaf J D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sheafificationAdjunction_counit_app_val (P : Sheaf J D) :
    ((sheafificationAdjunction J D).counit.app P).hom = sheafifyLift J (𝟙 P.obj) P.property := by
  unfold sheafifyLift
  rw [Adjunction.homEquiv_counit]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.toSheafify_sheafifyLift** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：toSheafify_sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf
 J Q) : toSheafify J P ≫ sheafifyLift J η hQ = η
参数：η : P ⟶ Q；hQ : Presheaf.IsSheaf J Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.toSheafify.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C) {D : Type u_1}  
 [inst_1 : CategoryT…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.sheafifyLift.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C) {D : Type u_1}
   [inst_1 : CategoryT…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSheafify_sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    toSheafify J P ≫ sheafifyLift J η hQ = η := by
  rw [toSheafify, sheafifyLift, Adjunction.homEquiv_counit]
  change _ ≫ (sheafToPresheaf J D).map _ ≫ _ = _
  simp only [Adjunction.unit_naturality_assoc]
  change _ ≫ (sheafificationAdjunction J D).unit.app ((sheafToPresheaf J D).obj ⟨Q, hQ⟩) ≫ _ = _
  change _ ≫ _ ≫ (sheafToPresheaf J D).map _ = _
  rw [sheafificationAdjunction J D |>.right_triangle_components (Y := ⟨Q, hQ⟩)]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.sheafifyLift_unique** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q
) (γ : sheafify J P ⟶ Q) : toSheafify J P ≫ γ = η -> γ = sheafifyLift J η hQ
参数：η : P ⟶ Q；hQ : Presheaf.IsSheaf J Q；γ : sheafify J P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.sheafifyLift.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C) {D : Type u_1}
   [inst_1 : CategoryT…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sheaf.hom_ext_iff`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Type u₂} 
  [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_apply_eq`：homEquiv_apply_eq {A : C} {
B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) : adj.homEquiv A B f = g ↔ f = (adj.h
omEquiv A B).symm g
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.toSheafify.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C) {D : Type u_1}  
 [inst_1 : CategoryT…
-/
theorem sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (γ : sheafify J P ⟶ Q) : toSheafify J P ≫ γ = η → γ = sheafifyLift J η hQ := by
  intro h
  rw [toSheafify] at h
  rw [sheafifyLift]
  let γ' : (presheafToSheaf J D).obj P ⟶ ⟨Q, hQ⟩ := ⟨γ⟩
  change γ'.hom = _
  rw [← Sheaf.hom_ext_iff, ← Adjunction.homEquiv_apply_eq, Adjunction.homEquiv_unit]
  exact h

@[simp]
/-
**CategoryTheory.isoSheafify_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isoSheafify_inv {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : (isoSheafify J
 hP).inv = sheafifyLift J (𝟙 _) hP
参数：hP : Presheaf.IsSheaf J P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.sheafifyLift_unique`：sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} 
(η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ : sheafify J P ⟶ Q) : toSheafify J P 
≫ γ = η -> γ = sheafifyL…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoSheafify_inv {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (isoSheafify J hP).inv = sheafifyLift J (𝟙 _) hP := by
  apply sheafifyLift_unique
  simp [Iso.comp_inv_eq]
/-
**CategoryTheory.sheafify_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：sheafify_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : sheafify J P ⟶ Q) (hQ : Presheaf.I
sSheaf J Q) (h : toSheafify J P ≫ η = toSheafify J P ≫ γ) : η = γ
参数：η γ : sheafify J P ⟶ Q；hQ : Presheaf.IsSheaf J Q；h : toSheafify J P ≫ η = toS
heafify J P ≫ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.sheafifyLift_unique`：sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} 
(η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ : sheafify J P ⟶ Q) : toSheafify J P 
≫ γ = η -> γ = sheafifyL…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sheafify_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : sheafify J P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (h : toSheafify J P ≫ η = toSheafify J P ≫ γ) : η = γ := by
  rw [sheafifyLift_unique J _ hQ _ h, ← h]
  exact (sheafifyLift_unique J _ hQ _ h.symm).symm

@[reassoc (attr := simp)]
/-
**CategoryTheory.sheafifyMap_sheafifyLift** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：sheafifyMap_sheafifyLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : P
resheaf.IsSheaf J R) : sheafifyMap J η ≫ sheafifyLift J γ hR = sheafifyLift J (η
 ≫ γ) hR
参数：η : P ⟶ Q；γ : Q ⟶ R；hR : Presheaf.IsSheaf J R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.sheafifyLift_unique`：sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} 
(η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ : sheafify J P ⟶ Q) : toSheafify J P 
≫ γ = η -> γ = sheafifyL…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.toSheafify_naturality`：toSheafify_naturality {P Q : Cᵒᵖ ⥤
 D} (η : P ⟶ Q) : η ≫ toSheafify J _ = toSheafify J _ ≫ sheafifyMap J η
· 使用定理 `CategoryTheory.toSheafify_sheafifyLift`：toSheafify_sheafifyLift {P Q : C
ᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : toSheafify J P ≫ sheafifyLift 
J η hQ = η
-/
theorem sheafifyMap_sheafifyLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
    (hR : Presheaf.IsSheaf J R) :
    sheafifyMap J η ≫ sheafifyLift J γ hR = sheafifyLift J (η ≫ γ) hR := by
  apply sheafifyLift_unique
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc, toSheafify_sheafifyLift]
/-
**CategoryTheory.sheafifyLift_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：sheafifyLift_comp {F P Q : Cᵒᵖ ⥤ D} (a : F ⟶ P) (hP : Presheaf.IsSheaf J P
) (η : P ⟶ Q) (hQ : CategoryTheory.Presheaf.IsSheaf J Q) : sheafifyLift J (a ≫ η
) hQ = sheafifyLift _ a hP ≫ η
参数：a : F ⟶ P；hP : Presheaf.IsSheaf J P；η : P ⟶ Q；hQ : CategoryTheory.Presheaf.Is
Sheaf J Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.sheafifyLift_unique`：sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} 
(η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ : sheafify J P ⟶ Q) : toSheafify J P 
≫ γ = η -> γ = sheafifyL…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.toSheafify_sheafifyLift_assoc`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C) {D
 : Type u_1}   [inst_1 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sheafifyLift_comp {F P Q : Cᵒᵖ ⥤ D} (a : F ⟶ P) (hP : Presheaf.IsSheaf J P)
    (η : P ⟶ Q) (hQ : CategoryTheory.Presheaf.IsSheaf J Q) :
    sheafifyLift J (a ≫ η) hQ = sheafifyLift _ a hP ≫ η :=
  (sheafifyLift_unique _ _ _ _ (by simp)).symm

variable {J}

/-- A sheaf `P` is isomorphic to its own sheafification. -/
@[simps]
/-
**CategoryTheory.sheafificationIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafificationIso (P : Sheaf J D) : P ≅ (presheafToSheaf J D).obj P.obj wh
ere hom
参数：P : Sheaf J D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sheaf `P` is isomorphic to its own sheafification.
-/
noncomputable def sheafificationIso (P : Sheaf J D) : P ≅ (presheafToSheaf J D).obj P.obj where
  hom := ⟨(isoSheafify J P.2).hom⟩
  inv := ⟨(isoSheafify J P.2).inv⟩
  hom_inv_id := by
    ext1
    apply (isoSheafify J P.2).hom_inv_id
  inv_hom_id := by
    ext1
    apply (isoSheafify J P.2).inv_hom_id
/-
**CategoryTheory.isIso_sheafificationAdjunction_counit** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory`。
形式化陈述：isIso_sheafificationAdjunction_counit (P : Sheaf J D) : IsIso ((sheafifica
tionAdjunction J D).counit.app P)
参数：P : Sheaf J D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_of_fully_faithful`：isIso_of_fully_faithful (f : X ⟶
 Y) [IsIso (F.map f)] : IsIso f
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
-/
instance isIso_sheafificationAdjunction_counit (P : Sheaf J D) :
    IsIso ((sheafificationAdjunction J D).counit.app P) :=
  isIso_of_fully_faithful (sheafToPresheaf J D) _
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : Sheaf J D) :
    IsIso ((sheafificationAdjunction J D).counit.app P).hom :=
  inferInstanceAs (IsIso ((sheafToPresheaf J D).map _))
/-
**CategoryTheory.sheafification_reflective** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory`。
形式化陈述：sheafification_reflective : IsIso (sheafificationAdjunction J D).counit
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
-/
instance sheafification_reflective : IsIso (sheafificationAdjunction J D).counit :=
  NatIso.isIso_of_isIso_app _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.sheafifyLift_id_toSheafify** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：sheafifyLift_id_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : she
afifyLift J (𝟙 P) hP ≫ toSheafify J P = 𝟙 (sheafify J P)
参数：hP : Presheaf.IsSheaf J P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.instMonoFunctorOppositeHomFullSubcategoryIsSheafOfHasWeak
SheafifyOfSheaf`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J 
: CategoryTheory.GrothendieckTopology C) (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.toSheafify_naturality`：toSheafify_naturality {P Q : Cᵒᵖ ⥤
 D} (η : P ⟶ Q) : η ≫ toSheafify J _ = toSheafify J _ ≫ sheafifyMap J η
· 使用定理 `CategoryTheory.sheafificationAdjunction_counit_app_val`：sheafificationAd
junction_counit_app_val (P : Sheaf J D) : ((sheafificationAdjunction J D).counit
.app P).hom = sheafifyLift J (𝟙 P.obj) P.pro…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.sheafifyMap_sheafifyLift`：sheafifyMap_sheafifyLift {P Q R
 : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : Presheaf.IsSheaf J R) : sheafifyMap J 
η ≫ sheafifyLift J γ hR = she…
· 使用定理 `CategoryTheory.sheafifyLift.congr_simp`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C) {D : Typ
e u_1}   [inst_1 : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.toSheafify_sheafifyLift`：toSheafify_sheafifyLift {P Q : C
ᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : toSheafify J P ≫ sheafifyLift 
J η hQ = η
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sheafifyLift_id_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    sheafifyLift J (𝟙 P) hP ≫ toSheafify J P = 𝟙 (sheafify J P) := by
  rw [← cancel_mono ((sheafificationAdjunction J D).counit.app ⟨P, hP⟩).hom]
  cat_disch

variable (J D)

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism `𝟭 (Sheaf J D) ≅ sheafToPresheaf J D ⋙ presheafToSheaf J D`. -/
@[simps!]
/-
**CategoryTheory.sheafificationNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：sheafificationNatIso : 𝟭 (Sheaf J D) ≅ sheafToPresheaf J D ⋙ presheafToShe
af J D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `𝟭 (Sheaf J D) ≅ sheafToPresheaf J D ⋙ presheafToSheaf J
 D`.
-/
noncomputable def sheafificationNatIso :
    𝟭 (Sheaf J D) ≅ sheafToPresheaf J D ⋙ presheafToSheaf J D :=
  NatIso.ofComponents (fun P => sheafificationIso P) (by cat_disch)

end CategoryTheory

