/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Preservation of biproducts

We define the image of a (binary) bicone under a functor that preserves zero morphisms and define
classes `PreservesBiproduct` and `PreservesBinaryBiproduct`. We then

* show that a functor that preserves biproducts of a two-element type preserves binary biproducts,
* construct the comparison morphisms between the image of a biproduct and the biproduct of the
  images and show that the biproduct is preserved if one of them is an isomorphism,
* give the canonical isomorphism between the image of a biproduct and the biproduct of the images
  in case that the biproduct is preserved.

-/

@[expose] public section


universe w₁ w₂ v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section HasZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroMorphisms D]

namespace Functor

section Map

variable (F : C ⥤ D) [PreservesZeroMorphisms F]

section Bicone

variable {J : Type w₁}

set_option backward.isDefEq.respectTransparency false in
/-- The image of a bicone under a functor. -/
@[simps]
/-
**CategoryTheory.Functor.mapBicone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：mapBicone {f : J -> C} (b : Bicone f) : Bicone (F.obj ∘ f) where pt
参数：b : Bicone f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a bicone under a functor.
-/
def mapBicone {f : J → C} (b : Bicone f) : Bicone (F.obj ∘ f) where
  pt := F.obj b.pt
  π j := F.map (b.π j)
  ι j := F.map (b.ι j)
  ι_π j j' := by
    rw [← F.map_comp]
    split_ifs with h
    · subst h
      simp only [bicone_ι_π_self, CategoryTheory.Functor.map_id, eqToHom_refl]; dsimp
    · rw [bicone_ι_π_ne _ h, F.map_zero]
/-
**CategoryTheory.Functor.mapBicone_whisker** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：mapBicone_whisker {K : Type w₂} {g : K ≃ J} {f : J -> C} (c : Bicone f) : 
F.mapBicone (c.whisker g) = (F.mapBicone c).whisker g
参数：c : Bicone f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapBicone_whisker {K : Type w₂} {g : K ≃ J} {f : J → C} (c : Bicone f) :
    F.mapBicone (c.whisker g) = (F.mapBicone c).whisker g :=
  rfl

end Bicone

/-- The image of a binary bicone under a functor. -/
@[simps!]
/-
**CategoryTheory.Functor.mapBinaryBicone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：mapBinaryBicone {X Y : C} (b : BinaryBicone X Y) : BinaryBicone (F.obj X) 
(F.obj Y)
参数：b : BinaryBicone X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a binary bicone under a functor.
-/
def mapBinaryBicone {X Y : C} (b : BinaryBicone X Y) : BinaryBicone (F.obj X) (F.obj Y) :=
  (BinaryBicones.functoriality _ _ F).obj b

end Map

end Functor

open CategoryTheory.Functor

namespace Limits

section Bicone

variable {J : Type w₁} {K : Type w₂}

/-- A functor `F` preserves biproducts of `f` if `F` maps every bilimit bicone over `f` to a
bilimit bicone over `F.obj ∘ f`. -/
/-
**CategoryTheory.Limits.PreservesBiproduct** 是 Mathlib 中的一个归纳类型，位于命名空间 `Category
Theory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         [inst_2 
: CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : CategoryTheory
.Limits.HasZeroMorphisms D] →             {J : Type w₁} → (J → C) → (F : Categor
yTheory.Functor C D) → [F.PreservesZeroMorphisms] → Prop
参数：J → C；F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` preserves biproducts of `f` if `F` maps every bilimit bicone over 
`f` to a
bilimit bicone over `F.obj ∘ f`.
-/
class PreservesBiproduct (f : J → C) (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {b : Bicone f}, b.IsBilimit → Nonempty (F.mapBicone b).IsBilimit

attribute [inherit_doc PreservesBiproduct] PreservesBiproduct.preserves

/-- A functor `F` preserves biproducts of `f` if `F` maps every bilimit bicone over `f` to a
bilimit bicone over `F.obj ∘ f`. -/
/-
**CategoryTheory.Limits.isBilimitOfPreserves** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：isBilimitOfPreserves {f : J -> C} (F : C ⥤ D) [PreservesZeroMorphisms F] [
PreservesBiproduct f F] {b : Bicone f} (hb : b.IsBilimit) : (F.mapBicone b).IsBi
limit
参数：F : C ⥤ D；hb : b.IsBilimit。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesBiproduct.preserves`：∀ {C : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D}   {inst_2 : Category…

--- 原说明 ---
A functor `F` preserves biproducts of `f` if `F` maps every bilimit bicone over 
`f` to a
bilimit bicone over `F.obj ∘ f`.
-/
def isBilimitOfPreserves {f : J → C} (F : C ⥤ D) [PreservesZeroMorphisms F] [PreservesBiproduct f F]
    {b : Bicone f} (hb : b.IsBilimit) : (F.mapBicone b).IsBilimit :=
  (PreservesBiproduct.preserves hb).some

variable (J)

/-- A functor `F` preserves biproducts of shape `J` if it preserves biproducts of `f` for every
`f : J → C`. -/
/-
**CategoryTheory.Limits.PreservesBiproductsOfShape** 是 Mathlib 中的一个归纳类型，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         [inst_2 
: CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : CategoryTheory
.Limits.HasZeroMorphisms D] →             Type w₁ → (F : CategoryTheory.Functor 
C D) → [F.PreservesZeroMorphisms] → Prop
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` preserves biproducts of shape `J` if it preserves biproducts of `f
` for every
`f : J → C`.
-/
class PreservesBiproductsOfShape (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {f : J → C}, PreservesBiproduct f F

attribute [inherit_doc PreservesBiproductsOfShape] PreservesBiproductsOfShape.preserves

attribute [instance 100] PreservesBiproductsOfShape.preserves

end Bicone

/-- A functor `F` preserves finite biproducts if it preserves biproducts of shape `J`
whenever `J` is a finite type. -/
/-
**CategoryTheory.Limits.PreservesFiniteBiproducts** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         [inst_2 
: CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : CategoryTheory
.Limits.HasZeroMorphisms D] →             (F : CategoryTheory.Functor C D) → [F.
PreservesZeroMorphisms] → Prop
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` preserves finite biproducts if it preserves biproducts of shape `J
`
whenever `J` is a finite type.
-/
class PreservesFiniteBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {J : Type} [Finite J], PreservesBiproductsOfShape J F

attribute [inherit_doc PreservesFiniteBiproducts] PreservesFiniteBiproducts.preserves
attribute [instance 100] PreservesFiniteBiproducts.preserves

/-- A functor `F` preserves biproducts if it preserves biproducts of any shape `J` of size `w`.
The usual notion of preservation of biproducts is recovered by choosing `w` to be the universe
of the morphisms of `C`. -/
/-
**CategoryTheory.Limits.PreservesBiproducts** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         [inst_2 
: CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : CategoryTheory
.Limits.HasZeroMorphisms D] →             (F : CategoryTheory.Functor C D) → [F.
PreservesZeroMorphisms] → Prop
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` preserves biproducts if it preserves biproducts of any shape `J` o
f size `w`.
The usual notion of preservation of biproducts is recovered by choosing `w` to b
e the universe
of the morphisms of `C`.
-/
class PreservesBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {J : Type w₁}, PreservesBiproductsOfShape J F

attribute [inherit_doc PreservesBiproducts] PreservesBiproducts.preserves

attribute [instance 100] PreservesBiproducts.preserves

/-- Preserving biproducts at a bigger universe level implies preserving biproducts at a
smaller universe level. -/
/-
**CategoryTheory.Limits.preservesBiproducts_shrink** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：preservesBiproducts_shrink (F : C ⥤ D) [PreservesZeroMorphisms F] [Preserv
esBiproducts.{max w₁ w₂} F] : PreservesBiproducts.{w₁} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesBiproductsOfShape.preserves`：∀ {C : Type 
u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Category
Theory.Category.{v₂, u₂} D}   {inst_2 : Category…
· 使用定理 `CategoryTheory.Limits.PreservesBiproducts.preserves`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {inst_2 : Category…

--- 原说明 ---
Preserving biproducts at a bigger universe level implies preserving biproducts a
t a
smaller universe level.
-/
lemma preservesBiproducts_shrink (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBiproducts.{max w₁ w₂} F] : PreservesBiproducts.{w₁} F :=
  ⟨fun {_} =>
    ⟨fun {_} =>
      ⟨fun {b} ib =>
        ⟨((F.mapBicone b).whiskerIsBilimitIff _).toFun
          (isBilimitOfPreserves F ((b.whiskerIsBilimitIff Equiv.ulift.{w₂}).invFun ib))⟩⟩⟩⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) preservesFiniteBiproductsOfPreservesBiproducts (F : C ⥤ D)
    [PreservesZeroMorphisms F] [PreservesBiproducts.{w₁} F] : PreservesFiniteBiproducts F where
  preserves {J} _ := by let := preservesBiproducts_shrink.{0} F; infer_instance

/-- A functor `F` preserves binary biproducts of `X` and `Y` if `F` maps every bilimit bicone over
`X` and `Y` to a bilimit bicone over `F.obj X` and `F.obj Y`. -/
/-
**CategoryTheory.Limits.PreservesBinaryBiproduct** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         [inst_2 
: CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : CategoryTheory
.Limits.HasZeroMorphisms D] →             C → C → (F : CategoryTheory.Functor C 
D) → [F.PreservesZeroMorphisms] → Prop
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` preserves binary biproducts of `X` and `Y` if `F` maps every bilim
it bicone over
`X` and `Y` to a bilimit bicone over `F.obj X` and `F.obj Y`.
-/
class PreservesBinaryBiproduct (X Y : C) (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {b : BinaryBicone X Y}, b.IsBilimit → Nonempty ((F.mapBinaryBicone b).IsBilimit)

attribute [inherit_doc PreservesBinaryBiproduct] PreservesBinaryBiproduct.preserves

/-- A functor `F` preserves binary biproducts of `X` and `Y` if `F` maps every bilimit bicone over
`X` and `Y` to a bilimit bicone over `F.obj X` and `F.obj Y`. -/
/-
**CategoryTheory.Limits.isBinaryBilimitOfPreserves** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：isBinaryBilimitOfPreserves {X Y : C} (F : C ⥤ D) [PreservesZeroMorphisms F
] [PreservesBinaryBiproduct X Y F] {b : BinaryBicone X Y} (hb : b.IsBilimit) : (
F.mapBinaryBicone b).IsBilimit
参数：F : C ⥤ D；hb : b.IsBilimit。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesBinaryBiproduct.preserves`：∀ {C : Type u₁
} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTh
eory.Category.{v₂, u₂} D}   {inst_2 : Category…

--- 原说明 ---
A functor `F` preserves binary biproducts of `X` and `Y` if `F` maps every bilim
it bicone over
`X` and `Y` to a bilimit bicone over `F.obj X` and `F.obj Y`.
-/
def isBinaryBilimitOfPreserves {X Y : C} (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBinaryBiproduct X Y F] {b : BinaryBicone X Y} (hb : b.IsBilimit) :
    (F.mapBinaryBicone b).IsBilimit :=
  (PreservesBinaryBiproduct.preserves hb).some

/-- A functor `F` preserves binary biproducts if it preserves the binary biproduct of `X` and `Y`
for all `X` and `Y`. -/
/-
**CategoryTheory.Limits.PreservesBinaryBiproducts** 是 Mathlib 中的一个类，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：PreservesBinaryBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop wh
ere preserves : forall {X Y : C}, PreservesBinaryBiproduct X Y F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` preserves binary biproducts if it preserves the binary biproduct o
f `X` and `Y`
for all `X` and `Y`.
-/
class PreservesBinaryBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {X Y : C}, PreservesBinaryBiproduct X Y F := by infer_instance

attribute [inherit_doc PreservesBinaryBiproducts] PreservesBinaryBiproducts.preserves

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor that preserves biproducts of a pair preserves binary biproducts. -/
/-
**CategoryTheory.Limits.preservesBinaryBiproduct_of_preservesBiproduct** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBinaryBiproduct_of_preservesBiproduct (F : C ⥤ D) [PreservesZeroM
orphisms F] (X Y : C) [PreservesBiproduct (pairFunction X Y) F] : PreservesBinar
yBiproduct X Y F where preserves {b} hb
参数：F : C ⥤ D；X Y : C；pairFunction X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
A functor that preserves biproducts of a pair preserves binary biproducts.
-/
lemma preservesBinaryBiproduct_of_preservesBiproduct (F : C ⥤ D)
    [PreservesZeroMorphisms F] (X Y : C) [PreservesBiproduct (pairFunction X Y) F] :
    PreservesBinaryBiproduct X Y F where
  preserves {b} hb := ⟨{
      isLimit :=
        IsLimit.ofIsoLimit
            ((IsLimit.postcomposeHomEquiv (diagramIsoPair _) _).symm
              (isBilimitOfPreserves F (b.toBiconeIsBilimit.symm hb)).isLimit) <|
          Cone.ext (Iso.refl _) fun j => by
            rcases j with ⟨⟨⟩⟩ <;> simp
      isColimit :=
        IsColimit.ofIsoColimit
            ((IsColimit.precomposeInvEquiv (diagramIsoPair _) _).symm
              (isBilimitOfPreserves F (b.toBiconeIsBilimit.symm hb)).isColimit) <|
          Cocone.ext (Iso.refl _) fun j => by
            rcases j with ⟨⟨⟩⟩ <;> simp }⟩

/-- A functor that preserves biproducts of a pair preserves binary biproducts. -/
/-
**CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesBinaryBiproducts_of_preservesBiproducts (F : C ⥤ D) [PreservesZer
oMorphisms F] [PreservesBiproductsOfShape WalkingPair F] : PreservesBinaryBiprod
ucts F where preserves {X} Y
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproduct_of_preservesBiproduct`：pr
eservesBinaryBiproduct_of_preservesBiproduct (F : C ⥤ D) [PreservesZeroMorphisms
 F] (X Y : C) [PreservesBiproduct (pairFunction X Y) F] : …
· 使用定理 `CategoryTheory.Limits.PreservesBiproductsOfShape.preserves`：∀ {C : Type 
u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Category
Theory.Category.{v₂, u₂} D}   {inst_2 : Category…

--- 原说明 ---
A functor that preserves biproducts of a pair preserves binary biproducts.
-/
lemma preservesBinaryBiproducts_of_preservesBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBiproductsOfShape WalkingPair F] : PreservesBinaryBiproducts F where
  preserves {X} Y := preservesBinaryBiproduct_of_preservesBiproduct F X Y

attribute [instance 100] PreservesBinaryBiproducts.preserves

end Limits

open CategoryTheory.Limits

namespace Functor

section Bicone

variable {J : Type w₁} (F : C ⥤ D) (f : J → C) [HasBiproduct f]

section

variable [HasBiproduct (F.obj ∘ f)]

/-- As for products, any functor between categories with biproducts gives rise to a morphism
`F.obj (⨁ f) ⟶ ⨁ (F.obj ∘ f)`. -/
/-
**CategoryTheory.Functor.biproductComparison** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor`。
形式化陈述：biproductComparison : F.obj (⨁ f) ⟶ ⨁ F.obj ∘ f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As for products, any functor between categories with biproducts gives rise to a 
morphism
`F.obj (⨁ f) ⟶ ⨁ (F.obj ∘ f)`.
-/
def biproductComparison : F.obj (⨁ f) ⟶ ⨁ F.obj ∘ f :=
  biproduct.lift fun j => F.map (biproduct.π f j)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.biproductComparison_** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproductComparison_π (j : J) :
    biproductComparison F f ≫ biproduct.π _ j = F.map (biproduct.π f j) :=
  biproduct.lift_π _ _

/-- As for coproducts, any functor between categories with biproducts gives rise to a morphism
`⨁ (F.obj ∘ f) ⟶ F.obj (⨁ f)` -/
/-
**CategoryTheory.Functor.biproductComparison'** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：biproductComparison' : ⨁ F.obj ∘ f ⟶ F.obj (⨁ f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As for coproducts, any functor between categories with biproducts gives rise to 
a morphism
`⨁ (F.obj ∘ f) ⟶ F.obj (⨁ f)`
-/
def biproductComparison' : ⨁ F.obj ∘ f ⟶ F.obj (⨁ f) :=
  biproduct.desc fun j => F.map (biproduct.ι f j)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_biproductComparison' (j : J) :
    biproduct.ι _ j ≫ biproductComparison' F f = F.map (biproduct.ι f j) :=
  biproduct.ι_desc _ _

variable [PreservesZeroMorphisms F]

set_option backward.isDefEq.respectTransparency false in
/-- The composition in the opposite direction is equal to the identity if and only if `F` preserves
the biproduct, see `preservesBiproduct_of_monoBiproductComparison`. -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.biproductComparison'_comp_biproductComparison** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D] {J : Typ
e w₁}   (F : CategoryTheory.Functor C D) (f : J → C) [inst_4 : CategoryTheory.Li
mits.HasBiproduct f]   [inst_5 : CategoryTheory.Limits.HasBiproduct (F.obj ∘ f)]
 [F.PreservesZeroMorphisms],   CategoryTheory.CategoryStruct.comp (F.biproductCo
mparison' f) (F.biproductComparison f) =     CategoryTheory.CategoryStruct.id (⨁
 F.obj ∘ f)
参数：F : CategoryTheory.Functor C D；f : J → C；F.obj ∘ f；F.biproductComparison' f；F
.biproductComparison f；⨁ F.obj ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.biproductComparison_π`：biproductComparison_π (j :
 J) : biproductComparison F f ≫ biproduct.π _ j = F.map (biproduct.π f j)
· 使用定理 `CategoryTheory.Functor.ι_biproductComparison'_assoc`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π`：∀ {J : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.Functor.map_dite`：map_dite (F : C ⥤ D) {X Y : C} {P : Pro
p} [Decidable P] (f : P -> (X ⟶ Y)) (g : ¬P -> (X ⟶ Y)) : F.map (if h : P then f
 h else g h) = if h :…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The composition in the opposite direction is equal to the identity if and only i
f `F` preserves
the biproduct, see `preservesBiproduct_of_monoBiproductComparison`.
-/
theorem biproductComparison'_comp_biproductComparison :
    biproductComparison' F f ≫ biproductComparison F f = 𝟙 (⨁ F.obj ∘ f) := by
  classical
    ext
    simp [biproduct.ι_π, ← Functor.map_comp, eqToHom_map]

/-- `biproduct_comparison F f` is a split epimorphism. -/
@[simps]
/-
**CategoryTheory.Functor.splitEpiBiproductComparison** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         [inst_2 
: CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : CategoryTheory
.Limits.HasZeroMorphisms D] →             {J : Type w₁} →               (F : Cat
egoryTheory.Functor C D) →                 (f : J → C) →                   [inst
_4 : CategoryTheory.Limits.HasBiproduct f] →                     [inst_5 : Categ
oryTheory.Limits.HasBiproduct (F.obj ∘ f)] →                       [F.PreservesZ
eroMorphisms] → CategoryTheory.SplitEpi (F.biproductComparison f)
参数：F : CategoryTheory.Functor C D；f : J → C；F.obj ∘ f；F.biproductComparison f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`biproduct_comparison F f` is a split epimorphism.
-/
def splitEpiBiproductComparison : SplitEpi (biproductComparison F f) where
  section_ := biproductComparison' F f
  id := by simp
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitEpi (biproductComparison F f) :=
  IsSplitEpi.mk' (splitEpiBiproductComparison F f)

/-- `biproduct_comparison' F f` is a split monomorphism. -/
@[simps]
/-
**CategoryTheory.Functor.splitMonoBiproductComparison'** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：splitMonoBiproductComparison' : SplitMono (biproductComparison' F f) where
 retraction
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`biproduct_comparison' F f` is a split monomorphism.
-/
def splitMonoBiproductComparison' : SplitMono (biproductComparison' F f) where
  retraction := biproductComparison F f
  id := by simp
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitMono (biproductComparison' F f) :=
  IsSplitMono.mk' (splitMonoBiproductComparison' F f)

end

variable [PreservesZeroMorphisms F] [PreservesBiproduct f F]

/-
**CategoryTheory.Functor.hasBiproduct_of_preserves** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：hasBiproduct_of_preserves : HasBiproduct (F.obj ∘ f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBiproduct.mk`：∀ {J : Type w} {C : Type uC} [ins
t : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C] {F : J → C} …
-/
instance hasBiproduct_of_preserves : HasBiproduct (F.obj ∘ f) :=
  HasBiproduct.mk
    { bicone := F.mapBicone (biproduct.bicone f)
      isBilimit := isBilimitOfPreserves _ (biproduct.isBilimit _) }

/-- This instance applies more often than `hasBiproduct_of_preserves`, but the discrimination
tree key matches a lot more (since it does not look through lambdas). -/
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance applies more often than `hasBiproduct_of_preserves`, but the discr
imination
tree key matches a lot more (since it does not look through lambdas).
-/
instance (priority := low) hasBiproduct_of_preserves' : HasBiproduct fun i => F.obj (f i) :=
  HasBiproduct.mk
    { bicone := F.mapBicone (biproduct.bicone f)
      isBilimit := isBilimitOfPreserves _ (biproduct.isBilimit _) }

/-- If `F` preserves a biproduct, we get a definitionally nice isomorphism
`F.obj (⨁ f) ≅ ⨁ (F.obj ∘ f)`. -/
/-
**CategoryTheory.Functor.mapBiproduct** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：mapBiproduct : F.obj (⨁ f) ≅ ⨁ F.obj ∘ f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` preserves a biproduct, we get a definitionally nice isomorphism
`F.obj (⨁ f) ≅ ⨁ (F.obj ∘ f)`.
-/
abbrev mapBiproduct : F.obj (⨁ f) ≅ ⨁ F.obj ∘ f :=
  biproduct.uniqueUpToIso _ (isBilimitOfPreserves _ (biproduct.isBilimit _))
/-
**CategoryTheory.Functor.mapBiproduct_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：mapBiproduct_hom : (mapBiproduct F f).hom = biproduct.lift fun j => F.map 
(biproduct.π f j)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapBiproduct_hom :
    (mapBiproduct F f).hom = biproduct.lift fun j => F.map (biproduct.π f j) := rfl
/-
**CategoryTheory.Functor.mapBiproduct_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：mapBiproduct_inv : (mapBiproduct F f).inv = biproduct.desc fun j => F.map 
(biproduct.ι f j)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapBiproduct_inv :
    (mapBiproduct F f).inv = biproduct.desc fun j => F.map (biproduct.ι f j) := rfl

end Bicone

variable (F : C ⥤ D) (X Y : C) [HasBinaryBiproduct X Y]

section

variable [HasBinaryBiproduct (F.obj X) (F.obj Y)]

/-- As for products, any functor between categories with binary biproducts gives rise to a
morphism `F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y`. -/
/-
**CategoryTheory.Functor.biprodComparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：biprodComparison : F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As for products, any functor between categories with binary biproducts gives ris
e to a
morphism `F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y`.
-/
def biprodComparison : F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y :=
  biprod.lift (F.map biprod.fst) (F.map biprod.snd)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.biprodComparison_fst** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：biprodComparison_fst : biprodComparison F X Y ≫ biprod.fst = F.map biprod.
fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
theorem biprodComparison_fst : biprodComparison F X Y ≫ biprod.fst = F.map biprod.fst :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.biprodComparison_snd** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：biprodComparison_snd : biprodComparison F X Y ≫ biprod.snd = F.map biprod.
snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
theorem biprodComparison_snd : biprodComparison F X Y ≫ biprod.snd = F.map biprod.snd :=
  biprod.lift_snd _ _

/-- As for coproducts, any functor between categories with binary biproducts gives rise to a
morphism `F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y)`. -/
/-
**CategoryTheory.Functor.biprodComparison'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：biprodComparison' : F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As for coproducts, any functor between categories with binary biproducts gives r
ise to a
morphism `F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y)`.
-/
def biprodComparison' : F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y) :=
  biprod.desc (F.map biprod.inl) (F.map biprod.inr)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.inl_biprodComparison'** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：inl_biprodComparison' : biprod.inl ≫ biprodComparison' F X Y = F.map bipro
d.inl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
theorem inl_biprodComparison' : biprod.inl ≫ biprodComparison' F X Y = F.map biprod.inl :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.inr_biprodComparison'** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：inr_biprodComparison' : biprod.inr ≫ biprodComparison' F X Y = F.map bipro
d.inr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
theorem inr_biprodComparison' : biprod.inr ≫ biprodComparison' F X Y = F.map biprod.inr :=
  biprod.inr_desc _ _

variable [PreservesZeroMorphisms F]

/-- The composition in the opposite direction is equal to the identity if and only if `F` preserves
the biproduct, see `preservesBinaryBiproduct_of_monoBiprodComparison`. -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.biprodComparison'_comp_biprodComparison** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) (X Y : C) [inst_4 : CategoryTheory.Limits.HasBinaryBi
product X Y]   [inst_5 : CategoryTheory.Limits.HasBinaryBiproduct (F.obj X) (F.o
bj Y)] [F.PreservesZeroMorphisms],   CategoryTheory.CategoryStruct.comp (F.bipro
dComparison' X Y) (F.biprodComparison X Y) =     CategoryTheory.CategoryStruct.i
d (F.obj X ⊞ F.obj Y)
参数：F : CategoryTheory.Functor C D；X Y : C；F.obj X；F.obj Y；F.biprodComparison' X 
Y；F.biprodComparison X Y；F.obj X ⊞ F.obj Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.inl_biprodComparison'_assoc`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.biprodComparison_fst`：biprodComparison_fst : bipr
odComparison F X Y ≫ biprod.fst = F.map biprod.fst
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.biprodComparison_snd`：biprodComparison_snd : bipr
odComparison F X Y ≫ biprod.snd = F.map biprod.snd
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.inr_biprodComparison'_assoc`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…

--- 原说明 ---
The composition in the opposite direction is equal to the identity if and only i
f `F` preserves
the biproduct, see `preservesBinaryBiproduct_of_monoBiprodComparison`.
-/
theorem biprodComparison'_comp_biprodComparison :
    biprodComparison' F X Y ≫ biprodComparison F X Y = 𝟙 (F.obj X ⊞ F.obj Y) := by
  ext <;> simp [← Functor.map_comp]

/-- `biprodComparison F X Y` is a split epi. -/
@[simps]
/-
**CategoryTheory.Functor.splitEpiBiprodComparison** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         [inst_2 
: CategoryTheory.Limits.HasZeroMorphisms C] →           [inst_3 : CategoryTheory
.Limits.HasZeroMorphisms D] →             (F : CategoryTheory.Functor C D) →    
           (X Y : C) →                 [inst_4 : CategoryTheory.Limits.HasBinary
Biproduct X Y] →                   [inst_5 : CategoryTheory.Limits.HasBinaryBipr
oduct (F.obj X) (F.obj Y)] →                     [F.PreservesZeroMorphisms] → Ca
tegoryTheory.SplitEpi (F.biprodComparison X Y)
参数：F : CategoryTheory.Functor C D；X Y : C；F.obj X；F.obj Y；F.biprodComparison X Y
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`biprodComparison F X Y` is a split epi.
-/
def splitEpiBiprodComparison : SplitEpi (biprodComparison F X Y) where
  section_ := biprodComparison' F X Y
  id := by simp
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitEpi (biprodComparison F X Y) :=
  IsSplitEpi.mk' (splitEpiBiprodComparison F X Y)

/-- `biprodComparison' F X Y` is a split mono. -/
@[simps]
/-
**CategoryTheory.Functor.splitMonoBiprodComparison'** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：splitMonoBiprodComparison' : SplitMono (biprodComparison' F X Y) where ret
raction
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`biprodComparison' F X Y` is a split mono.
-/
def splitMonoBiprodComparison' : SplitMono (biprodComparison' F X Y) where
  retraction := biprodComparison F X Y
  id := by simp
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitMono (biprodComparison' F X Y) :=
  IsSplitMono.mk' (splitMonoBiprodComparison' F X Y)

end

variable [PreservesZeroMorphisms F] [PreservesBinaryBiproduct X Y F]

/-
**CategoryTheory.Functor.hasBinaryBiproduct_of_preserves** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：hasBinaryBiproduct_of_preserves : HasBinaryBiproduct (F.obj X) (F.obj Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.mk`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {P Q : C} (d : CategoryTh…
-/
instance hasBinaryBiproduct_of_preserves : HasBinaryBiproduct (F.obj X) (F.obj Y) :=
  HasBinaryBiproduct.mk
    { bicone := F.mapBinaryBicone (BinaryBiproduct.bicone X Y)
      isBilimit := isBinaryBilimitOfPreserves F (BinaryBiproduct.isBilimit _ _) }

/-- If `F` preserves a binary biproduct, we get a definitionally nice isomorphism
`F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y`. -/
/-
**CategoryTheory.Functor.mapBiprod** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：mapBiprod : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` preserves a binary biproduct, we get a definitionally nice isomorphism
`F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y`.
-/
abbrev mapBiprod : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y :=
  biprod.uniqueUpToIso _ _ (isBinaryBilimitOfPreserves F (BinaryBiproduct.isBilimit _ _))
/-
**CategoryTheory.Functor.mapBiprod_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：mapBiprod_hom : (mapBiprod F X Y).hom = biprod.lift (F.map biprod.fst) (F.
map biprod.snd)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapBiprod_hom : (mapBiprod F X Y).hom = biprod.lift (F.map biprod.fst) (F.map biprod.snd) :=
  rfl
/-
**CategoryTheory.Functor.mapBiprod_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：mapBiprod_inv : (mapBiprod F X Y).inv = biprod.desc (F.map biprod.inl) (F.
map biprod.inr)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapBiprod_inv : (mapBiprod F X Y).inv = biprod.desc (F.map biprod.inl) (F.map biprod.inr) :=
  rfl

end Functor

namespace Limits

variable (F : C ⥤ D) [PreservesZeroMorphisms F]

section Bicone

variable {J : Type w₁} (f : J → C) [HasBiproduct f] [PreservesBiproduct f F] {W : C}

/-
**CategoryTheory.Limits.biproduct.map_lift_mapBiprod** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.biproduct`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] {J : Type w₁} (f 
: J → C)   [inst_5 : CategoryTheory.Limits.HasBiproduct f] [inst_6 : CategoryThe
ory.Limits.PreservesBiproduct f F] {W : C}   (g : (j : J) → W ⟶ f j),   Category
Theory.CategoryStruct.comp (F.map (CategoryTheory.Limits.biproduct.lift g)) (F.m
apBiproduct f).hom =     CategoryTheory.Limits.biproduct.lift fun j => F.map (g 
j)
参数：F : CategoryTheory.Functor C D；f : J → C；g : (j : J) → W ⟶ f j；F.map (Categor
yTheory.Limits.biproduct.lift g)；F.mapBiproduct f；g j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Functor.hasBiproduct_of_preserves'`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.map_lift_mapBiprod (g : ∀ j, W ⟶ f j) :
    F.map (biproduct.lift g) ≫ (F.mapBiproduct f).hom = biproduct.lift fun j => F.map (g j) := by
  ext j
  dsimp only [Function.comp_def]
  simp only [mapBiproduct_hom, Category.assoc, biproduct.lift_π, ← F.map_comp]
/-
**CategoryTheory.Limits.biproduct.mapBiproduct_inv_map_desc** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.biproduct`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] {J : Type w₁} (f 
: J → C)   [inst_5 : CategoryTheory.Limits.HasBiproduct f] [inst_6 : CategoryThe
ory.Limits.PreservesBiproduct f F] {W : C}   (g : (j : J) → f j ⟶ W),   Category
Theory.CategoryStruct.comp (F.mapBiproduct f).inv (F.map (CategoryTheory.Limits.
biproduct.desc g)) =     CategoryTheory.Limits.biproduct.desc fun j => F.map (g 
j)
参数：F : CategoryTheory.Functor C D；f : J → C；g : (j : J) → f j ⟶ W；F.mapBiproduct
 f；F.map (CategoryTheory.Limits.biproduct.desc g)；g j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Functor.hasBiproduct_of_preserves'`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.mapBiproduct_inv_map_desc (g : ∀ j, f j ⟶ W) :
    (F.mapBiproduct f).inv ≫ F.map (biproduct.desc g) = biproduct.desc fun j => F.map (g j) := by
  ext j
  dsimp only [Function.comp_def]
  simp only [mapBiproduct_inv, ← Category.assoc, biproduct.ι_desc, ← F.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.biproduct.mapBiproduct_hom_desc** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.biproduct`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] {J : Type w₁} (f 
: J → C)   [inst_5 : CategoryTheory.Limits.HasBiproduct f] [inst_6 : CategoryThe
ory.Limits.PreservesBiproduct f F] {W : C}   (g : (j : J) → f j ⟶ W),   Category
Theory.CategoryStruct.comp (F.mapBiproduct f).hom       (CategoryTheory.Limits.b
iproduct.desc fun j => F.map (g j)) =     F.map (CategoryTheory.Limits.biproduct
.desc g)
参数：F : CategoryTheory.Functor C D；f : J → C；g : (j : J) → f j ⟶ W；F.mapBiproduct
 f；CategoryTheory.Limits.biproduct.desc fun j => F.map (g j)；CategoryTheory.Limi
ts.biproduct.desc g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.hasBiproduct_of_preserves'`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.biproduct.mapBiproduct_inv_map_desc`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
theorem biproduct.mapBiproduct_hom_desc (g : ∀ j, f j ⟶ W) :
    ((F.mapBiproduct f).hom ≫ biproduct.desc fun j => F.map (g j)) = F.map (biproduct.desc g) := by
  rw [← biproduct.mapBiproduct_inv_map_desc, Iso.hom_inv_id_assoc]

end Bicone

section BinaryBicone

variable (X Y : C) [HasBinaryBiproduct X Y] [PreservesBinaryBiproduct X Y F] {W : C}

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.biprod.map_lift_mapBiprod** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] (X Y : C)   [inst
_5 : CategoryTheory.Limits.HasBinaryBiproduct X Y]   [inst_6 : CategoryTheory.Li
mits.PreservesBinaryBiproduct X Y F] {W : C} (f : W ⟶ X) (g : W ⟶ Y),   Category
Theory.CategoryStruct.comp (F.map (CategoryTheory.Limits.biprod.lift f g)) (F.ma
pBiprod X Y).hom =     CategoryTheory.Limits.biprod.lift (F.map f) (F.map g)
参数：F : CategoryTheory.Functor C D；X Y : C；f : W ⟶ X；g : W ⟶ Y；F.map (CategoryThe
ory.Limits.biprod.lift f g)；F.mapBiprod X Y；F.map f；F.map g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
theorem biprod.map_lift_mapBiprod (f : W ⟶ X) (g : W ⟶ Y) :
    F.map (biprod.lift f g) ≫ (F.mapBiprod X Y).hom = biprod.lift (F.map f) (F.map g) := by
  ext <;> simp [mapBiprod, ← F.map_comp]
/-
**CategoryTheory.Limits.biprod.lift_mapBiprod** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.biprod`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] (X Y : C)   [inst
_5 : CategoryTheory.Limits.HasBinaryBiproduct X Y]   [inst_6 : CategoryTheory.Li
mits.PreservesBinaryBiproduct X Y F] {W : C} (f : W ⟶ X) (g : W ⟶ Y),   Category
Theory.CategoryStruct.comp (CategoryTheory.Limits.biprod.lift (F.map f) (F.map g
)) (F.mapBiprod X Y).inv =     F.map (CategoryTheory.Limits.biprod.lift f g)
参数：F : CategoryTheory.Functor C D；X Y : C；f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Lim
its.biprod.lift (F.map f) (F.map g)；F.mapBiprod X Y；CategoryTheory.Limits.biprod
.lift f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.biprod.map_lift_mapBiprod`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem biprod.lift_mapBiprod (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift (F.map f) (F.map g) ≫ (F.mapBiprod X Y).inv = F.map (biprod.lift f g) := by
  rw [← biprod.map_lift_mapBiprod, Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.biprod.mapBiprod_inv_map_desc** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] (X Y : C)   [inst
_5 : CategoryTheory.Limits.HasBinaryBiproduct X Y]   [inst_6 : CategoryTheory.Li
mits.PreservesBinaryBiproduct X Y F] {W : C} (f : X ⟶ W) (g : Y ⟶ W),   Category
Theory.CategoryStruct.comp (F.mapBiprod X Y).inv (F.map (CategoryTheory.Limits.b
iprod.desc f g)) =     CategoryTheory.Limits.biprod.desc (F.map f) (F.map g)
参数：F : CategoryTheory.Functor C D；X Y : C；f : X ⟶ W；g : Y ⟶ W；F.mapBiprod X Y；F.
map (CategoryTheory.Limits.biprod.desc f g)；F.map f；F.map g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
theorem biprod.mapBiprod_inv_map_desc (f : X ⟶ W) (g : Y ⟶ W) :
    (F.mapBiprod X Y).inv ≫ F.map (biprod.desc f g) = biprod.desc (F.map f) (F.map g) := by
  ext <;> simp [mapBiprod, ← F.map_comp]
/-
**CategoryTheory.Limits.biprod.mapBiprod_hom_desc** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.biprod`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] (X Y : C)   [inst
_5 : CategoryTheory.Limits.HasBinaryBiproduct X Y]   [inst_6 : CategoryTheory.Li
mits.PreservesBinaryBiproduct X Y F] {W : C} (f : X ⟶ W) (g : Y ⟶ W),   Category
Theory.CategoryStruct.comp (F.mapBiprod X Y).hom (CategoryTheory.Limits.biprod.d
esc (F.map f) (F.map g)) =     F.map (CategoryTheory.Limits.biprod.desc f g)
参数：F : CategoryTheory.Functor C D；X Y : C；f : X ⟶ W；g : Y ⟶ W；F.mapBiprod X Y；Ca
tegoryTheory.Limits.biprod.desc (F.map f) (F.map g)；CategoryTheory.Limits.biprod
.desc f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.biprod.mapBiprod_inv_map_desc`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
theorem biprod.mapBiprod_hom_desc (f : X ⟶ W) (g : Y ⟶ W) :
    (F.mapBiprod X Y).hom ≫ biprod.desc (F.map f) (F.map g) = F.map (biprod.desc f g) := by
  rw [← biprod.mapBiprod_inv_map_desc, Iso.hom_inv_id_assoc]

end BinaryBicone

end Limits

end HasZeroMorphisms

end CategoryTheory

