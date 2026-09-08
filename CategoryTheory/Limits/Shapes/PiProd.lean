/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Products
/-!

# A product as a binary product

We write a product indexed by `I` as a binary product of the products indexed by a subset of `I`
and its complement.

-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C I : Type*} [Category* C] {X Y : I → C}
  (f : (i : I) → X i ⟶ Y i) (P : I → Prop)
  [HasProduct X] [HasProduct Y]
  [HasProduct (fun (i : {x : I // P x}) ↦ X i.val)]
  [HasProduct (fun (i : {x : I // ¬ P x}) ↦ X i.val)]
  [HasProduct (fun (i : {x : I // P x}) ↦ Y i.val)]
  [HasProduct (fun (i : {x : I // ¬ P x}) ↦ Y i.val)]

variable (X) in
/--
The projection maps of a product to the products indexed by a subset and its complement, as a
binary fan.
-/
/-
**CategoryTheory.Limits.Pi.binaryFanOfProp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Pi`。
形式化陈述：{C : Type u_1} →   {I : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       (X : I → C) →         (P : I → Prop) →           [CategoryTh
eory.Limits.HasProduct X] →             [inst_2 : CategoryTheory.Limits.HasProdu
ct fun i => X ↑i] →               [inst_3 : CategoryTheory.Limits.HasProduct fun
 i => X ↑i] →                 CategoryTheory.Limits.BinaryFan (∏ᶜ fun i => X ↑i)
 (∏ᶜ fun i => X ↑i)
参数：X : I → C；P : I → Prop；∏ᶜ fun i => X ↑i；∏ᶜ fun i => X ↑i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection maps of a product to the products indexed by a subset and its com
plement, as a
binary fan.
-/
noncomputable def Pi.binaryFanOfProp : BinaryFan (∏ᶜ (fun (i : {x : I // P x}) ↦ X i.val))
    (∏ᶜ (fun (i : {x : I // ¬ P x}) ↦ X i.val)) :=
  BinaryFan.mk (P := ∏ᶜ X) (Pi.map' Subtype.val fun _ ↦ 𝟙 _)
    (Pi.map' Subtype.val fun _ ↦ 𝟙 _)

set_option backward.isDefEq.respectTransparency false in
variable (X) in
/--
A product indexed by `I` is a binary product of the products indexed by a subset of `I` and its
complement.
-/
/-
**CategoryTheory.Limits.Pi.binaryFanOfPropIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.Pi`。
形式化陈述：{C : Type u_1} →   {I : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       (X : I → C) →         (P : I → Prop) →           [inst_1 : C
ategoryTheory.Limits.HasProduct X] →             [inst_2 : CategoryTheory.Limits
.HasProduct fun i => X ↑i] →               [inst_3 : CategoryTheory.Limits.HasPr
oduct fun i => X ↑i] →                 [(i : I) → Decidable (P i)] →            
       CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.Pi.binaryFanOfProp X
 P)
参数：X : I → C；P : I → Prop；i : I；P i；CategoryTheory.Limits.Pi.binaryFanOfProp X P
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product indexed by `I` is a binary product of the products indexed by a subset
 of `I` and its
complement.
-/
noncomputable def Pi.binaryFanOfPropIsLimit [∀ i, Decidable (P i)] :
    IsLimit (Pi.binaryFanOfProp X P) :=
  BinaryFan.isLimitMk
    (fun s ↦ Pi.lift fun b ↦ if h : P b then
      s.π.app ⟨WalkingPair.left⟩ ≫ Pi.π (fun (i : {x : I // P x}) ↦ X i.val) ⟨b, h⟩ else
      s.π.app ⟨WalkingPair.right⟩ ≫ Pi.π (fun (i : {x : I // ¬ P x}) ↦ X i.val) ⟨b, h⟩)
    (by aesop) (by aesop)
    (fun _ _ h₁ h₂ ↦ Pi.hom_ext _ _ fun b ↦ by
      by_cases h : P b
      · simp [← h₁, dif_pos h]
      · simp [← h₂, dif_neg h])
/-
**CategoryTheory.Limits.hasBinaryProduct_of_products** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：hasBinaryProduct_of_products : HasBinaryProduct (∏ᶜ (fun (i : {x : I // P 
x}) => X i.val)) (∏ᶜ (fun (i : {x : I // ¬ P x}) => X i.val))
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasBinaryProduct_of_products : HasBinaryProduct (∏ᶜ (fun (i : {x : I // P x}) ↦ X i.val))
    (∏ᶜ (fun (i : {x : I // ¬ P x}) ↦ X i.val)) := by
  classical exact ⟨Pi.binaryFanOfProp X P, Pi.binaryFanOfPropIsLimit X P⟩

attribute [local instance] hasBinaryProduct_of_products

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.Pi.map_eq_prod_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.Pi`。
形式化陈述：∀ {C : Type u_1} {I : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C] {X Y : I → C} (f : (i : I) → X i ⟶ Y i)   (P : I → Prop) [inst_1 : CategoryT
heory.Limits.HasProduct X] [inst_2 : CategoryTheory.Limits.HasProduct Y]   [inst
_3 : CategoryTheory.Limits.HasProduct fun i => X ↑i] [inst_4 : CategoryTheory.Li
mits.HasProduct fun i => X ↑i]   [inst_5 : CategoryTheory.Limits.HasProduct fun 
i => Y ↑i] [inst_6 : CategoryTheory.Limits.HasProduct fun i => Y ↑i]   [inst_7 :
 (i : I) → Decidable (P i)],   CategoryTheory.Limits.Pi.map f =     CategoryTheo
ry.CategoryStruct.comp       ((CategoryTheory.Limits.Pi.binaryFanOfPropIsLimit X
 P).conePointUniqueUpToIso           (CategoryTheory.Limits.prodIsProd (∏ᶜ fun i
 => X ↑i) (∏ᶜ fun i => X ↑i))).hom       (CategoryTheory.CategoryStruct.comp    
     (CategoryTheory.Limits.prod.map (CategoryTheory.Limits.Pi.map fun i => f ↑i
)           (CategoryTheory.Limits.Pi.map fun i => f ↑i))         ((CategoryTheo
ry.Limits.Pi.binaryFanOfPropIsLimit Y P).conePointUniqueUpToIso             (Cat
egoryTheory.Limits.prodIsProd (∏ᶜ fun i => Y ↑i) (∏ᶜ fun i => Y ↑i))).inv)
参数：f : (i : I) → X i ⟶ Y i；P : I → Prop；i : I；P i；(CategoryTheory.Limits.Pi.bina
ryFanOfPropIsLimit X P).conePointUniqueUpToIso           (CategoryTheory.Limits.
prodIsProd (∏ᶜ fun i => X ↑i) (∏ᶜ fun i => X ↑i))；CategoryTheory.CategoryStruct.
comp         (CategoryTheory.Limits.prod.map (CategoryTheory.Limits.Pi.map fun i
 => f ↑i)           (CategoryTheory.Limits.Pi.map fun i => f ↑i))         ((Cate
goryTheory.Limits.Pi.binaryFanOfPropIsLimit Y P).conePointUniqueUpToIso         
    (CategoryTheory.Limits.prodIsProd (∏ᶜ fun i => Y ↑i) (∏ᶜ fun i => Y ↑i))).in
v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasBinaryProduct_of_products`：hasBinaryProduct_of_
products : HasBinaryProduct (∏ᶜ (fun (i : {x : I // P x}) => X i.val)) (∏ᶜ (fun 
(i : {x : I // ¬ P x}) => X i.val))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.IsLimit.uniqueUpToIso_hom`：∀ {J : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Cate
gory.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Cone.forget_map`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, 
u₃} C]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsLimit.liftConeMorphism_hom`：∀ {J : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.C
ategory.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Cone.ext_hom_hom`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃,
 u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.Pi.map'_comp_π`：∀ {β : Type w} {α : Type w₂} {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C}   [ins
t_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Pi.map_π`：∀ {β : Type w} {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] [inst_2 …
· 使用定理 `CategoryTheory.Limits.Pi.map'_comp_π_assoc`：∀ {β : Type w} {α : Type w₂}
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C} 
  [inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.map_eq_prod_map [∀ i, Decidable (P i)] : Pi.map f =
    ((Pi.binaryFanOfPropIsLimit X P).conePointUniqueUpToIso (prodIsProd _ _)).hom ≫
      prod.map (Pi.map (fun (i : {x : I // P x}) ↦ f i.val))
      (Pi.map (fun (i : {x : I // ¬ P x}) ↦ f i.val)) ≫
        ((Pi.binaryFanOfPropIsLimit Y P).conePointUniqueUpToIso (prodIsProd _ _)).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  dsimp only [IsLimit.conePointUniqueUpToIso, binaryFanOfProp, prodIsProd]
  cat_disch

end CategoryTheory.Limits

