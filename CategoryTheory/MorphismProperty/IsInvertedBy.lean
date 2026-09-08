/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Morphism properties that are inverted by a functor

In this file, we introduce the predicate `P.IsInvertedBy F` which expresses
that the morphisms satisfying `P : MorphismProperty C` are mapped to
isomorphisms by a functor `F : C ⥤ D`.

This is used in the localization of categories API (folder `CategoryTheory.Localization`).

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- If `P : MorphismProperty C` and `F : C ⥤ D`, then
`P.IsInvertedBy F` means that all morphisms in `P` are mapped by `F`
to isomorphisms in `D`. -/
/-
**CategoryTheory.MorphismProperty.IsInvertedBy** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：IsInvertedBy (P : MorphismProperty C) (F : C ⥤ D) : Prop
参数：P : MorphismProperty C；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P : MorphismProperty C` and `F : C ⥤ D`, then
`P.IsInvertedBy F` means that all morphisms in `P` are mapped by `F`
to isomorphisms in `D`.
-/
def IsInvertedBy (P : MorphismProperty C) (F : C ⥤ D) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (_ : P f), IsIso (F.map f)

namespace IsInvertedBy

/-
**CategoryTheory.MorphismProperty.IsInvertedBy.of_le** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MorphismProperty.IsInvertedBy`。
形式化陈述：of_le (P Q : MorphismProperty C) (F : C ⥤ D) (hQ : Q.IsInvertedBy F) (h : 
P <= Q) : P.IsInvertedBy F
参数：P Q : MorphismProperty C；F : C ⥤ D；hQ : Q.IsInvertedBy F；h : P <= Q。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_le (P Q : MorphismProperty C) (F : C ⥤ D) (hQ : Q.IsInvertedBy F) (h : P ≤ Q) :
    P.IsInvertedBy F :=
  fun _ _ _ hf => hQ _ (h _ hf)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.IsInvertedBy.of_comp** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MorphismProperty.IsInvertedBy`。
形式化陈述：of_comp {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] (W
 : MorphismProperty C₁) (F : C₁ ⥤ C₂) (hF : W.IsInvertedBy F) (G : C₂ ⥤ C₃) : W.
IsInvertedBy (F ⋙ G)
参数：W : MorphismProperty C₁；F : C₁ ⥤ C₂；hF : W.IsInvertedBy F；G : C₂ ⥤ C₃。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_comp {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (W : MorphismProperty C₁) (F : C₁ ⥤ C₂) (hF : W.IsInvertedBy F) (G : C₂ ⥤ C₃) :
    W.IsInvertedBy (F ⋙ G) := fun X Y f hf => by
  have := hF f hf
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.IsInvertedBy.op** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MorphismProperty.IsInvertedBy`。
形式化陈述：op {W : MorphismProperty C} {L : C ⥤ D} (h : W.IsInvertedBy L) : W.op.IsIn
vertedBy L.op
参数：h : W.IsInvertedBy L。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op {W : MorphismProperty C} {L : C ⥤ D} (h : W.IsInvertedBy L) : W.op.IsInvertedBy L.op :=
  fun X Y f hf => by
  have := h f.unop hf
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.IsInvertedBy.rightOp** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MorphismProperty.IsInvertedBy`。
形式化陈述：rightOp {W : MorphismProperty C} {L : Cᵒᵖ ⥤ D} (h : W.op.IsInvertedBy L) :
 W.IsInvertedBy L.rightOp
参数：h : W.op.IsInvertedBy L。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightOp {W : MorphismProperty C} {L : Cᵒᵖ ⥤ D} (h : W.op.IsInvertedBy L) :
    W.IsInvertedBy L.rightOp := fun X Y f hf => by
  have := h f.op hf
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.IsInvertedBy.leftOp** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MorphismProperty.IsInvertedBy`。
形式化陈述：leftOp {W : MorphismProperty C} {L : C ⥤ Dᵒᵖ} (h : W.IsInvertedBy L) : W.o
p.IsInvertedBy L.leftOp
参数：h : W.IsInvertedBy L。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftOp {W : MorphismProperty C} {L : C ⥤ Dᵒᵖ} (h : W.IsInvertedBy L) :
    W.op.IsInvertedBy L.leftOp := fun X Y f hf => by
  have := h f.unop hf
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.IsInvertedBy.unop** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MorphismProperty.IsInvertedBy`。
形式化陈述：unop {W : MorphismProperty C} {L : Cᵒᵖ ⥤ Dᵒᵖ} (h : W.op.IsInvertedBy L) : 
W.IsInvertedBy L.unop
参数：h : W.op.IsInvertedBy L。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop {W : MorphismProperty C} {L : Cᵒᵖ ⥤ Dᵒᵖ} (h : W.op.IsInvertedBy L) :
    W.IsInvertedBy L.unop := fun X Y f hf => by
  have := h f.op hf
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.IsInvertedBy.prod** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty.IsInvertedBy`。
形式化陈述：prod {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] {W₁ : MorphismProperty 
C₁} {W₂ : MorphismProperty C₂} {E₁ E₂ : Type*} [Category* E₁] [Category* E₂] {F₁
 : C₁ ⥤ E₁} {F₂ : C₂ ⥤ E₂} (h₁ : W₁.IsInvertedBy F₁) (h₂ : W₂.IsInvertedBy F₂) :
 (W₁.prod W₂).IsInvertedBy (F₁.prod F₂)
参数：h₁ : W₁.IsInvertedBy F₁；h₂ : W₂.IsInvertedBy F₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isIso_prod_iff`：isIso_prod_iff {P Q : C} {S T : D} {f : (
P, S) ⟶ (Q, T)} : IsIso f ↔ IsIso f.1 ∧ IsIso f.2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma prod {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
    {E₁ E₂ : Type*} [Category* E₁] [Category* E₂] {F₁ : C₁ ⥤ E₁} {F₂ : C₂ ⥤ E₂}
    (h₁ : W₁.IsInvertedBy F₁) (h₂ : W₂.IsInvertedBy F₂) :
    (W₁.prod W₂).IsInvertedBy (F₁.prod F₂) := fun _ _ f hf => by
  rw [isIso_prod_iff]
  exact ⟨h₁ _ hf.1, h₂ _ hf.2⟩
/-
**CategoryTheory.MorphismProperty.IsInvertedBy.pi** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty.IsInvertedBy`。
形式化陈述：pi {J : Type w} {C : J -> Type u} {D : J -> Type u'} [forall j, Category.{
v} (C j)] [forall j, Category.{v'} (D j)] (W : forall j, MorphismProperty (C j))
 (F : forall j, C j ⥤ D j) (hF : forall j, (W j).IsInvertedBy (F j)) : (Morphism
Property.pi W).IsInvertedBy (Functor.pi F)
参数：C j；D j；W : forall j, MorphismProperty (C j)；F : forall j, C j ⥤ D j；hF : for
all j, (W j).IsInvertedBy (F j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isIso_pi_iff`：isIso_pi_iff {X Y : forall i, C i} (f : X ⟶
 Y) : IsIso f ↔ forall i, IsIso (f i)
-/
lemma pi {J : Type w} {C : J → Type u} {D : J → Type u'}
    [∀ j, Category.{v} (C j)] [∀ j, Category.{v'} (D j)]
    (W : ∀ j, MorphismProperty (C j)) (F : ∀ j, C j ⥤ D j)
    (hF : ∀ j, (W j).IsInvertedBy (F j)) :
    (MorphismProperty.pi W).IsInvertedBy (Functor.pi F) := by
  intro _ _ f hf
  rw [isIso_pi_iff]
  intro j
  exact hF j _ (hf j)

end IsInvertedBy

/-- The full subcategory of `C ⥤ D` consisting of functors inverting morphisms in `W` -/
/-
**CategoryTheory.MorphismProperty.FunctorsInverting** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：FunctorsInverting (W : MorphismProperty C) (D : Type*) [Category* D]
参数：W : MorphismProperty C；D : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subcategory of `C ⥤ D` consisting of functors inverting morphisms in `W
`
-/
def FunctorsInverting (W : MorphismProperty C) (D : Type*) [Category* D] :=
  ObjectProperty.FullSubcategory fun F : C ⥤ D => W.IsInvertedBy F

@[ext]
/-
**CategoryTheory.MorphismProperty.FunctorsInverting.ext** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.MorphismProperty.FunctorsInverting`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {W : CategoryTheory.MorphismPropert
y C} {F₁ F₂ : W.FunctorsInverting D}, F₁.obj = F₂.obj → F₁ = F₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma FunctorsInverting.ext {W : MorphismProperty C} {F₁ F₂ : FunctorsInverting W D}
    (h : F₁.obj = F₂.obj) : F₁ = F₂ := by
  cases F₁
  cases F₂
  subst h
  rfl
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (W : MorphismProperty C) (D : Type*) [Category* D] : Category (FunctorsInverting W D) :=
  ObjectProperty.FullSubcategory.category _

@[simp]
/-
**CategoryTheory.MorphismProperty.FunctorsInverting.id_hom** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.MorphismProperty.FunctorsInverting`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {W : CategoryTheory.MorphismPropert
y C} (F : W.FunctorsInverting D),   (CategoryTheory.CategoryStruct.id F).hom = C
ategoryTheory.CategoryStruct.id F.obj
参数：F : W.FunctorsInverting D；CategoryTheory.CategoryStruct.id F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FunctorsInverting.id_hom
    {W : MorphismProperty C} (F : FunctorsInverting W D) :
    InducedCategory.Hom.hom (𝟙 F) = 𝟙 _ := rfl

@[simp, reassoc]
/-
**CategoryTheory.MorphismProperty.FunctorsInverting.comp_hom** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.MorphismProperty.FunctorsInverting`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {W : CategoryTheory.MorphismPropert
y C} {F₁ F₂ F₃ : W.FunctorsInverting D} (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃),   (Category
Theory.CategoryStruct.comp f g).hom = CategoryTheory.CategoryStruct.comp f.hom g
.hom
参数：f : F₁ ⟶ F₂；g : F₂ ⟶ F₃；CategoryTheory.CategoryStruct.comp f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FunctorsInverting.comp_hom
    {W : MorphismProperty C} {F₁ F₂ F₃ : FunctorsInverting W D}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[ext]
/-
**CategoryTheory.MorphismProperty.FunctorsInverting.hom_ext** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.MorphismProperty.FunctorsInverting`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {W : CategoryTheory.MorphismPropert
y C} {F₁ F₂ : W.FunctorsInverting D} {α β : F₁ ⟶ F₂}, α.hom.app = β.hom.app → α 
= β
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
-/
lemma FunctorsInverting.hom_ext {W : MorphismProperty C} {F₁ F₂ : FunctorsInverting W D}
    {α β : F₁ ⟶ F₂} (h : α.hom.app = β.hom.app) : α = β :=
  ObjectProperty.hom_ext _ (NatTrans.ext h)

/-- A constructor for `W.FunctorsInverting D` -/
/-
**CategoryTheory.MorphismProperty.FunctorsInverting.mk** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.MorphismProperty.FunctorsInverting`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W : Cate
goryTheory.MorphismProperty C} →       {D : Type u_1} →         [inst_1 : Catego
ryTheory.Category.{v_1, u_1} D] →           (F : CategoryTheory.Functor C D) → W
.IsInvertedBy F → W.FunctorsInverting D
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for `W.FunctorsInverting D`
-/
def FunctorsInverting.mk {W : MorphismProperty C} {D : Type*} [Category* D] (F : C ⥤ D)
    (hF : W.IsInvertedBy F) : W.FunctorsInverting D :=
  ⟨F, hF⟩
/-
**CategoryTheory.MorphismProperty.IsInvertedBy.iff_of_iso** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.MorphismProperty.IsInvertedBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   (W : CategoryTheory.MorphismPropert
y C) {F₁ F₂ : CategoryTheory.Functor C D} (e : F₁ ≅ F₂),   W.IsInvertedBy F₁ ↔ W
.IsInvertedBy F₂
参数：W : CategoryTheory.MorphismProperty C；e : F₁ ≅ F₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CategoryTheory.NatIso.isIso_map_iff`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F₁ F₂ : CategoryT…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsInvertedBy.iff_of_iso (W : MorphismProperty C) {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) :
    W.IsInvertedBy F₁ ↔ W.IsInvertedBy F₂ := by
  dsimp [IsInvertedBy]
  simp only [NatIso.isIso_map_iff e]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.MorphismProperty.IsInvertedBy.isoClosure_iff** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.MorphismProperty.IsInvertedBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   (W : CategoryTheory.MorphismPropert
y C) (F : CategoryTheory.Functor C D),   W.isoClosure.IsInvertedBy F ↔ W.IsInver
tedBy F
参数：W : CategoryTheory.MorphismProperty C；F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.le_isoClosure`：le_isoClosure (P : Morphi
smProperty C) : P <= P.isoClosure
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Arrow.iso_w'`：iso_w' {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z
} (e : Arrow.mk f ≅ Arrow.mk g) : g = e.inv.left ≫ f ≫ e.hom.right
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Arrow.isIso_right`：∀ {T : Type u} [inst : CategoryTheory.
Category.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory
.IsIso sq], CategoryTh…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma IsInvertedBy.isoClosure_iff (W : MorphismProperty C) (F : C ⥤ D) :
    W.isoClosure.IsInvertedBy F ↔ W.IsInvertedBy F := by
  constructor
  · intro h X Y f hf
    exact h _ (W.le_isoClosure _ hf)
  · intro h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    simp only [Arrow.iso_w' e, F.map_comp]
    have := h _ hf'
    infer_instance

@[simp]
/-
**CategoryTheory.MorphismProperty.IsInvertedBy.iff_comp** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.MorphismProperty.IsInvertedBy`。
形式化陈述：∀ {C₁ : Type u_1} {C₂ : Type u_2} {C₃ : Type u_3} [inst : CategoryTheory.C
ategory.{v_1, u_1} C₁]   [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] [inst_
2 : CategoryTheory.Category.{v_3, u_3} C₃]   (W : CategoryTheory.MorphismPropert
y C₁) (F : CategoryTheory.Functor C₁ C₂) (G : CategoryTheory.Functor C₂ C₃)   [G
.ReflectsIsomorphisms], W.IsInvertedBy (F.comp G) ↔ W.IsInvertedBy F
参数：W : CategoryTheory.MorphismProperty C₁；F : CategoryTheory.Functor C₁ C₂；G : C
ategoryTheory.Functor C₂ C₃；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.of_comp`：of_comp {C₁ C₂ C₃ 
: Type*} [Category* C₁] [Category* C₂] [Category* C₃] (W : MorphismProperty C₁) 
(F : C₁ ⥤ C₂) (hF : W.IsInvertedBy F) (G :…
-/
lemma IsInvertedBy.iff_comp {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (W : MorphismProperty C₁) (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [G.ReflectsIsomorphisms] :
    W.IsInvertedBy (F ⋙ G) ↔ W.IsInvertedBy F := by
  constructor
  · intro h X Y f hf
    have : IsIso (G.map (F.map f)) := h _ hf
    exact isIso_of_reflects_iso (F.map f) G
  · intro hF
    exact IsInvertedBy.of_comp W F hF G
/-
**CategoryTheory.MorphismProperty.IsInvertedBy.iff_le_inverseImage_isomorphisms*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsInvertedBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   (W : CategoryTheory.MorphismPropert
y C) (F : CategoryTheory.Functor C D),   W.IsInvertedBy F ↔ W ≤ (CategoryTheory.
MorphismProperty.isomorphisms D).inverseImage F
参数：W : CategoryTheory.MorphismProperty C；F : CategoryTheory.Functor C D；Category
Theory.MorphismProperty.isomorphisms D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsInvertedBy.iff_le_inverseImage_isomorphisms (W : MorphismProperty C) (F : C ⥤ D) :
    W.IsInvertedBy F ↔ W ≤ (isomorphisms D).inverseImage F := Iff.rfl
/-
**CategoryTheory.MorphismProperty.IsInvertedBy.iff_map_le_isomorphisms** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsInvertedBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   (W : CategoryTheory.MorphismPropert
y C) (F : CategoryTheory.Functor C D),   W.IsInvertedBy F ↔ W.map F ≤ CategoryTh
eory.MorphismProperty.isomorphisms D
参数：W : CategoryTheory.MorphismProperty C；F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.iff_le_inverseImage_isomorp
hisms`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [i
nst_1 : CategoryTheory.Category.{v', u'} D]   (W : CategoryTheory.M…
· 使用引理 `CategoryTheory.MorphismProperty.map_le_iff`：map_le_iff (P : MorphismProp
erty C) {F : C ⥤ D} (Q : MorphismProperty D) [RespectsIso Q] : P.map F <= Q ↔ P 
<= Q.inverseImage F
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsInvertedBy.iff_map_le_isomorphisms (W : MorphismProperty C) (F : C ⥤ D) :
    W.IsInvertedBy F ↔ W.map F ≤ isomorphisms D := by
  rw [iff_le_inverseImage_isomorphisms, map_le_iff]
/-
**CategoryTheory.MorphismProperty.IsInvertedBy.map_iff** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MorphismProperty.IsInvertedBy`。
形式化陈述：∀ {C₁ : Type u_1} {C₂ : Type u_2} {C₃ : Type u_3} [inst : CategoryTheory.C
ategory.{v_1, u_1} C₁]   [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] [inst_
2 : CategoryTheory.Category.{v_3, u_3} C₃]   (W : CategoryTheory.MorphismPropert
y C₁) (F : CategoryTheory.Functor C₁ C₂) (G : CategoryTheory.Functor C₂ C₃),   (
W.map F).IsInvertedBy G ↔ W.IsInvertedBy (F.comp G)
参数：W : CategoryTheory.MorphismProperty C₁；F : CategoryTheory.Functor C₁ C₂；G : C
ategoryTheory.Functor C₂ C₃；W.map F；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.MorphismProperty.map_map`：map_map (P : MorphismProperty C
) (F : C ⥤ D) {E : Type*} [Category* E] (G : D ⥤ E) : (P.map F).map G = P.map (F
 ⋙ G)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsInvertedBy.map_iff {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (W : MorphismProperty C₁) (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) :
    (W.map F).IsInvertedBy G ↔ W.IsInvertedBy (F ⋙ G) := by
  simp only [IsInvertedBy.iff_map_le_isomorphisms, map_map]
/-
**CategoryTheory.MorphismProperty.isInvertedBy_isomorphisms** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isInvertedBy_isomorphisms (F : C ⥤ D) : (isomorphisms C).IsInvertedBy F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isInvertedBy_isomorphisms (F : C ⥤ D) : (isomorphisms C).IsInvertedBy F := by
  intro _ _ _ hf
  simp only [isomorphisms.iff] at hf
  infer_instance

end MorphismProperty

end CategoryTheory

