/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# Colimit of representables

In this file, We show that every presheaf of types on a category `C` (with `Category.{v₁} C`)
is a colimit of representables. This result is also known as the density theorem,
the co-Yoneda lemma and the Ninja Yoneda lemma. Three formulations are given:
* `colimitOfRepresentable` uses the category of elements of a functor to types;
* `isColimitTautologicalCocone` uses the category of costructured arrows
  for `yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁`;
* `isColimitTautologicalCocone'` uses the category of costructured arrows
  for `uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type max w v₁`, when the presheaf has values
  in `Type max w v₁`;

In this file, we also study the left Kan extensions of functors `A : C ⥤ ℰ`
along the Yoneda embedding `uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type max w v₁ v₂`
(when `Category.{v₂} ℰ` and `w` is an auxiliary universe). In particular,
the definition `uliftYonedaAdjunction` shows that such a pointwise left Kan
extension (which exists when `ℰ` has colimits) is a left adjoint to the
functor `restrictedULiftYoneda : ℰ ⥤ Cᵒᵖ ⥤ Type max w v₁ v₂`.

In the lemma `isLeftKanExtension_along_uliftYoneda_iff`, we show that
if `L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ` and `α : A ⟶ uliftYoneda ⋙ L`, then
`α` makes `L` the left Kan extension of `L` along yoneda if and only if
`α` is an isomorphism (i.e. `L` extends `A`) and `L` preserves colimits.
`uniqueExtensionAlongULiftYoneda` shows `uliftYoneda.leftKanExtension A` is
unique amongst functors preserving colimits with this property, establishing the
presheaf category as the free cocompletion of a category.

Given a functor `F : C ⥤ D`, we also show construct an isomorphism
`compULiftYonedaIsoULiftYonedaCompLan : F ⋙ uliftYoneda ≅ uliftYoneda ⋙ F.op.lan`, and
show that it makes `F.op.lan` a left Kan extension of `F ⋙ uliftYoneda`.

## Tags
colimit, representable, presheaf, free cocompletion

## References
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://ncatlab.org/nlab/show/Yoneda+extension
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Opposite ConcreteCategory

universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

namespace Presheaf

variable {ℰ : Type u₂} [Category.{v₂} ℰ] (A : C ⥤ ℰ)

/--
Given a functor `A : C ⥤ ℰ` (with `Category.{v₂} ℰ`) and an auxiliary universe `w`,
this is the functor `ℰ ⥤ Cᵒᵖ ⥤ Type max w v₂` which sends `(E : ℰ) (c : Cᵒᵖ)`
to the homset `A.obj C ⟶ E` (considered in the higher universe `max w v₂`).
Under the existence of a suitable pointwise left Kan extension, it is shown in
`uliftYonedaAdjunction` that this functor has a left adjoint.

Defined as in [MM92], Chapter I, Section 5, Theorem 2.
-/
@[simps! obj_map map_app]
/-
**CategoryTheory.Presheaf.restrictedULiftYoneda** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Presheaf`。
形式化陈述：restrictedULiftYoneda : ℰ ⥤ Cᵒᵖ ⥤ Type max w v₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `A : C ⥤ ℰ` (with `Category.{v₂} ℰ`) and an auxiliary universe `
w`,
this is the functor `ℰ ⥤ Cᵒᵖ ⥤ Type max w v₂` which sends `(E : ℰ) (c : Cᵒᵖ)`
to the homset `A.obj C ⟶ E` (considered in the higher universe `max w v₂`).
Under the existence of a suitable pointwise left Kan extension, it is shown in
`uliftYonedaAdjunction` that this functor has a left adjoint.

Defined as in [MM92], Chapter I, Section 5, Theorem 2.
-/
def restrictedULiftYoneda : ℰ ⥤ Cᵒᵖ ⥤ Type max w v₂ :=
    uliftYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ _).obj A.op

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Presheaf.map_comp_uliftYonedaEquiv_down** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Presheaf`。
形式化陈述：map_comp_uliftYonedaEquiv_down (E : ℰ) {X Y : C} (f : X ⟶ Y) (g : uliftYon
eda.{max w v₂}.obj Y ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E) : A.map f ≫ (
uliftYonedaEquiv g).down = (uliftYonedaEquiv (uliftYoneda.map f ≫ g)).down
参数：E : ℰ；f : X ⟶ Y；g : uliftYoneda.{max w v₂}.obj Y ⟶ (restrictedULiftYoneda.{ma
x w v₁} A).obj E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_uliftYonedaEquiv_down (E : ℰ) {X Y : C} (f : X ⟶ Y)
    (g : uliftYoneda.{max w v₂}.obj Y ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E) :
    A.map f ≫ (uliftYonedaEquiv g).down =
      (uliftYonedaEquiv (uliftYoneda.map f ≫ g)).down := by
  have := (g.naturality_apply f.op) (ULift.up (𝟙 Y))
  dsimp [uliftYonedaEquiv, uliftYoneda] at this ⊢
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `restrictedULiftYonedaHomEquiv`. -/
/-
**CategoryTheory.Presheaf.restrictedULiftYonedaHomEquiv'** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Presheaf`。
形式化陈述：restrictedULiftYonedaHomEquiv' (P : Cᵒᵖ ⥤ Type max w v₁ v₂) (E : ℰ) : (Cos
tructuredArrow.proj uliftYoneda.{max w v₂} P ⋙ A ⟶ (Functor.const (CostructuredA
rrow uliftYoneda.{max w v₂} P)).obj E) ≃ (P ⟶ (restrictedULiftYoneda.{max w v₁} 
A).obj E) where toFun f
参数：P : Cᵒᵖ ⥤ Type max w v₁ v₂；E : ℰ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Auxiliary definition for `restrictedULiftYonedaHomEquiv`.
-/
def restrictedULiftYonedaHomEquiv' (P : Cᵒᵖ ⥤ Type max w v₁ v₂) (E : ℰ) :
    (CostructuredArrow.proj uliftYoneda.{max w v₂} P ⋙ A ⟶
      (Functor.const (CostructuredArrow uliftYoneda.{max w v₂} P)).obj E) ≃
      (P ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E) where
  toFun f :=
    { app _ := ↾fun x ↦ ULift.up
        (f.app (CostructuredArrow.mk (uliftYonedaEquiv.symm x)))
      naturality _ _ g := by
        ext x
        let φ : CostructuredArrow.mk (uliftYonedaEquiv.{max w v₂}.symm (P.map g x)) ⟶
          CostructuredArrow.mk (uliftYonedaEquiv.symm x) :=
            CostructuredArrow.homMk g.unop (by
              dsimp
              rw [uliftYonedaEquiv_symm_map])
        dsimp
        congr 1
        simpa using! (f.naturality φ).symm }
  invFun g :=
    { app y := (uliftYonedaEquiv.{max w v₂} (y.hom ≫ g)).down
      naturality y y' f := by
        dsimp
        rw [comp_id, ← CostructuredArrow.w f, assoc, map_comp_uliftYonedaEquiv_down] }
  left_inv f := by
    ext X
    let e : CostructuredArrow.mk
      (uliftYonedaEquiv.{max w v₂}.symm (X.hom.app (op X.left) ⟨𝟙 X.left⟩)) ≅ X :=
        CostructuredArrow.isoMk (Iso.refl _) (by
          ext Y x
          dsimp
          simp [← NatTrans.naturality_apply])
    simpa [e] using! f.naturality e.inv
  right_inv g := by
    ext X x
    apply ULift.down_injective
    simp [uliftYonedaEquiv]

@[reassoc]
/-
**CategoryTheory.Presheaf.restrictedULiftYonedaHomEquiv'_symm_naturality_right**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {ℰ : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} ℰ]   (A : CategoryTheory.Functor C ℰ)
 (P : CategoryTheory.Functor Cᵒᵖ (Type (max w v₁ v₂))) {E E' : ℰ} (g : E ⟶ E')  
 (f : P ⟶ (CategoryTheory.Presheaf.restrictedULiftYoneda A).obj E),   (CategoryT
heory.Presheaf.restrictedULiftYonedaHomEquiv' A P E').symm       (CategoryTheory
.CategoryStruct.comp f ((CategoryTheory.Presheaf.restrictedULiftYoneda A).map g)
) =     CategoryTheory.CategoryStruct.comp ((CategoryTheory.Presheaf.restrictedU
LiftYonedaHomEquiv' A P E).symm f)       ((CategoryTheory.Functor.const         
    (CategoryTheory.CostructuredArrow CategoryTheory.uliftYoneda.{max w v₂, v₁, 
u₁} P)).map         g)
参数：A : CategoryTheory.Functor C ℰ；P : CategoryTheory.Functor Cᵒᵖ (Type (max w v₁
 v₂))；g : E ⟶ E'；f : P ⟶ (CategoryTheory.Presheaf.restrictedULiftYoneda A).obj E
；CategoryTheory.Presheaf.restrictedULiftYonedaHomEquiv' A P E'；CategoryTheory.Ca
tegoryStruct.comp f ((CategoryTheory.Presheaf.restrictedULiftYoneda A).map g)；(C
ategoryTheory.Presheaf.restrictedULiftYonedaHomEquiv' A P E).symm f；(CategoryThe
ory.Functor.const             (CategoryTheory.CostructuredArrow CategoryTheory.u
liftYoneda.{max w v₂, v₁, u₁} P)).map         g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma restrictedULiftYonedaHomEquiv'_symm_naturality_right (P : Cᵒᵖ ⥤ Type max w v₁ v₂)
    {E E' : ℰ} (g : E ⟶ E') (f : P ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E) :
    (restrictedULiftYonedaHomEquiv' A P E').symm (f ≫ (restrictedULiftYoneda A).map g) =
      (restrictedULiftYonedaHomEquiv' A P E).symm f ≫ (Functor.const _).map g := by
  rfl

@[reassoc]
/-
**CategoryTheory.Presheaf.restrictedULiftYonedaHomEquiv'_symm_app_naturality_lef
t** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {ℰ : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} ℰ]   (A : CategoryTheory.Functor C ℰ)
 {P Q : CategoryTheory.Functor Cᵒᵖ (Type (max w v₁ v₂))} (f : P ⟶ Q) (E : ℰ)   (
g : Q ⟶ (CategoryTheory.Presheaf.restrictedULiftYoneda A).obj E)   (p : Category
Theory.CostructuredArrow CategoryTheory.uliftYoneda.{max w v₂, v₁, u₁} P),   ((C
ategoryTheory.Presheaf.restrictedULiftYonedaHomEquiv' A P E).symm (CategoryTheor
y.CategoryStruct.comp f g)).app p =     ((CategoryTheory.Presheaf.restrictedULif
tYonedaHomEquiv' A Q E).symm g).app       ((CategoryTheory.CostructuredArrow.map
 f).obj p)
参数：A : CategoryTheory.Functor C ℰ；Type (max w v₁ v₂)；f : P ⟶ Q；E : ℰ；g : Q ⟶ (Ca
tegoryTheory.Presheaf.restrictedULiftYoneda A).obj E；p : CategoryTheory.Costruct
uredArrow CategoryTheory.uliftYoneda.{max w v₂, v₁, u₁} P；(CategoryTheory.Preshe
af.restrictedULiftYonedaHomEquiv' A P E).symm (CategoryTheory.CategoryStruct.com
p f g)；(CategoryTheory.Presheaf.restrictedULiftYonedaHomEquiv' A Q E).symm g；(Ca
tegoryTheory.CostructuredArrow.map f).obj p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma restrictedULiftYonedaHomEquiv'_symm_app_naturality_left
    {P Q : Cᵒᵖ ⥤ Type max w v₁ v₂} (f : P ⟶ Q) (E : ℰ)
    (g : Q ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E)
    (p : CostructuredArrow uliftYoneda.{max w v₂} P) :
    ((restrictedULiftYonedaHomEquiv' A P E).symm (f ≫ g)).app p =
      ((restrictedULiftYonedaHomEquiv' A Q E).symm g).app
        ((CostructuredArrow.map f).obj p) :=
  rfl

section

variable (P : ℰᵒᵖ ⥤ Type max w v₁ v₂)

/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [HasColimitsOfSize.{v₁, max u₁ v₁ v₂ w} ℰ] :
    (uliftYoneda.{max w v₂}).HasPointwiseLeftKanExtension A := by
  infer_instance

variable [(uliftYoneda.{max w v₂}).HasPointwiseLeftKanExtension A]

variable {A}
variable (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ)
  (α : A ⟶ uliftYoneda.{max w v₂} ⋙ L) [L.IsLeftKanExtension α]

/-- Auxiliary definition for `uliftYonedaAdjunction`. -/
/-
**CategoryTheory.Presheaf.restrictedULiftYonedaHomEquiv** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Presheaf`。
形式化陈述：restrictedULiftYonedaHomEquiv (P : Cᵒᵖ ⥤ Type max w v₁ v₂) (E : ℰ) : (L.ob
j P ⟶ E) ≃ (P ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E)
参数：P : Cᵒᵖ ⥤ Type max w v₁ v₂；E : ℰ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Auxiliary definition for `uliftYonedaAdjunction`.
-/
noncomputable def restrictedULiftYonedaHomEquiv (P : Cᵒᵖ ⥤ Type max w v₁ v₂) (E : ℰ) :
    (L.obj P ⟶ E) ≃ (P ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E) :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α P).homEquiv.trans
    (restrictedULiftYonedaHomEquiv' A P E)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ` is a pointwise left Kan extension
of a functor `A : C ⥤ ℰ` along the Yoneda embedding,
then `L` is a left adjoint of `restrictedULiftYoneda A : ℰ ⥤ Cᵒᵖ ⥤ Type max w v₁ v₂` -/
/-
**CategoryTheory.Presheaf.uliftYonedaAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Presheaf`。
形式化陈述：uliftYonedaAdjunction : L ⊣ restrictedULiftYoneda.{max w v₁} A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ` is a pointwise left Kan extension
of a functor `A : C ⥤ ℰ` along the Yoneda embedding,
then `L` is a left adjoint of `restrictedULiftYoneda A : ℰ ⥤ Cᵒᵖ ⥤ Type max w v₁
 v₂`
-/
noncomputable def uliftYonedaAdjunction : L ⊣ restrictedULiftYoneda.{max w v₁} A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := restrictedULiftYonedaHomEquiv L α
      homEquiv_naturality_left_symm {P Q X} f g := by
        apply (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P).hom_ext
        intro p
        have hfg := (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
          L α P).comp_homEquiv_symm ((restrictedULiftYonedaHomEquiv' A P X).symm (f ≫ g)) p
        have hg := (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
          L α Q).comp_homEquiv_symm ((restrictedULiftYonedaHomEquiv' A Q X).symm g)
            ((CostructuredArrow.map f).obj p)
        dsimp at hfg hg
        dsimp [restrictedULiftYonedaHomEquiv]
        simp only [assoc, hfg, ← L.map_comp_assoc, hg,
          restrictedULiftYonedaHomEquiv'_symm_app_naturality_left]
      homEquiv_naturality_right {P X Y} f g := by
        have := @IsColimit.homEquiv_symm_naturality (h :=
          Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P)
        dsimp at this
        apply (restrictedULiftYonedaHomEquiv L α P Y).symm.injective
        apply (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P).hom_ext
        intro
        simp [restrictedULiftYonedaHomEquiv,
          restrictedULiftYonedaHomEquiv'_symm_naturality_right, this] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Presheaf.uliftYonedaAdjunction_homEquiv_app** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：uliftYonedaAdjunction_homEquiv_app {P : Cᵒᵖ ⥤ Type max w v₁ v₂} {Y : ℰ} (f
 : L.obj P ⟶ Y) {Z : Cᵒᵖ} (z : P.obj Z) : ((uliftYonedaAdjunction.{w} L α).homEq
uiv P Y f).app Z z = ULift.up (α.app Z.unop ≫ L.map (uliftYonedaEquiv.symm z) ≫ 
f)
参数：f : L.obj P ⟶ Y；z : P.obj Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用引理 `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`：mkOfHomEquiv_homEquiv (
adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEquiv = adj.homEquiv
· 使用定理 `CategoryTheory.NatTrans.mk.congr_simp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uliftYonedaAdjunction_homEquiv_app {P : Cᵒᵖ ⥤ Type max w v₁ v₂}
    {Y : ℰ} (f : L.obj P ⟶ Y) {Z : Cᵒᵖ} (z : P.obj Z) :
    ((uliftYonedaAdjunction.{w} L α).homEquiv P Y f).app Z z =
      ULift.up (α.app Z.unop ≫ L.map (uliftYonedaEquiv.symm z) ≫ f) := by
  simp [uliftYonedaAdjunction, restrictedULiftYonedaHomEquiv,
    restrictedULiftYonedaHomEquiv', IsColimit.homEquiv]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Presheaf.uliftYonedaAdjunction_unit_app_app** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：uliftYonedaAdjunction_unit_app_app (P : Cᵒᵖ ⥤ Type max w v₁ v₂) {Z : Cᵒᵖ} 
(z : P.obj Z) : dsimp% ((uliftYonedaAdjunction.{w} L α).unit.app P).app Z z = UL
ift.up (α.app Z.unop ≫ L.map (uliftYonedaEquiv.symm z))
参数：P : Cᵒᵖ ⥤ Type max w v₁ v₂；z : P.obj Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Presheaf.uliftYonedaAdjunction_homEquiv_app`：uliftYonedaA
djunction_homEquiv_app {P : Cᵒᵖ ⥤ Type max w v₁ v₂} {Y : ℰ} (f : L.obj P ⟶ Y) {Z
 : Cᵒᵖ} (z : P.obj Z) : ((uliftYonedaAdjunction.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uliftYonedaAdjunction_unit_app_app (P : Cᵒᵖ ⥤ Type max w v₁ v₂)
    {Z : Cᵒᵖ} (z : P.obj Z) :
    dsimp% ((uliftYonedaAdjunction.{w} L α).unit.app P).app Z z =
      ULift.up (α.app Z.unop ≫ L.map (uliftYonedaEquiv.symm z)) := by
  have h₁ := (uliftYonedaAdjunction.{w} L α).homEquiv_unit P _ (𝟙 _)
  simp only [Functor.comp_obj, Functor.map_id, comp_id] at h₁
  simp [← h₁]

include α in
/-- Any left Kan extension along the Yoneda embedding preserves colimits. -/
/-
**CategoryTheory.Presheaf.preservesColimitsOfSize_of_isLeftKanExtension** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：preservesColimitsOfSize_of_isLeftKanExtension : PreservesColimitsOfSize.{v
₃, u₃} L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`：leftAdjoint_pre
servesColimits : PreservesColimitsOfSize.{v, u} F where preservesColimitsOfShape

--- 原说明 ---
Any left Kan extension along the Yoneda embedding preserves colimits.
-/
lemma preservesColimitsOfSize_of_isLeftKanExtension :
    PreservesColimitsOfSize.{v₃, u₃} L :=
  (uliftYonedaAdjunction L α).leftAdjoint_preservesColimits
/-
**CategoryTheory.Presheaf.isIso_of_isLeftKanExtension** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Presheaf`。
形式化陈述：isIso_of_isLeftKanExtension : IsIso α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.isIso_h
om`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.ULiftYoneda.instFullFunctorOppositeTypeUliftYoneda`：∀ (C 
: Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C], CategoryTheory.uliftYone
da.{w, v₁, u₁}.Full
· 使用定理 `CategoryTheory.ULiftYoneda.instFaithfulFunctorOppositeTypeUliftYoneda`：∀
 (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C], CategoryTheory.ulift
Yoneda.{w, v₁, u₁}.Faithful
-/
lemma isIso_of_isLeftKanExtension : IsIso α :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α).isIso_hom

variable (A)

/-- See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties. -/
/-
**CategoryTheory.Presheaf.preservesColimitsOfSize_leftKanExtension** 是 Mathlib 中
的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：preservesColimitsOfSize_leftKanExtension : PreservesColimitsOfSize.{v₃, u₃
} (uliftYoneda.{max w v₂}.leftKanExtension A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`：leftAdjoint_pre
servesColimits : PreservesColimitsOfSize.{v, u} F where preservesColimitsOfShape
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionLeftKanExtensionLeftKanExte
nsionUnit`：∀ {C : Type u_1} {H : Type u_3} {D : Type u_4} [inst : CategoryTheory
.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} …

--- 原说明 ---
See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
instance preservesColimitsOfSize_leftKanExtension :
    PreservesColimitsOfSize.{v₃, u₃} (uliftYoneda.{max w v₂}.leftKanExtension A) :=
  (uliftYonedaAdjunction _ (uliftYoneda.leftKanExtensionUnit A)).leftAdjoint_preservesColimits
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (uliftYoneda.{max w v₂}.leftKanExtensionUnit A) :=
  isIso_of_isLeftKanExtension _ (uliftYoneda.leftKanExtensionUnit A)

/-- A pointwise left Kan extension along the Yoneda embedding is an extension. -/
/-
**CategoryTheory.Presheaf.isExtensionAlongULiftYoneda** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Presheaf`。
形式化陈述：isExtensionAlongULiftYoneda : uliftYoneda.{max w v₂} ⋙ uliftYoneda.leftKan
Extension A ≅ A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.instIsIsoFunctorLeftKanExtensionUnitOppositeType
UliftYoneda`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {ℰ : Ty
pe u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} ℰ]   (A : CategoryTheor…

--- 原说明 ---
A pointwise left Kan extension along the Yoneda embedding is an extension.
-/
noncomputable def isExtensionAlongULiftYoneda :
    uliftYoneda.{max w v₂} ⋙ uliftYoneda.leftKanExtension A ≅ A :=
  (asIso (uliftYoneda.leftKanExtensionUnit A)).symm

end

/-- Given `P : Cᵒᵖ ⥤ Type max w v₁`, this is the functor from the opposite category
of the category of elements of `X` which sends an element in `P.obj (op X)` to the
presheaf represented by `X`. The definition `coconeOfRepresentable`
gives a cocone for this functor which is a colimit and has point `P`.
-/
@[simps! obj map]
/-
**CategoryTheory.Presheaf.functorToRepresentables** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Presheaf`。
形式化陈述：functorToRepresentables (P : Cᵒᵖ ⥤ Type max w v₁) : P.Elementsᵒᵖ ⥤ Cᵒᵖ ⥤ T
ype max w v₁
参数：P : Cᵒᵖ ⥤ Type max w v₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : Cᵒᵖ ⥤ Type max w v₁`, this is the functor from the opposite category
of the category of elements of `X` which sends an element in `P.obj (op X)` to t
he
presheaf represented by `X`. The definition `coconeOfRepresentable`
gives a cocone for this functor which is a colimit and has point `P`.
-/
def functorToRepresentables (P : Cᵒᵖ ⥤ Type max w v₁) :
    P.Elementsᵒᵖ ⥤ Cᵒᵖ ⥤ Type max w v₁ :=
  (CategoryOfElements.π P).leftOp ⋙ uliftYoneda.{w}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- This is a cocone with point `P` for the functor `functorToRepresentables P`. It is shown in
`colimitOfRepresentable P` that this cocone is a colimit: that is, we have exhibited an arbitrary
presheaf `P` as a colimit of representables.

The construction of [MM92], Chapter I, Section 5, Corollary 3.
-/
@[simps]
/-
**CategoryTheory.Presheaf.coconeOfRepresentable** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Presheaf`。
形式化陈述：coconeOfRepresentable (P : Cᵒᵖ ⥤ Type max w v₁) : Cocone (functorToReprese
ntables P) where pt
参数：P : Cᵒᵖ ⥤ Type max w v₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
This is a cocone with point `P` for the functor `functorToRepresentables P`. It 
is shown in
`colimitOfRepresentable P` that this cocone is a colimit: that is, we have exhib
ited an arbitrary
presheaf `P` as a colimit of representables.

The construction of [MM92], Chapter I, Section 5, Corollary 3.
-/
def coconeOfRepresentable (P : Cᵒᵖ ⥤ Type max w v₁) :
    Cocone (functorToRepresentables P) where
  pt := P
  ι :=
    { app x := uliftYonedaEquiv.symm x.unop.2
      naturality {x₁ x₂} f := by
        dsimp
        rw [comp_id, ← uliftYonedaEquiv_symm_map, f.unop.2] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The legs of the cocone `coconeOfRepresentable` are natural in the choice of presheaf. -/
/-
**CategoryTheory.Presheaf.coconeOfRepresentable_naturality** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Presheaf`。
形式化陈述：coconeOfRepresentable_naturality {P₁ P₂ : Cᵒᵖ ⥤ Type max w v₁} (α : P₁ ⟶ P
₂) (j : P₁.Elementsᵒᵖ) : (coconeOfRepresentable P₁).ι.app j ≫ α = (coconeOfRepre
sentable P₂).ι.app ((CategoryOfElements.map α).op.obj j)
参数：α : P₁ ⟶ P₂；j : P₁.Elementsᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The legs of the cocone `coconeOfRepresentable` are natural in the choice of pres
heaf.
-/
theorem coconeOfRepresentable_naturality
    {P₁ P₂ : Cᵒᵖ ⥤ Type max w v₁} (α : P₁ ⟶ P₂) (j : P₁.Elementsᵒᵖ) :
    (coconeOfRepresentable P₁).ι.app j ≫ α =
      (coconeOfRepresentable P₂).ι.app ((CategoryOfElements.map α).op.obj j) := by
  ext T f
  simp [uliftYonedaEquiv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cocone with point `P` given by `coconeOfRepresentable` is a colimit:
that is, we have exhibited an arbitrary presheaf `P` as a colimit of representables.

The result of [MM92], Chapter I, Section 5, Corollary 3.
-/
/-
**CategoryTheory.Presheaf.colimitOfRepresentable** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Presheaf`。
形式化陈述：colimitOfRepresentable (P : Cᵒᵖ ⥤ Type max w v₁) : IsColimit (coconeOfRepr
esentable P) where desc s
参数：P : Cᵒᵖ ⥤ Type max w v₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone with point `P` given by `coconeOfRepresentable` is a colimit:
that is, we have exhibited an arbitrary presheaf `P` as a colimit of representab
les.

The result of [MM92], Chapter I, Section 5, Corollary 3.
-/
def colimitOfRepresentable (P : Cᵒᵖ ⥤ Type max w v₁) :
    IsColimit (coconeOfRepresentable P) where
  desc s :=
    { app X := ↾fun x ↦ uliftYonedaEquiv
        (s.ι.app (Opposite.op (Functor.elementsMk P X x)))
      naturality X Y f := by
        ext x
        have := s.w (Quiver.Hom.op (CategoryOfElements.homMk (P.elementsMk X x)
          (P.elementsMk Y (P.map f x)) f rfl))
        dsimp at this x ⊢
        rw [← this, uliftYonedaEquiv_comp]
        dsimp
        rw [uliftYonedaEquiv_apply, uliftYonedaEquiv_apply,
          ← NatTrans.naturality_apply]
        simp [uliftYoneda] }
  fac s j := by
    ext X x
    let φ : j.unop ⟶ (Functor.elementsMk P _
      ((uliftYonedaEquiv.symm (unop j).snd).app X x)) := ⟨x.down.op, rfl⟩
    have := s.w φ.op
    dsimp [φ] at this x ⊢
    rw [← this, uliftYonedaEquiv_apply]
    simp [uliftYoneda]
  uniq s m hm := by
    ext X x
    simp only [functorToRepresentables_obj, coconeOfRepresentable_pt, Functor.const_obj_obj,
      coconeOfRepresentable_ι_app, Functor.leftOp_obj, CategoryOfElements.π_obj, op_unop,
      TypeCat.Fun.toFun_apply, hom_ofHom, TypeCat.Fun.coe_mk] at hm ⊢
    rw [← hm, uliftYonedaEquiv_comp, Equiv.apply_symm_apply]

variable {A : C ⥤ ℰ}
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [HasColimitsOfSize.{v₁, max w u₁ v₁ v₂} ℰ] :
    uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension A := by
  infer_instance

variable [uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension A]

section

variable (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ) (α : A ⟶ uliftYoneda.{max w v₂} ⋙ L)

/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [L.IsLeftKanExtension α] : IsIso α :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α).isIso_hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Presheaf.isLeftKanExtension_along_uliftYoneda_iff** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLeftKanExtension_along_uliftYoneda_iff : L.IsLeftKanExtension α ↔ (IsIso
 α ∧ PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.instIsIsoFunctorOfIsLeftKanExtensionOppositeType
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {ℰ : Type u₂} [ins
t_1 : CategoryTheory.Category.{v₂, u₂} ℰ]   {A : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesColimits_of_natIso`：preservesColimits_of_
natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfSize.{w, w'} F] : Preserves
ColimitsOfSize.{w, w'} G where preserve…
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionLeftKanExtensionLeftKanExte
nsionUnit`：∀ {C : Type u_1} {H : Type u_3} {D : Type u_4} [inst : CategoryTheory
.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用定理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftK
anExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheo
ry.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerRight_id'`：whiskerRight_id' {G : C ⥤ D} (F
 : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
-/
lemma isLeftKanExtension_along_uliftYoneda_iff :
    L.IsLeftKanExtension α ↔
      (IsIso α ∧ PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L) := by
  constructor
  · intro
    exact ⟨inferInstance, preservesColimits_of_natIso (Functor.leftKanExtensionUnique _
      (uliftYoneda.{max w v₂}.leftKanExtensionUnit A) _ α)⟩
  · rintro ⟨_, _⟩
    apply Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftKanExtension
      (E := Functor.LeftExtension.mk _ α)
    intro P
    dsimp [Functor.LeftExtension.IsPointwiseLeftKanExtensionAt]
    apply IsColimit.ofWhiskerEquivalence
      (CategoryOfElements.costructuredArrowULiftYonedaEquivalence _)
    let e : (CategoryOfElements.costructuredArrowULiftYonedaEquivalence P).functor ⋙
      CostructuredArrow.proj uliftYoneda.{max w v₂} P ⋙ A ≅
        functorToRepresentables.{max w v₂} P ⋙ L :=
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (asIso α)) ≪≫
        Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (Iso.refl _) L
    refine (IsColimit.precomposeHomEquiv e.symm _).1 ?_
    exact IsColimit.ofIsoColimit (isColimitOfPreserves L (colimitOfRepresentable.{max w v₂} P))
      (Cocone.ext (Iso.refl _))
/-
**CategoryTheory.Presheaf.isLeftKanExtension_of_preservesColimits** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLeftKanExtension_of_preservesColimits (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ)
 (e : A ≅ uliftYoneda.{max w v₂} ⋙ L) [PreservesColimitsOfSize.{v₁, max w u₁ v₁ 
v₂} L] : L.IsLeftKanExtension e.hom
参数：L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ；e : A ≅ uliftYoneda.{max w v₂} ⋙ L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presheaf.isLeftKanExtension_along_uliftYoneda_iff`：isLeft
KanExtension_along_uliftYoneda_iff : L.IsLeftKanExtension α ↔ (IsIso α ∧ Preserv
esColimitsOfSize.{v₁, max w u₁ v₁ v₂} L)
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
lemma isLeftKanExtension_of_preservesColimits
    (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ) (e : A ≅ uliftYoneda.{max w v₂} ⋙ L)
    [PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L] :
    L.IsLeftKanExtension e.hom := by
  rw [isLeftKanExtension_along_uliftYoneda_iff]
  exact ⟨inferInstance, ⟨inferInstance⟩⟩

end

/-- Show that `uliftYoneda.leftKanExtension A` is the unique colimit-preserving
functor which extends `A` to the presheaf category.

The second part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 3 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
/-
**CategoryTheory.Presheaf.uniqueExtensionAlongULiftYoneda** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Presheaf`。
形式化陈述：uniqueExtensionAlongULiftYoneda (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ) (e : A 
≅ uliftYoneda.{max w v₂} ⋙ L) [PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L] :
 L ≅ uliftYoneda.{max w v₂}.leftKanExtension A
参数：L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ；e : A ≅ uliftYoneda.{max w v₂} ⋙ L。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isLeftKanExtension_of_preservesColimits`：isLeftK
anExtension_of_preservesColimits (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ) (e : A ≅ uli
ftYoneda.{max w v₂} ⋙ L) [PreservesColimitsOfSize.{v₁…

--- 原说明 ---
Show that `uliftYoneda.leftKanExtension A` is the unique colimit-preserving
functor which extends `A` to the presheaf category.

The second part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 3 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
noncomputable def uniqueExtensionAlongULiftYoneda (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ)
    (e : A ≅ uliftYoneda.{max w v₂} ⋙ L)
    [PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L] :
    L ≅ uliftYoneda.{max w v₂}.leftKanExtension A :=
  have := isLeftKanExtension_of_preservesColimits L e
  Functor.leftKanExtensionUnique _ e.hom _ (uliftYoneda.leftKanExtensionUnit A)
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ) [PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L]
    [uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension (uliftYoneda.{max w v₂} ⋙ L)] :
    L.IsLeftKanExtension (𝟙 _ : uliftYoneda.{max w v₂} ⋙ L ⟶ _) :=
  isLeftKanExtension_of_preservesColimits _ (Iso.refl _)

/-- If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. Note this is a (partial)
converse to `leftAdjointPreservesColimits`.
-/
/-
**CategoryTheory.Presheaf.isLeftAdjoint_of_preservesColimits** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLeftAdjoint_of_preservesColimits (L : (C ⥤ Type max w v₁ v₂) ⥤ ℰ) [Prese
rvesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L] [uliftYoneda.{max w v₂}.HasPointwiseL
eftKanExtension (uliftYoneda.{max w v₂} ⋙ (opOpEquivalence C).congrLeft.functor.
comp L)] : L.IsLeftAdjoint
参数：L : (C ⥤ Type max w v₁ v₂) ⥤ ℰ；uliftYoneda.{max w v₂} ⋙ (opOpEquivalence C).c
ongrLeft.functor.comp L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.instIsLeftKanExtensionFunctorOppositeTypeIdCompU
liftYonedaOfPreservesColimitsOfSizeOfHasPointwiseLeftKanExtension`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {ℰ : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} ℰ]   (L : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.comp_preservesColimits`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {E : Type u₃} [ℰ :…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. Note this
 is a (partial)
converse to `leftAdjointPreservesColimits`.
-/
lemma isLeftAdjoint_of_preservesColimits (L : (C ⥤ Type max w v₁ v₂) ⥤ ℰ)
    [PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L]
    [uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension
      (uliftYoneda.{max w v₂} ⋙ (opOpEquivalence C).congrLeft.functor.comp L)] :
    L.IsLeftAdjoint :=
  ⟨_, ⟨((opOpEquivalence C).congrLeft.symm.toAdjunction.comp
    (uliftYonedaAdjunction _ (𝟙 _))).ofNatIsoLeft
      ((opOpEquivalence C).congrLeft.invFunIdAssoc L)⟩⟩

section

variable {D : Type u₂} [Category.{v₁} D] (F : C ⥤ D)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (Y : F.op.LeftExtension (yoneda.obj X)) :
    Unique (Functor.LeftExtension.mk _ (yonedaMap F X) ⟶ Y) where
  default := StructuredArrow.homMk
      (yonedaEquiv.symm (yonedaEquiv (F := F.op.comp Y.right) Y.hom)) (by
        ext Z f
        convert! (Y.hom.naturality_apply f.op _).symm
        simp)
  uniq φ := by
    ext1
    apply yonedaEquiv.injective
    simp [← StructuredArrow.w φ, yonedaEquiv, yonedaMap]

/-- Given `F : C ⥤ D` and `X : C`, `yoneda.obj (F.obj X) : Dᵒᵖ ⥤ Type _` is the
left Kan extension of `yoneda.obj X : Cᵒᵖ ⥤ Type _` along `F.op`. -/
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : C ⥤ D` and `X : C`, `yoneda.obj (F.obj X) : Dᵒᵖ ⥤ Type _` is the
left Kan extension of `yoneda.obj X : Cᵒᵖ ⥤ Type _` along `F.op`.
-/
instance (X : C) : (yoneda.obj (F.obj X)).IsLeftKanExtension (yonedaMap F X) :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩

end

section

variable {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (Y : F.op.LeftExtension (uliftYoneda.{max w v₂}.obj X)) :
    Unique (Functor.LeftExtension.mk _ (uliftYonedaMap.{w} F X) ⟶ Y) where
  default := StructuredArrow.homMk
    (uliftYonedaEquiv.symm (uliftYonedaEquiv (F := F.op ⋙ Y.right) Y.hom)) (by
      ext Z ⟨f⟩
      simpa [uliftYonedaEquiv, uliftYoneda] using
        ConcreteCategory.congr_hom (CC := fun X ↦ X) (Y.hom.naturality f.op).symm (ULift.up (𝟙 _)))
  uniq φ := by
    ext : 1
    apply uliftYonedaEquiv.injective
    simp [← StructuredArrow.w φ, uliftYonedaEquiv, uliftYonedaMap]

/-- Given `F : C ⥤ D` and `X : C`, `uliftYoneda.obj (F.obj X) : Dᵒᵖ ⥤ Type max w v₁ v₂` is the
left Kan extension of `uliftYoneda.obj X : Cᵒᵖ ⥤ Type max w v₁ v₂` along `F.op`. -/
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : C ⥤ D` and `X : C`, `uliftYoneda.obj (F.obj X) : Dᵒᵖ ⥤ Type max w v₁ 
v₂` is the
left Kan extension of `uliftYoneda.obj X : Cᵒᵖ ⥤ Type max w v₁ v₂` along `F.op`.
-/
instance (X : C) : (uliftYoneda.{max w v₁}.obj (F.obj X)).IsLeftKanExtension
    (uliftYonedaMap.{w} F X) :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩

section
variable [∀ (P : Cᵒᵖ ⥤ Type max w v₁ v₂), F.op.HasLeftKanExtension P]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `F ⋙ uliftYoneda` is naturally isomorphic to `uliftYoneda ⋙ F.op.lan`. -/
/-
**CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：compULiftYonedaIsoULiftYonedaCompLan : F ⋙ uliftYoneda.{max w v₁} ≅ uliftY
oneda.{max w v₂} ⋙ F.op.lan
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.instIsLeftKanExtensionOppositeObjFunctorTypeUlif
tYonedaUliftYonedaMap`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…

--- 原说明 ---
`F ⋙ uliftYoneda` is naturally isomorphic to `uliftYoneda ⋙ F.op.lan`.
-/
noncomputable def compULiftYonedaIsoULiftYonedaCompLan :
    F ⋙ uliftYoneda.{max w v₁} ≅ uliftYoneda.{max w v₂} ⋙ F.op.lan :=
  NatIso.ofComponents (fun X => Functor.leftKanExtensionUnique _
    (uliftYonedaMap.{w} F X) (F.op.lan.obj _) (F.op.lanUnit.app (uliftYoneda.obj X)))
    (fun {X Y} f => by
      apply uliftYonedaEquiv.injective
      have eq₁ := ConcreteCategory.congr_hom
        ((uliftYoneda.{max w v₁}.obj (F.obj Y)).descOfIsLeftKanExtension_fac_app
        (uliftYonedaMap F Y) (F.op.lan.obj (uliftYoneda.obj Y))
          (F.op.lanUnit.app (uliftYoneda.obj Y)) _) ⟨f⟩
      have eq₂ := ConcreteCategory.congr_hom
        (((uliftYoneda.{max w v₁}.obj (F.obj X)).descOfIsLeftKanExtension_fac_app
        (uliftYonedaMap F X) (F.op.lan.obj (uliftYoneda.obj X))
          (F.op.lanUnit.app (uliftYoneda.obj X))) _) ⟨𝟙 _⟩
      have eq₃ := ConcreteCategory.congr_hom (congr_app (F.op.lanUnit.naturality
        (uliftYoneda.{max w v₂}.map f)) _) ⟨𝟙 _⟩
      dsimp [uliftYoneda, uliftYonedaMap, uliftYonedaEquiv,
        Functor.leftKanExtensionUnique] at eq₁ eq₂ eq₃ ⊢
      simp only [Functor.map_id] at eq₂
      simp only [id_comp] at eq₃
      simp [eq₁, eq₂, eq₃])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan_inv_app_app_apply
_eq_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：compULiftYonedaIsoULiftYonedaCompLan_inv_app_app_apply_eq_id (X : C) : dsi
mp% ((compULiftYonedaIsoULiftYonedaCompLan.{w} F).inv.app X).app (op (F.obj X)) 
((F.op.lanUnit.app ((uliftYoneda.{max w v₂}).obj X)).app (op X) (ULift.up (𝟙 X))
) = ULift.up (𝟙 (F.obj X))
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionObjLanAppLanUnit`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac_app`：descOfIsLeftKan
Extension_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) : α.app X ≫ (F'.descOfIsLe
ftKanExtension α G β).app (L.obj X) = β.app X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compULiftYonedaIsoULiftYonedaCompLan_inv_app_app_apply_eq_id (X : C) :
    dsimp% ((compULiftYonedaIsoULiftYonedaCompLan.{w} F).inv.app X).app (op (F.obj X))
          ((F.op.lanUnit.app ((uliftYoneda.{max w v₂}).obj X)).app (op X)
        (ULift.up (𝟙 X))) = ULift.up (𝟙 (F.obj X)) :=
        (ConcreteCategory.congr_hom (CC := fun X ↦ X) (Functor.descOfIsLeftKanExtension_fac_app _
    (F.op.lanUnit.app ((uliftYoneda.{max w v₂}).obj X)) _
    (uliftYonedaMap.{w} F X) (op X)) (ULift.up (𝟙 X))).trans (by simp [uliftYonedaMap])

end

namespace compULiftYonedaIsoULiftYonedaCompLan

variable {F}

section

variable {X : C} {G : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂}
  (φ : F ⋙ uliftYoneda.{max w v₁} ⟶ uliftYoneda.{max w v₂} ⋙ G)

/-- Auxiliary definition for `presheafHom`. -/
/-
**CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan.coconeApp** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan
`。
形式化陈述：coconeApp {P : Cᵒᵖ ⥤ Type max w v₁ v₂} (x : P.Elements) : uliftYoneda.{max
 w v₂}.obj x.1.unop ⟶ F.op ⋙ G.obj P
参数：x : P.Elements。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Auxiliary definition for `presheafHom`.
-/
def coconeApp {P : Cᵒᵖ ⥤ Type max w v₁ v₂} (x : P.Elements) :
    uliftYoneda.{max w v₂}.obj x.1.unop ⟶ F.op ⋙ G.obj P :=
  uliftYonedaEquiv.symm
    ((G.map (uliftYonedaEquiv.{max w v₂}.symm x.2)).app _
      ((φ.app x.1.unop).app _ (ULift.up (𝟙 _))))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan.coconeApp_natural
ity** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf.compULiftYonedaIsoULiftYo
nedaCompLan`。
形式化陈述：coconeApp_naturality {P : Cᵒᵖ ⥤ Type max w v₁ v₂} {x y : P.Elements} (f : 
x ⟶ y) : uliftYoneda.map f.1.unop ≫ coconeApp.{w} φ x = coconeApp φ y
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.uliftYonedaEquiv_naturality`：uliftYonedaEquiv_naturality 
{X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type (max w v₁)} (f : uliftYoneda.{w}.obj (unop X) ⟶ F) (
g : X ⟶ Y) : F.map g (uliftYoned…
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coconeApp_naturality {P : Cᵒᵖ ⥤ Type max w v₁ v₂} {x y : P.Elements} (f : x ⟶ y) :
    uliftYoneda.map f.1.unop ≫ coconeApp.{w} φ x = coconeApp φ y := by
  have eq₁ : uliftYoneda.map f.1.unop ≫ uliftYonedaEquiv.symm x.2 =
      uliftYonedaEquiv.{max w v₂}.symm y.2 :=
    uliftYonedaEquiv.injective
      (by simpa only [Equiv.apply_symm_apply, ← uliftYonedaEquiv_naturality] using f.2)
  have eq₂ := ConcreteCategory.congr_hom ((G.map (uliftYonedaEquiv.{max w v₂}.symm x.2)).naturality
    (F.map f.1.unop).op) ((φ.app x.1.unop).app _ (ULift.up (𝟙 _)))
  have eq₃ := ConcreteCategory.congr_hom (CC := fun X ↦ X)
    (congr_app (φ.naturality f.1.unop) _) (ULift.up (𝟙 _))
  have eq₄ := ConcreteCategory.congr_hom ((φ.app x.1.unop).naturality (F.map f.1.unop).op)
  dsimp at eq₂ eq₃ eq₄
  apply uliftYonedaEquiv.{max w v₂}.injective
  dsimp only [coconeApp]
  rw [Equiv.apply_symm_apply, ← uliftYonedaEquiv_naturality, Equiv.apply_symm_apply]
  simp only [op_unop, Functor.comp_obj, Functor.op_obj, Functor.comp_map, Functor.op_map,
    uliftYoneda_obj_obj, yoneda_obj_obj, ← eq₃, ← eq₄, ← eq₂, ← eq₁, Functor.map_comp,
    NatTrans.comp_app, comp_apply]
  simp [uliftYoneda]

set_option backward.isDefEq.respectTransparency false in
/-- Given functors `F : C ⥤ D` and
`G : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ (Dᵒᵖ ⥤ Type max w v₁ v₂)`,
and a natural transformation `φ : F ⋙ uliftYoneda ⟶ uliftYoneda ⋙ G`, this is the
(natural) morphism `P ⟶ F.op ⋙ G.obj P` for all `P : Cᵒᵖ ⥤ Type max w v₁ v₂` that is
determined by `φ`. -/
/-
**CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan.presheafHom** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompL
an`。
形式化陈述：presheafHom (P : Cᵒᵖ ⥤ Type max w v₁ v₂) : P ⟶ F.op ⋙ G.obj P
参数：P : Cᵒᵖ ⥤ Type max w v₁ v₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given functors `F : C ⥤ D` and
`G : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ (Dᵒᵖ ⥤ Type max w v₁ v₂)`,
and a natural transformation `φ : F ⋙ uliftYoneda ⟶ uliftYoneda ⋙ G`, this is th
e
(natural) morphism `P ⟶ F.op ⋙ G.obj P` for all `P : Cᵒᵖ ⥤ Type max w v₁ v₂` tha
t is
determined by `φ`.
-/
def presheafHom (P : Cᵒᵖ ⥤ Type max w v₁ v₂) : P ⟶ F.op ⋙ G.obj P :=
  (colimitOfRepresentable P).desc
    (Cocone.mk _ { app x := coconeApp.{w} φ x.unop })
/-
**CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan.uliftYonedaEquiv_
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf.compULiftYonedaIsoULiftYoned
aCompLan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uliftYonedaEquiv_ι_presheafHom (P : Cᵒᵖ ⥤ Type max w v₁ v₂) {X : C}
    (f : uliftYoneda.{max w v₂}.obj X ⟶ P) :
    uliftYonedaEquiv (f ≫ presheafHom.{w} φ P) =
      (G.map f).app (Opposite.op (F.obj X)) ((φ.app X).app _ (ULift.up (𝟙 _))) := by
  obtain ⟨x, rfl⟩ := uliftYonedaEquiv.symm.surjective f
  erw [(colimitOfRepresentable P).fac _ (Opposite.op (P.elementsMk _ x))]
  dsimp only [coconeApp]
  apply Equiv.apply_symm_apply
/-
**CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan.uliftYonedaEquiv_
presheafHom_uliftYoneda_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf.c
ompULiftYonedaIsoULiftYonedaCompLan`。
形式化陈述：uliftYonedaEquiv_presheafHom_uliftYoneda_obj (X : C) : uliftYonedaEquiv.{m
ax w v₂} (presheafHom.{w} φ (uliftYoneda.{max w v₂}.obj X)) = ((φ.app X).app (F.
op.obj (Opposite.op X)) (ULift.up (𝟙 _)))
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用引理 `CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan.uliftYoneda
Equiv_ι_presheafHom`：uliftYonedaEquiv_ι_presheafHom (P : Cᵒᵖ ⥤ Type max w v₁ v₂)
 {X : C} (f : uliftYoneda.{max w v₂}.obj X ⟶ P) : uliftYonedaEquiv (f ≫ presheaf
H…
-/
lemma uliftYonedaEquiv_presheafHom_uliftYoneda_obj (X : C) :
    uliftYonedaEquiv.{max w v₂} (presheafHom.{w} φ (uliftYoneda.{max w v₂}.obj X)) =
      ((φ.app X).app (F.op.obj (Opposite.op X)) (ULift.up (𝟙 _))) := by
  simpa using! uliftYonedaEquiv_ι_presheafHom.{w} φ (uliftYoneda.obj X) (𝟙 _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan.presheafHom_natur
ality** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf.compULiftYonedaIsoULift
YonedaCompLan`。
形式化陈述：presheafHom_naturality {P Q : Cᵒᵖ ⥤ Type max w v₁ v₂} (f : P ⟶ Q) : preshe
afHom.{w} φ P ≫ Functor.whiskerLeft F.op (G.map f) = f ≫ presheafHom φ Q
参数：f : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.hom_ext_uliftYoneda`：hom_ext_uliftYoneda {P Q : Cᵒᵖ ⥤ Typ
e (max w v₁)} {f g : P ⟶ Q} (h : forall (X : C) (p : uliftYoneda.{w}.obj X ⟶ P),
 p ≫ f = p ≫ g) : f = g
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan.uliftYoneda
Equiv_ι_presheafHom`：uliftYonedaEquiv_ι_presheafHom (P : Cᵒᵖ ⥤ Type max w v₁ v₂)
 {X : C} (f : uliftYoneda.{max w v₂}.obj X ⟶ P) : uliftYonedaEquiv (f ≫ presheaf
H…
· 使用引理 `CategoryTheory.uliftYonedaEquiv_comp`：uliftYonedaEquiv_comp {X : C} {F G
 : Cᵒᵖ ⥤ Type (max w v₁)} (α : uliftYoneda.{w}.obj X ⟶ F) (β : F ⟶ G) : uliftYon
edaEquiv.{w} (α ≫ β) = β.a…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma presheafHom_naturality {P Q : Cᵒᵖ ⥤ Type max w v₁ v₂} (f : P ⟶ Q) :
    presheafHom.{w} φ P ≫ Functor.whiskerLeft F.op (G.map f) = f ≫ presheafHom φ Q :=
  hom_ext_uliftYoneda.{max w v₂} (fun X p ↦ uliftYonedaEquiv.injective (by
    rw [← assoc p f, uliftYonedaEquiv_ι_presheafHom, ← assoc,
      uliftYonedaEquiv_comp, uliftYonedaEquiv_ι_presheafHom,
      Functor.map_comp]
    dsimp))

variable [∀ (P : Cᵒᵖ ⥤ Type max w v₁ v₂), F.op.HasLeftKanExtension P]

set_option backward.defeqAttrib.useBackward true in
/-- Given functors `F : C ⥤ D` and `G : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ (Dᵒᵖ ⥤ Type max w v₁ v₂)`,
and a natural transformation `φ : F ⋙ uliftYoneda ⟶ uliftYoneda ⋙ G`, this is
the canonical natural transformation `F.op.lan ⟶ G`, which is part of the
fact that `F.op.lan : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂`
is the left Kan extension of `F ⋙ uliftYoneda : C ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂`
along `uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type max w v₁ v₂`. -/
/-
**CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan.natTrans** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan`
。
形式化陈述：natTrans : F.op.lan ⟶ G where app P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given functors `F : C ⥤ D` and `G : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ (Dᵒᵖ ⥤ Type max w
 v₁ v₂)`,
and a natural transformation `φ : F ⋙ uliftYoneda ⟶ uliftYoneda ⋙ G`, this is
the canonical natural transformation `F.op.lan ⟶ G`, which is part of the
fact that `F.op.lan : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂`
is the left Kan extension of `F ⋙ uliftYoneda : C ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂`
along `uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type max w v₁ v₂`.
-/
noncomputable def natTrans : F.op.lan ⟶ G where
  app P := (F.op.lan.obj P).descOfIsLeftKanExtension (F.op.lanUnit.app P) _ (presheafHom φ P)
  naturality {P Q} f := by
    apply (F.op.lan.obj P).hom_ext_of_isLeftKanExtension (F.op.lanUnit.app P)
    have eq := F.op.lanUnit.naturality f
    dsimp at eq ⊢
    rw [Functor.descOfIsLeftKanExtension_fac_assoc, ← reassoc_of% eq,
      Functor.descOfIsLeftKanExtension_fac, presheafHom_naturality]
/-
**CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan.natTrans_app_ulif
tYoneda_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf.compULiftYonedaIs
oULiftYonedaCompLan`。
形式化陈述：natTrans_app_uliftYoneda_obj (X : C) : (natTrans.{w} φ).app (uliftYoneda.{
max w v₂}.obj X) = (compULiftYonedaIsoULiftYonedaCompLan.{w} F).inv.app X ≫ φ.ap
p X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionObjLanAppLanUnit`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac`：descOfIsLeftKanExte
nsion_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (F'.descOfIsLeftKanExt
ension α G β) = β
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用引理 `CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan.uliftYoneda
Equiv_presheafHom_uliftYoneda_obj`：uliftYonedaEquiv_presheafHom_uliftYoneda_obj 
(X : C) : uliftYonedaEquiv.{max w v₂} (presheafHom.{w} φ (uliftYoneda.{max w v₂}
.obj X)) = ((φ.…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan_inv_app_app
_apply_eq_id`：compULiftYonedaIsoULiftYonedaCompLan_inv_app_app_apply_eq_id (X : 
C) : dsimp% ((compULiftYonedaIsoULiftYonedaCompLan.{w} F).inv.app X).app (…
-/
lemma natTrans_app_uliftYoneda_obj (X : C) :
    (natTrans.{w} φ).app (uliftYoneda.{max w v₂}.obj X) =
      (compULiftYonedaIsoULiftYonedaCompLan.{w} F).inv.app X ≫ φ.app X := by
  dsimp [natTrans]
  apply (F.op.lan.obj (uliftYoneda.obj X)).hom_ext_of_isLeftKanExtension (F.op.lanUnit.app _)
  rw [Functor.descOfIsLeftKanExtension_fac]
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_presheafHom_uliftYoneda_obj]
  exact _root_.congr_arg _ (compULiftYonedaIsoULiftYonedaCompLan_inv_app_app_apply_eq_id F X).symm

end

variable [∀ (P : Cᵒᵖ ⥤ Type max w v₁ v₂), F.op.HasLeftKanExtension P]

set_option backward.defeqAttrib.useBackward true in
/-- Given a functor `F : C ⥤ D`, this definition is part of the verification that
`Functor.LeftExtension.mk F.op.lan (compULiftYonedaIsoULiftYonedaCompLan F).hom`
is universal, i.e. that  `F.op.lan : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂`
is the left Kan extension of `F ⋙ uliftYoneda : C ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂`
along `uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type max w v₁ v₂`. -/
/-
**CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan.extensionHom** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaComp
Lan`。
形式化陈述：extensionHom (Φ : uliftYoneda.{max w v₂}.LeftExtension (F ⋙ uliftYoneda.{m
ax w v₁})) : Functor.LeftExtension.mk F.op.lan (compULiftYonedaIsoULiftYonedaCom
pLan.{w} F).hom ⟶ Φ
参数：Φ : uliftYoneda.{max w v₂}.LeftExtension (F ⋙ uliftYoneda.{max w v₁})。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C ⥤ D`, this definition is part of the verification that
`Functor.LeftExtension.mk F.op.lan (compULiftYonedaIsoULiftYonedaCompLan F).hom`
is universal, i.e. that  `F.op.lan : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ Dᵒᵖ ⥤ Type max w
 v₁ v₂`
is the left Kan extension of `F ⋙ uliftYoneda : C ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂`
along `uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type max w v₁ v₂`.
-/
noncomputable def extensionHom
    (Φ : uliftYoneda.{max w v₂}.LeftExtension (F ⋙ uliftYoneda.{max w v₁})) :
    Functor.LeftExtension.mk F.op.lan (compULiftYonedaIsoULiftYonedaCompLan.{w} F).hom ⟶ Φ :=
  StructuredArrow.homMk (natTrans Φ.hom) (by
    ext X : 2
    dsimp
    rw [natTrans_app_uliftYoneda_obj, Iso.hom_inv_id_app_assoc])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[ext]
/-
**CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan.hom_ext** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf.compULiftYonedaIsoULiftYonedaCompLan`。
形式化陈述：hom_ext {Φ : uliftYoneda.{max w v₂}.LeftExtension (F ⋙ uliftYoneda.{max w 
v₁})} (f g : Functor.LeftExtension.mk F.op.lan (compULiftYonedaIsoULiftYonedaCom
pLan F).hom ⟶ Φ) : f = g
参数：F ⋙ uliftYoneda.{max w v₁}；f g : Functor.LeftExtension.mk F.op.lan (compULift
YonedaIsoULiftYonedaCompLan F).hom ⟶ Φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.StructuredArrow.hom_ext`：hom_ext {X Y : StructuredArrow S
 T} (f g : X ⟶ Y) (h : f.right = g.right) : f = g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionObjLanAppLanUnit`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.StructuredArrow.w`：w : X.hom ≫ T.map f.right = Y.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_ext {Φ : uliftYoneda.{max w v₂}.LeftExtension (F ⋙ uliftYoneda.{max w v₁})}
    (f g : Functor.LeftExtension.mk F.op.lan (compULiftYonedaIsoULiftYonedaCompLan F).hom ⟶ Φ) :
    f = g := by
  ext P : 3
  apply (F.op.lan.obj P).hom_ext_of_isLeftKanExtension (F.op.lanUnit.app P)
  apply (colimitOfRepresentable.{max w v₂} P).hom_ext
  intro x
  have eq := F.op.lanUnit.naturality (uliftYonedaEquiv.{max w v₂}.symm x.unop.2)
  have eq₁ := congr_hom (CC := fun X ↦ X) (congr_app (congr_app (StructuredArrow.w f) x.unop.1.unop)
    (F.op.obj x.unop.1)) (ULift.up (𝟙 _))
  have eq₂ := congr_hom (CC := fun X ↦ X) (congr_app (congr_app (StructuredArrow.w g) x.unop.1.unop)
    (F.op.obj x.unop.1)) (ULift.up (𝟙 _))
  dsimp at eq₁ eq₂ eq ⊢
  simp only [reassoc_of% eq, ← Functor.whiskerLeft_comp]
  congr 2
  simp only [← cancel_epi ((compULiftYonedaIsoULiftYonedaCompLan F).hom.app x.unop.1.unop),
    NatTrans.naturality]
  apply uliftYonedaEquiv.injective
  simp [eq₁, eq₂, uliftYonedaEquiv_apply]

end compULiftYonedaIsoULiftYonedaCompLan

variable [∀ (P : Cᵒᵖ ⥤ Type max w v₁ v₂), F.op.HasLeftKanExtension P]

/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (Φ : StructuredArrow (F ⋙ uliftYoneda.{max w v₁})
    ((Functor.whiskeringLeft C (Cᵒᵖ ⥤ Type max w v₁ v₂)
      (Dᵒᵖ ⥤ Type max w v₁ v₂)).obj uliftYoneda.{max w v₂})) :
    Unique (Functor.LeftExtension.mk F.op.lan
      (compULiftYonedaIsoULiftYonedaCompLan.{w} F).hom ⟶ Φ) where
  default := compULiftYonedaIsoULiftYonedaCompLan.extensionHom Φ
  uniq _ := compULiftYonedaIsoULiftYonedaCompLan.hom_ext _ _

/-- Given a functor `F : C ⥤ D`, `F.op.lan : (Cᵒᵖ ⥤ Type v₁) ⥤ Dᵒᵖ ⥤ Type v₁` is the
left Kan extension of `F ⋙ yoneda : C ⥤ Dᵒᵖ ⥤ Type v₁` along `yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁`. -/
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C ⥤ D`, `F.op.lan : (Cᵒᵖ ⥤ Type v₁) ⥤ Dᵒᵖ ⥤ Type v₁` is the
left Kan extension of `F ⋙ yoneda : C ⥤ Dᵒᵖ ⥤ Type v₁` along `yoneda : C ⥤ Cᵒᵖ ⥤
 Type v₁`.
-/
instance : F.op.lan.IsLeftKanExtension (compULiftYonedaIsoULiftYonedaCompLan.{w} F).hom :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For a presheaf `P`, consider the forgetful functor from the category of representable
    presheaves over `P` to the category of presheaves. There is a tautological cocone over this
    functor whose leg for a natural transformation `V ⟶ P` with `V` representable is just that
    natural transformation. (In this version, we allow the presheaf `P` to have values in
    a larger universe.) -/
@[simps]
/-
**CategoryTheory.Presheaf.tautologicalCocone'** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Presheaf`。
形式化陈述：tautologicalCocone' (P : Cᵒᵖ ⥤ Type max w v₁) : Cocone (CostructuredArrow.
proj uliftYoneda.{w} P ⋙ uliftYoneda.{w}) where pt
参数：P : Cᵒᵖ ⥤ Type max w v₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a presheaf `P`, consider the forgetful functor from the category of represen
table
    presheaves over `P` to the category of presheaves. There is a tautological c
ocone over this
    functor whose leg for a natural transformation `V ⟶ P` with `V` representabl
e is just that
    natural transformation. (In this version, we allow the presheaf `P` to have 
values in
    a larger universe.)
-/
def tautologicalCocone' (P : Cᵒᵖ ⥤ Type max w v₁) :
    Cocone (CostructuredArrow.proj uliftYoneda.{w} P ⋙ uliftYoneda.{w}) where
  pt := P
  ι := { app X := X.hom }

/-- The tautological cocone with point `P` is a colimit cocone, exhibiting `P` as a colimit of
    representables. (In this version, we allow the presheaf `P` to have values in
    a larger universe.)

    Proposition 2.6.3(i) in [Kashiwara2006] -/
/-
**CategoryTheory.Presheaf.isColimitTautologicalCocone'** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Presheaf`。
形式化陈述：isColimitTautologicalCocone' (P : Cᵒᵖ ⥤ Type max w v₁) : IsColimit (tautol
ogicalCocone'.{w} P)
参数：P : Cᵒᵖ ⥤ Type max w v₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological cocone with point `P` is a colimit cocone, exhibiting `P` as a 
colimit of
    representables. (In this version, we allow the presheaf `P` to have values i
n
    a larger universe.)

    Proposition 2.6.3(i) in [Kashiwara2006]
-/
def isColimitTautologicalCocone' (P : Cᵒᵖ ⥤ Type max w v₁) :
    IsColimit (tautologicalCocone'.{w} P) :=
  (IsColimit.whiskerEquivalenceEquiv
    (CategoryOfElements.costructuredArrowULiftYonedaEquivalence.{w} P)).2
      (colimitOfRepresentable.{w} P)


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For a presheaf `P`, consider the forgetful functor from the category of representable
    presheaves over `P` to the category of presheaves. There is a tautological cocone over this
    functor whose leg for a natural transformation `V ⟶ P` with `V` representable is just that
    natural transformation. -/
@[simps]
/-
**CategoryTheory.Presheaf.tautologicalCocone** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Presheaf`。
形式化陈述：tautologicalCocone (P : Cᵒᵖ ⥤ Type v₁) : Cocone (CostructuredArrow.proj yo
neda P ⋙ yoneda) where pt
参数：P : Cᵒᵖ ⥤ Type v₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a presheaf `P`, consider the forgetful functor from the category of represen
table
    presheaves over `P` to the category of presheaves. There is a tautological c
ocone over this
    functor whose leg for a natural transformation `V ⟶ P` with `V` representabl
e is just that
    natural transformation.
-/
def tautologicalCocone (P : Cᵒᵖ ⥤ Type v₁) :
    Cocone (CostructuredArrow.proj yoneda P ⋙ yoneda) where
  pt := P
  ι := { app X := X.hom }

/-- The tautological cocone with point `P` is a colimit cocone, exhibiting `P` as a colimit of
    representables.

    Proposition 2.6.3(i) in [Kashiwara2006] -/
/-
**CategoryTheory.Presheaf.isColimitTautologicalCocone** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Presheaf`。
形式化陈述：isColimitTautologicalCocone (P : Cᵒᵖ ⥤ Type v₁) : IsColimit (tautologicalC
ocone P)
参数：P : Cᵒᵖ ⥤ Type v₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological cocone with point `P` is a colimit cocone, exhibiting `P` as a 
colimit of
    representables.

    Proposition 2.6.3(i) in [Kashiwara2006]
-/
def isColimitTautologicalCocone (P : Cᵒᵖ ⥤ Type v₁) :
    IsColimit (tautologicalCocone P) :=
  let e : functorToRepresentables.{v₁} P ≅
    ((CategoryOfElements.costructuredArrowYonedaEquivalence P).functor ⋙
      CostructuredArrow.proj yoneda P ⋙ yoneda) :=
    NatIso.ofComponents (fun e ↦ NatIso.ofComponents (fun X ↦ Equiv.ulift.toIso))
  (IsColimit.whiskerEquivalenceEquiv
    (CategoryOfElements.costructuredArrowYonedaEquivalence P)).2
      ((IsColimit.precomposeHomEquiv e _).1 (colimitOfRepresentable.{v₁} P))

variable {I : Type v₁} [SmallCategory I] (F : I ⥤ C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a functor `F : I ⥤ C`, a cocone `c` on `F ⋙ yoneda : I ⥤ Cᵒᵖ ⥤ Type v₁` induces a
    functor `I ⥤ CostructuredArrow yoneda c.pt` which maps `i : I` to the leg
    `yoneda.obj (F.obj i) ⟶ c.pt`. If `c` is a colimit cocone, then that functor is
    final.

    Proposition 2.6.3(ii) in [Kashiwara2006] -/
/-
**CategoryTheory.Presheaf.final_toCostructuredArrow_comp_pre** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：final_toCostructuredArrow_comp_pre {c : Cocone (F ⋙ yoneda)} (hc : IsColim
it c) : Functor.Final (c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.
pt)
参数：F ⋙ yoneda；hc : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_isTerminal_colimit_comp_yoneda`：final_of
_isTerminal_colimit_comp_yoneda (h : IsTerminal (colimit (F ⋙ yoneda))) : Final 
F
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.preservesColimit_of_createsColimit_and_hasColimit`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom_assoc`
：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst
_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CreatesLimit.toReflectsLimit`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Limits.instHasColimitCompOfPreservesColimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
Given a functor `F : I ⥤ C`, a cocone `c` on `F ⋙ yoneda : I ⥤ Cᵒᵖ ⥤ Type v₁` in
duces a
    functor `I ⥤ CostructuredArrow yoneda c.pt` which maps `i : I` to the leg
    `yoneda.obj (F.obj i) ⟶ c.pt`. If `c` is a colimit cocone, then that functor
 is
    final.

    Proposition 2.6.3(ii) in [Kashiwara2006]
-/
theorem final_toCostructuredArrow_comp_pre {c : Cocone (F ⋙ yoneda)} (hc : IsColimit c) :
    Functor.Final (c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) := by
  apply Functor.final_of_isTerminal_colimit_comp_yoneda
  suffices IsTerminal (colimit ((c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) ⋙
      CostructuredArrow.toOver yoneda c.pt)) by
    apply IsTerminal.isTerminalOfObj (overEquivPresheafCostructuredArrow c.pt).inverse
    apply IsTerminal.ofIso this
    refine ?_ ≪≫ (preservesColimitIso (overEquivPresheafCostructuredArrow c.pt).inverse _).symm
    apply HasColimit.isoOfNatIso
    exact Functor.isoWhiskerLeft _
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow c.pt).isoCompInverse
  apply IsTerminal.ofIso Over.mkIdTerminal
  let isc : IsColimit ((Over.forget _).mapCocone _) := isColimitOfPreserves _
    (colimit.isColimit ((c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) ⋙
      CostructuredArrow.toOver yoneda c.pt))
  exact Over.isoMk (hc.coconePointUniqueUpToIso isc) (hc.hom_ext fun i => by simp)

end Presheaf

namespace Functor.Elements

variable [LocallySmall.{w} C] (F : C ⥤ Type w)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F : C ⥤ Type w` and `C` is locally `w`-small, then for any `X : C`,
this is the colimit cocone which identifies `F.obj X` to the colimit of
`(CategoryOfElements.π F).op ⋙ shrinkYoneda.obj X`. -/
@[simps]
/-
**CategoryTheory.Functor.Elements.cocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor.Elements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Type w` and `C` is locally `w`-small, then for any `X : C`,
this is the colimit cocone which identifies `F.obj X` to the colimit of
`(CategoryOfElements.π F).op ⋙ shrinkYoneda.obj X`.
-/
noncomputable def coconeπOpCompShrinkYonedaObj (X : C) :
    Cocone ((CategoryOfElements.π F).op ⋙ shrinkYoneda.{w}.obj X) where
  pt := F.obj X
  ι.app u := ↾fun t ↦ F.map (shrinkYonedaObjObjEquiv t) u.unop.snd
  ι.naturality u₁ u₂ g := by
    ext f
    obtain ⟨f, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective f
    simp [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F : C ⥤ Type w` and `C` is locally `w`-small, then for any `X : C`,
`F.obj X` identifies to the colimit of
`(CategoryOfElements.π F).op ⋙ shrinkYoneda.obj X`. -/
/-
**CategoryTheory.Functor.Elements.isColimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor.Elements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Type w` and `C` is locally `w`-small, then for any `X : C`,
`F.obj X` identifies to the colimit of
`(CategoryOfElements.π F).op ⋙ shrinkYoneda.obj X`.
-/
noncomputable def isColimitCoconeπOpCompShrinkYonedaObj (X : C) :
    IsColimit (coconeπOpCompShrinkYonedaObj F X) := by
  refine Nonempty.some ((Types.isColimit_iff_coconeTypesIsColimit _).2
    ⟨?_, fun x ↦ ?_⟩)
  · let G := (CategoryOfElements.π F).op ⋙ shrinkYoneda.{w}.obj X
    let c := G.coconeTypesEquiv.symm (coconeπOpCompShrinkYonedaObj F X)
    have (u : G.ColimitType) (x : F.obj X) (h : G.descColimitType c u = x) :
        G.ιColimitType (op (elementsMk _ _ x))
          (shrinkYonedaObjObjEquiv.symm (𝟙 X)) = u := by
      obtain ⟨⟨u⟩, v, rfl⟩ := Functor.ιColimitType_jointly_surjective _ u
      obtain ⟨v, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective v
      dsimp [c] at v h
      simp only [Equiv.apply_symm_apply] at h
      rw [← G.ιColimitType_map (show u ⟶ F.elementsMk _ x from ⟨v, h⟩).op]
      simp [G, shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}]
    intro u₁ u₂ hu
    generalize hx₁ : G.descColimitType c u₁ = x
    have hx₂ : G.descColimitType c u₂ = x := by rw [← hx₁]; exact hu.symm
    rw [← this _ _ hx₁, ← this _ _ hx₂]
  · exact ⟨Functor.ιColimitType _ (op (elementsMk _ _ x))
      (shrinkYonedaObjObjEquiv.symm (𝟙 X)), by simp⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Elements.shrinkYoneda_map_app_cocone** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Functor.Elements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shrinkYoneda_map_app_coconeπOpCompShrinkYonedaObj_ι_app
    {X₁ X₂ : C} (f : X₁ ⟶ X₂) (u : F.Elements) :
    dsimp% (shrinkYoneda.{w}.map f).app (op u.fst) ≫
      (coconeπOpCompShrinkYonedaObj F X₂).ι.app (op u) =
    (coconeπOpCompShrinkYonedaObj F X₁).ι.app (op u) ≫ F.map f := by
  ext g
  obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
  simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `C` is a locally `w`-small category, this is a (colimit) cocone
expressing `F : C ⥤ Type w` as a colimit of corepresentable functors. -/
/-
**CategoryTheory.Functor.Elements.cocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor.Elements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is a locally `w`-small category, this is a (colimit) cocone
expressing `F : C ⥤ Type w` as a colimit of corepresentable functors.
-/
noncomputable def coconeπOpCompShrinkYonedaFlip :
    Cocone ((CategoryOfElements.π F).op ⋙ shrinkYoneda.{w}.flip) where
  pt := F
  ι.app u :=
    { app X := (coconeπOpCompShrinkYonedaObj F X).ι.app u
      naturality {X Y} f := by
        ext x
        obtain ⟨x, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective x
        simp }
  ι.naturality u v g := by
    ext X x
    obtain ⟨x, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective x
    simp [← shrinkYonedaObjObjEquiv_symm_comp.{w}]

/-- If `F : C ⥤ Type w` and `C` is locally `w`-small, then `F` identifies to the colimit
of `(CategoryOfElements.π F).op ⋙ shrinkYoneda.{w}.flip`. -/
/-
**CategoryTheory.Functor.Elements.isColimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor.Elements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Type w` and `C` is locally `w`-small, then `F` identifies to the col
imit
of `(CategoryOfElements.π F).op ⋙ shrinkYoneda.{w}.flip`.
-/
noncomputable def isColimitCoconeπOpCompShrinkYonedaFlip :
    IsColimit (coconeπOpCompShrinkYonedaFlip F) :=
  evaluationJointlyReflectsColimits _ (isColimitCoconeπOpCompShrinkYonedaObj F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F : C ⥤ Type w` and `C` is locally `w`-small, then `F` identifies to the composition
`shrinkYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π F).op ⋙ colim`. -/
/-
**CategoryTheory.Functor.Elements.shrinkYonedaCompWhiskeringLeftObj** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Functor.Elements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Type w` and `C` is locally `w`-small, then `F` identifies to the com
position
`shrinkYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π F).op ⋙
 colim`.
-/
noncomputable def shrinkYonedaCompWhiskeringLeftObjπCompColimIso
    [HasColimitsOfShape F.Elementsᵒᵖ (Type w)] :
    shrinkYoneda.{w} ⋙
      (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π F).op ⋙ colim ≅ F :=
  NatIso.ofComponents (fun X ↦
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      (isColimitCoconeπOpCompShrinkYonedaObj F X)) (fun {X₁ X₂} f ↦ colimit.hom_ext (by
        cat_disch))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.Elements.shrinkYonedaCompWhiskeringLeftObj** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor.Elements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shrinkYonedaCompWhiskeringLeftObjπCompColimIso_inv_app_apply
    [HasColimitsOfShape F.Elementsᵒᵖ (Type w)] (u : F.Elements) :
      (shrinkYonedaCompWhiskeringLeftObjπCompColimIso F).inv.app _ u.snd =
      (colimit.ι ((CategoryOfElements.π F).op ⋙ shrinkYoneda.{w}.obj u.fst) (op u)
        (shrinkYonedaObjObjEquiv.symm (𝟙 _))) := by
  have :
      (coconeπOpCompShrinkYonedaObj F u.fst).ι.app (op u) ≫
        (shrinkYonedaCompWhiskeringLeftObjπCompColimIso F).inv.app u.fst =
      colimit.ι ((CategoryOfElements.π F).op ⋙ shrinkYoneda.{w}.obj u.fst) (op u) :=
    IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit _) _ (op u)
  simpa using ConcreteCategory.congr_hom this (shrinkYonedaObjObjEquiv.symm (𝟙 _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The object of the category of elements `shrinkYoneda.{w}.flip.obj (op X)`
corresponding to the identity of `X` is initial. -/
/-
**CategoryTheory.Functor.Elements.isInitialElementsMkShrinkYonedaObjObjEquivId**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.Elements`。
形式化陈述：isInitialElementsMkShrinkYonedaObjObjEquivId (X : C) : IsInitial (Functor.
elementsMk (shrinkYoneda.{w}.flip.obj (op X)) X (shrinkYonedaObjObjEquiv.symm (𝟙
 X)))
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The object of the category of elements `shrinkYoneda.{w}.flip.obj (op X)`
corresponding to the identity of `X` is initial.
-/
noncomputable def isInitialElementsMkShrinkYonedaObjObjEquivId (X : C) :
    IsInitial (Functor.elementsMk (shrinkYoneda.{w}.flip.obj (op X)) X
      (shrinkYonedaObjObjEquiv.symm (𝟙 X))) :=
  IsInitial.ofUniqueHom (fun u ↦ ⟨shrinkYonedaObjObjEquiv.{w} u.2, by
    simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}]⟩) (by
    rintro u ⟨m, hm⟩
    ext
    simp [← hm, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}])
/-
**CategoryTheory.Functor.Elements.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fun
ctor.Elements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : HasInitial (shrinkYoneda.{w}.flip.obj (op X)).Elements :=
  (isInitialElementsMkShrinkYonedaObjObjEquivId X).hasInitial

end Functor.Elements

end CategoryTheory

