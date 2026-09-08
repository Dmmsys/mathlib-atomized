/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered

/-!
# The image of a point by a cocontinuous functor

Let `F : C ⥤ D` be a cocontinuous functor between sites `(C, J)` and `(D, K)`.
Let `Φ` be a point of `(C, J)`. In this file, we define a point `Φ.map F K`
of `(D, K)` and show that there are natural isomorphisms
`(Φ.map F K).presheafFiber ≅ (Functor.whiskeringLeft _ _ A).obj F.op ⋙ Φ.presheafFiber`
and `(Φ.map F K).sheafFiber ≅ F.sheafPushforwardContinuous A J K ⋙ Φ.sheafFiber`
(the latter is defined only if `F` is also continuous).

-/

@[expose] public section

universe w v'' v' v u'' u' u

namespace CategoryTheory

open Limits Opposite

namespace GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} (Φ : Point.{w} J) (F : C ⥤ D)
  (K : GrothendieckTopology D) [F.IsCocontinuous J K]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.GrothendieckTopology.Point.map_aux** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.GrothendieckTopology.Point`。
形式化陈述：map_aux ⦃X : D⦄ (R : Sieve X) (hR : R in K X) ⦃u : Φ.fiber.Elements⦄ (f : 
(CategoryOfElements.π Φ.fiber ⋙ F).obj u ⟶ X) : exists (Y : D) (g : Y ⟶ X) (_ : 
R.arrows g) (v : Φ.fiber.Elements) (q : v ⟶ u) (a : F.obj v.fst ⟶ Y), a ≫ g = F.
map q.1 ≫ f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.jointly_surjective`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckT
opology C} (self : J.Point)   {X : C},   ∀ R ∈ J X…
· 使用定理 `CategoryTheory.Functor.cover_lift`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_aux ⦃X : D⦄ (R : Sieve X) (hR : R ∈ K X)
    ⦃u : Φ.fiber.Elements⦄ (f : (CategoryOfElements.π Φ.fiber ⋙ F).obj u ⟶ X) :
    ∃ (Y : D) (g : Y ⟶ X) (_ : R.arrows g) (v : Φ.fiber.Elements)
      (q : v ⟶ u) (a : F.obj v.fst ⟶ Y), a ≫ g = F.map q.1 ≫ f := by
  obtain ⟨U, u⟩ := u
  dsimp at f ⊢
  obtain ⟨V, g, hg, v, rfl⟩ :=
    Φ.jointly_surjective _ (F.cover_lift J K (K.pullback_stable f hR)) u
  exact ⟨_, F.map g ≫ f, hg, Φ.fiber.elementsMk _ v, ⟨g, rfl⟩, 𝟙 _, by simp⟩

variable [LocallySmall.{w} D]

/-- The image of a point of a site by a cocontinuous functor. -/
/-
**CategoryTheory.GrothendieckTopology.Point.map** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.GrothendieckTopology.Point`。
形式化陈述：map : Point.{w} K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.initiallySmall`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopol
ogy C} (self : J.Point),   CategoryTheory.Init…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.isCofiltered`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} (self : J.Point),   CategoryTheory.IsCo…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.map_aux`：map_aux ⦃X : D⦄ (R : 
Sieve X) (hR : R in K X) ⦃u : Φ.fiber.Elements⦄ (f : (CategoryOfElements.π Φ.fib
er ⋙ F).obj u ⟶ X) : exists (Y : D) (g …

--- 原说明 ---
The image of a point of a site by a cocontinuous functor.
-/
noncomputable def map : Point.{w} K :=
  Point.ofIsCofiltered.{w} (CategoryOfElements.π Φ.fiber ⋙ F) (Φ.map_aux F K)

variable {A : Type u''} [Category.{v''} A] [HasColimitsOfSize.{w, w} A]

/-- Given a cocontinuous functor `F : C ⥤ D` between sites `(C, J)` and `(D, K)`,
`P` a presheaf on `D`, `X : C`, `x : Φ.fiber.obj X`, this is the canonical morphism
`P.obj (op (F.obj X)) ⟶ (Φ.map F K).presheafFiber.obj P`, which is part
of the colimit cocone `presheafFiberMapCocone`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiberMap** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiberMap (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X) : P.obj (op (
F.obj X)) ⟶ (Φ.map F K).presheafFiber.obj P
参数：P : Dᵒᵖ ⥤ A；X : C；x : Φ.fiber.obj X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.initiallySmall`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopol
ogy C} (self : J.Point),   CategoryTheory.Init…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.isCofiltered`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} (self : J.Point),   CategoryTheory.IsCo…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.map_aux`：map_aux ⦃X : D⦄ (R : 
Sieve X) (hR : R in K X) ⦃u : Φ.fiber.Elements⦄ (f : (CategoryOfElements.π Φ.fib
er ⋙ F).obj u ⟶ X) : exists (Y : D) (g …

--- 原说明 ---
Given a cocontinuous functor `F : C ⥤ D` between sites `(C, J)` and `(D, K)`,
`P` a presheaf on `D`, `X : C`, `x : Φ.fiber.obj X`, this is the canonical morph
ism
`P.obj (op (F.obj X)) ⟶ (Φ.map F K).presheafFiber.obj P`, which is part
of the colimit cocone `presheafFiberMapCocone`.
-/
noncomputable def toPresheafFiberMap (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X) :
    P.obj (op (F.obj X)) ⟶ (Φ.map F K).presheafFiber.obj P :=
  toPresheafFiberOfIsCofiltered _ (Φ.map_aux F K) (Φ.fiber.elementsMk X x) P

@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiberMap_w** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiberMap_w {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) (P : Dᵒᵖ ⥤ 
A) : P.map (F.map f).op ≫ Φ.toPresheafFiberMap F K P X x = Φ.toPresheafFiberMap 
F K P Y (Φ.fiber.map f x)
参数：f : X ⟶ Y；x : Φ.fiber.obj X；P : Dᵒᵖ ⥤ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered_
w`：toPresheafFiberOfIsCofiltered_w {V U : N} (f : V ⟶ U) (P : Cᵒᵖ ⥤ A) : P.map (
p.map f).op ≫ toPresheafFiberOfIsCofiltered p hp V P = toPreshe…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.initiallySmall`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopol
ogy C} (self : J.Point),   CategoryTheory.Init…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.isCofiltered`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} (self : J.Point),   CategoryTheory.IsCo…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.map_aux`：map_aux ⦃X : D⦄ (R : 
Sieve X) (hR : R in K X) ⦃u : Φ.fiber.Elements⦄ (f : (CategoryOfElements.π Φ.fib
er ⋙ F).obj u ⟶ X) : exists (Y : D) (g …
-/
lemma toPresheafFiberMap_w {X Y : C} (f : X ⟶ Y)
    (x : Φ.fiber.obj X) (P : Dᵒᵖ ⥤ A) :
    P.map (F.map f).op ≫ Φ.toPresheafFiberMap F K P X x =
      Φ.toPresheafFiberMap F K P Y (Φ.fiber.map f x) :=
  toPresheafFiberOfIsCofiltered_w _ (Φ.map_aux F K)
    (V := ⟨X, x⟩) (U := ⟨Y, Φ.fiber.map f x⟩) ⟨f, rfl⟩ P

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiberMap_naturality** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiberMap_naturality {P Q : Dᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.f
iber.obj X) : Φ.toPresheafFiberMap F K P X x ≫ (Φ.map F K).presheafFiber.map g =
 g.app _ ≫ Φ.toPresheafFiberMap F K Q X x
参数：g : P ⟶ Q；X : C；x : Φ.fiber.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered_
naturality`：toPresheafFiberOfIsCofiltered_naturality {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q)
 (U : N) : toPresheafFiberOfIsCofiltered p hp U P ≫ (ofIsCofiltered p hp…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.initiallySmall`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopol
ogy C} (self : J.Point),   CategoryTheory.Init…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.isCofiltered`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} (self : J.Point),   CategoryTheory.IsCo…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.map_aux`：map_aux ⦃X : D⦄ (R : 
Sieve X) (hR : R in K X) ⦃u : Φ.fiber.Elements⦄ (f : (CategoryOfElements.π Φ.fib
er ⋙ F).obj u ⟶ X) : exists (Y : D) (g …
-/
lemma toPresheafFiberMap_naturality {P Q : Dᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiberMap F K P X x ≫ (Φ.map F K).presheafFiber.map g =
      g.app _ ≫ Φ.toPresheafFiberMap F K Q X x :=
  toPresheafFiberOfIsCofiltered_naturality _ _ _ _

set_option backward.defeqAttrib.useBackward true in
/-- Given a cocontinuous functor `F : C ⥤ D` between sites `(C, J)` and `(D, K)`,
`P` a presheaf on `D`, this is the (colimit) cocone which expresses
`(Φ.map F K).presheafFiber.obj P` as a colimit of `P.obj (op (F.obj X))`
for `X : C`, `x : Φ.fiber.obj X`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Point.presheafFiberMapCocone** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：presheafFiberMapCocone (P : Dᵒᵖ ⥤ A) : Cocone ((CategoryOfElements.π Φ.fib
er).op ⋙ F.op ⋙ P) where pt
参数：P : Dᵒᵖ ⥤ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cocontinuous functor `F : C ⥤ D` between sites `(C, J)` and `(D, K)`,
`P` a presheaf on `D`, this is the (colimit) cocone which expresses
`(Φ.map F K).presheafFiber.obj P` as a colimit of `P.obj (op (F.obj X))`
for `X : C`, `x : Φ.fiber.obj X`.
-/
noncomputable def presheafFiberMapCocone (P : Dᵒᵖ ⥤ A) :
    Cocone ((CategoryOfElements.π Φ.fiber).op ⋙ F.op ⋙ P) where
  pt := (Φ.map F K).presheafFiber.obj P
  ι.app x := Φ.toPresheafFiberMap F K P x.unop.1 x.unop.2

/-- Given a cocontinuous functor `F : C ⥤ D` between sites `(C, J)` and `(D, K)`,
`P` a presheaf on `D`, then `(Φ.map F K).presheafFiber.obj P` is a colimit
of `P.obj (op (F.obj X))` for `X : C`, `x : Φ.fiber.obj X`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.isColimitPresheafFiberMapCocone** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：isColimitPresheafFiberMapCocone (P : Dᵒᵖ ⥤ A) : IsColimit (Φ.presheafFiber
MapCocone F K P)
参数：P : Dᵒᵖ ⥤ A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.initiallySmall`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopol
ogy C} (self : J.Point),   CategoryTheory.Init…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.isCofiltered`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} (self : J.Point),   CategoryTheory.IsCo…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.map_aux`：map_aux ⦃X : D⦄ (R : 
Sieve X) (hR : R in K X) ⦃u : Φ.fiber.Elements⦄ (f : (CategoryOfElements.π Φ.fib
er ⋙ F).obj u ⟶ X) : exists (Y : D) (g …

--- 原说明 ---
Given a cocontinuous functor `F : C ⥤ D` between sites `(C, J)` and `(D, K)`,
`P` a presheaf on `D`, then `(Φ.map F K).presheafFiber.obj P` is a colimit
of `P.obj (op (F.obj X))` for `X : C`, `x : Φ.fiber.obj X`.
-/
noncomputable def isColimitPresheafFiberMapCocone (P : Dᵒᵖ ⥤ A) :
    IsColimit (Φ.presheafFiberMapCocone F K P) :=
  isColimitPresheafFiberOfIsCofilteredCocone.{w} _ (Φ.map_aux F K) P

@[ext]
/-
**CategoryTheory.GrothendieckTopology.Point.presheafFiberMap_hom_ext** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：presheafFiberMap_hom_ext {P : Dᵒᵖ ⥤ A} {T : A} {f g : (Φ.map F K).presheaf
Fiber.obj P ⟶ T} (h : forall (X : C) (x : Φ.fiber.obj X), Φ.toPresheafFiberMap F
 K P X x ≫ f = Φ.toPresheafFiberMap F K P X x ≫ g) : f = g
参数：Φ.map F K；h : forall (X : C) (x : Φ.fiber.obj X), Φ.toPresheafFiberMap F K P 
X x ≫ f = Φ.toPresheafFiberMap F K P X x ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
-/
lemma presheafFiberMap_hom_ext {P : Dᵒᵖ ⥤ A} {T : A}
    {f g : (Φ.map F K).presheafFiber.obj P ⟶ T}
    (h : ∀ (X : C) (x : Φ.fiber.obj X),
      Φ.toPresheafFiberMap F K P X x ≫ f = Φ.toPresheafFiberMap F K P X x ≫ g) :
    f = g :=
  (Φ.isColimitPresheafFiberMapCocone F K P).hom_ext (fun _ ↦ h _ _)

/-- Relation between the fiber functors on presheaves for the points `Φ.map F K`
and `Φ`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.presheafFiberMapObjIso** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：presheafFiberMapObjIso (P : Dᵒᵖ ⥤ A) : (Φ.map F K).presheafFiber.obj P ≅ Φ
.presheafFiber.obj (F.op ⋙ P)
参数：P : Dᵒᵖ ⥤ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Relation between the fiber functors on presheaves for the points `Φ.map F K`
and `Φ`.
-/
noncomputable def presheafFiberMapObjIso (P : Dᵒᵖ ⥤ A) :
    (Φ.map F K).presheafFiber.obj P ≅ Φ.presheafFiber.obj (F.op ⋙ P) :=
  IsColimit.coconePointUniqueUpToIso (Φ.isColimitPresheafFiberMapCocone F K P)
    (Φ.isColimitPresheafFiberCocone (F.op ⋙ P))

@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiberMap_presheafFiberMapO
bjIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiberMap_presheafFiberMapObjIso_hom (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ
.fiber.obj X) : Φ.toPresheafFiberMap F K P X x ≫ (Φ.presheafFiberMapObjIso F K P
).hom = Φ.toPresheafFiber X x (F.op ⋙ P)
参数：P : Dᵒᵖ ⥤ A；X : C；x : Φ.fiber.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
lemma toPresheafFiberMap_presheafFiberMapObjIso_hom (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiberMap F K P X x ≫ (Φ.presheafFiberMapObjIso F K P).hom =
      Φ.toPresheafFiber X x (F.op ⋙ P) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (Φ.isColimitPresheafFiberMapCocone F K P) _ ⟨X, x⟩

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_presheafFiberMapObjI
so_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiber_presheafFiberMapObjIso_inv (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fi
ber.obj X) : Φ.toPresheafFiber X x (F.op ⋙ P) ≫ (Φ.presheafFiberMapObjIso F K P)
.inv = Φ.toPresheafFiberMap F K P X x
参数：P : Dᵒᵖ ⥤ A；X : C；x : Φ.fiber.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiberMap_presheafFib
erMapObjIso_hom`：toPresheafFiberMap_presheafFiberMapObjIso_hom (P : Dᵒᵖ ⥤ A) (X 
: C) (x : Φ.fiber.obj X) : Φ.toPresheafFiberMap F K P X x ≫ (Φ.presheafFiberM…
-/
lemma toPresheafFiber_presheafFiberMapObjIso_inv (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x (F.op ⋙ P) ≫ (Φ.presheafFiberMapObjIso F K P).inv =
      Φ.toPresheafFiberMap F K P X x := by
  simpa [-toPresheafFiberMap_presheafFiberMapObjIso_hom] using
    (Φ.toPresheafFiberMap_presheafFiberMapObjIso_hom F K ..).symm =≫
      (Φ.presheafFiberMapObjIso F K P).inv

set_option backward.isDefEq.respectTransparency false in
variable (A) in
/-- Relation between the fiber functors on presheaves for the points `Φ.map F K`
and `Φ` when `F : C ⥤ D` is a cocontinuous functor between sites `(C, J)` and `(D, K)`. -/
@[simps!]
/-
**CategoryTheory.GrothendieckTopology.Point.presheafFiberMapIso** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：presheafFiberMapIso : (Φ.map F K).presheafFiber ≅ (Functor.whiskeringLeft 
_ _ A).obj F.op ⋙ Φ.presheafFiber
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Relation between the fiber functors on presheaves for the points `Φ.map F K`
and `Φ` when `F : C ⥤ D` is a cocontinuous functor between sites `(C, J)` and `(
D, K)`.
-/
noncomputable def presheafFiberMapIso :
    (Φ.map F K).presheafFiber ≅
      (Functor.whiskeringLeft _ _ A).obj F.op ⋙ Φ.presheafFiber :=
  NatIso.ofComponents (Φ.presheafFiberMapObjIso F K)

variable (A) in
/-- Relation between the fiber functors on presheaves for the points `Φ.map F K`
and `Φ` when `F : C ⥤ D` is a cocontinuous and continuous functor between
sites `(C, J)` and `(D, K)`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.sheafFiberMapIso** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：sheafFiberMapIso [Functor.IsContinuous F J K] : (Φ.map F K).sheafFiber ≅ F
.sheafPushforwardContinuous A J K ⋙ Φ.sheafFiber
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Relation between the fiber functors on presheaves for the points `Φ.map F K`
and `Φ` when `F : C ⥤ D` is a cocontinuous and continuous functor between
sites `(C, J)` and `(D, K)`.
-/
noncomputable def sheafFiberMapIso [Functor.IsContinuous F J K] :
    (Φ.map F K).sheafFiber ≅
      F.sheafPushforwardContinuous A J K ⋙ Φ.sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf K A) (Φ.presheafFiberMapIso F K A) ≪≫
    (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight (F.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm _ ≪≫
    Functor.associator ..

end GrothendieckTopology.Point

end CategoryTheory

