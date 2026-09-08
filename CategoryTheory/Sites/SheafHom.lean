/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Over

/-! # Internal hom of sheaves

In this file, given two sheaves `F` and `G` on a site `(C, J)` with values
in a category `A`, we define a sheaf of types
`sheafHom F G` which sends `X : C` to the type of morphisms
between the restrictions of `F` and `G` to the categories `Over X`.

We first define `presheafHom F G` when `F` and `G` are
presheaves `Cᵒᵖ ⥤ A` and show that it is a sheaf when `G` is a sheaf.

TODO:
- turn both `presheafHom` and `sheafHom` into bifunctors
- for a sheaf of types `F`, the `sheafHom` functor from `F` is right-adjoint to
  the product functor with `F`, i.e. for all `X` and `Y`, there is a
  natural bijection `(X ⨯ F ⟶ Y) ≃ (X ⟶ sheafHom F Y)`.
- use these results in order to show that the category of sheaves of types is Cartesian closed

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Category Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

variable (F G : Cᵒᵖ ⥤ A)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given two presheaves `F` and `G` on a category `C` with values in a category `A`,
this `presheafHom F G` is the presheaf of types which sends an object `X : C`
to the type of morphisms between the "restrictions" of `F` and `G` to the category `Over X`. -/
@[simps! obj]
/-
**CategoryTheory.presheafHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：presheafHom : Cᵒᵖ ⥤ Type _ where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two presheaves `F` and `G` on a category `C` with values in a category `A`
,
this `presheafHom F G` is the presheaf of types which sends an object `X : C`
to the type of morphisms between the "restrictions" of `F` and `G` to the catego
ry `Over X`.
-/
def presheafHom : Cᵒᵖ ⥤ Type _ where
  obj X := (Over.forget X.unop).op ⋙ F ⟶ (Over.forget X.unop).op ⋙ G
  map f := ↾(Functor.whiskerLeft (Over.map f.unop).op)
  map_id := by
    rintro ⟨X⟩
    ext φ ⟨Y⟩
    simpa [Over.mapId] using φ.naturality ((Over.mapId X).hom.app Y).op
  map_comp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f : Y ⟶ X⟩ ⟨g : Z ⟶ Y⟩
    ext φ ⟨W⟩
    simpa [Over.mapComp] using φ.naturality ((Over.mapComp g f).hom.app W).op

variable {F G}

/-- Equational lemma for the presheaf structure on `presheafHom`.
It is advisable to use this lemma rather than `dsimp [presheafHom]` which may result
in the need to prove equalities of objects in an `Over` category. -/
/-
**CategoryTheory.presheafHom_map_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：presheafHom_map_app {X Y Z : C} (f : Z ⟶ Y) (g : Y ⟶ X) (h : Z ⟶ X) (w : f
 ≫ g = h) (α : (presheafHom F G).obj (op X)) : ((presheafHom F G).map g.op α).ap
p (op (Over.mk f)) = α.app (op (Over.mk h))
参数：f : Z ⟶ Y；g : Y ⟶ X；h : Z ⟶ X；w : f ≫ g = h；α : (presheafHom F G).obj (op X)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equational lemma for the presheaf structure on `presheafHom`.
It is advisable to use this lemma rather than `dsimp [presheafHom]` which may re
sult
in the need to prove equalities of objects in an `Over` category.
-/
lemma presheafHom_map_app {X Y Z : C} (f : Z ⟶ Y) (g : Y ⟶ X) (h : Z ⟶ X) (w : f ≫ g = h)
    (α : (presheafHom F G).obj (op X)) :
    ((presheafHom F G).map g.op α).app (op (Over.mk f)) =
      α.app (op (Over.mk h)) := by
  subst w
  rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.presheafHom_map_app_op_mk_id** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：presheafHom_map_app_op_mk_id {X Y : C} (g : Y ⟶ X) (α : (presheafHom F G).
obj (op X)) : dsimp% ((presheafHom F G).map g.op α).app (op (Over.mk (𝟙 Y))) = α
.app (op (Over.mk g))
参数：g : Y ⟶ X；α : (presheafHom F G).obj (op X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.presheafHom_map_app`：presheafHom_map_app {X Y Z : C} (f :
 Z ⟶ Y) (g : Y ⟶ X) (h : Z ⟶ X) (w : f ≫ g = h) (α : (presheafHom F G).obj (op X
)) : ((presheafHom F G).…
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
lemma presheafHom_map_app_op_mk_id {X Y : C} (g : Y ⟶ X)
    (α : (presheafHom F G).obj (op X)) :
    dsimp% ((presheafHom F G).map g.op α).app (op (Over.mk (𝟙 Y))) =
      α.app (op (Over.mk g)) :=
  presheafHom_map_app (𝟙 Y) g g (by simp) α

variable (F G)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The sections of the presheaf `presheafHom F G` identify to morphisms `F ⟶ G`. -/
/-
**CategoryTheory.presheafHomSectionsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory`。
形式化陈述：presheafHomSectionsEquiv : (presheafHom F G).sections ≃ (F ⟶ G) where toFu
n s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sections of the presheaf `presheafHom F G` identify to morphisms `F ⟶ G`.
-/
def presheafHomSectionsEquiv : (presheafHom F G).sections ≃ (F ⟶ G) where
  toFun s :=
    { app := fun X => (s.1 X).app ⟨Over.mk (𝟙 _)⟩
      naturality := by
        rintro ⟨X₁⟩ ⟨X₂⟩ ⟨f : X₂ ⟶ X₁⟩
        dsimp
        refine Eq.trans ?_ ((s.1 ⟨X₁⟩).naturality
          (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 X₁)).op)
        rw [← s.2 f.op]
        dsimp
        rw [presheafHom_map_app_op_mk_id]
        rfl }
  invFun f := ⟨fun _ => Functor.whiskerLeft _ f, fun _ => rfl⟩
  left_inv s := by
    dsimp
    ext ⟨X⟩ ⟨Y : Over X⟩
    have H := s.2 Y.hom.op
    dsimp at H ⊢
    rw [← H]
    apply presheafHom_map_app_op_mk_id

variable {F G}

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.PresheafHom.isAmalgamation_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.PresheafHom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} A]   {F G : CategoryTheory.Functor Cᵒᵖ A
} {X : C} (S : CategoryTheory.Sieve X)   (x : CategoryTheory.Presieve.FamilyOfEl
ements (CategoryTheory.presheafHom F G) S.arrows),   x.Compatible →     ∀ (y : (
CategoryTheory.presheafHom F G).obj (Opposite.op X)),       x.IsAmalgamation y ↔
         ∀ (Y : C) (g : Y ⟶ X) (hg : S.arrows g),           y.app (Opposite.op (
CategoryTheory.Over.mk g)) =             (x g hg).app (Opposite.op (CategoryTheo
ry.Over.mk (CategoryTheory.CategoryStruct.id Y)))
参数：S : CategoryTheory.Sieve X；x : CategoryTheory.Presieve.FamilyOfElements (Cate
goryTheory.presheafHom F G) S.arrows；y : (CategoryTheory.presheafHom F G).obj (O
pposite.op X)；Y : C；g : Y ⟶ X；hg : S.arrows g；Opposite.op (CategoryTheory.Over.m
k g)；x g hg；Opposite.op (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.i
d Y))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.presheafHom_map_app_op_mk_id`：presheafHom_map_app_op_mk_i
d {X Y : C} (g : Y ⟶ X) (α : (presheafHom F G).obj (op X)) : dsimp% ((presheafHo
m F G).map g.op α).app (op (Over.…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用引理 `CategoryTheory.presheafHom_map_app`：presheafHom_map_app {X Y Z : C} (f :
 Z ⟶ Y) (g : Y ⟶ X) (h : Z ⟶ X) (w : f ≫ g = h) (α : (presheafHom F G).obj (op X
)) : ((presheafHom F G).…
-/
lemma PresheafHom.isAmalgamation_iff {X : C} (S : Sieve X)
    (x : Presieve.FamilyOfElements (presheafHom F G) S.arrows)
    (hx : x.Compatible) (y : (presheafHom F G).obj (op X)) :
    x.IsAmalgamation y ↔ ∀ (Y : C) (g : Y ⟶ X) (hg : S g),
      y.app (op (Over.mk g)) = (x g hg).app (op (Over.mk (𝟙 Y))) := by
  constructor
  · intro h Y g hg
    rw [← h g hg]
    dsimp
    rw [presheafHom_map_app_op_mk_id]
  · intro h Y g hg
    dsimp
    ext ⟨W : Over Y⟩
    refine (h W.left (W.hom ≫ g) (S.downward_closed hg _)).trans ?_
    have H := hx (𝟙 _) W.hom (S.downward_closed hg W.hom) hg (by simp)
    simp only [op_id, Functor.map_id, id_apply] at H
    rw [H, presheafHom_map_app _ _ W.hom (by simp)]
    rfl

section

variable {X : C} {S : Sieve X}
    (hG : ∀ ⦃Y : C⦄ (f : Y ⟶ X), IsLimit (G.mapCone (S.pullback f).arrows.cocone.op))

namespace PresheafHom.IsSheafFor

variable (x : Presieve.FamilyOfElements (presheafHom F G) S.arrows) {Y : C}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
include hG in
/-
**CategoryTheory.PresheafHom.IsSheafFor.exists_app** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.PresheafHom.IsSheafFor`。
形式化陈述：exists_app (hx : x.Compatible) (g : Y ⟶ X) : exists (φ : F.obj (op Y) ⟶ G.
obj (op Y)), forall {Z : C} (p : Z ⟶ Y) (hp : S (p ≫ g)), φ ≫ G.map p.op = F.map
 p.op ≫ (x (p ≫ g) hp).app ⟨Over.mk (𝟙 Z)⟩
参数：hx : x.Compatible；g : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Over.w_assoc`：∀ {T : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} T] {X : T} {f g : CategoryTheory.Over X} (φ : f ⟶ g) {Z : T}   (h 
: X ⟶ Z),   Categ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用引理 `CategoryTheory.presheafHom_map_app_op_mk_id`：presheafHom_map_app_op_mk_i
d {X Y : C} (g : Y ⟶ X) (α : (presheafHom F G).obj (op X)) : dsimp% ((presheafHo
m F G).map g.op α).app (op (Over.…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
lemma exists_app (hx : x.Compatible) (g : Y ⟶ X) :
    ∃ (φ : F.obj (op Y) ⟶ G.obj (op Y)),
      ∀ {Z : C} (p : Z ⟶ Y) (hp : S (p ≫ g)), φ ≫ G.map p.op =
        F.map p.op ≫ (x (p ≫ g) hp).app ⟨Over.mk (𝟙 Z)⟩ := by
  let c : Cone ((Presieve.diagram (Sieve.pullback g S).arrows).op ⋙ G) :=
    { pt := F.obj (op Y)
      π :=
        { app := fun ⟨Z, hZ⟩ => F.map Z.hom.op ≫ (x _ hZ).app (op (Over.mk (𝟙 _)))
          naturality := by
            rintro ⟨Z₁, hZ₁⟩ ⟨Z₂, hZ₂⟩ ⟨⟨f : Z₂ ⟶ Z₁⟩⟩
            dsimp
            rw [id_comp, assoc]
            have H := hx f.left (𝟙 _) hZ₁ hZ₂ (by simp)
            simp only [op_id, Functor.map_id, id_apply] at H
            let φ : Over.mk f.left ⟶ Over.mk (𝟙 Z₁.left) := Over.homMk f.left
            have H' := (x (Z₁.hom ≫ g) hZ₁).naturality φ.op
            dsimp at H H' ⊢
            erw [← H, ← H', presheafHom_map_app_op_mk_id, ← F.map_comp_assoc,
              ← op_comp, Over.w f] } }
  use (hG g).lift c
  intro Z p hp
  exact ((hG g).fac c ⟨Over.mk p, hp⟩)

/-- Auxiliary definition for `presheafHom_isSheafFor`. -/
/-
**CategoryTheory.PresheafHom.IsSheafFor.app** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.PresheafHom.IsSheafFor`。
形式化陈述：app (hx : x.Compatible) (g : Y ⟶ X) : F.obj (op Y) ⟶ G.obj (op Y)
参数：hx : x.Compatible；g : Y ⟶ X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.PresheafHom.IsSheafFor.exists_app`：exists_app (hx : x.Com
patible) (g : Y ⟶ X) : exists (φ : F.obj (op Y) ⟶ G.obj (op Y)), forall {Z : C} 
(p : Z ⟶ Y) (hp : S (p ≫ g)), φ ≫ G.ma…

--- 原说明 ---
Auxiliary definition for `presheafHom_isSheafFor`.
-/
noncomputable def app (hx : x.Compatible) (g : Y ⟶ X) : F.obj (op Y) ⟶ G.obj (op Y) :=
  (exists_app hG x hx g).choose
/-
**CategoryTheory.PresheafHom.IsSheafFor.app_cond** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.PresheafHom.IsSheafFor`。
形式化陈述：app_cond (hx : x.Compatible) (g : Y ⟶ X) {Z : C} (p : Z ⟶ Y) (hp : S (p ≫ 
g)) : app hG x hx g ≫ G.map p.op = F.map p.op ≫ (x (p ≫ g) hp).app ⟨Over.mk (𝟙 Z
)⟩
参数：hx : x.Compatible；g : Y ⟶ X；p : Z ⟶ Y；hp : S (p ≫ g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `CategoryTheory.PresheafHom.IsSheafFor.exists_app`：exists_app (hx : x.Com
patible) (g : Y ⟶ X) : exists (φ : F.obj (op Y) ⟶ G.obj (op Y)), forall {Z : C} 
(p : Z ⟶ Y) (hp : S (p ≫ g)), φ ≫ G.ma…
-/
lemma app_cond (hx : x.Compatible) (g : Y ⟶ X) {Z : C} (p : Z ⟶ Y) (hp : S (p ≫ g)) :
    app hG x hx g ≫ G.map p.op = F.map p.op ≫ (x (p ≫ g) hp).app ⟨Over.mk (𝟙 Z)⟩ :=
  (exists_app hG x hx g).choose_spec p hp

end PresheafHom.IsSheafFor

variable (F G S)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hG in
open PresheafHom.IsSheafFor in
/-
**CategoryTheory.presheafHom_isSheafFor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y`。
形式化陈述：presheafHom_isSheafFor : Presieve.IsSheafFor (presheafHom F G) S.arrows
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_of_exists_of_unique`：existsUnique_of_exists_of_unique {p : 
α -> Prop} (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y
₂) : exists! x, p x
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.PresheafHom.IsSheafFor.app_cond`：app_cond (hx : x.Compati
ble) (g : Y ⟶ X) {Z : C} (p : Z ⟶ Y) (hp : S (p ≫ g)) : app hG x hx g ≫ G.map p.
op = F.map p.op ≫ (x (p ≫ g) hp).app…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.PresheafHom.isAmalgamation_iff`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {A : Type u'} [inst_1 : CategoryTheory.Category.
{v', u'} A]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.op_id`：op_id {X : C} : (𝟙 X).op = 𝟙 (op X)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma presheafHom_isSheafFor :
    Presieve.IsSheafFor (presheafHom F G) S.arrows := by
  intro x hx
  apply existsUnique_of_exists_of_unique
  · refine ⟨
      { app := fun Y => app hG x hx Y.unop.hom
        naturality := by
          rintro ⟨Y₁ : Over X⟩ ⟨Y₂ : Over X⟩ ⟨φ : Y₂ ⟶ Y₁⟩
          apply (hG Y₂.hom).hom_ext
          rintro ⟨Z : Over Y₂.left, hZ⟩
          dsimp
          rw [assoc, assoc, app_cond hG x hx Y₂.hom Z.hom hZ, ← G.map_comp, ← op_comp]
          rw [app_cond hG x hx Y₁.hom (Z.hom ≫ φ.left) (by simpa using hZ),
            ← F.map_comp_assoc, op_comp]
          congr 3
          simp }, ?_⟩
    rw [PresheafHom.isAmalgamation_iff _ _ hx]
    intro Y g hg
    dsimp
    have H := app_cond hG x hx g (𝟙 _) (by simpa using hg)
    rw [op_id, G.map_id, comp_id, F.map_id, id_comp] at H
    exact H.trans (by congr; simp)
  · intro y₁ y₂ hy₁ hy₂
    rw [PresheafHom.isAmalgamation_iff _ _ hx] at hy₁ hy₂
    apply NatTrans.ext
    ext ⟨Y : Over X⟩
    apply (hG Y.hom).hom_ext
    rintro ⟨Z : Over Y.left, hZ⟩
    dsimp
    let φ : Over.mk (Z.hom ≫ Y.hom) ⟶ Y := Over.homMk Z.hom
    refine (y₁.naturality φ.op).symm.trans (Eq.trans ?_ (y₂.naturality φ.op))
    rw [(hy₁ _ _ hZ), ← ((hy₂ _ _ hZ))]

end

variable (F G)

/-
**CategoryTheory.Presheaf.IsSheaf.hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Presheaf.IsSheaf`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C} {A : Type u'}   [inst_1 : CategoryTheory.Category.{v'
, u'} A] (F G : CategoryTheory.Functor Cᵒᵖ A),   CategoryTheory.Presheaf.IsSheaf
 J G → CategoryTheory.Presheaf.IsSheaf J (CategoryTheory.presheafHom F G)
参数：F G : CategoryTheory.Functor Cᵒᵖ A；CategoryTheory.presheafHom F G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用引理 `CategoryTheory.presheafHom_isSheafFor`：presheafHom_isSheafFor : Presieve
.IsSheafFor (presheafHom F G) S.arrows
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_isLimit`：isSheaf_iff_isLimit : IsShe
af J P ↔ forall ⦃X : C⦄ (S : Sieve X), S in J X -> Nonempty (IsLimit (P.mapCone 
S.arrows.cocone.op))
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
-/
lemma Presheaf.IsSheaf.hom (hG : Presheaf.IsSheaf J G) :
    Presheaf.IsSheaf J (presheafHom F G) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS
  exact presheafHom_isSheafFor F G S
    (fun _ _ => ((Presheaf.isSheaf_iff_isLimit J G).1 hG _ (J.pullback_stable _ hS)).some)


/-- The underlying presheaf of `sheafHom F G`. It is isomorphic to `presheafHom F.1 G.1`
(see `sheafHom'Iso`), but has better definitional properties. -/
/-
**CategoryTheory.sheafHom'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafHom' (F G : Sheaf J A) : Cᵒᵖ ⥤ Type _ where obj X
参数：F G : Sheaf J A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying presheaf of `sheafHom F G`. It is isomorphic to `presheafHom F.1 
G.1`
(see `sheafHom'Iso`), but has better definitional properties.
-/
def sheafHom' (F G : Sheaf J A) : Cᵒᵖ ⥤ Type _ where
  obj X := ((J.overPullback A X.unop).obj F ⟶ (J.overPullback A X.unop).obj G)
  map f := ↾((J.overMapPullback A f.unop).map)
  map_id X := by
    ext φ : 4
    exact ConcreteCategory.congr_hom ((presheafHom F.1 G.1).map_id X) φ.1
  map_comp f g := by
    ext φ : 4
    exact ConcreteCategory.congr_hom ((presheafHom F.1 G.1).map_comp f g) φ.1

/-- The canonical isomorphism `sheafHom' F G ≅ presheafHom F.1 G.1`. -/
/-
**CategoryTheory.sheafHom'Iso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       {A : Type u'} →         [inst_1 : Cat
egoryTheory.Category.{v', u'} A] →           (F G : CategoryTheory.Sheaf J A) → 
CategoryTheory.sheafHom' F G ≅ CategoryTheory.presheafHom F.obj G.obj
参数：F G : CategoryTheory.Sheaf J A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `sheafHom' F G ≅ presheafHom F.1 G.1`.
-/
def sheafHom'Iso (F G : Sheaf J A) :
    sheafHom' F G ≅ presheafHom F.1 G.1 :=
  NatIso.ofComponents
    (fun _ => Sheaf.homEquiv.toIso) (fun _ => rfl)

/-- Given two sheaves `F` and `G` on a site `(C, J)` with values in a category `A`,
this `sheafHom F G` is the sheaf of types which sends an object `X : C`
to the type of morphisms between the "restrictions" of `F` and `G` to the category `Over X`. -/
/-
**CategoryTheory.sheafHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafHom (F G : Sheaf J A) : Sheaf J (Type _) where obj
参数：F G : Sheaf J A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two sheaves `F` and `G` on a site `(C, J)` with values in a category `A`,
this `sheafHom F G` is the sheaf of types which sends an object `X : C`
to the type of morphisms between the "restrictions" of `F` and `G` to the catego
ry `Over X`.
-/
def sheafHom (F G : Sheaf J A) : Sheaf J (Type _) where
  obj := sheafHom' F G
  property := (Presheaf.isSheaf_of_iso_iff (sheafHom'Iso F G)).2 (G.2.hom F.1)

set_option backward.isDefEq.respectTransparency.types false in
/-- The sections of the sheaf `sheafHom F G` identify to morphisms `F ⟶ G`. -/
/-
**CategoryTheory.sheafHomSectionsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：sheafHomSectionsEquiv (F G : Sheaf J A) : (sheafHom F G).1.sections ≃ (F ⟶
 G)
参数：F G : Sheaf J A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The sections of the sheaf `sheafHom F G` identify to morphisms `F ⟶ G`.
-/
def sheafHomSectionsEquiv (F G : Sheaf J A) :
    (sheafHom F G).1.sections ≃ (F ⟶ G) :=
  ((Functor.sectionsFunctor Cᵒᵖ).mapIso (sheafHom'Iso F G)).toEquiv.trans
    ((presheafHomSectionsEquiv F.1 G.1).trans Sheaf.homEquiv.symm)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.sheafHomSectionsEquiv_symm_apply_coe_apply** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory`。
形式化陈述：sheafHomSectionsEquiv_symm_apply_coe_apply {F G : Sheaf J A} (φ : F ⟶ G) (
X : Cᵒᵖ) : ((sheafHomSectionsEquiv F G).symm φ).1 X = (J.overPullback A X.unop).
map φ
参数：φ : F ⟶ G；X : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma sheafHomSectionsEquiv_symm_apply_coe_apply {F G : Sheaf J A} (φ : F ⟶ G) (X : Cᵒᵖ) :
    ((sheafHomSectionsEquiv F G).symm φ).1 X = (J.overPullback A X.unop).map φ := (rfl)

end CategoryTheory

