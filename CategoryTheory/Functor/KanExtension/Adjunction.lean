/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor

/-! # The Kan extension functor

Given a functor `L : C ⥤ D`, we define the left Kan extension functor
`L.lan : (C ⥤ H) ⥤ (D ⥤ H)` which sends a functor `F : C ⥤ H` to its
left Kan extension along `L`. This is defined if all `F` have such
a left Kan extension. It is shown that `L.lan` is the left adjoint to
the functor `(D ⥤ H) ⥤ (C ⥤ H)` given by the precomposition
with `L` (see `Functor.lanAdjunction`).

Similarly, we define the right Kan extension functor
`L.ran : (C ⥤ H) ⥤ (D ⥤ H)` which sends a functor `F : C ⥤ H` to its
right Kan extension along `L`.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) {H : Type*} [Category* H]

section lan

section

variable [∀ (F : C ⥤ H), HasLeftKanExtension L F]

/-- The left Kan extension functor `(C ⥤ H) ⥤ (D ⥤ H)` along a functor `C ⥤ D`. -/
/-
**CategoryTheory.Functor.lan** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：lan : (C ⥤ H) ⥤ (D ⥤ H) where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left Kan extension functor `(C ⥤ H) ⥤ (D ⥤ H)` along a functor `C ⥤ D`.
-/
noncomputable def lan : (C ⥤ H) ⥤ (D ⥤ H) where
  obj F := leftKanExtension L F
  map {F₁ F₂} φ := descOfIsLeftKanExtension _ (leftKanExtensionUnit L F₁) _
    (φ ≫ leftKanExtensionUnit L F₂)

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `F ⟶ L ⋙ (L.lan).obj G`. -/
/-
**CategoryTheory.Functor.lanUnit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：lanUnit : (𝟭 (C ⥤ H)) ⟶ L.lan ⋙ (whiskeringLeft C D H).obj L where app F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `F ⟶ L ⋙ (L.lan).obj G`.
-/
noncomputable def lanUnit : (𝟭 (C ⥤ H)) ⟶ L.lan ⋙ (whiskeringLeft C D H).obj L where
  app F := leftKanExtensionUnit L F
  naturality {F₁ F₂} φ := by ext; simp [lan]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ H) : (L.lan.obj F).IsLeftKanExtension (L.lanUnit.app F) := by
  dsimp [lan, lanUnit]
  infer_instance

end

/-- If there exists a pointwise left Kan extension of `F` along `L`,
then `L.lan.obj G` is a pointwise left Kan extension of `F`. -/
/-
**CategoryTheory.Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isPointwiseLeftKanExtensionLeftKanExtensionUnit (F : C ⥤ H) [HasPointwiseL
eftKanExtension L F] : (LeftExtension.mk _ (L.leftKanExtensionUnit F)).IsPointwi
seLeftKanExtension
参数：F : C ⥤ H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …

--- 原说明 ---
If there exists a pointwise left Kan extension of `F` along `L`,
then `L.lan.obj G` is a pointwise left Kan extension of `F`.
-/
noncomputable def isPointwiseLeftKanExtensionLeftKanExtensionUnit
    (F : C ⥤ H) [HasPointwiseLeftKanExtension L F] :
    (LeftExtension.mk _ (L.leftKanExtensionUnit F)).IsPointwiseLeftKanExtension :=
  isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _ (leftKanExtensionUnit L F)

section

open CostructuredArrow

variable (F : C ⥤ H) [HasPointwiseLeftKanExtension L F]

/-- If a left Kan extension is pointwise, then evaluating it at an object is isomorphic to
taking a colimit. -/
/-
**CategoryTheory.Functor.leftKanExtensionObjIsoColimit** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：leftKanExtensionObjIsoColimit [HasLeftKanExtension L F] (X : D) : (L.leftK
anExtension F).obj X ≅ colimit (proj L X ⋙ F)
参数：X : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …

--- 原说明 ---
If a left Kan extension is pointwise, then evaluating it at an object is isomorp
hic to
taking a colimit.
-/
noncomputable def leftKanExtensionObjIsoColimit [HasLeftKanExtension L F] (X : D) :
    (L.leftKanExtension F).obj X ≅ colimit (proj L X ⋙ F) :=
  LeftExtension.IsPointwiseLeftKanExtensionAt.isoColimit (F := F)
    (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_leftKanExtensionObjIsoColimit_inv [HasLeftKanExtension L F] (X : D)
    (f : CostructuredArrow L X) :
    colimit.ι _ f ≫ (L.leftKanExtensionObjIsoColimit F X).inv =
    (L.leftKanExtensionUnit F).app f.left ≫ (L.leftKanExtension F).map f.hom := by
  simp [leftKanExtensionObjIsoColimit]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_leftKanExtensionObjIsoColimit_hom (X : D) (f : CostructuredArrow L X) :
    (L.leftKanExtensionUnit F).app f.left ≫ (L.leftKanExtension F).map f.hom ≫
      (L.leftKanExtensionObjIsoColimit F X).hom =
    colimit.ι (proj L X ⋙ F) f :=
  LeftExtension.IsPointwiseLeftKanExtensionAt.ι_isoColimit_hom (F := F)
    (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F X) f
/-
**CategoryTheory.Functor.leftKanExtensionUnit_leftKanExtension_map_leftKanExtens
ionObjIsoColimit_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：leftKanExtensionUnit_leftKanExtension_map_leftKanExtensionObjIsoColimit_ho
m (X : D) (f : CostructuredArrow L X) : (leftKanExtensionUnit L F).app f.left ≫ 
(leftKanExtension L F).map f.hom ≫ (L.leftKanExtensionObjIsoColimit F X).hom = c
olimit.ι (proj L X ⋙ F) f
参数：X : D；f : CostructuredArrow L X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.ι_iso
Colimit_hom`：ι_isoColimit_hom (g : CostructuredArrow L Y) : E.hom.app g.left ≫ E
.right.map g.hom ≫ h.isoColimit.hom = colimit.ι (CostructuredArrow.proj L…
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
-/
lemma leftKanExtensionUnit_leftKanExtension_map_leftKanExtensionObjIsoColimit_hom (X : D)
    (f : CostructuredArrow L X) :
    (leftKanExtensionUnit L F).app f.left ≫ (leftKanExtension L F).map f.hom ≫
       (L.leftKanExtensionObjIsoColimit F X).hom =
    colimit.ι (proj L X ⋙ F) f :=
  LeftExtension.IsPointwiseLeftKanExtensionAt.ι_isoColimit_hom (F := F)
    (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F X) f

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom (X : C) : (L.leftKa
nExtensionUnit F).app X ≫ (L.leftKanExtensionObjIsoColimit F (L.obj X)).hom = co
limit.ι (proj L (L.obj X) ⋙ F) (CostructuredArrow.mk (𝟙 _))
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.Functor.leftKanExtensionUnit_leftKanExtension_map_leftKan
ExtensionObjIsoColimit_hom`：leftKanExtensionUnit_leftKanExtension_map_leftKanExt
ensionObjIsoColimit_hom (X : D) (f : CostructuredArrow L X) : (leftKanExtensionU
nit L F)…
-/
lemma leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom (X : C) :
    (L.leftKanExtensionUnit F).app X ≫ (L.leftKanExtensionObjIsoColimit F (L.obj X)).hom =
    colimit.ι (proj L (L.obj X) ⋙ F) (CostructuredArrow.mk (𝟙 _)) := by
  simpa using leftKanExtensionUnit_leftKanExtension_map_leftKanExtensionObjIsoColimit_hom L F
    (L.obj X) (CostructuredArrow.mk (𝟙 _))

set_option backward.isDefEq.respectTransparency false in
@[instance]
/-
**CategoryTheory.Functor.hasColimit_map_comp_** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasColimit_map_comp_ι_comp_grothendieckProj {X Y : D} (f : X ⟶ Y) :
    HasColimit (((functor L).map f).toFunctor ⋙ Grothendieck.ι (functor L) Y ⋙
      grothendieckProj L ⋙ F) :=
  hasColimit_of_iso (isoWhiskerRight (mapCompιCompGrothendieckProj L f) F)

set_option backward.isDefEq.respectTransparency false in
/-- The left Kan extension of `F : C ⥤ H` along a functor `L : C ⥤ D` is isomorphic to the
fiberwise colimit of the projection functor on the Grothendieck construction of the costructured
arrow category composed with `F`. -/
@[simps!]
/-
**CategoryTheory.Functor.leftKanExtensionIsoFiberwiseColimit** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：leftKanExtensionIsoFiberwiseColimit [HasLeftKanExtension L F] : leftKanExt
ension L F ≅ fiberwiseColimit (grothendieckProj L ⋙ F)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.hasColimit_map_comp_ι_comp_grothendieckProj`：hasC
olimit_map_comp_ι_comp_grothendieckProj {X Y : D} (f : X ⟶ Y) : HasColimit (((fu
nctor L).map f).toFunctor ⋙ Grothendieck.ι (functor L) Y…

--- 原说明 ---
The left Kan extension of `F : C ⥤ H` along a functor `L : C ⥤ D` is isomorphic 
to the
fiberwise colimit of the projection functor on the Grothendieck construction of 
the costructured
arrow category composed with `F`.
-/
noncomputable def leftKanExtensionIsoFiberwiseColimit [HasLeftKanExtension L F] :
    leftKanExtension L F ≅ fiberwiseColimit (grothendieckProj L ⋙ F) :=
  letI : ∀ X, HasColimit (Grothendieck.ι (functor L) X ⋙ grothendieckProj L ⋙ F) :=
      fun X => hasColimit_of_iso <| Iso.symm <|
        isoWhiskerRight (eqToIso congr($((functor L).map_id X).toFunctor)) _ ≪≫
        Functor.leftUnitor (Grothendieck.ι (functor L) X ⋙ grothendieckProj L ⋙ F)
  Iso.symm <| NatIso.ofComponents
    (fun X => HasColimit.isoOfNatIso (isoWhiskerRight (ιCompGrothendieckProj L X) F) ≪≫
      (leftKanExtensionObjIsoColimit L F X).symm)
    fun f => colimit.hom_ext (by simp)

end

section HasLeftKanExtension

variable [∀ (F : C ⥤ H), HasLeftKanExtension L F]

set_option backward.isDefEq.respectTransparency false in
variable (H) in
/-- The left Kan extension functor `L.Lan` is left adjoint to the precomposition by `L`. -/
/-
**CategoryTheory.Functor.lanAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：lanAdjunction : L.lan ⊣ (whiskeringLeft C D H).obj L
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionObjLanAppLanUnit`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] (L : Categor…

--- 原说明 ---
The left Kan extension functor `L.Lan` is left adjoint to the precomposition by 
`L`.
-/
noncomputable def lanAdjunction : L.lan ⊣ (whiskeringLeft C D H).obj L :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F G => homEquivOfIsLeftKanExtension _ (L.lanUnit.app F) G
      homEquiv_naturality_left_symm := fun {F₁ F₂ G} f α =>
        hom_ext_of_isLeftKanExtension _ (L.lanUnit.app F₁) _ _ (by
          ext X
          dsimp [homEquivOfIsLeftKanExtension]
          rw [descOfIsLeftKanExtension_fac_app, NatTrans.comp_app, ← assoc]
          have h := congr_app (L.lanUnit.naturality f) X
          dsimp at h ⊢
          rw [← h, assoc, descOfIsLeftKanExtension_fac_app])
      homEquiv_naturality_right := fun {F G₁ G₂} β f => by
        dsimp [homEquivOfIsLeftKanExtension]
        rw [assoc] }

set_option backward.isDefEq.respectTransparency false in
variable (H) in
@[simp]
/-
**CategoryTheory.Functor.lanAdjunction_unit** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：lanAdjunction_unit : (L.lanAdjunction H).unit = L.lanUnit
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lanAdjunction_unit : (L.lanAdjunction H).unit = L.lanUnit := by
  ext F : 2
  dsimp [lanAdjunction, homEquivOfIsLeftKanExtension]
  simp
/-
**CategoryTheory.Functor.lanAdjunction_counit_app** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：lanAdjunction_counit_app (G : D ⥤ H) : (L.lanAdjunction H).counit.app G = 
descOfIsLeftKanExtension (L.lan.obj (L ⋙ G)) (L.lanUnit.app (L ⋙ G)) G (𝟙 (L ⋙ G
))
参数：G : D ⥤ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lanAdjunction_counit_app (G : D ⥤ H) :
    (L.lanAdjunction H).counit.app G =
      descOfIsLeftKanExtension (L.lan.obj (L ⋙ G)) (L.lanUnit.app (L ⋙ G)) G (𝟙 (L ⋙ G)) :=
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.lanUnit_app_whiskerLeft_lanAdjunction_counit_app** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：lanUnit_app_whiskerLeft_lanAdjunction_counit_app (G : D ⥤ H) : L.lanUnit.a
pp (L ⋙ G) ≫ whiskerLeft L ((L.lanAdjunction H).counit.app G) = 𝟙 (L ⋙ G)
参数：G : D ⥤ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac`：descOfIsLeftKanExte
nsion_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (F'.descOfIsLeftKanExt
ension α G β) = β
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionObjLanAppLanUnit`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lanUnit_app_whiskerLeft_lanAdjunction_counit_app (G : D ⥤ H) :
    L.lanUnit.app (L ⋙ G) ≫ whiskerLeft L ((L.lanAdjunction H).counit.app G) = 𝟙 (L ⋙ G) := by
  simp [lanAdjunction_counit_app]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.lanUnit_app_app_lanAdjunction_counit_app_app** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：lanUnit_app_app_lanAdjunction_counit_app_app (G : D ⥤ H) (X : C) : (L.lanU
nit.app (L ⋙ G)).app X ≫ ((L.lanAdjunction H).counit.app G).app (L.obj X) = 𝟙 _
参数：G : D ⥤ H；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.Functor.lanUnit_app_whiskerLeft_lanAdjunction_counit_app`
：lanUnit_app_whiskerLeft_lanAdjunction_counit_app (G : D ⥤ H) : L.lanUnit.app (L
 ⋙ G) ≫ whiskerLeft L ((L.lanAdjunction H).counit.app G) = 𝟙 …
-/
lemma lanUnit_app_app_lanAdjunction_counit_app_app (G : D ⥤ H) (X : C) :
    (L.lanUnit.app (L ⋙ G)).app X ≫ ((L.lanAdjunction H).counit.app G).app (L.obj X) = 𝟙 _ :=
  congr_app (L.lanUnit_app_whiskerLeft_lanAdjunction_counit_app G) X

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.isIso_lanAdjunction_counit_app_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：isIso_lanAdjunction_counit_app_iff (G : D ⥤ H) : IsIso ((L.lanAdjunction H
).counit.app G) ↔ G.IsLeftKanExtension (𝟙 (L ⋙ G))
参数：G : D ⥤ H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.Functor.isLeftKanExtension_iff_isIso`：isLeftKanExtension_
iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F' ⟶ F'') {L : C ⥤ D} {F : C ⥤ H} (α :
 F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'') (comm : α…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.lanUnit_app_whiskerLeft_lanAdjunction_counit_app`
：lanUnit_app_whiskerLeft_lanAdjunction_counit_app (G : D ⥤ H) : L.lanUnit.app (L
 ⋙ G) ≫ whiskerLeft L ((L.lanAdjunction H).counit.app G) = 𝟙 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionObjLanAppLanUnit`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
-/
lemma isIso_lanAdjunction_counit_app_iff (G : D ⥤ H) :
    IsIso ((L.lanAdjunction H).counit.app G) ↔ G.IsLeftKanExtension (𝟙 (L ⋙ G)) :=
  (isLeftKanExtension_iff_isIso _ (L.lanUnit.app (L ⋙ G)) _ (by simp)).symm

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.isIso_lanAdjunction_homEquiv_symm_iff** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isIso_lanAdjunction_homEquiv_symm_iff {F : C ⥤ H} {G : D ⥤ H} (α : F ⟶ L ⋙
 G) : IsIso (((L.lanAdjunction H).homEquiv _ _).symm α) ↔ G.IsLeftKanExtension α
参数：α : F ⟶ L ⋙ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.Functor.isLeftKanExtension_iff_isIso`：isLeftKanExtension_
iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F' ⟶ F'') {L : C ⥤ D} {F : C ⥤ H} (α :
 F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'') (comm : α…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionObjLanAppLanUnit`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用引理 `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`：mkOfHomEquiv_homEquiv (
adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEquiv = adj.homEquiv
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac`：descOfIsLeftKanExte
nsion_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (F'.descOfIsLeftKanExt
ension α G β) = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isIso_lanAdjunction_homEquiv_symm_iff {F : C ⥤ H} {G : D ⥤ H} (α : F ⟶ L ⋙ G) :
    IsIso (((L.lanAdjunction H).homEquiv _ _).symm α) ↔ G.IsLeftKanExtension α :=
  (isLeftKanExtension_iff_isIso ((((L.lanAdjunction H).homEquiv _ _).symm α))
    (L.lanUnit.app F) α (by simp [lanAdjunction])).symm

/-- Composing the left Kan extension of `L : C ⥤ D` with `colim` on shapes `D` is isomorphic
to `colim` on shapes `C`. -/
@[simps!]
/-
**CategoryTheory.Functor.lanCompColimIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：lanCompColimIso [HasColimitsOfShape C H] [HasColimitsOfShape D H] : L.lan 
⋙ colim ≅ colim (C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionObjLanAppLanUnit`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] (L : Categor…

--- 原说明 ---
Composing the left Kan extension of `L : C ⥤ D` with `colim` on shapes `D` is is
omorphic
to `colim` on shapes `C`.
-/
noncomputable def lanCompColimIso [HasColimitsOfShape C H] [HasColimitsOfShape D H] :
    L.lan ⋙ colim ≅ colim (C := H) :=
  Iso.symm <| NatIso.ofComponents
    (fun G ↦ (colimitIsoOfIsLeftKanExtension _ (L.lanUnit.app G)).symm)
    (fun f ↦ colimit.hom_ext (fun i ↦ by
      dsimp
      rw [ι_colimMap_assoc, ι_colimitIsoOfIsLeftKanExtension_inv,
        ι_colimitIsoOfIsLeftKanExtension_inv_assoc, ι_colimMap, ← assoc, ← assoc]
      congr 1
      exact congr_app (L.lanUnit.naturality f) i))

end HasLeftKanExtension

section HasPointwiseLeftKanExtension

variable (G : C ⥤ H) [L.HasPointwiseLeftKanExtension G]

variable [HasColimitsOfShape D H]

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasColimit (CostructuredArrow.grothendieckProj L ⋙ G) :=
  hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit _

variable [HasColimitsOfShape C H]

/-- If `G : C ⥤ H` admits a left Kan extension along a functor `L : C ⥤ D` and `H` has colimits of
shape `C` and `D`, then the colimit of `G` is isomorphic to the colimit of a canonical functor
`Grothendieck (CostructuredArrow.functor L) ⥤ H` induced by `L` and `G`. -/
/-
**CategoryTheory.Functor.colimitIsoColimitGrothendieck** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：colimitIsoColimitGrothendieck : colimit G ≅ colimit (CostructuredArrow.gro
thendieckProj L ⋙ G)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Functor.hasColimit_map_comp_ι_comp_grothendieckProj`：hasC
olimit_map_comp_ι_comp_grothendieckProj {X Y : D} (f : X ⟶ Y) : HasColimit (((fu
nctor L).map f).toFunctor ⋙ Grothendieck.ι (functor L) Y…
· 使用定理 `CategoryTheory.Functor.instHasColimitGrothendieckFunctorCompGrothendieck
Proj`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …

--- 原说明 ---
If `G : C ⥤ H` admits a left Kan extension along a functor `L : C ⥤ D` and `H` h
as colimits of
shape `C` and `D`, then the colimit of `G` is isomorphic to the colimit of a can
onical functor
`Grothendieck (CostructuredArrow.functor L) ⥤ H` induced by `L` and `G`.
-/
noncomputable def colimitIsoColimitGrothendieck :
    colimit G ≅ colimit (CostructuredArrow.grothendieckProj L ⋙ G) := calc
  colimit G
    ≅ colimit (leftKanExtension L G) :=
        (colimitIsoOfIsLeftKanExtension _ (L.leftKanExtensionUnit G)).symm
  _ ≅ colimit (fiberwiseColimit (CostructuredArrow.grothendieckProj L ⋙ G)) :=
        HasColimit.isoOfNatIso (leftKanExtensionIsoFiberwiseColimit L G)
  _ ≅ colimit (CostructuredArrow.grothendieckProj L ⋙ G) :=
        colimitFiberwiseColimitIso _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_colimitIsoColimitGrothendieck_inv (X : Grothendieck (CostructuredArrow.functor L)) :
    colimit.ι (CostructuredArrow.grothendieckProj L ⋙ G) X ≫
      (colimitIsoColimitGrothendieck L G).inv =
    colimit.ι G ((CostructuredArrow.proj L X.base).obj X.fiber) := by
  simp [colimitIsoColimitGrothendieck]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_colimitIsoColimitGrothendieck_hom (X : C) :
    colimit.ι G X ≫ (colimitIsoColimitGrothendieck L G).hom =
    colimit.ι (CostructuredArrow.grothendieckProj L ⋙ G) ⟨L.obj X, .mk (𝟙 _)⟩ := by
  rw [← Iso.eq_comp_inv]
  exact (ι_colimitIsoColimitGrothendieck_inv L G ⟨L.obj X, .mk (𝟙 _)⟩).symm

end HasPointwiseLeftKanExtension


section

variable [Full L] [Faithful L]

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ H) (X : C) [HasPointwiseLeftKanExtension L F]
    [∀ (F : C ⥤ H), HasLeftKanExtension L F] :
    IsIso ((L.lanUnit.app F).app X) :=
  (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F (L.obj X)).isIso_hom_app
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ H) [HasPointwiseLeftKanExtension L F]
    [∀ (F : C ⥤ H), HasLeftKanExtension L F] :
    IsIso (L.lanUnit.app F) :=
  NatIso.isIso_of_isIso_app _
/-
**CategoryTheory.Functor.coreflective** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：coreflective [forall (F : C ⥤ H), HasPointwiseLeftKanExtension L F] : IsIs
o (L.lanUnit (H
参数：F : C ⥤ H。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.instIsIsoAppLanUnit_1`：∀ {C : Type u_1} {D : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] (L : Categor…
-/
instance coreflective [∀ (F : C ⥤ H), HasPointwiseLeftKanExtension L F] :
    IsIso (L.lanUnit (H := H)) := by
  apply NatIso.isIso_of_isIso_app _
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ H) [HasPointwiseLeftKanExtension L F]
    [∀ (F : C ⥤ H), HasLeftKanExtension L F] :
    IsIso ((L.lanAdjunction H).unit.app F) := by
  rw [lanAdjunction_unit]
  infer_instance
/-
**CategoryTheory.Functor.coreflective'** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：coreflective' [forall (F : C ⥤ H), HasPointwiseLeftKanExtension L F] : IsI
so (L.lanAdjunction H).unit
参数：F : C ⥤ H。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.instIsIsoAppUnitLanAdjunctionOfHasPointwiseLeftKa
nExtension`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1
, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
-/
instance coreflective' [∀ (F : C ⥤ H), HasPointwiseLeftKanExtension L F] :
    IsIso (L.lanAdjunction H).unit := by
  apply NatIso.isIso_of_isIso_app _

end

end lan

section ran

section

variable [∀ (F : C ⥤ H), HasRightKanExtension L F]

/-- The right Kan extension functor `(C ⥤ H) ⥤ (D ⥤ H)` along a functor `C ⥤ D`. -/
/-
**CategoryTheory.Functor.ran** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：ran : (C ⥤ H) ⥤ (D ⥤ H) where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right Kan extension functor `(C ⥤ H) ⥤ (D ⥤ H)` along a functor `C ⥤ D`.
-/
noncomputable def ran : (C ⥤ H) ⥤ (D ⥤ H) where
  obj F := rightKanExtension L F
  map {F₁ F₂} φ := liftOfIsRightKanExtension _ (rightKanExtensionCounit L F₂) _
    (rightKanExtensionCounit L F₁ ≫ φ)

/-- The natural transformation `L ⋙ (L.lan).obj G ⟶ L`. -/
/-
**CategoryTheory.Functor.ranCounit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：ranCounit : L.ran ⋙ (whiskeringLeft C D H).obj L ⟶ (𝟭 (C ⥤ H)) where app F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `L ⋙ (L.lan).obj G ⟶ L`.
-/
noncomputable def ranCounit : L.ran ⋙ (whiskeringLeft C D H).obj L ⟶ (𝟭 (C ⥤ H)) where
  app F := rightKanExtensionCounit L F
  naturality {F₁ F₂} φ := by ext; simp [ran]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ H) : (L.ran.obj F).IsRightKanExtension (L.ranCounit.app F) := by
  dsimp [ran, ranCounit]
  infer_instance

/-- If there exists a pointwise right Kan extension of `F` along `L`,
then `L.ran.obj G` is a pointwise right Kan extension of `F`. -/
/-
**CategoryTheory.Functor.isPointwiseRightKanExtensionRanCounit** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isPointwiseRightKanExtensionRanCounit (F : C ⥤ H) [HasPointwiseRightKanExt
ension L F] : (RightExtension.mk _ (L.ranCounit.app F)).IsPointwiseRightKanExten
sion
参数：F : C ⥤ H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instIsRightKanExtensionObjRanAppRanCounit`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor…

--- 原说明 ---
If there exists a pointwise right Kan extension of `F` along `L`,
then `L.ran.obj G` is a pointwise right Kan extension of `F`.
-/
noncomputable def isPointwiseRightKanExtensionRanCounit
    (F : C ⥤ H) [HasPointwiseRightKanExtension L F] :
    (RightExtension.mk _ (L.ranCounit.app F)).IsPointwiseRightKanExtension :=
  isPointwiseRightKanExtensionOfIsRightKanExtension (F := F) _ (L.ranCounit.app F)

/-- If a right Kan extension is pointwise, then evaluating it at an object is isomorphic to
taking a limit. -/
/-
**CategoryTheory.Functor.ranObjObjIsoLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：ranObjObjIsoLimit (F : C ⥤ H) [HasPointwiseRightKanExtension L F] (X : D) 
: (L.ran.obj F).obj X ≅ limit (StructuredArrow.proj X L ⋙ F)
参数：F : C ⥤ H；X : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a right Kan extension is pointwise, then evaluating it at an object is isomor
phic to
taking a limit.
-/
noncomputable def ranObjObjIsoLimit (F : C ⥤ H) [HasPointwiseRightKanExtension L F] (X : D) :
    (L.ran.obj F).obj X ≅ limit (StructuredArrow.proj X L ⋙ F) :=
  RightExtension.IsPointwiseRightKanExtensionAt.isoLimit (F := F)
    (isPointwiseRightKanExtensionRanCounit L F X)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.ranObjObjIsoLimit_hom_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ranObjObjIsoLimit_hom_π
    (F : C ⥤ H) [HasPointwiseRightKanExtension L F] (X : D) (f : StructuredArrow X L) :
    (L.ranObjObjIsoLimit F X).hom ≫ limit.π _ f =
    (L.ran.obj F).map f.hom ≫ (L.ranCounit.app F).app f.right := by
  simp [ranObjObjIsoLimit, ran, ranCounit]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.ranObjObjIsoLimit_inv_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ranObjObjIsoLimit_inv_π
    (F : C ⥤ H) [HasPointwiseRightKanExtension L F] (X : D) (f : StructuredArrow X L) :
    (L.ranObjObjIsoLimit F X).inv ≫ (L.ran.obj F).map f.hom ≫ (L.ranCounit.app F).app f.right =
    limit.π _ f :=
  RightExtension.IsPointwiseRightKanExtensionAt.isoLimit_inv_π (F := F)
    (isPointwiseRightKanExtensionRanCounit L F X) f

set_option backward.isDefEq.respectTransparency false in
variable (H) in
/-- The right Kan extension functor `L.ran` is right adjoint to the
precomposition by `L`. -/
/-
**CategoryTheory.Functor.ranAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：ranAdjunction : (whiskeringLeft C D H).obj L ⊣ L.ran
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Functor.instIsRightKanExtensionObjRanAppRanCounit`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor…

--- 原说明 ---
The right Kan extension functor `L.ran` is right adjoint to the
precomposition by `L`.
-/
noncomputable def ranAdjunction : (whiskeringLeft C D H).obj L ⊣ L.ran :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F G =>
        (homEquivOfIsRightKanExtension (α := L.ranCounit.app G) _ F).symm
      homEquiv_naturality_right := fun {F G₁ G₂} β f ↦
        hom_ext_of_isRightKanExtension _ (L.ranCounit.app G₂) _ _ (by
        ext X
        dsimp [homEquivOfIsRightKanExtension]
        rw [liftOfIsRightKanExtension_fac_app, NatTrans.comp_app, assoc]
        have h := congr_app (L.ranCounit.naturality f) X
        dsimp at h ⊢
        rw [h, liftOfIsRightKanExtension_fac_app_assoc])
      homEquiv_naturality_left_symm := fun {F₁ F₂ G} β f ↦ by
        dsimp [homEquivOfIsRightKanExtension]
        rw [assoc] }

set_option backward.isDefEq.respectTransparency false in
variable (H) in
@[simp]
/-
**CategoryTheory.Functor.ranAdjunction_counit** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：ranAdjunction_counit : (L.ranAdjunction H).counit = L.ranCounit
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
lemma ranAdjunction_counit : (L.ranAdjunction H).counit = L.ranCounit := by
  ext F : 2
  dsimp [ranAdjunction, homEquivOfIsRightKanExtension]
  simp
/-
**CategoryTheory.Functor.ranAdjunction_unit_app** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：ranAdjunction_unit_app (G : D ⥤ H) : (L.ranAdjunction H).unit.app G = lift
OfIsRightKanExtension (L.ran.obj (L ⋙ G)) (L.ranCounit.app (L ⋙ G)) G (𝟙 (L ⋙ G)
)
参数：G : D ⥤ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ranAdjunction_unit_app (G : D ⥤ H) :
    (L.ranAdjunction H).unit.app G =
      liftOfIsRightKanExtension (L.ran.obj (L ⋙ G)) (L.ranCounit.app (L ⋙ G)) G (𝟙 (L ⋙ G)) :=
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.ranCounit_app_whiskerLeft_ranAdjunction_unit_app** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：ranCounit_app_whiskerLeft_ranAdjunction_unit_app (G : D ⥤ H) : whiskerLeft
 L ((L.ranAdjunction H).unit.app G) ≫ L.ranCounit.app (L ⋙ G) = 𝟙 (L ⋙ G)
参数：G : D ⥤ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.liftOfIsRightKanExtension_fac`：liftOfIsRightKanEx
tension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) : whiskerLeft L (F'.liftOfIsRightKanExte
nsion α G β) ≫ α = β
· 使用定理 `CategoryTheory.Functor.instIsRightKanExtensionObjRanAppRanCounit`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ranCounit_app_whiskerLeft_ranAdjunction_unit_app (G : D ⥤ H) :
    whiskerLeft L ((L.ranAdjunction H).unit.app G) ≫ L.ranCounit.app (L ⋙ G) = 𝟙 (L ⋙ G) := by
  simp [ranAdjunction_unit_app]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.ranCounit_app_app_ranAdjunction_unit_app_app** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：ranCounit_app_app_ranAdjunction_unit_app_app (G : D ⥤ H) (X : C) : ((L.ran
Adjunction H).unit.app G).app (L.obj X) ≫ (L.ranCounit.app (L ⋙ G)).app X = 𝟙 _
参数：G : D ⥤ H；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.Functor.ranCounit_app_whiskerLeft_ranAdjunction_unit_app`
：ranCounit_app_whiskerLeft_ranAdjunction_unit_app (G : D ⥤ H) : whiskerLeft L ((
L.ranAdjunction H).unit.app G) ≫ L.ranCounit.app (L ⋙ G) = 𝟙 …
-/
lemma ranCounit_app_app_ranAdjunction_unit_app_app (G : D ⥤ H) (X : C) :
    ((L.ranAdjunction H).unit.app G).app (L.obj X) ≫ (L.ranCounit.app (L ⋙ G)).app X = 𝟙 _ :=
  congr_app (L.ranCounit_app_whiskerLeft_ranAdjunction_unit_app G) X

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.isIso_ranAdjunction_unit_app_iff** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：isIso_ranAdjunction_unit_app_iff (G : D ⥤ H) : IsIso ((L.ranAdjunction H).
unit.app G) ↔ G.IsRightKanExtension (𝟙 (L ⋙ G))
参数：G : D ⥤ H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.Functor.isRightKanExtension_iff_isIso`：isRightKanExtensio
n_iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F'' ⟶ F') {L : C ⥤ D} {F : C ⥤ H} (α
 : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.ranCounit_app_whiskerLeft_ranAdjunction_unit_app`
：ranCounit_app_whiskerLeft_ranAdjunction_unit_app (G : D ⥤ H) : whiskerLeft L ((
L.ranAdjunction H).unit.app G) ≫ L.ranCounit.app (L ⋙ G) = 𝟙 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.instIsRightKanExtensionObjRanAppRanCounit`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
-/
lemma isIso_ranAdjunction_unit_app_iff (G : D ⥤ H) :
    IsIso ((L.ranAdjunction H).unit.app G) ↔ G.IsRightKanExtension (𝟙 (L ⋙ G)) :=
  (isRightKanExtension_iff_isIso _ (L.ranCounit.app (L ⋙ G)) _ (by simp)).symm

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.isIso_ranAdjunction_homEquiv_iff** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：isIso_ranAdjunction_homEquiv_iff {F : C ⥤ H} {G : D ⥤ H} (α : L ⋙ G ⟶ F) :
 IsIso (((L.ranAdjunction H).homEquiv _ _) α) ↔ G.IsRightKanExtension α
参数：α : L ⋙ G ⟶ F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.Functor.isRightKanExtension_iff_isIso`：isRightKanExtensio
n_iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F'' ⟶ F') {L : C ⥤ D} {F : C ⥤ H} (α
 : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.instIsRightKanExtensionObjRanAppRanCounit`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`：mkOfHomEquiv_homEquiv (
adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEquiv = adj.homEquiv
· 使用引理 `CategoryTheory.Functor.liftOfIsRightKanExtension_fac`：liftOfIsRightKanEx
tension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) : whiskerLeft L (F'.liftOfIsRightKanExte
nsion α G β) ≫ α = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isIso_ranAdjunction_homEquiv_iff {F : C ⥤ H} {G : D ⥤ H} (α : L ⋙ G ⟶ F) :
    IsIso (((L.ranAdjunction H).homEquiv _ _) α) ↔ G.IsRightKanExtension α :=
  (isRightKanExtension_iff_isIso ((((L.ranAdjunction H).homEquiv _ _) α))
    (L.ranCounit.app F) α (by simp [ranAdjunction])).symm

/-- Composing the right Kan extension of `L : C ⥤ D` with `lim` on shapes `D` is isomorphic
to `lim` on shapes `C`. -/
@[simps!]
/-
**CategoryTheory.Functor.ranCompLimIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：ranCompLimIso (L : C ⥤ D) [forall (G : C ⥤ H), L.HasRightKanExtension G] [
HasLimitsOfShape C H] [HasLimitsOfShape D H] : L.ran ⋙ lim ≅ lim (C
参数：L : C ⥤ D；G : C ⥤ H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instIsRightKanExtensionObjRanAppRanCounit`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor…

--- 原说明 ---
Composing the right Kan extension of `L : C ⥤ D` with `lim` on shapes `D` is iso
morphic
to `lim` on shapes `C`.
-/
noncomputable def ranCompLimIso (L : C ⥤ D) [∀ (G : C ⥤ H), L.HasRightKanExtension G]
    [HasLimitsOfShape C H] [HasLimitsOfShape D H] : L.ran ⋙ lim ≅ lim (C := H) :=
  NatIso.ofComponents
    (fun G ↦ limitIsoOfIsRightKanExtension _ (L.ranCounit.app G))
    (fun f ↦ limit.hom_ext (fun i ↦ by
      dsimp
      rw [assoc, assoc, limMap_π, limitIsoOfIsRightKanExtension_hom_π_assoc,
        limitIsoOfIsRightKanExtension_hom_π, limMap_π_assoc]
      congr 1
      exact congr_app (L.ranCounit.naturality f) i))

end

section

variable [Full L] [Faithful L]

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ H) (X : C) [HasPointwiseRightKanExtension L F]
    [∀ (F : C ⥤ H), HasRightKanExtension L F] :
    IsIso ((L.ranCounit.app F).app X) :=
  (isPointwiseRightKanExtensionRanCounit L F (L.obj X)).isIso_hom_app
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ H) [HasPointwiseRightKanExtension L F]
    [∀ (F : C ⥤ H), HasRightKanExtension L F] :
    IsIso (L.ranCounit.app F) :=
  NatIso.isIso_of_isIso_app _
/-
**CategoryTheory.Functor.reflective** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：reflective [forall (F : C ⥤ H), HasPointwiseRightKanExtension L F] : IsIso
 (L.ranCounit (H
参数：F : C ⥤ H。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.instHasRightKanExtension`：∀ {C : Type u_1} {D : T
ype u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.instIsIsoAppRanCounit_1`：∀ {C : Type u_1} {D : Ty
pe u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory
.Category.{v_2, u_2} D] (L : Categor…
-/
instance reflective [∀ (F : C ⥤ H), HasPointwiseRightKanExtension L F] :
    IsIso (L.ranCounit (H := H)) := by
  apply NatIso.isIso_of_isIso_app _
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ H) [HasPointwiseRightKanExtension L F]
    [∀ (F : C ⥤ H), HasRightKanExtension L F] :
    IsIso ((L.ranAdjunction H).counit.app F) := by
  rw [ranAdjunction_counit]
  infer_instance
/-
**CategoryTheory.Functor.reflective'** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：reflective' [forall (F : C ⥤ H), HasPointwiseRightKanExtension L F] : IsIs
o (L.ranAdjunction H).counit
参数：F : C ⥤ H。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.instHasRightKanExtension`：∀ {C : Type u_1} {D : T
ype u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.instIsIsoAppCounitRanAdjunctionOfHasPointwiseRigh
tKanExtension`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{
v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
-/
instance reflective' [∀ (F : C ⥤ H), HasPointwiseRightKanExtension L F] :
    IsIso (L.ranAdjunction H).counit := by
  apply NatIso.isIso_of_isIso_app _

end

end ran

end Functor

end CategoryTheory

