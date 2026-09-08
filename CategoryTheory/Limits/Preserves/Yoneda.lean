/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.FunctorToTypes

/-!
# Yoneda preserves certain colimits

Given a bifunctor `F : J ⥤ Cᵒᵖ ⥤ Type v`, we prove the isomorphism
`Hom(YX, colim_j F(j, -)) ≅ colim_j Hom(YX, F(j, -))`, where `Y` is the Yoneda embedding.

We state this in two ways. One is functorial in `X` and stated as a natural isomorphism of functors
`yoneda.op ⋙ yoneda.obj (colimit F) ≅ yoneda.op ⋙ colimit (F ⋙ yoneda)`, and from this we
deduce the more traditional preservation statement
`PreservesColimit F (coyoneda.obj (op (yoneda.obj X)))`.

The proof combines the Yoneda lemma with the fact that colimits in functor categories are computed
pointwise.

## See also

There is also a relative version of this statement where `F : J ⥤ Over A` for some presheaf
`A`, see `Mathlib/CategoryTheory/Comma/Presheaf/Colimit.lean`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open CategoryTheory.Limits Opposite CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]

variable {J : Type u₂} [Category.{v₂} J] [HasColimitsOfShape J (Type v₁)]
  [HasColimitsOfShape J (Type (max u₁ v₁))] (F : J ⥤ Cᵒᵖ ⥤ Type v₁)

/-- Naturally in `X`, we have `Hom(YX, colim_i Fi) ≅ colim_i Hom(YX, Fi)`. -/
/-
**CategoryTheory.yonedaYonedaColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaYonedaColimit : yoneda.op ⋙ yoneda.obj (colimit F) ≅ yoneda.op ⋙ col
imit (F ⋙ yoneda)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Types.instPreservesColimitsOfSizeUliftFunctor`：Cat
egoryTheory.Limits.PreservesColimitsOfSize.{w', w, u, max u v, u + 1, max (u + 1
) (v + 1)}   CategoryTheory.uliftFunctor.{v, u}

--- 原说明 ---
Naturally in `X`, we have `Hom(YX, colim_i Fi) ≅ colim_i Hom(YX, Fi)`.
-/
noncomputable def yonedaYonedaColimit :
    yoneda.op ⋙ yoneda.obj (colimit F) ≅ yoneda.op ⋙ colimit (F ⋙ yoneda) := calc
  yoneda.op ⋙ yoneda.obj (colimit F)
    ≅ colimit F ⋙ uliftFunctor.{u₁} := yonedaOpCompYonedaObj (colimit F)
  _ ≅ F.flip ⋙ colim ⋙ uliftFunctor.{u₁} :=
        isoWhiskerRight (colimitIsoFlipCompColim F) uliftFunctor.{u₁}
  _ ≅ F.flip ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} ⋙ colim :=
        isoWhiskerLeft F.flip (preservesColimitNatIso uliftFunctor.{u₁})
  _ ≅ (yoneda.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj F) ⋙ colim := isoWhiskerRight
        (isoWhiskerRight largeCurriedYonedaLemma.symm ((whiskeringLeft _ _ _).obj F)) colim
  _ ≅ yoneda.op ⋙ colimit (F ⋙ yoneda) :=
        isoWhiskerLeft yoneda.op (colimitIsoFlipCompColim (F ⋙ yoneda)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.yonedaYonedaColimit_app_inv** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：yonedaYonedaColimit_app_inv {X : C} : ((yonedaYonedaColimit F).app (op X))
.inv = (colimitObjIsoColimitCompEvaluation _ _).hom ≫ (colimit.post F (coyoneda.
obj (op (yoneda.obj X))))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Types.instPreservesColimitsOfSizeUliftFunctor`：Cat
egoryTheory.Limits.PreservesColimitsOfSize.{w', w, u, max u v, u + 1, max (u + 1
) (v + 1)}   CategoryTheory.uliftFunctor.{v, u}
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_post`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   (F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.ι_colimMap_assoc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.instHasColimitCompOfPreservesColimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.ι_preservesColimitIso_inv_assoc`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_ι_inv`：colimitO
bjIsoColimitCompEvaluation_ι_inv [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J
) (k : K) : colimit.ι (F ⋙ (evaluation K C).obj k) j…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem yonedaYonedaColimit_app_inv {X : C} : ((yonedaYonedaColimit F).app (op X)).inv =
    (colimitObjIsoColimitCompEvaluation _ _).hom ≫
      (colimit.post F (coyoneda.obj (op (yoneda.obj X)))) := by
  dsimp [yonedaYonedaColimit]
  simp only [Iso.cancel_iso_hom_left]
  apply colimit.hom_ext
  intro j
  rw [colimit.ι_post, ι_colimMap_assoc]
  simp only [← CategoryTheory.Functor.assoc, comp_evaluation]
  rw [ι_preservesColimitIso_inv_assoc]
  simp only [← comp_evaluation, comp_obj, evaluation_obj_obj, yoneda_obj_obj, uliftFunctor_obj,
    whiskerLeft_app, uliftFunctor_map, Functor.comp_map, evaluation_obj_map, yoneda_map_app]
  ext η Y f
  dsimp [largeCurriedYonedaLemma, yonedaOpCompYonedaObj, yonedaEquiv]
  simp only [← comp_apply, Category.assoc, colimitObjIsoColimitCompEvaluation_ι_inv,
    ← NatTrans.naturality, ← NatTrans.naturality_assoc, yoneda_obj_obj, yoneda_obj_map,
    Quiver.Hom.unop_op]
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {X : C} : PreservesColimit F (coyoneda.obj (op (yoneda.obj X))) := by
  suffices IsIso (colimit.post F (coyoneda.obj (op (yoneda.obj X)))) from
    preservesColimit_of_isIso_post _ _
  suffices colimit.post F (coyoneda.obj (op (yoneda.obj X))) =
      (colimitObjIsoColimitCompEvaluation _ _).inv ≫ ((yonedaYonedaColimit F).app (op X)).inv from
    this ▸ inferInstance
  rw [yonedaYonedaColimit_app_inv, Iso.inv_hom_id_assoc]

end CategoryTheory

