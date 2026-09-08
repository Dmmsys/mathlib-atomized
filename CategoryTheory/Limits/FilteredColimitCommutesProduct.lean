/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Filtered
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# The IPC property

Given a family of categories `I i` (`i : α`) and a family of functors `F i : I i ⥤ C`, we consider
the diagram `pointwiseProduct F : Π i, I i ⥤ C` defined by `(Xᵢ)ᵢ ↦ ∏ᶜ Xᵢ`. Given a cocone
`cᵢ` on `Fᵢ` for each `i`, there is a natural cocone on `pointwiseProduct F` with point `∏ᶜ cᵢ`.

Similarly to the study of finite limits commuting with filtered colimits, we then study sufficient
conditions for this cocone to be colimiting if all the `cᵢ` are colimiting. We say that `C`
satisfies the `w`-IPC property if the morphism is an isomorphism as long as `α` is `w`-small and
`I i` is `w`-small and filtered for all `i`.

## Main definitions

- `CategoryTheory.Limits.IsIPCOfShape`: `C` satisfies `w`-IPC of shape `α` if `w`-sized filtered
  colimits commute products of shape `α`, i.e. if the joint cocone from above is colimiting if the
  components are.
- `CategoryTheory.Limits.IsIPC`: `C` satisfies the `w`-IPC property if it satisfies `w`-IPC for
  every `α : Type w`.

## Main results

- The category `Type u` satisfies the `u`-IPC property (available by `inferInstance`).
- If `C` satisfies the `w`-IPC property, then `D ⥤ C` satisfies the `w`-IPC property
  (available by `inferInstance`).

These results will be used to show that if a category `C` has products indexed by `α`, then so
does the category of Ind-objects of `C`.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], 3.1.10, 3.1.11, 3.1.12.
-/

@[expose] public section

universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory.Limits

open ConcreteCategory

section

variable {C : Type u} [Category.{v} C] {α : Type*} {I : α → Type*} [∀ i, Category* (I i)]
  [HasProductsOfShape α C] (F : ∀ i, I i ⥤ C)

/-- Given a family of functors `I i ⥤ C` for `i : α`, we obtain a functor `(∀ i, I i) ⥤ C` which
maps `k : ∀ i, I i` to `∏ᶜ fun (s : α) => (F s).obj (k s)`. -/
/-
**CategoryTheory.Limits.pointwiseProduct** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：pointwiseProduct : (forall i, I i) ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of functors `I i ⥤ C` for `i : α`, we obtain a functor `(∀ i, I i
) ⥤ C` which
maps `k : ∀ i, I i` to `∏ᶜ fun (s : α) => (F s).obj (k s)`.
-/
noncomputable abbrev pointwiseProduct : (∀ i, I i) ⥤ C :=
  Functor.pi F ⋙ Pi.functor α

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Functor.pi in
/-- `pointwiseProduct` is invariant under re-indexing. -/
@[simps!]
noncomputable
/-
**CategoryTheory.Limits.Pi.equivalenceOfEquivCompPointwiseProduct** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Limits.Pi`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {α : Type
 u_1} →       {I : α → Type u_2} →         [inst_1 : (i : α) → CategoryTheory.Ca
tegory.{v_1, u_2} (I i)] →           [inst_2 : CategoryTheory.Limits.HasProducts
OfShape α C] →             (F : (i : α) → CategoryTheory.Functor (I i) C) →     
          {β : Type u_3} →                 (f : β ≃ α) →                   [inst
_3 : CategoryTheory.Limits.HasProductsOfShape β C] →                     (Catego
ryTheory.Pi.equivalenceOfEquiv I f).inverse.comp                         (Catego
ryTheory.Limits.pointwiseProduct fun i => F (f i)) ≅                       Categ
oryTheory.Limits.pointwiseProduct F
参数：i : α；I i；F : (i : α) → CategoryTheory.Functor (I i) C；f : β ≃ α；CategoryTheo
ry.Pi.equivalenceOfEquiv I f；CategoryTheory.Limits.pointwiseProduct fun i => F (
f i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Pi.equivalenceOfEquivCompPointwiseProduct {β : Type*} (f : β ≃ α) [HasProductsOfShape β C] :
    (Pi.equivalenceOfEquiv I f).inverse ⋙ pointwiseProduct (fun i ↦ F (f i)) ≅
      pointwiseProduct F :=
  (NatIso.ofComponents
    (fun a ↦ (Pi.whiskerEquiv f (fun j ↦ (Iso.refl ((F (f j)).obj <| a (f j))))).symm)).symm

set_option backward.defeqAttrib.useBackward true in
variable {F} in
/-- The inclusions `(F s).obj (k s) ⟶ colimit (F s)` induce a cocone on `pointwiseProduct F` with
cone point `∏ᶜ (fun s : α) => colimit (F s)`. -/
@[simps]
/-
**CategoryTheory.Limits.coconePointwiseProduct** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：coconePointwiseProduct (c : forall i, Cocone (F i)) : Cocone (pointwisePro
duct F) where pt
参数：c : forall i, Cocone (F i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusions `(F s).obj (k s) ⟶ colimit (F s)` induce a cocone on `pointwisePr
oduct F` with
cone point `∏ᶜ (fun s : α) => colimit (F s)`.
-/
noncomputable def coconePointwiseProduct (c : ∀ i, Cocone (F i)) :
    Cocone (pointwiseProduct F) where
  pt := ∏ᶜ fun i ↦ (c i).pt
  ι := Functor.whiskerRight (NatTrans.pi fun i ↦ (c i).ι) _ ≫ (Pi.constCompPiIsoConst _).hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `coconePointwiseProduct` is invariant under isomorphisms of cocones. -/
/-
**CategoryTheory.Limits.coconePointwiseProductIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：coconePointwiseProductIso {c c' : forall i, Cocone (F i)} (e : forall i, c
 i ≅ c' i) : coconePointwiseProduct c ≅ coconePointwiseProduct c'
参数：F i；e : forall i, c i ≅ c' i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coconePointwiseProduct` is invariant under isomorphisms of cocones.
-/
noncomputable def coconePointwiseProductIso {c c' : ∀ i, Cocone (F i)} (e : ∀ i, c i ≅ c' i) :
    coconePointwiseProduct c ≅ coconePointwiseProduct c' :=
  Cocone.ext (Pi.mapIso fun i ↦ (Cocone.forget _).mapIso (e i)) fun i ↦ by
    dsimp
    ext
    simp [Functor.pi]

/-- The natural morphism `colim_k (∏ᶜ s ↦ (F s).obj (k s)) ⟶ ∏ᶜ s ↦ colim_k (F s).obj (k s)`.
A category has the `IPC` property of shape `α` if this morphism is an isomorphism as long
as the indexing categories are filtered. -/
/-
**CategoryTheory.Limits.colimitPointwiseProductToProductColimit** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：colimitPointwiseProductToProductColimit [forall i, HasColimit (F i)] [HasC
olimit (Functor.pi F ⋙ Pi.functor α)] : colimit (pointwiseProduct F) ⟶ ∏ᶜ fun (s
 : α) => colimit (F s)
参数：F i；Functor.pi F ⋙ Pi.functor α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural morphism `colim_k (∏ᶜ s ↦ (F s).obj (k s)) ⟶ ∏ᶜ s ↦ colim_k (F s).ob
j (k s)`.
A category has the `IPC` property of shape `α` if this morphism is an isomorphis
m as long
as the indexing categories are filtered.
-/
noncomputable def colimitPointwiseProductToProductColimit [∀ i, HasColimit (F i)]
    [HasColimit (Functor.pi F ⋙ Pi.functor α)] :
    colimit (pointwiseProduct F) ⟶ ∏ᶜ fun (s : α) => colimit (F s) :=
  colimit.desc _ (coconePointwiseProduct _)

variable [∀ i, HasColimit (F i)] [HasColimit (pointwiseProduct F)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_colimitPointwiseProductToProductColimit_π (k : ∀ i, I i) (s : α) :
    colimit.ι (pointwiseProduct F) k ≫
      colimitPointwiseProductToProductColimit F ≫ Pi.π _ s =
      Pi.π _ s ≫ colimit.ι (F s) (k s) := by
  simp [colimitPointwiseProductToProductColimit, Functor.pi, Pi.functor]

end

section functorCategory

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {α : Type*} {I : α → Type*} [∀ i, Category (I i)]
  [HasLimitsOfShape (Discrete α) C]
  (F : ∀ i, I i ⥤ D ⥤ C)

set_option backward.defeqAttrib.useBackward true in
/-- Evaluating the pointwise product `k ↦ ∏ᶜ fun (s : α) => (F s).obj (k s)` at `d` is the same as
taking the pointwise product `k ↦ ∏ᶜ fun (s : α) => ((F s).obj (k s)).obj d`. -/
@[simps!]
/-
**CategoryTheory.Limits.pointwiseProductCompEvaluation** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pointwiseProductCompEvaluation (d : D) : pointwiseProduct F ⋙ (evaluation 
D C).obj d ≅ pointwiseProduct (fun s => F s ⋙ (evaluation _ _).obj d)
参数：d : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluating the pointwise product `k ↦ ∏ᶜ fun (s : α) => (F s).obj (k s)` at `d` 
is the same as
taking the pointwise product `k ↦ ∏ᶜ fun (s : α) => ((F s).obj (k s)).obj d`.
-/
noncomputable def pointwiseProductCompEvaluation (d : D) :
    pointwiseProduct F ⋙ (evaluation D C).obj d ≅
      pointwiseProduct (fun s => F s ⋙ (evaluation _ _).obj d) :=
  NatIso.ofComponents (fun k => piObjIso _ _)
    (fun f => Pi.hom_ext _ _ (by simp [Functor.pi, ← NatTrans.comp_app]))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- In a functor category, `coconePointwiseProduct` commutes with evaluation. -/
/-
**CategoryTheory.Limits.evaluationCoconePointwiseProductIso** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：evaluationCoconePointwiseProductIso (X : D) (c : forall i, Cocone (F i)) :
 ((evaluation D C).obj X).mapCocone (coconePointwiseProduct c) ≅ (Cocone.precomp
ose <| (pointwiseProductCompEvaluation F X).hom).obj (coconePointwiseProduct fun
 i => ((evaluation D C).obj X).mapCocone (c i))
参数：X : D；c : forall i, Cocone (F i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a functor category, `coconePointwiseProduct` commutes with evaluation.
-/
noncomputable def evaluationCoconePointwiseProductIso (X : D) (c : ∀ i, Cocone (F i)) :
    ((evaluation D C).obj X).mapCocone (coconePointwiseProduct c) ≅
      (Cocone.precompose <| (pointwiseProductCompEvaluation F X).hom).obj
        (coconePointwiseProduct fun i ↦ ((evaluation D C).obj X).mapCocone (c i)) :=
  Cocone.ext (piObjIso (fun i ↦ (c i).pt) X) fun j ↦ by
    dsimp
    ext
    simp [Functor.pi, NatTrans.pi, ← NatTrans.comp_app]

variable [∀ i, HasColimitsOfShape (I i) C] [HasColimitsOfShape (∀ i, I i) C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.colimitPointwiseProductToProductColimit_app** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：colimitPointwiseProductToProductColimit_app (d : D) : (colimitPointwisePro
ductToProductColimit F).app d = (colimitObjIsoColimitCompEvaluation _ _).hom ≫ (
HasColimit.isoOfNatIso (pointwiseProductCompEvaluation F d)).hom ≫ colimitPointw
iseProductToProductColimit _ ≫ (Pi.mapIso fun _ => (colimitObjIsoColimitCompEval
uation _ _).symm).hom ≫ (piObjIso _ _).inv
参数：d : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.piObjIso_hom_comp_π`：piObjIso_hom_comp_π (f : α ->
 D ⥤ C) (d : D) (s : α) : (piObjIso f d).hom ≫ Pi.π (fun s => (f s).obj d) s = (
Pi.π f s).app d
· 使用定理 `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_ι_inv_assoc`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : C
ategoryTheory.Category.{v₁, u₁} J]   {K : Type u₂} [inst_2…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.ι_colimitPointwiseProductToProductColimit_π`：ι_col
imitPointwiseProductToProductColimit_π (k : forall i, I i) (s : α) : colimit.ι (
pointwiseProduct F) k ≫ colimitPointwiseProductToProduc…
· 使用定理 `CategoryTheory.Limits.Pi.mapIso_hom_π`：∀ {β : Type w} {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Li
mits.HasProductsOfShape β C…
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom_assoc`：∀ {J : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.ι_colimitPointwiseProductToProductColimit_π_assoc`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {α : Type u_1} {I : α 
→ Type u_2}   [inst_1 : (i : α) → CategoryTheory.Category.{v_…
· 使用定理 `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_ι_inv`：colimitO
bjIsoColimitCompEvaluation_ι_inv [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J
) (k : K) : colimit.ι (F ⋙ (evaluation K C).obj k) j…
· 使用定理 `CategoryTheory.Limits.piObjIso_hom_comp_π_assoc`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {D : Type u₁} [inst_1 : CategoryTheory.Categor
y.{v₁, u₁} D]   {α : Type w} [inst_2 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem colimitPointwiseProductToProductColimit_app (d : D) :
    (colimitPointwiseProductToProductColimit F).app d =
      (colimitObjIsoColimitCompEvaluation _ _).hom ≫
        (HasColimit.isoOfNatIso (pointwiseProductCompEvaluation F d)).hom ≫
          colimitPointwiseProductToProductColimit _ ≫
            (Pi.mapIso fun _ => (colimitObjIsoColimitCompEvaluation _ _).symm).hom ≫
              (piObjIso _ _).inv := by
  rw [← Iso.inv_comp_eq]
  simp only [← Category.assoc]
  rw [Iso.eq_comp_inv]
  refine Pi.hom_ext _ _ (fun s => colimit.hom_ext (fun k => ?_))
  simp [← NatTrans.comp_app, Functor.pi]

end functorCategory

section

variable {C : Type*} [Category* C]
variable {ι : Type*} [HasProductsOfShape ι C]

/-- A category `C` has the `w`-IPC property for shape `ι` if `w`-sized filtered colimits commute
with products of shape `ι`. -/
@[pp_with_univ]
/-
**CategoryTheory.Limits.IsIPCOfShape** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：(ι : Type u_3) →   (C : Type u_4) → [inst : CategoryTheory.Category.{v_2, 
u_4} C] → [CategoryTheory.Limits.HasProductsOfShape ι C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` has the `w`-IPC property for shape `ι` if `w`-sized filtered coli
mits commute
with products of shape `ι`.
-/
class IsIPCOfShape (ι : Type*) (C : Type*) [Category* C] [HasProductsOfShape ι C] : Prop where
  nonempty_isColimit ⦃J : ι → Type w⦄ [∀ i, SmallCategory (J i)]
    [∀ i, IsFiltered (J i)] ⦃F : ∀ i, J i ⥤ C⦄ ⦃c : ∀ i, Cocone (F i)⦄ :
    (∀ i, IsColimit (c i)) → Nonempty (IsColimit (coconePointwiseProduct c))
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIPCOfShape.{w} ι C] {J : ι → Type w} [∀ i, SmallCategory (J i)]
    [∀ i, IsFiltered (J i)] (F : ∀ i, J i ⥤ C)
    [∀ i, HasColimit (F i)] [HasColimit (pointwiseProduct F)] :
    IsIso (colimitPointwiseProductToProductColimit F) := by
  rw [colimitPointwiseProductToProductColimit, colimit.desc]
  refine ((colimit.isColimit (pointwiseProduct F)).nonempty_isColimit_iff_isIso_desc).mp ?_
  exact IsIPCOfShape.nonempty_isColimit fun i ↦ colimit.isColimit _
/-
**CategoryTheory.Limits.IsIPCOfShape.of_forall_exists** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.IsIPCOfShape`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {ι : Type u
_2}   [inst_1 : CategoryTheory.Limits.HasProductsOfShape ι C],   (∀ ⦃J : ι → Typ
e w⦄ [inst_2 : (i : ι) → CategoryTheory.SmallCategory (J i)]       [∀ (i : ι), C
ategoryTheory.IsFiltered (J i)] (F : (i : ι) → CategoryTheory.Functor (J i) C)  
     [∀ (i : ι), CategoryTheory.Limits.HasColimit (F i)],       ∃ c x, Nonempty 
(CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.coconePointwiseProduct c
))) →     CategoryTheory.Limits.IsIPCOfShape.{w, u_2, v_1, u_1} ι C
参数：∀ ⦃J : ι → Type w⦄ [inst_2 : (i : ι) → CategoryTheory.SmallCategory (J i)]   
    [∀ (i : ι), CategoryTheory.IsFiltered (J i)] (F : (i : ι) → CategoryTheory.F
unctor (J i) C)       [∀ (i : ι), CategoryTheory.Limits.HasColimit (F i)],      
 ∃ c x, Nonempty (CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.coconeP
ointwiseProduct c))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
-/
lemma IsIPCOfShape.of_forall_exists
    (H : ∀ ⦃J : ι → Type w⦄ [∀ i, SmallCategory (J i)]
      [∀ i, IsFiltered (J i)] (F : ∀ i, J i ⥤ C) [∀ i, HasColimit (F i)], ∃ (c : ∀ i, Cocone (F i))
      (_ : ∀ i, IsColimit (c i)), Nonempty (IsColimit (coconePointwiseProduct c))) :
    IsIPCOfShape.{w} ι C where
  nonempty_isColimit J _ _ F c hc := by
    have (i : ι) : HasColimit (F i) := ⟨_, hc i⟩
    obtain ⟨c', hc', _⟩ := H F
    let e : coconePointwiseProduct c ≅ coconePointwiseProduct c' :=
      coconePointwiseProductIso _ fun i ↦ (hc i).uniqueUpToIso (hc' i)
    rwa [(IsColimit.equivIsoColimit e).nonempty_congr]
/-
**CategoryTheory.Limits.IsIPCOfShape.of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.IsIPCOfShape`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {ι : Type u
_2}   [inst_1 : CategoryTheory.Limits.HasProductsOfShape ι C],   (∀ (J : ι → Typ
e w) [inst_2 : (i : ι) → CategoryTheory.SmallCategory (J i)]       [∀ (i : ι), C
ategoryTheory.IsFiltered (J i)] (F : (i : ι) → CategoryTheory.Functor (J i) C)  
     [inst_4 : ∀ (i : ι), CategoryTheory.Limits.HasColimit (F i)],       ∃ (x : 
CategoryTheory.Limits.HasColimit (CategoryTheory.Limits.pointwiseProduct F)),   
      CategoryTheory.IsIso (CategoryTheory.Limits.colimitPointwiseProductToProdu
ctColimit F)) →     CategoryTheory.Limits.IsIPCOfShape.{w, u_2, v_1, u_1} ι C
参数：∀ (J : ι → Type w) [inst_2 : (i : ι) → CategoryTheory.SmallCategory (J i)]   
    [∀ (i : ι), CategoryTheory.IsFiltered (J i)] (F : (i : ι) → CategoryTheory.F
unctor (J i) C)       [inst_4 : ∀ (i : ι), CategoryTheory.Limits.HasColimit (F i
)],       ∃ (x : CategoryTheory.Limits.HasColimit (CategoryTheory.Limits.pointwi
seProduct F)),         CategoryTheory.IsIso (CategoryTheory.Limits.colimitPointw
iseProductToProductColimit F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.IsIPCOfShape.of_forall_exists`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] {ι : Type u_2}   [inst_1 : CategoryT
heory.Limits.HasProductsOfShape ι C],   (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.nonempty_isColimit_iff_isIso_desc`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
lemma IsIPCOfShape.of_isIso
    (H : ∀ (J : ι → Type w) [∀ i, SmallCategory (J i)] [∀ i, IsFiltered (J i)]
      (F : ∀ i, J i ⥤ C) [∀ (i : ι), HasColimit (F i)],
      ∃ (_ : HasColimit (pointwiseProduct F)),
        IsIso (colimitPointwiseProductToProductColimit F)) :
    IsIPCOfShape.{w} ι C := by
  refine .of_forall_exists fun J _ _ F _ ↦ ?_
  refine ⟨fun i ↦ colimit.cocone _, fun i ↦ colimit.isColimit _, ?_⟩
  obtain ⟨_, h⟩ := H J F
  rwa [IsColimit.nonempty_isColimit_iff_isIso_desc (colimit.isColimit _)]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Functor.pi in
/-
**CategoryTheory.Limits.IsIPCOfShape.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.IsIPCOfShape`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {ι : Type u
_2}   [inst_1 : CategoryTheory.Limits.HasProductsOfShape ι C] {ι' : Type u_3}   
[inst_2 : CategoryTheory.Limits.HasProductsOfShape ι' C] [CategoryTheory.Limits.
IsIPCOfShape.{w, u_2, v_1, u_1} ι C]   (e : ι ≃ ι'), CategoryTheory.Limits.IsIPC
OfShape.{w, u_3, v_1, u_1} ι' C
参数：e : ι ≃ ι'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsIPCOfShape.nonempty_isColimit`：∀ {ι : Type u_3} 
{C : Type u_4} {inst : CategoryTheory.Category.{v_2, u_4} C}   {inst_1 : Categor
yTheory.Limits.HasProductsOfShape ι C}   [s…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
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
lemma IsIPCOfShape.of_equiv {ι' : Type*} [HasProductsOfShape ι' C] [IsIPCOfShape.{w} ι C]
    (e : ι ≃ ι') :
    IsIPCOfShape.{w} ι' C where
  nonempty_isColimit J _ _ F c hc := by
    obtain ⟨h⟩ := nonempty_isColimit fun i : ι ↦ hc (e i)
    constructor
    apply IsColimit.equivOfNatIsoOfIso _ _ _ _ <|
        h.whiskerEquivalence (Pi.equivalenceOfEquiv J e).symm
    · exact (Pi.equivalenceOfEquivCompPointwiseProduct F e)
    · -- Without the double `symm`, one runs into DTT hell
      exact (Cocone.ext (Pi.whiskerEquiv e fun _ ↦ Iso.refl _).symm).symm

variable (C) in
/-- A category `C` has the `w`-IPC property it satisfies the IPC-property for every `ι : Type w`. -/
/-
**CategoryTheory.Limits.IsIPC** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：IsIPC [HasProducts.{w} C] [HasFilteredColimitsOfSize.{w} C] : Prop where i
sIPCOfShape (ι : Type w) : IsIPCOfShape.{w} ι C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` has the `w`-IPC property it satisfies the IPC-property for every 
`ι : Type w`.
-/
class IsIPC [HasProducts.{w} C] [HasFilteredColimitsOfSize.{w} C] : Prop where
  isIPCOfShape (ι : Type w) : IsIPCOfShape.{w} ι C := by infer_instance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasProducts.{w} C] [HasFilteredColimitsOfSize.{w, w} C] [IsIPC.{w} C] (ι : Type*)
    [Small.{w} ι] [HasProductsOfShape ι C] :
    IsIPCOfShape.{w} ι C := by
  suffices IsIPCOfShape (Shrink.{w} ι) C from .of_equiv (equivShrink ι).symm
  apply IsIPC.isIPCOfShape

end

section types

variable {α : Type u} {I : α → Type u} [∀ i, SmallCategory (I i)] [∀ i, IsFiltered (I i)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.Types.isIso_colimitPointwiseProductToProductColimit** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：∀ {α : Type u} {I : α → Type u} [inst : (i : α) → CategoryTheory.SmallCate
gory (I i)]   [∀ (i : α), CategoryTheory.IsFiltered (I i)] (F : (i : α) → Catego
ryTheory.Functor (I i) (Type u)),   CategoryTheory.IsIso (CategoryTheory.Limits.
colimitPointwiseProductToProductColimit F)
参数：i : α；I i；i : α；I i；F : (i : α) → CategoryTheory.Functor (I i) (Type u)；Categ
oryTheory.Limits.colimitPointwiseProductToProductColimit F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.Types.instHasProductsType`：CategoryTheory.Limits.H
asProducts (Type v)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective'`：jointly_surjective' (x 
: colimit F) : exists (j : J) (y : F.obj j), colimit.ι F j y = x
· 使用定理 `CategoryTheory.instIsFilteredOrEmptyForall`：∀ {α : Type w} {I : α → Type
 u₁} [inst : (i : α) → CategoryTheory.Category.{v₁, u₁} (I i)]   [∀ (i : α), Cat
egoryTheory.IsFilteredOrEmpty (I…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.ι_colimitPointwiseProductToProductColimit_π`：ι_col
imitPointwiseProductToProductColimit_π (k : forall i, I i) (s : α) : colimit.ι (
pointwiseProduct F) k ≫ colimitPointwiseProductToProduc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff`：colimit_eq_i
ff [HasColimit F] {i j : J} {xi : F.obj i} {xj : F.obj j} : colimit.ι F i xi = c
olimit.ι F j xj ↔ exists (k : _) (f : i ⟶ k) (g …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.IsFiltered.coeq_condition`：coeq_condition {j j' : C} (f f
' : j ⟶ j') : f ≫ coeqHom f f' = f' ≫ coeqHom f f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.Types.colimit_sound'`：colimit_sound' {j j' : J} {x
 : F.obj j} {x' : F.obj j'} {j'' : J} (f : j ⟶ j'') (f' : j' ⟶ j'') (w : F.map f
 x = F.map f' x') : colimit.ι F …
· 使用定理 `CategoryTheory.Limits.Types.limit_ext'`：limit_ext' (F' : J ⥤ Type v) (x 
y : limit F') (w : forall j, limit.π F' j x = limit.π F' j y) : x = y
· 使用定理 `CategoryTheory.Limits.Pi.map_π_apply`：∀ {β : Type w} {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Lim
its.HasProduct f] [inst_2 …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.Limits.colimit.w_apply`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   (F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.Types.productIso_inv_comp_π_apply`：∀ {J : Type v} 
(F : J → Type (max v u)) (j : J) (x : (j : J) → F j),   (CategoryTheory.Concrete
Category.hom (CategoryTheory.Limits.Pi.π F j)…
-/
theorem Types.isIso_colimitPointwiseProductToProductColimit (F : ∀ i, I i ⥤ Type u) :
    IsIso (colimitPointwiseProductToProductColimit F) := by
  -- We follow the proof in [Kashiwara2006], Prop. 3.1.11(ii)
  refine (isIso_iff_bijective _).2 ⟨fun y y' hy => ?_, fun x => ?_⟩
  · obtain ⟨ky, yk₀, hyk₀⟩ := Types.jointly_surjective' y
    obtain ⟨ky', yk₀', hyk₀'⟩ := Types.jointly_surjective' y'
    let k := IsFiltered.max ky ky'
    let yk : (pointwiseProduct F).obj k :=
      (pointwiseProduct F).map (IsFiltered.leftToMax ky ky') yk₀
    let yk' : (pointwiseProduct F).obj k :=
      (pointwiseProduct F).map (IsFiltered.rightToMax ky ky') yk₀'
    obtain rfl : y = colimit.ι (pointwiseProduct F) k yk := by
      simp only [k, yk, colimit.w_apply, hyk₀]
    obtain rfl : y' = colimit.ι (pointwiseProduct F) k yk' := by
      simp only [k, yk', colimit.w_apply, hyk₀']
    dsimp at yk yk'
    have hch : ∀ (s : α), ∃ (i' : I s) (hi' : k s ⟶ i'),
        (F s).map hi' (Pi.π (fun s => (F s).obj (k s)) s yk) =
          (F s).map hi' (Pi.π (fun s => (F s).obj (k s)) s yk') := by
      intro s
      have hy₁ := congr_hom (ι_colimitPointwiseProductToProductColimit_π F k s) yk
      have hy₂ := congr_hom (ι_colimitPointwiseProductToProductColimit_π F k s) yk'
      dsimp at hy₁ hy₂ hy
      rw [← hy, hy₁, Types.FilteredColimit.colimit_eq_iff] at hy₂
      obtain ⟨i₀, f₀, g₀, h₀⟩ := hy₂
      refine ⟨IsFiltered.coeq f₀ g₀, f₀ ≫ IsFiltered.coeqHom f₀ g₀, ?_⟩
      conv_rhs => rw [IsFiltered.coeq_condition]
      dsimp [Functor.pi] at h₀
      simp [h₀]
    choose k' f hk' using hch
    apply Types.colimit_sound' f f
    exact Types.limit_ext' _ _ _ (fun ⟨s⟩ => by simpa [Functor.pi, Pi.map_π_apply] using hk' s)
  · have hch : ∀ (s : α), ∃ (i : I s) (xi : (F s).obj i), colimit.ι (F s) i xi =
        Pi.π (fun s => colimit (F s)) s x := fun s => Types.jointly_surjective' _
    choose k p hk using hch
    refine ⟨colimit.ι (pointwiseProduct F) k ((Types.productIso _).inv p), ?_⟩
    refine Types.limit_ext' _ _ _ (fun ⟨s⟩ => ?_)
    have := congr_hom (ι_colimitPointwiseProductToProductColimit_π F k s)
      ((Types.productIso _).inv p)
    exact this.trans (by simpa [Functor.pi] using hk _)
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIPC.{u} (Type u) where
  isIPCOfShape _ :=
    .of_isIso fun _ _ _ _ _ ↦ ⟨inferInstance, Types.isIso_colimitPointwiseProductToProductColimit _⟩

end types

section functorCategory

variable {C : Type u} [Category.{v} C]

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (ι : Type*) [HasProductsOfShape ι C] [IsIPCOfShape.{w} ι C]
    [HasFilteredColimitsOfSize.{w, w} C] {D : Type u₁}
    [Category.{v₁} D] : IsIPCOfShape.{w} ι (D ⥤ C) where
  nonempty_isColimit J _ _ F c hc := by
    refine ⟨evaluationJointlyReflectsColimits _ fun X ↦ ?_⟩
    exact IsColimit.equivOfNatIsoOfIso (pointwiseProductCompEvaluation F X).symm _ _
      (evaluationCoconePointwiseProductIso F X c).symm
      (IsIPCOfShape.nonempty_isColimit fun i ↦ isColimitOfPreserves _ (hc i)).some
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasProducts.{w} C] [HasFilteredColimitsOfSize.{w, w} C] [IsIPC.{w} C] {D : Type u₁}
    [Category.{v₁} D] : IsIPC.{w} (D ⥤ C) where

end functorCategory

end CategoryTheory.Limits

