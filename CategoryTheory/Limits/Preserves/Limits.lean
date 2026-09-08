/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Isomorphisms about functors which preserve (co)limits

If `G` preserves limits, and `C` and `D` have limits, then for any diagram `F : J ⥤ C` we have a
canonical isomorphism `preservesLimitsIso : G.obj (Limit F) ≅ Limit (F ⋙ G)`.
We also show that we can commute `IsLimit.lift` of a preserved limit with `Functor.mapCone`:
`(PreservesLimit.preserves t).lift (G.mapCone c₂) = G.map (t.lift c₂)`.

The duals of these are also given. For functors which preserve (co)limits of specific shapes, see
the files in the directory `Mathlib/CategoryTheory/Limits/Preserves/Shapes/`.
-/

@[expose] public section


universe w' w v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)
variable {J : Type w} [Category.{w'} J]
variable (F : J ⥤ C)

section

variable [PreservesLimit F G]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.preserves_lift_mapCone** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：preserves_lift_mapCone (c₁ c₂ : Cone F) (t : IsLimit c₁) : (isLimitOfPrese
rves G t).lift (G.mapCone c₂) = G.map (t.lift c₂)
参数：c₁ c₂ : Cone F；t : IsLimit c₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsLimit.uniq`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃}
 C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem preserves_lift_mapCone (c₁ c₂ : Cone F) (t : IsLimit c₁) :
    (isLimitOfPreserves G t).lift (G.mapCone c₂) = G.map (t.lift c₂) :=
  ((isLimitOfPreserves G t).uniq (G.mapCone c₂) _ (by simp [← G.map_comp])).symm

variable [HasLimit F]

/-- If `G` preserves limits, we have an isomorphism from the image of the limit of a functor `F`
to the limit of the functor `F ⋙ G`.
-/
/-
**CategoryTheory.preservesLimitIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：preservesLimitIso : G.obj (limit F) ≅ limit (F ⋙ G)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `G` preserves limits, we have an isomorphism from the image of the limit of a
 functor `F`
to the limit of the functor `F ⋙ G`.
-/
def preservesLimitIso : G.obj (limit F) ≅ limit (F ⋙ G) :=
  (isLimitOfPreserves G (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.preservesLimitIso_hom_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preservesLimitIso_hom_π (j) :
    (preservesLimitIso G F).hom ≫ limit.π _ j = G.map (limit.π F j) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ j

@[reassoc (attr := simp)]
/-
**CategoryTheory.preservesLimitIso_inv_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preservesLimitIso_inv_π (j) :
    (preservesLimitIso G F).inv ≫ G.map (limit.π F j) = limit.π _ j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ j

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.lift_comp_preservesLimitIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory`。
形式化陈述：lift_comp_preservesLimitIso_hom (t : Cone F) : G.map (limit.lift _ t) ≫ (p
reservesLimitIso G F).hom = limit.lift (F ⋙ G) (G.mapCone _)
参数：t : Cone F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.preservesLimitIso_hom_π`：preservesLimitIso_hom_π (j) : (p
reservesLimitIso G F).hom ≫ limit.π _ j = G.map (limit.π F j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_comp_preservesLimitIso_hom (t : Cone F) :
    G.map (limit.lift _ t) ≫ (preservesLimitIso G F).hom =
    limit.lift (F ⋙ G) (G.mapCone _) := by
  ext
  simp [← G.map_comp]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (limit.post F G) :=
  show IsIso (preservesLimitIso G F).hom from inferInstance

variable [PreservesLimitsOfShape J G] [HasLimitsOfShape J D] [HasLimitsOfShape J C]

set_option backward.defeqAttrib.useBackward true in
/-- If `C, D` has all limits of shape `J`, and `G` preserves them, then `preservesLimitsIso` is
functorial w.r.t. `F`. -/
@[simps!]
/-
**CategoryTheory.preservesLimitNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：preservesLimitNatIso : lim ⋙ G ≅ (Functor.whiskeringRight J C D).obj G ⋙ l
im
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `C, D` has all limits of shape `J`, and `G` preserves them, then `preservesLi
mitsIso` is
functorial w.r.t. `F`.
-/
def preservesLimitNatIso : lim ⋙ G ≅ (Functor.whiskeringRight J C D).obj G ⋙ lim :=
  NatIso.ofComponents (fun F => preservesLimitIso G F)
    (by
      intro _ _ f
      apply limit.hom_ext; intro j
      dsimp
      simp only [preservesLimitIso_hom_π, Functor.whiskerRight_app, limMap_π, Category.assoc,
        preservesLimitIso_hom_π_assoc, ← G.map_comp])

end

section

variable [HasLimit F] [HasLimit (F ⋙ G)]

/-- If the comparison morphism `G.obj (limit F) ⟶ limit (F ⋙ G)` is an isomorphism, then `G`
preserves limits of `F`. -/
/-
**CategoryTheory.preservesLimit_of_isIso_post** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：preservesLimit_of_isIso_post [IsIso (limit.post F G)] : PreservesLimit F G
参数：limit.post F G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…

--- 原说明 ---
If the comparison morphism `G.obj (limit F) ⟶ limit (F ⋙ G)` is an isomorphism, 
then `G`
preserves limits of `F`.
-/
lemma preservesLimit_of_isIso_post [IsIso (limit.post F G)] : PreservesLimit F G :=
  preservesLimit_of_preserves_limit_cone (limit.isLimit F) (by
    convert! IsLimit.ofPointIso (limit.isLimit (F ⋙ G))
    assumption)

end

section

variable [PreservesColimit F G]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.preserves_desc_mapCocone** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：preserves_desc_mapCocone (c₁ c₂ : Cocone F) (t : IsColimit c₁) : (isColimi
tOfPreserves G t).desc (G.mapCocone _) = G.map (t.desc c₂)
参数：c₁ c₂ : Cocone F；t : IsColimit c₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsColimit.uniq`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u
₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem preserves_desc_mapCocone (c₁ c₂ : Cocone F) (t : IsColimit c₁) :
    (isColimitOfPreserves G t).desc (G.mapCocone _) = G.map (t.desc c₂) :=
  ((isColimitOfPreserves G t).uniq (G.mapCocone _) _ (by simp [← G.map_comp])).symm

variable [HasColimit F]

-- TODO: think about swapping the order here
/-- If `G` preserves colimits, we have an isomorphism from the image of the colimit of a functor `F`
to the colimit of the functor `F ⋙ G`.
-/
/-
**CategoryTheory.preservesColimitIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：preservesColimitIso : G.obj (colimit F) ≅ colimit (F ⋙ G)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitCompOfPreservesColimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `G` preserves colimits, we have an isomorphism from the image of the colimit 
of a functor `F`
to the colimit of the functor `F ⋙ G`.
-/
def preservesColimitIso : G.obj (colimit F) ≅ colimit (F ⋙ G) :=
  (isColimitOfPreserves G (colimit.isColimit _)).coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_preservesColimitIso_inv (j : J) :
    colimit.ι _ j ≫ (preservesColimitIso G F).inv = G.map (colimit.ι F j) :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ (colimit.isColimit (F ⋙ G)) j

@[reassoc (attr := simp)]
/-
**CategoryTheory.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_preservesColimitIso_hom (j : J) :
    G.map (colimit.ι F j) ≫ (preservesColimitIso G F).hom = colimit.ι (F ⋙ G) j :=
  (isColimitOfPreserves G (colimit.isColimit _)).comp_coconePointUniqueUpToIso_hom _ j

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.preservesColimitIso_inv_comp_desc** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：preservesColimitIso_inv_comp_desc (t : Cocone F) : (preservesColimitIso G 
F).inv ≫ G.map (colimit.desc _ t) = colimit.desc _ (G.mapCocone t)
参数：t : Cocone F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitCompOfPreservesColimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ι_preservesColimitIso_inv_assoc`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preservesColimitIso_inv_comp_desc (t : Cocone F) :
    (preservesColimitIso G F).inv ≫ G.map (colimit.desc _ t) =
    colimit.desc _ (G.mapCocone t) := by
  ext
  simp [← G.map_comp]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (colimit.post F G) :=
  show IsIso (preservesColimitIso G F).inv from inferInstance

variable [PreservesColimitsOfShape J G] [HasColimitsOfShape J D] [HasColimitsOfShape J C]

set_option backward.defeqAttrib.useBackward true in
/-- If `C, D` has all colimits of shape `J`, and `G` preserves them, then `preservesColimitIso`
is functorial w.r.t. `F`. -/
@[simps!]
/-
**CategoryTheory.preservesColimitNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：preservesColimitNatIso : colim ⋙ G ≅ (Functor.whiskeringRight J C D).obj G
 ⋙ colim
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `C, D` has all colimits of shape `J`, and `G` preserves them, then `preserves
ColimitIso`
is functorial w.r.t. `F`.
-/
def preservesColimitNatIso : colim ⋙ G ≅ (Functor.whiskeringRight J C D).obj G ⋙ colim :=
  NatIso.ofComponents (fun F => preservesColimitIso G F)
    (by
      intro _ _ f
      rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
      apply colimit.hom_ext; intro j
      dsimp
      rw [ι_colimMap_assoc]
      simp only [ι_preservesColimitIso_inv, Functor.whiskerRight_app,
        ι_preservesColimitIso_inv_assoc, ← G.map_comp]
      rw [ι_colimMap])

end

section

variable [HasColimit F] [HasColimit (F ⋙ G)]

/-- If the comparison morphism `colimit (F ⋙ G) ⟶ G.obj (colimit F)` is an isomorphism, then `G`
preserves colimits of `F`. -/
/-
**CategoryTheory.preservesColimit_of_isIso_post** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
形式化陈述：preservesColimit_of_isIso_post [IsIso (colimit.post F G)] : PreservesColim
it F G
参数：colimit.post F G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…

--- 原说明 ---
If the comparison morphism `colimit (F ⋙ G) ⟶ G.obj (colimit F)` is an isomorphi
sm, then `G`
preserves colimits of `F`.
-/
lemma preservesColimit_of_isIso_post [IsIso (colimit.post F G)] : PreservesColimit F G :=
  preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F) (by
    convert! IsColimit.ofPointIso (colimit.isColimit (F ⋙ G))
    assumption)

end

end CategoryTheory

