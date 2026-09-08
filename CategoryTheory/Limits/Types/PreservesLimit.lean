/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
public import Mathlib.CategoryTheory.ObjectProperty.Local

/-!
# Presheaves of types which preserves a limit

Let `F : J ⥤ Cᵒᵖ` be a functor. We show that a presheaf `P : Cᵒᵖ ⥤ Type w`
preserves the limit of `F` iff `P` is a local object with respect to a suitable
family of morphisms in `Cᵒᵖ ⥤ Type w` (this family contains `1` or `0` morphism
depending on whether the limit of `F` exists or not).

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits Opposite

namespace Presheaf

section

variable {C : Type u} [Category.{v} C]
  {J : Type u'} [Category.{v'} J] [LocallySmall.{w} C]
  {F : J ⥤ Cᵒᵖ} (c : Cone F) {c' : Cocone (F.leftOp ⋙ shrinkYoneda.{w})}
  (hc : IsLimit c) (hc' : IsColimit c') (P : Cᵒᵖ ⥤ Type w)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {P} in
/-- Let `F : J ⥤ Cᵒᵖ` be a functor, `c'` a colimit cocone for `F.leftOp ⋙ shrinkYoneda.{w}`.
For any `P : Cᵒᵖ ⥤ Type w`, this is the bijection between `c'.pt ⟶ P` and the type
of sections of `F ⋙ P`. -/
@[simps -isSimp symm_apply apply_coe]
/-
**CategoryTheory.Presheaf.coconeCompShrinkYonedaHomEquiv** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Presheaf`。
形式化陈述：coconeCompShrinkYonedaHomEquiv : (c'.pt ⟶ P) ≃ (F ⋙ P).sections where toFu
n f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Let `F : J ⥤ Cᵒᵖ` be a functor, `c'` a colimit cocone for `F.leftOp ⋙ shrinkYone
da.{w}`.
For any `P : Cᵒᵖ ⥤ Type w`, this is the bijection between `c'.pt ⟶ P` and the ty
pe
of sections of `F ⋙ P`.
-/
noncomputable def coconeCompShrinkYonedaHomEquiv :
    (c'.pt ⟶ P) ≃ (F ⋙ P).sections where
  toFun f :=
    { val j := shrinkYonedaEquiv (c'.ι.app (op j) ≫ f)
      property {X X'} g := by
        dsimp
        rw [← dsimp% c'.w g.op, Category.assoc]
        conv_rhs => rw [shrinkYonedaEquiv_comp]
        rw [shrinkYonedaEquiv_shrinkYoneda_map]
        apply map_shrinkYonedaEquiv }
  invFun s := hc'.desc (Cocone.mk _
    { app j := shrinkYonedaEquiv.symm (s.val j.unop)
      naturality j₁ j₂ f := by
        rw [← s.property f.unop]
        dsimp
        rw [shrinkYonedaEquiv_symm_map, Category.comp_id] })
  left_inv f := hc'.hom_ext (by simp)
  right_inv u := by cat_disch

/-- Let `F : J ⥤ Cᵒᵖ` be a functor, `c'` a colimit cocone for `F.leftOp ⋙ shrinkYoneda.{w}`.
For any cone `c` for `F`, this is the canonical natural transformation
`c'.pt ⟶ shrinkYoneda.{w}.obj c.pt.unop`. -/
/-
**CategoryTheory.Presheaf.coconePtToShrinkYoneda** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Presheaf`。
形式化陈述：coconePtToShrinkYoneda : c'.pt ⟶ shrinkYoneda.{w}.obj c.pt.unop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `F : J ⥤ Cᵒᵖ` be a functor, `c'` a colimit cocone for `F.leftOp ⋙ shrinkYone
da.{w}`.
For any cone `c` for `F`, this is the canonical natural transformation
`c'.pt ⟶ shrinkYoneda.{w}.obj c.pt.unop`.
-/
noncomputable def coconePtToShrinkYoneda :
    c'.pt ⟶ shrinkYoneda.{w}.obj c.pt.unop :=
  hc'.desc (shrinkYoneda.{w}.mapCocone (coconeLeftOpOfCone c))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {P} in
@[reassoc]
/-
**CategoryTheory.Presheaf.coconePtToShrinkYoneda_comp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Presheaf`。
形式化陈述：coconePtToShrinkYoneda_comp (x : P.obj c.pt) : coconePtToShrinkYoneda c hc
' ≫ shrinkYonedaEquiv.symm x = (coconeCompShrinkYonedaHomEquiv hc').symm (Types.
sectionOfCone (P.mapCone c) x)
参数：x : P.obj c.pt。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.fac_assoc`：∀ {J : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{
v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.shrinkYonedaEquiv_symm_map`：shrinkYonedaEquiv_symm_map {X
 Y : Cᵒᵖ} (f : X ⟶ Y) {P : Cᵒᵖ ⥤ Type w} (t : P.obj X) : shrinkYonedaEquiv.symm 
(P.map f t) = shrinkYoneda.map …
-/
lemma coconePtToShrinkYoneda_comp (x : P.obj c.pt) :
    coconePtToShrinkYoneda c hc' ≫ shrinkYonedaEquiv.symm x =
      (coconeCompShrinkYonedaHomEquiv hc').symm
        (Types.sectionOfCone (P.mapCone c) x) := by
  refine hc'.hom_ext (fun _ ↦ ?_)
  dsimp [coconePtToShrinkYoneda, coconeCompShrinkYonedaHomEquiv_symm_apply]
  rw [hc'.fac_assoc, hc'.fac]
  exact (shrinkYonedaEquiv_symm_map _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Presheaf.nonempty_isLimit_mapCone_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Presheaf`。
形式化陈述：nonempty_isLimit_mapCone_iff : Nonempty (IsLimit (P.mapCone c)) ↔ (Morphis
mProperty.single (coconePtToShrinkYoneda c hc')).isLocal P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.isLimit_iff_bijective_sectionOfCone`：isLimit
_iff_bijective_sectionOfCone (c : Cone F) : Nonempty (IsLimit c) ↔ (Types.sectio
nOfCone c).Bijective
· 使用引理 `CategoryTheory.MorphismProperty.isLocal_single_iff_bijective`：isLocal_si
ngle_iff_bijective {X Y : C} (f : X ⟶ Y) (Z : C) : (MorphismProperty.single f).i
sLocal Z ↔ (Function.Bijective (fun (g : _ ⟶ Z) =>…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonempty_isLimit_mapCone_iff :
    Nonempty (IsLimit (P.mapCone c)) ↔
      (MorphismProperty.single (coconePtToShrinkYoneda c hc')).isLocal P := by
  rw [Types.isLimit_iff_bijective_sectionOfCone,
    MorphismProperty.isLocal_single_iff_bijective,
    ← Function.Bijective.of_comp_iff' (coconeCompShrinkYonedaHomEquiv hc').symm.bijective,
    ← Function.Bijective.of_comp_iff _ shrinkYonedaEquiv.bijective]
  convert Iff.rfl using 2
  ext : 1
  simp [← coconePtToShrinkYoneda_comp]

variable {c}

include hc in
/-
**CategoryTheory.Presheaf.preservesLimit_eq_isLocal_single** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Presheaf`。
形式化陈述：preservesLimit_eq_isLocal_single : ObjectProperty.preservesLimit F = (Morp
hismProperty.single (coconePtToShrinkYoneda c hc')).isLocal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Presheaf.nonempty_isLimit_mapCone_iff`：nonempty_isLimit_m
apCone_iff : Nonempty (IsLimit (P.mapCone c)) ↔ (MorphismProperty.single (cocone
PtToShrinkYoneda c hc')).isLocal P
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
-/
lemma preservesLimit_eq_isLocal_single :
    ObjectProperty.preservesLimit F =
      (MorphismProperty.single (coconePtToShrinkYoneda c hc')).isLocal := by
  ext P
  rw [← nonempty_isLimit_mapCone_iff c hc' P]
  exact ⟨fun _ ↦ ⟨isLimitOfPreserves P hc⟩,
    fun ⟨h⟩ ↦ preservesLimit_of_preserves_limit_cone hc h⟩

variable (F) [Small.{w} J]

/-- Auxiliary definition for `Presheaf.preservesLimitHomFamily`. -/
/-
**CategoryTheory.Presheaf.preservesLimitHomFamilySrc** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.Presheaf`。
形式化陈述：preservesLimitHomFamilySrc
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Presheaf.preservesLimitHomFamily`.
-/
noncomputable abbrev preservesLimitHomFamilySrc :=
  colimit (F.leftOp ⋙ shrinkYoneda)

/-- Auxiliary definition for `Presheaf.preservesLimitHomFamily`. -/
/-
**CategoryTheory.Presheaf.preservesLimitHomFamilyTgt** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.Presheaf`。
形式化陈述：preservesLimitHomFamilyTgt (h : PLift (HasLimit F))
参数：h : PLift (HasLimit F)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Presheaf.preservesLimitHomFamily`.
-/
noncomputable abbrev preservesLimitHomFamilyTgt (h : PLift (HasLimit F)) :=
  letI := h.down
  shrinkYoneda.obj (limit F).unop

/-- Let `F : J ⥤ Cᵒᵖ` be a functor. This is the family of morphisms
which consists of the single morphism
`colimit (F.leftOp ⋙ shrinkYoneda) ⟶ shrinkYoneda.obj (limit F).unop`
if `F` has a limit, or is the empty family otherwise. -/
/-
**CategoryTheory.Presheaf.preservesLimitHomFamily** 是 Mathlib 中的一个缩写定义，位于命名空间 `C
ategoryTheory.Presheaf`。
形式化陈述：preservesLimitHomFamily (h : PLift (HasLimit F)) : preservesLimitHomFamily
Src F ⟶ preservesLimitHomFamilyTgt F h
参数：h : PLift (HasLimit F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `F : J ⥤ Cᵒᵖ` be a functor. This is the family of morphisms
which consists of the single morphism
`colimit (F.leftOp ⋙ shrinkYoneda) ⟶ shrinkYoneda.obj (limit F).unop`
if `F` has a limit, or is the empty family otherwise.
-/
noncomputable abbrev preservesLimitHomFamily (h : PLift (HasLimit F)) :
    preservesLimitHomFamilySrc F ⟶ preservesLimitHomFamilyTgt F h :=
  letI := h.down
  coconePtToShrinkYoneda (limit.cone F) (colimit.isColimit _)
/-
**CategoryTheory.Presheaf.preservesLimit_eq_isLocal** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Presheaf`。
形式化陈述：preservesLimit_eq_isLocal : ObjectProperty.preservesLimit F = (MorphismPro
perty.ofHoms (preservesLimitHomFamily F)).isLocal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presheaf.preservesLimit_eq_isLocal_single`：preservesLimit
_eq_isLocal_single : ObjectProperty.preservesLimit F = (MorphismProperty.single 
(coconePtToShrinkYoneda c hc')).isLocal
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma preservesLimit_eq_isLocal :
    ObjectProperty.preservesLimit F =
      (MorphismProperty.ofHoms (preservesLimitHomFamily F)).isLocal := by
  ext
  by_cases hF : HasLimit F
  · rw [preservesLimit_eq_isLocal_single (limit.isLimit F) (colimit.isColimit _)]
    convert Iff.rfl
    ext
    exact ⟨fun ⟨_⟩ ↦ ⟨⟨⟩⟩, fun ⟨_⟩ ↦ ⟨⟨hF⟩⟩⟩
  · exact ⟨fun _ _ _ _ ⟨h⟩ ↦ (hF h.down).elim,
      fun _ ↦ ⟨fun hc ↦ (hF ⟨_, hc⟩).elim⟩⟩
/-
**CategoryTheory.Presheaf.preservesLimitsOfShape_eq_isLocal** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：preservesLimitsOfShape_eq_isLocal : ObjectProperty.preservesLimitsOfShape 
J = (⨆ (F : J ⥤ Cᵒᵖ), MorphismProperty.ofHoms (preservesLimitHomFamily F)).isLoc
al
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.preservesLimitsOfShape_eq_iSup`：preservesL
imitsOfShape_eq_iSup : preservesLimitsOfShape (J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Presheaf.preservesLimit_eq_isLocal`：preservesLimit_eq_isL
ocal : ObjectProperty.preservesLimit F = (MorphismProperty.ofHoms (preservesLimi
tHomFamily F)).isLocal
· 使用引理 `CategoryTheory.MorphismProperty.isLocal_iSup`：isLocal_iSup {ι : Sort*} (
W : ι -> MorphismProperty C) : (⨆ (i : ι), W i).isLocal = ⨅ (i : ι), (W i).isLoc
al
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preservesLimitsOfShape_eq_isLocal :
    ObjectProperty.preservesLimitsOfShape J =
      (⨆ (F : J ⥤ Cᵒᵖ), MorphismProperty.ofHoms (preservesLimitHomFamily F)).isLocal := by
  simp only [ObjectProperty.preservesLimitsOfShape_eq_iSup,
    MorphismProperty.isLocal_iSup, preservesLimit_eq_isLocal]

end

end Presheaf

end CategoryTheory

