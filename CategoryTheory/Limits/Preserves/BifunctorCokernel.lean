/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Action of bifunctors on cokernels

Let `c₁` (resp. `c₂`) be a cokernel cofork for a morphism `f₁ : X₁ ⟶ Y₁`
in a category `C₁` (resp. `f₂ : X₂ ⟶ Y₂` in `C₂`). Given a bifunctor `F : C₁ ⥤ C₂ ⥤ C`,
we construct a cokernel cofork with point `(F.obj c₁.pt).obj c₂.pt` for
the obvious morphism `(F.obj X₁).obj Y₂ ⨿ (F.obj Y₁).obj X₂ ⟶ (F.obj Y₁).obj Y₂`,
and show that it is a colimit when both coforks are colimit, the cokernel of `f₁`
is preserved by `F.obj c₁.pt` and the cokernel of `f₂` is preserved by
`F.flip.obj X₁` and `F.flip.obj Y₁`.

-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C₁ C₂ C : Type*} [Category* C₁] [Category* C₂] [Category* C]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms C]

namespace CokernelCofork

variable {X₁ Y₁ : C₁} {f₁ : X₁ ⟶ Y₁} {c₁ : CokernelCofork f₁} (hc₁ : IsColimit c₁)
  {X₂ Y₂ : C₂} {f₂ : X₂ ⟶ Y₂} {c₂ : CokernelCofork f₂} (hc₂ : IsColimit c₂)
  (F : C₁ ⥤ C₂ ⥤ C)
  [(F.obj c₁.pt).PreservesZeroMorphisms]
  [F.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
variable (c₁ c₂) in
/-- Let `c₁` (resp. `c₂`) be a cokernel cofork for a morphism `f₁ : X₁ ⟶ Y₁`
in a category `C₁` (resp. `f₂ : X₂ ⟶ Y₂` in `C₂`). Given a bifunctor `F : C₁ ⥤ C₂ ⥤ C`,
this is the cokernel cofork with point `(F.obj c₁.pt).obj c₂.pt` for
the obvious morphism `(F.obj X₁).obj Y₂ ⨿ (F.obj Y₁).obj X₂ ⟶ (F.obj Y₁).obj Y₂`. -/
/-
**CategoryTheory.Limits.CokernelCofork.mapBifunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.Limits.CokernelCofork`。
形式化陈述：mapBifunctor [HasBinaryCoproduct ((F.obj X₁).obj Y₂) ((F.obj Y₁).obj X₂)] 
: CokernelCofork (coprod.desc ((F.map f₁).app Y₂) ((F.obj Y₁).map f₂))
参数：(F.obj X₁).obj Y₂；(F.obj Y₁).obj X₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `c₁` (resp. `c₂`) be a cokernel cofork for a morphism `f₁ : X₁ ⟶ Y₁`
in a category `C₁` (resp. `f₂ : X₂ ⟶ Y₂` in `C₂`). Given a bifunctor `F : C₁ ⥤ C
₂ ⥤ C`,
this is the cokernel cofork with point `(F.obj c₁.pt).obj c₂.pt` for
the obvious morphism `(F.obj X₁).obj Y₂ ⨿ (F.obj Y₁).obj X₂ ⟶ (F.obj Y₁).obj Y₂`
.
-/
noncomputable abbrev mapBifunctor [HasBinaryCoproduct ((F.obj X₁).obj Y₂) ((F.obj Y₁).obj X₂)] :
    CokernelCofork (coprod.desc ((F.map f₁).app Y₂) ((F.obj Y₁).map f₂)) :=
  CokernelCofork.ofπ (Z := (F.obj c₁.pt).obj c₂.pt)
    ((F.map c₁.π).app Y₂ ≫ (F.obj c₁.pt).map c₂.π) (by
      ext
      · simp [← NatTrans.comp_app_assoc, ← Functor.map_comp]
      · simp [← Functor.map_comp])

variable [PreservesColimit (parallelPair f₂ 0) (F.obj c₁.pt)]
  [PreservesColimit (parallelPair f₁ 0) (F.flip.obj Y₂)]

namespace isColimitMapBifunctor

include hc₁ hc₂

/-
**CategoryTheory.Limits.CokernelCofork.isColimitMapBifunctor.hom_ext** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Limits.CokernelCofork.isColimitMapBifunctor`。
形式化陈述：hom_ext {T : C} {f g : (F.obj c₁.pt).obj c₂.pt ⟶ T} (h : (F.map c₁.π).app 
Y₂ ≫ (F.obj c₁.pt).map c₂.π ≫ f = (F.map c₁.π).app Y₂ ≫ (F.obj c₁.pt).map c₂.π ≫
 g) : f = g
参数：F.obj c₁.pt；h : (F.map c₁.π).app Y₂ ≫ (F.obj c₁.pt).map c₂.π ≫ f = (F.map c₁.
π).app Y₂ ≫ (F.obj c₁.pt).map c₂.π ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.hom_ext`：∀ {C : Type u} {X Y : C}
 [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Lim
its.Cofork f g}   (hs : CategoryTheo…
· 使用定理 `CategoryTheory.Functor.instPreservesZeroMorphismsObjFlip`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
-/
lemma hom_ext {T : C} {f g : (F.obj c₁.pt).obj c₂.pt ⟶ T}
    (h : (F.map c₁.π).app Y₂ ≫ (F.obj c₁.pt).map c₂.π ≫ f =
      (F.map c₁.π).app Y₂ ≫ (F.obj c₁.pt).map c₂.π ≫ g) : f = g :=
  Cofork.IsColimit.hom_ext (mapIsColimit _ hc₂ (F.obj c₁.pt))
    (Cofork.IsColimit.hom_ext (mapIsColimit _ hc₁ (F.flip.obj Y₂)) h)

variable [HasBinaryCoproduct ((F.obj X₁).obj Y₂) ((F.obj Y₁).obj X₂)]
  [PreservesColimit (parallelPair f₁ 0) (F.flip.obj X₂)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.CokernelCofork.isColimitMapBifunctor.exists_desc** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CokernelCofork.isColimitMapBifunctor`。
形式化陈述：exists_desc (s : CokernelCofork (coprod.desc ((F.map f₁).app Y₂) ((F.obj Y
₁).map f₂))) : exists (l : (F.obj c₁.pt).obj c₂.pt ⟶ s.pt), (F.map c₁.π).app Y₂ 
≫ (F.obj c₁.pt).map c₂.π ≫ l = s.π
参数：s : CokernelCofork (coprod.desc ((F.map f₁).app Y₂) ((F.obj Y₁).map f₂))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instPreservesZeroMorphismsObjFlip`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `CategoryTheory.Limits.CokernelCofork.condition`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   {f : X ⟶ Y} (s : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.coprod.inl_desc_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasB
inaryCoproduct X Y] (f : X ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.hom_ext`：∀ {C : Type u} {X Y : C}
 [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Lim
its.Cofork f g}   (hs : CategoryTheo…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.coprod.inr_desc_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasB
inaryCoproduct X Y] (f : X ⟶ W) (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_desc (s : CokernelCofork (coprod.desc ((F.map f₁).app Y₂) ((F.obj Y₁).map f₂))) :
    ∃ (l : (F.obj c₁.pt).obj c₂.pt ⟶ s.pt),
      (F.map c₁.π).app Y₂ ≫ (F.obj c₁.pt).map c₂.π ≫ l = s.π := by
  obtain ⟨l, hl⟩ := Cofork.IsColimit.desc' (mapIsColimit _ hc₁ (F.flip.obj Y₂)) s.π (by
    have := coprod.inl ≫= s.condition
    rw [coprod.inl_desc_assoc, comp_zero] at this
    rwa [zero_comp])
  obtain ⟨l', hl'⟩ := Cofork.IsColimit.desc' (mapIsColimit _ hc₂ (F.obj c₁.pt)) l (by
    have := coprod.inr ≫= s.condition
    rw [coprod.inr_desc_assoc, ← dsimp% hl, NatTrans.naturality_assoc, comp_zero] at this
    apply Cofork.IsColimit.hom_ext (mapIsColimit _ hc₁ (F.flip.obj X₂))
    rwa [zero_comp, comp_zero])
  exact ⟨l', by cat_disch⟩

end isColimitMapBifunctor

variable [HasBinaryCoproduct ((F.obj X₁).obj Y₂) ((F.obj Y₁).obj X₂)]
  [PreservesColimit (parallelPair f₁ 0) (F.flip.obj X₂)]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open isColimitMapBifunctor in
/-- Let `c₁` (resp. `c₂`) be a colimit cokernel cofork for a morphism `f₁ : X₁ ⟶ Y₁`
in a category `C₁` (resp. `f₂ : X₂ ⟶ Y₂` in `C₂`). If `F : C₁ ⥤ C₂ ⥤ C` is a bifunctor,
then `(F.obj c₁.pt).obj c₂.pt` identifies to the cokernel of the morphism
`(F.obj X₁).obj Y₂ ⨿ (F.obj Y₁).obj X₂ ⟶ (F.obj Y₁).obj Y₂`
when the cokernel of `f₁` is preserved by `F.obj c₁.pt` and the cokernel of `f₂`
is preserved by `F.flip.obj X₁` and `F.flip.obj Y₁`. -/
/-
**CategoryTheory.Limits.CokernelCofork.isColimitMapBifunctor** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits.CokernelCofork`。
形式化陈述：isColimitMapBifunctor : IsColimit (mapBifunctor c₁ c₂ F)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CokernelCofork.isColimitMapBifunctor.exists_desc`：
exists_desc (s : CokernelCofork (coprod.desc ((F.map f₁).app Y₂) ((F.obj Y₁).map
 f₂))) : exists (l : (F.obj c₁.pt).obj c₂.pt ⟶ s.pt), (F.map…

--- 原说明 ---
Let `c₁` (resp. `c₂`) be a colimit cokernel cofork for a morphism `f₁ : X₁ ⟶ Y₁`
in a category `C₁` (resp. `f₂ : X₂ ⟶ Y₂` in `C₂`). If `F : C₁ ⥤ C₂ ⥤ C` is a bif
unctor,
then `(F.obj c₁.pt).obj c₂.pt` identifies to the cokernel of the morphism
`(F.obj X₁).obj Y₂ ⨿ (F.obj Y₁).obj X₂ ⟶ (F.obj Y₁).obj Y₂`
when the cokernel of `f₁` is preserved by `F.obj c₁.pt` and the cokernel of `f₂`
is preserved by `F.flip.obj X₁` and `F.flip.obj Y₁`.
-/
noncomputable def isColimitMapBifunctor :
    IsColimit (mapBifunctor c₁ c₂ F) :=
  Cofork.IsColimit.mk _
    (fun s ↦ (exists_desc hc₁ hc₂ F s).choose)
    (fun s ↦ by simpa using (exists_desc hc₁ hc₂ F s).choose_spec)
    (fun s m hm ↦ hom_ext hc₁ hc₂ F (by
      rw [(exists_desc hc₁ hc₂ F s).choose_spec, ← dsimp% hm, Category.assoc]))

end CokernelCofork

end CategoryTheory.Limits

