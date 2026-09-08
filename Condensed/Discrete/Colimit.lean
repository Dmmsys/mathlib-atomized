/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Discrete.LocallyConstant
public import Mathlib.Condensed.Equivalence
public import Mathlib.Topology.Category.LightProfinite.Extend

/-!

# The condensed set given by left Kan extension from `FintypeCat` to `Profinite`.

This file provides the necessary API to prove that a condensed set `X` is discrete if and only if
for every profinite set `S = limᵢSᵢ`, `X(S) ≅ colimᵢX(Sᵢ)`, and the analogous result for light
condensed sets.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Functor Limits FintypeCat CompHausLike.LocallyConstant

namespace Condensed

section LocallyConstantAsColimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {F : I ⥤ FintypeCat.{u}}
  (c : Cone <| F ⋙ toProfinite) (X : Type (u + 1))

/-- The presheaf on `Profinite` of locally constant functions to `X`. -/
/-
**Condensed.locallyConstantPresheaf** 是 Mathlib 中的一个缩写定义，位于命名空间 `Condensed`。
形式化陈述：locallyConstantPresheaf : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presheaf on `Profinite` of locally constant functions to `X`.
-/
abbrev locallyConstantPresheaf : Profinite.{u}ᵒᵖ ⥤ Type (u + 1) :=
  CompHausLike.LocallyConstant.functorToPresheaves.{u, u + 1}.obj X

#adaptation_note
/--
In this declaration and `isColimitLocallyConstantPresheaf`, `coe_comp` interferes with rewriting via
`Cone.w`, so we needed to manually exclude it.
-/
set_option backward.defeqAttrib.useBackward true in
/--
The functor `locallyConstantPresheaf` takes cofiltered limits of finite sets with surjective
projection maps to colimits.
-/
/-
**Condensed.isColimitLocallyConstantPresheaf** 是 Mathlib 中的一个定义，位于命名空间 `Condense
d`。
形式化陈述：isColimitLocallyConstantPresheaf (hc : IsLimit c) [forall i, Epi (c.π.app 
i)] : IsColimit (locallyConstantPresheaf X).mapCocone c.op
参数：hc : IsLimit c；c.π.app i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `locallyConstantPresheaf` takes cofiltered limits of finite sets wit
h surjective
projection maps to colimits.
-/
noncomputable def isColimitLocallyConstantPresheaf (hc : IsLimit c) [∀ i, Epi (c.π.app i)] :
    IsColimit <| (locallyConstantPresheaf X).mapCocone c.op := by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, u} c hc f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (c.π.app i).hom.hom = fj.comap (c.π.app j).hom.hom)
    obtain ⟨k, ki, kj, _⟩ := IsCofilteredOrEmpty.cone_objs i j
    refine ⟨⟨k⟩, ki.op, kj.op, ?_⟩
    dsimp
    ext x
    obtain ⟨x, hx⟩ := ((Profinite.epi_iff_surjective (c.π.app k)).mp inferInstance) x
    rw [← hx]
    change fi ((c.π.app k ≫ (F ⋙ toProfinite).map _) x) =
      fj ((c.π.app k ≫ (F ⋙ toProfinite).map _) x)
    have h := LocallyConstant.congr_fun h x
    dsimp [- CompHausLike.coe_comp] -- `coe_comp` prevents rewriting with `c.w`
    rwa [dsimp% c.w, dsimp% c.w]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Condensed.isColimitLocallyConstantPresheaf_desc_apply** 是 Mathlib 中的一个引理，位于命名空
间 `Condensed`。
形式化陈述：isColimitLocallyConstantPresheaf_desc_apply (hc : IsLimit c) [forall i, Ep
i (c.π.app i)] (s : Cocone ((F ⋙ toProfinite).op ⋙ locallyConstantPresheaf X)) (
i : I) (f : LocallyConstant (toProfinite.obj (F.obj i)) X) : dsimp% (isColimitLo
callyConstantPresheaf c X hc).desc s (f.comap (c.π.app i).hom.hom) = s.ι.app ⟨i⟩
 f
参数：hc : IsLimit c；c.π.app i；s : Cocone ((F ⋙ toProfinite).op ⋙ locallyConstantPr
esheaf X)；i : I；f : LocallyConstant (toProfinite.obj (F.obj i)) X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma isColimitLocallyConstantPresheaf_desc_apply (hc : IsLimit c) [∀ i, Epi (c.π.app i)]
    (s : Cocone ((F ⋙ toProfinite).op ⋙ locallyConstantPresheaf X))
    (i : I) (f : LocallyConstant (toProfinite.obj (F.obj i)) X) :
    dsimp% (isColimitLocallyConstantPresheaf c X hc).desc s (f.comap (c.π.app i).hom.hom) =
      s.ι.app ⟨i⟩ f := by
  change ((((locallyConstantPresheaf X).mapCocone c.op).ι.app ⟨i⟩) ≫
    (isColimitLocallyConstantPresheaf c X hc).desc s) _ = _
  rw [(isColimitLocallyConstantPresheaf c X hc).fac]

/-- `isColimitLocallyConstantPresheaf` in the case of `S.asLimit`. -/
/-
**Condensed.isColimitLocallyConstantPresheafDiagram** 是 Mathlib 中的一个定义，位于命名空间 `C
ondensed`。
形式化陈述：isColimitLocallyConstantPresheafDiagram (S : Profinite) : IsColimit (local
lyConstantPresheaf X).mapCocone S.asLimitCone.op
参数：S : Profinite。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.instEpiAppDiscreteQuotientCarrierToTopTotallyDisconnectedSpace
πAsLimitCone`：∀ (S : Profinite) (i : DiscreteQuotient ↑S.toTop), CategoryTheory.
Epi (S.asLimitCone.π.app i)

--- 原说明 ---
`isColimitLocallyConstantPresheaf` in the case of `S.asLimit`.
-/
noncomputable def isColimitLocallyConstantPresheafDiagram (S : Profinite) :
    IsColimit <| (locallyConstantPresheaf X).mapCocone S.asLimitCone.op :=
  isColimitLocallyConstantPresheaf _ _ S.asLimit

@[simp]
/-
**Condensed.isColimitLocallyConstantPresheafDiagram_desc_apply** 是 Mathlib 中的一个引
理，位于命名空间 `Condensed`。
形式化陈述：isColimitLocallyConstantPresheafDiagram_desc_apply (S : Profinite) (s : Co
cone (S.diagram.op ⋙ locallyConstantPresheaf X)) (i : DiscreteQuotient S) (f : L
ocallyConstant (S.diagram.obj i) X) : dsimp% (isColimitLocallyConstantPresheafDi
agram X S).desc s (f.comap (S.asLimitCone.π.app i).hom.hom) = s.ι.app ⟨i⟩ f
参数：S : Profinite；s : Cocone (S.diagram.op ⋙ locallyConstantPresheaf X)；i : Discr
eteQuotient S；f : LocallyConstant (S.diagram.obj i) X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Condensed.isColimitLocallyConstantPresheaf_desc_apply`：isColimitLocallyC
onstantPresheaf_desc_apply (hc : IsLimit c) [forall i, Epi (c.π.app i)] (s : Coc
one ((F ⋙ toProfinite).op ⋙ locallyConstant…
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Profinite.instEpiAppDiscreteQuotientCarrierToTopTotallyDisconnectedSpace
πAsLimitCone`：∀ (S : Profinite) (i : DiscreteQuotient ↑S.toTop), CategoryTheory.
Epi (S.asLimitCone.π.app i)
-/
lemma isColimitLocallyConstantPresheafDiagram_desc_apply (S : Profinite)
    (s : Cocone (S.diagram.op ⋙ locallyConstantPresheaf X))
    (i : DiscreteQuotient S) (f : LocallyConstant (S.diagram.obj i) X) :
    dsimp% (isColimitLocallyConstantPresheafDiagram X S).desc s
      (f.comap (S.asLimitCone.π.app i).hom.hom) = s.ι.app ⟨i⟩ f :=
  isColimitLocallyConstantPresheaf_desc_apply S.asLimitCone X S.asLimit s i f

end LocallyConstantAsColimit

/--
Given a presheaf `F` on `Profinite`, `lanPresheaf F` is the left Kan extension of its
restriction to finite sets along the inclusion functor of finite sets into `Profinite`.
-/
/-
**Condensed.lanPresheaf** 是 Mathlib 中的一个缩写定义，位于命名空间 `Condensed`。
形式化陈述：lanPresheaf (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)) : Profinite.{u}ᵒᵖ ⥤ Type 
(u + 1)
参数：F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a presheaf `F` on `Profinite`, `lanPresheaf F` is the left Kan extension o
f its
restriction to finite sets along the inclusion functor of finite sets into `Prof
inite`.
-/
abbrev lanPresheaf (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)) : Profinite.{u}ᵒᵖ ⥤ Type (u + 1) :=
  pointwiseLeftKanExtension toProfinite.op (toProfinite.op ⋙ F)

/--
To presheaves on `Profinite` whose restrictions to finite sets are isomorphic have isomorphic left
Kan extensions.
-/
/-
**Condensed.lanPresheafExt** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：lanPresheafExt {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)} (i : toProfinite.op 
⋙ F ≅ toProfinite.op ⋙ G) : lanPresheaf F ≅ lanPresheaf G
参数：u + 1；i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To presheaves on `Profinite` whose restrictions to finite sets are isomorphic ha
ve isomorphic left
Kan extensions.
-/
def lanPresheafExt {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)}
    (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G) : lanPresheaf F ≅ lanPresheaf G :=
  leftKanExtensionUniqueOfIso _ (pointwiseLeftKanExtensionUnit _ _) i _
    (pointwiseLeftKanExtensionUnit _ _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Condensed.lanPresheafExt_hom** 是 Mathlib 中的一个引理，位于命名空间 `Condensed`。
形式化陈述：lanPresheafExt_hom {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)} (S : Profinite.{
u}ᵒᵖ) (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G) : (lanPresheafExt i).hom.app
 S = colimMap (whiskerLeft (CostructuredArrow.proj toProfinite.op S) i.hom)
参数：u + 1；S : Profinite.{u}ᵒᵖ；i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.leftKanExtensionUniqueOfIso_hom`：∀ {C : Type u_1}
 {H : Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [
inst_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.pointwiseLeftKanExtension_desc_app`：pointwiseLeft
KanExtension_desc_app (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D) : ((pointwiseLeftKanEx
tension L F).descOfIsLeftKanExtension (pointwis…
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Functor.costructuredArrowMapCocone_ι_app`：∀ {C : Type u_1
} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   
[inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.pointwiseLeftKanExtensionUnit_app`：∀ {C : Type u_
1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.pointwiseLeftKanExtension_map`：∀ {C : Type u_1} {
D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [in
st_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
-/
lemma lanPresheafExt_hom {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)} (S : Profinite.{u}ᵒᵖ)
    (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G) : (lanPresheafExt i).hom.app S =
      colimMap (whiskerLeft (CostructuredArrow.proj toProfinite.op S) i.hom) := by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_hom, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Condensed.lanPresheafExt_inv** 是 Mathlib 中的一个引理，位于命名空间 `Condensed`。
形式化陈述：lanPresheafExt_inv {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)} (S : Profinite.{
u}ᵒᵖ) (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G) : (lanPresheafExt i).inv.app
 S = colimMap (whiskerLeft (CostructuredArrow.proj toProfinite.op S) i.inv)
参数：u + 1；S : Profinite.{u}ᵒᵖ；i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.leftKanExtensionUniqueOfIso_inv`：∀ {C : Type u_1}
 {H : Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [
inst_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.pointwiseLeftKanExtension_desc_app`：pointwiseLeft
KanExtension_desc_app (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D) : ((pointwiseLeftKanEx
tension L F).descOfIsLeftKanExtension (pointwis…
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Functor.costructuredArrowMapCocone_ι_app`：∀ {C : Type u_1
} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   
[inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.pointwiseLeftKanExtensionUnit_app`：∀ {C : Type u_
1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.pointwiseLeftKanExtension_map`：∀ {C : Type u_1} {
D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [in
st_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
-/
lemma lanPresheafExt_inv {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)} (S : Profinite.{u}ᵒᵖ)
    (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G) : (lanPresheafExt i).inv.app S =
      colimMap (whiskerLeft (CostructuredArrow.proj toProfinite.op S) i.inv) := by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_inv, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

variable {S : Profinite.{u}} {F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)}
/-
**Condensed.** 是 Mathlib 中的一个实例，位于命名空间 `Condensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Final <| Profinite.Extend.functorOp S.asLimitCone :=
  Profinite.Extend.functorOp_final S.asLimitCone S.asLimit

set_option backward.isDefEq.respectTransparency.types false in
/--
A presheaf, which takes a profinite set written as a cofiltered limit to the corresponding
colimit, agrees with the left Kan extension of its restriction.
-/
/-
**Condensed.lanPresheafIso** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：lanPresheafIso (hF : IsColimit <| F.mapCocone S.asLimitCone.op) : (lanPres
heaf F).obj ⟨S⟩ ≅ F.obj ⟨S⟩
参数：hF : IsColimit <| F.mapCocone S.asLimitCone.op。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Condensed.instFinalOppositeDiscreteQuotientCarrierToTopTotallyDisconnect
edSpaceCostructuredArrowFintypeCatProfiniteOpToProfiniteOpPtAsLimitConeFunctorOp
`：∀ {S : Profinite}, (Profinite.Extend.functorOp S.asLimitCone).Final

--- 原说明 ---
A presheaf, which takes a profinite set written as a cofiltered limit to the cor
responding
colimit, agrees with the left Kan extension of its restriction.
-/
def lanPresheafIso (hF : IsColimit <| F.mapCocone S.asLimitCone.op) :
    (lanPresheaf F).obj ⟨S⟩ ≅ F.obj ⟨S⟩ :=
  (Functor.Final.colimitIso (Profinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hF

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Condensed.lanPresheafIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `Condensed`。
形式化陈述：lanPresheafIso_hom (hF : IsColimit <| F.mapCocone S.asLimitCone.op) : (lan
PresheafIso hF).hom = colimit.desc _ (Profinite.Extend.cocone _ _)
参数：hF : IsColimit <| F.mapCocone S.asLimitCone.op。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.comp_hasColimit`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Condensed.instFinalOppositeDiscreteQuotientCarrierToTopTotallyDisconnect
edSpaceCostructuredArrowFintypeCatProfiniteOpToProfiniteOpPtAsLimitConeFunctorOp
`：∀ {S : Profinite}, (Profinite.Extend.functorOp S.asLimitCone).Final
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.pre_desc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} K]   {C : Type u} [inst…
-/
lemma lanPresheafIso_hom (hF : IsColimit <| F.mapCocone S.asLimitCone.op) :
    (lanPresheafIso hF).hom = colimit.desc _ (Profinite.Extend.cocone _ _) := by
  simp [lanPresheafIso, Final.colimitIso]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `lanPresheafIso` is natural in `S`. -/
/-
**Condensed.lanPresheafNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：lanPresheafNatIso (hF : forall S : Profinite, IsColimit <| F.mapCocone S.a
sLimitCone.op) : lanPresheaf F ≅ F
参数：hF : forall S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lanPresheafIso` is natural in `S`.
-/
def lanPresheafNatIso (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op) :
    lanPresheaf F ≅ F :=
  NatIso.ofComponents (fun ⟨S⟩ ↦ (lanPresheafIso (hF S)))
    fun _ ↦ (by simpa using colimit.hom_ext fun _ ↦ (by simp))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Condensed.lanPresheafNatIso_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `Condensed`。
形式化陈述：lanPresheafNatIso_hom_app (hF : forall S : Profinite, IsColimit <| F.mapCo
cone S.asLimitCone.op) (S : Profiniteᵒᵖ) : (lanPresheafNatIso hF).hom.app S = co
limit.desc _ (Profinite.Extend.cocone _ _)
参数：hF : forall S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op；S : Prof
initeᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Condensed.lanPresheafIso_hom`：lanPresheafIso_hom (hF : IsColimit <| F.ma
pCocone S.asLimitCone.op) : (lanPresheafIso hF).hom = colimit.desc _ (Profinite.
Extend.cocone _ _)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lanPresheafNatIso_hom_app (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op)
    (S : Profiniteᵒᵖ) : (lanPresheafNatIso hF).hom.app S =
      colimit.desc _ (Profinite.Extend.cocone _ _) := by
  simp [lanPresheafNatIso]

/--
`lanPresheaf (locallyConstantPresheaf X)` is a sheaf for the coherent topology on `Profinite`.
-/
/-
**Condensed.lanSheafProfinite** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：lanSheafProfinite (X : Type (u + 1)) : Sheaf (coherentTopology Profinite.{
u}) (Type (u + 1)) where obj
参数：X : Type (u + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lanPresheaf (locallyConstantPresheaf X)` is a sheaf for the coherent topology o
n `Profinite`.
-/
def lanSheafProfinite (X : Type (u + 1)) :
    Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)) where
  obj := lanPresheaf (locallyConstantPresheaf X)
  property := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheafNatIso
      fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _)]
    exact ((CompHausLike.LocallyConstant.functor.{u, u + 1}
      (hs := fun _ _ _ ↦ ((Profinite.effectiveEpi_tfae _).out 0 2).mp)).obj X).property

/-- `lanPresheaf (locallyConstantPresheaf X)` as a condensed set. -/
/-
**Condensed.lanCondensedSet** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：lanCondensedSet (X : Type (u + 1)) : CondensedSet.{u}
参数：X : Type (u + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lanPresheaf (locallyConstantPresheaf X)` as a condensed set.
-/
def lanCondensedSet (X : Type (u + 1)) : CondensedSet.{u} :=
  (ProfiniteCompHaus.equivalence _).functor.obj (lanSheafProfinite X)

variable (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))

/--
The functor which takes a finite set to the set of maps into `F(*)` for a presheaf `F` on
`Profinite`.
-/
@[simps obj map]
/-
**Condensed.finYoneda** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：finYoneda : FintypeCat.{u}ᵒᵖ ⥤ Type (u + 1) where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The functor which takes a finite set to the set of maps into `F(*)` for a preshe
af `F` on
`Profinite`.
-/
def finYoneda : FintypeCat.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj X := X.unop → F.obj (toProfinite.op.obj ⟨of <| PUnit.{u + 1}⟩)
  map f := ↾fun g ↦ g ∘ f.unop

/-- `locallyConstantPresheaf` restricted to finite sets is isomorphic to `finYoneda F`. -/
@[simps! hom_app]
/-
**Condensed.locallyConstantIsoFinYoneda** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：locallyConstantIsoFinYoneda : toProfinite.op ⋙ (locallyConstantPresheaf (F
.obj (toProfinite.op.obj ⟨of PUnit.{u + 1}⟩))) ≅ finYoneda F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
`locallyConstantPresheaf` restricted to finite sets is isomorphic to `finYoneda 
F`.
-/
def locallyConstantIsoFinYoneda :
    toProfinite.op ⋙ (locallyConstantPresheaf (F.obj (toProfinite.op.obj
      ⟨of <| PUnit.{u + 1}⟩))) ≅
    finYoneda F :=
  NatIso.ofComponents fun Y ↦ {
    hom := ↾fun f ↦ f.1
    inv := ↾fun f ↦ ⟨f, @IsLocallyConstant.of_discrete _ _ _ ⟨rfl⟩ _⟩ }

/-- A finite set as a coproduct cocone in `Profinite` over itself. -/
/-
**Condensed.fintypeCatAsCofan** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：fintypeCatAsCofan (X : Profinite) : Cofan (fun (_ : X) => (Profinite.of (P
Unit.{u + 1})))
参数：X : Profinite。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
A finite set as a coproduct cocone in `Profinite` over itself.
-/
def fintypeCatAsCofan (X : Profinite) :
    Cofan (fun (_ : X) ↦ (Profinite.of (PUnit.{u + 1}))) :=
  Cofan.mk X (fun x ↦ ConcreteCategory.ofHom (ContinuousMap.const _ x))

/-- A finite set is the coproduct of its points in `Profinite`. -/
/-
**Condensed.fintypeCatAsCofanIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：fintypeCatAsCofanIsColimit (X : Profinite) [Finite X] : IsColimit (fintype
CatAsCofan X)
参数：X : Profinite。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
A finite set is the coproduct of its points in `Profinite`.
-/
def fintypeCatAsCofanIsColimit (X : Profinite) [Finite X] :
    IsColimit (fintypeCatAsCofan X) :=
  Cofan.IsColimit.mk _ (fun t ↦ ConcreteCategory.ofHom ⟨fun x ↦ t.inj x PUnit.unit,
    continuous_of_discreteTopology (α := X)⟩) (by aesop)
    (fun _ _ h ↦ by ext x; exact CategoryTheory.congr_fun (h x) _)

variable [PreservesFiniteProducts F]
/-
**Condensed.** 是 Mathlib 中的一个实例，位于命名空间 `Condensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (X : Profinite) [Finite X] :
    PreservesLimitsOfShape (Discrete X) F :=
  let X' := (Countable.toSmall.{0} X).equiv_small.choose
  let e : X ≃ X' := (Countable.toSmall X).equiv_small.choose_spec.some
  have : Finite X' := .of_equiv X e
  preservesLimitsOfShape_of_equiv (Discrete.equivalence e.symm) F

/-- Auxiliary definition for `isoFinYoneda`. -/
/-
**Condensed.isoFinYonedaComponents** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：isoFinYonedaComponents (X : Profinite.{u}) [Finite X] : F.obj ⟨X⟩ ≅ (X -> 
F.obj ⟨Profinite.of PUnit.{u + 1}⟩)
参数：X : Profinite.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
Auxiliary definition for `isoFinYoneda`.
-/
def isoFinYonedaComponents (X : Profinite.{u}) [Finite X] :
    F.obj ⟨X⟩ ≅ (X → F.obj ⟨Profinite.of PUnit.{u + 1}⟩) :=
  (isLimitFanMkObjOfIsLimit F _ _
    (Cofan.IsColimit.op (fintypeCatAsCofanIsColimit X))).conePointUniqueUpToIso
      (Types.productLimitCone.{u, u + 1} fun _ ↦ F.obj ⟨Profinite.of PUnit.{u + 1}⟩).2

@[simp]
/-
**Condensed.isoFinYonedaComponents_hom** 是 Mathlib 中的一个引理，位于命名空间 `Condensed`。
形式化陈述：isoFinYonedaComponents_hom (X : Profinite.{u}) [Finite X] : (isoFinYonedaC
omponents F X).hom = ↾fun y x => F.map ((Profinite.of PUnit.{u + 1}).const x).op
 y
参数：X : Profinite.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `instTotallySeparatedSpaceOfExtremallyDisconnectedOfT2Space`：∀ (X : Type 
u) [inst : TopologicalSpace X] [ExtremallyDisconnected X] [T2Space X], TotallySe
paratedSpace X
· 使用定理 `instExtremallyDisconnectedOfPreirreducibleSpace`：∀ {X : Type u} [inst : 
TopologicalSpace X] [h : PreirreducibleSpace X], ExtremallyDisconnected X
· 使用定理 `instPreirreducibleSpaceOfIndiscreteTopology`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [IndiscreteTopology X], PreirreducibleSpace X
-/
lemma isoFinYonedaComponents_hom (X : Profinite.{u}) [Finite X] :
    (isoFinYonedaComponents F X).hom =
    ↾fun y x ↦ F.map ((Profinite.of PUnit.{u + 1}).const x).op y :=
  rfl
/-
**Condensed.isoFinYonedaComponents_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Condense
d`。
形式化陈述：isoFinYonedaComponents_hom_apply (X : Profinite.{u}) [Finite X] (y : F.obj
 ⟨X⟩) (x : X) : (isoFinYonedaComponents F X).hom y x = F.map ((Profinite.of PUni
t.{u + 1}).const x).op y
参数：X : Profinite.{u}；y : F.obj ⟨X⟩；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `instTotallySeparatedSpaceOfExtremallyDisconnectedOfT2Space`：∀ (X : Type 
u) [inst : TopologicalSpace X] [ExtremallyDisconnected X] [T2Space X], TotallySe
paratedSpace X
· 使用定理 `instExtremallyDisconnectedOfPreirreducibleSpace`：∀ {X : Type u} [inst : 
TopologicalSpace X] [h : PreirreducibleSpace X], ExtremallyDisconnected X
· 使用定理 `instPreirreducibleSpaceOfIndiscreteTopology`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [IndiscreteTopology X], PreirreducibleSpace X
-/
lemma isoFinYonedaComponents_hom_apply (X : Profinite.{u}) [Finite X] (y : F.obj ⟨X⟩) (x : X) :
    (isoFinYonedaComponents F X).hom y x =
      F.map ((Profinite.of PUnit.{u + 1}).const x).op y :=
  rfl
/-
**Condensed.isoFinYonedaComponents_inv_comp** 是 Mathlib 中的一个引理，位于命名空间 `Condensed
`。
形式化陈述：isoFinYonedaComponents_inv_comp {X Y : Profinite.{u}} [Finite X] [Finite Y
] (f : Y -> F.obj ⟨Profinite.of PUnit⟩) (g : X ⟶ Y) : (isoFinYonedaComponents F 
X).inv (f ∘ g) = F.map g.op ((isoFinYonedaComponents F Y).inv f)
参数：f : Y -> F.obj ⟨Profinite.of PUnit⟩；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `instTotallySeparatedSpaceOfExtremallyDisconnectedOfT2Space`：∀ (X : Type 
u) [inst : TopologicalSpace X] [ExtremallyDisconnected X] [T2Space X], TotallySe
paratedSpace X
· 使用定理 `instExtremallyDisconnectedOfPreirreducibleSpace`：∀ {X : Type u} [inst : 
TopologicalSpace X] [h : PreirreducibleSpace X], ExtremallyDisconnected X
· 使用定理 `instPreirreducibleSpaceOfIndiscreteTopology`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [IndiscreteTopology X], PreirreducibleSpace X
· 使用定理 `CategoryTheory.injective_of_mono`：injective_of_mono {X Y : Type u} (f : 
X ⟶ Y) [hf : Mono f] : Function.Injective f
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Condensed.isoFinYonedaComponents_hom_apply`：isoFinYonedaComponents_hom_a
pply (X : Profinite.{u}) [Finite X] (y : F.obj ⟨X⟩) (x : X) : (isoFinYonedaCompo
nents F X).hom y x = F.map ((Pro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isoFinYonedaComponents_inv_comp {X Y : Profinite.{u}} [Finite X] [Finite Y]
    (f : Y → F.obj ⟨Profinite.of PUnit⟩) (g : X ⟶ Y) :
    (isoFinYonedaComponents F X).inv (f ∘ g) = F.map g.op ((isoFinYonedaComponents F Y).inv f) := by
  apply injective_of_mono (isoFinYonedaComponents F X).hom
  simp only [Iso.inv_hom_id_apply]
  ext x
  rw [isoFinYonedaComponents_hom_apply]
  simp only [← Functor.map_comp_apply, ← op_comp, CompHausLike.const_comp,
    ← isoFinYonedaComponents_hom_apply, Iso.inv_hom_id_apply, Function.comp_apply]

attribute [local simp] toProfinite_obj

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
The restriction of a finite-product-preserving presheaf `F` on `Profinite` to the category of
finite sets is isomorphic to `finYoneda F`.
-/
@[simps! +dsimpLhs]
/-
**Condensed.isoFinYoneda** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：isoFinYoneda : toProfinite.op ⋙ F ≅ finYoneda F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a finite-product-preserving presheaf `F` on `Profinite` to th
e category of
finite sets is isomorphic to `finYoneda F`.
-/
def isoFinYoneda : toProfinite.op ⋙ F ≅ finYoneda F :=
  NatIso.ofComponents (fun X ↦ isoFinYonedaComponents F (toProfinite.obj X.unop)) fun _ ↦ by
    simp only [comp_obj, op_obj, finYoneda_obj, Functor.comp_map, op_map]
    ext
    simp only [isoFinYonedaComponents_hom, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
      ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, toProfinite_obj,
      ← Functor.map_comp_apply]
    rfl

/--
A presheaf `F`, which takes a profinite set written as a cofiltered limit to the corresponding
colimit, is isomorphic to the presheaf `LocallyConstant - F(*)`.
-/
/-
**Condensed.isoLocallyConstantOfIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：isoLocallyConstantOfIsColimit (hF : forall S : Profinite, IsColimit <| F.m
apCocone S.asLimitCone.op) : F ≅ locallyConstantPresheaf (F.obj (toProfinite.op.
obj ⟨of <| PUnit.{u + 1}⟩))
参数：hF : forall S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
A presheaf `F`, which takes a profinite set written as a cofiltered limit to the
 corresponding
colimit, is isomorphic to the presheaf `LocallyConstant - F(*)`.
-/
def isoLocallyConstantOfIsColimit
    (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op) :
    F ≅ locallyConstantPresheaf (F.obj (toProfinite.op.obj ⟨of <| PUnit.{u + 1}⟩)) :=
  (lanPresheafNatIso hF).symm ≪≫
    lanPresheafExt (isoFinYoneda F ≪≫ (locallyConstantIsoFinYoneda F).symm) ≪≫
      lanPresheafNatIso fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**Condensed.isoLocallyConstantOfIsColimit_inv** 是 Mathlib 中的一个引理，位于命名空间 `Condens
ed`。
形式化陈述：isoLocallyConstantOfIsColimit_inv (X : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)) [Pr
eservesFiniteProducts X] (hX : forall S : Profinite.{u}, (IsColimit <| X.mapCoco
ne S.asLimitCone.op)) : (isoLocallyConstantOfIsColimit X hX).inv = (CompHausLike
.LocallyConstant.counitApp.{u, u + 1} X)
参数：X : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)；hX : forall S : Profinite.{u}, (IsColimit 
<| X.mapCocone S.asLimitCone.op)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Profinite.instHasPropTotallyDisconnectedSpaceCarrier`：∀ (X : Type u_1) [
inst : TopologicalSpace X] [TotallyDisconnectedSpace X],   CompHausLike.HasProp 
(fun Y => TotallyDisconnectedSpace ↑Y) X
· 使用定理 `Profinite.instTotallyDisconnectedSpaceCarrierToTop`：∀ {X : Profinite}, T
otallyDisconnectedSpace ↑X.toTop
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `instTotallySeparatedSpaceOfExtremallyDisconnectedOfT2Space`：∀ (X : Type 
u) [inst : TopologicalSpace X] [ExtremallyDisconnected X] [T2Space X], TotallySe
paratedSpace X
· 使用定理 `instExtremallyDisconnectedOfPreirreducibleSpace`：∀ {X : Type u} [inst : 
TopologicalSpace X] [h : PreirreducibleSpace X], ExtremallyDisconnected X
· 使用定理 `instPreirreducibleSpaceOfIndiscreteTopology`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [IndiscreteTopology X], PreirreducibleSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Profinite.instHasExplicitFiniteCoproductsTotallyDisconnectedSpaceCarrier
`：CompHausLike.HasExplicitFiniteCoproducts fun Y => TotallyDisconnectedSpace ↑Y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `instFiniteCarrierToTopTotallyDisconnectedSpaceObjFintypeCatProfiniteToPr
ofinite`：∀ (X : FintypeCat), Finite ↑(FintypeCat.toProfinite.obj X).toTop
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用引理 `CompHausLike.LocallyConstant.presheaf_ext`：presheaf_ext (X : (CompHausLi
ke.{u} P)ᵒᵖ ⥤ Type (max u w)) [PreservesFiniteProducts X] (x y : X.obj ⟨S⟩) [Has
ExplicitFiniteCoproducts.{u} P]…
· 使用引理 `CompHausLike.LocallyConstant.incl_of_counitAppApp`：incl_of_counitAppApp 
[PreservesFiniteProducts Y] [HasExplicitFiniteCoproducts.{u} P] (a : Fiber f) : 
Y.map (sigmaIncl f a).op (counitAppApp …
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
（共 52 条，此处仅展示前 30 条）
-/
lemma isoLocallyConstantOfIsColimit_inv (X : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))
    [PreservesFiniteProducts X]
    (hX : ∀ S : Profinite.{u}, (IsColimit <| X.mapCocone S.asLimitCone.op)) :
    (isoLocallyConstantOfIsColimit X hX).inv =
      (CompHausLike.LocallyConstant.counitApp.{u, u + 1} X) := by
  dsimp [isoLocallyConstantOfIsColimit]
  simp only [Category.assoc]
  rw [Iso.inv_comp_eq]
  ext S : 2
  apply colimit.hom_ext
  intro ⟨Y, _, g⟩
  suffices _ ≫ (isoFinYonedaComponents _ _).inv ≫ X.map g =
    (locallyConstantPresheaf _).map g ≫ counitAppApp (Opposite.unop S) X by
      simpa [locallyConstantIsoFinYoneda, isoFinYoneda, counitApp]
  erw [(counitApp.{u, u + 1} X).naturality]
  simp only [← Category.assoc, op_obj, functorToPresheaves_obj_obj]
  congr
  ext f
  simp only [toProfinite_obj, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
    ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, counitApp_app]
  apply presheaf_ext.{u, u + 1} (X := X) (Y := X) (f := f)
  intro x
  dsimp [toProfinite_obj]
  rw [incl_of_counitAppApp.{u, u + 1}]
  simp only [counitAppAppImage]
  have : Finite (fiber.{u, u + 1} f x) :=
    Finite.of_injective (sigmaIncl.{u, u + 1} f x).1 Subtype.val_injective
  apply injective_of_mono (isoFinYonedaComponents X (fiber.{u, u + 1} f x)).hom
  ext y
  simp only [toProfinite_obj, isoFinYonedaComponents_hom, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.coe_mk, ← Functor.map_comp_apply, ← op_comp]
  rw [show (Profinite.of PUnit.{u + 1}).const y ≫
    IsTerminal.from _ (fiber.{u, u + 1} f x) = 𝟙 _ from rfl]
  simp only [op_comp, Functor.map_comp_apply, op_id, Functor.map_id_apply]
  simpa [← dsimp% isoFinYonedaComponents_inv_comp X _ (sigmaIncl.{u, u + 1} f x),
    ← isoFinYonedaComponents_hom_apply, -isoFinYonedaComponents_hom] using! x.map_eq_image f y

end Condensed

namespace LightCondensed

section LocallyConstantAsColimit

variable {F : ℕᵒᵖ ⥤ FintypeCat.{u}} (c : Cone <| F ⋙ toLightProfinite) (X : Type u)

/-- The presheaf on `LightProfinite` of locally constant functions to `X`. -/
/-
**LightCondensed.locallyConstantPresheaf** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightConde
nsed`。
形式化陈述：locallyConstantPresheaf : LightProfiniteᵒᵖ ⥤ Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presheaf on `LightProfinite` of locally constant functions to `X`.
-/
abbrev locallyConstantPresheaf : LightProfiniteᵒᵖ ⥤ Type u :=
  CompHausLike.LocallyConstant.functorToPresheaves.{u, u}.obj X

set_option backward.defeqAttrib.useBackward true in
/--
The functor `locallyConstantPresheaf` takes sequential limits of finite sets with surjective
projection maps to colimits.
-/
/-
**LightCondensed.isColimitLocallyConstantPresheaf** 是 Mathlib 中的一个定义，位于命名空间 `Lig
htCondensed`。
形式化陈述：isColimitLocallyConstantPresheaf (hc : IsLimit c) [forall i, Epi (c.π.app 
i)] : IsColimit (locallyConstantPresheaf X).mapCocone c.op
参数：hc : IsLimit c；c.π.app i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `locallyConstantPresheaf` takes sequential limits of finite sets wit
h surjective
projection maps to colimits.
-/
noncomputable def isColimitLocallyConstantPresheaf (hc : IsLimit c) [∀ i, Epi (c.π.app i)] :
    IsColimit <| (locallyConstantPresheaf X).mapCocone c.op := by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, 0} (lightToProfinite.mapCone c)
      (isLimitOfPreserves lightToProfinite hc) f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (c.π.app i).hom.hom = fj.comap (c.π.app j).hom.hom)
    obtain ⟨k, ki, kj, _⟩ := IsCofilteredOrEmpty.cone_objs i j
    refine ⟨⟨k⟩, ki.op, kj.op, ?_⟩
    dsimp
    ext x
    obtain ⟨x, hx⟩ := ((LightProfinite.epi_iff_surjective (c.π.app k)).mp inferInstance) x
    rw [← hx]
    change fi ((c.π.app k ≫ (F ⋙ toLightProfinite).map _) x) =
      fj ((c.π.app k ≫ (F ⋙ toLightProfinite).map _) x)
    have h := LocallyConstant.congr_fun h x
    dsimp [- CompHausLike.coe_comp] -- `coe_comp` prevents rewriting with `c.w`
    rwa [dsimp% c.w, dsimp% c.w]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**LightCondensed.isColimitLocallyConstantPresheaf_desc_apply** 是 Mathlib 中的一个引理，
位于命名空间 `LightCondensed`。
形式化陈述：isColimitLocallyConstantPresheaf_desc_apply (hc : IsLimit c) [forall i, Ep
i (c.π.app i)] (s : Cocone ((F ⋙ toLightProfinite).op ⋙ locallyConstantPresheaf 
X)) (n : Natᵒᵖ) (f : LocallyConstant (toLightProfinite.obj (F.obj n)) X) : dsimp
% (isColimitLocallyConstantPresheaf c X hc).desc s (f.comap (c.π.app n).hom.hom)
 = s.ι.app ⟨n⟩ f
参数：hc : IsLimit c；c.π.app i；s : Cocone ((F ⋙ toLightProfinite).op ⋙ locallyConst
antPresheaf X)；n : Natᵒᵖ；f : LocallyConstant (toLightProfinite.obj (F.obj n)) X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma isColimitLocallyConstantPresheaf_desc_apply (hc : IsLimit c) [∀ i, Epi (c.π.app i)]
    (s : Cocone ((F ⋙ toLightProfinite).op ⋙ locallyConstantPresheaf X))
    (n : ℕᵒᵖ) (f : LocallyConstant (toLightProfinite.obj (F.obj n)) X) :
    dsimp% (isColimitLocallyConstantPresheaf c X hc).desc s (f.comap (c.π.app n).hom.hom) =
      s.ι.app ⟨n⟩ f := by
  change ((((locallyConstantPresheaf X).mapCocone c.op).ι.app ⟨n⟩) ≫
    (isColimitLocallyConstantPresheaf c X hc).desc s) _ = _
  rw [(isColimitLocallyConstantPresheaf c X hc).fac]

/-- `isColimitLocallyConstantPresheaf` in the case of `S.asLimit`. -/
/-
**LightCondensed.isColimitLocallyConstantPresheafDiagram** 是 Mathlib 中的一个定义，位于命名
空间 `LightCondensed`。
形式化陈述：isColimitLocallyConstantPresheafDiagram (S : LightProfinite) : IsColimit (
locallyConstantPresheaf X).mapCocone (coconeRightOpOfCone S.asLimitCone)
参数：S : LightProfinite。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LightProfinite.instEpiAppOppositeNatπAsLimitCone`：∀ (S : LightProfinite)
 (i : ℕᵒᵖ), CategoryTheory.Epi (S.asLimitCone.π.app i)

--- 原说明 ---
`isColimitLocallyConstantPresheaf` in the case of `S.asLimit`.
-/
noncomputable def isColimitLocallyConstantPresheafDiagram (S : LightProfinite) :
    IsColimit <| (locallyConstantPresheaf X).mapCocone (coconeRightOpOfCone S.asLimitCone) :=
  (Functor.Final.isColimitWhiskerEquiv (opOpEquivalence ℕ).inverse _).symm
    (isColimitLocallyConstantPresheaf _ _ S.asLimit)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**LightCondensed.isColimitLocallyConstantPresheafDiagram_desc_apply** 是 Mathlib 
中的一个引理，位于命名空间 `LightCondensed`。
形式化陈述：isColimitLocallyConstantPresheafDiagram_desc_apply (S : LightProfinite) (s
 : Cocone (S.diagram.rightOp ⋙ locallyConstantPresheaf X)) (n : Nat) (f : Locall
yConstant (S.diagram.obj ⟨n⟩) X) : dsimp% (isColimitLocallyConstantPresheafDiagr
am X S).desc s (f.comap (S.asLimitCone.π.app ⟨n⟩).hom.hom) = s.ι.app n f
参数：S : LightProfinite；s : Cocone (S.diagram.rightOp ⋙ locallyConstantPresheaf X)
；n : Nat；f : LocallyConstant (S.diagram.obj ⟨n⟩) X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma isColimitLocallyConstantPresheafDiagram_desc_apply (S : LightProfinite)
    (s : Cocone (S.diagram.rightOp ⋙ locallyConstantPresheaf X))
    (n : ℕ) (f : LocallyConstant (S.diagram.obj ⟨n⟩) X) :
    dsimp% (isColimitLocallyConstantPresheafDiagram X S).desc s
      (f.comap (S.asLimitCone.π.app ⟨n⟩).hom.hom) = s.ι.app n f := by
  change ((((locallyConstantPresheaf X).mapCocone (coconeRightOpOfCone S.asLimitCone)).ι.app n) ≫
    (isColimitLocallyConstantPresheafDiagram X S).desc s) _ = _
  rw [(isColimitLocallyConstantPresheafDiagram X S).fac]

end LocallyConstantAsColimit

/-
**LightCondensed.** 是 Mathlib 中的一个实例，位于命名空间 `LightCondensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : LightProfinite.{u}ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow toLightProfinite.op S) (Type u) :=
  hasColimitsOfShape_of_equivalence (asEquivalence (CostructuredArrow.pre Skeleton.incl.op _ S))

/--
Given a presheaf `F` on `LightProfinite`, `lanPresheaf F` is the left Kan extension of its
restriction to finite sets along the inclusion functor of finite sets into `Profinite`.
-/
/-
**LightCondensed.lanPresheaf** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightCondensed`。
形式化陈述：lanPresheaf (F : LightProfinite.{u}ᵒᵖ ⥤ Type u) : LightProfinite.{u}ᵒᵖ ⥤ T
ype u
参数：F : LightProfinite.{u}ᵒᵖ ⥤ Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a presheaf `F` on `LightProfinite`, `lanPresheaf F` is the left Kan extens
ion of its
restriction to finite sets along the inclusion functor of finite sets into `Prof
inite`.
-/
abbrev lanPresheaf (F : LightProfinite.{u}ᵒᵖ ⥤ Type u) : LightProfinite.{u}ᵒᵖ ⥤ Type u :=
  pointwiseLeftKanExtension toLightProfinite.op (toLightProfinite.op ⋙ F)

/--
To presheaves on `LightProfinite` whose restrictions to finite sets are isomorphic have isomorphic
left Kan extensions.
-/
/-
**LightCondensed.lanPresheafExt** 是 Mathlib 中的一个定义，位于命名空间 `LightCondensed`。
形式化陈述：lanPresheafExt {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u} (i : toLightProfinite
.op ⋙ F ≅ toLightProfinite.op ⋙ G) : lanPresheaf F ≅ lanPresheaf G
参数：i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To presheaves on `LightProfinite` whose restrictions to finite sets are isomorph
ic have isomorphic
left Kan extensions.
-/
def lanPresheafExt {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u}
    (i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ G) : lanPresheaf F ≅ lanPresheaf G :=
  leftKanExtensionUniqueOfIso _ (pointwiseLeftKanExtensionUnit _ _) i _
    (pointwiseLeftKanExtensionUnit _ _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LightCondensed.lanPresheafExt_hom** 是 Mathlib 中的一个引理，位于命名空间 `LightCondensed`。
形式化陈述：lanPresheafExt_hom {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u} (S : LightProfini
te.{u}ᵒᵖ) (i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ G) : (lanPresheaf
Ext i).hom.app S = colimMap (whiskerLeft (CostructuredArrow.proj toLightProfinit
e.op S) i.hom)
参数：S : LightProfinite.{u}ᵒᵖ；i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ 
G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `LightCondensed.instHasColimitsOfShapeCostructuredArrowOppositeFintypeCat
LightProfiniteOpToLightProfiniteType`：∀ (S : LightProfiniteᵒᵖ),   CategoryTheory
.Limits.HasColimitsOfShape (CategoryTheory.CostructuredArrow FintypeCat.toLightP
rofinite.op S) (Ty…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.leftKanExtensionUniqueOfIso_hom`：∀ {C : Type u_1}
 {H : Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [
inst_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.pointwiseLeftKanExtension_desc_app`：pointwiseLeft
KanExtension_desc_app (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D) : ((pointwiseLeftKanEx
tension L F).descOfIsLeftKanExtension (pointwis…
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Functor.costructuredArrowMapCocone_ι_app`：∀ {C : Type u_1
} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   
[inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.pointwiseLeftKanExtensionUnit_app`：∀ {C : Type u_
1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.pointwiseLeftKanExtension_map`：∀ {C : Type u_1} {
D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [in
st_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
-/
lemma lanPresheafExt_hom {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u} (S : LightProfinite.{u}ᵒᵖ)
    (i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ G) : (lanPresheafExt i).hom.app S =
      colimMap (whiskerLeft (CostructuredArrow.proj toLightProfinite.op S) i.hom) := by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_hom, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LightCondensed.lanPresheafExt_inv** 是 Mathlib 中的一个引理，位于命名空间 `LightCondensed`。
形式化陈述：lanPresheafExt_inv {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u} (S : LightProfini
te.{u}ᵒᵖ) (i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ G) : (lanPresheaf
Ext i).inv.app S = colimMap (whiskerLeft (CostructuredArrow.proj toLightProfinit
e.op S) i.inv)
参数：S : LightProfinite.{u}ᵒᵖ；i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ 
G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `LightCondensed.instHasColimitsOfShapeCostructuredArrowOppositeFintypeCat
LightProfiniteOpToLightProfiniteType`：∀ (S : LightProfiniteᵒᵖ),   CategoryTheory
.Limits.HasColimitsOfShape (CategoryTheory.CostructuredArrow FintypeCat.toLightP
rofinite.op S) (Ty…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.leftKanExtensionUniqueOfIso_inv`：∀ {C : Type u_1}
 {H : Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [
inst_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.pointwiseLeftKanExtension_desc_app`：pointwiseLeft
KanExtension_desc_app (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D) : ((pointwiseLeftKanEx
tension L F).descOfIsLeftKanExtension (pointwis…
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Functor.costructuredArrowMapCocone_ι_app`：∀ {C : Type u_1
} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   
[inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.pointwiseLeftKanExtensionUnit_app`：∀ {C : Type u_
1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.pointwiseLeftKanExtension_map`：∀ {C : Type u_1} {
D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [in
st_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
-/
lemma lanPresheafExt_inv {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u} (S : LightProfinite.{u}ᵒᵖ)
    (i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ G) : (lanPresheafExt i).inv.app S =
      colimMap (whiskerLeft (CostructuredArrow.proj toLightProfinite.op S) i.inv) := by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_inv, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

variable {S : LightProfinite.{u}} {F : LightProfinite.{u}ᵒᵖ ⥤ Type u}
/-
**LightCondensed.** 是 Mathlib 中的一个实例，位于命名空间 `LightCondensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Final <| LightProfinite.Extend.functorOp S.asLimitCone :=
  LightProfinite.Extend.functorOp_final S.asLimitCone S.asLimit

set_option backward.isDefEq.respectTransparency.types false in
/--
A presheaf, which takes a light profinite set written as a sequential limit to the corresponding
colimit, agrees with the left Kan extension of its restriction.
-/
/-
**LightCondensed.lanPresheafIso** 是 Mathlib 中的一个定义，位于命名空间 `LightCondensed`。
形式化陈述：lanPresheafIso (hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLim
itCone)) : (lanPresheaf F).obj ⟨S⟩ ≅ F.obj ⟨S⟩
参数：hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LightCondensed.instFinalNatCostructuredArrowOppositeFintypeCatLightProfi
niteOpToLightProfiniteOpPtAsLimitConeFunctorOp`：∀ {S : LightProfinite}, (LightPr
ofinite.Extend.functorOp S.asLimitCone).Final

--- 原说明 ---
A presheaf, which takes a light profinite set written as a sequential limit to t
he corresponding
colimit, agrees with the left Kan extension of its restriction.
-/
def lanPresheafIso (hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    (lanPresheaf F).obj ⟨S⟩ ≅ F.obj ⟨S⟩ :=
  (Functor.Final.colimitIso (LightProfinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hF

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LightCondensed.lanPresheafIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `LightCondensed`。
形式化陈述：lanPresheafIso_hom (hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.a
sLimitCone)) : (lanPresheafIso hF).hom = colimit.desc _ (LightProfinite.Extend.c
ocone _ _)
参数：hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.comp_hasColimit`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `LightCondensed.instFinalNatCostructuredArrowOppositeFintypeCatLightProfi
niteOpToLightProfiniteOpPtAsLimitConeFunctorOp`：∀ {S : LightProfinite}, (LightPr
ofinite.Extend.functorOp S.asLimitCone).Final
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.pre_desc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} K]   {C : Type u} [inst…
-/
lemma lanPresheafIso_hom (hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    (lanPresheafIso hF).hom = colimit.desc _ (LightProfinite.Extend.cocone _ _) := by
  simp [lanPresheafIso, Final.colimitIso]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `lanPresheafIso` is natural in `S`. -/
/-
**LightCondensed.lanPresheafNatIso** 是 Mathlib 中的一个定义，位于命名空间 `LightCondensed`。
形式化陈述：lanPresheafNatIso (hF : forall S : LightProfinite, IsColimit <| F.mapCocon
e (coconeRightOpOfCone S.asLimitCone)) : lanPresheaf F ≅ F
参数：hF : forall S : LightProfinite, IsColimit <| F.mapCocone (coconeRightOpOfCone
 S.asLimitCone)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lanPresheafIso` is natural in `S`.
-/
def lanPresheafNatIso
    (hF : ∀ S : LightProfinite, IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    lanPresheaf F ≅ F := by
  refine NatIso.ofComponents
    (fun ⟨S⟩ ↦ (lanPresheafIso (hF S))) fun _ ↦ ?_
  simp only [lanPresheaf, pointwiseLeftKanExtension_map,
    lanPresheafIso_hom, Opposite.op_unop]
  exact colimit.hom_ext fun _ ↦ (by simp)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**LightCondensed.lanPresheafNatIso_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `LightConde
nsed`。
形式化陈述：lanPresheafNatIso_hom_app (hF : forall S : LightProfinite, IsColimit <| F.
mapCocone (coconeRightOpOfCone S.asLimitCone)) (S : LightProfiniteᵒᵖ) : (lanPres
heafNatIso hF).hom.app S = colimit.desc _ (LightProfinite.Extend.cocone _ _)
参数：hF : forall S : LightProfinite, IsColimit <| F.mapCocone (coconeRightOpOfCone
 S.asLimitCone)；S : LightProfiniteᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LightCondensed.lanPresheafIso_hom`：lanPresheafIso_hom (hF : IsColimit <|
 F.mapCocone (coconeRightOpOfCone S.asLimitCone)) : (lanPresheafIso hF).hom = co
limit.desc _ (LightProf…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lanPresheafNatIso_hom_app
    (hF : ∀ S : LightProfinite, IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone))
    (S : LightProfiniteᵒᵖ) : (lanPresheafNatIso hF).hom.app S =
      colimit.desc _ (LightProfinite.Extend.cocone _ _) := by
  simp [lanPresheafNatIso]

/--
`lanPresheaf (locallyConstantPresheaf X)` as a light condensed set.
-/
/-
**LightCondensed.lanLightCondSet** 是 Mathlib 中的一个定义，位于命名空间 `LightCondensed`。
形式化陈述：lanLightCondSet (X : Type u) : LightCondSet.{u} where obj
参数：X : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lanPresheaf (locallyConstantPresheaf X)` as a light condensed set.
-/
def lanLightCondSet (X : Type u) : LightCondSet.{u} where
  obj := lanPresheaf (locallyConstantPresheaf X)
  property := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheafNatIso
      fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _)]
    exact (CompHausLike.LocallyConstant.functor.{u, u}
      (hs := fun _ _ _ ↦ ((LightProfinite.effectiveEpi_iff_surjective _).mp)).obj X).property

variable (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)

/--
The functor which takes a finite set to the set of maps into `F(*)` for a presheaf `F` on
`LightProfinite`.
-/
@[simps]
/-
**LightCondensed.finYoneda** 是 Mathlib 中的一个定义，位于命名空间 `LightCondensed`。
形式化陈述：finYoneda : FintypeCat.{u}ᵒᵖ ⥤ Type u where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The functor which takes a finite set to the set of maps into `F(*)` for a preshe
af `F` on
`LightProfinite`.
-/
def finYoneda : FintypeCat.{u}ᵒᵖ ⥤ Type u where
  obj X := X.unop → F.obj (toLightProfinite.op.obj ⟨of PUnit.{u + 1}⟩)
  map f := ↾fun g ↦ g ∘ f.unop

/-- `locallyConstantPresheaf` restricted to finite sets is isomorphic to `finYoneda F`. -/
/-
**LightCondensed.locallyConstantIsoFinYoneda** 是 Mathlib 中的一个定义，位于命名空间 `LightCon
densed`。
形式化陈述：locallyConstantIsoFinYoneda : toLightProfinite.op ⋙ (locallyConstantPreshe
af (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u + 1}⟩))) ≅ finYoneda F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
`locallyConstantPresheaf` restricted to finite sets is isomorphic to `finYoneda 
F`.
-/
def locallyConstantIsoFinYoneda : toLightProfinite.op ⋙
    (locallyConstantPresheaf (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u + 1}⟩))) ≅ finYoneda F :=
  NatIso.ofComponents fun Y ↦ {
    hom := ↾fun f ↦ f.1
    inv := ↾fun f ↦ ⟨f, @IsLocallyConstant.of_discrete _ _ _ ⟨rfl⟩ _⟩ }

/-- A finite set as a coproduct cocone in `LightProfinite` over itself. -/
/-
**LightCondensed.fintypeCatAsCofan** 是 Mathlib 中的一个定义，位于命名空间 `LightCondensed`。
形式化陈述：fintypeCatAsCofan (X : LightProfinite) : Cofan (fun (_ : X) => (LightProfi
nite.of (PUnit.{u + 1})))
参数：X : LightProfinite。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
A finite set as a coproduct cocone in `LightProfinite` over itself.
-/
def fintypeCatAsCofan (X : LightProfinite) :
    Cofan (fun (_ : X) ↦ (LightProfinite.of (PUnit.{u + 1}))) :=
  Cofan.mk X (fun x ↦ ConcreteCategory.ofHom (ContinuousMap.const _ x))

/-- A finite set is the coproduct of its points in `LightProfinite`. -/
/-
**LightCondensed.fintypeCatAsCofanIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `LightCond
ensed`。
形式化陈述：fintypeCatAsCofanIsColimit (X : LightProfinite) [Finite X] : IsColimit (fi
ntypeCatAsCofan X)
参数：X : LightProfinite。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
A finite set is the coproduct of its points in `LightProfinite`.
-/
def fintypeCatAsCofanIsColimit (X : LightProfinite) [Finite X] :
    IsColimit (fintypeCatAsCofan X) :=
  Cofan.IsColimit.mk _ (fun t ↦ ConcreteCategory.ofHom ⟨fun x ↦ t.inj x PUnit.unit,
    continuous_of_discreteTopology (α := X)⟩) (by aesop)
    (fun _ _ h ↦ by ext x; exact CategoryTheory.congr_fun (h x) _)

variable [PreservesFiniteProducts F]
/-
**LightCondensed.** 是 Mathlib 中的一个实例，位于命名空间 `LightCondensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (X : FintypeCat.{u}) : PreservesLimitsOfShape (Discrete X) F :=
  let X' := (Countable.toSmall.{0} X).equiv_small.choose
  let e : X ≃ X' := (Countable.toSmall X).equiv_small.choose_spec.some
  have : Finite X' := Finite.of_equiv X e
  preservesLimitsOfShape_of_equiv (Discrete.equivalence e.symm) F

/-- Auxiliary definition for `isoFinYoneda`. -/
/-
**LightCondensed.isoFinYonedaComponents** 是 Mathlib 中的一个定义，位于命名空间 `LightCondense
d`。
形式化陈述：isoFinYonedaComponents (X : LightProfinite.{u}) [Finite X] : F.obj ⟨X⟩ ≅ (
X -> F.obj ⟨LightProfinite.of PUnit.{u + 1}⟩)
参数：X : LightProfinite.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
Auxiliary definition for `isoFinYoneda`.
-/
def isoFinYonedaComponents (X : LightProfinite.{u}) [Finite X] :
    F.obj ⟨X⟩ ≅ (X → F.obj ⟨LightProfinite.of PUnit.{u + 1}⟩) :=
  (isLimitFanMkObjOfIsLimit F _ _
    (Cofan.IsColimit.op (fintypeCatAsCofanIsColimit X))).conePointUniqueUpToIso
      (Types.productLimitCone.{u, u} fun _ ↦ F.obj ⟨LightProfinite.of PUnit.{u + 1}⟩).2

@[simp]
/-
**LightCondensed.isoFinYonedaComponents_hom** 是 Mathlib 中的一个引理，位于命名空间 `LightCond
ensed`。
形式化陈述：isoFinYonedaComponents_hom (X : LightProfinite.{u}) [Finite X] : (isoFinYo
nedaComponents F X).hom = ↾fun y x => F.map ((LightProfinite.of PUnit.{u + 1}).c
onst x).op y
参数：X : LightProfinite.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `instTotallySeparatedSpaceOfExtremallyDisconnectedOfT2Space`：∀ (X : Type 
u) [inst : TopologicalSpace X] [ExtremallyDisconnected X] [T2Space X], TotallySe
paratedSpace X
· 使用定理 `instExtremallyDisconnectedOfPreirreducibleSpace`：∀ {X : Type u} [inst : 
TopologicalSpace X] [h : PreirreducibleSpace X], ExtremallyDisconnected X
· 使用定理 `instPreirreducibleSpaceOfIndiscreteTopology`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [IndiscreteTopology X], PreirreducibleSpace X
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
-/
lemma isoFinYonedaComponents_hom (X : LightProfinite.{u}) [Finite X] :
    (isoFinYonedaComponents F X).hom =
    ↾fun y x ↦ F.map ((LightProfinite.of PUnit.{u + 1}).const x).op y :=
  rfl
/-
**LightCondensed.isoFinYonedaComponents_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Lig
htCondensed`。
形式化陈述：isoFinYonedaComponents_hom_apply (X : LightProfinite.{u}) [Finite X] (y : 
F.obj ⟨X⟩) (x : X) : (isoFinYonedaComponents F X).hom y x = F.map ((LightProfini
te.of PUnit.{u + 1}).const x).op y
参数：X : LightProfinite.{u}；y : F.obj ⟨X⟩；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `instTotallySeparatedSpaceOfExtremallyDisconnectedOfT2Space`：∀ (X : Type 
u) [inst : TopologicalSpace X] [ExtremallyDisconnected X] [T2Space X], TotallySe
paratedSpace X
· 使用定理 `instExtremallyDisconnectedOfPreirreducibleSpace`：∀ {X : Type u} [inst : 
TopologicalSpace X] [h : PreirreducibleSpace X], ExtremallyDisconnected X
· 使用定理 `instPreirreducibleSpaceOfIndiscreteTopology`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [IndiscreteTopology X], PreirreducibleSpace X
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
-/
lemma isoFinYonedaComponents_hom_apply (X : LightProfinite.{u}) [Finite X] (y : F.obj ⟨X⟩)
    (x : X) : (isoFinYonedaComponents F X).hom y x =
      F.map ((LightProfinite.of PUnit.{u + 1}).const x).op y := rfl
/-
**LightCondensed.isoFinYonedaComponents_inv_comp** 是 Mathlib 中的一个引理，位于命名空间 `Ligh
tCondensed`。
形式化陈述：isoFinYonedaComponents_inv_comp {X Y : LightProfinite.{u}} [Finite X] [Fin
ite Y] (f : Y -> F.obj ⟨LightProfinite.of PUnit⟩) (g : X ⟶ Y) : (isoFinYonedaCom
ponents F X).inv (f ∘ g) = F.map g.op ((isoFinYonedaComponents F Y).inv f)
参数：f : Y -> F.obj ⟨LightProfinite.of PUnit⟩；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `instTotallySeparatedSpaceOfExtremallyDisconnectedOfT2Space`：∀ (X : Type 
u) [inst : TopologicalSpace X] [ExtremallyDisconnected X] [T2Space X], TotallySe
paratedSpace X
· 使用定理 `instExtremallyDisconnectedOfPreirreducibleSpace`：∀ {X : Type u} [inst : 
TopologicalSpace X] [h : PreirreducibleSpace X], ExtremallyDisconnected X
· 使用定理 `instPreirreducibleSpaceOfIndiscreteTopology`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [IndiscreteTopology X], PreirreducibleSpace X
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `CategoryTheory.injective_of_mono`：injective_of_mono {X Y : Type u} (f : 
X ⟶ Y) [hf : Mono f] : Function.Injective f
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `LightCondensed.isoFinYonedaComponents_hom_apply`：isoFinYonedaComponents_
hom_apply (X : LightProfinite.{u}) [Finite X] (y : F.obj ⟨X⟩) (x : X) : (isoFinY
onedaComponents F X).hom y x = F.map …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isoFinYonedaComponents_inv_comp {X Y : LightProfinite.{u}} [Finite X] [Finite Y]
    (f : Y → F.obj ⟨LightProfinite.of PUnit⟩) (g : X ⟶ Y) :
    (isoFinYonedaComponents F X).inv (f ∘ g) = F.map g.op ((isoFinYonedaComponents F Y).inv f) := by
  apply injective_of_mono (isoFinYonedaComponents F X).hom
  simp only [Iso.inv_hom_id_apply]
  ext x
  rw [isoFinYonedaComponents_hom_apply]
  simp only [← Functor.map_comp_apply, ← op_comp, CompHausLike.const_comp,
    ← isoFinYonedaComponents_hom_apply, Iso.inv_hom_id_apply, Function.comp_apply]

attribute [local simp] toLightProfinite_obj

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
The restriction of a finite-product-preserving presheaf `F` on `Profinite` to the category of
finite sets is isomorphic to `finYoneda F`.
-/
@[simps! +dsimpLhs]
/-
**LightCondensed.isoFinYoneda** 是 Mathlib 中的一个定义，位于命名空间 `LightCondensed`。
形式化陈述：isoFinYoneda : toLightProfinite.op ⋙ F ≅ finYoneda F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a finite-product-preserving presheaf `F` on `Profinite` to th
e category of
finite sets is isomorphic to `finYoneda F`.
-/
def isoFinYoneda : toLightProfinite.op ⋙ F ≅ finYoneda F :=
  NatIso.ofComponents (fun X ↦ isoFinYonedaComponents F (toLightProfinite.obj X.unop)) fun _ ↦ by
    simp only [comp_obj, op_obj, finYoneda_obj, Functor.comp_map, op_map]
    ext
    simp only [isoFinYonedaComponents_hom, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
      ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, toLightProfinite_obj,
      ← Functor.map_comp_apply]
    rfl

/--
A presheaf `F`, which takes a light profinite set written as a sequential limit to the corresponding
colimit, is isomorphic to the presheaf `LocallyConstant - F(*)`.
-/
/-
**LightCondensed.isoLocallyConstantOfIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `LightC
ondensed`。
形式化陈述：isoLocallyConstantOfIsColimit (hF : forall S : LightProfinite, IsColimit <
| F.mapCocone (coconeRightOpOfCone S.asLimitCone)) : F ≅ (locallyConstantPreshea
f (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u + 1}⟩)))
参数：hF : forall S : LightProfinite, IsColimit <| F.mapCocone (coconeRightOpOfCone
 S.asLimitCone)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
A presheaf `F`, which takes a light profinite set written as a sequential limit 
to the corresponding
colimit, is isomorphic to the presheaf `LocallyConstant - F(*)`.
-/
def isoLocallyConstantOfIsColimit (hF : ∀ S : LightProfinite, IsColimit <|
    F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
      F ≅ (locallyConstantPresheaf
        (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u + 1}⟩))) :=
  (lanPresheafNatIso hF).symm ≪≫
    lanPresheafExt (isoFinYoneda F ≪≫ (locallyConstantIsoFinYoneda F).symm) ≪≫
      lanPresheafNatIso fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**LightCondensed.isoLocallyConstantOfIsColimit_inv** 是 Mathlib 中的一个引理，位于命名空间 `Li
ghtCondensed`。
形式化陈述：isoLocallyConstantOfIsColimit_inv (X : LightProfinite.{u}ᵒᵖ ⥤ Type u) [Pre
servesFiniteProducts X] (hX : forall S : LightProfinite.{u}, (IsColimit <| X.map
Cocone (coconeRightOpOfCone S.asLimitCone))) : (isoLocallyConstantOfIsColimit X 
hX).inv = (CompHausLike.LocallyConstant.counitApp.{u, u} X)
参数：X : LightProfinite.{u}ᵒᵖ ⥤ Type u；hX : forall S : LightProfinite.{u}, (IsColi
mit <| X.mapCocone (coconeRightOpOfCone S.asLimitCone))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LightCondSet.LocallyConstant.instHasPropAndTotallyDisconnectedSpaceCarri
erSecondCountableTopologySubtypeToTop`：∀ (S : LightProfinite) (p : ↑S.toTop → Pr
op),   CompHausLike.HasProp (fun X => TotallyDisconnectedSpace ↑X ∧ SecondCounta
bleTopology ↑X) (Su…
· 使用定理 `LightProfinite.instHasPropAndTotallyDisconnectedSpaceCarrierSecondCounta
bleTopology`：∀ (X : Type u_1) [inst : TopologicalSpace X] [TotallyDisconnectedSp
ace X] [SecondCountableTopology X],   CompHausLike.HasProp (fun Y => Tota…
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `instTotallySeparatedSpaceOfExtremallyDisconnectedOfT2Space`：∀ (X : Type 
u) [inst : TopologicalSpace X] [ExtremallyDisconnected X] [T2Space X], TotallySe
paratedSpace X
· 使用定理 `instExtremallyDisconnectedOfPreirreducibleSpace`：∀ {X : Type u} [inst : 
TopologicalSpace X] [h : PreirreducibleSpace X], ExtremallyDisconnected X
· 使用定理 `instPreirreducibleSpaceOfIndiscreteTopology`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [IndiscreteTopology X], PreirreducibleSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `LightProfinite.instHasExplicitFiniteCoproductsAndTotallyDisconnectedSpac
eCarrierSecondCountableTopology`：CompHausLike.HasExplicitFiniteCoproducts fun Y 
=> TotallyDisconnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `instFiniteCarrierToTopAndTotallyDisconnectedSpaceSecondCountableTopology
ObjFintypeCatLightProfiniteToLightProfinite`：∀ (X : FintypeCat), Finite ↑(Fintyp
eCat.toLightProfinite.obj X).toTop
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用引理 `CompHausLike.LocallyConstant.presheaf_ext`：presheaf_ext (X : (CompHausLi
ke.{u} P)ᵒᵖ ⥤ Type (max u w)) [PreservesFiniteProducts X] (x y : X.obj ⟨S⟩) [Has
ExplicitFiniteCoproducts.{u} P]…
· 使用引理 `CompHausLike.LocallyConstant.incl_of_counitAppApp`：incl_of_counitAppApp 
[PreservesFiniteProducts Y] [HasExplicitFiniteCoproducts.{u} P] (a : Fiber f) : 
Y.map (sigmaIncl f a).op (counitAppApp …
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
（共 58 条，此处仅展示前 30 条）
-/
lemma isoLocallyConstantOfIsColimit_inv (X : LightProfinite.{u}ᵒᵖ ⥤ Type u)
    [PreservesFiniteProducts X] (hX : ∀ S : LightProfinite.{u}, (IsColimit <|
      X.mapCocone (coconeRightOpOfCone S.asLimitCone))) :
    (isoLocallyConstantOfIsColimit X hX).inv =
      (CompHausLike.LocallyConstant.counitApp.{u, u} X) := by
  dsimp [isoLocallyConstantOfIsColimit]
  simp only [Category.assoc]
  rw [Iso.inv_comp_eq]
  ext S : 2
  apply colimit.hom_ext
  intro ⟨Y, _, g⟩
  suffices _ ≫ (isoFinYonedaComponents _ _).inv ≫ X.map g =
    (locallyConstantPresheaf _).map g ≫ counitAppApp (Opposite.unop S) X by
      simpa [locallyConstantIsoFinYoneda, isoFinYoneda, counitApp]
  erw [(counitApp.{u, u} X).naturality]
  simp only [← Category.assoc, op_obj, functorToPresheaves_obj_obj]
  congr
  ext f
  apply presheaf_ext.{u, u} (X := X) (Y := X) (f := f)
  intro x
  dsimp [toLightProfinite_obj]
  rw [incl_of_counitAppApp]
  simp only [counitAppAppImage]
  have : Finite (fiber.{u, u} f x) :=
    Finite.of_injective (sigmaIncl.{u, u} f x).1 Subtype.val_injective
  apply injective_of_mono (isoFinYonedaComponents X (fiber.{u, u} f x)).hom
  ext y
  simp only [toLightProfinite_obj, isoFinYonedaComponents_hom, TypeCat.hom_ofHom,
    TypeCat.Fun.coe_mk, ← map_comp_apply, ← op_comp]
  rw [show (LightProfinite.of PUnit.{u + 1}).const y ≫
    IsTerminal.from _ (fiber.{u, u} f x) = 𝟙 _ from rfl]
  simpa [← dsimp% isoFinYonedaComponents_inv_comp X _ (sigmaIncl.{u, u} f x),
    ← isoFinYonedaComponents_hom_apply, -isoFinYonedaComponents_hom] using! x.map_eq_image f y

end LightCondensed

