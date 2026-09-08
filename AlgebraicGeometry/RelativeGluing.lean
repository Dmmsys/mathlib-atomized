/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Relative gluing

In this file we show a relative gluing lemma (see https://stacks.math.columbia.edu/tag/01LH):
If `{Uᵢ}` is a locally directed open cover of `S` and we have a compatible family of `Xᵢ` over `Uᵢ`,
the `Xᵢ` glue to a morphism `f : X ⟶ S` such that `Xᵢ ≅ f⁻¹ Uᵢ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.isLocallyDirected_of_equifibered_of_injective** 是 Mat
hlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {J : Type u_1} [inst : CategoryTheory.Category.{u_2, u_1} J] {F G : Cate
goryTheory.Functor J AlgebraicGeometry.Scheme}   (s : F ⟶ G) [Quiver.IsThin J], 
  CategoryTheory.NatTrans.Equifibered s →     (∀ {i j : J} (hij : i ⟶ j), Functi
on.Injective ⇑(F.map hij)) →       ∀ [(G.comp AlgebraicGeometry.Scheme.forget).I
sLocallyDirected],         (F.comp AlgebraicGeometry.Scheme.forget).IsLocallyDir
ected
参数：s : F ⟶ G；∀ {i j : J} (hij : i ⟶ j), Function.Injective ⇑(F.map hij)；G.comp A
lgebraicGeometry.Scheme.forget；F.comp AlgebraicGeometry.Scheme.forget。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.exists_map_eq_of_isLocallyDirected`：∀ {J : Type u
_1} {inst : CategoryTheory.Category.{v_1, u_1} J} (F : CategoryTheory.Functor J 
(Type u_2))   [self : F.IsLocallyDirected] {i j…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`：exists_preim
age_pullback (x : X) (y : Y) (h : f x = g y) : exists z : ↑(pullback f g), pullb
ack.fst f g z = x ∧ pullback.snd f g z = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.IsPullback.isoPullback_inv_fst`：isoPullback_inv_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.inv ≫ fst = pullback.f
st _ _
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.isoPullback_inv_fst_assoc`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ 
Y} {f : X ⟶ Z}   {g : Y ⟶ Z} (h : Categor…
-/
lemma Scheme.isLocallyDirected_of_equifibered_of_injective {J : Type*} [Category J]
    {F G : J ⥤ Scheme.{u}} (s : F ⟶ G) [Quiver.IsThin J] (hs : s.Equifibered)
    (H : ∀ {i j} (hij : i ⟶ j), Function.Injective (F.map hij))
    [(G ⋙ Scheme.forget).IsLocallyDirected] :
    (F ⋙ Scheme.forget).IsLocallyDirected where
  cond {i j k} fi fj xi xj heq := by
    simp only [Functor.comp_obj, Scheme.forget_obj, Functor.comp_map, Scheme.forget_map] at heq
    obtain ⟨l, fli, flj, x, hi, hj⟩ := (G ⋙ Scheme.forget).exists_map_eq_of_isLocallyDirected fi fj
        (s.app i xi) (s.app j xj) <| by
      simp only [Functor.comp_obj, forget_obj, Functor.comp_map, forget_map,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
      dsimp at heq
      rw [← Scheme.Hom.comp_apply, ← s.naturality, Scheme.Hom.comp_apply, heq,
        ← Scheme.Hom.comp_apply, s.naturality]
      simp
    use l, fli, flj
    let e := (hs fli).isoPullback
    obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback xi x hi.symm
    refine ⟨e.inv z, ?_, ?_⟩
    · simp [← h1, ← Scheme.Hom.comp_apply, e]
    · apply H fj
      simp only [Functor.comp_obj, forget_obj, Functor.comp_map, forget_map,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, ← Scheme.Hom.comp_apply,
        Category.assoc, ← Functor.map_comp, show flj ≫ fj = fli ≫ fi by subsingleton]
      dsimp at heq
      simp [e, Functor.map_comp, ← heq, h1]

namespace Scheme.Cover

variable {S : Scheme.{u}} (𝒰 : S.OpenCover) [Category 𝒰.I₀] [𝒰.LocallyDirected]

/--
A relative gluing datum over a locally directed cover `𝒰` of `S` is a scheme `Xᵢ` for every
`i : 𝒰.I₀` and natural maps `Xᵢ ⟶ Uᵢ` such that for every `i ⟶ j`, the diagram
```
Xᵢ --> Uᵢ
|      |
v      v
Xⱼ --> Uⱼ
```
is a pullback square. We bundle this in the form of a functor and an equifibered natural
transformation.
The `Xᵢ` then glue to a scheme over `S`
(see `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.glued`).
-/
@[stacks 01LH]
/-
**AlgebraicGeometry.Scheme.Cover.RelativeGluingData** 是 Mathlib 中的一个归纳类型，位于命名空间 
`AlgebraicGeometry.Scheme.Cover`。
形式化陈述：{S : AlgebraicGeometry.Scheme} →   (𝒰 : S.OpenCover) →     [inst : Categor
yTheory.Category.{u_2, u_1} 𝒰.I₀] →       [AlgebraicGeometry.Scheme.Cover.Locall
yDirected 𝒰] → Type (max (max (u + 1) u_1) u_2)
参数：𝒰 : S.OpenCover；max (max (u + 1) u_1) u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relative gluing datum over a locally directed cover `𝒰` of `S` is a scheme `Xᵢ
` for every
`i : 𝒰.I₀` and natural maps `Xᵢ ⟶ Uᵢ` such that for every `i ⟶ j`, the diagram
```
Xᵢ --> Uᵢ
|      |
v      v
Xⱼ --> Uⱼ
```
is a pullback square. We bundle this in the form of a functor and an equifibered
 natural
transformation.
The `Xᵢ` then glue to a scheme over `S`
(see `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.glued`).
-/
structure RelativeGluingData where
  /-- The schemes `Xᵢ`. -/
  functor : 𝒰.I₀ ⥤ Scheme.{u}
  /-- The natural maps `Xᵢ ⟶ Uᵢ`. -/
  natTrans : functor ⟶ 𝒰.functorOfLocallyDirected
  equifibered : natTrans.Equifibered

variable {𝒰} (d : RelativeGluingData 𝒰)

namespace RelativeGluingData

/-
**AlgebraicGeometry.Scheme.Cover.RelativeGluingData.** 是 Mathlib 中的一个实例，位于命名空间 `
AlgebraicGeometry.Scheme.Cover.RelativeGluingData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {i j : 𝒰.I₀} (hij : i ⟶ j) : IsOpenImmersion (d.functor.map hij) := by
  apply MorphismProperty.of_isPullback (d.equifibered hij).flip
  infer_instance
/-
**AlgebraicGeometry.Scheme.Cover.RelativeGluingData.** 是 Mathlib 中的一个实例，位于命名空间 `
AlgebraicGeometry.Scheme.Cover.RelativeGluingData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Quiver.IsThin 𝒰.I₀] : (d.functor ⋙ Scheme.forget).IsLocallyDirected := by
  apply isLocallyDirected_of_equifibered_of_injective d.natTrans d.equifibered
  intro i j hij
  exact (d.functor.map hij).injective

variable [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]

/--
The glued scheme of a relative gluing datum is the colimit over the `Xᵢ`. For the
structure map, see `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.toBase` and the isomorphisms
with the preimages `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.isPullback_natTrans_ι_toBase`.
-/
@[stacks 01LH]
/-
**AlgebraicGeometry.Scheme.Cover.RelativeGluingData.glued** 是 Mathlib 中的一个缩写定义，位
于命名空间 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData`。
形式化陈述：glued : Scheme.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The glued scheme of a relative gluing datum is the colimit over the `Xᵢ`. For th
e
structure map, see `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.toBase` an
d the isomorphisms
with the preimages `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.isPullback
_natTrans_ι_toBase`.
-/
noncomputable abbrev glued : Scheme.{u} :=
  colimit d.functor

/-- The cover of the glued `Xᵢ` given by the `Xᵢ`. -/
@[simps!]
/-
**AlgebraicGeometry.Scheme.Cover.RelativeGluingData.cover** 是 Mathlib 中的一个定义，位于命
名空间 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData`。
形式化陈述：cover : OpenCover d.glued
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsOpenImmersionMap
I₀Functor`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [inst : CategoryTh
eory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Scheme.Cov…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI
₀CompFunctorForgetOfIsThin`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [
inst : CategoryTheory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Sc
heme.Cov…

--- 原说明 ---
The cover of the glued `Xᵢ` given by the `Xᵢ`.
-/
noncomputable def cover : OpenCover d.glued :=
  Scheme.IsLocallyDirected.openCover _
/-
**AlgebraicGeometry.Scheme.Cover.RelativeGluingData.** 是 Mathlib 中的一个实例，位于命名空间 `
AlgebraicGeometry.Scheme.Cover.RelativeGluingData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category d.cover.I₀ :=
  inferInstanceAs <| Category 𝒰.I₀

/-- The structure map from the colimit of the `Xᵢ` to `S`. -/
/-
**AlgebraicGeometry.Scheme.Cover.RelativeGluingData.toBase** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData`。
形式化陈述：toBase : d.glued ⟶ S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure map from the colimit of the `Xᵢ` to `S`.
-/
noncomputable def toBase : d.glued ⟶ S :=
  colimit.desc _
    { pt := S
      ι := d.natTrans ≫ 𝒰.functorOfLocallyDirectedHomBase }

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Cover.RelativeGluingData.** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme.Cover.RelativeGluingData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma ι_toBase (i : 𝒰.I₀) :
    colimit.ι d.functor i ≫ d.toBase = d.natTrans.app i ≫ 𝒰.f i := by
  simp [toBase]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Cover.RelativeGluingData.** 是 Mathlib 中的一个实例，位于命名空间 `
AlgebraicGeometry.Scheme.Cover.RelativeGluingData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : d.cover.LocallyDirected where
  trans {i j} hij := d.functor.map hij
  directed {i j} x := by
    let xi := pullback.fst (d.cover.f i) _ x
    let xj := pullback.snd (d.cover.f i) _ x
    obtain ⟨k, fi, fj, uk, h1, h2⟩ :=
        𝒰.exists_of_f_eq_f (d.natTrans.app i xi) (d.natTrans.app j xj) <| by
      dsimp [functorOfLocallyDirected_obj, xi, xj]
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← ι_toBase, pullback.condition_assoc]
      simp
    use k, fi, fj
    obtain ⟨xk, h1, h2⟩ := exists_preimage_of_isPullback (d.equifibered fj) xj uk <| by
      apply (𝒰.f j).injective
      dsimp only [functorOfLocallyDirected_obj, functorOfLocallyDirected_map]
      rw [← Scheme.Hom.comp_apply]
      simp [xj, h2]
    use xk
    apply (pullback.snd (d.cover.f i) _).injective
    rw [← Scheme.Hom.comp_apply]
    simp [h1, xj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Cover.RelativeGluingData.preimage_toBase_eq_range_** 
是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_toBase_eq_range_ι (i : 𝒰.I₀) :
    d.toBase ⁻¹' (Set.range <| 𝒰.f i) = Set.range (colimit.ι d.functor i) := by
  ext x
  refine ⟨fun ⟨ui, h⟩ ↦ ?_, ?_⟩
  · obtain ⟨j, xj, rfl⟩ := IsLocallyDirected.ι_jointly_surjective _ x
    obtain ⟨k, fi, fj, uk, rfl, h⟩ := 𝒰.exists_of_f_eq_f ui (d.natTrans.app j xj) <| by
      simp only [h, functorOfLocallyDirected_obj, ← Scheme.Hom.comp_apply, ι_toBase]
    obtain ⟨xk, rfl, h2⟩ := exists_preimage_of_isPullback (d.equifibered fj) xj uk <| by
      apply (𝒰.f j).injective
      simp only [functorOfLocallyDirected_obj, functorOfLocallyDirected_map]
      rw [← Scheme.Hom.comp_apply, ← ι_toBase, Scheme.Hom.comp_apply, ← h]
      simp [← Scheme.Hom.comp_apply]
    use d.functor.map fi xk
    simp [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  · rintro ⟨y, rfl⟩
    use d.natTrans.app i y
    rw [← Scheme.Hom.comp_apply, ι_toBase]
    simp
/-
**AlgebraicGeometry.Scheme.Cover.RelativeGluingData.toBase_preimage_eq_opensRang
e_** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toBase_preimage_eq_opensRange_ι (i : 𝒰.I₀) :
    d.toBase ⁻¹ᵁ (𝒰.f i).opensRange = (colimit.ι d.functor i).opensRange :=
  TopologicalSpace.Opens.coe_inj.mp (preimage_toBase_eq_range_ι d i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Cover.RelativeGluingData.isPullback_natTrans_** 是 Mat
hlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isPullback_natTrans_ι_toBase (i : 𝒰.I₀) :
    IsPullback (d.natTrans.app i) (colimit.ι d.functor i) (𝒰.f i) d.toBase := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    apply IsOpenImmersion.lift (colimit.ι d.functor i) s.snd
    rw [← preimage_toBase_eq_range_ι]
    rintro x ⟨x, rfl⟩
    use s.fst x
    rw [← Scheme.Hom.comp_apply, ← s.condition]
    simp
  · intro s
    rw [← cancel_mono (𝒰.f i), Category.assoc, ← ι_toBase, IsOpenImmersion.lift_fac_assoc,
      s.condition]
  · simp
  · intro s m h1 h2
    simpa [← cancel_mono (colimit.ι d.functor i)]

end Scheme.Cover.RelativeGluingData

end AlgebraicGeometry

