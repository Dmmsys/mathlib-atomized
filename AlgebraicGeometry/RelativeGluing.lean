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
/--
lemma `Scheme.isLocallyDirected_of_equifibered_of_injective` / 引理 `Scheme.isLocallyDirected_of_equifibered_of_injective`

English:
lemma Scheme.isLocallyDirected_of_equifibered_of_injective
  statement: {J : Type*} [Category J]
  proof: by
    simp only [Functor.comp_obj, Scheme.forget_obj, Functor.comp_map, Scheme.forget_map] at heq
    obtain ⟨l, fli, flj, x, hi, hj⟩ := (G ⋙ Scheme.forget).exists_map_eq_of_isLocallyDirected fi fj
(s.app i xi) (s.app j xj) by
      simp only [Functor.comp_obj, forget_obj, Functor.comp_map, forget_map,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
      dsimp at heq
      rw [← Scheme.Hom.comp_apply]; rw [← s.naturality]; rw [Scheme.Hom.comp_apply]; rw [heq]; rw [← Scheme.Hom.comp_apply]; rw [s.naturality]
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

中文:
引理 概形.isLocallyDirected_of_equifibered_of_injective
  结论: {J : 类型} [范畴 J]
  证明: by
    simp only [Functor.comp_obj, Scheme.forget_obj, Functor.comp_map, Scheme.forget_map] at heq
    obtain ⟨l, fli, flj, x, hi, hj⟩ := (G ⋙ Scheme.forget).exists_map_eq_of_isLocallyDirected fi fj
(s.app i xi) (s.app j xj) by
      simp only [Functor.comp_obj, forget_obj, Functor.comp_map, forget_map,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
      dsimp at heq
      rw [← Scheme.Hom.comp_apply]; rw [← s.naturality]; rw [Scheme.Hom.comp_apply]; rw [heq]; rw [← Scheme.Hom.comp_apply]; rw [s.naturality]
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

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ofHom, Functor, Functor.comp_map, Functor.comp_obj, Scheme, Scheme.Hom.comp_apply, Scheme.forget, Scheme.forget_map, Scheme.forget_obj, TypeCat, TypeCat.Fun.coe_mk, coe_mk, comp_apply, comp_map, comp_obj, exists_map_eq_of_isLocallyDirected, forget, forget_map, forget_obj
-/
lemma Scheme.isLocallyDirected_of_equifibered_of_injective {J : Type*} [Category J]
    {F G : J ⥤ Scheme.{u}} (s : F ⟶ G) [Quiver.IsThin J] (hs : s.Equifibered)
    (H : forall {i j} (hij : i ⟶ j), Function.Injective (F.map hij))
    [(G ⋙ Scheme.forget).IsLocallyDirected] :
    (F ⋙ Scheme.forget).IsLocallyDirected where
  cond {i j k} fi fj xi xj heq := by
    simp only [Functor.comp_obj, Scheme.forget_obj, Functor.comp_map, Scheme.forget_map] at heq
    obtain ⟨l, fli, flj, x, hi, hj⟩ := (G ⋙ Scheme.forget).exists_map_eq_of_isLocallyDirected fi fj
(s.app i xi) (s.app j xj) by
      simp only [Functor.comp_obj, forget_obj, Functor.comp_map, forget_map,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
      dsimp at heq
      rw [← Scheme.Hom.comp_apply]; rw [← s.naturality]; rw [Scheme.Hom.comp_apply]; rw [heq]; rw [← Scheme.Hom.comp_apply]; rw [s.naturality]
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
| |
v v
Xⱼ --> Uⱼ
```
is a pullback square. We bundle this in the form of a functor and an equifibered natural
transformation.
The `Xᵢ` then glue to a scheme over `S`
(see `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.glued`).
-/
@[stacks 01LH]
/--
Definition of `RelativeGluingData` / `RelativeGluingData` 的定义

English:
structure RelativeGluingData
  parameters: where
  axioms and operations (3):
    - functor : 𝒰.I₀ ⥤ Scheme.{u}
    - natTrans : functor ⟶ 𝒰.functorOfLocallyDirected
    - equifibered : natTrans.Equifibered

中文:
结构 RelativeGluingData
  参数: where
  公理与运算 (3 个):
    - functor : 𝒰.I₀ ⥤ 概形.{u}
    - natTrans : functor ⟶ 𝒰.functorOfLocallyDirected
    - equifibered : natTrans.Equifibered
-/
structure RelativeGluingData where
  /-- The schemes `Xᵢ`. -/
  functor : 𝒰.I₀ ⥤ Scheme.{u}
  /-- The natural maps `Xᵢ ⟶ Uᵢ`. -/
  natTrans : functor ⟶ 𝒰.functorOfLocallyDirected
  equifibered : natTrans.Equifibered

variable {𝒰} (d : RelativeGluingData 𝒰)

namespace RelativeGluingData

instance {i j : 𝒰.I₀} (hij : i ⟶ j) : IsOpenImmersion (d.functor.map hij) := by
  apply MorphismProperty.of_isPullback (d.equifibered hij).flip
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Quiver.IsThin
  signature: 𝒰.I₀] : (d.functor ⋙ Scheme.forget).IsLocallyDirected
  body: by
  apply isLocallyDirected_of_equifibered_of_injective d.natTrans d.equifibered
  intro i j hij
  exact (d.functor.map hij).injective

中文:
实例 [箭图.IsThin
  签名: 𝒰.I₀] : (d.functor ⋙ 概形.forget).是LocallyDirected
  定义体: by
  apply isLocallyDirected_of_equifibered_of_injective d.natTrans d.equifibered
  intro i j hij
  exact (d.functor.map hij).injective

Depends on / 依赖: d.equifibered, d.functor.map, d.natTrans, equifibered, functor, injective, isLocallyDirected_of_equifibered_of_injective, natTrans
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
/--
Definition of `glued` / `glued` 的定义

English:
abbreviation glued
  signature: : Scheme.{u}
  body: colimit d.functor

中文:
缩写 glued
  签名: : 概形.{u}
  定义体: colimit d.functor

Depends on / 依赖: colimit, d.functor, functor
-/
noncomputable abbrev glued : Scheme.{u} :=
  colimit d.functor

/-- The cover of the glued `Xᵢ` given by the `Xᵢ`. -/
@[simps!]
/--
Definition of `cover` / `cover` 的定义

English:
definition cover
  signature: : OpenCover d.glued
  body: Scheme.IsLocallyDirected.openCover _

中文:
定义 cover
  签名: : OpenCover d.glued
  定义体: Scheme.IsLocallyDirected.openCover _

Depends on / 依赖: IsLocallyDirected, Scheme, Scheme.IsLocallyDirected.openCover, openCover
-/
noncomputable def cover : OpenCover d.glued :=
  Scheme.IsLocallyDirected.openCover _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category d.cover.I₀
  body: inferInstanceAs Category 𝒰.I₀

中文:
实例 :
  签名: 范畴 d.cover.I₀
  定义体: inferInstanceAs Category 𝒰.I₀

Depends on / 依赖: Category
-/
instance : Category d.cover.I₀ :=
inferInstanceAs Category 𝒰.I₀

/--
Definition of `toBase` / `toBase` 的定义

English:
definition toBase
  signature: : d.glued ⟶ S
  body: colimit.desc _
    { pt := S
      ι := d.natTrans ≫ 𝒰.functorOfLocallyDirectedHomBase }

#adaptation_note

中文:
定义 toBase
  签名: : d.glued ⟶ S
  定义体: colimit.desc _
    { pt := S
      ι := d.natTrans ≫ 𝒰.functorOfLocallyDirectedHomBase }

#adaptation_note

Depends on / 依赖: colimit, colimit.desc, d.natTrans, functorOfLocallyDirectedHomBase, natTrans
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
/--
lemma `ι_toBase` / 引理 `ι_toBase`

English:
lemma ι_toBase
  given: (i : 𝒰.I₀)
  proof: by
  simp [toBase]

中文:
引理 ι_toBase
  条件: (i : 𝒰.I₀)
  证明: by
  simp [toBase]

Depends on / 依赖: toBase
-/
lemma ι_toBase (i : 𝒰.I₀) :
    colimit.ι d.functor i ≫ d.toBase = d.natTrans.app i ≫ 𝒰.f i := by
  simp [toBase]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: d.cover.LocallyDirected
  body: d.functor.map hij
  directed {i j} x := by
    let xi := pullback.fst (d.cover.f i) _ x
    let xj := pullback.snd (d.cover.f i) _ x
    obtain ⟨k, fi, fj, uk, h1, h2⟩ :=
𝒰.exists_of_f_eq_f (d.natTrans.app i xi) (d.natTrans.app j xj) by
      dsimp [functorOfLocallyDirected_obj, xi, xj]
      rw [← Scheme.Hom.comp_apply]; rw [← Scheme.Hom.comp_apply]; rw [← ι_toBase]; rw [pullback.condition_assoc]
      simp
    use k, fi, fj
obtain ⟨xk, h1, h2⟩ := exists_preimage_of_isPullback (d.equifibered fj) xj uk by
      apply (𝒰.f j).injective
      dsimp only [functorOfLocallyDirected_obj, functorOfLocallyDirected_map]
      rw [← Scheme.Hom.comp_apply]
      simp [xj, h2]
    use xk
    apply (pullback.snd (d.cover.f i) _).injective
    rw [← Scheme.Hom.comp_apply]
    simp [h1, xj]

中文:
实例 :
  签名: d.cover.LocallyDirected
  定义体: d.functor.map hij
  directed {i j} x := by
    let xi := pullback.fst (d.cover.f i) _ x
    let xj := pullback.snd (d.cover.f i) _ x
    obtain ⟨k, fi, fj, uk, h1, h2⟩ :=
𝒰.exists_of_f_eq_f (d.natTrans.app i xi) (d.natTrans.app j xj) by
      dsimp [functorOfLocallyDirected_obj, xi, xj]
      rw [← Scheme.Hom.comp_apply]; rw [← Scheme.Hom.comp_apply]; rw [← ι_toBase]; rw [pullback.condition_assoc]
      simp
    use k, fi, fj
obtain ⟨xk, h1, h2⟩ := exists_preimage_of_isPullback (d.equifibered fj) xj uk by
      apply (𝒰.f j).injective
      dsimp only [functorOfLocallyDirected_obj, functorOfLocallyDirected_map]
      rw [← Scheme.Hom.comp_apply]
      simp [xj, h2]
    use xk
    apply (pullback.snd (d.cover.f i) _).injective
    rw [← Scheme.Hom.comp_apply]
    simp [h1, xj]

Depends on / 依赖: d.functor.map, functor
-/
instance : d.cover.LocallyDirected where
  trans {i j} hij := d.functor.map hij
  directed {i j} x := by
    let xi := pullback.fst (d.cover.f i) _ x
    let xj := pullback.snd (d.cover.f i) _ x
    obtain ⟨k, fi, fj, uk, h1, h2⟩ :=
𝒰.exists_of_f_eq_f (d.natTrans.app i xi) (d.natTrans.app j xj) by
      dsimp [functorOfLocallyDirected_obj, xi, xj]
      rw [← Scheme.Hom.comp_apply]; rw [← Scheme.Hom.comp_apply]; rw [← ι_toBase]; rw [pullback.condition_assoc]
      simp
    use k, fi, fj
obtain ⟨xk, h1, h2⟩ := exists_preimage_of_isPullback (d.equifibered fj) xj uk by
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
/--
lemma `preimage_toBase_eq_range_ι` / 引理 `preimage_toBase_eq_range_ι`

English:
lemma preimage_toBase_eq_range_ι
  given: (i : 𝒰.I₀)
  proof: by
  ext x
  refine ⟨fun ⟨ui, h⟩ => ?_, ?_⟩
  · obtain ⟨j, xj, rfl⟩ := IsLocallyDirected.ι_jointly_surjective _ x
obtain ⟨k, fi, fj, uk, rfl, h⟩ := 𝒰.exists_of_f_eq_f ui (d.natTrans.app j xj) by
      simp only [h, functorOfLocallyDirected_obj, ← Scheme.Hom.comp_apply, ι_toBase]
obtain ⟨xk, rfl, h2⟩ := exists_preimage_of_isPullback (d.equifibered fj) xj uk by
      apply (𝒰.f j).injective
      simp only [functorOfLocallyDirected_obj, functorOfLocallyDirected_map]
      rw [← Scheme.Hom.comp_apply]; rw [← ι_toBase]; rw [Scheme.Hom.comp_apply]; rw [← h]
      simp [← Scheme.Hom.comp_apply]
    use d.functor.map fi xk
    simp [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  · rintro ⟨y, rfl⟩
    use d.natTrans.app i y
    rw [← Scheme.Hom.comp_apply]; rw [ι_toBase]
    simp

中文:
引理 preimage_toBase_eq_range_ι
  条件: (i : 𝒰.I₀)
  证明: by
  ext x
  refine ⟨fun ⟨ui, h⟩ => ?_, ?_⟩
  · obtain ⟨j, xj, rfl⟩ := IsLocallyDirected.ι_jointly_surjective _ x
obtain ⟨k, fi, fj, uk, rfl, h⟩ := 𝒰.exists_of_f_eq_f ui (d.natTrans.app j xj) by
      simp only [h, functorOfLocallyDirected_obj, ← Scheme.Hom.comp_apply, ι_toBase]
obtain ⟨xk, rfl, h2⟩ := exists_preimage_of_isPullback (d.equifibered fj) xj uk by
      apply (𝒰.f j).injective
      simp only [functorOfLocallyDirected_obj, functorOfLocallyDirected_map]
      rw [← Scheme.Hom.comp_apply]; rw [← ι_toBase]; rw [Scheme.Hom.comp_apply]; rw [← h]
      simp [← Scheme.Hom.comp_apply]
    use d.functor.map fi xk
    simp [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  · rintro ⟨y, rfl⟩
    use d.natTrans.app i y
    rw [← Scheme.Hom.comp_apply]; rw [ι_toBase]
    simp

Depends on / 依赖: IsLocallyDirected, Scheme, Scheme.Hom.comp_apply, comp_apply, d.equifibered, d.natTrans.app, equifibered, exists_of_f_eq_f, exists_preimage_of_isPullback, functorOfLocallyDirected_map, functorOfLocallyDirected_obj, injective, natTrans
-/
lemma preimage_toBase_eq_range_ι (i : 𝒰.I₀) :
    d.toBase ⁻¹' (Set.range <| 𝒰.f i) = Set.range (colimit.ι d.functor i) := by
  ext x
  refine ⟨fun ⟨ui, h⟩ => ?_, ?_⟩
  · obtain ⟨j, xj, rfl⟩ := IsLocallyDirected.ι_jointly_surjective _ x
obtain ⟨k, fi, fj, uk, rfl, h⟩ := 𝒰.exists_of_f_eq_f ui (d.natTrans.app j xj) by
      simp only [h, functorOfLocallyDirected_obj, ← Scheme.Hom.comp_apply, ι_toBase]
obtain ⟨xk, rfl, h2⟩ := exists_preimage_of_isPullback (d.equifibered fj) xj uk by
      apply (𝒰.f j).injective
      simp only [functorOfLocallyDirected_obj, functorOfLocallyDirected_map]
      rw [← Scheme.Hom.comp_apply]; rw [← ι_toBase]; rw [Scheme.Hom.comp_apply]; rw [← h]
      simp [← Scheme.Hom.comp_apply]
    use d.functor.map fi xk
    simp [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  · rintro ⟨y, rfl⟩
    use d.natTrans.app i y
    rw [← Scheme.Hom.comp_apply]; rw [ι_toBase]
    simp

/--
lemma `toBase_preimage_eq_opensRange_ι` / 引理 `toBase_preimage_eq_opensRange_ι`

English:
lemma toBase_preimage_eq_opensRange_ι
  given: (i : 𝒰.I₀)
  proof: TopologicalSpace.Opens.coe_inj.mp (preimage_toBase_eq_range_ι d i)

中文:
引理 toBase_preimage_eq_opensRange_ι
  条件: (i : 𝒰.I₀)
  证明: TopologicalSpace.Opens.coe_inj.mp (preimage_toBase_eq_range_ι d i)

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens.coe_inj.mp, coe_inj
-/
lemma toBase_preimage_eq_opensRange_ι (i : 𝒰.I₀) :
    d.toBase ⁻¹ᵁ (𝒰.f i).opensRange = (colimit.ι d.functor i).opensRange :=
  TopologicalSpace.Opens.coe_inj.mp (preimage_toBase_eq_range_ι d i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isPullback_natTrans_ι_toBase` / 引理 `isPullback_natTrans_ι_toBase`

English:
lemma isPullback_natTrans_ι_toBase
  given: (i : 𝒰.I₀)
  proof: by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    apply IsOpenImmersion.lift (colimit.ι d.functor i) s.snd
    rw [← preimage_toBase_eq_range_ι]
    rintro x ⟨x, rfl⟩
    use s.fst x
    rw [← Scheme.Hom.comp_apply]; rw [← s.condition]
    simp
  · intro s
    rw [← cancel_mono (𝒰.f i)]; rw [Category.assoc]; rw [← ι_toBase]; rw [IsOpenImmersion.lift_fac_assoc]; rw [s.condition]
  · simp
  · intro s m h1 h2
    simpa [← cancel_mono (colimit.ι d.functor i)]

中文:
引理 isPullback_natTrans_ι_toBase
  条件: (i : 𝒰.I₀)
  证明: by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    apply IsOpenImmersion.lift (colimit.ι d.functor i) s.snd
    rw [← preimage_toBase_eq_range_ι]
    rintro x ⟨x, rfl⟩
    use s.fst x
    rw [← Scheme.Hom.comp_apply]; rw [← s.condition]
    simp
  · intro s
    rw [← cancel_mono (𝒰.f i)]; rw [Category.assoc]; rw [← ι_toBase]; rw [IsOpenImmersion.lift_fac_assoc]; rw [s.condition]
  · simp
  · intro s m h1 h2
    simpa [← cancel_mono (colimit.ι d.functor i)]

Depends on / 依赖: Category, Category.assoc, IsLimit, IsOpenImmersion, IsOpenImmersion.lift, IsOpenImmersion.lift_fac_assoc, PullbackCone, PullbackCone.IsLimit.mk, Scheme, Scheme.Hom.comp_apply, cancel_mono, colimit, comp_apply, condition, d.functor, functor, lift_fac_assoc, s.condition, s.fst, s.snd
-/
lemma isPullback_natTrans_ι_toBase (i : 𝒰.I₀) :
    IsPullback (d.natTrans.app i) (colimit.ι d.functor i) (𝒰.f i) d.toBase := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    apply IsOpenImmersion.lift (colimit.ι d.functor i) s.snd
    rw [← preimage_toBase_eq_range_ι]
    rintro x ⟨x, rfl⟩
    use s.fst x
    rw [← Scheme.Hom.comp_apply]; rw [← s.condition]
    simp
  · intro s
    rw [← cancel_mono (𝒰.f i)]; rw [Category.assoc]; rw [← ι_toBase]; rw [IsOpenImmersion.lift_fac_assoc]; rw [s.condition]
  · simp
  · intro s m h1 h2
    simpa [← cancel_mono (colimit.ι d.functor i)]

end Scheme.Cover.RelativeGluingData

end AlgebraicGeometry
