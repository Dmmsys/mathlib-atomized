/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.LocalAtTarget
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors

/-!
# Properties on the underlying functions of morphisms of schemes

This file includes various results on properties of morphisms of schemes that come from properties
of the underlying map of topological spaces, including

- `Injective`
- `Surjective`
- `IsOpenMap`
- `IsClosedMap`
- `GeneralizingMap`
- `IsEmbedding`
- `IsOpenEmbedding`
- `IsClosedEmbedding`
- `DenseRange` (`IsDominant`)

-/

@[expose] public section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u v

section Injective

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.RespectsIso (topologically Function.Injective)
  body: topologically_respectsIso _ (fun e => e.injective) (fun _ _ hf hg => hg.comp hf)

中文:
实例 :
  签名: Morphism命题erty.RespectsIso (topologically Function.Injective)
  定义体: topologically_respectsIso _ (fun e => e.injective) (fun _ _ hf hg => hg.comp hf)

Depends on / 依赖: e.injective, hg.comp, injective, topologically_respectsIso
-/
instance : MorphismProperty.RespectsIso (topologically Function.Injective) :=
  topologically_respectsIso _ (fun e => e.injective) (fun _ _ hf hg => hg.comp hf)

/--
Instance `injective_isZariskiLocalAtTarget` / 实例 `injective_isZariskiLocalAtTarget`

English:
instance injective_isZariskiLocalAtTarget
  signature: :
  body: by
  refine topologically_isZariskiLocalAtTarget _ (fun _ s _ _ h => h.restrictPreimage s)
    fun f ι U H _ hf x₁ x₂ e => ?_
  obtain ⟨i, hxi⟩ : exists i, f x₁ in U i := by simpa using congr(f x₁ in $H)
  exact congr(($(@hf i ⟨x₁, hxi⟩ ⟨x₂, show f x₂ in U i from e ▸ hxi⟩ (Subtype.ext e))).1)

中文:
实例 injective_isZariskiLocalAtTarget
  签名: :
  定义体: by
  refine topologically_isZariskiLocalAtTarget _ (fun _ s _ _ h => h.restrictPreimage s)
    fun f ι U H _ hf x₁ x₂ e => ?_
  obtain ⟨i, hxi⟩ : exists i, f x₁ in U i := by simpa using congr(f x₁ in $H)
  exact congr(($(@hf i ⟨x₁, hxi⟩ ⟨x₂, show f x₂ in U i from e ▸ hxi⟩ (Subtype.ext e))).1)

Depends on / 依赖: Subtype, Subtype.ext, h.restrictPreimage, restrictPreimage, topologically_isZariskiLocalAtTarget
-/
instance injective_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically Function.Injective) := by
  refine topologically_isZariskiLocalAtTarget _ (fun _ s _ _ h => h.restrictPreimage s)
    fun f ι U H _ hf x₁ x₂ e => ?_
  obtain ⟨i, hxi⟩ : exists i, f x₁ in U i := by simpa using congr(f x₁ in $H)
  exact congr(($(@hf i ⟨x₁, hxi⟩ ⟨x₂, show f x₂ in U i from e ▸ hxi⟩ (Subtype.ext e))).1)

end Injective

section Surjective

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes is surjective if the underlying map is. -/
@[mk_iff]
/--
Definition of `Surjective` / `Surjective` 的定义

English:
class Surjective
  parameters: : Prop where
  axioms and operations (1):
    - surj : Function.Surjective f

中文:
类 Surjective
  参数: : 命题 where
  公理与运算 (1 个):
    - surj : Function.Surjective f
-/
class Surjective : Prop where
  surj : Function.Surjective f

/--
lemma `surjective_eq_topologically` / 引理 `surjective_eq_topologically`

English:
lemma surjective_eq_topologically
  proof: by ext; exact surjective_iff _

@[grind .]

中文:
引理 surjective_eq_topologically
  证明: by ext; exact surjective_iff _

@[grind .]

Depends on / 依赖: surjective_iff
-/
lemma surjective_eq_topologically :
    @Surjective = topologically Function.Surjective := by ext; exact surjective_iff _

@[grind .]
/--
lemma `Scheme.Hom.surjective` / 引理 `Scheme.Hom.surjective`

English:
lemma Scheme.Hom.surjective
  given: (f : X ⟶ Y) [Surjective f]
  statement: Function.Surjective f
  proof: Surjective.surj

中文:
引理 Scheme.Hom.surjective
  条件: (f : X ⟶ Y) [Surjective f]
  结论: Function.Surjective f
  证明: Surjective.surj

Depends on / 依赖: Surjective, Surjective.surj
-/
lemma Scheme.Hom.surjective (f : X ⟶ Y) [Surjective f] : Function.Surjective f :=
  Surjective.surj

instance (priority := 100) [IsIso f] : Surjective f := ⟨f.homeomorph.surjective⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Surjective
  signature: f] [Surjective g] : Surjective (f ≫ g)
  body: ⟨g.surjective.comp f.surjective⟩

中文:
实例 [Surjective
  签名: f] [Surjective g] : Surjective (f ≫ g)
  定义体: ⟨g.surjective.comp f.surjective⟩

Depends on / 依赖: f.surjective, g.surjective.comp, surjective
-/
instance [Surjective f] [Surjective g] : Surjective (f ≫ g) := ⟨g.surjective.comp f.surjective⟩

/--
lemma `Surjective.of_comp` / 引理 `Surjective.of_comp`

English:
lemma Surjective.of_comp
  given: [Surjective (f ≫ g)]
  statement: Surjective g where
  proof: Function.Surjective.of_comp (g := f) (f ≫ g).surjective

中文:
引理 Surjective.of_comp
  条件: [Surjective (f ≫ g)]
  结论: Surjective g where
  证明: Function.Surjective.of_comp (g := f) (f ≫ g).surjective

Depends on / 依赖: Function, Function.Surjective.of_comp, Surjective, of_comp, surjective
-/
lemma Surjective.of_comp [Surjective (f ≫ g)] : Surjective g where
  surj := Function.Surjective.of_comp (g := f) (f ≫ g).surjective

instance (priority := low) [Nonempty X] [Subsingleton Y] (f : X ⟶ Y) :
    Surjective f := ⟨Function.surjective_to_subsingleton _⟩

/--
lemma `Surjective.comp_iff` / 引理 `Surjective.comp_iff`

English:
lemma Surjective.comp_iff
  given: [Surjective f]
  statement: Surjective (f ≫ g) ↔ Surjective g
  proof: ⟨fun _ => of_comp f g, fun _ => inferInstance⟩

中文:
引理 Surjective.comp_iff
  条件: [Surjective f]
  结论: Surjective (f ≫ g) ↔ Surjective g
  证明: ⟨fun _ => of_comp f g, fun _ => inferInstance⟩

Depends on / 依赖: of_comp
-/
lemma Surjective.comp_iff [Surjective f] : Surjective (f ≫ g) ↔ Surjective g :=
  ⟨fun _ => of_comp f g, fun _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @Surjective.{u}
  body: inferInstance
  comp_mem _ _ hf hg := ⟨hg.1.comp hf.1⟩

中文:
实例 :
  签名: Morphism命题erty.IsMultiplicative @Surjective.{u}
  定义体: inferInstance
  comp_mem _ _ hf hg := ⟨hg.1.comp hf.1⟩
-/
instance : MorphismProperty.IsMultiplicative @Surjective.{u} where
  id_mem _ := inferInstance
  comp_mem _ _ hf hg := ⟨hg.1.comp hf.1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.RespectsIso @Surjective
  body: surjective_eq_topologically ▸ topologically_respectsIso _ (fun e => e.surjective)
    (fun _ _ hf hg => hg.comp hf)

中文:
实例 :
  签名: Morphism命题erty.RespectsIso @Surjective
  定义体: surjective_eq_topologically ▸ topologically_respectsIso _ (fun e => e.surjective)
    (fun _ _ hf hg => hg.comp hf)

Depends on / 依赖: e.surjective, hg.comp, surjective, surjective_eq_topologically, topologically_respectsIso
-/
instance : MorphismProperty.RespectsIso @Surjective :=
  surjective_eq_topologically ▸ topologically_respectsIso _ (fun e => e.surjective)
    (fun _ _ hf hg => hg.comp hf)

instance (P : MorphismProperty Scheme.{u}) :
    MorphismProperty.HasOfPrecompProperty @Surjective P where
  of_precomp f g _ _ := .of_comp f g

/--
Instance `surjective_isZariskiLocalAtTarget` / 实例 `surjective_isZariskiLocalAtTarget`

English:
instance surjective_isZariskiLocalAtTarget
  signature: : IsZariskiLocalAtTarget @Surjective
  body: by
  have : MorphismProperty.RespectsIso @Surjective := inferInstance
  rw [surjective_eq_topologically] at this ⊢
  refine topologically_isZariskiLocalAtTarget _ (fun _ s _ _ h => h.restrictPreimage s) ?_
  intro α β _ _ f ι U H _ hf x
  obtain ⟨i, hxi⟩ : exists i, x in U i := by simpa using congr(

中文:
实例 surjective_isZariskiLocalAtTarget
  签名: : IsZariskiLocalAtTarget @Surjective
  定义体: by
  have : MorphismProperty.RespectsIso @Surjective := inferInstance
  rw [surjective_eq_topologically] at this ⊢
  refine topologically_isZariskiLocalAtTarget _ (fun _ s _ _ h => h.restrictPreimage s) ?_
  intro α β _ _ f ι U H _ hf x
  obtain ⟨i, hxi⟩ : exists i, x in U i := by simpa using congr(

Depends on / 依赖: MorphismProperty, MorphismProperty.RespectsIso, RespectsIso, Surjective, h.restrictPreimage, restrictPreimage, surjective_eq_topologically, topologically_isZariskiLocalAtTarget
-/
instance surjective_isZariskiLocalAtTarget : IsZariskiLocalAtTarget @Surjective := by
  have : MorphismProperty.RespectsIso @Surjective := inferInstance
  rw [surjective_eq_topologically] at this ⊢
  refine topologically_isZariskiLocalAtTarget _ (fun _ s _ _ h => h.restrictPreimage s) ?_
  intro α β _ _ f ι U H _ hf x
  obtain ⟨i, hxi⟩ : exists i, x in U i := by simpa using congr(x in $H)
  obtain ⟨⟨y, _⟩, hy⟩ := hf i ⟨x, hxi⟩
  exact ⟨y, congr(($hy).1)⟩

@[simp]
/--
lemma `range_eq_univ` / 引理 `range_eq_univ`

English:
lemma range_eq_univ
  given: [Surjective f]
  statement: Set.range f = Set.univ
  proof: by
  simpa [Set.range_eq_univ] using f.surjective

中文:
引理 range_eq_univ
  条件: [Surjective f]
  结论: Set.range f = Set.univ
  证明: by
  simpa [Set.range_eq_univ] using f.surjective

Depends on / 依赖: Set.range_eq_univ, f.surjective, range_eq_univ, surjective
-/
lemma range_eq_univ [Surjective f] : Set.range f = Set.univ := by
  simpa [Set.range_eq_univ] using f.surjective

/--
lemma `range_eq_range_of_surjective` / 引理 `range_eq_range_of_surjective`

English:
lemma range_eq_range_of_surjective
  statement: {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : X ⟶ Y)
  proof: by
  rw [← hge]
  simp [Set.range_comp]

中文:
引理 range_eq_range_of_surjective
  结论: {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : X ⟶ Y)
  证明: by
  rw [← hge]
  simp [Set.range_comp]

Depends on / 依赖: Set.range_comp, range_comp
-/
lemma range_eq_range_of_surjective {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : X ⟶ Y)
    [Surjective e] (hge : e ≫ g = f) : Set.range f = Set.range g := by
  rw [← hge]
  simp [Set.range_comp]

/--
lemma `mem_range_iff_of_surjective` / 引理 `mem_range_iff_of_surjective`

English:
lemma mem_range_iff_of_surjective
  statement: {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : X ⟶ Y)
  proof: by
  rw [range_eq_range_of_surjective f g e hge]

中文:
引理 mem_range_iff_of_surjective
  结论: {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : X ⟶ Y)
  证明: by
  rw [range_eq_range_of_surjective f g e hge]

Depends on / 依赖: range_eq_range_of_surjective
-/
lemma mem_range_iff_of_surjective {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : X ⟶ Y)
    [Surjective e] (hge : e ≫ g = f) (s : S) : s in Set.range f ↔ s in Set.range g := by
  rw [range_eq_range_of_surjective f g e hge]

/--
lemma `Surjective.sigmaDesc_of_union_range_eq_univ` / 引理 `Surjective.sigmaDesc_of_union_range_eq_univ`

English:
lemma Surjective.sigmaDesc_of_union_range_eq_univ
  statement: {X : Scheme.{u}}
  proof: by
  refine ⟨fun x => ?_⟩
  simp_rw [Set.eq_univ_iff_forall, Set.mem_iUnion] at H
  obtain ⟨i, x, rfl⟩ := H x
  use Limits.Sigma.ι Y i x
  rw [← Scheme.Hom.comp_apply]; rw [Limits.Sigma.ι_desc]

中文:
引理 Surjective.sigmaDesc_of_union_range_eq_univ
  结论: {X : Scheme.{u}}
  证明: by
  refine ⟨fun x => ?_⟩
  simp_rw [Set.eq_univ_iff_forall, Set.mem_iUnion] at H
  obtain ⟨i, x, rfl⟩ := H x
  use Limits.Sigma.ι Y i x
  rw [← Scheme.Hom.comp_apply]; rw [Limits.Sigma.ι_desc]

Depends on / 依赖: Limits, Limits.Sigma, Scheme, Scheme.Hom.comp_apply, Set.eq_univ_iff_forall, Set.mem_iUnion, comp_apply, eq_univ_iff_forall, mem_iUnion, simp_rw
-/
lemma Surjective.sigmaDesc_of_union_range_eq_univ {X : Scheme.{u}}
    {ι : Type v} [Small.{u} ι] {Y : ι -> Scheme.{u}} {f : forall i, Y i ⟶ X}
    (H : ⋃ i, Set.range (f i) = Set.univ) : Surjective (Limits.Sigma.desc f) := by
  refine ⟨fun x => ?_⟩
  simp_rw [Set.eq_univ_iff_forall, Set.mem_iUnion] at H
  obtain ⟨i, x, rfl⟩ := H x
  use Limits.Sigma.ι Y i x
  rw [← Scheme.Hom.comp_apply]; rw [Limits.Sigma.ι_desc]

instance {X : Scheme.{u}} {P : MorphismProperty Scheme.{u}} (𝒰 : X.Cover (Scheme.precoverage P)) :
    Surjective (Limits.Sigma.desc fun i => 𝒰.f i) :=
  Surjective.sigmaDesc_of_union_range_eq_univ 𝒰.iUnion_range

/-- The single object covering by one surjective morphism satisfying `P`. -/
@[simps! I₀ X f]
/--
Definition of `Scheme.Hom.cover` / `Scheme.Hom.cover` 的定义

English:
definition Scheme.Hom.cover
  signature: {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f)
  body: .singleton f by
    rw [singleton_mem_precoverage_iff]
    exact ⟨f.surjective, hf⟩

@[simp]

中文:
定义 Scheme.Hom.cover
  签名: {P : Morphism命题erty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f)
  定义体: .singleton f by
    rw [singleton_mem_precoverage_iff]
    exact ⟨f.surjective, hf⟩

@[simp]

Depends on / 依赖: f.surjective, singleton, singleton_mem_precoverage_iff, surjective
-/
def Scheme.Hom.cover {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f)
    [Surjective f] : Cover.{v} (precoverage P) S :=
.singleton f by
    rw [singleton_mem_precoverage_iff]
    exact ⟨f.surjective, hf⟩

@[simp]
/--
lemma `Scheme.Hom.presieve₀_cover` / 引理 `Scheme.Hom.presieve₀_cover`

English:
lemma Scheme.Hom.presieve₀_cover
  statement: {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S)
  proof: by
  simp [cover]

中文:
引理 Scheme.Hom.presieve₀_cover
  结论: {P : Morphism命题erty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S)
  证明: by
  simp [cover]
-/
lemma Scheme.Hom.presieve₀_cover {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : P f) [Surjective f] : (f.cover hf).presieve₀ = Presieve.singleton f := by
  simp [cover]

instance {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f)
    [Surjective f] : Unique (Scheme.Hom.cover f hf).I₀ :=
inferInstanceAs Unique PUnit

end Surjective

section Injective

/--
Instance `injective_isStableUnderComposition` / 实例 `injective_isStableUnderComposition`

English:
instance injective_isStableUnderComposition
  signature: :
  body: hg.comp hf

中文:
实例 injective_isStableUnderComposition
  签名: :
  定义体: hg.comp hf

Depends on / 依赖: hg.comp
-/
instance injective_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (topologically (Function.Injective ·)) where
  comp_mem _ _ hf hg := hg.comp hf

end Injective

section IsOpenMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (topologically IsOpenMap).RespectsIso
  body: topologically_respectsIso _ (fun e => e.isOpenMap) (fun _ _ hf hg => hg.comp hf)

中文:
实例 :
  签名: (topologically IsOpenMap).RespectsIso
  定义体: topologically_respectsIso _ (fun e => e.isOpenMap) (fun _ _ hf hg => hg.comp hf)

Depends on / 依赖: e.isOpenMap, hg.comp, isOpenMap, topologically_respectsIso
-/
instance : (topologically IsOpenMap).RespectsIso :=
  topologically_respectsIso _ (fun e => e.isOpenMap) (fun _ _ hf hg => hg.comp hf)

/--
Instance `isOpenMap_isZariskiLocalAtTarget` / 实例 `isOpenMap_isZariskiLocalAtTarget`

English:
instance isOpenMap_isZariskiLocalAtTarget
  signature: : IsZariskiLocalAtTarget (topologically IsOpenMap)
  body: topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU _ => hU.isOpenMap_iff_restrictPreimage

中文:
实例 isOpenMap_isZariskiLocalAtTarget
  签名: : IsZariskiLocalAtTarget (topologically IsOpenMap)
  定义体: topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU _ => hU.isOpenMap_iff_restrictPreimage

Depends on / 依赖: hU.isOpenMap_iff_restrictPreimage, isOpenMap_iff_restrictPreimage, topologically_isZariskiLocalAtTarget
-/
instance isOpenMap_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically IsOpenMap) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU _ => hU.isOpenMap_iff_restrictPreimage

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtSource (topologically IsOpenMap)
  body: topologically_isZariskiLocalAtSource' (fun _ => _) fun _ _ _ hU _ => hU.isOpenMap_iff_comp

中文:
实例 :
  签名: IsZariskiLocalAtSource (topologically IsOpenMap)
  定义体: topologically_isZariskiLocalAtSource' (fun _ => _) fun _ _ _ hU _ => hU.isOpenMap_iff_comp

Depends on / 依赖: hU.isOpenMap_iff_comp, isOpenMap_iff_comp, topologically_isZariskiLocalAtSource
-/
instance : IsZariskiLocalAtSource (topologically IsOpenMap) :=
  topologically_isZariskiLocalAtSource' (fun _ => _) fun _ _ _ hU _ => hU.isOpenMap_iff_comp

end IsOpenMap

section IsClosedMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (topologically IsClosedMap).RespectsIso
  body: topologically_respectsIso _ (fun e => e.isClosedMap) (fun _ _ hf hg => hg.comp hf)

中文:
实例 :
  签名: (topologically IsClosedMap).RespectsIso
  定义体: topologically_respectsIso _ (fun e => e.isClosedMap) (fun _ _ hf hg => hg.comp hf)

Depends on / 依赖: e.isClosedMap, hg.comp, isClosedMap, topologically_respectsIso
-/
instance : (topologically IsClosedMap).RespectsIso :=
  topologically_respectsIso _ (fun e => e.isClosedMap) (fun _ _ hf hg => hg.comp hf)

/--
Instance `isClosedMap_isZariskiLocalAtTarget` / 实例 `isClosedMap_isZariskiLocalAtTarget`

English:
instance isClosedMap_isZariskiLocalAtTarget
  signature: : IsZariskiLocalAtTarget (topologically IsClosedMap)
  body: topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU _ => hU.isClosedMap_iff_restrictPreimage

中文:
实例 isClosedMap_isZariskiLocalAtTarget
  签名: : IsZariskiLocalAtTarget (topologically IsClosedMap)
  定义体: topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU _ => hU.isClosedMap_iff_restrictPreimage

Depends on / 依赖: hU.isClosedMap_iff_restrictPreimage, isClosedMap_iff_restrictPreimage, topologically_isZariskiLocalAtTarget
-/
instance isClosedMap_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically IsClosedMap) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU _ => hU.isClosedMap_iff_restrictPreimage

end IsClosedMap

section IsEmbedding

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (topologically IsEmbedding).RespectsIso
  body: topologically_respectsIso _ (fun e => e.isEmbedding) (fun _ _ hf hg => hg.comp hf)

中文:
实例 :
  签名: (topologically IsEmbedding).RespectsIso
  定义体: topologically_respectsIso _ (fun e => e.isEmbedding) (fun _ _ hf hg => hg.comp hf)

Depends on / 依赖: e.isEmbedding, hg.comp, isEmbedding, topologically_respectsIso
-/
instance : (topologically IsEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e => e.isEmbedding) (fun _ _ hf hg => hg.comp hf)

/--
Instance `isEmbedding_isZariskiLocalAtTarget` / 实例 `isEmbedding_isZariskiLocalAtTarget`

English:
instance isEmbedding_isZariskiLocalAtTarget
  signature: : IsZariskiLocalAtTarget (topologically IsEmbedding)
  body: topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU => hU.isEmbedding_iff_restrictPreimage

中文:
实例 isEmbedding_isZariskiLocalAtTarget
  签名: : IsZariskiLocalAtTarget (topologically IsEmbedding)
  定义体: topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU => hU.isEmbedding_iff_restrictPreimage

Depends on / 依赖: hU.isEmbedding_iff_restrictPreimage, isEmbedding_iff_restrictPreimage, topologically_isZariskiLocalAtTarget
-/
instance isEmbedding_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically IsEmbedding) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU => hU.isEmbedding_iff_restrictPreimage

end IsEmbedding

section IsOpenEmbedding

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (topologically IsOpenEmbedding).RespectsIso
  body: topologically_respectsIso _ (fun e => e.isOpenEmbedding) (fun _ _ hf hg => hg.comp hf)

中文:
实例 :
  签名: (topologically IsOpenEmbedding).RespectsIso
  定义体: topologically_respectsIso _ (fun e => e.isOpenEmbedding) (fun _ _ hf hg => hg.comp hf)

Depends on / 依赖: e.isOpenEmbedding, hg.comp, isOpenEmbedding, topologically_respectsIso
-/
instance : (topologically IsOpenEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e => e.isOpenEmbedding) (fun _ _ hf hg => hg.comp hf)

/--
Instance `isOpenEmbedding_isZariskiLocalAtTarget` / 实例 `isOpenEmbedding_isZariskiLocalAtTarget`

English:
instance isOpenEmbedding_isZariskiLocalAtTarget
  signature: :
  body: topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU => hU.isOpenEmbedding_iff_restrictPreimage

中文:
实例 isOpenEmbedding_isZariskiLocalAtTarget
  签名: :
  定义体: topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU => hU.isOpenEmbedding_iff_restrictPreimage

Depends on / 依赖: hU.isOpenEmbedding_iff_restrictPreimage, isOpenEmbedding_iff_restrictPreimage, topologically_isZariskiLocalAtTarget
-/
instance isOpenEmbedding_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically IsOpenEmbedding) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU => hU.isOpenEmbedding_iff_restrictPreimage

end IsOpenEmbedding

section IsClosedEmbedding

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (topologically IsClosedEmbedding).RespectsIso
  body: topologically_respectsIso _ (fun e => e.isClosedEmbedding) (fun _ _ hf hg => hg.comp hf)

中文:
实例 :
  签名: (topologically IsClosedEmbedding).RespectsIso
  定义体: topologically_respectsIso _ (fun e => e.isClosedEmbedding) (fun _ _ hf hg => hg.comp hf)

Depends on / 依赖: e.isClosedEmbedding, hg.comp, isClosedEmbedding, topologically_respectsIso
-/
instance : (topologically IsClosedEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e => e.isClosedEmbedding) (fun _ _ hf hg => hg.comp hf)

/--
Instance `isClosedEmbedding_isZariskiLocalAtTarget` / 实例 `isClosedEmbedding_isZariskiLocalAtTarget`

English:
instance isClosedEmbedding_isZariskiLocalAtTarget
  signature: :
  body: topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU => hU.isClosedEmbedding_iff_restrictPreimage

中文:
实例 isClosedEmbedding_isZariskiLocalAtTarget
  签名: :
  定义体: topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU => hU.isClosedEmbedding_iff_restrictPreimage

Depends on / 依赖: hU.isClosedEmbedding_iff_restrictPreimage, isClosedEmbedding_iff_restrictPreimage, topologically_isZariskiLocalAtTarget
-/
instance isClosedEmbedding_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically IsClosedEmbedding) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU => hU.isClosedEmbedding_iff_restrictPreimage

end IsClosedEmbedding

section IsDominant

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes is dominant if the underlying map has dense range. -/
@[mk_iff]
/--
Definition of `IsDominant` / `IsDominant` 的定义

English:
class IsDominant
  parameters: : Prop where
  axioms and operations (1):
    - denseRange : DenseRange f

中文:
类 IsDominant
  参数: : 命题 where
  公理与运算 (1 个):
    - denseRange : DenseRange f
-/
class IsDominant : Prop where
  denseRange : DenseRange f

/--
lemma `dominant_eq_topologically` / 引理 `dominant_eq_topologically`

English:
lemma dominant_eq_topologically
  proof: by ext; exact isDominant_iff _

中文:
引理 dominant_eq_topologically
  证明: by ext; exact isDominant_iff _

Depends on / 依赖: isDominant_iff
-/
lemma dominant_eq_topologically :
    @IsDominant = topologically DenseRange := by ext; exact isDominant_iff _

/--
lemma `Scheme.Hom.denseRange` / 引理 `Scheme.Hom.denseRange`

English:
lemma Scheme.Hom.denseRange
  given: (f : X ⟶ Y) [IsDominant f]
  statement: DenseRange f
  proof: IsDominant.denseRange

中文:
引理 Scheme.Hom.denseRange
  条件: (f : X ⟶ Y) [IsDominant f]
  结论: DenseRange f
  证明: IsDominant.denseRange

Depends on / 依赖: IsDominant, IsDominant.denseRange, denseRange
-/
lemma Scheme.Hom.denseRange (f : X ⟶ Y) [IsDominant f] : DenseRange f :=
  IsDominant.denseRange

instance (priority := 100) [Surjective f] : IsDominant f := ⟨f.surjective.denseRange⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDominant
  signature: f] [IsDominant g] : IsDominant (f ≫ g)
  body: ⟨g.denseRange.comp f.denseRange g.continuous⟩

中文:
实例 [IsDominant
  签名: f] [IsDominant g] : IsDominant (f ≫ g)
  定义体: ⟨g.denseRange.comp f.denseRange g.continuous⟩

Depends on / 依赖: continuous, denseRange, f.denseRange, g.continuous, g.denseRange.comp
-/
instance [IsDominant f] [IsDominant g] : IsDominant (f ≫ g) :=
  ⟨g.denseRange.comp f.denseRange g.continuous⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @IsDominant
  body: fun _ => inferInstance
  comp_mem := fun _ _ _ _ => inferInstance

中文:
实例 :
  签名: Morphism命题erty.IsMultiplicative @IsDominant
  定义体: fun _ => inferInstance
  comp_mem := fun _ _ _ _ => inferInstance
-/
instance : MorphismProperty.IsMultiplicative @IsDominant where
  id_mem := fun _ => inferInstance
  comp_mem := fun _ _ _ _ => inferInstance

/--
lemma `IsDominant.of_comp` / 引理 `IsDominant.of_comp`

English:
lemma IsDominant.of_comp
  given: [H : IsDominant (f ≫ g)]
  statement: IsDominant g
  proof: by
  rw [isDominant_iff]; rw [denseRange_iff_closure_range]; rw [← Set.univ_subset_iff] at H ⊢
  exact H.trans (closure_mono (Set.range_comp_subset_range f g))

中文:
引理 IsDominant.of_comp
  条件: [H : IsDominant (f ≫ g)]
  结论: IsDominant g
  证明: by
  rw [isDominant_iff]; rw [denseRange_iff_closure_range]; rw [← Set.univ_subset_iff] at H ⊢
  exact H.trans (closure_mono (Set.range_comp_subset_range f g))

Depends on / 依赖: H.trans, Set.range_comp_subset_range, Set.univ_subset_iff, closure_mono, denseRange_iff_closure_range, isDominant_iff, range_comp_subset_range, univ_subset_iff
-/
lemma IsDominant.of_comp [H : IsDominant (f ≫ g)] : IsDominant g := by
  rw [isDominant_iff]; rw [denseRange_iff_closure_range]; rw [← Set.univ_subset_iff] at H ⊢
  exact H.trans (closure_mono (Set.range_comp_subset_range f g))

/--
lemma `IsDominant.comp_iff` / 引理 `IsDominant.comp_iff`

English:
lemma IsDominant.comp_iff
  given: [IsDominant f]
  statement: IsDominant (f ≫ g) ↔ IsDominant g
  proof: ⟨fun _ => of_comp f g, fun _ => inferInstance⟩

中文:
引理 IsDominant.comp_iff
  条件: [IsDominant f]
  结论: IsDominant (f ≫ g) ↔ IsDominant g
  证明: ⟨fun _ => of_comp f g, fun _ => inferInstance⟩

Depends on / 依赖: of_comp
-/
lemma IsDominant.comp_iff [IsDominant f] : IsDominant (f ≫ g) ↔ IsDominant g :=
  ⟨fun _ => of_comp f g, fun _ => inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `IsDominant.respectsIso` / 实例 `IsDominant.respectsIso`

English:
instance IsDominant.respectsIso
  signature: : MorphismProperty.RespectsIso @IsDominant
  body: MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) => inferInstance

中文:
实例 IsDominant.respectsIso
  签名: : Morphism命题erty.RespectsIso @IsDominant
  定义体: MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) => inferInstance

Depends on / 依赖: MorphismProperty, MorphismProperty.respectsIso_of_isStableUnderComposition, respectsIso_of_isStableUnderComposition
-/
instance IsDominant.respectsIso : MorphismProperty.RespectsIso @IsDominant :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) => inferInstance

/--
Instance `IsDominant.isZariskiLocalAtTarget` / 实例 `IsDominant.isZariskiLocalAtTarget`

English:
instance IsDominant.isZariskiLocalAtTarget
  signature: : IsZariskiLocalAtTarget @IsDominant
  body: have : MorphismProperty.RespectsIso (topologically DenseRange) :=
    dominant_eq_topologically ▸ IsDominant.respectsIso
  dominant_eq_topologically ▸ topologically_isZariskiLocalAtTarget' DenseRange
    fun _ _ _ hU _ => hU.denseRange_iff_restrictPreimage

中文:
实例 IsDominant.isZariskiLocalAtTarget
  签名: : IsZariskiLocalAtTarget @IsDominant
  定义体: have : MorphismProperty.RespectsIso (topologically DenseRange) :=
    dominant_eq_topologically ▸ IsDominant.respectsIso
  dominant_eq_topologically ▸ topologically_isZariskiLocalAtTarget' DenseRange
    fun _ _ _ hU _ => hU.denseRange_iff_restrictPreimage

Depends on / 依赖: DenseRange, IsDominant, IsDominant.respectsIso, MorphismProperty, MorphismProperty.RespectsIso, RespectsIso, denseRange_iff_restrictPreimage, dominant_eq_topologically, hU.denseRange_iff_restrictPreimage, respectsIso, topologically, topologically_isZariskiLocalAtTarget
-/
instance IsDominant.isZariskiLocalAtTarget : IsZariskiLocalAtTarget @IsDominant :=
  have : MorphismProperty.RespectsIso (topologically DenseRange) :=
    dominant_eq_topologically ▸ IsDominant.respectsIso
  dominant_eq_topologically ▸ topologically_isZariskiLocalAtTarget' DenseRange
    fun _ _ _ hU _ => hU.denseRange_iff_restrictPreimage

/--
lemma `surjective_of_isDominant_of_isClosed_range` / 引理 `surjective_of_isDominant_of_isClosed_range`

English:
lemma surjective_of_isDominant_of_isClosed_range
  statement: (f : X ⟶ Y) [IsDominant f]
  proof: ⟨by rw [← Set.range_eq_univ, ← hf.closure_eq, f.denseRange.closure_range]⟩

中文:
引理 surjective_of_isDominant_of_isClosed_range
  结论: (f : X ⟶ Y) [IsDominant f]
  证明: ⟨by rw [← Set.range_eq_univ, ← hf.closure_eq, f.denseRange.closure_range]⟩

Depends on / 依赖: Set.range_eq_univ, closure_eq, closure_range, denseRange, f.denseRange.closure_range, hf.closure_eq, range_eq_univ
-/
lemma surjective_of_isDominant_of_isClosed_range (f : X ⟶ Y) [IsDominant f]
    (hf : IsClosed (Set.range f)) :
    Surjective f :=
  ⟨by rw [← Set.range_eq_univ, ← hf.closure_eq, f.denseRange.closure_range]⟩

/--
lemma `IsDominant.of_comp_of_isOpenImmersion` / 引理 `IsDominant.of_comp_of_isOpenImmersion`

English:
lemma IsDominant.of_comp_of_isOpenImmersion
  proof: by
  rw [isDominant_iff]; rw [DenseRange] at H ⊢
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] at H
  convert H.preimage g.isOpenEmbedding.isOpenMap
  rw [Set.preimage_image_eq _ g.isOpenEmbedding.injective]

中文:
引理 IsDominant.of_comp_of_isOpenImmersion
  证明: by
  rw [isDominant_iff]; rw [DenseRange] at H ⊢
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] at H
  convert H.preimage g.isOpenEmbedding.isOpenMap
  rw [Set.preimage_image_eq _ g.isOpenEmbedding.injective]

Depends on / 依赖: DenseRange, H.preimage, Scheme, Scheme.Hom.comp_base, Set.preimage_image_eq, Set.range_comp, TopCat, TopCat.coe_comp, coe_comp, comp_base, convert, g.isOpenEmbedding.injective, g.isOpenEmbedding.isOpenMap, injective, isDominant_iff, isOpenEmbedding, isOpenMap, preimage, preimage_image_eq, range_comp
-/
lemma IsDominant.of_comp_of_isOpenImmersion
    (f : X ⟶ Y) (g : Y ⟶ Z) [H : IsDominant (f ≫ g)] [IsOpenImmersion g] :
    IsDominant f := by
  rw [isDominant_iff]; rw [DenseRange] at H ⊢
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] at H
  convert H.preimage g.isOpenEmbedding.isOpenMap
  rw [Set.preimage_image_eq _ g.isOpenEmbedding.injective]

/--
lemma `Opens.isDominant_ι` / 引理 `Opens.isDominant_ι`

English:
lemma Opens.isDominant_ι
  given: {U : X.Opens} (hU : Dense (X := X) U)
  statement: IsDominant U.ι
  proof: ⟨by simpa [DenseRange] using hU⟩

中文:
引理 Opens.isDominant_ι
  条件: {U : X.Opens} (hU : Dense (X := X) U)
  结论: IsDominant U.ι
  证明: ⟨by simpa [DenseRange] using hU⟩

Depends on / 依赖: IsDominant
-/
lemma Opens.isDominant_ι {U : X.Opens} (hU : Dense (X := X) U) : IsDominant U.ι :=
  ⟨by simpa [DenseRange] using hU⟩

/--
lemma `Opens.isDominant_homOfLE` / 引理 `Opens.isDominant_homOfLE`

English:
lemma Opens.isDominant_homOfLE
  given: {U V : X.Opens} (hU : Dense (X := X) U) (hU' : U <= V)
  proof: have : IsDominant (X.homOfLE hU' ≫ V.ι) := by simpa using Opens.isDominant_ι hU
  IsDominant.of_comp_of_isOpenImmersion (g := V.ι) _

中文:
引理 Opens.isDominant_homOfLE
  条件: {U V : X.Opens} (hU : Dense (X := X) U) (hU' : U <= V)
  证明: have : IsDominant (X.homOfLE hU' ≫ V.ι) := by simpa using Opens.isDominant_ι hU
  IsDominant.of_comp_of_isOpenImmersion (g := V.ι) _
-/
lemma Opens.isDominant_homOfLE {U V : X.Opens} (hU : Dense (X := X) U) (hU' : U <= V) :
    IsDominant (X.homOfLE hU') :=
  have : IsDominant (X.homOfLE hU' ≫ V.ι) := by simpa using Opens.isDominant_ι hU
  IsDominant.of_comp_of_isOpenImmersion (g := V.ι) _

end IsDominant

section SpecializingMap

open TopologicalSpace

/--
Instance `specializingMap_respectsIso` / 实例 `specializingMap_respectsIso`

English:
instance specializingMap_respectsIso
  signature: : (topologically @SpecializingMap).RespectsIso
  body: by
  apply topologically_respectsIso
  · introv
    exact f.isClosedMap.specializingMap
  · introv hf hg
    exact hf.comp hg

中文:
实例 specializingMap_respectsIso
  签名: : (topologically @SpecializingMap).RespectsIso
  定义体: by
  apply topologically_respectsIso
  · introv
    exact f.isClosedMap.specializingMap
  · introv hf hg
    exact hf.comp hg

Depends on / 依赖: f.isClosedMap.specializingMap, hf.comp, introv, isClosedMap, specializingMap, topologically_respectsIso
-/
instance specializingMap_respectsIso : (topologically @SpecializingMap).RespectsIso := by
  apply topologically_respectsIso
  · introv
    exact f.isClosedMap.specializingMap
  · introv hf hg
    exact hf.comp hg

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `specializingMap_isZariskiLocalAtTarget` / 实例 `specializingMap_isZariskiLocalAtTarget`

English:
instance specializingMap_isZariskiLocalAtTarget
  signature: :
  body: by
  apply topologically_isZariskiLocalAtTarget
  · introv _ _ hf
    rw [specializingMap_iff_closure_singleton_subset] at hf ⊢
    intro ⟨x, hx⟩ ⟨y, hy⟩ hcl
    simp only [closure_subtype, Set.restrictPreimage_mk, Set.image_singleton] at hcl
    obtain ⟨a, ha, hay⟩ := hf x hcl
    rw [← specializes

中文:
实例 specializingMap_isZariskiLocalAtTarget
  签名: :
  定义体: by
  apply topologically_isZariskiLocalAtTarget
  · introv _ _ hf
    rw [specializingMap_iff_closure_singleton_subset] at hf ⊢
    intro ⟨x, hx⟩ ⟨y, hy⟩ hcl
    simp only [closure_subtype, Set.restrictPreimage_mk, Set.image_singleton] at hcl
    obtain ⟨a, ha, hay⟩ := hf x hcl
    rw [← specializes

Depends on / 依赖: Set.image_singleton, Set.restrictPreimage_mk, closure_subtype, image_singleton, introv, restrictPreimage_mk, simp_rw, specializes_iff_mem_closure, specializingMap_iff_closure_singleton_subset, topologically_isZariskiLocalAtTarget
-/
instance specializingMap_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically @SpecializingMap) := by
  apply topologically_isZariskiLocalAtTarget
  · introv _ _ hf
    rw [specializingMap_iff_closure_singleton_subset] at hf ⊢
    intro ⟨x, hx⟩ ⟨y, hy⟩ hcl
    simp only [closure_subtype, Set.restrictPreimage_mk, Set.image_singleton] at hcl
    obtain ⟨a, ha, hay⟩ := hf x hcl
    rw [← specializes_iff_mem_closure] at hcl
    exact ⟨⟨a, by simp [hay, hy]⟩, by simpa [closure_subtype], by simpa⟩
  · introv hU _ hsp
    simp_rw [specializingMap_iff_closure_singleton_subset] at hsp ⊢
    intro x y hy
    have : exists i, y in U i := Opens.mem_iSup.mp (hU ▸ Opens.mem_top _)
    obtain ⟨i, hi⟩ := this
    rw [← specializes_iff_mem_closure] at hy
    have hfx : f x in U i := (U i).2.stableUnderGeneralization hy hi
    have hy : (⟨y, hi⟩ : U i) in closure {⟨f x, hfx⟩} := by
      simp only [closure_subtype, Set.image_singleton]
      rwa [← specializes_iff_mem_closure]
    obtain ⟨a, ha, hay⟩ := hsp i ⟨x, hfx⟩ hy
    rw [closure_subtype] at ha
    simp only [Opens.carrier_eq_coe, Set.image_singleton] at ha
    apply_fun Subtype.val at hay
    simp only [Opens.carrier_eq_coe, Set.restrictPreimage_coe] at hay
    use a.val, ha, hay

end SpecializingMap

section GeneralizingMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (topologically GeneralizingMap).RespectsIso
  body: topologically_respectsIso _ (fun f => f.isOpenEmbedding.generalizingMap)
    (fun _ _ hf hg => hf.comp hg)

中文:
实例 :
  签名: (topologically GeneralizingMap).RespectsIso
  定义体: topologically_respectsIso _ (fun f => f.isOpenEmbedding.generalizingMap)
    (fun _ _ hf hg => hf.comp hg)

Depends on / 依赖: f.isOpenEmbedding.generalizingMap, generalizingMap, hf.comp, isOpenEmbedding, topologically_respectsIso
-/
instance : (topologically GeneralizingMap).RespectsIso :=
  topologically_respectsIso _ (fun f => f.isOpenEmbedding.generalizingMap)
    (fun _ _ hf hg => hf.comp hg)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtSource (topologically GeneralizingMap)
  body: topologically_isZariskiLocalAtSource' (fun _ => _) fun _ _ _ hU _ => hU.generalizingMap_iff_comp

中文:
实例 :
  签名: IsZariskiLocalAtSource (topologically GeneralizingMap)
  定义体: topologically_isZariskiLocalAtSource' (fun _ => _) fun _ _ _ hU _ => hU.generalizingMap_iff_comp

Depends on / 依赖: generalizingMap_iff_comp, hU.generalizingMap_iff_comp, topologically_isZariskiLocalAtSource
-/
instance : IsZariskiLocalAtSource (topologically GeneralizingMap) :=
  topologically_isZariskiLocalAtSource' (fun _ => _) fun _ _ _ hU _ => hU.generalizingMap_iff_comp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtTarget (topologically GeneralizingMap)
  body: topologically_isZariskiLocalAtTarget' (fun _ => _) fun _ _ _ hU _ =>
    hU.generalizingMap_iff_restrictPreimage

中文:
实例 :
  签名: IsZariskiLocalAtTarget (topologically GeneralizingMap)
  定义体: topologically_isZariskiLocalAtTarget' (fun _ => _) fun _ _ _ hU _ =>
    hU.generalizingMap_iff_restrictPreimage

Depends on / 依赖: generalizingMap_iff_restrictPreimage, hU.generalizingMap_iff_restrictPreimage, topologically_isZariskiLocalAtTarget
-/
instance : IsZariskiLocalAtTarget (topologically GeneralizingMap) :=
  topologically_isZariskiLocalAtTarget' (fun _ => _) fun _ _ _ hU _ =>
    hU.generalizingMap_iff_restrictPreimage

end GeneralizingMap

end AlgebraicGeometry
