/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Preorder

/-!
# Open immersions of schemes

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


noncomputable section

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

/--
Definition of `IsOpenImmersion` / `IsOpenImmersion` 的定义

English:
abbreviation IsOpenImmersion
  signature: : MorphismProperty (Scheme.{u})
  body: fun _ _ f => LocallyRingedSpace.IsOpenImmersion f.toLRSHom

中文:
缩写 是开浸入
  签名: : MorphismProperty (概形.{u})
  定义体: fun _ _ f => LocallyRingedSpace.IsOpenImmersion f.toLRSHom

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion, f.toLRSHom, toLRSHom
-/
abbrev IsOpenImmersion : MorphismProperty (Scheme.{u}) :=
  fun _ _ f => LocallyRingedSpace.IsOpenImmersion f.toLRSHom

/--
Instance `IsOpenImmersion.comp` / 实例 `IsOpenImmersion.comp`

English:
instance IsOpenImmersion.comp
  signature: {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  body: LocallyRingedSpace.IsOpenImmersion.comp f.toLRSHom g.toLRSHom

中文:
实例 是开浸入.comp
  签名: {X Y Z : 概形.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  定义体: LocallyRingedSpace.IsOpenImmersion.comp f.toLRSHom g.toLRSHom

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion.comp, f.toLRSHom, g.toLRSHom, toLRSHom
-/
instance IsOpenImmersion.comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] : IsOpenImmersion (f ≫ g) :=
  LocallyRingedSpace.IsOpenImmersion.comp f.toLRSHom g.toLRSHom

namespace LocallyRingedSpace.IsOpenImmersion

/--
Definition of `scheme` / `scheme` 的定义

English:
definition scheme
  signature: (X : LocallyRingedSpace.{u})
  body: X
  local_affine := by
    intro x
    obtain ⟨R, f, h₁, h₂⟩ := h x
    refine ⟨⟨⟨_, h₂.base_open.isOpen_range⟩, h₁⟩, R, ⟨?_⟩⟩
    apply LocallyRingedSpace.isoOfSheafedSpaceIso
    refine SheafedSpace.forgetToPresheafedSpace.preimageIso ?_
    apply PresheafedSpace.IsOpenImmersion.isoOfRangeEq (Pres

中文:
定义 scheme
  签名: (X : LocallyRinged空间.{u})
  定义体: X
  local_affine := by
    intro x
    obtain ⟨R, f, h₁, h₂⟩ := h x
    refine ⟨⟨⟨_, h₂.base_open.isOpen_range⟩, h₁⟩, R, ⟨?_⟩⟩
    apply LocallyRingedSpace.isoOfSheafedSpaceIso
    refine SheafedSpace.forgetToPresheafedSpace.preimageIso ?_
    apply PresheafedSpace.IsOpenImmersion.isoOfRangeEq (Pres
-/
protected def scheme (X : LocallyRingedSpace.{u})
    (h :
      forall x : X,
        exists (R : CommRingCat) (f : Spec.toLocallyRingedSpace.obj (op R) ⟶ X),
          (x in Set.range f.base :) ∧ LocallyRingedSpace.IsOpenImmersion f) :
    Scheme where
  toLocallyRingedSpace := X
  local_affine := by
    intro x
    obtain ⟨R, f, h₁, h₂⟩ := h x
    refine ⟨⟨⟨_, h₂.base_open.isOpen_range⟩, h₁⟩, R, ⟨?_⟩⟩
    apply LocallyRingedSpace.isoOfSheafedSpaceIso
    refine SheafedSpace.forgetToPresheafedSpace.preimageIso ?_
    apply PresheafedSpace.IsOpenImmersion.isoOfRangeEq (PresheafedSpace.ofRestrict _ _) f.1
    exact Subtype.range_coe_subtype

end LocallyRingedSpace.IsOpenImmersion

/--
theorem `IsOpenImmersion.isOpen_range` / 定理 `IsOpenImmersion.isOpen_range`

English:
theorem IsOpenImmersion.isOpen_range
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f]
  proof: H.base_open.isOpen_range

中文:
定理 是开浸入.isOpen_range
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) [H : 是开浸入 f]
  证明: H.base_open.isOpen_range

Depends on / 依赖: H.base_open.isOpen_range, base_open, isOpen_range
-/
theorem IsOpenImmersion.isOpen_range {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsOpen (Set.range f) :=
  H.base_open.isOpen_range

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f]

/--
theorem `isOpenEmbedding` / 定理 `isOpenEmbedding`

English:
theorem isOpenEmbedding
  statement: IsOpenEmbedding f
  proof: H.base_open

中文:
定理 isOpenEmbedding
  结论: 是开嵌入 f
  证明: H.base_open

Depends on / 依赖: H.base_open, base_open
-/
theorem isOpenEmbedding : IsOpenEmbedding f :=
  H.base_open

/-- The image of an open immersion as an open set. -/
@[simps]
/--
Definition of `opensRange` / `opensRange` 的定义

English:
definition opensRange
  signature: : Y.Opens
  body: ⟨_, f.isOpenEmbedding.isOpen_range⟩

@[simp]

中文:
定义 opensRange
  签名: : Y.Opens
  定义体: ⟨_, f.isOpenEmbedding.isOpen_range⟩

@[simp]

Depends on / 依赖: f.isOpenEmbedding.isOpen_range, isOpenEmbedding, isOpen_range
-/
def opensRange : Y.Opens :=
  ⟨_, f.isOpenEmbedding.isOpen_range⟩

@[simp]
/--
theorem `mem_opensRange` / 定理 `mem_opensRange`

English:
theorem mem_opensRange
  given: {f : X ⟶ Y} [IsOpenImmersion f] {y : Y}
  proof: .rfl

中文:
定理 mem_opensRange
  条件: {f : X ⟶ Y} [是开浸入 f] {y : Y}
  证明: .rfl
-/
theorem mem_opensRange {f : X ⟶ Y} [IsOpenImmersion f] {y : Y} :
    y in opensRange f ↔ exists x, f x = y := .rfl

/--
Definition of `opensFunctor` / `opensFunctor` 的定义

English:
definition opensFunctor
  signature: : X.Opens ⥤ Y.Opens
  body: LocallyRingedSpace.IsOpenImmersion.opensFunctor f.toLRSHom

中文:
定义 opensFunctor
  签名: : X.Opens ⥤ Y.Opens
  定义体: LocallyRingedSpace.IsOpenImmersion.opensFunctor f.toLRSHom

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion.opensFunctor, f.toLRSHom, opensFunctor, toLRSHom
-/
def opensFunctor : X.Opens ⥤ Y.Opens :=
  LocallyRingedSpace.IsOpenImmersion.opensFunctor f.toLRSHom

/--
Definition of `opensFunctorAdjunction` / `opensFunctorAdjunction` 的定义

English:
definition opensFunctorAdjunction
  signature: : f.opensFunctor ⊣ TopologicalSpace.Opens.map f.base
  body: IsOpenMap.adjunction ‹IsOpenImmersion f›.base_open.isOpenMap

中文:
定义 opensFunctorAdjunction
  签名: : f.opensFunctor ⊣ 拓扑空间.Opens.map f.base
  定义体: IsOpenMap.adjunction ‹IsOpenImmersion f›.base_open.isOpenMap

Depends on / 依赖: IsOpenImmersion, IsOpenMap, IsOpenMap.adjunction, adjunction, base_open, base_open.isOpenMap, isOpenMap
-/
def opensFunctorAdjunction : f.opensFunctor ⊣ TopologicalSpace.Opens.map f.base :=
  IsOpenMap.adjunction ‹IsOpenImmersion f›.base_open.isOpenMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: f.opensFunctor.IsLeftAdjoint
  body: f.opensFunctorAdjunction.isLeftAdjoint

中文:
实例 :
  签名: f.opensFunctor.是左伴随
  定义体: f.opensFunctorAdjunction.isLeftAdjoint

Depends on / 依赖: f.opensFunctorAdjunction.isLeftAdjoint, isLeftAdjoint, opensFunctorAdjunction
-/
instance : f.opensFunctor.IsLeftAdjoint :=
  f.opensFunctorAdjunction.isLeftAdjoint

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: f.opensFunctor.IsCocontinuous (Opens.grothendieckTopology _)
  body: by
  rw [f.opensFunctorAdjunction.isCocontinuous_iff_coverPreserving]
  exact coverPreserving_opens_map f.base

中文:
实例 :
  签名: f.opensFunctor.是余continuous (Opens.grothendieckTopology _)
  定义体: by
  rw [f.opensFunctorAdjunction.isCocontinuous_iff_coverPreserving]
  exact coverPreserving_opens_map f.base

Depends on / 依赖: coverPreserving_opens_map, f.base, f.opensFunctorAdjunction.isCocontinuous_iff_coverPreserving, isCocontinuous_iff_coverPreserving, opensFunctorAdjunction
-/
instance : f.opensFunctor.IsCocontinuous (Opens.grothendieckTopology _)
    (Opens.grothendieckTopology _) := by
  rw [f.opensFunctorAdjunction.isCocontinuous_iff_coverPreserving]
  exact coverPreserving_opens_map f.base

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: f.opensFunctor.Full
  body: have : Mono f.base := (TopCat.mono_iff_injective f.base).mpr f.isOpenEmbedding.injective
  inferInstanceAs f.isOpenEmbedding.functor.Full

中文:
实例 :
  签名: f.opensFunctor.满
  定义体: have : Mono f.base := (TopCat.mono_iff_injective f.base).mpr f.isOpenEmbedding.injective
  inferInstanceAs f.isOpenEmbedding.functor.Full

Depends on / 依赖: TopCat, TopCat.mono_iff_injective, f.base, f.isOpenEmbedding.functor.Full, f.isOpenEmbedding.injective, functor, injective, isOpenEmbedding, mono_iff_injective
-/
instance : f.opensFunctor.Full :=
  have : Mono f.base := (TopCat.mono_iff_injective f.base).mpr f.isOpenEmbedding.injective
  inferInstanceAs f.isOpenEmbedding.functor.Full

/--
lemma `coverPreserving_opensFunctor` / 引理 `coverPreserving_opensFunctor`

English:
lemma coverPreserving_opensFunctor
  proof: f.isOpenEmbedding.isOpenMap.coverPreserving

中文:
引理 coverPreserving_opensFunctor
  证明: f.isOpenEmbedding.isOpenMap.coverPreserving

Depends on / 依赖: Set.mem_univ, Set.top_eq_univ, SimplexCategory, SimplexCategory.len_le_of_mono, coverPreserving, f.isOpenEmbedding.isOpenMap.coverPreserving, iff_true, isOpenEmbedding, isOpenMap, len_le_of_mono, mem_nonDegenerate_iff_mono, mem_univ, objEquiv, top_eq_univ
-/
lemma coverPreserving_opensFunctor :
    CoverPreserving (Opens.grothendieckTopology _) (Opens.grothendieckTopology _) f.opensFunctor :=
  f.isOpenEmbedding.isOpenMap.coverPreserving

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesLimitsOfShape WalkingCospan (Scheme.Hom.opensFunctor f) := by
  dsimp [Scheme.Hom.opensFunctor]
  infer_instance

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f.opensFunctor.PreservesOneHypercovers (Opens.grothendieckTopology _)
      (Opens.grothendieckTopology _) := by
  refine Functor.PreservesOneHypercovers.of_coverPreserving ?_
  exact Scheme.Hom.coverPreserving_opensFunctor f

/-- `f ''ᵁ U` is notation for the image (as an open set) of `U` under an open immersion `f`.
The preferred name in lemmas is `image` and it should be treated as an infix. -/
scoped[AlgebraicGeometry] notation3:90 f:91 " ''ᵁ " U:90 => (Scheme.Hom.opensFunctor f).obj U

/--
lemma `coe_image` / 引理 `coe_image`

English:
lemma coe_image
  given: {U : X.Opens}
  statement: f ''ᵁ U = f '' U
  proof: rfl

中文:
引理 coe_image
  条件: {U : X.Opens}
  结论: f ''ᵁ U = f '' U
  证明: rfl
-/
@[simp] lemma coe_image {U : X.Opens} : f ''ᵁ U = f '' U := rfl

/--
lemma `image_mono` / 引理 `image_mono`

English:
lemma image_mono
  given: {U V : X.Opens} (e : U <= V)
  statement: f ''ᵁ U <= f ''ᵁ V
  proof: Set.image_mono e

@[simp]

中文:
引理 image_mono
  条件: {U V : X.Opens} (e : U <= V)
  结论: f ''ᵁ U <= f ''ᵁ V
  证明: Set.image_mono e

@[simp]

Depends on / 依赖: Set.image_mono, image_mono
-/
lemma image_mono {U V : X.Opens} (e : U <= V) : f ''ᵁ U <= f ''ᵁ V := Set.image_mono e

@[simp]
/--
lemma `opensFunctor_map_homOfLE` / 引理 `opensFunctor_map_homOfLE`

English:
lemma opensFunctor_map_homOfLE
  given: {U V : X.Opens} (e : U <= V)
  proof: rfl

中文:
引理 opensFunctor_map_homOfLE
  条件: {U V : X.Opens} (e : U <= V)
  证明: rfl
-/
lemma opensFunctor_map_homOfLE {U V : X.Opens} (e : U <= V) :
    (Scheme.Hom.opensFunctor f).map (homOfLE e) = homOfLE (f.image_mono e) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: f.opensFunctor.IsContinuous
  body: f.isOpenEmbedding.functor_isContinuous

@[simp]

中文:
实例 :
  签名: f.opensFunctor.是连续
  定义体: f.isOpenEmbedding.functor_isContinuous

@[simp]

Depends on / 依赖: f.isOpenEmbedding.functor_isContinuous, functor_isContinuous, isOpenEmbedding
-/
instance : f.opensFunctor.IsContinuous
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
  f.isOpenEmbedding.functor_isContinuous

@[simp]
/--
lemma `image_top_eq_opensRange` / 引理 `image_top_eq_opensRange`

English:
lemma image_top_eq_opensRange
  statement: f ''ᵁ ⊤ = f.opensRange
  proof: by
  apply Opens.ext
  simp

中文:
引理 image_top_eq_opensRange
  结论: f ''ᵁ ⊤ = f.opensRange
  证明: by
  apply Opens.ext
  simp

Depends on / 依赖: Opens.ext
-/
lemma image_top_eq_opensRange : f ''ᵁ ⊤ = f.opensRange := by
  apply Opens.ext
  simp

/--
lemma `opensRange_comp` / 引理 `opensRange_comp`

English:
lemma opensRange_comp
  statement: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: TopologicalSpace.Opens.ext (Set.range_comp g f)

中文:
引理 opensRange_comp
  结论: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: TopologicalSpace.Opens.ext (Set.range_comp g f)

Depends on / 依赖: Set.range_comp, TopologicalSpace, TopologicalSpace.Opens.ext, range_comp
-/
lemma opensRange_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] : (f ≫ g).opensRange = g ''ᵁ f.opensRange :=
  TopologicalSpace.Opens.ext (Set.range_comp g f)

/--
lemma `opensRange_of_isIso` / 引理 `opensRange_of_isIso`

English:
lemma opensRange_of_isIso
  given: {X Y : Scheme} (f : X ⟶ Y) [IsIso f]
  proof: TopologicalSpace.Opens.ext (Set.range_eq_univ.mpr f.homeomorph.surjective)

中文:
引理 opensRange_of_isIso
  条件: {X Y : 概形} (f : X ⟶ Y) [是同构 f]
  证明: TopologicalSpace.Opens.ext (Set.range_eq_univ.mpr f.homeomorph.surjective)

Depends on / 依赖: Set.range_eq_univ.mpr, TopologicalSpace, TopologicalSpace.Opens.ext, f.homeomorph.surjective, homeomorph, range_eq_univ, surjective
-/
lemma opensRange_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    f.opensRange = ⊤ :=
  TopologicalSpace.Opens.ext (Set.range_eq_univ.mpr f.homeomorph.surjective)

/--
lemma `opensRange_comp_of_isIso` / 引理 `opensRange_comp_of_isIso`

English:
lemma opensRange_comp_of_isIso
  statement: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  rw [opensRange_comp]; rw [opensRange_of_isIso]; rw [image_top_eq_opensRange]

中文:
引理 opensRange_comp_of_isIso
  结论: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  rw [opensRange_comp]; rw [opensRange_of_isIso]; rw [image_top_eq_opensRange]

Depends on / 依赖: image_top_eq_opensRange, opensRange_comp, opensRange_of_isIso
-/
lemma opensRange_comp_of_isIso {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIso f] [IsOpenImmersion g] : (f ≫ g).opensRange = g.opensRange := by
  rw [opensRange_comp]; rw [opensRange_of_isIso]; rw [image_top_eq_opensRange]

/--
lemma `image_le_opensRange` / 引理 `image_le_opensRange`

English:
lemma image_le_opensRange
  given: (U : X.Opens)
  statement: f ''ᵁ U <= f.opensRange
  proof: by
  simpa using f.image_mono le_top

@[simp]

中文:
引理 image_le_opensRange
  条件: (U : X.Opens)
  结论: f ''ᵁ U <= f.opensRange
  证明: by
  simpa using f.image_mono le_top

@[simp]

Depends on / 依赖: f.image_mono, image_mono, le_top
-/
lemma image_le_opensRange (U : X.Opens) : f ''ᵁ U <= f.opensRange := by
  simpa using f.image_mono le_top

@[simp]
/--
lemma `preimage_image_eq` / 引理 `preimage_image_eq`

English:
lemma preimage_image_eq
  given: (U : X.Opens)
  statement: f ⁻¹ᵁ f ''ᵁ U = U
  proof: by
  apply Opens.ext
  simp [Set.preimage_image_eq _ f.isOpenEmbedding.injective]

中文:
引理 preimage_image_eq
  条件: (U : X.Opens)
  结论: f ⁻¹ᵁ f ''ᵁ U = U
  证明: by
  apply Opens.ext
  simp [Set.preimage_image_eq _ f.isOpenEmbedding.injective]

Depends on / 依赖: Opens.ext, Set.preimage_image_eq, f.isOpenEmbedding.injective, injective, isOpenEmbedding, preimage_image_eq
-/
lemma preimage_image_eq (U : X.Opens) : f ⁻¹ᵁ f ''ᵁ U = U := by
  apply Opens.ext
  simp [Set.preimage_image_eq _ f.isOpenEmbedding.injective]

/--
lemma `image_le_image_iff` / 引理 `image_le_image_iff`

English:
lemma image_le_image_iff
  given: (f : X ⟶ Y) [IsOpenImmersion f] (U U' : X.Opens)
  proof: by
  refine ⟨fun h => ?_, f.image_mono⟩
  rw [← preimage_image_eq f U]; rw [← preimage_image_eq f U']
  apply f.preimage_mono h

中文:
引理 image_le_image_iff
  条件: (f : X ⟶ Y) [是开浸入 f] (U U' : X.Opens)
  证明: by
  refine ⟨fun h => ?_, f.image_mono⟩
  rw [← preimage_image_eq f U]; rw [← preimage_image_eq f U']
  apply f.preimage_mono h

Depends on / 依赖: f.image_mono, f.preimage_mono, image_mono, preimage_image_eq, preimage_mono
-/
lemma image_le_image_iff (f : X ⟶ Y) [IsOpenImmersion f] (U U' : X.Opens) :
    f ''ᵁ U <= f ''ᵁ U' ↔ U <= U' := by
  refine ⟨fun h => ?_, f.image_mono⟩
  rw [← preimage_image_eq f U]; rw [← preimage_image_eq f U']
  apply f.preimage_mono h

/--
lemma `image_preimage_eq_opensRange_inf` / 引理 `image_preimage_eq_opensRange_inf`

English:
lemma image_preimage_eq_opensRange_inf
  given: (U : Y.Opens)
  statement: f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U
  proof: by
  apply Opens.ext
  simp [Set.image_preimage_eq_range_inter]

中文:
引理 image_preimage_eq_opensRange_inf
  条件: (U : Y.Opens)
  结论: f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U
  证明: by
  apply Opens.ext
  simp [Set.image_preimage_eq_range_inter]

Depends on / 依赖: Opens.ext, Set.image_preimage_eq_range_inter, image_preimage_eq_range_inter
-/
lemma image_preimage_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U := by
  apply Opens.ext
  simp [Set.image_preimage_eq_range_inter]

/--
lemma `image_preimage_le` / 引理 `image_preimage_le`

English:
lemma image_preimage_le
  given: (U : Y.Opens)
  statement: f ''ᵁ f ⁻¹ᵁ U <= U
  proof: (f.image_preimage_eq_opensRange_inf U).trans_le inf_le_right

中文:
引理 image_preimage_le
  条件: (U : Y.Opens)
  结论: f ''ᵁ f ⁻¹ᵁ U <= U
  证明: (f.image_preimage_eq_opensRange_inf U).trans_le inf_le_right

Depends on / 依赖: f.image_preimage_eq_opensRange_inf, image_preimage_eq_opensRange_inf, inf_le_right, trans_le
-/
lemma image_preimage_le (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U <= U :=
  (f.image_preimage_eq_opensRange_inf U).trans_le inf_le_right

/--
lemma `image_injective` / 引理 `image_injective`

English:
lemma image_injective
  statement: Function.Injective (f ''ᵁ ·)
  proof: by
  intro U V hUV
  simpa using congrArg (f ⁻¹ᵁ ·) hUV

中文:
引理 image_injective
  结论: 函数.单射 (f ''ᵁ ·)
  证明: by
  intro U V hUV
  simpa using congrArg (f ⁻¹ᵁ ·) hUV
-/
lemma image_injective : Function.Injective (f ''ᵁ ·) := by
  intro U V hUV
  simpa using congrArg (f ⁻¹ᵁ ·) hUV

/--
lemma `image_iSup` / 引理 `image_iSup`

English:
lemma image_iSup
  given: {ι : Sort*} (s : ι -> X.Opens)
  proof: by
  ext : 1
  simp [Set.image_iUnion]

中文:
引理 image_iSup
  条件: {ι : 类型层*} (s : ι -> X.Opens)
  证明: by
  ext : 1
  simp [Set.image_iUnion]

Depends on / 依赖: Set.image_iUnion, image_iUnion
-/
lemma image_iSup {ι : Sort*} (s : ι -> X.Opens) :
    (f ''ᵁ ⨆ (i : ι), s i) = ⨆ (i : ι), f ''ᵁ s i := by
  ext : 1
  simp [Set.image_iUnion]

/--
lemma `image_iSup₂` / 引理 `image_iSup₂`

English:
lemma image_iSup₂
  given: {ι : Sort*} {κ : ι -> Sort*} (s : (i : ι) -> κ i -> X.Opens)
  proof: by
  ext : 1
  simp [Set.image_iUnion₂]

@[simp]

中文:
引理 image_iSup₂
  条件: {ι : 类型层*} {κ : ι -> 类型层*} (s : (i : ι) -> κ i -> X.Opens)
  证明: by
  ext : 1
  simp [Set.image_iUnion₂]

@[simp]

Depends on / 依赖: Set.image_iUnion
-/
lemma image_iSup₂ {ι : Sort*} {κ : ι -> Sort*} (s : (i : ι) -> κ i -> X.Opens) :
    (f ''ᵁ ⨆ (i : ι), ⨆ (j : κ i), s i j) = ⨆ (i : ι), ⨆ (j : κ i), f ''ᵁ s i j := by
  ext : 1
  simp [Set.image_iUnion₂]

@[simp]
/--
lemma `comp_image` / 引理 `comp_image`

English:
lemma comp_image
  statement: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U : X.Opens)
  proof: TopologicalSpace.Opens.ext (Set.image_comp g f U)

@[simp]

中文:
引理 comp_image
  结论: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z) (U : X.Opens)
  证明: TopologicalSpace.Opens.ext (Set.image_comp g f U)

@[simp]

Depends on / 依赖: Set.image_comp, TopologicalSpace, TopologicalSpace.Opens.ext, image_comp
-/
lemma comp_image {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U : X.Opens)
    [IsOpenImmersion f] [IsOpenImmersion g] : (f ≫ g) ''ᵁ U = g ''ᵁ f ''ᵁ U :=
  TopologicalSpace.Opens.ext (Set.image_comp g f U)

@[simp]
/--
lemma `id_image` / 引理 `id_image`

English:
lemma id_image
  given: {X : Scheme} (U : X.Opens)
  statement: 𝟙 X ''ᵁ U = U
  proof: TopologicalSpace.Opens.ext (Set.image_id _)

@[simp]

中文:
引理 id_image
  条件: {X : 概形} (U : X.Opens)
  结论: 𝟙 X ''ᵁ U = U
  证明: TopologicalSpace.Opens.ext (Set.image_id _)

@[simp]

Depends on / 依赖: Equiv.ofBijective_symm_apply_apply, Finset, Finset.mem_image, Finset.mem_univ, Set.image_id, TopologicalSpace, TopologicalSpace.Opens.ext, image_id, mem_image, mem_univ, nonDegenerateEquiv, ofBijective_symm_apply_apply, surjective, true_and
-/
lemma id_image {X : Scheme} (U : X.Opens) : 𝟙 X ''ᵁ U = U :=
  TopologicalSpace.Opens.ext (Set.image_id _)

@[simp]
/--
lemma `inv_image` / 引理 `inv_image`

English:
lemma inv_image
  given: {X Y : Scheme} (e : X ≅ Y) (U : Y.Opens)
  statement: e.inv ''ᵁ U = e.hom ⁻¹ᵁ U
  proof: TopologicalSpace.Opens.ext (Scheme.homeoOfIso e.symm).toEquiv.image_eq_preimage_symm _

中文:
引理 inv_image
  条件: {X Y : 概形} (e : X ≅ Y) (U : Y.Opens)
  结论: e.inv ''ᵁ U = e.hom ⁻¹ᵁ U
  证明: TopologicalSpace.Opens.ext (Scheme.homeoOfIso e.symm).toEquiv.image_eq_preimage_symm _

Depends on / 依赖: Equiv.symm_apply_apply, Scheme, Scheme.homeoOfIso, Subcomplex, Subcomplex.ofSimplex_le_iff, TopologicalSpace, TopologicalSpace.Opens.ext, e.symm, face_nonDegenerateEquiv, homeoOfIso, image_eq_preimage_symm, nonDegenerateEquiv, ofSimplex_le_iff, surjective, symm_apply_apply, toEquiv, toEquiv.image_eq_preimage_symm
-/
lemma inv_image {X Y : Scheme} (e : X ≅ Y) (U : Y.Opens) : e.inv ''ᵁ U = e.hom ⁻¹ᵁ U :=
TopologicalSpace.Opens.ext (Scheme.homeoOfIso e.symm).toEquiv.image_eq_preimage_symm _

/--
lemma `inv_preimage` / 引理 `inv_preimage`

English:
lemma inv_preimage
  given: {X Y : Scheme} (e : X ≅ Y) (U : X.Opens)
  statement: e.inv ⁻¹ᵁ U = e.hom ''ᵁ U
  proof: (inv_image e.symm U).symm

@[simp]

中文:
引理 inv_preimage
  条件: {X Y : 概形} (e : X ≅ Y) (U : X.Opens)
  结论: e.inv ⁻¹ᵁ U = e.hom ''ᵁ U
  证明: (inv_image e.symm U).symm

@[simp]

Depends on / 依赖: e.symm, finite_iff, infer_instance, inv_image, objEquiv, objEquiv.finite_iff
-/
lemma inv_preimage {X Y : Scheme} (e : X ≅ Y) (U : X.Opens) : e.inv ⁻¹ᵁ U = e.hom ''ᵁ U :=
  (inv_image e.symm U).symm

@[simp]
/--
lemma `apply_mem_image_iff` / 引理 `apply_mem_image_iff`

English:
lemma apply_mem_image_iff
  statement: {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
  proof: f.isOpenEmbedding.injective.mem_set_image

@[simp]

中文:
引理 apply_mem_image_iff
  结论: {X Y : 概形} (f : X ⟶ Y) [是开浸入 f]
  证明: f.isOpenEmbedding.injective.mem_set_image

@[simp]

Depends on / 依赖: SimplexCategory, SimplexCategory.rec, f.isOpenEmbedding.injective.mem_set_image, finite_of_hasDimensionLT, injective, isOpenEmbedding, mem_set_image
-/
lemma apply_mem_image_iff {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    {U : X.Opens} {x : X} : f x in f ''ᵁ U ↔ x in U :=
  f.isOpenEmbedding.injective.mem_set_image

@[simp]
/--
lemma `preimage_opensRange` / 引理 `preimage_opensRange`

English:
lemma preimage_opensRange
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
  proof: by
  simp [Scheme.Hom.opensRange]

中文:
引理 preimage_opensRange
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) [是开浸入 f]
  证明: by
  simp [Scheme.Hom.opensRange]

Depends on / 依赖: Scheme, Scheme.Hom.opensRange, Subcomplex, Subcomplex.range_eq_ofSimplex, infer_instance, opensRange, range_eq_ofSimplex, surjective, yonedaEquiv, yonedaEquiv.surjective
-/
lemma preimage_opensRange {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f ⁻¹ᵁ f.opensRange = ⊤ := by
  simp [Scheme.Hom.opensRange]

set_option backward.isDefEq.respectTransparency false in
instance (U : X.Opens) : IsIso (f.app (f ''ᵁ U)) := by delta opensFunctor; infer_instance

/--
lemma `isIso_app` / 引理 `isIso_app`

English:
lemma isIso_app
  given: (V : Y.Opens) (hV : V <= f.opensRange)
  statement: IsIso (f.app V)
  proof: by
  rw [show V = f ''ᵁ f ⁻¹ᵁ V from Opens.ext (Set.image_preimage_eq_of_subset hV).symm]
  infer_instance

中文:
引理 isIso_app
  条件: (V : Y.Opens) (hV : V <= f.opensRange)
  结论: 是同构 (f.app V)
  证明: by
  rw [show V = f ''ᵁ f ⁻¹ᵁ V from Opens.ext (Set.image_preimage_eq_of_subset hV).symm]
  infer_instance

Depends on / 依赖: Opens.ext, Set.image_preimage_eq_of_subset, image_preimage_eq_of_subset, infer_instance
-/
lemma isIso_app (V : Y.Opens) (hV : V <= f.opensRange) : IsIso (f.app V) := by
  rw [show V = f ''ᵁ f ⁻¹ᵁ V from Opens.ext (Set.image_preimage_eq_of_subset hV).symm]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `appIso` / `appIso` 的定义

English:
definition appIso
  signature: (U)
  body: (asIso <| LocallyRingedSpace.IsOpenImmersion.invApp f.toLRSHom U).symm

中文:
定义 appIso
  签名: (U)
  定义体: (asIso <| LocallyRingedSpace.IsOpenImmersion.invApp f.toLRSHom U).symm

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion.invApp, f.toLRSHom, invApp, toLRSHom
-/
def appIso (U) : Γ(Y, f ''ᵁ U) ≅ Γ(X, U) :=
  (asIso <| LocallyRingedSpace.IsOpenImmersion.invApp f.toLRSHom U).symm

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `appIso_inv_naturality` / 定理 `appIso_inv_naturality`

English:
theorem appIso_inv_naturality
  given: {U V : X.Opens} (i : op U ⟶ op V)
  proof: PresheafedSpace.IsOpenImmersion.inv_naturality _ _

中文:
定理 appIso_inv_naturality
  条件: {U V : X.Opens} (i : op U ⟶ op V)
  证明: PresheafedSpace.IsOpenImmersion.inv_naturality _ _

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.inv_naturality, inv_naturality
-/
theorem appIso_inv_naturality {U V : X.Opens} (i : op U ⟶ op V) :
    X.presheaf.map i ≫ (f.appIso V).inv =
      (f.appIso U).inv ≫ Y.presheaf.map (f.opensFunctor.op.map i) :=
  PresheafedSpace.IsOpenImmersion.inv_naturality _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `appIso_hom` / 定理 `appIso_hom`

English:
theorem appIso_hom
  given: (U)
  proof: (PresheafedSpace.IsOpenImmersion.inv_invApp f.toPshHom U).trans (by rw [eqToHom_op]; rfl)

中文:
定理 appIso_hom
  条件: (U)
  证明: (PresheafedSpace.IsOpenImmersion.inv_invApp f.toPshHom U).trans (by rw [eqToHom_op]; rfl)

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.inv_invApp, eqToHom_op, f.toPshHom, inv_invApp, toPshHom
-/
theorem appIso_hom (U) :
    (f.appIso U).hom = f.app (f ''ᵁ U) ≫ X.presheaf.map
      (eqToHom (preimage_image_eq f U).symm).op :=
  (PresheafedSpace.IsOpenImmersion.inv_invApp f.toPshHom U).trans (by rw [eqToHom_op]; rfl)

/--
theorem `appIso_hom'` / 定理 `appIso_hom'`

English:
theorem appIso_hom'
  given: (U)
  proof: f.appIso_hom U

中文:
定理 appIso_hom'
  条件: (U)
  证明: f.appIso_hom U

Depends on / 依赖: appIso_hom, f.appIso_hom
-/
theorem appIso_hom' (U) :
    (f.appIso U).hom = f.appLE (f ''ᵁ U) U (preimage_image_eq f U).ge :=
  f.appIso_hom U

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `appIso_hom_naturality` / 引理 `appIso_hom_naturality`

English:
lemma appIso_hom_naturality
  given: {U V : X.Opens} (i : op U ⟶ op V)
  proof: by
  simp [← cancel_mono (f.appIso V).inv]

中文:
引理 appIso_hom_naturality
  条件: {U V : X.Opens} (i : op U ⟶ op V)
  证明: by
  simp [← cancel_mono (f.appIso V).inv]

Depends on / 依赖: appIso, cancel_mono, f.appIso
-/
lemma appIso_hom_naturality {U V : X.Opens} (i : op U ⟶ op V) :
    dsimp% Y.presheaf.map (f.opensFunctor.op.map i) ≫ (f.appIso V).hom =
      (f.appIso U).hom ≫ X.presheaf.map i := by
  simp [← cancel_mono (f.appIso V).inv]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `app_appIso_inv` / 定理 `app_appIso_inv`

English:
theorem app_appIso_inv
  given: (U)
  proof: PresheafedSpace.IsOpenImmersion.app_invApp _ _

中文:
定理 app_appIso_inv
  条件: (U)
  证明: PresheafedSpace.IsOpenImmersion.app_invApp _ _

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.app_invApp, app_invApp
-/
theorem app_appIso_inv (U) :
    f.app U ≫ (f.appIso (f ⁻¹ᵁ U)).inv =
      Y.presheaf.map (homOfLE (Set.image_preimage_subset f U.1)).op :=
  PresheafedSpace.IsOpenImmersion.app_invApp _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `app_invApp` that gives an `eqToHom` instead of `homOfLE`. -/
@[reassoc]
/--
theorem `app_invApp'` / 定理 `app_invApp'`

English:
theorem app_invApp'
  given: (U) (hU : U <= f.opensRange)
  proof: PresheafedSpace.IsOpenImmersion.app_invApp _ _

中文:
定理 app_invApp'
  条件: (U) (hU : U <= f.opensRange)
  证明: PresheafedSpace.IsOpenImmersion.app_invApp _ _

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.app_invApp, app_invApp
-/
theorem app_invApp' (U) (hU : U <= f.opensRange) :
    f.app U ≫ (f.appIso (f ⁻¹ᵁ U)).inv =
      Y.presheaf.map (eqToHom (Opens.ext <| by simpa [Set.image_preimage_eq_inter_range])).op :=
  PresheafedSpace.IsOpenImmersion.app_invApp _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise nosimp]
/--
theorem `appIso_inv_app` / 定理 `appIso_inv_app`

English:
theorem appIso_inv_app
  given: (U)
  proof: (PresheafedSpace.IsOpenImmersion.invApp_app _ _).trans (by rw [eqToHom_op])

中文:
定理 appIso_inv_app
  条件: (U)
  证明: (PresheafedSpace.IsOpenImmersion.invApp_app _ _).trans (by rw [eqToHom_op])

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.invApp_app, eqToHom_op, invApp_app
-/
theorem appIso_inv_app (U) :
    (f.appIso U).inv ≫ f.app (f ''ᵁ U) = X.presheaf.map (eqToHom (preimage_image_eq f U)).op :=
  (PresheafedSpace.IsOpenImmersion.invApp_app _ _).trans (by rw [eqToHom_op])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp), elementwise nosimp]
/--
lemma `appLE_appIso_inv` / 引理 `appLE_appIso_inv`

English:
lemma appLE_appIso_inv
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {U : Y.Opens}
  proof: by
  simp only [appLE, Category.assoc, appIso_inv_naturality, Functor.op_obj, Functor.op_map,
    Quiver.Hom.unop_op, opensFunctor_map_homOfLE, app_appIso_inv_assoc, Opens.carrier_eq_coe]
  rw [← Functor.map_comp]
  rfl

@[reassoc (attr := simp)]

中文:
引理 appLE_appIso_inv
  结论: {X Y : 概形.{u}} (f : X ⟶ Y) [是开浸入 f] {U : Y.Opens}
  证明: by
  simp only [appLE, Category.assoc, appIso_inv_naturality, Functor.op_obj, Functor.op_map,
    Quiver.Hom.unop_op, opensFunctor_map_homOfLE, app_appIso_inv_assoc, Opens.carrier_eq_coe]
  rw [← Functor.map_comp]
  rfl

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, Functor.op_map, Functor.op_obj, Opens.carrier_eq_coe, Quiver, Quiver.Hom.unop_op, appIso_inv_naturality, app_appIso_inv_assoc, carrier_eq_coe, map_comp, op_map, op_obj, opensFunctor_map_homOfLE, unop_op
-/
lemma appLE_appIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {U : Y.Opens}
    {V : X.Opens} (e : V <= f ⁻¹ᵁ U) :
    f.appLE U V e ≫ (f.appIso V).inv =
        Y.presheaf.map (homOfLE <| (f.image_mono e).trans
          (f.image_preimage_eq_opensRange_inf U ▸ inf_le_right)).op := by
  simp only [appLE, Category.assoc, appIso_inv_naturality, Functor.op_obj, Functor.op_map,
    Quiver.Hom.unop_op, opensFunctor_map_homOfLE, app_appIso_inv_assoc, Opens.carrier_eq_coe]
  rw [← Functor.map_comp]
  rfl

@[reassoc (attr := simp)]
/--
lemma `appIso_inv_appLE` / 引理 `appIso_inv_appLE`

English:
lemma appIso_inv_appLE
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {U V : X.Opens}
  proof: by
  simp only [appLE, appIso_inv_app_assoc, eqToHom_op]
  rw [← Functor.map_comp]
  rfl

中文:
引理 appIso_inv_appLE
  结论: {X Y : 概形.{u}} (f : X ⟶ Y) [是开浸入 f] {U V : X.Opens}
  证明: by
  simp only [appLE, appIso_inv_app_assoc, eqToHom_op]
  rw [← Functor.map_comp]
  rfl

Depends on / 依赖: Functor, Functor.map_comp, appIso_inv_app_assoc, eqToHom_op, map_comp
-/
lemma appIso_inv_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {U V : X.Opens}
    (e : V <= f ⁻¹ᵁ f ''ᵁ U) :
    (f.appIso U).inv ≫ f.appLE (f ''ᵁ U) V e =
        X.presheaf.map (homOfLE (by rwa [preimage_image_eq] at e)).op := by
  simp only [appLE, appIso_inv_app_assoc, eqToHom_op]
  rw [← Functor.map_comp]
  rfl

/--
lemma `appIso_inv_app_presheafMap` / 引理 `appIso_inv_app_presheafMap`

English:
lemma appIso_inv_app_presheafMap
  given: (U : X.Opens)
  proof: by
  rw [Scheme.Hom.appIso_inv_app_assoc]; rw [← Functor.map_comp]; rw [← X.presheaf.map_id]; rfl

中文:
引理 appIso_inv_app_presheafMap
  条件: (U : X.Opens)
  证明: by
  rw [Scheme.Hom.appIso_inv_app_assoc]; rw [← Functor.map_comp]; rw [← X.presheaf.map_id]; rfl

Depends on / 依赖: Functor, Functor.map_comp, Scheme, Scheme.Hom.appIso_inv_app_assoc, X.presheaf.map_id, appIso_inv_app_assoc, map_comp, map_id, presheaf
-/
lemma appIso_inv_app_presheafMap (U : X.Opens) :
    (f.appIso U).inv ≫ f.app _ ≫
      X.presheaf.map (eqToHom (f.preimage_image_eq U).symm).op = 𝟙 _ := by
  rw [Scheme.Hom.appIso_inv_app_assoc]; rw [← Functor.map_comp]; rw [← X.presheaf.map_id]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `id_appIso` / 引理 `id_appIso`

English:
lemma id_appIso
  given: (U : X.Opens)
  proof: by
  ext; simp [appIso_hom]

中文:
引理 id_appIso
  条件: (U : X.Opens)
  证明: by
  ext; simp [appIso_hom]

Depends on / 依赖: appIso_hom
-/
lemma id_appIso (U : X.Opens) :
    (𝟙 X :).appIso U = X.presheaf.mapIso (eqToIso (by simp)).op := by
  ext; simp [appIso_hom]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `comp_appIso` / 引理 `comp_appIso`

English:
lemma comp_appIso
  statement: {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f]
  proof: by
  ext : 1; simp [appIso_hom, app_eq_appLE, appLE_comp_appLE, -comp_appLE]

中文:
引理 comp_appIso
  结论: {X Y Z : 概形.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [是开浸入 f]
  证明: by
  ext : 1; simp [appIso_hom, app_eq_appLE, appLE_comp_appLE, -comp_appLE]

Depends on / 依赖: appIso_hom, appLE_comp_appLE, app_eq_appLE, comp_appLE
-/
lemma comp_appIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f]
    [IsOpenImmersion g] (U : X.Opens) :
    (f ≫ g).appIso U =
      Z.presheaf.mapIso (eqToIso (by simp)).op ≪≫ g.appIso _ ≪≫ f.appIso U := by
  ext : 1; simp [appIso_hom, app_eq_appLE, appLE_comp_appLE, -comp_appLE]

end Scheme.Hom

/-- The open sets of an open subscheme corresponds to the open sets containing in the image. -/
@[simps]
/--
Definition of `IsOpenImmersion.opensEquiv` / `IsOpenImmersion.opensEquiv` 的定义

English:
definition IsOpenImmersion.opensEquiv
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
  body: ⟨f ''ᵁ U, Set.image_subset_range _ _⟩
  invFun U := f ⁻¹ᵁ U
  left_inv _ := Opens.ext (Set.preimage_image_eq _ f.isOpenEmbedding.injective)
  right_inv U := Subtype.ext (Opens.ext (Set.image_preimage_eq_of_subset U.2))

中文:
定义 是开浸入.opensEquiv
  签名: {X Y : 概形.{u}} (f : X ⟶ Y) [是开浸入 f]
  定义体: ⟨f ''ᵁ U, Set.image_subset_range _ _⟩
  invFun U := f ⁻¹ᵁ U
  left_inv _ := Opens.ext (Set.preimage_image_eq _ f.isOpenEmbedding.injective)
  right_inv U := Subtype.ext (Opens.ext (Set.image_preimage_eq_of_subset U.2))

Depends on / 依赖: Set.image_subset_range, image_subset_range
-/
def IsOpenImmersion.opensEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    X.Opens ≃ { U : Y.Opens // U <= f.opensRange } where
  toFun U := ⟨f ''ᵁ U, Set.image_subset_range _ _⟩
  invFun U := f ⁻¹ᵁ U
  left_inv _ := Opens.ext (Set.preimage_image_eq _ f.isOpenEmbedding.injective)
  right_inv U := Subtype.ext (Opens.ext (Set.image_preimage_eq_of_subset U.2))

namespace Scheme

/--
Instance `isOpenImmersion_SpecMap_localizationAway` / 实例 `isOpenImmersion_SpecMap_localizationAway`

English:
instance isOpenImmersion_SpecMap_localizationAway
  signature: {R : CommRingCat.{u}} (f : R)
  body: by
  apply SheafedSpace.IsOpenImmersion.of_stalk_iso (H := ?_)
  · exact (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away f) f :)
  · intro x
    exact isIso_SpecMap_stakMap_localization R (Submonoid.powers f) x

中文:
实例 isOpenImmersion_SpecMap_localizationAway
  签名: {R : 交换环范畴.{u}} (f : R)
  定义体: by
  apply SheafedSpace.IsOpenImmersion.of_stalk_iso (H := ?_)
  · exact (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away f) f :)
  · intro x
    exact isIso_SpecMap_stakMap_localization R (Submonoid.powers f) x

Depends on / 依赖: IsOpenImmersion, Localization, Localization.Away, PrimeSpectrum, PrimeSpectrum.localization_away_isOpenEmbedding, SheafedSpace, SheafedSpace.IsOpenImmersion.of_stalk_iso, Submonoid, Submonoid.powers, isIso_SpecMap_stakMap_localization, localization_away_isOpenEmbedding, of_stalk_iso, powers
-/
instance isOpenImmersion_SpecMap_localizationAway {R : CommRingCat.{u}} (f : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) := by
  apply SheafedSpace.IsOpenImmersion.of_stalk_iso (H := ?_)
  · exact (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away f) f :)
  · intro x
    exact isIso_SpecMap_stakMap_localization R (Submonoid.powers f) x

instance {R} [CommRing R] (f : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) :=
  isOpenImmersion_SpecMap_localizationAway (R := .of R) f

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `Hom.opensRange_localizationAway` / 引理 `Hom.opensRange_localizationAway`

English:
lemma Hom.opensRange_localizationAway
  given: {R : CommRingCat.{u}} (g : R)
  proof: by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range _ g

中文:
引理 态射.opensRange_localizationAway
  条件: {R : 交换环范畴.{u}} (g : R)
  证明: by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range _ g

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.localization_away_comap_range, SetLike, SetLike.ext, _iff, localization_away_comap_range
-/
lemma Hom.opensRange_localizationAway {R : CommRingCat.{u}} (g : R) :
    (Spec.map <| CommRingCat.ofHom <| algebraMap R (Localization.Away g)).opensRange =
      PrimeSpectrum.basicOpen g := by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range _ g

/--
lemma `_root_.AlgebraicGeometry.IsOpenImmersion.of_isLocalization` / 引理 `_root_.AlgebraicGeometry.IsOpenImmersion.of_isLocalization`

English:
lemma _root_.AlgebraicGeometry.IsOpenImmersion.of_isLocalization
  statement: {R S} [CommRing R] [CommRing S]
  proof: by
  have e := (IsLocalization.algEquiv (.powers f) S
    (Localization.Away f)).symm.toAlgHom.comp_algebraMap
  rw [← e]; rw [CommRingCat.ofHom_comp]; rw [Spec.map_comp]
  have H : IsIso (CommRingCat.ofHom (IsLocalization.algEquiv
    (Submonoid.powers f) S (Localization.Away f)).symm.toAlgHom.toRi

中文:
引理 _root_.AlgebraicGeometry.是开浸入.of_isLocalization
  结论: {R S} [交换环 R] [交换环 S]
  证明: by
  have e := (IsLocalization.algEquiv (.powers f) S
    (Localization.Away f)).symm.toAlgHom.comp_algebraMap
  rw [← e]; rw [CommRingCat.ofHom_comp]; rw [Spec.map_comp]
  have H : IsIso (CommRingCat.ofHom (IsLocalization.algEquiv
    (Submonoid.powers f) S (Localization.Away f)).symm.toAlgHom.toRi

Depends on / 依赖: AlgEquiv, AlgEquiv.toAlgHom_toRingHom, AlgHom, AlgHom.toRingHom_eq_coe, CommRingCat, CommRingCat.ofHom, CommRingCat.ofHom_comp, IsLocalization, IsLocalization.algEquiv, Localization, Localization.Away, Spec.map_comp, Submonoid, Submonoid.powers, algEquiv, comp_algebraMap, map_comp, ofHom_comp, powers, symm.toAlgHom.comp_algebraMap
-/
lemma _root_.AlgebraicGeometry.IsOpenImmersion.of_isLocalization {R S} [CommRing R] [CommRing S]
    [Algebra R S] (f : R) [IsLocalization.Away f S] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have e := (IsLocalization.algEquiv (.powers f) S
    (Localization.Away f)).symm.toAlgHom.comp_algebraMap
  rw [← e]; rw [CommRingCat.ofHom_comp]; rw [Spec.map_comp]
  have H : IsIso (CommRingCat.ofHom (IsLocalization.algEquiv
    (Submonoid.powers f) S (Localization.Away f)).symm.toAlgHom.toRingHom) := by
    exact inferInstanceAs (IsIso <| (IsLocalization.algEquiv
      (Submonoid.powers f) S (Localization.Away f)).toRingEquiv.toCommRingCatIso.inv)
  simp only [AlgHom.toRingHom_eq_coe, AlgEquiv.toAlgHom_toRingHom] at H ⊢
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_affine_mem_range_and_range_subset` / 定理 `exists_affine_mem_range_and_range_subset`

English:
theorem exists_affine_mem_range_and_range_subset
  proof: by
  obtain ⟨⟨V, hxV⟩, R, ⟨e⟩⟩ := X.2 x
  have : e.hom.base ⟨x, hxV⟩ in (Opens.map (e.inv.base ≫ V.inclusion')).obj U :=
    show ((e.hom ≫ e.inv).base ⟨x, hxV⟩).1 in U from e.hom_inv_id ▸ hxU
  obtain ⟨_, ⟨_, ⟨r : R, rfl⟩, rfl⟩, hr, hr'⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem

中文:
定理 存在_affine_mem_range_and_range_subset
  证明: by
  obtain ⟨⟨V, hxV⟩, R, ⟨e⟩⟩ := X.2 x
  have : e.hom.base ⟨x, hxV⟩ in (Opens.map (e.inv.base ≫ V.inclusion')).obj U :=
    show ((e.hom ≫ e.inv).base ⟨x, hxV⟩).1 in U from e.hom_inv_id ▸ hxU
  obtain ⟨_, ⟨_, ⟨r : R, rfl⟩, rfl⟩, hr, hr'⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Localization, Localization.Away, Opens.is_open, Opens.map, PrimeSpectrum, PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open, Spec.map, V.inclusion, X.ofRestrict, algebraMap, e.hom, e.hom.base, e.hom_inv_id, e.inv, e.inv.base, exists_subset_of_mem_open, hom_inv_id, inclusion
-/
theorem exists_affine_mem_range_and_range_subset
    {X : Scheme.{u}} {x : X} {U : X.Opens} (hxU : x in U) :
    exists R, exists (f : Spec R ⟶ X), IsOpenImmersion f ∧ x in Set.range f ∧ Set.range f subseteq U := by
  obtain ⟨⟨V, hxV⟩, R, ⟨e⟩⟩ := X.2 x
  have : e.hom.base ⟨x, hxV⟩ in (Opens.map (e.inv.base ≫ V.inclusion')).obj U :=
    show ((e.hom ≫ e.inv).base ⟨x, hxV⟩).1 in U from e.hom_inv_id ▸ hxU
  obtain ⟨_, ⟨_, ⟨r : R, rfl⟩, rfl⟩, hr, hr'⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open this (Opens.is_open' _)
  let f : Spec (.of <| Localization.Away r) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ ⟨e.inv ≫ X.ofRestrict _⟩
  refine ⟨.of (Localization.Away r), f, inferInstance, ?_⟩
  rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]
  erw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
  exact ⟨⟨_, hr, congr(($(e.hom_inv_id).base ⟨x, hxV⟩).1)⟩, Set.image_subset_iff.mpr hr'⟩

end Scheme

namespace PresheafedSpace.IsOpenImmersion

section ToScheme

variable {X : PresheafedSpace CommRingCat.{u}} (Y : Scheme.{u})
variable (f : X ⟶ Y.toPresheafedSpace) [H : PresheafedSpace.IsOpenImmersion f]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toScheme` / `toScheme` 的定义

English:
definition toScheme
  signature: : Scheme
  body: by
  apply LocallyRingedSpace.IsOpenImmersion.scheme (toLocallyRingedSpace _ f)
  intro x
  obtain ⟨R, i, _, h₁, h₂⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := ⟨_, H.base_open.isOpen_range⟩) ⟨x, rfl⟩
  refine ⟨R, LocallyRingedSpace.IsOpenImmersion.lift (toLocallyRingedSpaceHom _ f)

中文:
定义 toScheme
  签名: : 概形
  定义体: by
  apply LocallyRingedSpace.IsOpenImmersion.scheme (toLocallyRingedSpace _ f)
  intro x
  obtain ⟨R, i, _, h₁, h₂⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := ⟨_, H.base_open.isOpen_range⟩) ⟨x, rfl⟩
  refine ⟨R, LocallyRingedSpace.IsOpenImmersion.lift (toLocallyRingedSpaceHom _ f)

Depends on / 依赖: H.base_open.isOpen_range, IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion.lift, LocallyRingedSpace.IsOpenImmersion.lift_range, LocallyRingedSpace.IsOpenImmersion.scheme, Scheme, Scheme.exists_affine_mem_range_and_range_subset, base_open, exists_affine_mem_range_and_range_subset, infer_instance, isOpen_range, lift_range, scheme, toLocallyRingedSpace, toLocallyRingedSpaceHom
-/
def toScheme : Scheme := by
  apply LocallyRingedSpace.IsOpenImmersion.scheme (toLocallyRingedSpace _ f)
  intro x
  obtain ⟨R, i, _, h₁, h₂⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := ⟨_, H.base_open.isOpen_range⟩) ⟨x, rfl⟩
  refine ⟨R, LocallyRingedSpace.IsOpenImmersion.lift (toLocallyRingedSpaceHom _ f) _ h₂, ?_, ?_⟩
  · rw [LocallyRingedSpace.IsOpenImmersion.lift_range]; exact h₁
  · delta LocallyRingedSpace.IsOpenImmersion.lift; infer_instance

@[simp]
/--
theorem `toScheme_toLocallyRingedSpace` / 定理 `toScheme_toLocallyRingedSpace`

English:
theorem toScheme_toLocallyRingedSpace
  proof: rfl

中文:
定理 toScheme_toLocallyRingedSpace
  证明: rfl
-/
theorem toScheme_toLocallyRingedSpace :
    (toScheme Y f).toLocallyRingedSpace = toLocallyRingedSpace Y.1 f :=
  rfl

/--
Definition of `toSchemeHom` / `toSchemeHom` 的定义

English:
definition toSchemeHom
  signature: : toScheme Y f ⟶ Y
  body: ⟨toLocallyRingedSpaceHom _ f⟩

@[simp]

中文:
定义 toSchemeHom
  签名: : toScheme Y f ⟶ Y
  定义体: ⟨toLocallyRingedSpaceHom _ f⟩

@[simp]

Depends on / 依赖: toLocallyRingedSpaceHom
-/
def toSchemeHom : toScheme Y f ⟶ Y :=
  ⟨toLocallyRingedSpaceHom _ f⟩

@[simp]
/--
theorem `toSchemeHom_toPshHom` / 定理 `toSchemeHom_toPshHom`

English:
theorem toSchemeHom_toPshHom
  statement: (toSchemeHom Y f).toPshHom = f
  proof: rfl

中文:
定理 toSchemeHom_toPshHom
  结论: (toSchemeHom Y f).toPshHom = f
  证明: rfl
-/
theorem toSchemeHom_toPshHom : (toSchemeHom Y f).toPshHom = f :=
  rfl

/--
Instance `toSchemeHom_isOpenImmersion` / 实例 `toSchemeHom_isOpenImmersion`

English:
instance toSchemeHom_isOpenImmersion
  signature: : AlgebraicGeometry.IsOpenImmersion (toSchemeHom Y f)
  body: H

中文:
实例 toSchemeHom_isOpenImmersion
  签名: : AlgebraicGeometry.是开浸入 (toSchemeHom Y f)
  定义体: H
-/
instance toSchemeHom_isOpenImmersion : AlgebraicGeometry.IsOpenImmersion (toSchemeHom Y f) :=
  H

/--
theorem `scheme_eq_of_locallyRingedSpace_eq` / 定理 `scheme_eq_of_locallyRingedSpace_eq`

English:
theorem scheme_eq_of_locallyRingedSpace_eq
  statement: {X Y : Scheme.{u}}
  proof: by
  cases X; cases Y; congr

中文:
定理 scheme_eq_of_locallyRingedSpace_eq
  结论: {X Y : 概形.{u}}
  证明: by
  cases X; cases Y; congr
-/
theorem scheme_eq_of_locallyRingedSpace_eq {X Y : Scheme.{u}}
    (H : X.toLocallyRingedSpace = Y.toLocallyRingedSpace) : X = Y := by
  cases X; cases Y; congr

/--
theorem `scheme_toScheme` / 定理 `scheme_toScheme`

English:
theorem scheme_toScheme
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f]
  proof: by
  apply scheme_eq_of_locallyRingedSpace_eq
  exact locallyRingedSpace_toLocallyRingedSpace f.toLRSHom

中文:
定理 scheme_toScheme
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) [AlgebraicGeometry.是开浸入 f]
  证明: by
  apply scheme_eq_of_locallyRingedSpace_eq
  exact locallyRingedSpace_toLocallyRingedSpace f.toLRSHom

Depends on / 依赖: f.toLRSHom, locallyRingedSpace_toLocallyRingedSpace, scheme_eq_of_locallyRingedSpace_eq, toLRSHom
-/
theorem scheme_toScheme {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] :
    toScheme Y f.toPshHom = X := by
  apply scheme_eq_of_locallyRingedSpace_eq
  exact locallyRingedSpace_toLocallyRingedSpace f.toLRSHom

end ToScheme

end PresheafedSpace.IsOpenImmersion

section Restrict

variable {U : TopCat.{u}} (X : Scheme.{u}) {f : U ⟶ TopCat.of X} (h : IsOpenEmbedding f)

/-- The restriction of a Scheme along an open embedding. -/
@[simps! -isSimp carrier, simps! presheaf_obj]
/--
Definition of `Scheme.restrict` / `Scheme.restrict` 的定义

English:
definition Scheme.restrict
  signature: : Scheme
  body: { PresheafedSpace.IsOpenImmersion.toScheme X (X.toPresheafedSpace.ofRestrict h) with
    toPresheafedSpace := X.toPresheafedSpace.restrict h }

中文:
定义 概形.restrict
  签名: : 概形
  定义体: { PresheafedSpace.IsOpenImmersion.toScheme X (X.toPresheafedSpace.ofRestrict h) with
    toPresheafedSpace := X.toPresheafedSpace.restrict h }

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.toScheme, X.toPresheafedSpace.ofRestrict, X.toPresheafedSpace.restrict, ofRestrict, restrict, toPresheafedSpace, toScheme
-/
def Scheme.restrict : Scheme :=
  { PresheafedSpace.IsOpenImmersion.toScheme X (X.toPresheafedSpace.ofRestrict h) with
    toPresheafedSpace := X.toPresheafedSpace.restrict h }

/--
lemma `Scheme.restrict_toPresheafedSpace` / 引理 `Scheme.restrict_toPresheafedSpace`

English:
lemma Scheme.restrict_toPresheafedSpace
  proof: rfl

中文:
引理 概形.restrict_toPresheafedSpace
  证明: rfl
-/
lemma Scheme.restrict_toPresheafedSpace :
    (X.restrict h).toPresheafedSpace = X.toPresheafedSpace.restrict h := rfl

/-- The canonical map from the restriction to the subspace. -/
@[simps! toLRSHom_base, simps! -isSimp toLRSHom_c_app]
/--
Definition of `Scheme.ofRestrict` / `Scheme.ofRestrict` 的定义

English:
definition Scheme.ofRestrict
  signature: : X.restrict h ⟶ X
  body: ⟨X.toLocallyRingedSpace.ofRestrict h⟩

@[simp]

中文:
定义 概形.ofRestrict
  签名: : X.restrict h ⟶ X
  定义体: ⟨X.toLocallyRingedSpace.ofRestrict h⟩

@[simp]

Depends on / 依赖: X.toLocallyRingedSpace.ofRestrict, ofRestrict, toLocallyRingedSpace
-/
def Scheme.ofRestrict : X.restrict h ⟶ X :=
  ⟨X.toLocallyRingedSpace.ofRestrict h⟩

@[simp]
/--
lemma `Scheme.ofRestrict_app` / 引理 `Scheme.ofRestrict_app`

English:
lemma Scheme.ofRestrict_app
  given: (V)
  proof: rfl

中文:
引理 概形.ofRestrict_app
  条件: (V)
  证明: rfl
-/
lemma Scheme.ofRestrict_app (V) :
    (X.ofRestrict h).app V = X.presheaf.map (h.isOpenMap.adjunction.counit.app V).op :=
  rfl

/--
Instance `IsOpenImmersion.ofRestrict` / 实例 `IsOpenImmersion.ofRestrict`

English:
instance IsOpenImmersion.ofRestrict
  signature: : IsOpenImmersion (X.ofRestrict h)
  body: show PresheafedSpace.IsOpenImmersion (X.toPresheafedSpace.ofRestrict h) by infer_instance

@[simp]

中文:
实例 是开浸入.ofRestrict
  签名: : 是开浸入 (X.ofRestrict h)
  定义体: show PresheafedSpace.IsOpenImmersion (X.toPresheafedSpace.ofRestrict h) by infer_instance

@[simp]

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion, X.toPresheafedSpace.ofRestrict, infer_instance, ofRestrict, toPresheafedSpace
-/
instance IsOpenImmersion.ofRestrict : IsOpenImmersion (X.ofRestrict h) :=
  show PresheafedSpace.IsOpenImmersion (X.toPresheafedSpace.ofRestrict h) by infer_instance

@[simp]
/--
lemma `Scheme.ofRestrict_appLE` / 引理 `Scheme.ofRestrict_appLE`

English:
lemma Scheme.ofRestrict_appLE
  given: (V W e)
  proof: by
  dsimp [Hom.appLE]
  exact (X.presheaf.map_comp _ _).symm

中文:
引理 概形.ofRestrict_appLE
  条件: (V W e)
  证明: by
  dsimp [Hom.appLE]
  exact (X.presheaf.map_comp _ _).symm

Depends on / 依赖: Hom.appLE, X.presheaf.map_comp, map_comp, presheaf
-/
lemma Scheme.ofRestrict_appLE (V W e) :
    (X.ofRestrict h).appLE V W e = X.presheaf.map
      (homOfLE (show X.ofRestrict h ''ᵁ _ <= _ by exact Set.image_subset_iff.mpr e)).op := by
  dsimp [Hom.appLE]
  exact (X.presheaf.map_comp _ _).symm

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `Scheme.ofRestrict_appIso` / 引理 `Scheme.ofRestrict_appIso`

English:
lemma Scheme.ofRestrict_appIso
  given: (U)
  proof: by
  ext1
  simp only [Hom.appIso_hom', ofRestrict_appLE, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, Iso.refl_hom]

@[simp]

中文:
引理 概形.ofRestrict_appIso
  条件: (U)
  证明: by
  ext1
  simp only [Hom.appIso_hom', ofRestrict_appLE, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, Iso.refl_hom]

@[simp]

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_id, Functor, Hom.appIso_hom, Iso.refl_hom, appIso_hom, homOfLE_refl, map_id, ofRestrict_appLE, op_id, refl_hom
-/
lemma Scheme.ofRestrict_appIso (U) :
    (X.ofRestrict h).appIso U = Iso.refl _ := by
  ext1
  simp only [Hom.appIso_hom', ofRestrict_appLE, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, Iso.refl_hom]

@[simp]
/--
lemma `Scheme.restrict_presheaf_map` / 引理 `Scheme.restrict_presheaf_map`

English:
lemma Scheme.restrict_presheaf_map
  given: (V W) (i : V ⟶ W)
  proof: rfl

中文:
引理 概形.restrict_presheaf_map
  条件: (V W) (i : V ⟶ W)
  证明: rfl
-/
lemma Scheme.restrict_presheaf_map (V W) (i : V ⟶ W) :
    (X.restrict h).presheaf.map i = X.presheaf.map (homOfLE (show X.ofRestrict h ''ᵁ W.unop <=
      X.ofRestrict h ''ᵁ V.unop from Set.image_mono i.unop.le)).op := rfl

end Restrict

namespace IsOpenImmersion

variable {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [H : IsOpenImmersion f]

instance (priority := 100) of_isIso [IsIso g] : IsOpenImmersion g :=
  LocallyRingedSpace.IsOpenImmersion.of_isIso _

/--
theorem `isIso` / 定理 `isIso`

English:
theorem isIso
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] [Epi f.base]
  statement: IsIso f
  proof: @isIso_of_reflects_iso _ _ _ _ _ _ f
    (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace)
    (@PresheafedSpace.IsOpenImmersion.to_iso _ _ _ _ f.toPshHom ‹_› _) _

中文:
定理 isIso
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) [是开浸入 f] [满态射 f.base]
  结论: 是同构 f
  证明: @isIso_of_reflects_iso _ _ _ _ _ _ f
    (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace)
    (@PresheafedSpace.IsOpenImmersion.to_iso _ _ _ _ f.toPshHom ‹_› _) _

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace, PresheafedSpace, PresheafedSpace.IsOpenImmersion.to_iso, Scheme, Scheme.forgetToLocallyRingedSpace, SheafedSpace, SheafedSpace.forgetToPresheafedSpace, f.toPshHom, forgetToLocallyRingedSpace, forgetToPresheafedSpace, forgetToSheafedSpace, isIso_of_reflects_iso, toPshHom, to_iso
-/
theorem isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] [Epi f.base] : IsIso f :=
  @isIso_of_reflects_iso _ _ _ _ _ _ f
    (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace)
    (@PresheafedSpace.IsOpenImmersion.to_iso _ _ _ _ f.toPshHom ‹_› _) _

/--
theorem `of_isIso_stalkMap` / 定理 `of_isIso_stalkMap`

English:
theorem of_isIso_stalkMap
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsOpenEmbedding f)
  proof: have (x : X) : IsIso (f.toShHom.hom.stalkMap x) := inferInstanceAs (IsIso (f.stalkMap x))
  SheafedSpace.IsOpenImmersion.of_stalk_iso f.toShHom hf

中文:
定理 of_isIso_stalkMap
  结论: {X Y : 概形.{u}} (f : X ⟶ Y) (hf : 是开嵌入 f)
  证明: have (x : X) : IsIso (f.toShHom.hom.stalkMap x) := inferInstanceAs (IsIso (f.stalkMap x))
  SheafedSpace.IsOpenImmersion.of_stalk_iso f.toShHom hf

Depends on / 依赖: IsOpenImmersion, SheafedSpace, SheafedSpace.IsOpenImmersion.of_stalk_iso, f.stalkMap, f.toShHom, f.toShHom.hom.stalkMap, of_stalk_iso, stalkMap, toShHom
-/
theorem of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsOpenEmbedding f)
    [forall x, IsIso (f.stalkMap x)] : IsOpenImmersion f :=
  have (x : X) : IsIso (f.toShHom.hom.stalkMap x) := inferInstanceAs (IsIso (f.stalkMap x))
  SheafedSpace.IsOpenImmersion.of_stalk_iso f.toShHom hf

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    IsIso (f.stalkMap x) :=
inferInstanceAs IsIso (f.toLRSHom.stalkMap x)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  statement: {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g]
  proof: haveI (x : X) : IsIso (f.stalkMap x) :=
    haveI : IsIso (g.stalkMap (f x) ≫ f.stalkMap x) := by
      rw [← Scheme.Hom.stalkMap_comp]
      infer_instance
    IsIso.of_isIso_comp_left (f := g.stalkMap (f x)) _
IsOpenImmersion.of_isIso_stalkMap _
    IsOpenEmbedding.of_comp _ (Scheme.Hom.isOpenEmbe

中文:
引理 of_comp
  结论: {X Y Z : 概形.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [是开浸入 g]
  证明: haveI (x : X) : IsIso (f.stalkMap x) :=
    haveI : IsIso (g.stalkMap (f x) ≫ f.stalkMap x) := by
      rw [← Scheme.Hom.stalkMap_comp]
      infer_instance
    IsIso.of_isIso_comp_left (f := g.stalkMap (f x)) _
IsOpenImmersion.of_isIso_stalkMap _
    IsOpenEmbedding.of_comp _ (Scheme.Hom.isOpenEmbe

Depends on / 依赖: IsIso.of_isIso_comp_left, IsOpenEmbedding, IsOpenEmbedding.of_comp, IsOpenImmersion, IsOpenImmersion.of_isIso_stalkMap, Scheme, Scheme.Hom.isOpenEmbedding, Scheme.Hom.stalkMap_comp, f.stalkMap, g.stalkMap, infer_instance, isOpenEmbedding, of_comp, of_isIso_comp_left, of_isIso_stalkMap, stalkMap, stalkMap_comp
-/
lemma of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g]
    [IsOpenImmersion (f ≫ g)] : IsOpenImmersion f :=
  haveI (x : X) : IsIso (f.stalkMap x) :=
    haveI : IsIso (g.stalkMap (f x) ≫ f.stalkMap x) := by
      rw [← Scheme.Hom.stalkMap_comp]
      infer_instance
    IsIso.of_isIso_comp_left (f := g.stalkMap (f x)) _
IsOpenImmersion.of_isIso_stalkMap _
    IsOpenEmbedding.of_comp _ (Scheme.Hom.isOpenEmbedding g) (Scheme.Hom.isOpenEmbedding (f ≫ g))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasOfPostcompProperty @IsOpenImmersion @IsOpenImmersion
  body: .of_comp f g

中文:
实例 :
  签名: MorphismProperty.有OfPostcompProperty @是开浸入 @是开浸入
  定义体: .of_comp f g

Depends on / 依赖: of_comp
-/
instance : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion @IsOpenImmersion where
  of_postcomp f g _ _ := .of_comp f g

/--
theorem `iff_isIso_stalkMap` / 定理 `iff_isIso_stalkMap`

English:
theorem iff_isIso_stalkMap
  given: {X Y : Scheme.{u}} {f : X ⟶ Y}
  proof: ⟨fun H => ⟨H.1, fun x => inferInstanceAs IsIso (f.toPshHom.stalkMap x)⟩,
    fun ⟨h, _⟩ => .of_isIso_stalkMap f h⟩

中文:
定理 iff_isIso_stalkMap
  条件: {X Y : 概形.{u}} {f : X ⟶ Y}
  证明: ⟨fun H => ⟨H.1, fun x => inferInstanceAs IsIso (f.toPshHom.stalkMap x)⟩,
    fun ⟨h, _⟩ => .of_isIso_stalkMap f h⟩

Depends on / 依赖: f.toPshHom.stalkMap, of_isIso_stalkMap, stalkMap, toPshHom
-/
theorem iff_isIso_stalkMap {X Y : Scheme.{u}} {f : X ⟶ Y} :
    IsOpenImmersion f ↔ IsOpenEmbedding f ∧ forall x, IsIso (f.stalkMap x) :=
⟨fun H => ⟨H.1, fun x => inferInstanceAs IsIso (f.toPshHom.stalkMap x)⟩,
    fun ⟨h, _⟩ => .of_isIso_stalkMap f h⟩

/--
theorem `_root_.AlgebraicGeometry.isIso_iff_isOpenImmersion_and_epi_base` / 定理 `_root_.AlgebraicGeometry.isIso_iff_isOpenImmersion_and_epi_base`

English:
theorem _root_.AlgebraicGeometry.isIso_iff_isOpenImmersion_and_epi_base
  proof: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => IsOpenImmersion.isIso f⟩

中文:
定理 _root_.AlgebraicGeometry.isIso_iff_isOpenImmersion_and_epi_base
  证明: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => IsOpenImmersion.isIso f⟩

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isIso
-/
theorem _root_.AlgebraicGeometry.isIso_iff_isOpenImmersion_and_epi_base
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion f ∧ Epi f.base :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => IsOpenImmersion.isIso f⟩

/--
theorem `_root_.AlgebraicGeometry.isIso_iff_isIso_stalkMap` / 定理 `_root_.AlgebraicGeometry.isIso_iff_isIso_stalkMap`

English:
theorem _root_.AlgebraicGeometry.isIso_iff_isIso_stalkMap
  given: {X Y : Scheme.{u}} (f : X ⟶ Y)
  proof: by
  rw [isIso_iff_isOpenImmersion_and_epi_base]; rw [IsOpenImmersion.iff_isIso_stalkMap]; rw [and_comm]; rw [← and_assoc]
  refine and_congr ⟨?_, ?_⟩ Iff.rfl
  · rintro ⟨h₁, h₂⟩
    convert_to!
      IsIso
        (TopCat.isoOfHomeo
          (Equiv.toHomeomorphOfContinuousOpen
            (.ofBije

中文:
定理 _root_.AlgebraicGeometry.isIso_iff_isIso_stalkMap
  条件: {X Y : 概形.{u}} (f : X ⟶ Y)
  证明: by
  rw [isIso_iff_isOpenImmersion_and_epi_base]; rw [IsOpenImmersion.iff_isIso_stalkMap]; rw [and_comm]; rw [← and_assoc]
  refine and_congr ⟨?_, ?_⟩ Iff.rfl
  · rintro ⟨h₁, h₂⟩
    convert_to!
      IsIso
        (TopCat.isoOfHomeo
          (Equiv.toHomeomorphOfContinuousOpen
            (.ofBije

Depends on / 依赖: Equiv.toHomeomorphOfContinuousOpen, Iff.rfl, IsOpenImmersion, IsOpenImmersion.iff_isIso_stalkMap, TopCat, TopCat.epi_iff_surjective, TopCat.homeoOfIso, TopCat.isoOfHomeo, and_assoc, and_comm, and_congr, continuous, convert_to, epi_iff_surjective, f.base, homeoOfIso, iff_isIso_stalkMap, infer_instance, injective, isIso_iff_isOpenImmersion_and_epi_base
-/
theorem _root_.AlgebraicGeometry.isIso_iff_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsIso f.base ∧ forall x, IsIso (f.stalkMap x) := by
  rw [isIso_iff_isOpenImmersion_and_epi_base]; rw [IsOpenImmersion.iff_isIso_stalkMap]; rw [and_comm]; rw [← and_assoc]
  refine and_congr ⟨?_, ?_⟩ Iff.rfl
  · rintro ⟨h₁, h₂⟩
    convert_to!
      IsIso
        (TopCat.isoOfHomeo
          (Equiv.toHomeomorphOfContinuousOpen
            (.ofBijective _ ⟨h₂.injective, (TopCat.epi_iff_surjective _).mp h₁⟩) h₂.continuous
            h₂.isOpenMap)).hom
    infer_instance
  · intro H; exact ⟨inferInstance, (TopCat.homeoOfIso (asIso f.base)).isOpenEmbedding⟩

/--
Definition of `isoRestrict` / `isoRestrict` 的定义

English:
definition isoRestrict
  signature: : X ≅ Z.restrict f.isOpenEmbedding
  body: Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
    (LocallyRingedSpace.IsOpenImmersion.isoRestrict f.toLRSHom)

local notation "forget" => Scheme.forgetToLocallyRingedSpace

中文:
定义 isoRestrict
  签名: : X ≅ Z.restrict f.isOpenEmbedding
  定义体: Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
    (LocallyRingedSpace.IsOpenImmersion.isoRestrict f.toLRSHom)

local notation "forget" => Scheme.forgetToLocallyRingedSpace

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion.isoRestrict, Scheme, Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso, f.toLRSHom, fullyFaithfulForgetToLocallyRingedSpace, isoRestrict, preimageIso, toLRSHom
-/
def isoRestrict : X ≅ Z.restrict f.isOpenEmbedding :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
    (LocallyRingedSpace.IsOpenImmersion.isoRestrict f.toLRSHom)

local notation "forget" => Scheme.forgetToLocallyRingedSpace

/--
Instance `mono` / 实例 `mono`

English:
instance mono
  signature: : Mono f
  body: (forget).mono_of_mono_map (inferInstanceAs (Mono f.toLRSHom))

中文:
实例 mono
  签名: : 单态射 f
  定义体: (forget).mono_of_mono_map (inferInstanceAs (Mono f.toLRSHom))

Depends on / 依赖: f.toLRSHom, forget, mono_of_mono_map, toLRSHom
-/
instance mono : Mono f :=
  (forget).mono_of_mono_map (inferInstanceAs (Mono f.toLRSHom))

/--
lemma `le_monomorphisms` / 引理 `le_monomorphisms`

English:
lemma le_monomorphisms
  proof: fun _ _ _ _ =>
  MorphismProperty.monomorphisms.infer_property _

中文:
引理 le_monomorphisms
  证明: fun _ _ _ _ =>
  MorphismProperty.monomorphisms.infer_property _
-/
lemma le_monomorphisms :
    IsOpenImmersion <= MorphismProperty.monomorphisms Scheme.{u} := fun _ _ _ _ =>
  MorphismProperty.monomorphisms.infer_property _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyRingedSpace.IsOpenImmersion ((forget).map f)
  body: ⟨H.base_open, H.c_iso⟩

中文:
实例 :
  签名: LocallyRinged空间.是开浸入 ((forget).map f)
  定义体: ⟨H.base_open, H.c_iso⟩

Depends on / 依赖: H.base_open, H.c_iso, base_open, c_iso
-/
instance : LocallyRingedSpace.IsOpenImmersion ((forget).map f) :=
  ⟨H.base_open, H.c_iso⟩

/--
Instance `hasLimit_cospan_forget_of_left` / 实例 `hasLimit_cospan_forget_of_left`

English:
instance hasLimit_cospan_forget_of_left
  signature: :
  body: by
  rw [hasLimit_iff_of_iso (diagramIsoCospan _)]
  exact inferInstanceAs (HasLimit (cospan ((forget).map f) ((forget).map g)))

中文:
实例 hasLimit_cospan_forget_of_left
  签名: :
  定义体: by
  rw [hasLimit_iff_of_iso (diagramIsoCospan _)]
  exact inferInstanceAs (HasLimit (cospan ((forget).map f) ((forget).map g)))

Depends on / 依赖: HasLimit, cospan, diagramIsoCospan, forget, hasLimit_iff_of_iso
-/
instance hasLimit_cospan_forget_of_left :
    HasLimit (cospan f g ⋙ forget) := by
  rw [hasLimit_iff_of_iso (diagramIsoCospan _)]
  exact inferInstanceAs (HasLimit (cospan ((forget).map f) ((forget).map g)))

open CategoryTheory.Limits.WalkingCospan

/--
Instance `hasLimit_cospan_forget_of_left'` / 实例 `hasLimit_cospan_forget_of_left'`

English:
instance hasLimit_cospan_forget_of_left'
  signature: :
  body: show HasLimit (cospan ((forget).map f) ((forget).map g)) from inferInstance

中文:
实例 hasLimit_cospan_forget_of_left'
  签名: :
  定义体: show HasLimit (cospan ((forget).map f) ((forget).map g)) from inferInstance

Depends on / 依赖: HasLimit, cospan, forget
-/
instance hasLimit_cospan_forget_of_left' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map f) ((forget).map g)) from inferInstance

/--
Instance `hasLimit_cospan_forget_of_right` / 实例 `hasLimit_cospan_forget_of_right`

English:
instance hasLimit_cospan_forget_of_right
  signature: : HasLimit (cospan g f ⋙ forget)
  body: by
  rw [hasLimit_iff_of_iso (diagramIsoCospan _)]
  exact inferInstanceAs (HasLimit (cospan ((forget).map g) ((forget).map f)))

中文:
实例 hasLimit_cospan_forget_of_right
  签名: : 有极限 (cospan g f ⋙ forget)
  定义体: by
  rw [hasLimit_iff_of_iso (diagramIsoCospan _)]
  exact inferInstanceAs (HasLimit (cospan ((forget).map g) ((forget).map f)))

Depends on / 依赖: HasLimit, cospan, diagramIsoCospan, forget, hasLimit_iff_of_iso
-/
instance hasLimit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget) := by
  rw [hasLimit_iff_of_iso (diagramIsoCospan _)]
  exact inferInstanceAs (HasLimit (cospan ((forget).map g) ((forget).map f)))

/--
Instance `hasLimit_cospan_forget_of_right'` / 实例 `hasLimit_cospan_forget_of_right'`

English:
instance hasLimit_cospan_forget_of_right'
  signature: :
  body: show HasLimit (cospan ((forget).map g) ((forget).map f)) from inferInstance

中文:
实例 hasLimit_cospan_forget_of_right'
  签名: :
  定义体: show HasLimit (cospan ((forget).map g) ((forget).map f)) from inferInstance

Depends on / 依赖: HasLimit, cospan, forget
-/
instance hasLimit_cospan_forget_of_right' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map g) ((forget).map f)) from inferInstance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `forgetCreatesPullbackOfLeft` / 实例 `forgetCreatesPullbackOfLeft`

English:
instance forgetCreatesPullbackOfLeft
  signature: : CreatesLimit (cospan f g) forget
  body: createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (pullback.snd f.toLRSHom g.toLRSHom).toShHom.hom)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

中文:
实例 forgetCreatesPullbackOfLeft
  签名: : 创造极限 (cospan f g) forget
  定义体: createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (pullback.snd f.toLRSHom g.toLRSHom).toShHom.hom)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

Depends on / 依赖: HasLimit, HasLimit.isoOfNatIso, IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.toScheme, createsLimitOfFullyFaithfulOfIso, diagramIsoCospan, eqToIso, f.toLRSHom, g.toLRSHom, isoOfNatIso, pullback, pullback.snd, toLRSHom, toScheme, toShHom, toShHom.hom
-/
instance forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (pullback.snd f.toLRSHom g.toLRSHom).toShHom.hom)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `forgetCreatesPullbackOfRight` / 实例 `forgetCreatesPullbackOfRight`

English:
instance forgetCreatesPullbackOfRight
  signature: : CreatesLimit (cospan g f) forget
  body: createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (pullback.fst g.toLRSHom f.toLRSHom).1)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

中文:
实例 forgetCreatesPullbackOfRight
  签名: : 创造极限 (cospan g f) forget
  定义体: createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (pullback.fst g.toLRSHom f.toLRSHom).1)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

Depends on / 依赖: HasLimit, HasLimit.isoOfNatIso, IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.toScheme, createsLimitOfFullyFaithfulOfIso, diagramIsoCospan, eqToIso, f.toLRSHom, g.toLRSHom, isoOfNatIso, pullback, pullback.fst, toLRSHom, toScheme
-/
instance forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (pullback.fst g.toLRSHom f.toLRSHom).1)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimit (cospan f g) forget
  body: CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit _ _

中文:
实例 :
  签名: 保持极限 (cospan f g) forget
  定义体: CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit _ _

Depends on / 依赖: CategoryTheory, CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit, preservesLimit_of_createsLimit_and_hasLimit
-/
instance : PreservesLimit (cospan f g) forget :=
  CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimit (cospan g f) forget
  body: preservesPullback_symmetry _ _ _

中文:
实例 :
  签名: 保持极限 (cospan g f) forget
  定义体: preservesPullback_symmetry _ _ _

Depends on / 依赖: preservesPullback_symmetry
-/
instance : PreservesLimit (cospan g f) forget :=
  preservesPullback_symmetry _ _ _

/--
Instance `hasPullback_of_left` / 实例 `hasPullback_of_left`

English:
instance hasPullback_of_left
  signature: : HasPullback f g
  body: hasLimit_of_created (cospan f g) forget

中文:
实例 hasPullback_of_left
  签名: : HasPullback f g
  定义体: hasLimit_of_created (cospan f g) forget

Depends on / 依赖: cospan, forget, hasLimit_of_created
-/
instance hasPullback_of_left : HasPullback f g :=
  hasLimit_of_created (cospan f g) forget

/--
Instance `hasPullback_of_right` / 实例 `hasPullback_of_right`

English:
instance hasPullback_of_right
  signature: : HasPullback g f
  body: hasLimit_of_created (cospan g f) forget

中文:
实例 hasPullback_of_right
  签名: : HasPullback g f
  定义体: hasLimit_of_created (cospan g f) forget

Depends on / 依赖: cospan, forget, hasLimit_of_created
-/
instance hasPullback_of_right : HasPullback g f :=
  hasLimit_of_created (cospan g f) forget

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOpenImmersion (pullback.snd f g)
  body: by
  have := PreservesPullback.iso_hom_snd forget f g
  dsimp only [Scheme.forgetToLocallyRingedSpace, inducedFunctor_map] at this
  change LocallyRingedSpace.IsOpenImmersion _
  rw [← this]
  infer_instance

中文:
实例 :
  签名: 是开浸入 (pullback.snd f g)
  定义体: by
  have := PreservesPullback.iso_hom_snd forget f g
  dsimp only [Scheme.forgetToLocallyRingedSpace, inducedFunctor_map] at this
  change LocallyRingedSpace.IsOpenImmersion _
  rw [← this]
  infer_instance

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion, PreservesPullback, PreservesPullback.iso_hom_snd, Scheme, Scheme.forgetToLocallyRingedSpace, forget, forgetToLocallyRingedSpace, inducedFunctor_map, infer_instance, iso_hom_snd
-/
instance : IsOpenImmersion (pullback.snd f g) := by
  have := PreservesPullback.iso_hom_snd forget f g
  dsimp only [Scheme.forgetToLocallyRingedSpace, inducedFunctor_map] at this
  change LocallyRingedSpace.IsOpenImmersion _
  rw [← this]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOpenImmersion (pullback.fst g f)
  body: by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

中文:
实例 :
  签名: 是开浸入 (pullback.fst g f)
  定义体: by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

Depends on / 依赖: infer_instance, pullbackSymmetry_hom_comp_snd
-/
instance : IsOpenImmersion (pullback.fst g f) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsOpenImmersion
  signature: g] :
  body: by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl]
  change IsOpenImmersion (_ ≫ f)
  infer_instance

中文:
实例 [是开浸入
  签名: g] :
  定义体: by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl]
  change IsOpenImmersion (_ ≫ f)
  infer_instance

Depends on / 依赖: IsOpenImmersion, WalkingCospan, WalkingCospan.Hom.inl, cospan, infer_instance, limit.w
-/
instance [IsOpenImmersion g] :
    IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl]
  change IsOpenImmersion (_ ≫ f)
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimit (cospan f g) Scheme.forgetToTop
  body: by
  delta Scheme.forgetToTop
  refine @Limits.comp_preservesLimit _ _ _ _ _ _ (K := cospan f g) _ _ (F := forget)
    (G := LocallyRingedSpace.forgetToTop) ?_ ?_
  · infer_instance
  refine @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoCospan.{u} _).symm ?_
  dsimp [LocallyRingedSpace

中文:
实例 :
  签名: 保持极限 (cospan f g) 概形.forgetToTop
  定义体: by
  delta Scheme.forgetToTop
  refine @Limits.comp_preservesLimit _ _ _ _ _ _ (K := cospan f g) _ _ (F := forget)
    (G := LocallyRingedSpace.forgetToTop) ?_ ?_
  · infer_instance
  refine @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoCospan.{u} _).symm ?_
  dsimp [LocallyRingedSpace

Depends on / 依赖: Limits, Limits.comp_preservesLimit, LocallyRingedSpace, LocallyRingedSpace.forgetToTop, Scheme, Scheme.forgetToTop, comp_preservesLimit, cospan, diagramIsoCospan, forget, forgetToTop, infer_instance, preservesLimit_of_iso_diagram
-/
instance : PreservesLimit (cospan f g) Scheme.forgetToTop := by
  delta Scheme.forgetToTop
  refine @Limits.comp_preservesLimit _ _ _ _ _ _ (K := cospan f g) _ _ (F := forget)
    (G := LocallyRingedSpace.forgetToTop) ?_ ?_
  · infer_instance
  refine @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoCospan.{u} _).symm ?_
  dsimp [LocallyRingedSpace.forgetToTop]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimit (cospan g f) Scheme.forgetToTop
  body: preservesPullback_symmetry _ _ _

中文:
实例 :
  签名: 保持极限 (cospan g f) 概形.forgetToTop
  定义体: preservesPullback_symmetry _ _ _

Depends on / 依赖: preservesPullback_symmetry
-/
instance : PreservesLimit (cospan g f) Scheme.forgetToTop :=
  preservesPullback_symmetry _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimit (cospan f g) Scheme.forget
  body: by delta Scheme.forget; infer_instance

中文:
实例 :
  签名: 保持极限 (cospan f g) 概形.forget
  定义体: by delta Scheme.forget; infer_instance

Depends on / 依赖: Scheme, Scheme.forget, forget, infer_instance
-/
instance : PreservesLimit (cospan f g) Scheme.forget := by delta Scheme.forget; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimit (cospan g f) Scheme.forget
  body: by delta Scheme.forget; infer_instance

中文:
实例 :
  签名: 保持极限 (cospan g f) 概形.forget
  定义体: by delta Scheme.forget; infer_instance

Depends on / 依赖: Scheme, Scheme.forget, forget, infer_instance
-/
instance : PreservesLimit (cospan g f) Scheme.forget := by delta Scheme.forget; infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
theorem `range_pullbackSnd` / 定理 `range_pullbackSnd`

English:
theorem range_pullbackSnd
  proof: by
  rw [← show _ = (pullback.snd f g).base from
    PreservesPullback.iso_hom_snd Scheme.forgetToTop f g]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [Set.range_eq_univ.mpr]; rw [← @Set.preimage_univ _ _ (pullback.fst f.base g.base)]
  -- Porting note (https://github.com/leanprover-community/mat

中文:
定理 range_pullbackSnd
  证明: by
  rw [← show _ = (pullback.snd f g).base from
    PreservesPullback.iso_hom_snd Scheme.forgetToTop f g]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [Set.range_eq_univ.mpr]; rw [← @Set.preimage_univ _ _ (pullback.fst f.base g.base)]
  -- Porting note (https://github.com/leanprover-community/mat

Depends on / 依赖: PreservesPullback, PreservesPullback.iso_hom_snd, Scheme, Scheme.forgetToTop, Set.preimage_univ, Set.range_comp, Set.range_eq_univ.mpr, TopCat, TopCat.coe_comp, coe_comp, f.base, forgetToTop, g.base, iso_hom_snd, preimage_univ, pullback, pullback.fst, pullback.snd, range_comp, range_eq_univ
-/
theorem range_pullbackSnd :
    Set.range (pullback.snd f g) = g ⁻¹ᵁ f.opensRange := by
  rw [← show _ = (pullback.snd f g).base from
    PreservesPullback.iso_hom_snd Scheme.forgetToTop f g]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [Set.range_eq_univ.mpr]; rw [← @Set.preimage_univ _ _ (pullback.fst f.base g.base)]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): was `rw`
  · erw [TopCat.pullback_snd_image_fst_preimage]
    rw [Set.image_univ]
    rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance

/--
theorem `_root_.AlgebraicGeometry.Scheme.Hom.opensRange_pullbackSnd` / 定理 `_root_.AlgebraicGeometry.Scheme.Hom.opensRange_pullbackSnd`

English:
theorem _root_.AlgebraicGeometry.Scheme.Hom.opensRange_pullbackSnd
  proof: Opens.ext (range_pullbackSnd f g)

中文:
定理 _root_.AlgebraicGeometry.概形.态射.opensRange_pullbackSnd
  证明: Opens.ext (range_pullbackSnd f g)

Depends on / 依赖: Opens.ext, range_pullbackSnd
-/
theorem _root_.AlgebraicGeometry.Scheme.Hom.opensRange_pullbackSnd :
    (pullback.snd f g).opensRange = g ⁻¹ᵁ f.opensRange :=
  Opens.ext (range_pullbackSnd f g)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `range_pullbackFst` / 定理 `range_pullbackFst`

English:
theorem range_pullbackFst
  proof: by
  rw [← show _ = (pullback.fst g f).base from
    PreservesPullback.iso_hom_fst Scheme.forgetToTop g f]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [Set.range_eq_univ.mpr]; rw [← @Set.preimage_univ _ _ (pullback.snd g.base f.base)]
  -- Porting note (https://github.com/leanprover-community/mat

中文:
定理 range_pullbackFst
  证明: by
  rw [← show _ = (pullback.fst g f).base from
    PreservesPullback.iso_hom_fst Scheme.forgetToTop g f]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [Set.range_eq_univ.mpr]; rw [← @Set.preimage_univ _ _ (pullback.snd g.base f.base)]
  -- Porting note (https://github.com/leanprover-community/mat

Depends on / 依赖: PreservesPullback, PreservesPullback.iso_hom_fst, Scheme, Scheme.forgetToTop, Set.preimage_univ, Set.range_comp, Set.range_eq_univ.mpr, TopCat, TopCat.coe_comp, coe_comp, f.base, forgetToTop, g.base, iso_hom_fst, preimage_univ, pullback, pullback.fst, pullback.snd, range_comp, range_eq_univ
-/
theorem range_pullbackFst :
    Set.range (pullback.fst g f) = g ⁻¹ᵁ f.opensRange := by
  rw [← show _ = (pullback.fst g f).base from
    PreservesPullback.iso_hom_fst Scheme.forgetToTop g f]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [Set.range_eq_univ.mpr]; rw [← @Set.preimage_univ _ _ (pullback.snd g.base f.base)]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): was `rw`
  · erw [TopCat.pullback_fst_image_snd_preimage]
    rw [Set.image_univ]
    rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance

/--
theorem `_root_.AlgebraicGeometry.Scheme.Hom.opensRange_pullbackFst` / 定理 `_root_.AlgebraicGeometry.Scheme.Hom.opensRange_pullbackFst`

English:
theorem _root_.AlgebraicGeometry.Scheme.Hom.opensRange_pullbackFst
  proof: Opens.ext (range_pullbackFst f g)

中文:
定理 _root_.AlgebraicGeometry.概形.态射.opensRange_pullbackFst
  证明: Opens.ext (range_pullbackFst f g)

Depends on / 依赖: Opens.ext, range_pullbackFst
-/
theorem _root_.AlgebraicGeometry.Scheme.Hom.opensRange_pullbackFst :
    (pullback.fst g f).opensRange = g ⁻¹ᵁ f.opensRange :=
  Opens.ext (range_pullbackFst f g)

/--
theorem `range_pullback_to_base_of_left` / 定理 `range_pullback_to_base_of_left`

English:
theorem range_pullback_to_base_of_left
  proof: by
  rw [pullback.condition]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [range_pullbackSnd]; rw [Opens.map_obj]; rw [Opens.coe_mk]; rw [Set.image_preimage_eq_inter_range]; rw [Opens.carrier_eq_coe]; rw [Scheme.Hom.coe_opensRange]

中文:
定理 range_pullback_to_base_of_left
  证明: by
  rw [pullback.condition]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [range_pullbackSnd]; rw [Opens.map_obj]; rw [Opens.coe_mk]; rw [Set.image_preimage_eq_inter_range]; rw [Opens.carrier_eq_coe]; rw [Scheme.Hom.coe_opensRange]

Depends on / 依赖: Opens.carrier_eq_coe, Opens.coe_mk, Opens.map_obj, Scheme, Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, Set.image_preimage_eq_inter_range, Set.range_comp, TopCat, TopCat.coe_comp, carrier_eq_coe, coe_comp, coe_mk, coe_opensRange, comp_base, condition, image_preimage_eq_inter_range, map_obj, pullback, pullback.condition
-/
theorem range_pullback_to_base_of_left :
    Set.range (pullback.fst f g ≫ f) = Set.range f inter Set.range g := by
  rw [pullback.condition]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [range_pullbackSnd]; rw [Opens.map_obj]; rw [Opens.coe_mk]; rw [Set.image_preimage_eq_inter_range]; rw [Opens.carrier_eq_coe]; rw [Scheme.Hom.coe_opensRange]

/--
theorem `range_pullback_to_base_of_right` / 定理 `range_pullback_to_base_of_right`

English:
theorem range_pullback_to_base_of_right
  proof: by
  rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [range_pullbackFst]; rw [Opens.map_obj]; rw [Opens.coe_mk]; rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_comm]; rw [Opens.carrier_eq_coe]; rw [Scheme.Hom.coe_opensRange]

中文:
定理 range_pullback_to_base_of_right
  证明: by
  rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [range_pullbackFst]; rw [Opens.map_obj]; rw [Opens.coe_mk]; rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_comm]; rw [Opens.carrier_eq_coe]; rw [Scheme.Hom.coe_opensRange]

Depends on / 依赖: Opens.carrier_eq_coe, Opens.coe_mk, Opens.map_obj, Scheme, Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, Set.image_preimage_eq_inter_range, Set.inter_comm, Set.range_comp, TopCat, TopCat.coe_comp, carrier_eq_coe, coe_comp, coe_mk, coe_opensRange, comp_base, image_preimage_eq_inter_range, inter_comm, map_obj, range_comp
-/
theorem range_pullback_to_base_of_right :
    Set.range (pullback.fst g f ≫ g) = Set.range g inter Set.range f := by
  rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [range_pullbackFst]; rw [Opens.map_obj]; rw [Opens.coe_mk]; rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_comm]; rw [Opens.carrier_eq_coe]; rw [Scheme.Hom.coe_opensRange]

/--
lemma `image_preimage_eq_preimage_image_of_isPullback` / 引理 `image_preimage_eq_preimage_image_of_isPullback`

English:
lemma image_preimage_eq_preimage_image_of_isPullback
  statement: {X Y U V : Scheme.{u}}
  proof: by
  ext x
  by_cases hx : x in Set.range iU
  · obtain ⟨x, rfl⟩ := hx
    simp only [SetLike.mem_coe, Opens.map_coe, Set.mem_preimage, ← Scheme.Hom.comp_apply, ← H.w]
    simp
  · constructor
    · rintro ⟨x, hx, rfl⟩; cases hx ⟨x, rfl⟩
    · rintro ⟨y, hy, e : iV y = f x⟩
      obtain ⟨x, rfl⟩ := 

中文:
引理 image_preimage_eq_preimage_image_of_isPullback
  结论: {X Y U V : 概形.{u}}
  证明: by
  ext x
  by_cases hx : x in Set.range iU
  · obtain ⟨x, rfl⟩ := hx
    simp only [SetLike.mem_coe, Opens.map_coe, Set.mem_preimage, ← Scheme.Hom.comp_apply, ← H.w]
    simp
  · constructor
    · rintro ⟨x, hx, rfl⟩; cases hx ⟨x, rfl⟩
    · rintro ⟨y, hy, e : iV y = f x⟩
      obtain ⟨x, rfl⟩ := 

Depends on / 依赖: H.isoPullback_inv_snd, IsOpenImmersion, IsOpenImmersion.range_pullbackSnd, Opens.map_coe, Scheme, Scheme.Hom.comp_apply, Set.mem_preimage, Set.range, SetLike, SetLike.mem_coe, comp_apply, isoPullback_inv_snd, map_coe, mem_coe, mem_preimage, range_pullbackSnd
-/
lemma image_preimage_eq_preimage_image_of_isPullback {X Y U V : Scheme.{u}}
    {f : X ⟶ Y} {f' : U ⟶ V} {iU : U ⟶ X} {iV : V ⟶ Y} [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) (W : V.Opens) : iU ''ᵁ f' ⁻¹ᵁ W = f ⁻¹ᵁ iV ''ᵁ W := by
  ext x
  by_cases hx : x in Set.range iU
  · obtain ⟨x, rfl⟩ := hx
    simp only [SetLike.mem_coe, Opens.map_coe, Set.mem_preimage, ← Scheme.Hom.comp_apply, ← H.w]
    simp
  · constructor
    · rintro ⟨x, hx, rfl⟩; cases hx ⟨x, rfl⟩
    · rintro ⟨y, hy, e : iV y = f x⟩
      obtain ⟨x, rfl⟩ := (IsOpenImmersion.range_pullbackSnd iV f).ge ⟨y, e⟩
      rw [← H.isoPullback_inv_snd] at hx
      cases hx ⟨_, rfl⟩

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (H' : Set.range g subseteq Set.range f)
  body: ⟨LocallyRingedSpace.IsOpenImmersion.lift f.toLRSHom g.toLRSHom H'⟩

@[reassoc (attr := simp)]

中文:
定义 lift
  签名: (H' : 集合.range g subseteq 集合.range f)
  定义体: ⟨LocallyRingedSpace.IsOpenImmersion.lift f.toLRSHom g.toLRSHom H'⟩

@[reassoc (attr := simp)]

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion.lift, f.toLRSHom, g.toLRSHom, toLRSHom
-/
def lift (H' : Set.range g subseteq Set.range f) : Y ⟶ X :=
  ⟨LocallyRingedSpace.IsOpenImmersion.lift f.toLRSHom g.toLRSHom H'⟩

@[reassoc (attr := simp)]
/--
theorem `lift_fac` / 定理 `lift_fac`

English:
theorem lift_fac
  given: (H' : Set.range g subseteq Set.range f)
  statement: lift f g H' ≫ f = g
  proof: Scheme.Hom.ext' LocallyRingedSpace.IsOpenImmersion.lift_fac f.toLRSHom g.toLRSHom H'

中文:
定理 lift_fac
  条件: (H' : 集合.range g subseteq 集合.range f)
  结论: lift f g H' ≫ f = g
  证明: Scheme.Hom.ext' LocallyRingedSpace.IsOpenImmersion.lift_fac f.toLRSHom g.toLRSHom H'

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion.lift_fac, Scheme, Scheme.Hom.ext, f.toLRSHom, g.toLRSHom, lift_fac, toLRSHom
-/
theorem lift_fac (H' : Set.range g subseteq Set.range f) : lift f g H' ≫ f = g :=
Scheme.Hom.ext' LocallyRingedSpace.IsOpenImmersion.lift_fac f.toLRSHom g.toLRSHom H'

/--
theorem `lift_uniq` / 定理 `lift_uniq`

English:
theorem lift_uniq
  given: (H' : Set.range g subseteq Set.range f) (l : Y ⟶ X) (hl : l ≫ f = g)
  proof: Scheme.Hom.ext' LocallyRingedSpace.IsOpenImmersion.lift_uniq
    f.toLRSHom g.toLRSHom H' l.toLRSHom congr(($hl).toLRSHom)

@[reassoc]

中文:
定理 lift_uniq
  条件: (H' : 集合.range g subseteq 集合.range f) (l : Y ⟶ X) (hl : l ≫ f = g)
  证明: Scheme.Hom.ext' LocallyRingedSpace.IsOpenImmersion.lift_uniq
    f.toLRSHom g.toLRSHom H' l.toLRSHom congr(($hl).toLRSHom)

@[reassoc]

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion.lift_uniq, Scheme, Scheme.Hom.ext, f.toLRSHom, g.toLRSHom, l.toLRSHom, lift_uniq, toLRSHom
-/
theorem lift_uniq (H' : Set.range g subseteq Set.range f) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' :=
Scheme.Hom.ext' LocallyRingedSpace.IsOpenImmersion.lift_uniq
    f.toLRSHom g.toLRSHom H' l.toLRSHom congr(($hl).toLRSHom)

@[reassoc]
/--
lemma `comp_lift` / 引理 `comp_lift`

English:
lemma comp_lift
  given: {Y' : Scheme} (g' : Y' ⟶ Y) (H : Set.range g subseteq Set.range f)
  proof: by
  simp [← cancel_mono f]

中文:
引理 comp_lift
  条件: {Y' : 概形} (g' : Y' ⟶ Y) (H : 集合.range g subseteq 集合.range f)
  证明: by
  simp [← cancel_mono f]

Depends on / 依赖: cancel_mono
-/
lemma comp_lift {Y' : Scheme} (g' : Y' ⟶ Y) (H : Set.range g subseteq Set.range f) :
    g' ≫ lift f g H = lift f (g' ≫ g) (.trans (by simp [Set.range_comp_subset_range]) H) := by
  simp [← cancel_mono f]

/--
theorem `isPullback_lift_id` / 定理 `isPullback_lift_id`

English:
theorem isPullback_lift_id
  proof: by
  convert! IsPullback.of_id_snd.paste_horiz (IsKernelPair.id_of_mono g)
  · exact (Category.comp_id _).symm
  · simp

中文:
定理 isPullback_lift_id
  证明: by
  convert! IsPullback.of_id_snd.paste_horiz (IsKernelPair.id_of_mono g)
  · exact (Category.comp_id _).symm
  · simp

Depends on / 依赖: Category, Category.comp_id, IsKernelPair, IsKernelPair.id_of_mono, IsPullback, IsPullback.of_id_snd.paste_horiz, comp_id, convert, id_of_mono, of_id_snd, paste_horiz
-/
theorem isPullback_lift_id
    {X U Y : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [IsOpenImmersion g]
    (H : Set.range f subseteq Set.range g) :
    IsPullback (IsOpenImmersion.lift g f H) (𝟙 _) g f := by
  convert! IsPullback.of_id_snd.paste_horiz (IsKernelPair.id_of_mono g)
  · exact (Category.comp_id _).symm
  · simp

/--
Definition of `isoOfRangeEq` / `isoOfRangeEq` 的定义

English:
definition isoOfRangeEq
  signature: [IsOpenImmersion g] (e : Set.range f = Set.range g)
  body: lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

@[reassoc (attr := simp)]

中文:
定义 isoOfRangeEq
  签名: [是开浸入 g] (e : 集合.range f = 集合.range g)
  定义体: lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

@[reassoc (attr := simp)]

Depends on / 依赖: le_of_eq
-/
def isoOfRangeEq [IsOpenImmersion g] (e : Set.range f = Set.range g) : X ≅ Y where
  hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

@[reassoc (attr := simp)]
/--
lemma `isoOfRangeEq_hom_fac` / 引理 `isoOfRangeEq_hom_fac`

English:
lemma isoOfRangeEq_hom_fac
  statement: {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: lift_fac _ _ (le_of_eq e)

@[reassoc (attr := simp)]

中文:
引理 isoOfRangeEq_hom_fac
  结论: {X Y Z : 概形.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: lift_fac _ _ (le_of_eq e)

@[reassoc (attr := simp)]

Depends on / 依赖: le_of_eq, lift_fac
-/
lemma isoOfRangeEq_hom_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (e : Set.range f = Set.range g) :
    (isoOfRangeEq f g e).hom ≫ g = f :=
  lift_fac _ _ (le_of_eq e)

@[reassoc (attr := simp)]
/--
lemma `isoOfRangeEq_inv_fac` / 引理 `isoOfRangeEq_inv_fac`

English:
lemma isoOfRangeEq_inv_fac
  statement: {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: lift_fac _ _ (le_of_eq e.symm)

中文:
引理 isoOfRangeEq_inv_fac
  结论: {X Y Z : 概形.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: lift_fac _ _ (le_of_eq e.symm)

Depends on / 依赖: e.symm, le_of_eq, lift_fac
-/
lemma isoOfRangeEq_inv_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (e : Set.range f = Set.range g) :
    (isoOfRangeEq f g e).inv ≫ f = g :=
  lift_fac _ _ (le_of_eq e.symm)

/--
theorem `app_eq_invApp_app_of_comp_eq_aux` / 定理 `app_eq_invApp_app_of_comp_eq_aux`

English:
theorem app_eq_invApp_app_of_comp_eq_aux
  statement: {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
  proof: by
  simp_all

中文:
定理 app_eq_invApp_app_of_comp_eq_aux
  结论: {X Y U : 概形.{u}} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
  证明: by
  simp_all
-/
theorem app_eq_invApp_app_of_comp_eq_aux {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : U.Opens) :
    f ⁻¹ᵁ V = fg ⁻¹ᵁ (g ''ᵁ V) := by
  simp_all

set_option backward.isDefEq.respectTransparency false in
/--
theorem `app_eq_appIso_inv_app_of_comp_eq` / 定理 `app_eq_appIso_inv_app_of_comp_eq`

English:
theorem app_eq_appIso_inv_app_of_comp_eq
  statement: {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
  proof: by
  subst H
  rw [Scheme.Hom.comp_app]; rw [Category.assoc]; rw [Scheme.Hom.appIso_inv_app_assoc]; rw [f.naturality_assoc]; rw [← Functor.map_comp]; rw [← op_comp]; rw [Quiver.Hom.unop_op]; rw [eqToHom_map]; rw [eqToHom_trans]; rw [eqToHom_op]; rw [eqToHom_refl]; rw [CategoryTheory.Functor.map_id];

中文:
定理 app_eq_appIso_inv_app_of_comp_eq
  结论: {X Y U : 概形.{u}} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
  证明: by
  subst H
  rw [Scheme.Hom.comp_app]; rw [Category.assoc]; rw [Scheme.Hom.appIso_inv_app_assoc]; rw [f.naturality_assoc]; rw [← Functor.map_comp]; rw [← op_comp]; rw [Quiver.Hom.unop_op]; rw [eqToHom_map]; rw [eqToHom_trans]; rw [eqToHom_op]; rw [eqToHom_refl]; rw [CategoryTheory.Functor.map_id];

Depends on / 依赖: Category, Category.assoc, Category.comp_id, CategoryTheory, CategoryTheory.Functor.map_id, Functor, Functor.map_comp, Quiver, Quiver.Hom.unop_op, Scheme, Scheme.Hom.appIso_inv_app_assoc, Scheme.Hom.comp_app, appIso_inv_app_assoc, comp_app, comp_id, eqToHom_map, eqToHom_op, eqToHom_refl, eqToHom_trans, f.naturality_assoc
-/
theorem app_eq_appIso_inv_app_of_comp_eq {X Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : U.Opens) :
    f.app V = (g.appIso V).inv ≫ fg.app (g ''ᵁ V) ≫ Y.presheaf.map
      (eqToHom <| IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux f g fg H V).op := by
  subst H
  rw [Scheme.Hom.comp_app]; rw [Category.assoc]; rw [Scheme.Hom.appIso_inv_app_assoc]; rw [f.naturality_assoc]; rw [← Functor.map_comp]; rw [← op_comp]; rw [Quiver.Hom.unop_op]; rw [eqToHom_map]; rw [eqToHom_trans]; rw [eqToHom_op]; rw [eqToHom_refl]; rw [CategoryTheory.Functor.map_id]; rw [Category.comp_id]

/--
theorem `lift_app` / 定理 `lift_app`

English:
theorem lift_app
  statement: {X Y U : Scheme.{u}} (f : U ⟶ Y) (g : X ⟶ Y) [IsOpenImmersion f] (H)
  proof: IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq _ _ _ (lift_fac _ _ _).symm _

中文:
定理 lift_app
  结论: {X Y U : 概形.{u}} (f : U ⟶ Y) (g : X ⟶ Y) [是开浸入 f] (H)
  证明: IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq _ _ _ (lift_fac _ _ _).symm _

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq, app_eq_appIso_inv_app_of_comp_eq, lift_fac
-/
theorem lift_app {X Y U : Scheme.{u}} (f : U ⟶ Y) (g : X ⟶ Y) [IsOpenImmersion f] (H)
    (V : U.Opens) :
    (lift f g H).app V = (f.appIso V).inv ≫ g.app (f ''ᵁ V) ≫
      X.presheaf.map (eqToHom <| app_eq_invApp_app_of_comp_eq_aux _ _ _ (lift_fac ..).symm V).op :=
  IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq _ _ _ (lift_fac _ _ _).symm _

/--
lemma `isPullback` / 引理 `isPullback`

English:
lemma isPullback
  statement: {U V X Y : Scheme.{u}} (g : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) (f : X ⟶ Y)
  proof: by
  let e := IsOpenImmersion.isoOfRangeEq (pullback.snd iV f) iU
    (by simpa [range_pullbackSnd] using congr(($H').1))
  convert!
    (IsPullback.of_horiz_isIso
          (show CommSq e.inv iU (pullback.snd iV f) (𝟙 X) from ⟨by simp [e]⟩)).paste_horiz
      (IsPullback.of_hasPullback iV f)
  simp

中文:
引理 isPullback
  结论: {U V X Y : 概形.{u}} (g : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) (f : X ⟶ Y)
  证明: by
  let e := IsOpenImmersion.isoOfRangeEq (pullback.snd iV f) iU
    (by simpa [range_pullbackSnd] using congr(($H').1))
  convert!
    (IsPullback.of_horiz_isIso
          (show CommSq e.inv iU (pullback.snd iV f) (𝟙 X) from ⟨by simp [e]⟩)).paste_horiz
      (IsPullback.of_hasPullback iV f)
  simp

Depends on / 依赖: CommSq, IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, IsPullback, IsPullback.of_hasPullback, IsPullback.of_horiz_isIso, cancel_mono, condition, convert, e.inv, isoOfRangeEq, of_hasPullback, of_horiz_isIso, paste_horiz, pullback, pullback.condition, pullback.snd, range_pullbackSnd
-/
lemma isPullback {U V X Y : Scheme.{u}} (g : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) (f : X ⟶ Y)
    [IsOpenImmersion iU] [IsOpenImmersion iV] (H : iU ≫ f = g ≫ iV)
    (H' : f ⁻¹ᵁ iV.opensRange = iU.opensRange) : IsPullback g iU iV f := by
  let e := IsOpenImmersion.isoOfRangeEq (pullback.snd iV f) iU
    (by simpa [range_pullbackSnd] using congr(($H').1))
  convert!
    (IsPullback.of_horiz_isIso
          (show CommSq e.inv iU (pullback.snd iV f) (𝟙 X) from ⟨by simp [e]⟩)).paste_horiz
      (IsPullback.of_hasPullback iV f)
  simp [← cancel_mono iV, e, pullback.condition, H]

/-- If `f` is an open immersion `X ⟶ Y`, the global sections of `X`
are naturally isomorphic to the sections of `Y` over the image of `f`. -/
noncomputable
/--
Definition of `ΓIso` / `ΓIso` 的定义

English:
definition ΓIso
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens)
  body: (f.appIso (f ⁻¹ᵁ U)).symm ≪≫
    Y.presheaf.mapIso (eqToIso <| (f.image_preimage_eq_opensRange_inf U).symm).op

@[simp]

中文:
定义 ΓIso
  签名: {X Y : 概形.{u}} (f : X ⟶ Y) [是开浸入 f] (U : Y.Opens)
  定义体: (f.appIso (f ⁻¹ᵁ U)).symm ≪≫
    Y.presheaf.mapIso (eqToIso <| (f.image_preimage_eq_opensRange_inf U).symm).op

@[simp]

Depends on / 依赖: Y.presheaf.mapIso, appIso, eqToIso, f.appIso, f.image_preimage_eq_opensRange_inf, image_preimage_eq_opensRange_inf, mapIso, presheaf
-/
def ΓIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens) :
    Γ(X, f ⁻¹ᵁ U) ≅ Γ(Y, f.opensRange ⊓ U) :=
  (f.appIso (f ⁻¹ᵁ U)).symm ≪≫
    Y.presheaf.mapIso (eqToIso <| (f.image_preimage_eq_opensRange_inf U).symm).op

@[simp]
/--
lemma `ΓIso_inv` / 引理 `ΓIso_inv`

English:
lemma ΓIso_inv
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens)
  proof: by
  simp only [ΓIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, eqToHom_op,
    Iso.symm_inv, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

@[reassoc, elementwise]

中文:
引理 ΓIso_inv
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) [是开浸入 f] (U : Y.Opens)
  证明: by
  simp only [ΓIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, eqToHom_op,
    Iso.symm_inv, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

@[reassoc, elementwise]

Depends on / 依赖: Functor, Functor.mapIso_inv, Iso.op_inv, Iso.symm_inv, Iso.trans_inv, Scheme, Scheme.Hom.appIso_hom, Scheme.Hom.map_appLE, appIso_hom, eqToHom_op, eqToIso, eqToIso.inv, mapIso_inv, map_appLE, op_inv, symm_inv, trans_inv
-/
lemma ΓIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens) :
    (ΓIso f U).inv = f.appLE (f.opensRange ⊓ U) (f ⁻¹ᵁ U)
      (by rw [← f.image_preimage_eq_opensRange_inf, f.preimage_image_eq]) := by
  simp only [ΓIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, eqToHom_op,
    Iso.symm_inv, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

@[reassoc, elementwise]
/--
lemma `map_ΓIso_inv` / 引理 `map_ΓIso_inv`

English:
lemma map_ΓIso_inv
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens)
  proof: by
  simp [Scheme.Hom.appLE_eq_app]

@[reassoc, elementwise]

中文:
引理 map_ΓIso_inv
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) [是开浸入 f] (U : Y.Opens)
  证明: by
  simp [Scheme.Hom.appLE_eq_app]

@[reassoc, elementwise]

Depends on / 依赖: Scheme, Scheme.Hom.appLE_eq_app, appLE_eq_app
-/
lemma map_ΓIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens) :
    Y.presheaf.map (homOfLE inf_le_right).op ≫ (ΓIso f U).inv = f.app U := by
  simp [Scheme.Hom.appLE_eq_app]

@[reassoc, elementwise]
/--
lemma `app_ΓIso_hom` / 引理 `app_ΓIso_hom`

English:
lemma app_ΓIso_hom
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens)
  proof: by
  rw [← map_ΓIso_inv]
  simp [-ΓIso_inv]

中文:
引理 app_ΓIso_hom
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) [是开浸入 f] (U : Y.Opens)
  证明: by
  rw [← map_ΓIso_inv]
  simp [-ΓIso_inv]

Depends on / 依赖: A.obj, DecidableEq
-/
lemma app_ΓIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens) :
    f.app U ≫ (ΓIso f U).hom = Y.presheaf.map (homOfLE inf_le_right).op := by
  rw [← map_ΓIso_inv]
  simp [-ΓIso_inv]

/-- Given an open immersion `f : U ⟶ X`, the isomorphism between global sections
  of `U` and the sections of `X` at the image of `f`. -/
noncomputable
/--
Definition of `ΓIsoTop` / `ΓIsoTop` 的定义

English:
definition ΓIsoTop
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
  body: (f.appIso ⊤).symm ≪≫ Y.presheaf.mapIso (eqToIso f.image_top_eq_opensRange.symm).op

中文:
定义 ΓIsoTop
  签名: {X Y : 概形.{u}} (f : X ⟶ Y) [是开浸入 f]
  定义体: (f.appIso ⊤).symm ≪≫ Y.presheaf.mapIso (eqToIso f.image_top_eq_opensRange.symm).op

Depends on / 依赖: Y.presheaf.mapIso, appIso, eqToIso, f.appIso, f.image_top_eq_opensRange.symm, image_top_eq_opensRange, mapIso, presheaf
-/
def ΓIsoTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Γ(X, ⊤) ≅ Γ(Y, f.opensRange) :=
  (f.appIso ⊤).symm ≪≫ Y.presheaf.mapIso (eqToIso f.image_top_eq_opensRange.symm).op

instance {Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f]
    (H' : Set.range g subseteq Set.range f) [IsOpenImmersion g] :
    IsOpenImmersion (IsOpenImmersion.lift f g H') :=
  haveI : IsOpenImmersion (IsOpenImmersion.lift f g H' ≫ f) := by simpa
  IsOpenImmersion.of_comp _ f

end IsOpenImmersion

/--
lemma `isIso_of_isOpenImmersion_of_opensRange_eq_top` / 引理 `isIso_of_isOpenImmersion_of_opensRange_eq_top`

English:
lemma isIso_of_isOpenImmersion_of_opensRange_eq_top
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y)
  proof: by
  rw [isIso_iff_isOpenImmersion_and_epi_base]
  refine ⟨inferInstance, ?_⟩
  rw [TopCat.epi_iff_surjective]; rw [← Set.range_eq_univ]
  exact TopologicalSpace.Opens.ext_iff.mp hf

中文:
引理 isIso_of_isOpenImmersion_of_opensRange_eq_top
  结论: {X Y : 概形.{u}} (f : X ⟶ Y)
  证明: by
  rw [isIso_iff_isOpenImmersion_and_epi_base]
  refine ⟨inferInstance, ?_⟩
  rw [TopCat.epi_iff_surjective]; rw [← Set.range_eq_univ]
  exact TopologicalSpace.Opens.ext_iff.mp hf

Depends on / 依赖: Set.range_eq_univ, Subfunctor, TopCat, TopCat.epi_iff_surjective, TopologicalSpace, TopologicalSpace.Opens.ext_iff.mp, epi_iff_surjective, ext_iff, isIso_iff_isOpenImmersion_and_epi_base, range_eq_univ
-/
lemma isIso_of_isOpenImmersion_of_opensRange_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (hf : f.opensRange = ⊤) : IsIso f := by
  rw [isIso_iff_isOpenImmersion_and_epi_base]
  refine ⟨inferInstance, ?_⟩
  rw [TopCat.epi_iff_surjective]; rw [← Set.range_eq_univ]
  exact TopologicalSpace.Opens.ext_iff.mp hf

section MorphismProperty

/--
Instance `isOpenImmersion_isStableUnderComposition` / 实例 `isOpenImmersion_isStableUnderComposition`

English:
instance isOpenImmersion_isStableUnderComposition
  signature: :
  body: LocallyRingedSpace.IsOpenImmersion.comp f.toLRSHom g.toLRSHom

中文:
实例 isOpenImmersion_isStableUnderComposition
  签名: :
  定义体: LocallyRingedSpace.IsOpenImmersion.comp f.toLRSHom g.toLRSHom

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion.comp, f.toLRSHom, g.toLRSHom, toLRSHom
-/
instance isOpenImmersion_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @IsOpenImmersion where
  comp_mem f g _ _ := LocallyRingedSpace.IsOpenImmersion.comp f.toLRSHom g.toLRSHom

/--
Instance `isOpenImmersion_respectsIso` / 实例 `isOpenImmersion_respectsIso`

English:
instance isOpenImmersion_respectsIso
  signature: : MorphismProperty.RespectsIso @IsOpenImmersion
  body: by
  apply MorphismProperty.respectsIso_of_isStableUnderComposition
  intro _ _ f (hf : IsIso f)
  have : IsIso f := hf
  infer_instance

中文:
实例 isOpenImmersion_respectsIso
  签名: : MorphismProperty.RespectsIso @是开浸入
  定义体: by
  apply MorphismProperty.respectsIso_of_isStableUnderComposition
  intro _ _ f (hf : IsIso f)
  have : IsIso f := hf
  infer_instance

Depends on / 依赖: MorphismProperty, MorphismProperty.respectsIso_of_isStableUnderComposition, infer_instance, respectsIso_of_isStableUnderComposition
-/
instance isOpenImmersion_respectsIso : MorphismProperty.RespectsIso @IsOpenImmersion := by
  apply MorphismProperty.respectsIso_of_isStableUnderComposition
  intro _ _ f (hf : IsIso f)
  have : IsIso f := hf
  infer_instance

/--
Instance `isOpenImmersion_isMultiplicative` / 实例 `isOpenImmersion_isMultiplicative`

English:
instance isOpenImmersion_isMultiplicative
  signature: :
  body: inferInstance

中文:
实例 isOpenImmersion_isMultiplicative
  签名: :
  定义体: inferInstance
-/
instance isOpenImmersion_isMultiplicative :
    MorphismProperty.IsMultiplicative @IsOpenImmersion where
  id_mem _ := inferInstance

/--
Instance `isOpenImmersion_stableUnderBaseChange` / 实例 `isOpenImmersion_stableUnderBaseChange`

English:
instance isOpenImmersion_stableUnderBaseChange
  signature: :
  body: MorphismProperty.IsStableUnderBaseChange.mk' by
    intro X Y Z f g _ H; infer_instance

中文:
实例 isOpenImmersion_stableUnderBaseChange
  签名: :
  定义体: MorphismProperty.IsStableUnderBaseChange.mk' by
    intro X Y Z f g _ H; infer_instance

Depends on / 依赖: IsStableUnderBaseChange, MorphismProperty, MorphismProperty.IsStableUnderBaseChange.mk, infer_instance
-/
instance isOpenImmersion_stableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsOpenImmersion :=
MorphismProperty.IsStableUnderBaseChange.mk' by
    intro X Y Z f g _ H; infer_instance

end MorphismProperty

namespace Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f]

/--
theorem `image_basicOpen` / 定理 `image_basicOpen`

English:
theorem image_basicOpen
  given: {U : X.Opens} (r : Γ(X, U))
  proof: by
  have e := Scheme.preimage_basicOpen f ((f.appIso U).inv r)
  rw [Scheme.Hom.appIso_inv_app_apply]; rw [Scheme.basicOpen_res]; rw [inf_eq_right.mpr _] at e
  · rw [← e, f.image_preimage_eq_opensRange_inf, inf_eq_right]
    refine Set.Subset.trans (Scheme.basicOpen_le _ _) (Set.image_subset_range

中文:
定理 image_basicOpen
  条件: {U : X.Opens} (r : Γ(X, U))
  证明: by
  have e := Scheme.preimage_basicOpen f ((f.appIso U).inv r)
  rw [Scheme.Hom.appIso_inv_app_apply]; rw [Scheme.basicOpen_res]; rw [inf_eq_right.mpr _] at e
  · rw [← e, f.image_preimage_eq_opensRange_inf, inf_eq_right]
    refine Set.Subset.trans (Scheme.basicOpen_le _ _) (Set.image_subset_range

Depends on / 依赖: Scheme, Scheme.Hom.appIso_inv_app_apply, Scheme.basicOpen_le, Scheme.basicOpen_res, Scheme.preimage_basicOpen, Set.Subset.trans, Set.image_subset_range, Subset, X.basicOpen_le, appIso, appIso_inv_app_apply, basicOpen_le, basicOpen_res, f.appIso, f.image_preimage_eq_opensRange_inf, f.preimage_image_eq, image_preimage_eq_opensRange_inf, image_subset_range, inf_eq_right, inf_eq_right.mpr
-/
theorem image_basicOpen {U : X.Opens} (r : Γ(X, U)) :
    f ''ᵁ X.basicOpen r = Y.basicOpen ((f.appIso U).inv r) := by
  have e := Scheme.preimage_basicOpen f ((f.appIso U).inv r)
  rw [Scheme.Hom.appIso_inv_app_apply]; rw [Scheme.basicOpen_res]; rw [inf_eq_right.mpr _] at e
  · rw [← e, f.image_preimage_eq_opensRange_inf, inf_eq_right]
    refine Set.Subset.trans (Scheme.basicOpen_le _ _) (Set.image_subset_range _ _)
  · exact (X.basicOpen_le r).trans (f.preimage_image_eq _).ge

/--
lemma `image_zeroLocus` / 引理 `image_zeroLocus`

English:
lemma image_zeroLocus
  given: {U : X.Opens} (s : Set Γ(X, U))
  proof: by
  ext x
  by_cases hx : x in Set.range f
  · obtain ⟨x, rfl⟩ := hx
    simp [f.isOpenEmbedding.injective.mem_set_image, ← Scheme.image_basicOpen]
  · simp only [Set.mem_inter_iff, hx, and_false, iff_false]
    exact fun H => hx (Set.image_subset_range _ _ H)

中文:
引理 image_zeroLocus
  条件: {U : X.Opens} (s : 集合 Γ(X, U))
  证明: by
  ext x
  by_cases hx : x in Set.range f
  · obtain ⟨x, rfl⟩ := hx
    simp [f.isOpenEmbedding.injective.mem_set_image, ← Scheme.image_basicOpen]
  · simp only [Set.mem_inter_iff, hx, and_false, iff_false]
    exact fun H => hx (Set.image_subset_range _ _ H)

Depends on / 依赖: Scheme, Scheme.image_basicOpen, Set.image_subset_range, Set.mem_inter_iff, Set.range, and_false, f.isOpenEmbedding.injective.mem_set_image, iff_false, image_basicOpen, image_subset_range, injective, isOpenEmbedding, mem_inter_iff, mem_set_image
-/
lemma image_zeroLocus {U : X.Opens} (s : Set Γ(X, U)) :
    f '' X.zeroLocus s = Y.zeroLocus ((f.appIso U).inv.hom '' s) inter Set.range f := by
  ext x
  by_cases hx : x in Set.range f
  · obtain ⟨x, rfl⟩ := hx
    simp [f.isOpenEmbedding.injective.mem_set_image, ← Scheme.image_basicOpen]
  · simp only [Set.mem_inter_iff, hx, and_false, iff_false]
    exact fun H => hx (Set.image_subset_range _ _ H)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `stalkMapIsoOfIsPullback` / `stalkMapIsoOfIsPullback` 的定义

English:
definition stalkMapIsoOfIsPullback
  signature: {P X Y Z : Scheme.{u}}
  body: haveI : IsOpenImmersion fst := MorphismProperty.of_isPullback h.flip ‹_›
  Arrow.isoMk' _ _
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by rw [← hx, ← Scheme.Hom.comp_apply, h.w]; simp) ≪≫
      asIso (g.stalkMap (snd p)))
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by rw [hx]) ≪≫
      asIso (fst

中文:
定义 stalkMapIsoOfIsPullback
  签名: {P X Y Z : 概形.{u}}
  定义体: haveI : IsOpenImmersion fst := MorphismProperty.of_isPullback h.flip ‹_›
  Arrow.isoMk' _ _
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by rw [← hx, ← Scheme.Hom.comp_apply, h.w]; simp) ≪≫
      asIso (g.stalkMap (snd p)))
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by rw [hx]) ≪≫
      asIso (fst

Depends on / 依赖: cat_disch
-/
noncomputable def stalkMapIsoOfIsPullback {P X Y Z : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    [IsOpenImmersion g] (p : P) (x : X := fst p) (hx : fst p = x := by cat_disch) :
    Arrow.mk (f.stalkMap x) ≅ Arrow.mk (snd.stalkMap p) :=
  haveI : IsOpenImmersion fst := MorphismProperty.of_isPullback h.flip ‹_›
  Arrow.isoMk' _ _
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by rw [← hx, ← Scheme.Hom.comp_apply, h.w]; simp) ≪≫
      asIso (g.stalkMap (snd p)))
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by rw [hx]) ≪≫
      asIso (fst.stalkMap p))
    (by
      subst hx
      simp [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp,
        Scheme.Hom.stalkMap_congr_hom _ _ h.w])

end Scheme

end AlgebraicGeometry
