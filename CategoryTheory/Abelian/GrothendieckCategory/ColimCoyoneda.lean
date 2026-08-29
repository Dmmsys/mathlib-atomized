/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Morphisms to a colimit in a Grothendieck abelian category

Let `C : Type u` be an abelian category `[Category.{v} C]` which
satisfies `IsGrothendieckAbelian.{w} C`. We may expect
that all the objects `X : C` are `κ`-presentable for some regular
cardinal `κ`. However, we only prove a weaker result (which
is enough in order to obtain the existence of enough
injectives (TODO)): let `κ` be a big enough regular
cardinal such that if `Y : J ⥤ C` is a functor from
a `κ`-filtered category, and `c : Cocone Y` is a colimit cocone,
then the map from the colimit of the types `X ⟶ Y j` to
`X ⟶ c.pt` is injective, and it is bijective under the
additional assumption that for any map `f : j ⟶ j'` in `J`,
`Y.map f` is a monomorphism, see
`IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite

attribute [local instance] IsFiltered.isConnected

namespace IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {X : C} {J : Type w} [SmallCategory J]

namespace IsPresentable

variable {Y : J ⥤ C} {c : Cocone Y} (hc : IsColimit c)

namespace injectivity₀

variable {j₀ : J} (y : X ⟶ Y.obj j₀) (hy : y ≫ c.ι.app j₀ = 0)

/-!
Given `y : X ⟶ Y.obj j₀`, we introduce a natural
transformation `g : X ⟶ Y.obj t.right` for `t : Under j₀`.
We consider the kernel of this morphism: we have a natural exact sequence
`kernel (g y) ⟶ X ⟶ Y.obj t.right` for all `t : Under j₀`. Under the
assumption that the composition `y ≫ c.ι.app j₀ : X ⟶ c.pt` is zero,
we get that after passing to the colimit, the right map `X ⟶ c.pt` is
zero, which implies that the left map `f : colimit (kernel (g y)) ⟶ X`
is an epimorphism (see `epi_f`). If `κ` is a regular cardinal that is
bigger than the cardinality of `Subobject X` and `J` is `κ`-filtered,
it follows that for some `φ : j₀ ⟶ j` in `Under j₀`,
the inclusion `(kernel.ι (g y)).app j` is an isomorphism,
which implies that `y ≫ Y.map φ = 0` (see the lemma `injectivity₀`).
-/

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `X ⟶ Y.obj t.right` for `t : Under j₀`
that is induced by `y : X ⟶ Y.obj j₀`. -/
@[simps]
/--
Definition of `g` / `g` 的定义

English:
definition g
  signature: : (Functor.const _).obj X ⟶ Under.forget j₀ ⋙ Y where
  body: y ≫ Y.map t.hom
  naturality t₁ t₂ f := by
    dsimp
    simp only [Category.id_comp, Category.assoc, ← Functor.map_comp, Under.w]

中文:
定义 g
  签名: : (函子.const _).obj X ⟶ Under.forget j₀ ⋙ Y where
  定义体: y ≫ Y.map t.hom
  naturality t₁ t₂ f := by
    dsimp
    simp only [Category.id_comp, Category.assoc, ← Functor.map_comp, Under.w]

Depends on / 依赖: Y.map, t.hom
-/
def g : (Functor.const _).obj X ⟶ Under.forget j₀ ⋙ Y where
  app t := y ≫ Y.map t.hom
  naturality t₁ t₂ f := by
    dsimp
    simp only [Category.id_comp, Category.assoc, ← Functor.map_comp, Under.w]

/--
Definition of `f` / `f` 的定义

English:
definition f
  signature: : colimit (kernel (g y)) ⟶ X
  body: IsColimit.map (colimit.isColimit _) (constCocone _ X) (kernel.ι _)

中文:
定义 f
  签名: : colimit (kernel (g y)) ⟶ X
  定义体: IsColimit.map (colimit.isColimit _) (constCocone _ X) (kernel.ι _)

Depends on / 依赖: IsColimit, IsColimit.map, colimit, colimit.isColimit, constCocone, isColimit, kernel
-/
noncomputable def f : colimit (kernel (g y)) ⟶ X :=
  IsColimit.map (colimit.isColimit _) (constCocone _ X) (kernel.ι _)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `hf` / 引理 `hf`

English:
lemma hf
  given: (j : Under j₀)
  proof: (IsColimit.ι_map _ _ _ _).trans (by simp)

中文:
引理 hf
  条件: (j : Under j₀)
  证明: (IsColimit.ι_map _ _ _ _).trans (by simp)

Depends on / 依赖: IsColimit
-/
lemma hf (j : Under j₀) :
    colimit.ι (kernel (g y)) j ≫ f y = (kernel.ι (g y)).app j :=
  (IsColimit.ι_map _ _ _ _).trans (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {y} in
include hc hy in
/--
lemma `epi_f` / 引理 `epi_f`

English:
lemma epi_f
  given: [IsFiltered J]
  statement: Epi (f y)
  proof: by
  exact (colim.exact_mapShortComplex
    ((ShortComplex.mk _ _ (kernel.condition (g y))).exact_of_f_is_kernel
      (kernelIsKernel (g y)))
    (colimit.isColimit _) (isColimitConstCocone _ _)
    ((Functor.Final.isColimitWhiskerEquiv (Under.forget j₀) c).symm hc) (f y) 0
    (fun j => by simpa using! hf y j)
    (fun _ => by simpa using! hy.symm)).epi_f rfl

中文:
引理 epi_f
  条件: [是Filtered J]
  结论: 满态射 (f y)
  证明: by
  exact (colim.exact_mapShortComplex
    ((ShortComplex.mk _ _ (kernel.condition (g y))).exact_of_f_is_kernel
      (kernelIsKernel (g y)))
    (colimit.isColimit _) (isColimitConstCocone _ _)
    ((Functor.Final.isColimitWhiskerEquiv (Under.forget j₀) c).symm hc) (f y) 0
    (fun j => by simpa using! hf y j)
    (fun _ => by simpa using! hy.symm)).epi_f rfl

Depends on / 依赖: Functor, Functor.Final.isColimitWhiskerEquiv, ShortComplex, ShortComplex.mk, Under.forget, colim.exact_mapShortComplex, colimit, colimit.isColimit, condition, epi_f, exact_mapShortComplex, exact_of_f_is_kernel, forget, hy.symm, isColimit, isColimitConstCocone, isColimitWhiskerEquiv, kernel, kernel.condition, kernelIsKernel
-/
lemma epi_f [IsFiltered J] : Epi (f y) := by
  exact (colim.exact_mapShortComplex
    ((ShortComplex.mk _ _ (kernel.condition (g y))).exact_of_f_is_kernel
      (kernelIsKernel (g y)))
    (colimit.isColimit _) (isColimitConstCocone _ _)
    ((Functor.Final.isColimitWhiskerEquiv (Under.forget j₀) c).symm hc) (f y) 0
    (fun j => by simpa using! hf y j)
    (fun _ => by simpa using! hy.symm)).epi_f rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The kernel of `g y` gives a family of subobjects of `X` indexed by `Under j₀`, and
we consider it as a functor `Under j₀ ⥤ MonoOver X`. -/
@[simps]
/--
Definition of `F` / `F` 的定义

English:
definition F
  signature: : Under j₀ ⥤ MonoOver X where
  body: MonoOver.mk ((kernel.ι (g y)).app j)
  map {j j'} f := MonoOver.homMk ((kernel (g y)).map f)

中文:
定义 F
  签名: : Under j₀ ⥤ MonoOver X where
  定义体: MonoOver.mk ((kernel.ι (g y)).app j)
  map {j j'} f := MonoOver.homMk ((kernel (g y)).map f)

Depends on / 依赖: MonoOver, MonoOver.mk, kernel
-/
noncomputable def F : Under j₀ ⥤ MonoOver X where
  obj j := MonoOver.mk ((kernel.ι (g y)).app j)
  map {j j'} f := MonoOver.homMk ((kernel (g y)).map f)

end injectivity₀

section

variable {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (hXκ : HasCardinalLT (Subobject X) κ)

include hXκ hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open injectivity₀ in
/--
lemma `injectivity₀` / 引理 `injectivity₀`

English:
lemma injectivity₀
  given: {j₀ : J} (y : X ⟶ Y.obj j₀) (hy : y ≫ c.ι.app j₀ = 0)
  proof: by
  have := isFiltered_of_isCardinalFiltered J κ
  obtain ⟨j, h⟩ := exists_isIso_of_functor_from_monoOver (F y) hXκ _
      (colimit.isColimit (kernel (g y))) (f y) (fun j => by simpa using! hf y j)
      (epi_f hc hy)
  dsimp at h
  refine ⟨j.right, j.hom, ?_⟩
  simpa only [← cancel_epi ((kernel.ι (g y)).app j), comp_zero]
    using! NatTrans.congr_app (kernel.condition (g y)) j

中文:
引理 injectivity₀
  条件: {j₀ : J} (y : X ⟶ Y.obj j₀) (hy : y ≫ c.ι.app j₀ = 0)
  证明: by
  have := isFiltered_of_isCardinalFiltered J κ
  obtain ⟨j, h⟩ := exists_isIso_of_functor_from_monoOver (F y) hXκ _
      (colimit.isColimit (kernel (g y))) (f y) (fun j => by simpa using! hf y j)
      (epi_f hc hy)
  dsimp at h
  refine ⟨j.right, j.hom, ?_⟩
  simpa only [← cancel_epi ((kernel.ι (g y)).app j), comp_zero]
    using! NatTrans.congr_app (kernel.condition (g y)) j

Depends on / 依赖: NatTrans, NatTrans.congr_app, cancel_epi, colimit, colimit.isColimit, comp_zero, condition, congr_app, epi_f, exists_isIso_of_functor_from_monoOver, isColimit, isFiltered_of_isCardinalFiltered, j.hom, j.right, kernel, kernel.condition
-/
lemma injectivity₀ {j₀ : J} (y : X ⟶ Y.obj j₀) (hy : y ≫ c.ι.app j₀ = 0) :
    exists (j : J) (φ : j₀ ⟶ j), y ≫ Y.map φ = 0 := by
  have := isFiltered_of_isCardinalFiltered J κ
  obtain ⟨j, h⟩ := exists_isIso_of_functor_from_monoOver (F y) hXκ _
      (colimit.isColimit (kernel (g y))) (f y) (fun j => by simpa using! hf y j)
      (epi_f hc hy)
  dsimp at h
  refine ⟨j.right, j.hom, ?_⟩
  simpa only [← cancel_epi ((kernel.ι (g y)).app j), comp_zero]
    using! NatTrans.congr_app (kernel.condition (g y)) j

/--
lemma `injectivity` / 引理 `injectivity`

English:
lemma injectivity
  statement: (j₀ : J) (y₁ y₂ : X ⟶ Y.obj j₀)
  proof: by
  obtain ⟨j, φ, hφ⟩ := injectivity₀ hc hXκ (y₁ - y₂)
    (by rw [Preadditive.sub_comp, sub_eq_zero, hy])
  exact ⟨j, φ, by simpa only [Preadditive.sub_comp, sub_eq_zero] using hφ⟩

中文:
引理 injectivity
  结论: (j₀ : J) (y₁ y₂ : X ⟶ Y.obj j₀)
  证明: by
  obtain ⟨j, φ, hφ⟩ := injectivity₀ hc hXκ (y₁ - y₂)
    (by rw [Preadditive.sub_comp, sub_eq_zero, hy])
  exact ⟨j, φ, by simpa only [Preadditive.sub_comp, sub_eq_zero] using hφ⟩

Depends on / 依赖: Preadditive, Preadditive.sub_comp, sub_comp, sub_eq_zero
-/
lemma injectivity (j₀ : J) (y₁ y₂ : X ⟶ Y.obj j₀)
    (hy : y₁ ≫ c.ι.app j₀ = y₂ ≫ c.ι.app j₀) :
    exists (j : J) (φ : j₀ ⟶ j), y₁ ≫ Y.map φ = y₂ ≫ Y.map φ := by
  obtain ⟨j, φ, hφ⟩ := injectivity₀ hc hXκ (y₁ - y₂)
    (by rw [Preadditive.sub_comp, sub_eq_zero, hy])
  exact ⟨j, φ, by simpa only [Preadditive.sub_comp, sub_eq_zero] using hφ⟩

end

namespace surjectivity

variable (z : X ⟶ c.pt)

/-!
Let `z : X ⟶ c.pt` (where `c` is a colimit cocone for `Y : J ⥤ C`).
We consider the pullback of `c.ι` and of the constant
map `(Functor.const J).map z`. If we assume that `c.ι` is a monomorphism,
then this pullback evaluated at `j : J` can be identified to a subobject of `X`
(this is the inverse image by `z` of `Y.obj j` considered as a subobject of `c.pt`).
This corresponds to a functor `F z : J ⥤ MonoOver X`, and when taking the colimit
(computed in `C`), we obtain an epimorphism
`f z : colimit (pullback c.ι ((Functor.const J).map z)) ⟶ X`
when `J` is filtered (see `epi_f`). If `κ` is a regular cardinal that is
bigger than the cardinality of `Subobject X` and `J` is `κ`-filtered,
we deduce that `z` factors as `X ⟶ Y.obj j ⟶ c.pt` for some `j`
(see the lemma `surjectivity`).
-/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor `J ⥤ MonoOver X` which sends `j : J` to the inverse image by `z : X ⟶ c.pt`
of the subobject `Y.obj j` of `c.pt`; it is defined here as the object in `MonoOver X`
corresponding to the monomorphism
`(pullback.snd c.ι ((Functor.const _).map z)).app j`. -/
@[simps]
/--
Definition of `F` / `F` 的定义

English:
definition F
  signature: [Mono c.ι]
  body: MonoOver.mk ((pullback.snd c.ι ((Functor.const _).map z)).app j)
  map {j j'} f := MonoOver.homMk ((pullback c.ι ((Functor.const _).map z)).map f)

中文:
定义 F
  签名: [单态射 c.ι]
  定义体: MonoOver.mk ((pullback.snd c.ι ((Functor.const _).map z)).app j)
  map {j j'} f := MonoOver.homMk ((pullback c.ι ((Functor.const _).map z)).map f)

Depends on / 依赖: Functor, Functor.const, MonoOver, MonoOver.mk, pullback, pullback.snd
-/
noncomputable def F [Mono c.ι] : J ⥤ MonoOver X where
  obj j := MonoOver.mk ((pullback.snd c.ι ((Functor.const _).map z)).app j)
  map {j j'} f := MonoOver.homMk ((pullback c.ι ((Functor.const _).map z)).map f)

/--
Definition of `f` / `f` 的定义

English:
definition f
  signature: : colimit (pullback c.ι ((Functor.const J).map z)) ⟶ X
  body: colimit.desc _ (Cocone.mk X
    { app j := (pullback.snd c.ι ((Functor.const _).map z)).app j })

中文:
定义 f
  签名: : colimit (pullback c.ι ((函子.const J).map z)) ⟶ X
  定义体: colimit.desc _ (Cocone.mk X
    { app j := (pullback.snd c.ι ((Functor.const _).map z)).app j })

Depends on / 依赖: Cocone, Cocone.mk, Functor, Functor.const, colimit, colimit.desc, pullback, pullback.snd
-/
noncomputable def f : colimit (pullback c.ι ((Functor.const J).map z)) ⟶ X :=
  colimit.desc _ (Cocone.mk X
    { app j := (pullback.snd c.ι ((Functor.const _).map z)).app j })

/--
lemma `hf` / 引理 `hf`

English:
lemma hf
  given: (j : J)
  proof: colimit.ι_desc _ _

include hc

中文:
引理 hf
  条件: (j : J)
  证明: colimit.ι_desc _ _

include hc

Depends on / 依赖: IsLeftAdjoint, colimit, preservesEpimorphisms_of_isLeftAdjoint
-/
lemma hf (j : J) :
    colimit.ι (pullback c.ι ((Functor.const J).map z)) j ≫ f z =
      (pullback.snd c.ι ((Functor.const J).map z)).app j :=
  colimit.ι_desc _ _

include hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_f` / 引理 `isIso_f`

English:
lemma isIso_f
  given: [IsFiltered J]
  statement: IsIso (f z)
  proof: by
  refine ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff ?_).1
    (MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback c.ι ((Functor.const _).map z)).map colim) ?_)
  · refine Arrow.isoMk (Iso.refl _)
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitConstCocone J X)) ?_
    dsimp
    ext j
    rw [Category.id_comp]; rw [ι_colimMap_assoc]; rw [colimit.comp_coconePointUniqueUpToIso_hom]; rw [constCocone_ι]; rw [NatTrans.id_app]; rw [Category.comp_id]
    apply hf
  · refine ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff ?_).2
      ((inferInstance : IsIso (𝟙 c.pt)))
    exact Arrow.isoMk (IsColimit.coconePointUniqueUpToIso (colimit.isColimit Y) hc)
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
        (isColimitConstCocone J c.pt))

中文:
引理 isIso_f
  条件: [是Filtered J]
  结论: 是同构 (f z)
  证明: by
  refine ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff ?_).1
    (MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback c.ι ((Functor.const _).map z)).map colim) ?_)
  · refine Arrow.isoMk (Iso.refl _)
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitConstCocone J X)) ?_
    dsimp
    ext j
    rw [Category.id_comp]; rw [ι_colimMap_assoc]; rw [colimit.comp_coconePointUniqueUpToIso_hom]; rw [constCocone_ι]; rw [NatTrans.id_app]; rw [Category.comp_id]
    apply hf
  · refine ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff ?_).2
      ((inferInstance : IsIso (𝟙 c.pt)))
    exact Arrow.isoMk (IsColimit.coconePointUniqueUpToIso (colimit.isColimit Y) hc)
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
        (isColimitConstCocone J c.pt))

Depends on / 依赖: Arrow.isoMk, Category, Category.comp_id, Category.id_comp, Faithful, Functor, Functor.const, IsColimit, IsColimit.coconePointUniqueUpToIso, IsPullback, IsPullback.of_hasPullback, Iso.refl, MorphismPrope, MorphismProperty, MorphismProperty.isomorphisms, MorphismProperty.of_isPullback, NatTrans, NatTrans.id_app, arrow_mk_iso_iff, coconePointUniqueUpToIso
-/
lemma isIso_f [IsFiltered J] : IsIso (f z) := by
  refine ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff ?_).1
    (MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback c.ι ((Functor.const _).map z)).map colim) ?_)
  · refine Arrow.isoMk (Iso.refl _)
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitConstCocone J X)) ?_
    dsimp
    ext j
    rw [Category.id_comp]; rw [ι_colimMap_assoc]; rw [colimit.comp_coconePointUniqueUpToIso_hom]; rw [constCocone_ι]; rw [NatTrans.id_app]; rw [Category.comp_id]
    apply hf
  · refine ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff ?_).2
      ((inferInstance : IsIso (𝟙 c.pt)))
    exact Arrow.isoMk (IsColimit.coconePointUniqueUpToIso (colimit.isColimit Y) hc)
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
        (isColimitConstCocone J c.pt))

/--
lemma `epi_f` / 引理 `epi_f`

English:
lemma epi_f
  given: [IsFiltered J]
  statement: Epi (f z)
  proof: by
  have := isIso_f hc z
  infer_instance

中文:
引理 epi_f
  条件: [是Filtered J]
  结论: 满态射 (f z)
  证明: by
  have := isIso_f hc z
  infer_instance

Depends on / 依赖: IsSplitEpi, evaluation, infer_instance, isIso_f
-/
lemma epi_f [IsFiltered J] : Epi (f z) := by
  have := isIso_f hc z
  infer_instance

end surjectivity

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
open surjectivity in
/--
lemma `surjectivity` / 引理 `surjectivity`

English:
lemma surjectivity
  statement: [forall (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)]
  proof: by
  have := isFiltered_of_isCardinalFiltered J κ
  have := hc.mono_ι_app_of_isFiltered
  have := NatTrans.mono_of_mono_app c.ι
  obtain ⟨j, _⟩ := exists_isIso_of_functor_from_monoOver (F z) hXκ _
    (colimit.isColimit _) (f z) (hf z) (epi_f hc z)
  refine ⟨j, inv ((F z).obj j).obj.hom ≫ (pullback.fst c.ι _).app j, ?_⟩
  dsimp
  rw [Category.assoc]; rw [IsIso.eq_inv_comp]; rw [← NatTrans.comp_app]; rw [pullback.condition]; rw [NatTrans.comp_app]; rw [Functor.const_map_app]

中文:
引理 surjectivity
  结论: [对任意 (j j' : J) (φ : j ⟶ j'), 单态射 (Y.map φ)]
  证明: by
  have := isFiltered_of_isCardinalFiltered J κ
  have := hc.mono_ι_app_of_isFiltered
  have := NatTrans.mono_of_mono_app c.ι
  obtain ⟨j, _⟩ := exists_isIso_of_functor_from_monoOver (F z) hXκ _
    (colimit.isColimit _) (f z) (hf z) (epi_f hc z)
  refine ⟨j, inv ((F z).obj j).obj.hom ≫ (pullback.fst c.ι _).app j, ?_⟩
  dsimp
  rw [Category.assoc]; rw [IsIso.eq_inv_comp]; rw [← NatTrans.comp_app]; rw [pullback.condition]; rw [NatTrans.comp_app]; rw [Functor.const_map_app]

Depends on / 依赖: Category, Category.assoc, Functor, Functor.const_map_app, IsIso.eq_inv_comp, NatTrans, NatTrans.comp_app, NatTrans.mono_of_mono_app, colimit, colimit.isColimit, comp_app, condition, const_map_app, epi_f, eq_inv_comp, exists_isIso_of_functor_from_monoOver, hc.mono_, isColimit, isFiltered_of_isCardinalFiltered, mono_of_mono_app
-/
lemma surjectivity [forall (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)]
    {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hXκ : HasCardinalLT (Subobject X) κ) (z : X ⟶ c.pt) :
    exists (j₀ : J) (y : X ⟶ Y.obj j₀), z = y ≫ c.ι.app j₀ := by
  have := isFiltered_of_isCardinalFiltered J κ
  have := hc.mono_ι_app_of_isFiltered
  have := NatTrans.mono_of_mono_app c.ι
  obtain ⟨j, _⟩ := exists_isIso_of_functor_from_monoOver (F z) hXκ _
    (colimit.isColimit _) (f z) (hf z) (epi_f hc z)
  refine ⟨j, inv ((F z).obj j).obj.hom ≫ (pullback.fst c.ι _).app j, ?_⟩
  dsimp
  rw [Category.assoc]; rw [IsIso.eq_inv_comp]; rw [← NatTrans.comp_app]; rw [pullback.condition]; rw [NatTrans.comp_app]; rw [Functor.const_map_app]

end IsPresentable

open IsPresentable in
/--
lemma `preservesColimit_coyoneda_obj_of_mono` / 引理 `preservesColimit_coyoneda_obj_of_mono`

English:
lemma preservesColimit_coyoneda_obj_of_mono
  proof: ⟨by
    have := isFiltered_of_isCardinalFiltered J κ
    exact Types.FilteredColimit.isColimitOf' _ _
      (surjectivity hc hXκ) (injectivity hc hXκ)⟩

中文:
引理 preservesColimit_coyoneda_obj_of_mono
  证明: ⟨by
    have := isFiltered_of_isCardinalFiltered J κ
    exact Types.FilteredColimit.isColimitOf' _ _
      (surjectivity hc hXκ) (injectivity hc hXκ)⟩

Depends on / 依赖: FilteredColimit, Types.FilteredColimit.isColimitOf, injectivity, isColimitOf, isFiltered_of_isCardinalFiltered, surjectivity
-/
lemma preservesColimit_coyoneda_obj_of_mono
    (Y : J ⥤ C) {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
    [IsCardinalFiltered J κ] (hXκ : HasCardinalLT (Subobject X) κ)
    [forall (j j' : J) (φ : j ⟶ j'), Mono (Y.map φ)] :
    PreservesColimit Y ((coyoneda.obj (op X))) where
  preserves {c} hc := ⟨by
    have := isFiltered_of_isCardinalFiltered J κ
    exact Types.FilteredColimit.isColimitOf' _ _
      (surjectivity hc hXκ) (injectivity hc hXκ)⟩

end IsGrothendieckAbelian

end CategoryTheory
