/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
module

public import Mathlib.Algebra.Category.Ring.EqualizerPushout
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.Category.TopCat.EffectiveEpi
public import Mathlib.CategoryTheory.EffectiveEpi.Preserves

/-!
# Effective epimorphisms in the category of schemes

We collect results about effective epimorphisms in the category of schemes.

## Main results

For a surjective and flat morphism `π : X ⟶ Y` between affine schemes, we prove the following.
* `exists_comp_eq_of_flat_of_isAffine`: Any morphism `f : X ⟶ S` of schemes whose two pullbacks to
  `X ×[Y] X` agree descends to a morphism `u : Y ⟶ S` with `π ≫ u = f`.
* `isRegularEpi_of_flat_of_surjective_of_isAffine`: The map `π : X ⟶ Y` is a regular epimorphism
  in the category of schemes. This implies `EffectiveEpi π` by `inferInstance`.

For the general result that a quasi-compact, surjective and flat morphism is an effective
epimorphism, see the file `Mathlib.AlgebraicGeometry.Sites.Fpqc`.

## Reference

* https://stacks.math.columbia.edu/tag/023Q

-/

public section

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

section Scheme

/-- The underlying continuous map of a flat, surjective and quasi-compact morphism of schemes is an
effective epimorphism in the category of topological spaces. -/
/-
**AlgebraicGeometry.effectiveEpi_base_of_flat** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
icGeometry`。
形式化陈述：effectiveEpi_base_of_flat {X Y : Scheme.{u}} {f : X ⟶ Y} [Flat f] [Surject
ive f] [QuasiCompact f] : EffectiveEpi f.base
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.effectiveEpi_iff_isQuotientMap`：effectiveEpi_iff_isQuotientMap {B
 X : TopCat.{u}} (π : X ⟶ B) : EffectiveEpi π ↔ IsQuotientMap π
· 使用引理 `AlgebraicGeometry.Flat.isQuotientMap_of_surjective`：isQuotientMap_of_sur
jective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f] [Surjective f] 
: Topology.IsQuotientMap f

--- 原说明 ---
The underlying continuous map of a flat, surjective and quasi-compact morphism o
f schemes is an
effective epimorphism in the category of topological spaces.
-/
instance effectiveEpi_base_of_flat {X Y : Scheme.{u}} {f : X ⟶ Y} [Flat f] [Surjective f]
    [QuasiCompact f] : EffectiveEpi f.base := by
  rw [TopCat.effectiveEpi_iff_isQuotientMap]
  exact Flat.isQuotientMap_of_surjective _

namespace EffectiveEpiConstruction

/-- If `π : X ⟶ Y` is a surjective and flat morphism between affine schemes, then any morphism
`f : X ⟶ S` to an affine scheme `S` whose two pullbacks to `X ×[Y] X` agree descends to a morphism
`u : Y ⟶ S` with `π ≫ u = f`. -/
/-
**AlgebraicGeometry.EffectiveEpiConstruction.of_isAffine_target** 是 Mathlib 中的一个
引理，位于命名空间 `AlgebraicGeometry.EffectiveEpiConstruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `π : X ⟶ Y` is a surjective and flat morphism between affine schemes, then an
y morphism
`f : X ⟶ S` to an affine scheme `S` whose two pullbacks to `X ×[Y] X` agree desc
ends to a morphism
`u : Y ⟶ S` with `π ≫ u = f`.
-/
private lemma of_isAffine_target {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y)
    [Surjective π] [Flat π]
    (f : X ⟶ S) (hf : pullback.fst π π ≫ f = pullback.snd π π ≫ f)
    [IsAffine S] :
    ∃ u : Y ⟶ S, π ≫ u = f := by
  have : EffectiveEpi (AffineScheme.ofHom π) := by
    apply AffineScheme.equivCommRingCat.functor.effectiveEpi_of_map
    apply CommRingCat.Opposite.effectiveEpi_of_faithfullyFlat
    exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine π).mp ⟨‹_›, ‹_›⟩
  obtain ⟨u, hu⟩ := IsRegularEpi.exists_of_isKernelPair
    (AffineScheme.ofHom π)
    (IsPullback.of_map (f := AffineScheme.ofHom (pullback.fst π π)) (AffineScheme.forgetToScheme)
      (InducedCategory.Hom.ext pullback.condition) (.of_hasPullback _ _))
    (AffineScheme.ofHom f) (InducedCategory.Hom.ext hf)
  use u.hom, InducedCategory.Hom.ext_iff.mp hu

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open pullback in
/-- If `π : X ⟶ Y` is surjective and flat between affine schemes, then any morphism `f : X ⟶ S` of
schemes whose two pullbacks to `X ×[Y] X` agree descends Zariski locally on `Y`: there exists an
open cover `𝒰` of `Y` such that for each `i` there is `u : 𝒰.X i ⟶ S` with
`pullback.fst π (𝒰.f i) ≫ f = pullback.snd π (𝒰.f i) ≫ u`. -/
/-
**AlgebraicGeometry.EffectiveEpiConstruction.exists_openCover_exists** 是 Mathlib
 中的一个引理，位于命名空间 `AlgebraicGeometry.EffectiveEpiConstruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `π : X ⟶ Y` is surjective and flat between affine schemes, then any morphism 
`f : X ⟶ S` of
schemes whose two pullbacks to `X ×[Y] X` agree descends Zariski locally on `Y`:
 there exists an
open cover `𝒰` of `Y` such that for each `i` there is `u : 𝒰.X i ⟶ S` with
`pullback.fst π (𝒰.f i) ≫ f = pullback.snd π (𝒰.f i) ≫ u`.
-/
private lemma exists_openCover_exists {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y)
    [Surjective π] [Flat π]
    (f : X ⟶ S) (hf : pullback.fst π π ≫ f = pullback.snd π π ≫ f) :
    ∃ (𝒰 : OpenCover.{u} Y),
      ∀ i : 𝒰.I₀, ∃ (u : 𝒰.X i ⟶ S), pullback.fst π (𝒰.f i) ≫ f = pullback.snd _ _ ≫ u := by
  obtain ⟨b, hfac⟩ : ∃ (u : Y.carrier ⟶ S.carrier), π.base ≫ u = f.base := by
    apply IsRegularEpi.exists_of_isKernelPair _ (IsPullback.of_hasPullback _ _)
    have := congr(Scheme.forgetToTop.map $hf)
    rwa [Functor.map_comp, Functor.map_comp, ← pullbackComparison_comp_fst_assoc,
      ← pullbackComparison_comp_snd_assoc, cancel_epi] at this
  let 𝒰 := Y.openCoverOfIsOpenCover _ <| Y.isBasis_affineOpens.isOpenCover_mem_and_le
    (S.isBasis_affineOpens.isOpenCover.comap b.hom)
  refine ⟨𝒰, fun i ↦ ?_⟩
  have : IsAffine (𝒰.X i) := i.2.1
  let f' : pullback π (𝒰.f i) ⟶ i.1.2.1 := by
    apply IsOpenImmersion.lift (Scheme.Opens.ι i.1.2.1) (pullback.fst _ _ ≫ f)
    dsimp
    rw [← hfac, ← TopCat.coe_comp, ← Scheme.Hom.comp_base_assoc, pullback.condition]
    simp only [Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp,
      range_eq_univ, Set.image_univ, Opens.range_ι, Set.image_subset_iff]
    exact trans (by simp [𝒰]) i.2.2
  have h1 : fst (snd π (𝒰.f i)) _ ≫ fst _ _ = map _ _ _ _ (fst _ _) (fst _ _) _
    condition.symm condition.symm ≫ fst π π := by simp
  have h2 : snd (snd π (𝒰.f i)) _ ≫ fst _ _ = map _ _ _ _ (fst _ _) (fst _ _) _
    condition.symm condition.symm ≫ snd π π := by simp
  obtain ⟨u, hu⟩ := of_isAffine_target (pullback.snd π (𝒰.f i)) f' <| by
    simp only [← cancel_mono (Scheme.Opens.ι i.1.2.1),
      Category.assoc, IsOpenImmersion.lift_fac, f', reassoc_of% h1, reassoc_of% h2, hf]
  refine ⟨u ≫ Scheme.Opens.ι _, ?_⟩
  simp [reassoc_of% hu, f']

end EffectiveEpiConstruction

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `π : X ⟶ Y` is a flat and surjective morphism between affine schemes, then `π` is a
regular epimorphism in the category of schemes. -/
@[stacks 023Q]
/-
**AlgebraicGeometry.isRegularEpi_of_flat_of_surjective_of_isAffine** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isRegularEpi_of_flat_of_surjective_of_isAffine {X Y : Scheme.{u}} [IsAffin
e X] [IsAffine Y] (π : X ⟶ Y) [Surjective π] [Flat π] : IsRegularEpi π
参数：π : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Flat.epi_of_flat_of_surjective`：epi_of_flat_of_surject
ive (f : X ⟶ Y) [Flat f] [Surjective f] : Epi f
· 使用定理 `CategoryTheory.IsRegularEpi.of_epi_of_exists`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X B : C} {f : X ⟶ B}   [inst_1 : CategoryTheo
ry.Limits.HasPullback f f] [Catego…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `_private.Mathlib.AlgebraicGeometry.EffectiveEpi.0.AlgebraicGeometry.Effe
ctiveEpiConstruction.exists_openCover_exists`：∀ {X Y S : AlgebraicGeometry.Schem
e} [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y] (π : X ⟶ Y)   [
AlgebraicGeometry.Surjecti…
· 使用定理 `AlgebraicGeometry.Flat.instSndScheme`：∀ {X Y Z : AlgebraicGeometry.Schem
e} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.Flat f],   AlgebraicGeometry.Flat 
(CategoryTheory.Limits.pul…
· 使用定理 `AlgebraicGeometry.Surjective.instSndScheme`：∀ {X Y Z : AlgebraicGeometry
.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.Surjective f],   AlgebraicGe
ometry.Surjective (CategoryTheor…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.IsSplitEpi.EffectiveEpi`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {B X : C} (f : X ⟶ B) [CategoryTheory.IsSplitEpi 
f],   CategoryTheory.Effecti…
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullbackLeftPullbackSndIso_inv_snd_snd`：pullbackLe
ftPullbackSndIso_inv_snd_snd : (pullbackLeftPullbackSndIso f g g').inv ≫ pullbac
k.snd _ _ = pullback.snd _ _
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullbackLeftPullbackSndIso_inv_fst_assoc`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g : 
Y ⟶ Z) (g' : W ⟶ Y)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.Scheme.Cover.hom_ext`：hom_ext (𝒰 : OpenCover.{v} X) {Y
 : Scheme} (f₁ f₂ : X ⟶ Y) (h : forall x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms`：ι_glueMorphisms (𝒰 : Ope
nCover.{v} X) {Y : Scheme} (f : forall x, 𝒰.X x ⟶ Y) (hf : forall x y, pullback.
fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `π : X ⟶ Y` is a flat and surjective morphism between affine schemes, then `π
` is a
regular epimorphism in the category of schemes.
-/
lemma isRegularEpi_of_flat_of_surjective_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y) [Surjective π] [Flat π] :
    IsRegularEpi π := by
  have : Epi π := Flat.epi_of_flat_of_surjective _
  refine .of_epi_of_exists fun Z f hf ↦ ?_
  obtain ⟨𝒰, h⟩ := EffectiveEpiConstruction.exists_openCover_exists π f hf
  choose u hfac using h
  refine ⟨𝒰.glueMorphisms u ?_, ?_⟩
  · intro i j
    have : Epi (pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)) :=
      Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)),
      ← cancel_epi (pullback.congrHom rfl pullback.condition.symm).hom]
    conv_rhs =>
      simp only [pullback.congrHom_hom, limit.lift_π_assoc, PullbackCone.mk_pt, cospan_right,
      PullbackCone.mk_π_app, Category.comp_id]
    rw [← pullbackLeftPullbackSndIso_inv_snd_snd, Category.assoc,
      ← pullbackLeftPullbackSndIso_inv_snd_snd, Category.assoc, ← pullback.condition_assoc,
      ← hfac i, ← pullback.condition_assoc, ← hfac j]
    simp
  · apply Cover.hom_ext (𝒰.pullback₁ π)
    intro i
    simp [pullback.condition_assoc, hfac]

end Scheme

end AlgebraicGeometry

