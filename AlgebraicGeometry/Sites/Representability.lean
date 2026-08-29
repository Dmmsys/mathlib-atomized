/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.GluingOneHypercover
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Representability of schemes is a local property

In this file we prove that a sheaf of types `F` on `Sch` is representable if it is
locally representable.

## Main result
- `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`:
  Suppose
  * F is a `Type u`-valued sheaf on `Sch` with respect to the Zariski topology
  * X : ι → Sch is a family of schemes
  * f : Π i, yoneda.obj (X i) ⟶ F is a family of relatively representable open immersions
  * f is jointly surjective

  Then `F` is representable.

## References
* https://stacks.math.columbia.edu/tag/01JJ

-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory Category Limits Opposite

universe u

namespace Scheme

/-
Consider the following setup:
* F is `Type u`-valued a sheaf on `Sch` with respect to the Zariski topology
* X : ι → Sch is a family of schemes
* f : Π i, yoneda.obj (X i) ⟶ F is a family of relatively representable open immersions

Later, we will also assume:
* The family f is locally surjective with respect to the Zariski topology
-/
variable (F : Sheaf Scheme.zariskiTopology.{u} (Type u))
  {ι : Type u} {X : ι -> Scheme.{u}}
  (f : (i : ι) -> yoneda.obj (X i) ⟶ F.1) (hf : forall i, IsOpenImmersion.presheaf (f i))

namespace LocalRepresentability

variable {F f} (i j k : ι)

set_option backward.isDefEq.respectTransparency false in
open Functor.relativelyRepresentable in
/-- We get a family of gluing data by taking `U i = X i` and `V i j = (hf i).rep.pullback (f j)`. -/
@[simps]
/--
Definition of `glueData` / `glueData` 的定义

English:
definition glueData
  signature: : GlueData where
  body: ι
  U := X
  V := fun (i, j) => (hf i).rep.pullback (f j)
  f i j := (hf i).rep.fst' (f j)
  f_mono i j :=
    have := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip
    IsOpenImmersion.mono _
  f_id i := IsOpenImmersion.isIso_fst'_self IsOpenImmersion.le_monomorphisms (hf i)
  t i j := (hf

中文:
定义 glueData
  签名: : GlueData where
  定义体: ι
  U := X
  V := fun (i, j) => (hf i).rep.pullback (f j)
  f i j := (hf i).rep.fst' (f j)
  f_mono i j :=
    have := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip
    IsOpenImmersion.mono _
  f_id i := IsOpenImmersion.isIso_fst'_self IsOpenImmersion.le_monomorphisms (hf i)
  t i j := (hf
-/
noncomputable def glueData : GlueData where
  J := ι
  U := X
  V := fun (i, j) => (hf i).rep.pullback (f j)
  f i j := (hf i).rep.fst' (f j)
  f_mono i j :=
    have := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip
    IsOpenImmersion.mono _
  f_id i := IsOpenImmersion.isIso_fst'_self IsOpenImmersion.le_monomorphisms (hf i)
  t i j := (hf i).rep.symmetry (hf j).rep
  t_id i := by apply (hf i).rep.hom_ext' <;>
    simp [IsOpenImmersion.fst'_self_eq_snd IsOpenImmersion.le_monomorphisms (hf i)]
  t' i j k := lift₃ _ _ _ (pullback₃.p₂ _ _ _) (pullback₃.p₃ _ _ _) (pullback₃.p₁ _ _ _)
    (by simp) (by simp)
  t_fac i j k := (hf j).rep.hom_ext' (by simp) (by simp)
  cocycle i j k := pullback₃.hom_ext (by simp) (by simp) (by simp)
  f_open i j := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip

/--
Definition of `toGlued` / `toGlued` 的定义

English:
definition toGlued
  signature: (i : ι)
  body: (glueData hf).ι i

中文:
定义 toGlued
  签名: (i : ι)
  定义体: (glueData hf).ι i

Depends on / 依赖: glueData
-/
noncomputable def toGlued (i : ι) : X i ⟶ (glueData hf).glued :=
  (glueData hf).ι i

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOpenImmersion (toGlued hf i)
  body: inferInstanceAs (IsOpenImmersion ((glueData hf).ι i))

中文:
实例 :
  签名: IsOpenImmersion (toGlued hf i)
  定义体: inferInstanceAs (IsOpenImmersion ((glueData hf).ι i))

Depends on / 依赖: IsOpenImmersion, glueData
-/
instance : IsOpenImmersion (toGlued hf i) :=
  inferInstanceAs (IsOpenImmersion ((glueData hf).ι i))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `yonedaGluedToSheaf` / `yonedaGluedToSheaf` 的定义

English:
definition yonedaGluedToSheaf
  signature: :
  body: yonedaEquiv.symm
  -- This section is obtained from gluing the section corresponding to `f i : Hom(-, X i) ⟶ F`.
    ((glueData hf).sheafValGluedMk (fun i => yonedaEquiv (f i)) (by
      intro i j
      apply yonedaEquiv.symm.injective
      dsimp only [glueData_V, glueData_J, glueData_U, glueData_f

中文:
定义 yonedaGluedToSheaf
  签名: :
  定义体: yonedaEquiv.symm
  -- This section is obtained from gluing the section corresponding to `f i : Hom(-, X i) ⟶ F`.
    ((glueData hf).sheafValGluedMk (fun i => yonedaEquiv (f i)) (by
      intro i j
      apply yonedaEquiv.symm.injective
      dsimp only [glueData_V, glueData_J, glueData_U, glueData_f

Depends on / 依赖: yonedaEquiv, yonedaEquiv.symm
-/
noncomputable def yonedaGluedToSheaf :
    zariskiTopology.yoneda.obj (glueData hf).glued ⟶ F where
  -- The map is obtained by finding an object of `F((glueData hf).glued)`.
  hom := yonedaEquiv.symm
  -- This section is obtained from gluing the section corresponding to `f i : Hom(-, X i) ⟶ F`.
    ((glueData hf).sheafValGluedMk (fun i => yonedaEquiv (f i)) (by
      intro i j
      apply yonedaEquiv.symm.injective
      dsimp only [glueData_V, glueData_J, glueData_U, glueData_f, glueData_t]
      rw [yonedaEquiv_naturality]; rw [Equiv.symm_apply_apply]; rw [Functor.map_comp_apply]; rw [yonedaEquiv_naturality]; rw [yonedaEquiv_naturality]; rw [Equiv.symm_apply_apply]; rw [← Functor.map_comp_assoc]; rw [Functor.relativelyRepresentable.symmetry_fst]; rw [((hf i).rep.isPullback' (f j)).w]))

@[reassoc (attr := simp)]
/--
lemma `yoneda_toGlued_yonedaGluedToSheaf` / 引理 `yoneda_toGlued_yonedaGluedToSheaf`

English:
lemma yoneda_toGlued_yonedaGluedToSheaf
  given: (i : ι)
  proof: by
  apply yonedaEquiv.injective
  rw [yonedaGluedToSheaf]; rw [yonedaEquiv_apply]; rw [yonedaEquiv_apply]; rw [NatTrans.comp_app_apply]; rw [yoneda_map_app]
  simpa using! GlueData.sheafValGluedMk_val _ _ _ _

中文:
引理 yoneda_toGlued_yonedaGluedToSheaf
  条件: (i : ι)
  证明: by
  apply yonedaEquiv.injective
  rw [yonedaGluedToSheaf]; rw [yonedaEquiv_apply]; rw [yonedaEquiv_apply]; rw [NatTrans.comp_app_apply]; rw [yoneda_map_app]
  simpa using! GlueData.sheafValGluedMk_val _ _ _ _

Depends on / 依赖: GlueData, GlueData.sheafValGluedMk_val, NatTrans, NatTrans.comp_app_apply, comp_app_apply, injective, sheafValGluedMk_val, yonedaEquiv, yonedaEquiv.injective, yonedaEquiv_apply, yonedaGluedToSheaf, yoneda_map_app
-/
lemma yoneda_toGlued_yonedaGluedToSheaf (i : ι) :
    yoneda.map (toGlued hf i) ≫ (yonedaGluedToSheaf hf).hom = f i := by
  apply yonedaEquiv.injective
  rw [yonedaGluedToSheaf]; rw [yonedaEquiv_apply]; rw [yonedaEquiv_apply]; rw [NatTrans.comp_app_apply]; rw [yoneda_map_app]
  simpa using! GlueData.sheafValGluedMk_val _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `yonedaGluedToSheaf_app_toGlued` / 引理 `yonedaGluedToSheaf_app_toGlued`

English:
lemma yonedaGluedToSheaf_app_toGlued
  given: {i : ι}
  proof: by
  rw [← yoneda_toGlued_yonedaGluedToSheaf hf i]; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

中文:
引理 yonedaGluedToSheaf_app_toGlued
  条件: {i : ι}
  证明: by
  rw [← yoneda_toGlued_yonedaGluedToSheaf hf i]; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

Depends on / 依赖: yonedaEquiv_comp, yonedaEquiv_yoneda_map, yoneda_toGlued_yonedaGluedToSheaf
-/
lemma yonedaGluedToSheaf_app_toGlued {i : ι} :
    dsimp% (yonedaGluedToSheaf hf).hom.app _ (toGlued hf i) = yonedaEquiv (f i) := by
  rw [← yoneda_toGlued_yonedaGluedToSheaf hf i]; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `yonedaGluedToSheaf_app_comp` / 引理 `yonedaGluedToSheaf_app_comp`

English:
lemma yonedaGluedToSheaf_app_comp
  given: {V U : Scheme.{u}} (γ : V ⟶ U) (α : U ⟶ (glueData hf).glued)
  proof: ConcreteCategory.congr_hom ((yonedaGluedToSheaf hf).hom.naturality γ.op) α

中文:
引理 yonedaGluedToSheaf_app_comp
  条件: {V U : Scheme.{u}} (γ : V ⟶ U) (α : U ⟶ (glueData hf).glued)
  证明: ConcreteCategory.congr_hom ((yonedaGluedToSheaf hf).hom.naturality γ.op) α

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, hom.naturality, naturality, yonedaGluedToSheaf
-/
lemma yonedaGluedToSheaf_app_comp {V U : Scheme.{u}} (γ : V ⟶ U) (α : U ⟶ (glueData hf).glued) :
    dsimp% (yonedaGluedToSheaf hf).hom.app (op V) (γ ≫ α) =
      F.obj.map γ.op ((yonedaGluedToSheaf hf).hom.app (op U) α) :=
  ConcreteCategory.congr_hom ((yonedaGluedToSheaf hf).hom.naturality γ.op) α

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Presheaf.IsLocallySurjective
  signature: Scheme.zariskiTopology (Sigma.desc f)] :
  body: Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (show Sigma.desc (fun i => yoneda.map (toGlued hf i)) ≫
      (yonedaGluedToSheaf hf).hom = Sigma.desc f by cat_disch)

中文:
实例 [Presheaf.IsLocallySurjective
  签名: Scheme.zariskiTopology (Sigma.desc f)] :
  定义体: Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (show Sigma.desc (fun i => yoneda.map (toGlued hf i)) ≫
      (yonedaGluedToSheaf hf).hom = Sigma.desc f by cat_disch)

Depends on / 依赖: Presheaf, Presheaf.isLocallySurjective_of_isLocallySurjective_fac, Sigma.desc, cat_disch, isLocallySurjective_of_isLocallySurjective_fac, toGlued, yoneda, yoneda.map, yonedaGluedToSheaf
-/
instance [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)] :
    Sheaf.IsLocallySurjective (yonedaGluedToSheaf hf) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (show Sigma.desc (fun i => yoneda.map (toGlued hf i)) ≫
      (yonedaGluedToSheaf hf).hom = Sigma.desc f by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `comp_toGlued_eq` / 引理 `comp_toGlued_eq`

English:
lemma comp_toGlued_eq
  statement: {U : Scheme} {i j : ι} (a : U ⟶ X i) (b : U ⟶ X j)
  proof: by
  rw [← (hf i).rep.lift'_fst a b h]; rw [assoc]
  conv_rhs => rw [← (hf i).rep.lift'_snd a b h, assoc]
  congr 1
  exact ((glueData hf).glue_condition i j).symm.trans (by simp [toGlued])

@[simp]

中文:
引理 comp_toGlued_eq
  结论: {U : Scheme} {i j : ι} (a : U ⟶ X i) (b : U ⟶ X j)
  证明: by
  rw [← (hf i).rep.lift'_fst a b h]; rw [assoc]
  conv_rhs => rw [← (hf i).rep.lift'_snd a b h, assoc]
  congr 1
  exact ((glueData hf).glue_condition i j).symm.trans (by simp [toGlued])

@[simp]

Depends on / 依赖: _fst, _snd, conv_rhs, glueData, glue_condition, rep.lift, symm.trans, toGlued
-/
lemma comp_toGlued_eq {U : Scheme} {i j : ι} (a : U ⟶ X i) (b : U ⟶ X j)
    (h : yoneda.map a ≫ f i = yoneda.map b ≫ f j) :
    a ≫ toGlued hf i = b ≫ toGlued hf j := by
  rw [← (hf i).rep.lift'_fst a b h]; rw [assoc]
  conv_rhs => rw [← (hf i).rep.lift'_snd a b h, assoc]
  congr 1
  exact ((glueData hf).glue_condition i j).symm.trans (by simp [toGlued])

@[simp]
/--
lemma `glueData_openCover_map` / 引理 `glueData_openCover_map`

English:
lemma glueData_openCover_map
  statement: (glueData hf).openCover.f j = toGlued hf j
  proof: rfl

中文:
引理 glueData_openCover_map
  结论: (glueData hf).openCover.f j = toGlued hf j
  证明: rfl
-/
lemma glueData_openCover_map : (glueData hf).openCover.f j = toGlued hf j := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sheaf.IsLocallyInjective (yonedaGluedToSheaf hf)
  body: by
    rintro ⟨U⟩ (α β : U ⟶ _) h
    replace h : (yonedaGluedToSheaf hf).hom.app _ α = (yonedaGluedToSheaf hf).hom.app _ β := h
    have mem := (glueData hf).openCover.mem_grothendieckTopology
    refine GrothendieckTopology.superset_covering _ ?_
      (zariskiTopology.intersection_covering (zaris

中文:
实例 :
  签名: Sheaf.IsLocallyInjective (yonedaGluedToSheaf hf)
  定义体: by
    rintro ⟨U⟩ (α β : U ⟶ _) h
    replace h : (yonedaGluedToSheaf hf).hom.app _ α = (yonedaGluedToSheaf hf).hom.app _ β := h
    have mem := (glueData hf).openCover.mem_grothendieckTopology
    refine GrothendieckTopology.superset_covering _ ?_
      (zariskiTopology.intersection_covering (zaris

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.superset_covering, glueData, hom.app, intersection_covering, mem_grothendieckTopology, openCover, openCover.mem_grothendieckTopology, pullback_stable, replace, superset_covering, yonedaGluedToSheaf, zariskiTopology, zariskiTopology.intersection_covering, zariskiTopology.pullback_stable
-/
instance : Sheaf.IsLocallyInjective (yonedaGluedToSheaf hf) where
  equalizerSieve_mem := by
    rintro ⟨U⟩ (α β : U ⟶ _) h
    replace h : (yonedaGluedToSheaf hf).hom.app _ α = (yonedaGluedToSheaf hf).hom.app _ β := h
    have mem := (glueData hf).openCover.mem_grothendieckTopology
    refine GrothendieckTopology.superset_covering _ ?_
      (zariskiTopology.intersection_covering (zariskiTopology.pullback_stable α mem)
        (zariskiTopology.pullback_stable β mem))
    rintro V (γ : _ ⟶ U) ⟨⟨W₁, a, _, ⟨i⟩, fac₁⟩, ⟨W₂, b, _, ⟨j⟩, fac₂⟩⟩
    change γ ≫ α = γ ≫ β
    replace h : (yonedaGluedToSheaf hf).hom.app _ (γ ≫ α) =
        (yonedaGluedToSheaf hf).hom.app _ (γ ≫ β) := by dsimp at h; simp [h]
    rw [← fac₁]; rw [← fac₂] at h ⊢
    apply comp_toGlued_eq
    simpa [Scheme.GlueData.openCover_X, yonedaEquiv_naturality] using h

variable [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (yonedaGluedToSheaf hf)
  body: by
  rw [← Sheaf.isLocallyBijective_iff_isIso (yonedaGluedToSheaf hf)]
  constructor <;> infer_instance

中文:
实例 :
  签名: IsIso (yonedaGluedToSheaf hf)
  定义体: by
  rw [← Sheaf.isLocallyBijective_iff_isIso (yonedaGluedToSheaf hf)]
  constructor <;> infer_instance

Depends on / 依赖: Sheaf.isLocallyBijective_iff_isIso, infer_instance, isLocallyBijective_iff_isIso, yonedaGluedToSheaf
-/
instance : IsIso (yonedaGluedToSheaf hf) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (yonedaGluedToSheaf hf)]
  constructor <;> infer_instance

/--
Definition of `yonedaIsoSheaf` / `yonedaIsoSheaf` 的定义

English:
definition yonedaIsoSheaf
  signature: :
  body: asIso (yonedaGluedToSheaf hf)

中文:
定义 yonedaIsoSheaf
  签名: :
  定义体: asIso (yonedaGluedToSheaf hf)

Depends on / 依赖: yonedaGluedToSheaf
-/
noncomputable def yonedaIsoSheaf :
    zariskiTopology.yoneda.obj (glueData hf).glued ≅ F :=
  asIso (yonedaGluedToSheaf hf)

/--
Suppose
* F is a `Type u`-valued sheaf on `Sch` with respect to the Zariski topology
* X : ι → Sch is a family of schemes
* f : Π i, yoneda.obj (X i) ⟶ F is a family of relatively representable open immersions
* f is jointly surjective

Then `F` is representable, and the representing object is glued from the `X i`s
-/
noncomputable
/--
Definition of `representableBy` / `representableBy` 的定义

English:
definition representableBy
  signature: : F.1.RepresentableBy (glueData hf).glued
  body: Functor.representableByEquiv.symm ((sheafToPresheaf _ _).mapIso (yonedaIsoSheaf hf))


include hf in

中文:
定义 representableBy
  签名: : F.1.RepresentableBy (glueData hf).glued
  定义体: Functor.representableByEquiv.symm ((sheafToPresheaf _ _).mapIso (yonedaIsoSheaf hf))


include hf in

Depends on / 依赖: Functor, Functor.representableByEquiv.symm, mapIso, representableByEquiv, sheafToPresheaf, yonedaIsoSheaf
-/
def representableBy : F.1.RepresentableBy (glueData hf).glued :=
  Functor.representableByEquiv.symm ((sheafToPresheaf _ _).mapIso (yonedaIsoSheaf hf))


include hf in
/--
Suppose
* F is a `Type u`-valued sheaf on `Sch` with respect to the Zariski topology
* X : ι → Sch is a family of schemes
* f : Π i, yoneda.obj (X i) ⟶ F is a family of relatively representable open immersions
* f is jointly surjective

Then `F` is representable.
-/
@[stacks 01JJ]
/--
theorem `isRepresentable` / 定理 `isRepresentable`

English:
theorem isRepresentable
  statement: F.1.IsRepresentable
  proof: ⟨_, ⟨representableBy hf⟩⟩

中文:
定理 isRepresentable
  结论: F.1.IsRepresentable
  证明: ⟨_, ⟨representableBy hf⟩⟩

Depends on / 依赖: representableBy
-/
theorem isRepresentable : F.1.IsRepresentable :=
  ⟨_, ⟨representableBy hf⟩⟩

end LocalRepresentability

end Scheme

end AlgebraicGeometry
