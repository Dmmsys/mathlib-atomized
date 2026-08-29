/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided -- shake: keep (`example`)
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# `FDRep k G` is the category of finite-dimensional `k`-linear representations of `G`.

If `V : FDRep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with `Module k V` and `FiniteDimensional k V` instances.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We prove Schur's Lemma: the dimension of the `Hom`-space between two irreducible representation is
`0` if they are not isomorphic, and `1` if they are.
This is the content of `finrank_hom_simple_simple`

We verify that `FDRep k G` is a `k`-linear monoidal category, and rigid when `G` is a group.

`FDRep k G` has all finite limits.

## Implementation notes

We define `FDRep R G` for any ring `R` and monoid `G`,
as the category of finitely generated `R`-linear representations of `G`.

The main case of interest is when `R = k` is a field and `G` is a group,
and this is reflected in the documentation.

## TODO
* `FdRep k G ≌ FullSubcategory (FiniteDimensional k)`
* `FdRep k G` has all finite colimits.
* `FdRep k G` is abelian.
* `FdRep k G ≌ FGModuleCat k[G]`.

-/

@[expose] public section

suppress_compilation

universe u v

open CategoryTheory

open CategoryTheory.Limits


/--
Definition of `FDRep` / `FDRep` 的定义

English:
abbreviation FDRep
  signature: (R : Type u) (G : Type v) [Ring R] [Monoid G]
  body: Action (FGModuleCat.{u} R) G

中文:
缩写 FDRep
  签名: (R : 类型u) (G : 类型v) [Ring R] [Monoid G]
  定义体: Action (FGModuleCat.{u} R) G

Depends on / 依赖: Action, FGModuleCat
-/
abbrev FDRep (R : Type u) (G : Type v) [Ring R] [Monoid G] :=
  Action (FGModuleCat.{u} R) G

namespace FDRep

variable {R k : Type u} {G : Type v} [CommRing R] [Field k] [Monoid G]

example {G : Type u} [Monoid G] : LargeCategory (FDRep R G) := by infer_instance
example : ConcreteCategory (FDRep R G) (Action.HomSubtype _ _) := by infer_instance
example : Preadditive (FDRep R G) := by infer_instance
example : HasFiniteLimits (FDRep k G) := by infer_instance
example : Linear R (FDRep R G) := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (FDRep R G) (Type u)
  body: ⟨fun V => V.V⟩

example (V : FDRep R G) : Module.Finite R V := by infer_instance

中文:
实例 :
  签名: CoeSort (FDRep R G) (类型u)
  定义体: ⟨fun V => V.V⟩

example (V : FDRep R G) : Module.Finite R V := by infer_instance
-/
instance : CoeSort (FDRep R G) (Type u) :=
  ⟨fun V => V.V⟩

example (V : FDRep R G) : Module.Finite R V := by infer_instance

/-- All hom spaces are finite dimensional. -/
instance (V W : FDRep k G) : FiniteDimensional k (V ⟶ W) :=
  FiniteDimensional.of_injective ((forget₂ (FDRep k G) (FGModuleCat k)).mapLinearMap k)
    (Functor.map_injective (forget₂ (FDRep k G) (FGModuleCat k)))

/--
Definition of `ρ` / `ρ` 的定义

English:
definition ρ
  signature: (V : FDRep R G)
  body: (ModuleCat.endRingEquiv _).toMonoidHom.comp
    (InducedCategory.endEquiv.toMonoidHom.comp (Action.ρ V))

@[simp]

中文:
定义 ρ
  签名: (V : FDRep R G)
  定义体: (ModuleCat.endRingEquiv _).toMonoidHom.comp
    (InducedCategory.endEquiv.toMonoidHom.comp (Action.ρ V))

@[simp]

Depends on / 依赖: Action, InducedCategory, InducedCategory.endEquiv.toMonoidHom.comp, ModuleCat, ModuleCat.endRingEquiv, endEquiv, endRingEquiv, toMonoidHom, toMonoidHom.comp
-/
def ρ (V : FDRep R G) : G ->* V ->ₗ[R] V :=
  (ModuleCat.endRingEquiv _).toMonoidHom.comp
    (InducedCategory.endEquiv.toMonoidHom.comp (Action.ρ V))

@[simp]
/--
lemma `endRingEquiv_symm_comp_ρ` / 引理 `endRingEquiv_symm_comp_ρ`

English:
lemma endRingEquiv_symm_comp_ρ
  given: (V : FDRep R G)
  proof: rfl

中文:
引理 endRingEquiv_symm_comp_ρ
  条件: (V : FDRep R G)
  证明: rfl
-/
lemma endRingEquiv_symm_comp_ρ (V : FDRep R G) :
    (MonoidHomClass.toMonoidHom (ModuleCat.endRingEquiv V.V.obj).symm).comp (ρ V) =
      InducedCategory.endEquiv.toMonoidHom.comp (Action.ρ V) :=
  rfl

/--
lemma `endRingEquiv_comp_ρ` / 引理 `endRingEquiv_comp_ρ`

English:
lemma endRingEquiv_comp_ρ
  given: (V : FDRep R G)
  proof: rfl

@[simp]

中文:
引理 endRingEquiv_comp_ρ
  条件: (V : FDRep R G)
  证明: rfl

@[simp]
-/
lemma endRingEquiv_comp_ρ (V : FDRep R G) :
    (MonoidHomClass.toMonoidHom (ModuleCat.endRingEquiv V.V.obj)).comp
      (InducedCategory.endEquiv.toMonoidHom.comp (Action.ρ V)) = ρ V :=
  rfl

@[simp]
/--
lemma `hom_hom_action_ρ` / 引理 `hom_hom_action_ρ`

English:
lemma hom_hom_action_ρ
  given: (V : FDRep R G) (g : G)
  statement: (Action.ρ V g).hom.hom = (ρ V g)
  proof: rfl

中文:
引理 hom_hom_action_ρ
  条件: (V : FDRep R G) (g : G)
  结论: (Action.ρ V g).hom.hom = (ρ V g)
  证明: rfl
-/
lemma hom_hom_action_ρ (V : FDRep R G) (g : G) : (Action.ρ V g).hom.hom = (ρ V g) := rfl

/--
Definition of `isoToLinearEquiv` / `isoToLinearEquiv` 的定义

English:
definition isoToLinearEquiv
  signature: {V W : FDRep R G} (i : V ≅ W)
  body: FGModuleCat.isoToLinearEquiv ((Action.forget (FGModuleCat R) G).mapIso i)

中文:
定义 isoToLinearEquiv
  签名: {V W : FDRep R G} (i : V ≅ W)
  定义体: FGModuleCat.isoToLinearEquiv ((Action.forget (FGModuleCat R) G).mapIso i)

Depends on / 依赖: Action, Action.forget, FGModuleCat, FGModuleCat.isoToLinearEquiv, forget, isoToLinearEquiv, mapIso
-/
def isoToLinearEquiv {V W : FDRep R G} (i : V ≅ W) : V ≃ₗ[R] W :=
  FGModuleCat.isoToLinearEquiv ((Action.forget (FGModuleCat R) G).mapIso i)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `Iso.conj_ρ` / 定理 `Iso.conj_ρ`

English:
theorem Iso.conj_ρ
  given: {V W : FDRep R G} (i : V ≅ W) (g : G)
  proof: by
  rw [FDRep.isoToLinearEquiv]; rw [← hom_hom_action_ρ V]; rw [← FGModuleCat.Iso.conj_hom_eq_conj]; rw [Iso.conj_apply]; rw [← ModuleCat.hom_ofHom (W.ρ g)]; rw [← ModuleCat.hom_ext_iff]
  dsimp only [Action.forget_map, Functor.mapIso_hom]
  rw [i.hom.comm g]
  cat_disch

中文:
定理 Iso.conj_ρ
  条件: {V W : FDRep R G} (i : V ≅ W) (g : G)
  证明: by
  rw [FDRep.isoToLinearEquiv]; rw [← hom_hom_action_ρ V]; rw [← FGModuleCat.Iso.conj_hom_eq_conj]; rw [Iso.conj_apply]; rw [← ModuleCat.hom_ofHom (W.ρ g)]; rw [← ModuleCat.hom_ext_iff]
  dsimp only [Action.forget_map, Functor.mapIso_hom]
  rw [i.hom.comm g]
  cat_disch
-/
theorem Iso.conj_ρ {V W : FDRep R G} (i : V ≅ W) (g : G) :
    W.ρ g = (FDRep.isoToLinearEquiv i).conj (V.ρ g) := by
  rw [FDRep.isoToLinearEquiv]; rw [← hom_hom_action_ρ V]; rw [← FGModuleCat.Iso.conj_hom_eq_conj]; rw [Iso.conj_apply]; rw [← ModuleCat.hom_ofHom (W.ρ g)]; rw [← ModuleCat.hom_ext_iff]
  dsimp only [Action.forget_map, Functor.mapIso_hom]
  rw [i.hom.comm g]
  cat_disch

/-- Lift an unbundled representation to `FDRep`. -/
@[simps ρ]
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: {V : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V]
  body: ⟨FGModuleCat.of R V, (MulEquiv.toMonoidHom (MulEquiv.symm InducedCategory.endEquiv)).comp
    ((ModuleCat.endRingEquiv (ModuleCat.of R V)).symm.toMonoidHom.comp ρ)⟩

中文:
缩写 of
  签名: {V : 类型u} [AddCommGroup V] [Module R V] [Module.Finite R V]
  定义体: ⟨FGModuleCat.of R V, (MulEquiv.toMonoidHom (MulEquiv.symm InducedCategory.endEquiv)).comp
    ((ModuleCat.endRingEquiv (ModuleCat.of R V)).symm.toMonoidHom.comp ρ)⟩

Depends on / 依赖: FGModuleCat, FGModuleCat.of, InducedCategory, InducedCategory.endEquiv, ModuleCat, ModuleCat.endRingEquiv, ModuleCat.of, MulEquiv, MulEquiv.symm, MulEquiv.toMonoidHom, endEquiv, endRingEquiv, symm.toMonoidHom.comp, toMonoidHom
-/
abbrev of {V : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V]
    (ρ : Representation R G V) : FDRep R G :=
  ⟨FGModuleCat.of R V, (MulEquiv.toMonoidHom (MulEquiv.symm InducedCategory.endEquiv)).comp
    ((ModuleCat.endRingEquiv (ModuleCat.of R V)).symm.toMonoidHom.comp ρ)⟩

/-- This lemma is about `FDRep.ρ`, instead of `Action.ρ` for `of_ρ`. -/
@[simp]
/--
theorem `of_ρ'` / 定理 `of_ρ'`

English:
theorem of_ρ'
  given: {V : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V] (ρ : G ->* V ->ₗ[R] V)
  proof: rfl

中文:
定理 of_ρ'
  条件: {V : 类型u} [AddCommGroup V] [Module R V] [Module.Finite R V] (ρ : G ->* V ->ₗ[R] V)
  证明: rfl
-/
theorem of_ρ' {V : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V] (ρ : G ->* V ->ₗ[R] V) :
    (of ρ).ρ = ρ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ (FDRep R G) (Rep R G)
  body: (forget₂ (FGModuleCat R) (ModuleCat R)).mapAction G ⋙ Rep.ActionToRep R G

中文:
实例 :
  签名: HasForget₂ (FDRep R G) (Rep R G)
  定义体: (forget₂ (FGModuleCat R) (ModuleCat R)).mapAction G ⋙ Rep.ActionToRep R G

Depends on / 依赖: ActionToRep, FGModuleCat, ModuleCat, Rep.ActionToRep, mapAction
-/
instance : HasForget₂ (FDRep R G) (Rep R G) where
  forget₂ := (forget₂ (FGModuleCat R) (ModuleCat R)).mapAction G ⋙ Rep.ActionToRep R G

/--
theorem `forget₂_ρ` / 定理 `forget₂_ρ`

English:
theorem forget₂_ρ
  given: (V : FDRep R G)
  statement: ((forget₂ (FDRep R G) (Rep R G)).obj V).ρ = V.ρ
  proof: by
  ext g v; rfl

中文:
定理 forget₂_ρ
  条件: (V : FDRep R G)
  结论: ((forget₂ (FDRep R G) (Rep R G)).obj V).ρ = V.ρ
  证明: by
  ext g v; rfl
-/
theorem forget₂_ρ (V : FDRep R G) : ((forget₂ (FDRep R G) (Rep R G)).obj V).ρ = V.ρ := by
  ext g v; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsNoetherianRing
  signature: R] : PreservesFiniteLimits (forget₂ (FDRep R G) (Rep R G))
  body: Limits.comp_preservesFiniteLimits _ _

中文:
实例 [IsNoetherianRing
  签名: R] : PreservesFiniteLimits (forget₂ (FDRep R G) (Rep R G))
  定义体: Limits.comp_preservesFiniteLimits _ _

Depends on / 依赖: Limits, Limits.comp_preservesFiniteLimits, comp_preservesFiniteLimits
-/
instance [IsNoetherianRing R] : PreservesFiniteLimits (forget₂ (FDRep R G) (Rep R G)) :=
  Limits.comp_preservesFiniteLimits _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteColimits (forget₂ (FDRep R G) (Rep R G))
  body: Limits.comp_preservesFiniteColimits _ _

中文:
实例 :
  签名: PreservesFiniteColimits (forget₂ (FDRep R G) (Rep R G))
  定义体: Limits.comp_preservesFiniteColimits _ _

Depends on / 依赖: Limits, Limits.comp_preservesFiniteColimits, comp_preservesFiniteColimits
-/
instance : PreservesFiniteColimits (forget₂ (FDRep R G) (Rep R G)) :=
  Limits.comp_preservesFiniteColimits _ _

-- Verify that the monoidal structure is available.
example : MonoidalCategory (FDRep R G) := by infer_instance

example : MonoidalPreadditive (FDRep R G) := by infer_instance

example : MonoidalLinear R (FDRep R G) := by infer_instance

open Module

-- We need to provide this instance explicitly as otherwise `finrank_hom_simple_simple` gives a
-- deterministic timeout.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasKernels (FDRep k G)
  body: by infer_instance

中文:
实例 :
  签名: HasKernels (FDRep k G)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : HasKernels (FDRep k G) := by infer_instance

open scoped Classical in
/--
theorem `finrank_hom_simple_simple` / 定理 `finrank_hom_simple_simple`

English:
theorem finrank_hom_simple_simple
  given: [IsAlgClosed k] (V W : FDRep k G) [Simple V] [Simple W]
  proof: CategoryTheory.finrank_hom_simple_simple k V W

中文:
定理 finrank_hom_simple_simple
  条件: [IsAlgClosed k] (V W : FDRep k G) [Simple V] [Simple W]
  证明: CategoryTheory.finrank_hom_simple_simple k V W

Depends on / 依赖: CategoryTheory, CategoryTheory.finrank_hom_simple_simple, finrank_hom_simple_simple
-/
theorem finrank_hom_simple_simple [IsAlgClosed k] (V W : FDRep k G) [Simple V] [Simple W] :
    finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0 :=
  CategoryTheory.finrank_hom_simple_simple k V W

/--
Definition of `forget₂HomLinearEquiv` / `forget₂HomLinearEquiv` 的定义

English:
definition forget₂HomLinearEquiv
  signature: (X Y : FDRep R G)
  body: ⟨InducedCategory.homMk (ModuleCat.ofHom <| f.hom.toLinearMap), fun g => by
    ext1
    simp only [FGModuleCat.obj_carrier]
    exact f.hom.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom ⟨((forget₂ (FGModuleCat R) (ModuleCat R)).map f.hom).hom, fun g => by
    ext x
    ex

中文:
定义 forget₂HomLinearEquiv
  签名: (X Y : FDRep R G)
  定义体: ⟨InducedCategory.homMk (ModuleCat.ofHom <| f.hom.toLinearMap), fun g => by
    ext1
    simp only [FGModuleCat.obj_carrier]
    exact f.hom.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom ⟨((forget₂ (FGModuleCat R) (ModuleCat R)).map f.hom).hom, fun g => by
    ext x
    ex

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, FGModuleCat, FGModuleCat.obj_carrier, InducedCategory, InducedCategory.homMk, ModuleCat, ModuleCat.ofHom, Rep.ofHom, congr_hom, congr_map, f.comm, f.hom, f.hom.toLinearMap, forget, invFun, map_add, map_smul, obj_carrier, toLinearMap
-/
def forget₂HomLinearEquiv (X Y : FDRep R G) :
    ((forget₂ (FDRep R G) (Rep R G)).obj X ⟶
      (forget₂ (FDRep R G) (Rep R G)).obj Y) ≃ₗ[R] X ⟶ Y where
  toFun f := ⟨InducedCategory.homMk (ModuleCat.ofHom <| f.hom.toLinearMap), fun g => by
    ext1
    simp only [FGModuleCat.obj_carrier]
    exact f.hom.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom ⟨((forget₂ (FGModuleCat R) (ModuleCat R)).map f.hom).hom, fun g => by
    ext x
    exact ConcreteCategory.congr_hom ((forget (FGModuleCat R)).congr_map (f.comm g)) x⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (FDRep R G) (Rep R G)).Full
  body: by
  dsimp [forget₂, HasForget₂.forget₂]
  infer_instance

中文:
实例 :
  签名: (forget₂ (FDRep R G) (Rep R G)).Full
  定义体: by
  dsimp [forget₂, HasForget₂.forget₂]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : (forget₂ (FDRep R G) (Rep R G)).Full := by
  dsimp [forget₂, HasForget₂.forget₂]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (FDRep R G) (Rep R G)).Faithful
  body: by
  dsimp [forget₂, HasForget₂.forget₂]
  infer_instance

中文:
实例 :
  签名: (forget₂ (FDRep R G) (Rep R G)).Faithful
  定义体: by
  dsimp [forget₂, HasForget₂.forget₂]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : (forget₂ (FDRep R G) (Rep R G)).Faithful := by
  dsimp [forget₂, HasForget₂.forget₂]
  infer_instance

end FDRep

namespace FDRep

-- The variables in this section are slightly weird, living half in `Representation` and half in
-- `FDRep`. When we have a better API for general monoidal closed and rigid categories and these
-- structures on `FDRep`, we should remove the dependency of statements about `FDRep` on
-- `Representation.linHom` and `Representation.dual`. The isomorphism `dualTensorIsoLinHom`
-- below should then just be obtained from general results about rigid categories.
open Representation

variable {k : Type u} {G : Type v} {V : Type u} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]
variable (ρV : Representation k G V) (W : FDRep k G)

open scoped MonoidalCategory

/--
Definition of `dualTensorIsoLinHomAux` / `dualTensorIsoLinHomAux` 的定义

English:
definition dualTensorIsoLinHomAux
  signature: :
  body: LinearEquiv.toFGModuleCatIso (dualTensorHomEquiv k V W)

中文:
定义 dualTensorIsoLinHomAux
  签名: :
  定义体: LinearEquiv.toFGModuleCatIso (dualTensorHomEquiv k V W)

Depends on / 依赖: LinearEquiv, LinearEquiv.toFGModuleCatIso, dualTensorHomEquiv, toFGModuleCatIso
-/
noncomputable def dualTensorIsoLinHomAux :
    (FDRep.of ρV.dual otimes W).V ≅ (FDRep.of (linHom ρV W.ρ)).V :=
  LinearEquiv.toFGModuleCatIso (dualTensorHomEquiv k V W)

/--
Definition of `dualTensorIsoLinHom` / `dualTensorIsoLinHom` 的定义

English:
definition dualTensorIsoLinHom
  signature: : FDRep.of ρV.dual otimes W ≅ FDRep.of (linHom ρV W.ρ)
  body: by
  refine Action.mkIso (dualTensorIsoLinHomAux ρV W) (fun g => ?_)
  ext : 1
  exact dualTensorHom_comm ρV W.ρ g

@[simp]

中文:
定义 dualTensorIsoLinHom
  签名: : FDRep.of ρV.dual otimes W ≅ FDRep.of (linHom ρV W.ρ)
  定义体: by
  refine Action.mkIso (dualTensorIsoLinHomAux ρV W) (fun g => ?_)
  ext : 1
  exact dualTensorHom_comm ρV W.ρ g

@[simp]

Depends on / 依赖: Action, Action.mkIso, dualTensorHom_comm, dualTensorIsoLinHomAux
-/
noncomputable def dualTensorIsoLinHom : FDRep.of ρV.dual otimes W ≅ FDRep.of (linHom ρV W.ρ) := by
  refine Action.mkIso (dualTensorIsoLinHomAux ρV W) (fun g => ?_)
  ext : 1
  exact dualTensorHom_comm ρV W.ρ g

@[simp]
/--
theorem `dualTensorIsoLinHom_hom_hom` / 定理 `dualTensorIsoLinHom_hom_hom`

English:
theorem dualTensorIsoLinHom_hom_hom
  proof: rfl

中文:
定理 dualTensorIsoLinHom_hom_hom
  证明: rfl
-/
theorem dualTensorIsoLinHom_hom_hom :
    (dualTensorIsoLinHom ρV W).hom.hom = ConcreteCategory.ofHom (dualTensorHom k V W) :=
  rfl

end FDRep
