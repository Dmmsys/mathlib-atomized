/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# Adjunction between `Γ` and `Spec`

We define the adjunction `ΓSpec.adjunction : Γ ⊣ Spec` by defining the unit (`toΓSpec`,
in multiple steps in this file) and counit (done in `Spec.lean`) and checking that they satisfy
the left and right triangle identities. The constructions and proofs make use of
maps and lemmas defined and proved in `Mathlib/AlgebraicGeometry/StructureSheaf.lean`
extensively.

Notice that since the adjunction is between contravariant functors, you get to choose
one of the two categories to have arrows reversed, and it is equally valid to present
the adjunction as `Spec ⊣ Γ` (`Spec.to_LocallyRingedSpace.right_op ⊣ Γ`), in which
case the unit and the counit would switch to each other.

## Main definition

* `AlgebraicGeometry.identityToΓSpec` : The natural transformation `𝟭 _ ⟶ Γ ⋙ Spec`.
* `AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `LocallyRingedSpace`.
* `AlgebraicGeometry.ΓSpec.adjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `Scheme`.

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


noncomputable section

universe u

open PrimeSpectrum

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

open Spec (structureSheaf)

open TopologicalSpace

open AlgebraicGeometry.LocallyRingedSpace

open TopCat.Presheaf

open TopCat.Presheaf.SheafCondition

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/--
Definition of `toΓSpecFun` / `toΓSpecFun` 的定义

English:
definition toΓSpecFun
  signature: : X -> PrimeSpectrum (Γ.obj (op X))
  body: fun x =>
  comap (X.presheaf.Γgerm x).hom (IsLocalRing.closedPoint (X.presheaf.stalk x))

中文:
定义 toΓSpecFun
  签名: : X -> PrimeSpectrum (Γ.obj (op X))
  定义体: fun x =>
  comap (X.presheaf.Γgerm x).hom (IsLocalRing.closedPoint (X.presheaf.stalk x))
-/
def toΓSpecFun : X -> PrimeSpectrum (Γ.obj (op X)) := fun x =>
  comap (X.presheaf.Γgerm x).hom (IsLocalRing.closedPoint (X.presheaf.stalk x))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `notMem_prime_iff_unit_in_stalk` / 定理 `notMem_prime_iff_unit_in_stalk`

English:
theorem notMem_prime_iff_unit_in_stalk
  given: (r : Γ.obj (op X)) (x : X)
  proof: by
  simp [toΓSpecFun, IsLocalRing.closedPoint]

中文:
定理 notMem_prime_iff_unit_in_stalk
  条件: (r : Γ.obj (op X)) (x : X)
  证明: by
  simp [toΓSpecFun, IsLocalRing.closedPoint]

Depends on / 依赖: IsLocalRing, IsLocalRing.closedPoint, closedPoint
-/
theorem notMem_prime_iff_unit_in_stalk (r : Γ.obj (op X)) (x : X) :
    r ∉ (X.toΓSpecFun x).asIdeal ↔ IsUnit (X.presheaf.Γgerm x r) := by
  simp [toΓSpecFun, IsLocalRing.closedPoint]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toΓSpec_preimage_basicOpen_eq` / 定理 `toΓSpec_preimage_basicOpen_eq`

English:
theorem toΓSpec_preimage_basicOpen_eq
  given: (r : Γ.obj (op X))
  proof: by
      ext
      dsimp
      simp only [Set.mem_preimage, SetLike.mem_coe]
      rw [X.toRingedSpace.mem_top_basicOpen]
      exact notMem_prime_iff_unit_in_stalk ..

中文:
定理 toΓSpec_preimage_basicOpen_eq
  条件: (r : Γ.obj (op X))
  证明: by
      ext
      dsimp
      simp only [Set.mem_preimage, SetLike.mem_coe]
      rw [X.toRingedSpace.mem_top_basicOpen]
      exact notMem_prime_iff_unit_in_stalk ..

Depends on / 依赖: Set.mem_preimage, SetLike, SetLike.mem_coe, X.toRingedSpace.mem_top_basicOpen, mem_coe, mem_preimage, mem_top_basicOpen, notMem_prime_iff_unit_in_stalk, toRingedSpace
-/
theorem toΓSpec_preimage_basicOpen_eq (r : Γ.obj (op X)) :
    X.toΓSpecFun ⁻¹' basicOpen r = SetLike.coe (X.toRingedSpace.basicOpen r) := by
      ext
      dsimp
      simp only [Set.mem_preimage, SetLike.mem_coe]
      rw [X.toRingedSpace.mem_top_basicOpen]
      exact notMem_prime_iff_unit_in_stalk ..

/--
theorem `toΓSpec_continuous` / 定理 `toΓSpec_continuous`

English:
theorem toΓSpec_continuous
  statement: Continuous X.toΓSpecFun
  proof: by
  rw [isTopologicalBasis_basic_opens.continuous_iff]
  rintro _ ⟨r, rfl⟩
  rw [X.toΓSpec_preimage_basicOpen_eq r]
  exact (X.toRingedSpace.basicOpen r).2

中文:
定理 toΓSpec_continuous
  结论: Continuous X.toΓSpecFun
  证明: by
  rw [isTopologicalBasis_basic_opens.continuous_iff]
  rintro _ ⟨r, rfl⟩
  rw [X.toΓSpec_preimage_basicOpen_eq r]
  exact (X.toRingedSpace.basicOpen r).2

Depends on / 依赖: X.to, X.toRingedSpace.basicOpen, basicOpen, continuous_iff, isTopologicalBasis_basic_opens, isTopologicalBasis_basic_opens.continuous_iff, toRingedSpace
-/
theorem toΓSpec_continuous : Continuous X.toΓSpecFun := by
  rw [isTopologicalBasis_basic_opens.continuous_iff]
  rintro _ ⟨r, rfl⟩
  rw [X.toΓSpec_preimage_basicOpen_eq r]
  exact (X.toRingedSpace.basicOpen r).2

/--
Definition of `toΓSpecBase` / `toΓSpecBase` 的定义

English:
definition toΓSpecBase
  signature: : X.toTopCat ⟶ Spec.topObj (Γ.obj (op X))
  body: TopCat.ofHom
  { toFun := X.toΓSpecFun
    continuous_toFun := X.toΓSpec_continuous }

中文:
定义 toΓSpecBase
  签名: : X.toTopCat ⟶ Spec.topObj (Γ.obj (op X))
  定义体: TopCat.ofHom
  { toFun := X.toΓSpecFun
    continuous_toFun := X.toΓSpec_continuous }

Depends on / 依赖: TopCat, TopCat.ofHom, X.to, continuous_toFun
-/
def toΓSpecBase : X.toTopCat ⟶ Spec.topObj (Γ.obj (op X)) :=
  TopCat.ofHom
  { toFun := X.toΓSpecFun
    continuous_toFun := X.toΓSpec_continuous }

variable (r : Γ.obj (op X))

/--
Definition of `toΓSpecMapBasicOpen` / `toΓSpecMapBasicOpen` 的定义

English:
abbreviation toΓSpecMapBasicOpen
  signature: : Opens X
  body: (Opens.map X.toΓSpecBase).obj (basicOpen r)

中文:
缩写 toΓSpecMapBasicOpen
  签名: : Opens X
  定义体: (Opens.map X.toΓSpecBase).obj (basicOpen r)

Depends on / 依赖: Opens.map, X.to, basicOpen
-/
abbrev toΓSpecMapBasicOpen : Opens X :=
  (Opens.map X.toΓSpecBase).obj (basicOpen r)

/--
theorem `toΓSpecMapBasicOpen_eq` / 定理 `toΓSpecMapBasicOpen_eq`

English:
theorem toΓSpecMapBasicOpen_eq
  statement: X.toΓSpecMapBasicOpen r = X.toRingedSpace.basicOpen r
  proof: Opens.ext (X.toΓSpec_preimage_basicOpen_eq r)

中文:
定理 toΓSpecMapBasicOpen_eq
  结论: X.toΓSpecMapBasicOpen r = X.toRingedSpace.basicOpen r
  证明: Opens.ext (X.toΓSpec_preimage_basicOpen_eq r)

Depends on / 依赖: Opens.ext, X.to
-/
theorem toΓSpecMapBasicOpen_eq : X.toΓSpecMapBasicOpen r = X.toRingedSpace.basicOpen r :=
  Opens.ext (X.toΓSpec_preimage_basicOpen_eq r)

/--
Definition of `toToΓSpecMapBasicOpen` / `toToΓSpecMapBasicOpen` 的定义

English:
abbreviation toToΓSpecMapBasicOpen
  signature: :
  body: X.presheaf.map (X.toΓSpecMapBasicOpen r).leTop.op

中文:
缩写 toToΓSpecMapBasicOpen
  签名: :
  定义体: X.presheaf.map (X.toΓSpecMapBasicOpen r).leTop.op

Depends on / 依赖: X.presheaf.map, X.to, leTop.op, presheaf
-/
abbrev toToΓSpecMapBasicOpen :
    X.presheaf.obj (op ⊤) ⟶ X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  X.presheaf.map (X.toΓSpecMapBasicOpen r).leTop.op

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isUnit_res_toΓSpecMapBasicOpen` / 定理 `isUnit_res_toΓSpecMapBasicOpen`

English:
theorem isUnit_res_toΓSpecMapBasicOpen
  statement: IsUnit (X.toToΓSpecMapBasicOpen r r)
  proof: by
  convert!
    (X.presheaf.map <| (eqToHom <| X.toΓSpecMapBasicOpen_eq r).op).hom.isUnit_map
      (X.toRingedSpace.isUnit_res_basicOpen r)
  rw [← CommRingCat.comp_apply]; rw [← Functor.map_comp]
  congr

中文:
定理 isUnit_res_toΓSpecMapBasicOpen
  结论: IsUnit (X.toToΓSpecMapBasicOpen r r)
  证明: by
  convert!
    (X.presheaf.map <| (eqToHom <| X.toΓSpecMapBasicOpen_eq r).op).hom.isUnit_map
      (X.toRingedSpace.isUnit_res_basicOpen r)
  rw [← CommRingCat.comp_apply]; rw [← Functor.map_comp]
  congr

Depends on / 依赖: CommRingCat, CommRingCat.comp_apply, Fin.predAbove_surjective, Functor, Functor.map_comp, X.presheaf.map, X.to, X.toRingedSpace.isUnit_res_basicOpen, comp_apply, convert, epi_iff_surjective, eqToHom, hom.isUnit_map, isUnit_map, isUnit_res_basicOpen, map_comp, predAbove_surjective, presheaf, toRingedSpace
-/
theorem isUnit_res_toΓSpecMapBasicOpen : IsUnit (X.toToΓSpecMapBasicOpen r r) := by
  convert!
    (X.presheaf.map <| (eqToHom <| X.toΓSpecMapBasicOpen_eq r).op).hom.isUnit_map
      (X.toRingedSpace.isUnit_res_basicOpen r)
  rw [← CommRingCat.comp_apply]; rw [← Functor.map_comp]
  congr

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `toΓSpecCApp` / `toΓSpecCApp` 的定义

English:
definition toΓSpecCApp
  signature: :
  body: -- note: the explicit type annotations were not needed before
  -- https://github.com/leanprover-community/mathlib4/pull/19757
CommRingCat.ofHom
    IsLocalization.Away.lift
      (R := Γ.obj (op X))
      (S := (structureSheaf ↑(Γ.obj (op X))).obj.obj (op (basicOpen r)))
      r
      (isUnit_res_t

中文:
定义 toΓSpecCApp
  签名: :
  定义体: -- note: the explicit type annotations were not needed before
  -- https://github.com/leanprover-community/mathlib4/pull/19757
CommRingCat.ofHom
    IsLocalization.Away.lift
      (R := Γ.obj (op X))
      (S := (structureSheaf ↑(Γ.obj (op X))).obj.obj (op (basicOpen r)))
      r
      (isUnit_res_t
-/
def toΓSpecCApp :
    (structureSheaf <| Γ.obj <| op X).obj.obj (op <| basicOpen r) ⟶
      X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  -- note: the explicit type annotations were not needed before
  -- https://github.com/leanprover-community/mathlib4/pull/19757
CommRingCat.ofHom
    IsLocalization.Away.lift
      (R := Γ.obj (op X))
      (S := (structureSheaf ↑(Γ.obj (op X))).obj.obj (op (basicOpen r)))
      r
      (isUnit_res_toΓSpecMapBasicOpen _ r)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toΓSpecCApp_iff` / 定理 `toΓSpecCApp_iff`

English:
theorem toΓSpecCApp_iff
  proof: by
  have loc_inst := IsLocalization.to_basicOpen (Γ.obj (op X)) r
  refine ConcreteCategory.ext_iff.trans ?_
  rw [← @IsLocalization.Away.lift_comp _ _ _ _ _ _ _ r loc_inst _
      (X.isUnit_res_toΓSpecMapBasicOpen r)]
  constructor
  · intro h
    ext : 1
    exact IsLocalization.ringHom_ext (Subm

中文:
定理 toΓSpecCApp_iff
  证明: by
  have loc_inst := IsLocalization.to_basicOpen (Γ.obj (op X)) r
  refine ConcreteCategory.ext_iff.trans ?_
  rw [← @IsLocalization.Away.lift_comp _ _ _ _ _ _ _ r loc_inst _
      (X.isUnit_res_toΓSpecMapBasicOpen r)]
  constructor
  · intro h
    ext : 1
    exact IsLocalization.ringHom_ext (Subm

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ext_iff.trans, IsLocalization, IsLocalization.Away.lift_comp, IsLocalization.ringHom_ext, IsLocalization.to_basicOpen, Submonoid, Submonoid.powers, X.isUnit_res_to, congr_arg, ext_iff, lift_comp, loc_inst, powers, ringHom_ext, to_basicOpen
-/
theorem toΓSpecCApp_iff
    (f :
      (structureSheaf <| Γ.obj <| op X).obj.obj (op <| basicOpen r) ⟶
        X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r)) :
    CommRingCat.ofHom (algebraMap (Γ.obj (op X)) _) ≫ f = X.toToΓSpecMapBasicOpen r ↔
      f = X.toΓSpecCApp r := by
  have loc_inst := IsLocalization.to_basicOpen (Γ.obj (op X)) r
  refine ConcreteCategory.ext_iff.trans ?_
  rw [← @IsLocalization.Away.lift_comp _ _ _ _ _ _ _ r loc_inst _
      (X.isUnit_res_toΓSpecMapBasicOpen r)]
  constructor
  · intro h
    ext : 1
    exact IsLocalization.ringHom_ext (Submonoid.powers r) h
  apply congr_arg

/--
theorem `toΓSpecCApp_spec` / 定理 `toΓSpecCApp_spec`

English:
theorem toΓSpecCApp_spec
  proof: (X.toΓSpecCApp_iff r _).2 rfl

中文:
定理 toΓSpecCApp_spec
  证明: (X.toΓSpecCApp_iff r _).2 rfl

Depends on / 依赖: X.to
-/
theorem toΓSpecCApp_spec :
    CommRingCat.ofHom (algebraMap (Γ.obj (op X)) _) ≫ X.toΓSpecCApp r = X.toToΓSpecMapBasicOpen r :=
  (X.toΓSpecCApp_iff r _).2 rfl

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf hom on all basic opens, commuting with restrictions. -/
@[simps app]
/--
Definition of `toΓSpecCBasicOpens` / `toΓSpecCBasicOpens` 的定义

English:
definition toΓSpecCBasicOpens
  signature: :
  body: X.toΓSpecCApp r.unop
  naturality r s f := by
    apply (StructureSheaf.to_basicOpen_epi (Γ.obj (op X)) r.unop).1
    simp only [← Category.assoc]
    rw [show algebraMap (Γ.obj (op X)) ((structureSheaf (Γ.obj (op X))).obj.obj _) = algebraMap _
      ((structureSheafInType (Γ.obj (op X)) (Γ.obj (op 

中文:
定义 toΓSpecCBasicOpens
  签名: :
  定义体: X.toΓSpecCApp r.unop
  naturality r s f := by
    apply (StructureSheaf.to_basicOpen_epi (Γ.obj (op X)) r.unop).1
    simp only [← Category.assoc]
    rw [show algebraMap (Γ.obj (op X)) ((structureSheaf (Γ.obj (op X))).obj.obj _) = algebraMap _
      ((structureSheafInType (Γ.obj (op X)) (Γ.obj (op 

Depends on / 依赖: Fin.succAbove_right_injective, X.to, mono_iff_injective, r.unop, succAbove_right_injective
-/
def toΓSpecCBasicOpens :
    (inducedFunctor basicOpen).op ⋙ (structureSheaf (Γ.obj (op X))).1 ⟶
      (inducedFunctor basicOpen).op ⋙ ((TopCat.Sheaf.pushforward _ X.toΓSpecBase).obj X.𝒪).1 where
  app r := X.toΓSpecCApp r.unop
  naturality r s f := by
    apply (StructureSheaf.to_basicOpen_epi (Γ.obj (op X)) r.unop).1
    simp only [← Category.assoc]
    rw [show algebraMap (Γ.obj (op X)) ((structureSheaf (Γ.obj (op X))).obj.obj _) = algebraMap _
      ((structureSheafInType (Γ.obj (op X)) (Γ.obj (op X))).obj.obj _) from rfl]; rw [X.toΓSpecCApp_spec r.unop]
    convert! X.toΓSpecCApp_spec s.unop
    symm
    apply X.presheaf.map_comp

/-- The canonical morphism of sheafed spaces from `X` to the spectrum of its global sections. -/
@[simps! -isSimp]
/--
Definition of `toΓSpecSheafedSpace` / `toΓSpecSheafedSpace` 的定义

English:
definition toΓSpecSheafedSpace
  signature: : X.toSheafedSpace ⟶ Spec.toSheafedSpace.obj (op (Γ.obj (op X)))
  body: InducedCategory.homMk
    { base := X.toΓSpecBase
      c :=
        TopCat.Sheaf.restrictHomEquivHom (structureSheaf (Γ.obj (op X))).1 _ isBasis_basic_opens
          X.toΓSpecCBasicOpens }

中文:
定义 toΓSpecSheafedSpace
  签名: : X.toSheafedSpace ⟶ Spec.toSheafedSpace.obj (op (Γ.obj (op X)))
  定义体: InducedCategory.homMk
    { base := X.toΓSpecBase
      c :=
        TopCat.Sheaf.restrictHomEquivHom (structureSheaf (Γ.obj (op X))).1 _ isBasis_basic_opens
          X.toΓSpecCBasicOpens }

Depends on / 依赖: InducedCategory, InducedCategory.homMk, TopCat, TopCat.Sheaf.restrictHomEquivHom, X.to, isBasis_basic_opens, restrictHomEquivHom, structureSheaf
-/
def toΓSpecSheafedSpace : X.toSheafedSpace ⟶ Spec.toSheafedSpace.obj (op (Γ.obj (op X))) :=
  InducedCategory.homMk
    { base := X.toΓSpecBase
      c :=
        TopCat.Sheaf.restrictHomEquivHom (structureSheaf (Γ.obj (op X))).1 _ isBasis_basic_opens
          X.toΓSpecCBasicOpens }

/--
theorem `toΓSpecSheafedSpace_app_eq` / 定理 `toΓSpecSheafedSpace_app_eq`

English:
theorem toΓSpecSheafedSpace_app_eq
  proof: by
  apply TopCat.Sheaf.extend_hom_app _ _ _

中文:
定理 toΓSpecSheafedSpace_app_eq
  证明: by
  apply TopCat.Sheaf.extend_hom_app _ _ _

Depends on / 依赖: TopCat, TopCat.Sheaf.extend_hom_app, extend_hom_app
-/
theorem toΓSpecSheafedSpace_app_eq :
    X.toΓSpecSheafedSpace.hom.c.app (op (basicOpen r)) = X.toΓSpecCApp r := by
  apply TopCat.Sheaf.extend_hom_app _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `toΓSpecSheafedSpace_app_spec` / 定理 `toΓSpecSheafedSpace_app_spec`

English:
theorem toΓSpecSheafedSpace_app_spec
  given: (r : Γ.obj (op X))
  proof: (X.toΓSpecSheafedSpace_app_eq r).symm ▸ X.toΓSpecCApp_spec r

中文:
定理 toΓSpecSheafedSpace_app_spec
  条件: (r : Γ.obj (op X))
  证明: (X.toΓSpecSheafedSpace_app_eq r).symm ▸ X.toΓSpecCApp_spec r
-/
@[reassoc] theorem toΓSpecSheafedSpace_app_spec (r : Γ.obj (op X)) :
    CommRingCat.ofHom (algebraMap (Γ.obj (op X)) _) ≫
        X.toΓSpecSheafedSpace.hom.c.app (op (basicOpen r)) =
      X.toToΓSpecMapBasicOpen r :=
  (X.toΓSpecSheafedSpace_app_eq r).symm ▸ X.toΓSpecCApp_spec r

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toStalk_stalkMap_toΓSpec` / 定理 `toStalk_stalkMap_toΓSpec`

English:
theorem toStalk_stalkMap_toΓSpec
  given: (x : X)
  proof: by
  rw [PresheafedSpace.Hom.stalkMap]; rw [← algebraMap_germ (basicOpen (1 : Γ.obj (op X))) _ (by rw [basicOpen_one]; trivial),
    ← Category.assoc, Category.assoc (CommRingCat.ofHom _), stalkFunctor_map_germ, ← Category.assoc,
    X.toΓSpecSheafedSpace_app_eq, X.toΓSpecCApp_spec, Γgerm,
    ← dsi

中文:
定理 toStalk_stalkMap_toΓSpec
  条件: (x : X)
  证明: by
  rw [PresheafedSpace.Hom.stalkMap]; rw [← algebraMap_germ (basicOpen (1 : Γ.obj (op X))) _ (by rw [basicOpen_one]; trivial),
    ← Category.assoc, Category.assoc (CommRingCat.ofHom _), stalkFunctor_map_germ, ← Category.assoc,
    X.toΓSpecSheafedSpace_app_eq, X.toΓSpecCApp_spec, Γgerm,
    ← dsi

Depends on / 依赖: Category, Category.assoc, CommRingCat, CommRingCat.ofHom, PresheafedSpace, PresheafedSpace.Hom.stalkMap, X.presheaf, X.to, algebraMap_germ, basicOpen, basicOpen_one, germ_res, le_top, le_top.hom, presheaf, stalkFunctor_map_germ, stalkMap, stalkPushforward_germ
-/
theorem toStalk_stalkMap_toΓSpec (x : X) :
    toStalk _ _ ≫ X.toΓSpecSheafedSpace.hom.stalkMap x = X.presheaf.Γgerm x := by
  rw [PresheafedSpace.Hom.stalkMap]; rw [← algebraMap_germ (basicOpen (1 : Γ.obj (op X))) _ (by rw [basicOpen_one]; trivial),
    ← Category.assoc, Category.assoc (CommRingCat.ofHom _), stalkFunctor_map_germ, ← Category.assoc,
    X.toΓSpecSheafedSpace_app_eq, X.toΓSpecCApp_spec, Γgerm,
    ← dsimp% stalkPushforward_germ _ _ X.presheaf ⊤]
  congr 1
  exact (X.toΓSpecBase _* X.presheaf).germ_res le_top.hom _ _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical morphism from `X` to the spectrum of its global sections. -/
@[simps! base]
/--
Definition of `toΓSpec` / `toΓSpec` 的定义

English:
definition toΓSpec
  signature: : X ⟶ Spec.locallyRingedSpaceObj (Γ.obj (op X))
  body: LocallyRingedSpace.homMk (X.toΓSpecSheafedSpace) (fun x => by
    let p : PrimeSpectrum (Γ.obj (op X)) := X.toΓSpecFun x
    constructor
    -- show stalk map is local hom ↓
    let S := (structureSheaf _).presheaf.stalk p
    rintro (t : S) ht
    obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj p.asIdea

中文:
定义 toΓSpec
  签名: : X ⟶ Spec.locallyRingedSpaceObj (Γ.obj (op X))
  定义体: LocallyRingedSpace.homMk (X.toΓSpecSheafedSpace) (fun x => by
    let p : PrimeSpectrum (Γ.obj (op X)) := X.toΓSpecFun x
    constructor
    -- show stalk map is local hom ↓
    let S := (structureSheaf _).presheaf.stalk p
    rintro (t : S) ht
    obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj p.asIdea

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.homMk, PrimeSpectrum, X.to
-/
def toΓSpec : X ⟶ Spec.locallyRingedSpaceObj (Γ.obj (op X)) :=
  LocallyRingedSpace.homMk (X.toΓSpecSheafedSpace) (fun x => by
    let p : PrimeSpectrum (Γ.obj (op X)) := X.toΓSpecFun x
    constructor
    -- show stalk map is local hom ↓
    let S := (structureSheaf _).presheaf.stalk p
    rintro (t : S) ht
    obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj p.asIdeal.primeCompl t
    dsimp at he
    set t' := _
    change t * t' = _ at he
    apply isUnit_of_mul_isUnit_left (y := t')
    rw [he]
    refine IsLocalization.map_units S (⟨r, ?_⟩ : p.asIdeal.primeCompl)
    apply (notMem_prime_iff_unit_in_stalk _ _ _).mpr
    rw [← toStalk_stalkMap_toΓSpec]; rw [CommRingCat.comp_apply]
    erw [← he]
    rw [map_mul]
exact ht.mul (IsLocalization.map_units (R := Γ.obj (op X)) S s).map _)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toΓSpec_preimage_zeroLocus_eq` / 引理 `toΓSpec_preimage_zeroLocus_eq`

English:
lemma toΓSpec_preimage_zeroLocus_eq
  statement: {X : LocallyRingedSpace.{u}}
  proof: by
  simp only [RingedSpace.zeroLocus]
  have (i : LocallyRingedSpace.Γ.obj (op X)) (_ : i in s) :
      (SetLike.coe (X.toRingedSpace.basicOpen i))ᶜ =
        X.toΓSpec.base ⁻¹' ((PrimeSpectrum.basicOpen i).carrier)ᶜ := by
    symm
    rw [Set.preimage_compl]; rw [Opens.carrier_eq_coe]
    erw [X.t

中文:
引理 toΓSpec_preimage_zeroLocus_eq
  结论: {X : LocallyRingedSpace.{u}}
  证明: by
  simp only [RingedSpace.zeroLocus]
  have (i : LocallyRingedSpace.Γ.obj (op X)) (_ : i in s) :
      (SetLike.coe (X.toRingedSpace.basicOpen i))ᶜ =
        X.toΓSpec.base ⁻¹' ((PrimeSpectrum.basicOpen i).carrier)ᶜ := by
    symm
    rw [Set.preimage_compl]; rw [Opens.carrier_eq_coe]
    erw [X.t

Depends on / 依赖: LocallyRingedSpace, Opens.carrier_eq_coe, PrimeSpectrum, PrimeSpectrum.basicOpen, PrimeSpectrum.basicOpen_eq_zeroLocus_compl, PrimeSpectrum.zeroLocus_iUnion, RingedSpace, RingedSpace.zeroLocus, Set.iInter, Set.preimage_compl, Set.preimage_iInter, SetLike, SetLike.coe, Spec.base, X.to, X.toRingedSpace.basicOpen, basicOpen, basicOpen_eq_zeroLocus_compl, carrier, carrier_eq_coe
-/
lemma toΓSpec_preimage_zeroLocus_eq {X : LocallyRingedSpace.{u}}
    (s : Set (X.presheaf.obj (op ⊤))) :
    X.toΓSpec.base ⁻¹' PrimeSpectrum.zeroLocus s = X.toRingedSpace.zeroLocus s := by
  simp only [RingedSpace.zeroLocus]
  have (i : LocallyRingedSpace.Γ.obj (op X)) (_ : i in s) :
      (SetLike.coe (X.toRingedSpace.basicOpen i))ᶜ =
        X.toΓSpec.base ⁻¹' ((PrimeSpectrum.basicOpen i).carrier)ᶜ := by
    symm
    rw [Set.preimage_compl]; rw [Opens.carrier_eq_coe]
    erw [X.toΓSpec_preimage_basicOpen_eq i]
  erw [Set.iInter₂_congr this]
  simp_rw [← Set.preimage_iInter₂, Opens.carrier_eq_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl,
    compl_compl]
  rw [← PrimeSpectrum.zeroLocus_iUnion₂]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `comp_ring_hom_ext` / 定理 `comp_ring_hom_ext`

English:
theorem comp_ring_hom_ext
  statement: {X : LocallyRingedSpace.{u}} {R : CommRingCat.{u}} {f : R ⟶ Γ.obj (op X)}
  proof: by
  refine LocallyRingedSpace.forgetToSheafedSpace.map_injective
    (Spec.basicOpen_hom_ext w ?_)
  intro r U
  erw [SheafedSpace.comp_hom_c_app, toOpen_comp_comap_assoc]
  dsimp
  rw [Category.assoc]
  erw [toΓSpecSheafedSpace_app_spec, ← X.presheaf.map_comp]
  exact h r

中文:
定理 comp_ring_hom_ext
  结论: {X : LocallyRingedSpace.{u}} {R : CommRingCat.{u}} {f : R ⟶ Γ.obj (op X)}
  证明: by
  refine LocallyRingedSpace.forgetToSheafedSpace.map_injective
    (Spec.basicOpen_hom_ext w ?_)
  intro r U
  erw [SheafedSpace.comp_hom_c_app, toOpen_comp_comap_assoc]
  dsimp
  rw [Category.assoc]
  erw [toΓSpecSheafedSpace_app_spec, ← X.presheaf.map_comp]
  exact h r

Depends on / 依赖: Category, Category.assoc, LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace.map_injective, SheafedSpace, SheafedSpace.comp_hom_c_app, Spec.basicOpen_hom_ext, X.presheaf.map_comp, basicOpen_hom_ext, comp_hom_c_app, forgetToSheafedSpace, map_comp, map_injective, presheaf, toOpen_comp_comap_assoc
-/
theorem comp_ring_hom_ext {X : LocallyRingedSpace.{u}} {R : CommRingCat.{u}} {f : R ⟶ Γ.obj (op X)}
    {β : X ⟶ Spec.locallyRingedSpaceObj R}
    (w : X.toΓSpec.base ≫ (Spec.locallyRingedSpaceMap f).base = β.base)
    (h :
      forall r : R,
        f ≫ X.presheaf.map (homOfLE le_top : (Opens.map β.base).obj (basicOpen r) ⟶ _).op =
          CommRingCat.ofHom (algebraMap _ _) ≫ β.c.app (op (basicOpen r))) :
    X.toΓSpec ≫ Spec.locallyRingedSpaceMap f = β := by
  refine LocallyRingedSpace.forgetToSheafedSpace.map_injective
    (Spec.basicOpen_hom_ext w ?_)
  intro r U
  erw [SheafedSpace.comp_hom_c_app, toOpen_comp_comap_assoc]
  dsimp
  rw [Category.assoc]
  erw [toΓSpecSheafedSpace_app_spec, ← X.presheaf.map_comp]
  exact h r

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Γ_Spec_left_triangle` / 定理 `Γ_Spec_left_triangle`

English:
theorem Γ_Spec_left_triangle
  statement: toSpecΓ (Γ.obj (op X)) ≫ X.toΓSpec.c.app (op ⊤) = 𝟙 _
  proof: by
  unfold toSpecΓ
  have := X.toΓSpecSheafedSpace_app_spec 1
  unfold toToΓSpecMapBasicOpen toΓSpecMapBasicOpen at this
  rw! [basicOpen_one] at this
  convert! this
  exact (X.presheaf.map_id ..).symm

中文:
定理 Γ_Spec_left_triangle
  结论: toSpecΓ (Γ.obj (op X)) ≫ X.toΓSpec.c.app (op ⊤) = 𝟙 _
  证明: by
  unfold toSpecΓ
  have := X.toΓSpecSheafedSpace_app_spec 1
  unfold toToΓSpecMapBasicOpen toΓSpecMapBasicOpen at this
  rw! [basicOpen_one] at this
  convert! this
  exact (X.presheaf.map_id ..).symm

Depends on / 依赖: X.presheaf.map_id, X.to, basicOpen_one, convert, map_id, presheaf
-/
theorem Γ_Spec_left_triangle : toSpecΓ (Γ.obj (op X)) ≫ X.toΓSpec.c.app (op ⊤) = 𝟙 _ := by
  unfold toSpecΓ
  have := X.toΓSpecSheafedSpace_app_spec 1
  unfold toToΓSpecMapBasicOpen toΓSpecMapBasicOpen at this
  rw! [basicOpen_one] at this
  convert! this
  exact (X.presheaf.map_id ..).symm

end LocallyRingedSpace

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `identityToΓSpec` / `identityToΓSpec` 的定义

English:
definition identityToΓSpec
  signature: : 𝟭 LocallyRingedSpace.{u} ⟶ Γ.rightOp ⋙ Spec.toLocallyRingedSpace where
  body: LocallyRingedSpace.toΓSpec
  naturality X Y f := by
    symm
    apply LocallyRingedSpace.comp_ring_hom_ext
    · ext1 x
      dsimp
      change PrimeSpectrum.comap (f.c.app (op ⊤)).hom (X.toΓSpecFun x) = Y.toΓSpecFun (f.base x)
      dsimp [toΓSpecFun]
      rw [← IsLocalRing.comap_closedPoint (f.

中文:
定义 identityToΓSpec
  签名: : 𝟭 LocallyRingedSpace.{u} ⟶ Γ.rightOp ⋙ Spec.toLocallyRingedSpace where
  定义体: LocallyRingedSpace.toΓSpec
  naturality X Y f := by
    symm
    apply LocallyRingedSpace.comp_ring_hom_ext
    · ext1 x
      dsimp
      change PrimeSpectrum.comap (f.c.app (op ⊤)).hom (X.toΓSpecFun x) = Y.toΓSpecFun (f.base x)
      dsimp [toΓSpecFun]
      rw [← IsLocalRing.comap_closedPoint (f.

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.to
-/
def identityToΓSpec : 𝟭 LocallyRingedSpace.{u} ⟶ Γ.rightOp ⋙ Spec.toLocallyRingedSpace where
  app := LocallyRingedSpace.toΓSpec
  naturality X Y f := by
    symm
    apply LocallyRingedSpace.comp_ring_hom_ext
    · ext1 x
      dsimp
      change PrimeSpectrum.comap (f.c.app (op ⊤)).hom (X.toΓSpecFun x) = Y.toΓSpecFun (f.base x)
      dsimp [toΓSpecFun]
      rw [← IsLocalRing.comap_closedPoint (f.stalkMap x).hom]; rw [←
        PrimeSpectrum.comap_comp_apply]; rw [← PrimeSpectrum.comap_comp_apply]; rw [← CommRingCat.hom_comp]; rw [← CommRingCat.hom_comp]
      congr 2
      exact (PresheafedSpace.stalkMap_germ f.1 ⊤ x trivial).symm
    · intro r
      rw [LocallyRingedSpace.comp_c_app]; rw [← Category.assoc]
      erw [Y.toΓSpecSheafedSpace_app_spec, f.c.naturality]
      rfl

namespace ΓSpec

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `left_triangle` / 定理 `left_triangle`

English:
theorem left_triangle
  given: (X : LocallyRingedSpace)
  proof: X.Γ_Spec_left_triangle

中文:
定理 left_triangle
  条件: (X : LocallyRingedSpace)
  证明: X.Γ_Spec_left_triangle
-/
theorem left_triangle (X : LocallyRingedSpace) :
    SpecΓIdentity.inv.app (Γ.obj (op X)) ≫ (identityToΓSpec.app X).c.app (op ⊤) = 𝟙 _ :=
  X.Γ_Spec_left_triangle

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `right_triangle` / 定理 `right_triangle`

English:
theorem right_triangle
  given: (R : CommRingCat)
  proof: by
  apply LocallyRingedSpace.comp_ring_hom_ext
  · ext (p : PrimeSpectrum R)
    dsimp
    refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff ((structureSheaf R).presheaf.stalk p)
        p.asIdeal x]
    rfl
  · intro r; rfl

中文:
定理 right_triangle
  条件: (R : CommRingCat)
  证明: by
  apply LocallyRingedSpace.comp_ring_hom_ext
  · ext (p : PrimeSpectrum R)
    dsimp
    refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff ((structureSheaf R).presheaf.stalk p)
        p.asIdeal x]
    rfl
  · intro r; rfl

Depends on / 依赖: AtPrime, Ideal.ext, IsLocalization, IsLocalization.AtPrime.to_map_mem_maximal_iff, LocallyRingedSpace, LocallyRingedSpace.comp_ring_hom_ext, PrimeSpectrum, PrimeSpectrum.ext, asIdeal, comp_ring_hom_ext, p.asIdeal, presheaf, presheaf.stalk, structureSheaf, to_map_mem_maximal_iff
-/
theorem right_triangle (R : CommRingCat) :
    identityToΓSpec.app (Spec.toLocallyRingedSpace.obj <| op R) ≫
        Spec.toLocallyRingedSpace.map (SpecΓIdentity.inv.app R).op =
      𝟙 _ := by
  apply LocallyRingedSpace.comp_ring_hom_ext
  · ext (p : PrimeSpectrum R)
    dsimp
    refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff ((structureSheaf R).presheaf.stalk p)
        p.asIdeal x]
    rfl
  · intro r; rfl

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `LocallyRingedSpace`. -/
@[simps]
/--
Definition of `locallyRingedSpaceAdjunction` / `locallyRingedSpaceAdjunction` 的定义

English:
definition locallyRingedSpaceAdjunction
  signature: : Γ.rightOp ⊣ Spec.toLocallyRingedSpace.{u} where
  body: identityToΓSpec
  counit := (NatIso.op SpecΓIdentity).inv
  left_triangle_components X := by
    simp only [Functor.id_obj, Γ_obj, Functor.rightOp_map, Γ_map,
      Quiver.Hom.unop_op, NatIso.op_inv, NatTrans.op_app, SpecΓIdentity_inv_app]
    exact congr_arg Quiver.Hom.op (left_triangle X)
  right_

中文:
定义 locallyRingedSpaceAdjunction
  签名: : Γ.rightOp ⊣ Spec.toLocallyRingedSpace.{u} where
  定义体: identityToΓSpec
  counit := (NatIso.op SpecΓIdentity).inv
  left_triangle_components X := by
    simp only [Functor.id_obj, Γ_obj, Functor.rightOp_map, Γ_map,
      Quiver.Hom.unop_op, NatIso.op_inv, NatTrans.op_app, SpecΓIdentity_inv_app]
    exact congr_arg Quiver.Hom.op (left_triangle X)
  right_
-/
def locallyRingedSpaceAdjunction : Γ.rightOp ⊣ Spec.toLocallyRingedSpace.{u} where
  unit := identityToΓSpec
  counit := (NatIso.op SpecΓIdentity).inv
  left_triangle_components X := by
    simp only [Functor.id_obj, Γ_obj, Functor.rightOp_map, Γ_map,
      Quiver.Hom.unop_op, NatIso.op_inv, NatTrans.op_app, SpecΓIdentity_inv_app]
    exact congr_arg Quiver.Hom.op (left_triangle X)
  right_triangle_components R := by
    simp only [Functor.id_obj, NatIso.op_inv, NatTrans.op_app, SpecΓIdentity_inv_app]
    exact right_triangle R.unop


set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `toSpecΓ_unop` / 引理 `toSpecΓ_unop`

English:
lemma toSpecΓ_unop
  given: (R : CommRingCatᵒᵖ)
  proof: rfl

中文:
引理 toSpecΓ_unop
  条件: (R : CommRingCatᵒᵖ)
  证明: rfl
-/
lemma toSpecΓ_unop (R : CommRingCatᵒᵖ) :
    AlgebraicGeometry.toSpecΓ (Opposite.unop R) = CommRingCat.ofHom (algebraMap _ _) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `@[simp]`-normal form of `locallyRingedSpaceAdjunction_counit_app'`. -/
@[simp]
/--
lemma `toSpecΓ_of` / 引理 `toSpecΓ_of`

English:
lemma toSpecΓ_of
  given: (R : Type u) [CommRing R]
  proof: rfl

中文:
引理 toSpecΓ_of
  条件: (R : 类型u) [CommRing R]
  证明: rfl
-/
lemma toSpecΓ_of (R : Type u) [CommRing R] :
    AlgebraicGeometry.toSpecΓ (CommRingCat.of R) = CommRingCat.ofHom (algebraMap _ _) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `locallyRingedSpaceAdjunction_counit_app` / 引理 `locallyRingedSpaceAdjunction_counit_app`

English:
lemma locallyRingedSpaceAdjunction_counit_app
  given: (R : CommRingCatᵒᵖ)
  proof: rfl

中文:
引理 locallyRingedSpaceAdjunction_counit_app
  条件: (R : CommRingCatᵒᵖ)
  证明: rfl
-/
lemma locallyRingedSpaceAdjunction_counit_app (R : CommRingCatᵒᵖ) :
    locallyRingedSpaceAdjunction.counit.app R =
      (CommRingCat.ofHom (algebraMap _ _)).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `locallyRingedSpaceAdjunction_counit_app'` / 引理 `locallyRingedSpaceAdjunction_counit_app'`

English:
lemma locallyRingedSpaceAdjunction_counit_app'
  given: (R : Type u) [CommRing R]
  proof: rfl

中文:
引理 locallyRingedSpaceAdjunction_counit_app'
  条件: (R : 类型u) [CommRing R]
  证明: rfl
-/
lemma locallyRingedSpaceAdjunction_counit_app' (R : Type u) [CommRing R] :
    locallyRingedSpaceAdjunction.counit.app (op <| CommRingCat.of R) =
      (CommRingCat.ofHom (algebraMap _ _)).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unop_locallyRingedSpaceAdjunction_counit_app'` / 引理 `unop_locallyRingedSpaceAdjunction_counit_app'`

English:
lemma unop_locallyRingedSpaceAdjunction_counit_app'
  given: (R : Type u) [CommRing R]
  proof: rfl

中文:
引理 unop_locallyRingedSpaceAdjunction_counit_app'
  条件: (R : 类型u) [CommRing R]
  证明: rfl
-/
lemma unop_locallyRingedSpaceAdjunction_counit_app' (R : Type u) [CommRing R] :
    (locallyRingedSpaceAdjunction.counit.app (op <| CommRingCat.of R)).unop =
      (CommRingCat.ofHom (algebraMap _ _)) := rfl

/--
lemma `locallyRingedSpaceAdjunction_homEquiv_apply` / 引理 `locallyRingedSpaceAdjunction_homEquiv_apply`

English:
lemma locallyRingedSpaceAdjunction_homEquiv_apply
  proof: rfl

中文:
引理 locallyRingedSpaceAdjunction_homEquiv_apply
  证明: rfl

Depends on / 依赖: StrongEpi, StrongEpi.epi
-/
lemma locallyRingedSpaceAdjunction_homEquiv_apply
    {X : LocallyRingedSpace} {R : CommRingCatᵒᵖ}
    (f : Γ.rightOp.obj X ⟶ R) :
    locallyRingedSpaceAdjunction.homEquiv X R f =
      identityToΓSpec.app X ≫ Spec.locallyRingedSpaceMap f.unop := rfl

/--
lemma `locallyRingedSpaceAdjunction_homEquiv_apply'` / 引理 `locallyRingedSpaceAdjunction_homEquiv_apply'`

English:
lemma locallyRingedSpaceAdjunction_homEquiv_apply'
  proof: rfl

中文:
引理 locallyRingedSpaceAdjunction_homEquiv_apply'
  证明: rfl
-/
lemma locallyRingedSpaceAdjunction_homEquiv_apply'
    {X : LocallyRingedSpace} {R : Type u} [CommRing R]
    (f : CommRingCat.of R ⟶ Γ.obj <| op X) :
    locallyRingedSpaceAdjunction.homEquiv X (op <| CommRingCat.of R) (op f) =
      identityToΓSpec.app X ≫ Spec.locallyRingedSpaceMap f := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app` / 引理 `toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app`

English:
lemma toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app
  proof: by
  dsimp
  rw [← StructureSheaf.algebraMap_self_map _ U _ (homOfLE le_top).op]; rw [Category.assoc]; rw [NatTrans.naturality _ (homOfLE (le_top (a := U.unop))).op]; rw [← unop_locallyRingedSpaceAdjunction_counit_app']
  simp_rw [← Γ_map_op]
  rw [← Γ.rightOp_map_unop]; rw [← Category.assoc]; rw [←

中文:
引理 toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app
  证明: by
  dsimp
  rw [← StructureSheaf.algebraMap_self_map _ U _ (homOfLE le_top).op]; rw [Category.assoc]; rw [NatTrans.naturality _ (homOfLE (le_top (a := U.unop))).op]; rw [← unop_locallyRingedSpaceAdjunction_counit_app']
  simp_rw [← Γ_map_op]
  rw [← Γ.rightOp_map_unop]; rw [← Category.assoc]; rw [←

Depends on / 依赖: Adjunction, Adjunction.homEquiv_counit, Category, Category.assoc, Equiv.symm_apply_apply, NatTrans, NatTrans.naturality, StructureSheaf, StructureSheaf.algebraMap_self_map, U.unop, algebraMap_self_map, homEquiv_counit, homOfLE, le_top, naturality, rightOp_map_unop, simp_rw, symm_apply_apply, unop_comp, unop_locallyRingedSpaceAdjunction_counit_app
-/
lemma toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app
    {X : LocallyRingedSpace} {R : Type u} [CommRing R]
    (f : Γ.rightOp.obj X ⟶ op (CommRingCat.of R)) (U) :
    CommRingCat.ofHom (algebraMap R _) ≫
      (locallyRingedSpaceAdjunction.homEquiv X (op <| CommRingCat.of R) f).c.app U =
    f.unop ≫ X.presheaf.map (homOfLE le_top).op := by
  dsimp
  rw [← StructureSheaf.algebraMap_self_map _ U _ (homOfLE le_top).op]; rw [Category.assoc]; rw [NatTrans.naturality _ (homOfLE (le_top (a := U.unop))).op]; rw [← unop_locallyRingedSpaceAdjunction_counit_app']
  simp_rw [← Γ_map_op]
  rw [← Γ.rightOp_map_unop]; rw [← Category.assoc]; rw [← unop_comp]
  erw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]
  rfl

/--
Definition of `adjunction` / `adjunction` 的定义

English:
definition adjunction
  signature: : Scheme.Γ.rightOp ⊣ Scheme.Spec.{u} where
  body: { app := fun X => ⟨locallyRingedSpaceAdjunction.{u}.unit.app X.toLocallyRingedSpace⟩
    naturality := fun _ _ f =>
      Scheme.Hom.ext' (locallyRingedSpaceAdjunction.{u}.unit.naturality f.toLRSHom) }
  counit := (NatIso.op Scheme.SpecΓIdentity.{u}).inv
  left_triangle_components Y :=
    locallyRi

中文:
定义 adjunction
  签名: : Scheme.Γ.rightOp ⊣ Scheme.Spec.{u} where
  定义体: { app := fun X => ⟨locallyRingedSpaceAdjunction.{u}.unit.app X.toLocallyRingedSpace⟩
    naturality := fun _ _ f =>
      Scheme.Hom.ext' (locallyRingedSpaceAdjunction.{u}.unit.naturality f.toLRSHom) }
  counit := (NatIso.op Scheme.SpecΓIdentity.{u}).inv
  left_triangle_components Y :=
    locallyRi

Depends on / 依赖: NatIso, NatIso.op, Scheme, Scheme.Hom.ext, Scheme.Spec, X.toLocallyRingedSpace, Y.toLocallyRingedSpace, counit, f.toLRSHom, left_triangle_components, locallyRingedSpaceAdjunction, locallyRingedSpaceAdjunction.left_triangle_components, locallyRingedSpaceAdjunction.right_triangle_components, naturality, right_triangle_components, toLRSHom, toLocallyRingedSpace, unit.app, unit.naturality
-/
def adjunction : Scheme.Γ.rightOp ⊣ Scheme.Spec.{u} where
  unit :=
  { app := fun X => ⟨locallyRingedSpaceAdjunction.{u}.unit.app X.toLocallyRingedSpace⟩
    naturality := fun _ _ f =>
      Scheme.Hom.ext' (locallyRingedSpaceAdjunction.{u}.unit.naturality f.toLRSHom) }
  counit := (NatIso.op Scheme.SpecΓIdentity.{u}).inv
  left_triangle_components Y :=
    locallyRingedSpaceAdjunction.left_triangle_components Y.toLocallyRingedSpace
  right_triangle_components R :=
Scheme.Hom.ext' locallyRingedSpaceAdjunction.right_triangle_components R

/--
lemma `_root_.AlgebraicGeometry.ext_to_Spec` / 引理 `_root_.AlgebraicGeometry.ext_to_Spec`

English:
lemma _root_.AlgebraicGeometry.ext_to_Spec
  statement: {X : Scheme} {R : Type*} [CommRing R]
  proof: (ΓSpec.adjunction.homEquiv X (.op <| .of R)).symm.injective Opposite.unop_injective h

中文:
引理 _root_.AlgebraicGeometry.ext_to_Spec
  结论: {X : Scheme} {R : 类型} [CommRing R]
  证明: (ΓSpec.adjunction.homEquiv X (.op <| .of R)).symm.injective Opposite.unop_injective h

Depends on / 依赖: Opposite, Opposite.unop_injective, Spec.adjunction.homEquiv, adjunction, homEquiv, injective, symm.injective, unop_injective
-/
lemma _root_.AlgebraicGeometry.ext_to_Spec {X : Scheme} {R : Type*} [CommRing R]
    {f g : X ⟶ Spec (.of R)}
    (h : (Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map f.op =
      (Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map g.op) :
    f = g :=
(ΓSpec.adjunction.homEquiv X (.op <| .of R)).symm.injective Opposite.unop_injective h

/--
theorem `adjunction_homEquiv_apply` / 定理 `adjunction_homEquiv_apply`

English:
theorem adjunction_homEquiv_apply
  statement: {X : Scheme} {R : CommRingCatᵒᵖ}
  proof: rfl

中文:
定理 adjunction_homEquiv_apply
  结论: {X : Scheme} {R : CommRingCatᵒᵖ}
  证明: rfl
-/
theorem adjunction_homEquiv_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : (op <| Scheme.Γ.obj <| op X) ⟶ R) :
    ΓSpec.adjunction.homEquiv X R f = ⟨locallyRingedSpaceAdjunction.homEquiv X.1 R f⟩ := rfl

/--
theorem `adjunction_homEquiv_symm_apply` / 定理 `adjunction_homEquiv_symm_apply`

English:
theorem adjunction_homEquiv_symm_apply
  statement: {X : Scheme} {R : CommRingCatᵒᵖ}
  proof: rfl

中文:
定理 adjunction_homEquiv_symm_apply
  结论: {X : Scheme} {R : CommRingCatᵒᵖ}
  证明: rfl
-/
theorem adjunction_homEquiv_symm_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : X ⟶ Scheme.Spec.obj R) :
    (ΓSpec.adjunction.homEquiv X R).symm f =
      (locallyRingedSpaceAdjunction.homEquiv X.1 R).symm f.toLRSHom := rfl

/--
theorem `adjunction_counit_app'` / 定理 `adjunction_counit_app'`

English:
theorem adjunction_counit_app'
  given: {R : CommRingCatᵒᵖ}
  proof: rfl

@[simp]

中文:
定理 adjunction_counit_app'
  条件: {R : CommRingCatᵒᵖ}
  证明: rfl

@[simp]
-/
theorem adjunction_counit_app' {R : CommRingCatᵒᵖ} :
    ΓSpec.adjunction.counit.app R = locallyRingedSpaceAdjunction.counit.app R := rfl

@[simp]
/--
theorem `adjunction_counit_app` / 定理 `adjunction_counit_app`

English:
theorem adjunction_counit_app
  given: {R : CommRingCatᵒᵖ}
  proof: rfl

中文:
定理 adjunction_counit_app
  条件: {R : CommRingCatᵒᵖ}
  证明: rfl
-/
theorem adjunction_counit_app {R : CommRingCatᵒᵖ} :
    ΓSpec.adjunction.counit.app R = (Scheme.ΓSpecIso (unop R)).inv.op := rfl

/--
Definition of `_root_.AlgebraicGeometry.Scheme.toSpecΓ` / `_root_.AlgebraicGeometry.Scheme.toSpecΓ` 的定义

English:
definition _root_.AlgebraicGeometry.Scheme.toSpecΓ
  signature: (X : Scheme.{u})
  body: ΓSpec.adjunction.unit.app X

@[simp]

中文:
定义 _root_.AlgebraicGeometry.Scheme.toSpecΓ
  签名: (X : Scheme.{u})
  定义体: ΓSpec.adjunction.unit.app X

@[simp]

Depends on / 依赖: Spec.adjunction.unit.app, adjunction
-/
def _root_.AlgebraicGeometry.Scheme.toSpecΓ (X : Scheme.{u}) : X ⟶ Spec Γ(X, ⊤) :=
  ΓSpec.adjunction.unit.app X

@[simp]
/--
theorem `adjunction_unit_app` / 定理 `adjunction_unit_app`

English:
theorem adjunction_unit_app
  given: {X : Scheme}
  proof: rfl

中文:
定理 adjunction_unit_app
  条件: {X : Scheme}
  证明: rfl
-/
theorem adjunction_unit_app {X : Scheme} :
    ΓSpec.adjunction.unit.app X = X.toSpecΓ := rfl

/--
Instance `isIso_locallyRingedSpaceAdjunction_counit` / 实例 `isIso_locallyRingedSpaceAdjunction_counit`

English:
instance isIso_locallyRingedSpaceAdjunction_counit
  signature: :
  body: (NatIso.op SpecΓIdentity).isIso_inv

中文:
实例 isIso_locallyRingedSpaceAdjunction_counit
  签名: :
  定义体: (NatIso.op SpecΓIdentity).isIso_inv

Depends on / 依赖: NatIso, NatIso.op, isIso_inv
-/
instance isIso_locallyRingedSpaceAdjunction_counit :
    IsIso.{u + 1, u + 1} locallyRingedSpaceAdjunction.counit :=
  (NatIso.op SpecΓIdentity).isIso_inv

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isIso_adjunction_counit` / 实例 `isIso_adjunction_counit`

English:
instance isIso_adjunction_counit
  signature: : IsIso ΓSpec.adjunction.counit
  body: by
  apply +allowSynthFailures NatIso.isIso_of_isIso_app
  intro R
  rw [adjunction_counit_app]
  infer_instance

中文:
实例 isIso_adjunction_counit
  签名: : IsIso ΓSpec.adjunction.counit
  定义体: by
  apply +allowSynthFailures NatIso.isIso_of_isIso_app
  intro R
  rw [adjunction_counit_app]
  infer_instance

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, adjunction_counit_app, allowSynthFailures, infer_instance, isIso_of_isIso_app
-/
instance isIso_adjunction_counit : IsIso ΓSpec.adjunction.counit := by
  apply +allowSynthFailures NatIso.isIso_of_isIso_app
  intro R
  rw [adjunction_counit_app]
  infer_instance

end ΓSpec

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Scheme.toSpecΓ_apply` / 定理 `Scheme.toSpecΓ_apply`

English:
theorem Scheme.toSpecΓ_apply
  given: (X : Scheme.{u}) (x)
  proof: rfl

@[reassoc]

中文:
定理 Scheme.toSpecΓ_apply
  条件: (X : Scheme.{u}) (x)
  证明: rfl

@[reassoc]
-/
theorem Scheme.toSpecΓ_apply (X : Scheme.{u}) (x) :
    Scheme.toSpecΓ X x = Spec.map (X.presheaf.Γgerm x) (IsLocalRing.closedPoint _) := rfl

@[reassoc]
/--
theorem `Scheme.toSpecΓ_naturality` / 定理 `Scheme.toSpecΓ_naturality`

English:
theorem Scheme.toSpecΓ_naturality
  given: {X Y : Scheme.{u}} (f : X ⟶ Y)
  proof: ΓSpec.adjunction.unit.naturality f

中文:
定理 Scheme.toSpecΓ_naturality
  条件: {X Y : Scheme.{u}} (f : X ⟶ Y)
  证明: ΓSpec.adjunction.unit.naturality f

Depends on / 依赖: Spec.adjunction.unit.naturality, adjunction, naturality
-/
theorem Scheme.toSpecΓ_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f ≫ Y.toSpecΓ = X.toSpecΓ ≫ Spec.map f.appTop :=
  ΓSpec.adjunction.unit.naturality f

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `Scheme.toSpecΓ_appTop` / 定理 `Scheme.toSpecΓ_appTop`

English:
theorem Scheme.toSpecΓ_appTop
  given: (X : Scheme.{u})
  proof: by
  have := ΓSpec.adjunction.left_triangle_components X
  dsimp at this
  rw [← IsIso.eq_comp_inv] at this
  simp only [Category.id_comp] at this
  rw [← Quiver.Hom.op_inj.eq_iff]; rw [this]; rw [← op_inv]; rw [IsIso.Iso.inv_inv]

中文:
定理 Scheme.toSpecΓ_appTop
  条件: (X : Scheme.{u})
  证明: by
  have := ΓSpec.adjunction.left_triangle_components X
  dsimp at this
  rw [← IsIso.eq_comp_inv] at this
  simp only [Category.id_comp] at this
  rw [← Quiver.Hom.op_inj.eq_iff]; rw [this]; rw [← op_inv]; rw [IsIso.Iso.inv_inv]

Depends on / 依赖: Category, Category.id_comp, IsIso.Iso.inv_inv, IsIso.eq_comp_inv, Quiver, Quiver.Hom.op_inj.eq_iff, Spec.adjunction.left_triangle_components, adjunction, eq_comp_inv, eq_iff, id_comp, inv_inv, left_triangle_components, op_inj, op_inv
-/
theorem Scheme.toSpecΓ_appTop (X : Scheme.{u}) :
    X.toSpecΓ.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).hom := by
  have := ΓSpec.adjunction.left_triangle_components X
  dsimp at this
  rw [← IsIso.eq_comp_inv] at this
  simp only [Category.id_comp] at this
  rw [← Quiver.Hom.op_inj.eq_iff]; rw [this]; rw [← op_inv]; rw [IsIso.Iso.inv_inv]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `SpecMap_ΓSpecIso_hom` / 定理 `SpecMap_ΓSpecIso_hom`

English:
theorem SpecMap_ΓSpecIso_hom
  given: (R : CommRingCat.{u})
  proof: by
  have := ΓSpec.adjunction.right_triangle_components (op R)
  dsimp at this
  rwa [← IsIso.eq_comp_inv, Category.id_comp, ← Spec.map_inv, IsIso.Iso.inv_inv, eq_comm] at this

@[reassoc (attr := simp)]

中文:
定理 SpecMap_ΓSpecIso_hom
  条件: (R : CommRingCat.{u})
  证明: by
  have := ΓSpec.adjunction.right_triangle_components (op R)
  dsimp at this
  rwa [← IsIso.eq_comp_inv, Category.id_comp, ← Spec.map_inv, IsIso.Iso.inv_inv, eq_comm] at this

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.id_comp, IsIso.Iso.inv_inv, IsIso.eq_comp_inv, Spec.adjunction.right_triangle_components, Spec.map_inv, adjunction, eq_comm, eq_comp_inv, id_comp, inv_inv, map_inv, right_triangle_components
-/
theorem SpecMap_ΓSpecIso_hom (R : CommRingCat.{u}) :
    Spec.map ((Scheme.ΓSpecIso R).hom) = (Spec R).toSpecΓ := by
  have := ΓSpec.adjunction.right_triangle_components (op R)
  dsimp at this
  rwa [← IsIso.eq_comp_inv, Category.id_comp, ← Spec.map_inv, IsIso.Iso.inv_inv, eq_comm] at this

@[reassoc (attr := simp)]
/--
theorem `SpecMap_ΓSpecIso_inv_toSpecΓ` / 定理 `SpecMap_ΓSpecIso_inv_toSpecΓ`

English:
theorem SpecMap_ΓSpecIso_inv_toSpecΓ
  given: (R : CommRingCat.{u})
  proof: by
  rw [← SpecMap_ΓSpecIso_hom]; rw [← Spec.map_comp]; rw [Iso.hom_inv_id]; rw [Spec.map_id]

@[reassoc (attr := simp)]

中文:
定理 SpecMap_ΓSpecIso_inv_toSpecΓ
  条件: (R : CommRingCat.{u})
  证明: by
  rw [← SpecMap_ΓSpecIso_hom]; rw [← Spec.map_comp]; rw [Iso.hom_inv_id]; rw [Spec.map_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id, Spec.map_comp, Spec.map_id, hom_inv_id, map_comp, map_id
-/
theorem SpecMap_ΓSpecIso_inv_toSpecΓ (R : CommRingCat.{u}) :
    Spec.map (Scheme.ΓSpecIso R).inv ≫ (Spec R).toSpecΓ = 𝟙 _ := by
  rw [← SpecMap_ΓSpecIso_hom]; rw [← Spec.map_comp]; rw [Iso.hom_inv_id]; rw [Spec.map_id]

@[reassoc (attr := simp)]
/--
theorem `toSpecΓ_SpecMap_ΓSpecIso_inv` / 定理 `toSpecΓ_SpecMap_ΓSpecIso_inv`

English:
theorem toSpecΓ_SpecMap_ΓSpecIso_inv
  given: (R : CommRingCat.{u})
  proof: by
  rw [← SpecMap_ΓSpecIso_hom]; rw [← Spec.map_comp]; rw [Iso.inv_hom_id]; rw [Spec.map_id]

中文:
定理 toSpecΓ_SpecMap_ΓSpecIso_inv
  条件: (R : CommRingCat.{u})
  证明: by
  rw [← SpecMap_ΓSpecIso_hom]; rw [← Spec.map_comp]; rw [Iso.inv_hom_id]; rw [Spec.map_id]

Depends on / 依赖: Iso.inv_hom_id, Spec.map_comp, Spec.map_id, inv_hom_id, map_comp, map_id
-/
theorem toSpecΓ_SpecMap_ΓSpecIso_inv (R : CommRingCat.{u}) :
    (Spec R).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso R).inv = 𝟙 _ := by
  rw [← SpecMap_ΓSpecIso_hom]; rw [← Spec.map_comp]; rw [Iso.inv_hom_id]; rw [Spec.map_id]

/--
lemma `Scheme.toSpecΓ_preimage_basicOpen` / 引理 `Scheme.toSpecΓ_preimage_basicOpen`

English:
lemma Scheme.toSpecΓ_preimage_basicOpen
  given: (X : Scheme.{u}) (r : Γ(X, ⊤))
  proof: by
  rw [← basicOpen_eq_of_affine]; rw [Scheme.preimage_basicOpen]; rw [← Scheme.Hom.appTop]
  congr
  rw [Scheme.toSpecΓ_appTop]
  exact Iso.inv_hom_id_apply (C := CommRingCat) _ _

中文:
引理 Scheme.toSpecΓ_preimage_basicOpen
  条件: (X : Scheme.{u}) (r : Γ(X, ⊤))
  证明: by
  rw [← basicOpen_eq_of_affine]; rw [Scheme.preimage_basicOpen]; rw [← Scheme.Hom.appTop]
  congr
  rw [Scheme.toSpecΓ_appTop]
  exact Iso.inv_hom_id_apply (C := CommRingCat) _ _

Depends on / 依赖: CommRingCat, Iso.inv_hom_id_apply, Scheme, Scheme.Hom.appTop, Scheme.preimage_basicOpen, Scheme.toSpec, appTop, basicOpen_eq_of_affine, inv_hom_id_apply, preimage_basicOpen
-/
lemma Scheme.toSpecΓ_preimage_basicOpen (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen r = X.basicOpen r := by
  rw [← basicOpen_eq_of_affine]; rw [Scheme.preimage_basicOpen]; rw [← Scheme.Hom.appTop]
  congr
  rw [Scheme.toSpecΓ_appTop]
  exact Iso.inv_hom_id_apply (C := CommRingCat) _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `ΓSpecIso_inv_ΓSpec_adjunction_homEquiv` / 引理 `ΓSpecIso_inv_ΓSpec_adjunction_homEquiv`

English:
lemma ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
  given: {X : Scheme.{u}} {B : CommRingCat} (φ : B ⟶ Γ(X, ⊤))
  proof: by
  simp only [Adjunction.homEquiv_apply, Scheme.Spec_map, Opens.map_top, Scheme.Hom.comp_app]
  simp

中文:
引理 ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
  条件: {X : Scheme.{u}} {B : CommRingCat} (φ : B ⟶ Γ(X, ⊤))
  证明: by
  simp only [Adjunction.homEquiv_apply, Scheme.Spec_map, Opens.map_top, Scheme.Hom.comp_app]
  simp

Depends on / 依赖: Adjunction, Adjunction.homEquiv_apply, Opens.map_top, Scheme, Scheme.Hom.comp_app, Scheme.Spec_map, Spec_map, comp_app, homEquiv_apply, map_top
-/
lemma ΓSpecIso_inv_ΓSpec_adjunction_homEquiv {X : Scheme.{u}} {B : CommRingCat} (φ : B ⟶ Γ(X, ⊤)) :
    (Scheme.ΓSpecIso B).inv ≫ ((ΓSpec.adjunction.homEquiv X (op B)) φ.op).appTop = φ := by
  simp only [Adjunction.homEquiv_apply, Scheme.Spec_map, Opens.map_top, Scheme.Hom.comp_app]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ΓSpec_adjunction_homEquiv_eq` / 引理 `ΓSpec_adjunction_homEquiv_eq`

English:
lemma ΓSpec_adjunction_homEquiv_eq
  given: {X : Scheme.{u}} {B : CommRingCat} (φ : B ⟶ Γ(X, ⊤))
  proof: by
  rw [← Iso.inv_comp_eq]; rw [ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]

中文:
引理 ΓSpec_adjunction_homEquiv_eq
  条件: {X : Scheme.{u}} {B : CommRingCat} (φ : B ⟶ Γ(X, ⊤))
  证明: by
  rw [← Iso.inv_comp_eq]; rw [ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
lemma ΓSpec_adjunction_homEquiv_eq {X : Scheme.{u}} {B : CommRingCat} (φ : B ⟶ Γ(X, ⊤)) :
    ((ΓSpec.adjunction.homEquiv X (op B)) φ.op).appTop = (Scheme.ΓSpecIso B).hom ≫ φ := by
  rw [← Iso.inv_comp_eq]; rw [ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ΓSpecIso_obj_hom` / 定理 `ΓSpecIso_obj_hom`

English:
theorem ΓSpecIso_obj_hom
  given: {X : Scheme.{u}} (U : X.Opens)
  proof: by simp

中文:
定理 ΓSpecIso_obj_hom
  条件: {X : Scheme.{u}} (U : X.Opens)
  证明: by simp
-/
theorem ΓSpecIso_obj_hom {X : Scheme.{u}} (U : X.Opens) :
    (Scheme.ΓSpecIso Γ(X, U)).hom = (Spec.map U.topIso.inv).appTop ≫
      U.toScheme.toSpecΓ.appTop ≫ U.topIso.hom := by simp

/-! Immediate consequences of the adjunction. -/

/--
Definition of `Spec.fullyFaithfulToLocallyRingedSpace` / `Spec.fullyFaithfulToLocallyRingedSpace` 的定义

English:
definition Spec.fullyFaithfulToLocallyRingedSpace
  signature: : Spec.toLocallyRingedSpace.FullyFaithful
  body: ΓSpec.locallyRingedSpaceAdjunction.fullyFaithfulROfIsIsoCounit

中文:
定义 Spec.fullyFaithfulToLocallyRingedSpace
  签名: : Spec.toLocallyRingedSpace.FullyFaithful
  定义体: ΓSpec.locallyRingedSpaceAdjunction.fullyFaithfulROfIsIsoCounit

Depends on / 依赖: Spec.locallyRingedSpaceAdjunction.fullyFaithfulROfIsIsoCounit, fullyFaithfulROfIsIsoCounit, locallyRingedSpaceAdjunction
-/
def Spec.fullyFaithfulToLocallyRingedSpace : Spec.toLocallyRingedSpace.FullyFaithful :=
  ΓSpec.locallyRingedSpaceAdjunction.fullyFaithfulROfIsIsoCounit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Spec.toLocallyRingedSpace.Full
  body: Spec.fullyFaithfulToLocallyRingedSpace.full

中文:
实例 :
  签名: Spec.toLocallyRingedSpace.Full
  定义体: Spec.fullyFaithfulToLocallyRingedSpace.full

Depends on / 依赖: Spec.fullyFaithfulToLocallyRingedSpace.full, fullyFaithfulToLocallyRingedSpace
-/
instance : Spec.toLocallyRingedSpace.Full :=
  Spec.fullyFaithfulToLocallyRingedSpace.full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Spec.toLocallyRingedSpace.Faithful
  body: Spec.fullyFaithfulToLocallyRingedSpace.faithful

中文:
实例 :
  签名: Spec.toLocallyRingedSpace.Faithful
  定义体: Spec.fullyFaithfulToLocallyRingedSpace.faithful

Depends on / 依赖: Spec.fullyFaithfulToLocallyRingedSpace.faithful, faithful, fullyFaithfulToLocallyRingedSpace
-/
instance : Spec.toLocallyRingedSpace.Faithful :=
  Spec.fullyFaithfulToLocallyRingedSpace.faithful

/--
Definition of `Spec.fullyFaithful` / `Spec.fullyFaithful` 的定义

English:
definition Spec.fullyFaithful
  signature: : Scheme.Spec.FullyFaithful
  body: ΓSpec.adjunction.fullyFaithfulROfIsIsoCounit

中文:
定义 Spec.fullyFaithful
  签名: : Scheme.Spec.FullyFaithful
  定义体: ΓSpec.adjunction.fullyFaithfulROfIsIsoCounit

Depends on / 依赖: Spec.adjunction.fullyFaithfulROfIsIsoCounit, adjunction, fullyFaithfulROfIsIsoCounit
-/
def Spec.fullyFaithful : Scheme.Spec.FullyFaithful :=
  ΓSpec.adjunction.fullyFaithfulROfIsIsoCounit

/--
Instance `Spec.full` / 实例 `Spec.full`

English:
instance Spec.full
  signature: : Scheme.Spec.Full
  body: Spec.fullyFaithful.full

中文:
实例 Spec.full
  签名: : Scheme.Spec.Full
  定义体: Spec.fullyFaithful.full

Depends on / 依赖: Spec.fullyFaithful.full, fullyFaithful
-/
instance Spec.full : Scheme.Spec.Full :=
  Spec.fullyFaithful.full

/--
Instance `Spec.faithful` / 实例 `Spec.faithful`

English:
instance Spec.faithful
  signature: : Scheme.Spec.Faithful
  body: Spec.fullyFaithful.faithful

中文:
实例 Spec.faithful
  签名: : Scheme.Spec.Faithful
  定义体: Spec.fullyFaithful.faithful

Depends on / 依赖: Spec.fullyFaithful.faithful, faithful, fullyFaithful
-/
instance Spec.faithful : Scheme.Spec.Faithful :=
  Spec.fullyFaithful.faithful

section

variable {R S : CommRingCat.{u}} {φ ψ : R ⟶ S} (f : Spec S ⟶ Spec R)

/--
lemma `Spec.map_inj` / 引理 `Spec.map_inj`

English:
lemma Spec.map_inj
  statement: Spec.map φ = Spec.map ψ ↔ φ = ψ
  proof: by
  rw [iff_comm]; rw [← Quiver.Hom.op_inj.eq_iff]; rw [← Scheme.Spec.map_injective.eq_iff]
  rfl

中文:
引理 Spec.map_inj
  结论: Spec.map φ = Spec.map ψ ↔ φ = ψ
  证明: by
  rw [iff_comm]; rw [← Quiver.Hom.op_inj.eq_iff]; rw [← Scheme.Spec.map_injective.eq_iff]
  rfl

Depends on / 依赖: Quiver, Quiver.Hom.op_inj.eq_iff, Scheme, Scheme.Spec.map_injective.eq_iff, eq_iff, iff_comm, map_injective, op_inj
-/
lemma Spec.map_inj : Spec.map φ = Spec.map ψ ↔ φ = ψ := by
  rw [iff_comm]; rw [← Quiver.Hom.op_inj.eq_iff]; rw [← Scheme.Spec.map_injective.eq_iff]
  rfl

/--
lemma `Spec.map_injective` / 引理 `Spec.map_injective`

English:
lemma Spec.map_injective
  given: {R S : CommRingCat}
  statement: Function.Injective (Spec.map : (R ⟶ S) -> _)
  proof: fun _ _ => Spec.map_inj.mp

@[simp]

中文:
引理 Spec.map_injective
  条件: {R S : CommRingCat}
  结论: Function.Injective (Spec.map : (R ⟶ S) -> _)
  证明: fun _ _ => Spec.map_inj.mp

@[simp]

Depends on / 依赖: Spec.map_inj.mp, map_inj
-/
lemma Spec.map_injective {R S : CommRingCat} : Function.Injective (Spec.map : (R ⟶ S) -> _) :=
  fun _ _ => Spec.map_inj.mp

@[simp]
/--
lemma `Spec.map_eq_id` / 引理 `Spec.map_eq_id`

English:
lemma Spec.map_eq_id
  given: {R : CommRingCat} {ϕ : R ⟶ R}
  statement: Spec.map ϕ = 𝟙 (Spec R) ↔ ϕ = 𝟙 R
  proof: by
  simp [← map_inj]

中文:
引理 Spec.map_eq_id
  条件: {R : CommRingCat} {ϕ : R ⟶ R}
  结论: Spec.map ϕ = 𝟙 (Spec R) ↔ ϕ = 𝟙 R
  证明: by
  simp [← map_inj]

Depends on / 依赖: map_inj
-/
lemma Spec.map_eq_id {R : CommRingCat} {ϕ : R ⟶ R} : Spec.map ϕ = 𝟙 (Spec R) ↔ ϕ = 𝟙 R := by
  simp [← map_inj]

/--
Definition of `Spec.preimage` / `Spec.preimage` 的定义

English:
definition Spec.preimage
  signature: : R ⟶ S
  body: (Scheme.Spec.preimage f).unop

中文:
定义 Spec.preimage
  签名: : R ⟶ S
  定义体: (Scheme.Spec.preimage f).unop

Depends on / 依赖: Scheme, Scheme.Spec.preimage, preimage
-/
def Spec.preimage : R ⟶ S := (Scheme.Spec.preimage f).unop

/--
lemma `Spec.map_preimage` / 引理 `Spec.map_preimage`

English:
lemma Spec.map_preimage
  statement: Spec.map (Spec.preimage f) = f
  proof: Scheme.Spec.map_preimage f

中文:
引理 Spec.map_preimage
  结论: Spec.map (Spec.preimage f) = f
  证明: Scheme.Spec.map_preimage f
-/
@[simp] lemma Spec.map_preimage : Spec.map (Spec.preimage f) = f := Scheme.Spec.map_preimage f

/--
lemma `Spec.map_preimage_unop` / 引理 `Spec.map_preimage_unop`

English:
lemma Spec.map_preimage_unop
  given: (f : Spec R ⟶ Spec S)
  proof: Spec.fullyFaithful.map_preimage _

中文:
引理 Spec.map_preimage_unop
  条件: (f : Spec R ⟶ Spec S)
  证明: Spec.fullyFaithful.map_preimage _
-/
@[simp] lemma Spec.map_preimage_unop (f : Spec R ⟶ Spec S) :
    Spec.map (Spec.fullyFaithful.preimage f).unop = f := Spec.fullyFaithful.map_preimage _

variable (φ) in
/--
lemma `Spec.preimage_map` / 引理 `Spec.preimage_map`

English:
lemma Spec.preimage_map
  statement: Spec.preimage (Spec.map φ) = φ
  proof: Spec.map_injective (Spec.map_preimage (Spec.map φ))

中文:
引理 Spec.preimage_map
  结论: Spec.preimage (Spec.map φ) = φ
  证明: Spec.map_injective (Spec.map_preimage (Spec.map φ))

Depends on / 依赖: ObjectProperty, ObjectProperty.hom_ext, SimplexCategory, SimplexCategory.Hom.ext, hom_ext
-/
@[simp] lemma Spec.preimage_map : Spec.preimage (Spec.map φ) = φ :=
  Spec.map_injective (Spec.map_preimage (Spec.map φ))

/--
lemma `Spec.map_surjective` / 引理 `Spec.map_surjective`

English:
lemma Spec.map_surjective
  given: {R S : CommRingCat}
  proof: by
  intro f
  use Spec.preimage f
  simp

中文:
引理 Spec.map_surjective
  条件: {R S : CommRingCat}
  证明: by
  intro f
  use Spec.preimage f
  simp

Depends on / 依赖: Spec.preimage, preimage
-/
lemma Spec.map_surjective {R S : CommRingCat} :
    Function.Surjective (Spec.map : (R ⟶ S) -> _) := by
  intro f
  use Spec.preimage f
  simp

/-- Spec is fully faithful -/
@[simps]
/--
Definition of `Spec.homEquiv` / `Spec.homEquiv` 的定义

English:
definition Spec.homEquiv
  signature: {R S : CommRingCat}
  body: Spec.preimage
  invFun := Spec.map
  left_inv := Spec.map_preimage
  right_inv := Spec.preimage_map

@[simp]

中文:
定义 Spec.homEquiv
  签名: {R S : CommRingCat}
  定义体: Spec.preimage
  invFun := Spec.map
  left_inv := Spec.map_preimage
  right_inv := Spec.preimage_map

@[simp]

Depends on / 依赖: Spec.preimage, preimage
-/
def Spec.homEquiv {R S : CommRingCat} : (Spec S ⟶ Spec R) ≃ (R ⟶ S) where
  toFun := Spec.preimage
  invFun := Spec.map
  left_inv := Spec.map_preimage
  right_inv := Spec.preimage_map

@[simp]
/--
lemma `Spec.preimage_id` / 引理 `Spec.preimage_id`

English:
lemma Spec.preimage_id
  given: {R : CommRingCat}
  statement: Spec.preimage (𝟙 (Spec R)) = 𝟙 R
  proof: Spec.map_injective (by simp)

@[simp, reassoc]

中文:
引理 Spec.preimage_id
  条件: {R : CommRingCat}
  结论: Spec.preimage (𝟙 (Spec R)) = 𝟙 R
  证明: Spec.map_injective (by simp)

@[simp, reassoc]

Depends on / 依赖: Spec.map_injective, map_injective
-/
lemma Spec.preimage_id {R : CommRingCat} : Spec.preimage (𝟙 (Spec R)) = 𝟙 R :=
  Spec.map_injective (by simp)

@[simp, reassoc]
/--
lemma `Spec.preimage_comp` / 引理 `Spec.preimage_comp`

English:
lemma Spec.preimage_comp
  given: {R S T : CommRingCat} (f : Spec R ⟶ Spec S) (g : Spec S ⟶ Spec T)
  proof: Spec.map_injective (by simp)

中文:
引理 Spec.preimage_comp
  条件: {R S T : CommRingCat} (f : Spec R ⟶ Spec S) (g : Spec S ⟶ Spec T)
  证明: Spec.map_injective (by simp)

Depends on / 依赖: Spec.map_injective, map_injective
-/
lemma Spec.preimage_comp {R S T : CommRingCat} (f : Spec R ⟶ Spec S) (g : Spec S ⟶ Spec T) :
    Spec.preimage (f ≫ g) = Spec.preimage g ≫ Spec.preimage f :=
  Spec.map_injective (by simp)

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Reflective Spec.toLocallyRingedSpace
  body: Γ.rightOp
  adj := ΓSpec.locallyRingedSpaceAdjunction

中文:
实例 :
  签名: Reflective Spec.toLocallyRingedSpace
  定义体: Γ.rightOp
  adj := ΓSpec.locallyRingedSpaceAdjunction

Depends on / 依赖: rightOp
-/
instance : Reflective Spec.toLocallyRingedSpace where
  L := Γ.rightOp
  adj := ΓSpec.locallyRingedSpaceAdjunction

/--
Instance `Spec.reflective` / 实例 `Spec.reflective`

English:
instance Spec.reflective
  signature: : Reflective Scheme.Spec where
  body: Scheme.Γ.rightOp
  adj := ΓSpec.adjunction

中文:
实例 Spec.reflective
  签名: : Reflective Scheme.Spec where
  定义体: Scheme.Γ.rightOp
  adj := ΓSpec.adjunction

Depends on / 依赖: Scheme, rightOp
-/
instance Spec.reflective : Reflective Scheme.Spec where
  L := Scheme.Γ.rightOp
  adj := ΓSpec.adjunction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyRingedSpace.Γ.IsRightAdjoint
  body: ΓSpec.locallyRingedSpaceAdjunction.rightOp.isRightAdjoint

中文:
实例 :
  签名: LocallyRingedSpace.Γ.IsRightAdjoint
  定义体: ΓSpec.locallyRingedSpaceAdjunction.rightOp.isRightAdjoint

Depends on / 依赖: Spec.locallyRingedSpaceAdjunction.rightOp.isRightAdjoint, isRightAdjoint, locallyRingedSpaceAdjunction, rightOp
-/
instance : LocallyRingedSpace.Γ.IsRightAdjoint :=
  ΓSpec.locallyRingedSpaceAdjunction.rightOp.isRightAdjoint

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Scheme.Γ.IsRightAdjoint
  body: ΓSpec.adjunction.rightOp.isRightAdjoint

中文:
实例 :
  签名: Scheme.Γ.IsRightAdjoint
  定义体: ΓSpec.adjunction.rightOp.isRightAdjoint

Depends on / 依赖: Spec.adjunction.rightOp.isRightAdjoint, adjunction, isRightAdjoint, rightOp
-/
instance : Scheme.Γ.IsRightAdjoint := ΓSpec.adjunction.rightOp.isRightAdjoint

end AlgebraicGeometry
