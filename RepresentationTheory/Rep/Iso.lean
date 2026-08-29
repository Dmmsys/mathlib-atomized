/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Equivalence between `Rep k G` and `ModuleCat k[G]`

In this file we show that the category of `k`-linear representations of a monoid `G` is
equivalent to the category of modules over the monoid algebra `k[G]`.
-/

@[expose] public section

universe w w' u u' v v'

namespace Rep

open CategoryTheory
open scoped MonoidAlgebra

suppress_compilation

section Group

variable (k G H : Type u) [Group G] [Monoid H] [MulAction G H] [CommRing k] (n : Nat)

open MonoidalCategory Finsupp Representation.IntertwiningMap

/--
Definition of `diagonalSuccIsoTensorTrivial` / `diagonalSuccIsoTensorTrivial` 的定义

English:
abbreviation diagonalSuccIsoTensorTrivial
  signature: :
  body: linearizationOfMulActionIso k G (Fin (n + 1) -> G) ≪≫ (linearization k G).mapIso
    (Action.diagonalSuccIsoTensorTrivial G n) ≪≫
    (Functor.Monoidal.μIso (linearization k G) _ _).symm ≪≫
    tensorIso (linearizationOfMulActionIso k G G) (linearizationTrivialIso k G (Fin n -> G))

中文:
缩写 diagonalSuccIsoTensorTrivial
  签名: :
  定义体: linearizationOfMulActionIso k G (Fin (n + 1) -> G) ≪≫ (linearization k G).mapIso
    (Action.diagonalSuccIsoTensorTrivial G n) ≪≫
    (Functor.Monoidal.μIso (linearization k G) _ _).symm ≪≫
    tensorIso (linearizationOfMulActionIso k G G) (linearizationTrivialIso k G (Fin n -> G))

Depends on / 依赖: Action, Action.diagonalSuccIsoTensorTrivial, Functor, Functor.Monoidal, Monoidal, diagonalSuccIsoTensorTrivial, linearization, linearizationOfMulActionIso, linearizationTrivialIso, mapIso, tensorIso
-/
abbrev diagonalSuccIsoTensorTrivial :
    diagonal k G (n + 1) ≅ leftRegular k G otimes trivial k G k[Fin n -> G] :=
  linearizationOfMulActionIso k G (Fin (n + 1) -> G) ≪≫ (linearization k G).mapIso
    (Action.diagonalSuccIsoTensorTrivial G n) ≪≫
    (Functor.Monoidal.μIso (linearization k G) _ _).symm ≪≫
    tensorIso (linearizationOfMulActionIso k G G) (linearizationTrivialIso k G (Fin n -> G))

/--
Definition of `diagonalSuccIsoFree` / `diagonalSuccIsoFree` 的定义

English:
abbreviation diagonalSuccIsoFree
  signature: : diagonal k G (n + 1) ≅ free k G (Fin n -> G)
  body: diagonalSuccIsoTensorTrivial k G n ≪≫ leftRegularTensorTrivialIsoFree k G (Fin n -> G)

中文:
缩写 diagonalSuccIsoFree
  签名: : diagonal k G (n + 1) ≅ free k G (Fin n -> G)
  定义体: diagonalSuccIsoTensorTrivial k G n ≪≫ leftRegularTensorTrivialIsoFree k G (Fin n -> G)

Depends on / 依赖: diagonalSuccIsoTensorTrivial, leftRegularTensorTrivialIsoFree
-/
abbrev diagonalSuccIsoFree : diagonal k G (n + 1) ≅ free k G (Fin n -> G) :=
  diagonalSuccIsoTensorTrivial k G n ≪≫ leftRegularTensorTrivialIsoFree k G (Fin n -> G)

variable (A : Rep k G)

/--
Definition of `diagonalHomEquiv` / `diagonalHomEquiv` 的定义

English:
abbreviation diagonalHomEquiv
  signature: :
  body: Linear.homCongr k (diagonalSuccIsoFree k G n) (Iso.refl _) ≪≫ₗ
    freeLiftLEquiv k G (Fin n -> G) A

中文:
缩写 diagonalHomEquiv
  签名: :
  定义体: Linear.homCongr k (diagonalSuccIsoFree k G n) (Iso.refl _) ≪≫ₗ
    freeLiftLEquiv k G (Fin n -> G) A

Depends on / 依赖: Iso.refl, Linear, Linear.homCongr, diagonalSuccIsoFree, freeLiftLEquiv, homCongr
-/
abbrev diagonalHomEquiv :
    (Rep.diagonal k G (n + 1) ⟶ A) ≃ₗ[k] (Fin n -> G) -> A :=
  Linear.homCongr k (diagonalSuccIsoFree k G n) (Iso.refl _) ≪≫ₗ
    freeLiftLEquiv k G (Fin n -> G) A

end Group

/-!
### The categorical equivalence `Rep k G ≌ Module.{u} k[G]`.
-/


variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

open MonoidAlgebra

/--
theorem `to_Module_monoidAlgebra_map_aux` / 定理 `to_Module_monoidAlgebra_map_aux`

English:
theorem to_Module_monoidAlgebra_map_aux
  statement: {k G : Type*} [CommRing k] [Monoid G] (V W : Type*)
  proof: by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_single, MonoidAlgebra.of_apply]
    exact LinearMap.congr_fun (w g) x
  · intro g h gw hw; simp only [map_add, LinearMap.add_apply, hw, gw]
  · intro r g w
    simp only [map_smul, w, LinearMap.smul_apply

中文:
定理 to_Module_monoidAlgebra_map_aux
  结论: {k G : 类型} [CommRing k] [Monoid G] (V W : 类型)
  证明: by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_single, MonoidAlgebra.of_apply]
    exact LinearMap.congr_fun (w g) x
  · intro g h gw hw; simp only [map_add, LinearMap.add_apply, hw, gw]
  · intro r g w
    simp only [map_smul, w, LinearMap.smul_apply

Depends on / 依赖: LinearMap, LinearMap.add_apply, LinearMap.congr_fun, LinearMap.smul_apply, MonoidAlgebra, MonoidAlgebra.induction_on, MonoidAlgebra.lift_single, MonoidAlgebra.of_apply, add_apply, congr_fun, induction_on, lift_single, map_add, map_smul, of_apply, one_smul, smul_apply
-/
theorem to_Module_monoidAlgebra_map_aux {k G : Type*} [CommRing k] [Monoid G] (V W : Type*)
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W] (ρ : G ->* V ->ₗ[k] V)
    (σ : G ->* W ->ₗ[k] W) (f : V ->ₗ[k] W) (w : forall g : G, f.comp (ρ g) = (σ g).comp f)
    (r : k[G]) (x : V) :
    f (MonoidAlgebra.lift k (V ->ₗ[k] V) G ρ r x) =
      MonoidAlgebra.lift k (W ->ₗ[k] W) G σ r (f x) := by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_single, MonoidAlgebra.of_apply]
    exact LinearMap.congr_fun (w g) x
  · intro g h gw hw; simp only [map_add, LinearMap.add_apply, hw, gw]
  · intro r g w
    simp only [map_smul, w, LinearMap.smul_apply]

/--
Definition of `toModuleMonoidAlgebraMap` / `toModuleMonoidAlgebraMap` 的定义

English:
definition toModuleMonoidAlgebraMap
  signature: {V W : Rep.{w} k G} (f : V ⟶ W)
  body: ModuleCat.ofHom
    { f.hom.toLinearMap with
      map_smul' := fun r x => to_Module_monoidAlgebra_map_aux V.V W.V V.ρ W.ρ
        f.hom.toLinearMap f.hom.2 r x }

中文:
定义 toModuleMonoidAlgebraMap
  签名: {V W : Rep.{w} k G} (f : V ⟶ W)
  定义体: ModuleCat.ofHom
    { f.hom.toLinearMap with
      map_smul' := fun r x => to_Module_monoidAlgebra_map_aux V.V W.V V.ρ W.ρ
        f.hom.toLinearMap f.hom.2 r x }

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, f.hom, f.hom.toLinearMap, map_smul, toLinearMap, to_Module_monoidAlgebra_map_aux
-/
def toModuleMonoidAlgebraMap {V W : Rep.{w} k G} (f : V ⟶ W) :
    ModuleCat.of k[G] V.ρ.asModule ⟶ ModuleCat.of k[G] W.ρ.asModule :=
  ModuleCat.ofHom
    { f.hom.toLinearMap with
      map_smul' := fun r x => to_Module_monoidAlgebra_map_aux V.V W.V V.ρ W.ρ
        f.hom.toLinearMap f.hom.2 r x }

/--
Definition of `toModuleMonoidAlgebra` / `toModuleMonoidAlgebra` 的定义

English:
definition toModuleMonoidAlgebra
  signature: : Rep.{w} k G ⥤ ModuleCat k[G] where
  body: ModuleCat.of _ V.ρ.asModule
  map f := toModuleMonoidAlgebraMap f

中文:
定义 toModuleMonoidAlgebra
  签名: : Rep.{w} k G ⥤ ModuleCat k[G] where
  定义体: ModuleCat.of _ V.ρ.asModule
  map f := toModuleMonoidAlgebraMap f

Depends on / 依赖: ModuleCat, ModuleCat.of, asModule
-/
def toModuleMonoidAlgebra : Rep.{w} k G ⥤ ModuleCat k[G] where
  obj V := ModuleCat.of _ V.ρ.asModule
  map f := toModuleMonoidAlgebraMap f

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofModuleMonoidAlgebra` / `ofModuleMonoidAlgebra` 的定义

English:
definition ofModuleMonoidAlgebra
  signature: : ModuleCat k[G] ⥤ Rep.{w} k G where
  body: Rep.of (Representation.ofModule M)
  map f := ofHom {
    __ := f.hom
    map_smul' r x := f.hom.map_smul (algebraMap k _ r) x
    isIntertwining' g := by ext; apply f.hom.map_smul
  }

中文:
定义 ofModuleMonoidAlgebra
  签名: : ModuleCat k[G] ⥤ Rep.{w} k G where
  定义体: Rep.of (Representation.ofModule M)
  map f := ofHom {
    __ := f.hom
    map_smul' r x := f.hom.map_smul (algebraMap k _ r) x
    isIntertwining' g := by ext; apply f.hom.map_smul
  }

Depends on / 依赖: Rep.of, Representation, Representation.ofModule, ofModule
-/
def ofModuleMonoidAlgebra : ModuleCat k[G] ⥤ Rep.{w} k G where
  obj M := Rep.of (Representation.ofModule M)
  map f := ofHom {
    __ := f.hom
    map_smul' r x := f.hom.map_smul (algebraMap k _ r) x
    isIntertwining' g := by ext; apply f.hom.map_smul
  }

/--
theorem `ofModuleMonoidAlgebra_obj_coe` / 定理 `ofModuleMonoidAlgebra_obj_coe`

English:
theorem ofModuleMonoidAlgebra_obj_coe
  given: (M : ModuleCat.{w} k[G])
  proof: rfl

中文:
定理 ofModuleMonoidAlgebra_obj_coe
  条件: (M : ModuleCat.{w} k[G])
  证明: rfl
-/
theorem ofModuleMonoidAlgebra_obj_coe (M : ModuleCat.{w} k[G]) :
    ofModuleMonoidAlgebra.obj M = RestrictScalars k k[G] M :=
  rfl

/--
theorem `ofModuleMonoidAlgebra_obj_ρ` / 定理 `ofModuleMonoidAlgebra_obj_ρ`

English:
theorem ofModuleMonoidAlgebra_obj_ρ
  given: (M : ModuleCat.{w} k[G])
  proof: rfl

中文:
定理 ofModuleMonoidAlgebra_obj_ρ
  条件: (M : ModuleCat.{w} k[G])
  证明: rfl
-/
theorem ofModuleMonoidAlgebra_obj_ρ (M : ModuleCat.{w} k[G]) :
    (ofModuleMonoidAlgebra.obj M).ρ = Representation.ofModule M :=
  rfl

/--
Definition of `counitIsoAddEquiv` / `counitIsoAddEquiv` 的定义

English:
definition counitIsoAddEquiv
  signature: {M : ModuleCat.{w} k[G]}
  body: by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact (Representation.ofModule M).asModuleEquiv.toAddEquiv.trans
    (RestrictScalars.addEquiv k k[G] _)

中文:
定义 counitIsoAddEquiv
  签名: {M : ModuleCat.{w} k[G]}
  定义体: by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact (Representation.ofModule M).asModuleEquiv.toAddEquiv.trans
    (RestrictScalars.addEquiv k k[G] _)

Depends on / 依赖: Representation, Representation.ofModule, RestrictScalars, RestrictScalars.addEquiv, addEquiv, asModuleEquiv, asModuleEquiv.toAddEquiv.trans, ofModule, ofModuleMonoidAlgebra, toAddEquiv, toModuleMonoidAlgebra
-/
def counitIsoAddEquiv {M : ModuleCat.{w} k[G]} :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≃+ M := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact (Representation.ofModule M).asModuleEquiv.toAddEquiv.trans
    (RestrictScalars.addEquiv k k[G] _)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `unitIsoAddEquiv` / `unitIsoAddEquiv` 的定义

English:
definition unitIsoAddEquiv
  signature: {V : Rep.{w} k G}
  body: by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact V.ρ.asModuleEquiv.symm.toAddEquiv.trans (RestrictScalars.addEquiv _ _ _).symm

中文:
定义 unitIsoAddEquiv
  签名: {V : Rep.{w} k G}
  定义体: by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact V.ρ.asModuleEquiv.symm.toAddEquiv.trans (RestrictScalars.addEquiv _ _ _).symm

Depends on / 依赖: RestrictScalars, RestrictScalars.addEquiv, addEquiv, asModuleEquiv, asModuleEquiv.symm.toAddEquiv.trans, ofModuleMonoidAlgebra, toAddEquiv, toModuleMonoidAlgebra
-/
def unitIsoAddEquiv {V : Rep.{w} k G} : V ≃+ (toModuleMonoidAlgebra ⋙
    ofModuleMonoidAlgebra).obj V := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact V.ρ.asModuleEquiv.symm.toAddEquiv.trans (RestrictScalars.addEquiv _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `counitIso` / `counitIso` 的定义

English:
definition counitIso
  signature: (M : ModuleCat.{w} k[G])
  body: LinearEquiv.toModuleIso
    { counitIsoAddEquiv with
      map_smul' := fun r x => by
        simp [counitIsoAddEquiv] }

中文:
定义 counitIso
  签名: (M : ModuleCat.{w} k[G])
  定义体: LinearEquiv.toModuleIso
    { counitIsoAddEquiv with
      map_smul' := fun r x => by
        simp [counitIsoAddEquiv] }

Depends on / 依赖: LinearEquiv, LinearEquiv.toModuleIso, counitIsoAddEquiv, map_smul, toModuleIso
-/
def counitIso (M : ModuleCat.{w} k[G]) :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≅ M :=
  LinearEquiv.toModuleIso
    { counitIsoAddEquiv with
      map_smul' := fun r x => by
        simp [counitIsoAddEquiv] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `unit_iso_comm` / 定理 `unit_iso_comm`

English:
theorem unit_iso_comm
  given: (V : Rep.{w} k G) (g : G) (x : V)
  proof: by
  simp [unitIsoAddEquiv, ofModuleMonoidAlgebra, toModuleMonoidAlgebra]

中文:
定理 unit_iso_comm
  条件: (V : Rep.{w} k G) (g : G) (x : V)
  证明: by
  simp [unitIsoAddEquiv, ofModuleMonoidAlgebra, toModuleMonoidAlgebra]

Depends on / 依赖: ofModuleMonoidAlgebra, toModuleMonoidAlgebra, unitIsoAddEquiv
-/
theorem unit_iso_comm (V : Rep.{w} k G) (g : G) (x : V) :
    unitIsoAddEquiv ((V.ρ g).toFun x) = ((ofModuleMonoidAlgebra.obj
      (toModuleMonoidAlgebra.obj V)).ρ g).toFun (unitIsoAddEquiv x) := by
  simp [unitIsoAddEquiv, ofModuleMonoidAlgebra, toModuleMonoidAlgebra]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `unitIso` / `unitIso` 的定义

English:
definition unitIso
  signature: (V : Rep.{w} k G)
  body: mkIso .mk
  { unitIsoAddEquiv (k := k) (G := G) with
    map_smul' r x := show (RestrictScalars.addEquiv _ _ _).symm
      (V.ρ.asModuleEquiv.symm (r • x)) = _ by
      simp only [Representation.asModuleEquiv_symm_map_smul]
      rfl } fun g => by ext; exact unit_iso_comm ..

中文:
定义 unitIso
  签名: (V : Rep.{w} k G)
  定义体: mkIso .mk
  { unitIsoAddEquiv (k := k) (G := G) with
    map_smul' r x := show (RestrictScalars.addEquiv _ _ _).symm
      (V.ρ.asModuleEquiv.symm (r • x)) = _ by
      simp only [Representation.asModuleEquiv_symm_map_smul]
      rfl } fun g => by ext; exact unit_iso_comm ..

Depends on / 依赖: Representation, Representation.asModuleEquiv_symm_map_smul, RestrictScalars, RestrictScalars.addEquiv, addEquiv, asModuleEquiv, asModuleEquiv.symm, asModuleEquiv_symm_map_smul, map_smul, unitIsoAddEquiv, unit_iso_comm
-/
def unitIso (V : Rep.{w} k G) : V ≅ (toModuleMonoidAlgebra ⋙ ofModuleMonoidAlgebra).obj V :=
mkIso .mk
  { unitIsoAddEquiv (k := k) (G := G) with
    map_smul' r x := show (RestrictScalars.addEquiv _ _ _).symm
      (V.ρ.asModuleEquiv.symm (r • x)) = _ by
      simp only [Representation.asModuleEquiv_symm_map_smul]
      rfl } fun g => by ext; exact unit_iso_comm ..

/--
Definition of `equivalenceModuleMonoidAlgebra` / `equivalenceModuleMonoidAlgebra` 的定义

English:
definition equivalenceModuleMonoidAlgebra
  signature: : Rep.{w} k G ≌ ModuleCat k[G] where
  body: toModuleMonoidAlgebra
  inverse := ofModuleMonoidAlgebra
  unitIso := NatIso.ofComponents (fun V => unitIso V) (by cat_disch)
  counitIso := NatIso.ofComponents (fun M => counitIso M) (by cat_disch)

中文:
定义 equivalenceModuleMonoidAlgebra
  签名: : Rep.{w} k G ≌ ModuleCat k[G] where
  定义体: toModuleMonoidAlgebra
  inverse := ofModuleMonoidAlgebra
  unitIso := NatIso.ofComponents (fun V => unitIso V) (by cat_disch)
  counitIso := NatIso.ofComponents (fun M => counitIso M) (by cat_disch)

Depends on / 依赖: toModuleMonoidAlgebra
-/
def equivalenceModuleMonoidAlgebra : Rep.{w} k G ≌ ModuleCat k[G] where
  functor := toModuleMonoidAlgebra
  inverse := ofModuleMonoidAlgebra
  unitIso := NatIso.ofComponents (fun V => unitIso V) (by cat_disch)
  counitIso := NatIso.ofComponents (fun M => counitIso M) (by cat_disch)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toModuleMonoidAlgebra.{w} (k := k) (G := G)).IsEquivalence
  body: (equivalenceModuleMonoidAlgebra (k := k) (G := G)).isEquivalence_functor

中文:
实例 :
  签名: (toModuleMonoidAlgebra.{w} (k := k) (G := G)).IsEquivalence
  定义体: (equivalenceModuleMonoidAlgebra (k := k) (G := G)).isEquivalence_functor

Depends on / 依赖: IsEquivalence
-/
instance : (toModuleMonoidAlgebra.{w} (k := k) (G := G)).IsEquivalence :=
  (equivalenceModuleMonoidAlgebra (k := k) (G := G)).isEquivalence_functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ofModuleMonoidAlgebra (k := k) (G := G)).IsEquivalence
  body: (equivalenceModuleMonoidAlgebra (k := k) (G := G)).isEquivalence_inverse

中文:
实例 :
  签名: (ofModuleMonoidAlgebra (k := k) (G := G)).IsEquivalence
  定义体: (equivalenceModuleMonoidAlgebra (k := k) (G := G)).isEquivalence_inverse

Depends on / 依赖: IsEquivalence
-/
instance : (ofModuleMonoidAlgebra (k := k) (G := G)).IsEquivalence :=
  (equivalenceModuleMonoidAlgebra (k := k) (G := G)).isEquivalence_inverse

-- TODO Verify that the equivalence with `ModuleCat k[G]` is a monoidal functor.

variable {k G : Type u} [CommRing k] [Monoid G] in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryTheory.EnoughProjectives (Rep.{max w u} k G)
  body: equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2 ModuleCat.enoughProjectives.{max w u}

中文:
实例 :
  签名: CategoryTheory.EnoughProjectives (Rep.{max w u} k G)
  定义体: equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2 ModuleCat.enoughProjectives.{max w u}

Depends on / 依赖: ModuleCat, ModuleCat.enoughProjectives, enoughProjectives, enoughProjectives_iff, equivalenceModuleMonoidAlgebra, equivalenceModuleMonoidAlgebra.enoughProjectives_iff
-/
instance : CategoryTheory.EnoughProjectives (Rep.{max w u} k G) :=
  equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2 ModuleCat.enoughProjectives.{max w u}

/--
Instance `free_projective` / 实例 `free_projective`

English:
instance free_projective
  signature: {α : Type (max w u)}
  body: equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _
    @ModuleCat.projective_of_free _ _
      (ModuleCat.of k[G] (Representation.free k G α).asModule)
      _ (Representation.freeAsModuleBasis k G α)

中文:
实例 free_projective
  签名: {α : Type (max w u)}
  定义体: equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _
    @ModuleCat.projective_of_free _ _
      (ModuleCat.of k[G] (Representation.free k G α).asModule)
      _ (Representation.freeAsModuleBasis k G α)

Depends on / 依赖: ModuleCat, ModuleCat.of, ModuleCat.projective_of_free, Representation, Representation.free, Representation.freeAsModuleBasis, asModule, equivalenceModuleMonoidAlgebra, equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective, freeAsModuleBasis, projective_of_free, projective_of_map_projective, toAdjunction
-/
instance free_projective {α : Type (max w u)} :
    Projective (free k G α) :=
equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _
    @ModuleCat.projective_of_free _ _
      (ModuleCat.of k[G] (Representation.free k G α).asModule)
      _ (Representation.freeAsModuleBasis k G α)

section

variable {G : Type u} [Group G] {n : Nat}

/--
Instance `diagonal_succ_projective` / 实例 `diagonal_succ_projective`

English:
instance diagonal_succ_projective
  signature: :
  body: by
  exact Projective.of_iso (diagonalSuccIsoFree k G n).symm inferInstance

中文:
实例 diagonal_succ_projective
  签名: :
  定义体: by
  exact Projective.of_iso (diagonalSuccIsoFree k G n).symm inferInstance

Depends on / 依赖: Projective, Projective.of_iso, diagonalSuccIsoFree, of_iso
-/
instance diagonal_succ_projective :
    Projective (diagonal k G (n + 1)) := by
  exact Projective.of_iso (diagonalSuccIsoFree k G n).symm inferInstance

/--
Instance `leftRegular_projective` / 实例 `leftRegular_projective`

English:
instance leftRegular_projective
  signature: :
  body: Projective.of_iso (diagonalOneIsoLeftRegular k G) inferInstance

中文:
实例 leftRegular_projective
  签名: :
  定义体: Projective.of_iso (diagonalOneIsoLeftRegular k G) inferInstance

Depends on / 依赖: Projective, Projective.of_iso, diagonalOneIsoLeftRegular, of_iso
-/
instance leftRegular_projective :
    Projective (leftRegular k G) :=
  Projective.of_iso (diagonalOneIsoLeftRegular k G) inferInstance

/--
Instance `trivial_projective_of_subsingleton` / 实例 `trivial_projective_of_subsingleton`

English:
instance trivial_projective_of_subsingleton
  signature: [Subsingleton G]
  body: Projective.of_iso (ofMulActionSubsingletonIsoTrivial _ _ (Fin 1 -> G)) diagonal_succ_projective

中文:
实例 trivial_projective_of_subsingleton
  签名: [Subsingleton G]
  定义体: Projective.of_iso (ofMulActionSubsingletonIsoTrivial _ _ (Fin 1 -> G)) diagonal_succ_projective

Depends on / 依赖: Projective, Projective.of_iso, diagonal_succ_projective, ofMulActionSubsingletonIsoTrivial, of_iso
-/
instance trivial_projective_of_subsingleton [Subsingleton G] :
    Projective (trivial k G k) :=
  Projective.of_iso (ofMulActionSubsingletonIsoTrivial _ _ (Fin 1 -> G)) diagonal_succ_projective

end

end Rep
