/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel, Jujian Zhang, Weihong Xu,
  Andrew Yang, Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Data.Fintype.Order

/-!

# Construction of M^~

Given any commutative ring `R` and `R`-module `M`, we construct the sheaf `M^~` of `𝒪_SpecR`-modules
such that `M^~(U)` is the set of dependent functions that are locally fractions.

## Main definitions
* `AlgebraicGeometry.tilde` : `M^~` as a sheaf of `𝒪_{Spec R}`-modules.
* `AlgebraicGeometry.tilde.adjunction` : `~` is left adjoint to taking global sections.

-/

@[expose] public noncomputable section

universe u

open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

namespace AlgebraicGeometry

open _root_.PrimeSpectrum

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `modulesSpecToSheaf` / `modulesSpecToSheaf` 的定义

English:
definition modulesSpecToSheaf
  signature: :
  body: SheafOfModules.forgetToSheafModuleCat (Spec R).ringCatSheaf (.op ⊤)
    (Limits.initialOpOfTerminal Limits.isTerminalTop) ⋙
  sheafCompose _ (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom)

中文:
定义 modulesSpecToSheaf
  签名: :
  定义体: SheafOfModules.forgetToSheafModuleCat (Spec R).ringCatSheaf (.op ⊤)
    (Limits.initialOpOfTerminal Limits.isTerminalTop) ⋙
  sheafCompose _ (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom)

Depends on / 依赖: Limits, Limits.initialOpOfTerminal, Limits.isTerminalTop, ModuleCat, ModuleCat.restrictScalars, Scheme, SheafOfModules, SheafOfModules.forgetToSheafModuleCat, forgetToSheafModuleCat, initialOpOfTerminal, inv.hom, isTerminalTop, restrictScalars, ringCatSheaf, sheafCompose
-/
def modulesSpecToSheaf :
    (Spec R).Modules ⥤ TopCat.Sheaf (ModuleCat R) (Spec R) :=
  SheafOfModules.forgetToSheafModuleCat (Spec R).ringCatSheaf (.op ⊤)
    (Limits.initialOpOfTerminal Limits.isTerminalTop) ⋙
  sheafCompose _ (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom)

/-- The global section functor for `𝒪_{Spec R}` modules -/
noncomputable
/--
Definition of `moduleSpecΓFunctor` / `moduleSpecΓFunctor` 的定义

English:
definition moduleSpecΓFunctor
  signature: : (Spec (.of R)).Modules ⥤ ModuleCat R
  body: modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤)

中文:
定义 moduleSpecΓFunctor
  签名: : (Spec (.of R)).Modules ⥤ 模范畴 R
  定义体: modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤)

Depends on / 依赖: TopCat, TopCat.Sheaf.forget, evaluation, forget, modulesSpecToSheaf
-/
def moduleSpecΓFunctor : (Spec (.of R)).Modules ⥤ ModuleCat R :=
  modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤)

set_option backward.isDefEq.respectTransparency false in
open PrimeSpectrum in
/--
Definition of `SpecModulesToSheafFullyFaithful` / `SpecModulesToSheafFullyFaithful` 的定义

English:
definition SpecModulesToSheafFullyFaithful
  signature: : (modulesSpecToSheaf (R := R)).FullyFaithful where
  body: ⟨fun U => ModuleCat.ofHom ⟨(f.1.app U).hom.toAddHom, by
    intro t m
    apply TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj N).2
    intro x hxU
    obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : basicOpen _ <= _⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.unop.2
    refine ⟨_, hrU, hxr, ?_⟩
    refine Eq.trans ?_ (N.val.map_smul (homOfLE hrU).op t _).symm
    change N.1.map (homOfLE hrU).op (f.1.app _ _) = _ • N.1.map (homOfLE hrU).op (f.1.app _ _)
    have (x : _) :
        f.1.app _ (M.1.map (homOfLE hrU).op _) = N.1.map (homOfLE hrU).op (f.1.app _ x) :=
      congr($(f.1.naturality (homOfLE hrU).op).hom x)
    rw [← this]; rw [← this]; rw [M.val.map_smul]
    generalize (Spec R).ringCatSheaf.obj.map (homOfLE hrU).op t = t
    let := Module.compHom (R := Γ(Spec R, basicOpen r)) Γ(M, basicOpen r)
      (algebraMap R Γ(Spec R, basicOpen r))
    have : IsScalarTower R Γ(Spec R, basicOpen r) Γ(M, basicOpen r) :=
      .of_algebraMap_smul fun _ _ => rfl
    let := Module.compHom Γ(N, basicOpen r) (algebraMap R Γ(Spec R, basicOpen r))
    have : IsScalarTower R Γ(Spec R, basicOpen r) Γ(N, basicOpen r) :=
      .of_algebraMap_smul fun _ _ => rfl
    exact (IsLocalization.linearMap_compatibleSMul (.powers (M := R) r)
      Γ(Spec R, basicOpen r) Γ(M, basicOpen r) Γ(N, basicOpen r)).map_smul
      (f.hom.app _).hom _ _⟩, fun i => by ext x; exact congr($(f.1.naturality i).hom x)⟩
  map_preimage f := rfl
  preimage_map f := rfl

中文:
定义 SpecModulesToSheafFullyFaithful
  签名: : (modulesSpecToSheaf (R := R)).满忠实 where
  定义体: ⟨fun U => ModuleCat.ofHom ⟨(f.1.app U).hom.toAddHom, by
    intro t m
    apply TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj N).2
    intro x hxU
    obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : basicOpen _ <= _⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.unop.2
    refine ⟨_, hrU, hxr, ?_⟩
    refine Eq.trans ?_ (N.val.map_smul (homOfLE hrU).op t _).symm
    change N.1.map (homOfLE hrU).op (f.1.app _ _) = _ • N.1.map (homOfLE hrU).op (f.1.app _ _)
    have (x : _) :
        f.1.app _ (M.1.map (homOfLE hrU).op _) = N.1.map (homOfLE hrU).op (f.1.app _ x) :=
      congr($(f.1.naturality (homOfLE hrU).op).hom x)
    rw [← this]; rw [← this]; rw [M.val.map_smul]
    generalize (Spec R).ringCatSheaf.obj.map (homOfLE hrU).op t = t
    let := Module.compHom (R := Γ(Spec R, basicOpen r)) Γ(M, basicOpen r)
      (algebraMap R Γ(Spec R, basicOpen r))
    have : IsScalarTower R Γ(Spec R, basicOpen r) Γ(M, basicOpen r) :=
      .of_algebraMap_smul fun _ _ => rfl
    let := Module.compHom Γ(N, basicOpen r) (algebraMap R Γ(Spec R, basicOpen r))
    have : IsScalarTower R Γ(Spec R, basicOpen r) Γ(N, basicOpen r) :=
      .of_algebraMap_smul fun _ _ => rfl
    exact (IsLocalization.linearMap_compatibleSMul (.powers (M := R) r)
      Γ(Spec R, basicOpen r) Γ(M, basicOpen r) Γ(N, basicOpen r)).map_smul
      (f.hom.app _).hom _ _⟩, fun i => by ext x; exact congr($(f.1.naturality i).hom x)⟩
  map_preimage f := rfl
  preimage_map f := rfl

Depends on / 依赖: FullyFaithful
-/
def SpecModulesToSheafFullyFaithful : (modulesSpecToSheaf (R := R)).FullyFaithful where
  preimage {M N} f := ⟨fun U => ModuleCat.ofHom ⟨(f.1.app U).hom.toAddHom, by
    intro t m
    apply TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj N).2
    intro x hxU
    obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : basicOpen _ <= _⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.unop.2
    refine ⟨_, hrU, hxr, ?_⟩
    refine Eq.trans ?_ (N.val.map_smul (homOfLE hrU).op t _).symm
    change N.1.map (homOfLE hrU).op (f.1.app _ _) = _ • N.1.map (homOfLE hrU).op (f.1.app _ _)
    have (x : _) :
        f.1.app _ (M.1.map (homOfLE hrU).op _) = N.1.map (homOfLE hrU).op (f.1.app _ x) :=
      congr($(f.1.naturality (homOfLE hrU).op).hom x)
    rw [← this]; rw [← this]; rw [M.val.map_smul]
    generalize (Spec R).ringCatSheaf.obj.map (homOfLE hrU).op t = t
    let := Module.compHom (R := Γ(Spec R, basicOpen r)) Γ(M, basicOpen r)
      (algebraMap R Γ(Spec R, basicOpen r))
    have : IsScalarTower R Γ(Spec R, basicOpen r) Γ(M, basicOpen r) :=
      .of_algebraMap_smul fun _ _ => rfl
    let := Module.compHom Γ(N, basicOpen r) (algebraMap R Γ(Spec R, basicOpen r))
    have : IsScalarTower R Γ(Spec R, basicOpen r) Γ(N, basicOpen r) :=
      .of_algebraMap_smul fun _ _ => rfl
    exact (IsLocalization.linearMap_compatibleSMul (.powers (M := R) r)
      Γ(Spec R, basicOpen r) Γ(M, basicOpen r) Γ(N, basicOpen r)).map_smul
      (f.hom.app _).hom _ _⟩, fun i => by ext x; exact congr($(f.1.naturality i).hom x)⟩
  map_preimage f := rfl
  preimage_map f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (modulesSpecToSheaf (R := R)).Faithful
  body: SpecModulesToSheafFullyFaithful.faithful

中文:
实例 :
  签名: (modulesSpecToSheaf (R := R)).忠实
  定义体: SpecModulesToSheafFullyFaithful.faithful

Depends on / 依赖: Faithful, SpecModulesToSheafFullyFaithful, SpecModulesToSheafFullyFaithful.faithful, faithful
-/
instance : (modulesSpecToSheaf (R := R)).Faithful := SpecModulesToSheafFullyFaithful.faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (modulesSpecToSheaf (R := R)).Full
  body: SpecModulesToSheafFullyFaithful.full

中文:
实例 :
  签名: (modulesSpecToSheaf (R := R)).满
  定义体: SpecModulesToSheafFullyFaithful.full

Depends on / 依赖: SpecModulesToSheafFullyFaithful, SpecModulesToSheafFullyFaithful.full
-/
instance : (modulesSpecToSheaf (R := R)).Full := SpecModulesToSheafFullyFaithful.full

namespace Scheme.Modules

variable {M : (Spec R).Modules} {U V : (Spec R).Opens}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R Γ(M, U)
  body: inferInstanceAs Module R ((modulesSpecToSheaf.obj M).obj.obj (.op U))

中文:
实例 :
  签名: 模 R Γ(M, U)
  定义体: inferInstanceAs Module R ((modulesSpecToSheaf.obj M).obj.obj (.op U))

Depends on / 依赖: Module, modulesSpecToSheaf, modulesSpecToSheaf.obj, obj.obj
-/
instance : Module R Γ(M, U) :=
inferInstanceAs Module R ((modulesSpecToSheaf.obj M).obj.obj (.op U))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R Γ(Spec R, U) Γ(M, U)
  body: IsScalarTower.of_compHom R Γ(Spec R, U) Γ(M, U)

中文:
实例 :
  签名: 标量塔 R Γ(Spec R, U) Γ(M, U)
  定义体: IsScalarTower.of_compHom R Γ(Spec R, U) Γ(M, U)

Depends on / 依赖: IsScalarTower, IsScalarTower.of_compHom, of_compHom
-/
instance : IsScalarTower R Γ(Spec R, U) Γ(M, U) :=
  IsScalarTower.of_compHom R Γ(Spec R, U) Γ(M, U)

/--
lemma `smul_Spec_def` / 引理 `smul_Spec_def`

English:
lemma smul_Spec_def
  given: (r : R) (x : Γ(M, U))
  proof: rfl

@[simp]

中文:
引理 smul_Spec_def
  条件: (r : R) (x : Γ(M, U))
  证明: rfl

@[simp]
-/
lemma smul_Spec_def (r : R) (x : Γ(M, U)) :
    r • x = ((Spec R).presheaf.map U.leTop.op) ((Scheme.ΓSpecIso R).inv r) • x :=
  rfl

@[simp]
/--
lemma `map_smul_Spec` / 引理 `map_smul_Spec`

English:
lemma map_smul_Spec
  given: (hUV : .op V ⟶ .op U) (f : R) (x : Γ(M, V))
  proof: ((modulesSpecToSheaf.obj M).obj.map hUV).hom.map_smul f x

中文:
引理 map_smul_Spec
  条件: (hUV : .op V ⟶ .op U) (f : R) (x : Γ(M, V))
  证明: ((modulesSpecToSheaf.obj M).obj.map hUV).hom.map_smul f x

Depends on / 依赖: hom.map_smul, map_smul, modulesSpecToSheaf, modulesSpecToSheaf.obj, obj.map
-/
lemma map_smul_Spec (hUV : .op V ⟶ .op U) (f : R) (x : Γ(M, V)) :
    dsimp% M.presheaf.map hUV (f • x) = f • M.presheaf.map hUV x :=
  ((modulesSpecToSheaf.obj M).obj.map hUV).hom.map_smul f x

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isUnit_algebraMap_end_of_le_basicOpen` / 引理 `isUnit_algebraMap_end_of_le_basicOpen`

English:
lemma isUnit_algebraMap_end_of_le_basicOpen
  given: (f : R) (hf : U <= PrimeSpectrum.basicOpen f)
  proof: by
  rw [Module.End.isUnit_iff]
  have : ⇑((algebraMap R (Module.End ↑R ↑Γ(M, U))) f) =
      algebraMap (Γ(Spec R, U)) (Module.End Γ(Spec R, U) Γ(M, U))
        (((Spec R).presheaf.map (homOfLE hf).op) <| algebraMap R _ f) :=
    rfl
  rw [this]; rw [← Module.End.isUnit_iff]
  exact ((IsLocalization.Away.algebraMap_isUnit _).map _).map _

中文:
引理 isUnit_algebraMap_end_of_le_basicOpen
  条件: (f : R) (hf : U <= 素谱.basicOpen f)
  证明: by
  rw [Module.End.isUnit_iff]
  have : ⇑((algebraMap R (Module.End ↑R ↑Γ(M, U))) f) =
      algebraMap (Γ(Spec R, U)) (Module.End Γ(Spec R, U) Γ(M, U))
        (((Spec R).presheaf.map (homOfLE hf).op) <| algebraMap R _ f) :=
    rfl
  rw [this]; rw [← Module.End.isUnit_iff]
  exact ((IsLocalization.Away.algebraMap_isUnit _).map _).map _

Depends on / 依赖: IsLocalization, IsLocalization.Away.algebraMap_isUnit, Module, Module.End, Module.End.isUnit_iff, algebraMap, algebraMap_isUnit, homOfLE, isUnit_iff, presheaf, presheaf.map
-/
lemma isUnit_algebraMap_end_of_le_basicOpen (f : R) (hf : U <= PrimeSpectrum.basicOpen f) :
    IsUnit (algebraMap R (Module.End R Γ(M, U)) f) := by
  rw [Module.End.isUnit_iff]
  have : ⇑((algebraMap R (Module.End ↑R ↑Γ(M, U))) f) =
      algebraMap (Γ(Spec R, U)) (Module.End Γ(Spec R, U) Γ(M, U))
        (((Spec R).presheaf.map (homOfLE hf).op) <| algebraMap R _ f) :=
    rfl
  rw [this]; rw [← Module.End.isUnit_iff]
  exact ((IsLocalization.Away.algebraMap_isUnit _).map _).map _

/--
lemma `isSMulRegular_of_le_basicOpen` / 引理 `isSMulRegular_of_le_basicOpen`

English:
lemma isSMulRegular_of_le_basicOpen
  given: {f : R} (hle : U <= PrimeSpectrum.basicOpen f)
  proof: by
  intro x y hxy
  have := M.isUnit_algebraMap_end_of_le_basicOpen _ hle
  rw [Module.End.isUnit_iff] at this
  exact this.injective hxy

中文:
引理 isSMulRegular_of_le_basicOpen
  条件: {f : R} (hle : U <= 素谱.basicOpen f)
  证明: by
  intro x y hxy
  have := M.isUnit_algebraMap_end_of_le_basicOpen _ hle
  rw [Module.End.isUnit_iff] at this
  exact this.injective hxy

Depends on / 依赖: M.isUnit_algebraMap_end_of_le_basicOpen, Module, Module.End.isUnit_iff, injective, isUnit_algebraMap_end_of_le_basicOpen, isUnit_iff, this.injective
-/
lemma isSMulRegular_of_le_basicOpen {f : R} (hle : U <= PrimeSpectrum.basicOpen f) :
    IsSMulRegular Γ(M, U) f := by
  intro x y hxy
  have := M.isUnit_algebraMap_end_of_le_basicOpen _ hle
  rw [Module.End.isUnit_iff] at this
  exact this.injective hxy

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `restrictAppIso_smul_Spec` / 引理 `restrictAppIso_smul_Spec`

English:
lemma restrictAppIso_smul_Spec
  statement: {S : CommRingCat.{u}} (f : R ⟶ S)
  proof: by
  rw [smul_Spec_def]; rw [smul_Spec_def]
  simp_rw [smul_restrictAppIso_hom_apply, ← ConcreteCategory.comp_apply, Category.assoc]
  have :
      f ≫ (ΓSpecIso S).inv ≫ (Spec S).presheaf.map U.leTop.op ≫ (Hom.appIso (Spec.map f) U).inv =
        (ΓSpecIso R).inv ≫ (Spec R).presheaf.map (Spec.map f ''ᵁ U).leTop.op := by
    simp [Iso.cancel_iso_inv_left, Hom.app_eq_appLE]
    rfl
  rw [this]

中文:
引理 restrictAppIso_smul_Spec
  结论: {S : 交换环范畴.{u}} (f : R ⟶ S)
  证明: by
  rw [smul_Spec_def]; rw [smul_Spec_def]
  simp_rw [smul_restrictAppIso_hom_apply, ← ConcreteCategory.comp_apply, Category.assoc]
  have :
      f ≫ (ΓSpecIso S).inv ≫ (Spec S).presheaf.map U.leTop.op ≫ (Hom.appIso (Spec.map f) U).inv =
        (ΓSpecIso R).inv ≫ (Spec R).presheaf.map (Spec.map f ''ᵁ U).leTop.op := by
    simp [Iso.cancel_iso_inv_left, Hom.app_eq_appLE]
    rfl
  rw [this]

Depends on / 依赖: Category, Category.assoc, ConcreteCategory, ConcreteCategory.comp_apply, Hom.appIso, Hom.app_eq_appLE, Iso.cancel_iso_inv_left, Spec.map, U.leTop.op, appIso, app_eq_appLE, cancel_iso_inv_left, comp_apply, leTop.op, presheaf, presheaf.map, simp_rw, smul_Spec_def, smul_restrictAppIso_hom_apply
-/
lemma restrictAppIso_smul_Spec {S : CommRingCat.{u}} (f : R ⟶ S)
    [IsOpenImmersion (Spec.map f)] {U : (Spec S).Opens} (r : R)
    (x : Γ(M.restrict (Spec.map f), U)) :
    dsimp% (M.restrictAppIso (Spec.map f) U).hom (f r • x) =
      r • (M.restrictAppIso (Spec.map f) U).hom x := by
  rw [smul_Spec_def]; rw [smul_Spec_def]
  simp_rw [smul_restrictAppIso_hom_apply, ← ConcreteCategory.comp_apply, Category.assoc]
  have :
      f ≫ (ΓSpecIso S).inv ≫ (Spec S).presheaf.map U.leTop.op ≫ (Hom.appIso (Spec.map f) U).inv =
        (ΓSpecIso R).inv ≫ (Spec R).presheaf.map (Spec.map f ''ᵁ U).leTop.op := by
    simp [Iso.cancel_iso_inv_left, Hom.app_eq_appLE]
    rfl
  rw [this]

set_option linter.dupNamespace false in
@[deprecated (since := "2026-06-04")]
alias Scheme.Modules.restrictAppIso_smul_Spec := restrictAppIso_smul_Spec

end Scheme.Modules

/--
Definition of `tilde` / `tilde` 的定义

English:
definition tilde
  signature: : (Spec R).Modules where
  body: moduleStructurePresheaf R M
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (structureSheafInType R M).2

中文:
定义 tilde
  签名: : (Spec R).Modules where
  定义体: moduleStructurePresheaf R M
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (structureSheafInType R M).2

Depends on / 依赖: moduleStructurePresheaf
-/
def tilde : (Spec R).Modules where
  val := moduleStructurePresheaf R M
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (structureSheafInType R M).2

namespace tilde

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation). The image of `tilde` under `modulesSpecToSheaf` is isomorphic to
`structurePresheafInModuleCat`. They are defeq as types but the `Smul` instance are not defeq. -/
noncomputable
/--
Definition of `modulesSpecToSheafIso` / `modulesSpecToSheafIso` 的定义

English:
definition modulesSpecToSheafIso
  signature: :
  body: NatIso.ofComponents (fun U => LinearEquiv.toModuleIso
    (X₁ := (modulesSpecToSheaf.obj (tilde M)).presheaf.obj _)
    { __ := AddEquiv.refl _,
      map_smul' r m := IsScalarTower.algebraMap_smul (M := ((structureSheafInType R M).obj.obj U))
        ((structureSheafInType R R).obj.obj U) r m }) fun _ => rfl

中文:
定义 modulesSpecToSheafIso
  签名: :
  定义体: NatIso.ofComponents (fun U => LinearEquiv.toModuleIso
    (X₁ := (modulesSpecToSheaf.obj (tilde M)).presheaf.obj _)
    { __ := AddEquiv.refl _,
      map_smul' r m := IsScalarTower.algebraMap_smul (M := ((structureSheafInType R M).obj.obj U))
        ((structureSheafInType R R).obj.obj U) r m }) fun _ => rfl

Depends on / 依赖: AddEquiv, AddEquiv.refl, IsScalarTower, IsScalarTower.algebraMap_smul, LinearEquiv, LinearEquiv.toModuleIso, NatIso, NatIso.ofComponents, algebraMap_smul, map_smul, modulesSpecToSheaf, modulesSpecToSheaf.obj, obj.obj, ofComponents, presheaf, presheaf.obj, structureSheafInType, toModuleIso
-/
def modulesSpecToSheafIso :
    (modulesSpecToSheaf.obj (tilde M)).1 ≅ structurePresheafInModuleCat R M :=
  NatIso.ofComponents (fun U => LinearEquiv.toModuleIso
    (X₁ := (modulesSpecToSheaf.obj (tilde M)).presheaf.obj _)
    { __ := AddEquiv.refl _,
      map_smul' r m := IsScalarTower.algebraMap_smul (M := ((structureSheafInType R M).obj.obj U))
        ((structureSheafInType R R).obj.obj U) r m }) fun _ => rfl

/--
Definition of `toOpen` / `toOpen` 的定义

English:
definition toOpen
  signature: (U : (Spec R).Opens)
  body: ModuleCat.ofHom (StructureSheaf.toOpenₗ R M U) ≫ ((modulesSpecToSheafIso M).app _).inv

中文:
定义 toOpen
  签名: (U : (Spec R).Opens)
  定义体: ModuleCat.ofHom (StructureSheaf.toOpenₗ R M U) ≫ ((modulesSpecToSheafIso M).app _).inv

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, StructureSheaf, StructureSheaf.toOpen, modulesSpecToSheafIso
-/
def toOpen (U : (Spec R).Opens) : M ⟶ (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op U) :=
  ModuleCat.ofHom (StructureSheaf.toOpenₗ R M U) ≫ ((modulesSpecToSheafIso M).app _).inv

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `toOpen_res` / 定理 `toOpen_res`

English:
theorem toOpen_res
  given: (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U)
  proof: rfl

中文:
定理 toOpen_res
  条件: (U V : Opens (素谱.顶元素 R)) (i : V ⟶ U)
  证明: rfl
-/
theorem toOpen_res (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U) :
    toOpen M U ≫ (modulesSpecToSheaf.obj (tilde M)).presheaf.map i.op = toOpen M V :=
  rfl

instance (f : R) : IsLocalizedModule.Away f (toOpen M (basicOpen f)).hom :=
  .of_linearEquiv (.powers f) (StructureSheaf.toOpenₗ R M (basicOpen f))
    ((modulesSpecToSheafIso M).app _).toLinearEquiv.symm

noncomputable
instance (x : PrimeSpectrum.Top R) : Module R ((tilde M).presheaf.stalk x) :=
  inferInstanceAs (Module R ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x))

/--
Definition of `toStalk` / `toStalk` 的定义

English:
definition toStalk
  signature: (x : PrimeSpectrum.Top R)
  body: ModuleCat.ofHom (StructureSheaf.toStalkₗ ..)

中文:
定义 toStalk
  签名: (x : 素谱.顶元素 R)
  定义体: ModuleCat.ofHom (StructureSheaf.toStalkₗ ..)

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, StructureSheaf, StructureSheaf.toStalk
-/
noncomputable def toStalk (x : PrimeSpectrum.Top R) :
    ModuleCat.of R M ⟶ ModuleCat.of R ((tilde M).presheaf.stalk x) :=
  ModuleCat.ofHom (StructureSheaf.toStalkₗ ..)

set_option backward.isDefEq.respectTransparency.types false in
instance (x : PrimeSpectrum.Top R) :
    IsLocalizedModule x.asIdeal.primeCompl (toStalk M x).hom :=
  inferInstanceAs (IsLocalizedModule x.asIdeal.primeCompl (StructureSheaf.toStalkₗ ..))

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def map {M N : ModuleCat R} (f : M ⟶ N)
  body: SpecModulesToSheafFullyFaithful.preimage ⟨(modulesSpecToSheafIso M).hom ≫
    { app U := ModuleCat.ofHom (StructureSheaf.comapₗ f.hom _ _ .rfl) } ≫
    (modulesSpecToSheafIso N).inv⟩

中文:
定义 noncomputable
  签名: def map {M N : 模范畴 R} (f : M ⟶ N)
  定义体: SpecModulesToSheafFullyFaithful.preimage ⟨(modulesSpecToSheafIso M).hom ≫
    { app U := ModuleCat.ofHom (StructureSheaf.comapₗ f.hom _ _ .rfl) } ≫
    (modulesSpecToSheafIso N).inv⟩
-/
protected noncomputable def map {M N : ModuleCat R} (f : M ⟶ N) : tilde M ⟶ tilde N :=
  SpecModulesToSheafFullyFaithful.preimage ⟨(modulesSpecToSheafIso M).hom ≫
    { app U := ModuleCat.ofHom (StructureSheaf.comapₗ f.hom _ _ .rfl) } ≫
    (modulesSpecToSheafIso N).inv⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp, reassoc]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: {M : ModuleCat R}
  statement: tilde.map (𝟙 M) = 𝟙 _
  proof: by
  ext p x
  exact Subtype.ext (funext fun y => DFunLike.congr_fun (LocalizedModule.map_id _) _)

中文:
引理 map_id
  条件: {M : 模范畴 R}
  结论: tilde.map (𝟙 M) = 𝟙 _
  证明: by
  ext p x
  exact Subtype.ext (funext fun y => DFunLike.congr_fun (LocalizedModule.map_id _) _)
-/
protected lemma map_id {M : ModuleCat R} : tilde.map (𝟙 M) = 𝟙 _ := by
  ext p x
  exact Subtype.ext (funext fun y => DFunLike.congr_fun (LocalizedModule.map_id _) _)

set_option backward.isDefEq.respectTransparency.types false in
@[simp, reassoc]
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: {M N P : ModuleCat R} (f : M ⟶ N) (g : N ⟶ P)
  proof: by
  ext p x
  exact Subtype.ext (funext
    fun y => DFunLike.congr_fun (IsLocalizedModule.map_comp' y.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl N)
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl P) _ _) _)

中文:
引理 map_comp
  条件: {M N P : 模范畴 R} (f : M ⟶ N) (g : N ⟶ P)
  证明: by
  ext p x
  exact Subtype.ext (funext
    fun y => DFunLike.congr_fun (IsLocalizedModule.map_comp' y.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl N)
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl P) _ _) _)
-/
protected lemma map_comp {M N P : ModuleCat R} (f : M ⟶ N) (g : N ⟶ P) :
    tilde.map (f ≫ g) = tilde.map f ≫ tilde.map g := by
  ext p x
  exact Subtype.ext (funext
    fun y => DFunLike.congr_fun (IsLocalizedModule.map_comp' y.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl N)
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl P) _ _) _)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `toOpen_map_app` / 引理 `toOpen_map_app`

English:
lemma toOpen_map_app
  statement: {M N : ModuleCat R} (f : M ⟶ N)
  proof: by
  ext x; exact Subtype.ext (funext fun y => IsLocalizedModule.map_apply y.1.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
     (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl N) _ x)

中文:
引理 toOpen_map_app
  结论: {M N : 模范畴 R} (f : M ⟶ N)
  证明: by
  ext x; exact Subtype.ext (funext fun y => IsLocalizedModule.map_apply y.1.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
     (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl N) _ x)

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.map_apply, LocalizedModule, LocalizedModule.mkLinearMap, Subtype, Subtype.ext, asIdeal, asIdeal.primeCompl, map_apply, mkLinearMap, primeCompl
-/
lemma toOpen_map_app {M N : ModuleCat R} (f : M ⟶ N)
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    toOpen M U ≫ (modulesSpecToSheaf.map (tilde.map f)).1.app _ =
    f ≫ toOpen N U := by
  ext x; exact Subtype.ext (funext fun y => IsLocalizedModule.map_apply y.1.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
     (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl N) _ x)

variable (R) in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def functor
  body: tilde
  map := tilde.map

中文:
定义 noncomputable
  签名: def functor
  定义体: tilde
  map := tilde.map
-/
@[simps] protected noncomputable def functor : ModuleCat R ⥤ (Spec (.of R)).Modules where
  obj := tilde
  map := tilde.map

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isIso_toOpen_top` / 实例 `isIso_toOpen_top`

English:
instance isIso_toOpen_top
  signature: {M : ModuleCat R}
  body: by
  rw [toOpen]; rw [isIso_comp_right_iff]; rw [ConcreteCategory.isIso_iff_bijective]
  exact StructureSheaf.toOpenₗ_top_bijective

中文:
实例 isIso_toOpen_top
  签名: {M : 模范畴 R}
  定义体: by
  rw [toOpen]; rw [isIso_comp_right_iff]; rw [ConcreteCategory.isIso_iff_bijective]
  exact StructureSheaf.toOpenₗ_top_bijective

Depends on / 依赖: ConcreteCategory, ConcreteCategory.isIso_iff_bijective, StructureSheaf, StructureSheaf.toOpen, isIso_comp_right_iff, isIso_iff_bijective, toOpen
-/
instance isIso_toOpen_top {M : ModuleCat R} : IsIso (toOpen M ⊤) := by
  rw [toOpen]; rw [isIso_comp_right_iff]; rw [ConcreteCategory.isIso_iff_bijective]
  exact StructureSheaf.toOpenₗ_top_bijective

/-- The isomorphism between the global sections of `M^~` and `M`. -/
@[simps! hom]
/--
Definition of `isoTop` / `isoTop` 的定义

English:
definition isoTop
  signature: (M : ModuleCat R)
  body: asIso (toOpen M ⊤)

@[deprecated (since := "2026-05-30")]
alias isUnit_algebraMap_end_basicOpen := Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen

中文:
定义 isoTop
  签名: (M : 模范畴 R)
  定义体: asIso (toOpen M ⊤)

@[deprecated (since := "2026-05-30")]
alias isUnit_algebraMap_end_basicOpen := Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen

Depends on / 依赖: toOpen
-/
noncomputable def isoTop (M : ModuleCat R) :
    M ≅ (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op ⊤) :=
  asIso (toOpen M ⊤)

@[deprecated (since := "2026-05-30")]
alias isUnit_algebraMap_end_basicOpen := Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen

end tilde

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Scheme.Modules.fromTildeΓ` / `Scheme.Modules.fromTildeΓ` 的定义

English:
definition Scheme.Modules.fromTildeΓ
  signature: (M : (Spec (.of R)).Modules)
  body: SpecModulesToSheafFullyFaithful.preimage
    ⟨TopCat.Sheaf.restrictHomEquivHom _ _ isBasis_basic_opens
    { app (f : Rᵒᵖ) := by
        refine (ModuleCat.ofHom (IsLocalizedModule.lift (.powers (M := R) f.unop)
          (tilde.toOpen _ (PrimeSpectrum.basicOpen f.unop)).hom
          ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom ?_):)
        rw [Subtype.forall]
        change Submonoid.powers _ <= (IsUnit.submonoid _).comap _
        simp only [inducedFunctor_obj, Submonoid.powers_le, Submonoid.mem_comap]
        exact M.isUnit_algebraMap_end_of_le_basicOpen f.unop le_rfl
      naturality {f g : Rᵒᵖ} i := by
        let N := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)
        ext1
        apply IsLocalizedModule.ext (.powers (M := R) f.unop)
          (tilde.toOpen _ (PrimeSpectrum.basicOpen (R := R) f.unop)).hom
        · rw [Subtype.forall]
          change Submonoid.powers _ <= (IsUnit.submonoid _).comap _
          simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
          obtain ⟨n, a, e⟩ : exists n, f.unop ∣ g.unop ^ n := by
            simpa only [Ideal.mem_radical_iff, Ideal.mem_span_singleton] using
              (basicOpen_le_basicOpen_iff _ _).mp (i.1.hom.le)
          refine ((Commute.isUnit_mul_iff (b := algebraMap R _ a) (.map (.all _ _) _)).mp ?_).1
          rw [← map_mul]; rw [← e]; rw [map_pow]
          exact (M.isUnit_algebraMap_end_of_le_basicOpen g.unop le_rfl).pow n
        · dsimp [← ModuleCat.hom_comp]
          rw [tilde.toOpen_res_assoc]
          ext x
          dsimp
          simp only [IsLocalizedModule.lift_apply, ← ModuleCat.comp_apply, ← Functor.map_comp]
          rfl }⟩

中文:
定义 概形.Modules.fromTildeΓ
  签名: (M : (Spec (.of R)).Modules)
  定义体: SpecModulesToSheafFullyFaithful.preimage
    ⟨TopCat.Sheaf.restrictHomEquivHom _ _ isBasis_basic_opens
    { app (f : Rᵒᵖ) := by
        refine (ModuleCat.ofHom (IsLocalizedModule.lift (.powers (M := R) f.unop)
          (tilde.toOpen _ (PrimeSpectrum.basicOpen f.unop)).hom
          ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom ?_):)
        rw [Subtype.forall]
        change Submonoid.powers _ <= (IsUnit.submonoid _).comap _
        simp only [inducedFunctor_obj, Submonoid.powers_le, Submonoid.mem_comap]
        exact M.isUnit_algebraMap_end_of_le_basicOpen f.unop le_rfl
      naturality {f g : Rᵒᵖ} i := by
        let N := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)
        ext1
        apply IsLocalizedModule.ext (.powers (M := R) f.unop)
          (tilde.toOpen _ (PrimeSpectrum.basicOpen (R := R) f.unop)).hom
        · rw [Subtype.forall]
          change Submonoid.powers _ <= (IsUnit.submonoid _).comap _
          simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
          obtain ⟨n, a, e⟩ : exists n, f.unop ∣ g.unop ^ n := by
            simpa only [Ideal.mem_radical_iff, Ideal.mem_span_singleton] using
              (basicOpen_le_basicOpen_iff _ _).mp (i.1.hom.le)
          refine ((Commute.isUnit_mul_iff (b := algebraMap R _ a) (.map (.all _ _) _)).mp ?_).1
          rw [← map_mul]; rw [← e]; rw [map_pow]
          exact (M.isUnit_algebraMap_end_of_le_basicOpen g.unop le_rfl).pow n
        · dsimp [← ModuleCat.hom_comp]
          rw [tilde.toOpen_res_assoc]
          ext x
          dsimp
          simp only [IsLocalizedModule.lift_apply, ← ModuleCat.comp_apply, ← Functor.map_comp]
          rfl }⟩

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.lift, IsUnit, IsUnit.submonoid, M.isUnit_algebraMap_end_of_, ModuleCat, ModuleCat.ofHom, PrimeSpectrum, PrimeSpectrum.basicOpen, SpecModulesToSheafFullyFaithful, SpecModulesToSheafFullyFaithful.preimage, Submonoid, Submonoid.mem_comap, Submonoid.powers, Submonoid.powers_le, Subtype, Subtype.forall, TopCat, TopCat.Sheaf.restrictHomEquivHom, basicOpen
-/
noncomputable def Scheme.Modules.fromTildeΓ (M : (Spec (.of R)).Modules) :
    tilde ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) ⟶ M :=
  SpecModulesToSheafFullyFaithful.preimage
    ⟨TopCat.Sheaf.restrictHomEquivHom _ _ isBasis_basic_opens
    { app (f : Rᵒᵖ) := by
        refine (ModuleCat.ofHom (IsLocalizedModule.lift (.powers (M := R) f.unop)
          (tilde.toOpen _ (PrimeSpectrum.basicOpen f.unop)).hom
          ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom ?_):)
        rw [Subtype.forall]
        change Submonoid.powers _ <= (IsUnit.submonoid _).comap _
        simp only [inducedFunctor_obj, Submonoid.powers_le, Submonoid.mem_comap]
        exact M.isUnit_algebraMap_end_of_le_basicOpen f.unop le_rfl
      naturality {f g : Rᵒᵖ} i := by
        let N := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)
        ext1
        apply IsLocalizedModule.ext (.powers (M := R) f.unop)
          (tilde.toOpen _ (PrimeSpectrum.basicOpen (R := R) f.unop)).hom
        · rw [Subtype.forall]
          change Submonoid.powers _ <= (IsUnit.submonoid _).comap _
          simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
          obtain ⟨n, a, e⟩ : exists n, f.unop ∣ g.unop ^ n := by
            simpa only [Ideal.mem_radical_iff, Ideal.mem_span_singleton] using
              (basicOpen_le_basicOpen_iff _ _).mp (i.1.hom.le)
          refine ((Commute.isUnit_mul_iff (b := algebraMap R _ a) (.map (.all _ _) _)).mp ?_).1
          rw [← map_mul]; rw [← e]; rw [map_pow]
          exact (M.isUnit_algebraMap_end_of_le_basicOpen g.unop le_rfl).pow n
        · dsimp [← ModuleCat.hom_comp]
          rw [tilde.toOpen_res_assoc]
          ext x
          dsimp
          simp only [IsLocalizedModule.lift_apply, ← ModuleCat.comp_apply, ← Functor.map_comp]
          rfl }⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `Scheme.Modules.toOpen_fromTildeΓ_app` / 引理 `Scheme.Modules.toOpen_fromTildeΓ_app`

English:
lemma Scheme.Modules.toOpen_fromTildeΓ_app
  given: (M : (Spec (.of R)).Modules) (U)
  proof: by
  wlog hU : U = PrimeSpectrum.basicOpen 1 generalizing U
  · rw [← tilde.toOpen_res _ (PrimeSpectrum.basicOpen 1) _ (homOfLE (by simp)), Category.assoc,
      NatTrans.naturality, ← Category.assoc, this, ← Functor.map_comp, ← op_comp, homOfLE_comp]
    simp
  subst hU
  simp only [fromTildeΓ, inducedFunctor_obj, homOfLE_leOfHom, Functor.FullyFaithful.map_preimage,
    TopCat.Sheaf.extend_hom_app]
  ext x
  refine (IsLocalizedModule.lift_apply (.powers (M := R) 1)
    (tilde.toOpen _ (PrimeSpectrum.basicOpen (R := R) 1)).hom
    ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom (by simp) x)

中文:
引理 概形.Modules.toOpen_fromTildeΓ_app
  条件: (M : (Spec (.of R)).Modules) (U)
  证明: by
  wlog hU : U = PrimeSpectrum.basicOpen 1 generalizing U
  · rw [← tilde.toOpen_res _ (PrimeSpectrum.basicOpen 1) _ (homOfLE (by simp)), Category.assoc,
      NatTrans.naturality, ← Category.assoc, this, ← Functor.map_comp, ← op_comp, homOfLE_comp]
    simp
  subst hU
  simp only [fromTildeΓ, inducedFunctor_obj, homOfLE_leOfHom, Functor.FullyFaithful.map_preimage,
    TopCat.Sheaf.extend_hom_app]
  ext x
  refine (IsLocalizedModule.lift_apply (.powers (M := R) 1)
    (tilde.toOpen _ (PrimeSpectrum.basicOpen (R := R) 1)).hom
    ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom (by simp) x)

Depends on / 依赖: Category, Category.assoc, FullyFaithful, Functor, Functor.FullyFaithful.map_preimage, Functor.map_comp, IsLocalizedModule, IsLocalizedModule.lift_apply, NatTrans, NatTrans.naturality, PrimeSpectrum, PrimeSpectrum.basicOpen, TopCat, TopCat.Sheaf.extend_hom_app, basicOpen, extend_hom_app, generalizing, homOfLE, homOfLE_comp, homOfLE_leOfHom
-/
lemma Scheme.Modules.toOpen_fromTildeΓ_app (M : (Spec (.of R)).Modules) (U) :
    tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) U ≫
      (modulesSpecToSheaf.map M.fromTildeΓ).1.app (.op U) =
    (modulesSpecToSheaf.obj M).1.map (homOfLE le_top).op := by
  wlog hU : U = PrimeSpectrum.basicOpen 1 generalizing U
  · rw [← tilde.toOpen_res _ (PrimeSpectrum.basicOpen 1) _ (homOfLE (by simp)), Category.assoc,
      NatTrans.naturality, ← Category.assoc, this, ← Functor.map_comp, ← op_comp, homOfLE_comp]
    simp
  subst hU
  simp only [fromTildeΓ, inducedFunctor_obj, homOfLE_leOfHom, Functor.FullyFaithful.map_preimage,
    TopCat.Sheaf.extend_hom_app]
  ext x
  refine (IsLocalizedModule.lift_apply (.powers (M := R) 1)
    (tilde.toOpen _ (PrimeSpectrum.basicOpen (R := R) 1)).hom
    ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom (by simp) x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Scheme.Modules.fromTildeΓNatTrans` / `Scheme.Modules.fromTildeΓNatTrans` 的定义

English:
definition Scheme.Modules.fromTildeΓNatTrans
  signature: :
  body: fromTildeΓ
  naturality {M N} f := by
    apply SpecModulesToSheafFullyFaithful.map_injective
    apply CategoryTheory.Sheaf.hom_ext
    apply (TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens).symm.injective
    ext r : 3
    apply IsLocalizedModule.ext (.powers (M := R) r.unop)
      (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤))
        (PrimeSpectrum.basicOpen (R := R) r.unop)).hom
    · rw [Subtype.forall]
      change Submonoid.powers _ <= (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact N.isUnit_algebraMap_end_of_le_basicOpen r.unop le_rfl
    dsimp [TopCat.Sheaf.restrictHomEquivHom, Functor.IsCoverDense.restrictHomEquivHom,
      moduleSpecΓFunctor, Sheaf.forget]
    simp only [← ModuleCat.hom_comp, Functor.map_comp]
    congr 1
    erw [tilde.toOpen_map_app_assoc, toOpen_fromTildeΓ_app N (PrimeSpectrum.basicOpen r.unop),
      toOpen_fromTildeΓ_app_assoc M (PrimeSpectrum.basicOpen r.unop),
      ← (modulesSpecToSheaf.map f).hom.naturality]

中文:
定义 概形.Modules.fromTildeΓ自然数Trans
  签名: :
  定义体: fromTildeΓ
  naturality {M N} f := by
    apply SpecModulesToSheafFullyFaithful.map_injective
    apply CategoryTheory.Sheaf.hom_ext
    apply (TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens).symm.injective
    ext r : 3
    apply IsLocalizedModule.ext (.powers (M := R) r.unop)
      (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤))
        (PrimeSpectrum.basicOpen (R := R) r.unop)).hom
    · rw [Subtype.forall]
      change Submonoid.powers _ <= (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact N.isUnit_algebraMap_end_of_le_basicOpen r.unop le_rfl
    dsimp [TopCat.Sheaf.restrictHomEquivHom, Functor.IsCoverDense.restrictHomEquivHom,
      moduleSpecΓFunctor, Sheaf.forget]
    simp only [← ModuleCat.hom_comp, Functor.map_comp]
    congr 1
    erw [tilde.toOpen_map_app_assoc, toOpen_fromTildeΓ_app N (PrimeSpectrum.basicOpen r.unop),
      toOpen_fromTildeΓ_app_assoc M (PrimeSpectrum.basicOpen r.unop),
      ← (modulesSpecToSheaf.map f).hom.naturality]

Depends on / 依赖: functor, tilde.functor
-/
noncomputable def Scheme.Modules.fromTildeΓNatTrans :
    moduleSpecΓFunctor (R := R) ⋙ tilde.functor (R := R) ⟶ 𝟭 _ where
  app := fromTildeΓ
  naturality {M N} f := by
    apply SpecModulesToSheafFullyFaithful.map_injective
    apply CategoryTheory.Sheaf.hom_ext
    apply (TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens).symm.injective
    ext r : 3
    apply IsLocalizedModule.ext (.powers (M := R) r.unop)
      (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤))
        (PrimeSpectrum.basicOpen (R := R) r.unop)).hom
    · rw [Subtype.forall]
      change Submonoid.powers _ <= (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact N.isUnit_algebraMap_end_of_le_basicOpen r.unop le_rfl
    dsimp [TopCat.Sheaf.restrictHomEquivHom, Functor.IsCoverDense.restrictHomEquivHom,
      moduleSpecΓFunctor, Sheaf.forget]
    simp only [← ModuleCat.hom_comp, Functor.map_comp]
    congr 1
    erw [tilde.toOpen_map_app_assoc, toOpen_fromTildeΓ_app N (PrimeSpectrum.basicOpen r.unop),
      toOpen_fromTildeΓ_app_assoc M (PrimeSpectrum.basicOpen r.unop),
      ← (modulesSpecToSheaf.map f).hom.naturality]

/--
Definition of `tilde.toTildeΓNatIso` / `tilde.toTildeΓNatIso` 的定义

English:
definition tilde.toTildeΓNatIso
  signature: : 𝟭 _ ≅ tilde.functor R ⋙ moduleSpecΓFunctor
  body: NatIso.ofComponents tilde.isoTop fun f => (tilde.toOpen_map_app f _).symm

中文:
定义 tilde.toTildeΓ自然数Iso
  签名: : 𝟭 _ ≅ tilde.functor R ⋙ moduleSpecΓFunctor
  定义体: NatIso.ofComponents tilde.isoTop fun f => (tilde.toOpen_map_app f _).symm

Depends on / 依赖: NatIso, NatIso.ofComponents, isoTop, ofComponents, tilde.isoTop, tilde.toOpen_map_app, toOpen_map_app
-/
def tilde.toTildeΓNatIso : 𝟭 _ ≅ tilde.functor R ⋙ moduleSpecΓFunctor :=
  NatIso.ofComponents tilde.isoTop fun f => (tilde.toOpen_map_app f _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open Scheme.Modules in
/--
Definition of `tilde.adjunction` / `tilde.adjunction` 的定义

English:
definition tilde.adjunction
  signature: : tilde.functor R ⊣ moduleSpecΓFunctor where
  body: toTildeΓNatIso.hom
  counit := fromTildeΓNatTrans
  left_triangle_components M := by
    apply SpecModulesToSheafFullyFaithful.map_injective
    apply CategoryTheory.Sheaf.hom_ext
    apply (TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens).symm.injective
    ext r : 3
    apply IsLocalizedModule.ext (.powers (M := R) r.unop)
      (toOpen _ (PrimeSpectrum.basicOpen (R := R) r.unop)).hom
    · rw [Subtype.forall]
      change Submonoid.powers _ <= (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen r.unop le_rfl
    dsimp [toTildeΓNatIso, isoTop,
      TopCat.Sheaf.restrictHomEquivHom, Functor.IsCoverDense.restrictHomEquivHom,
      fromTildeΓNatTrans, moduleSpecΓFunctor, Sheaf.forget, sheafToPresheaf]
    simp only [← ModuleCat.hom_comp, Functor.map_comp]
    congr 1
    rw [ObjectProperty.FullSubcategory.comp_hom]
    dsimp
    rw [toOpen_map_app_assoc]; rw [toOpen_fromTildeΓ_app]
    rfl
  right_triangle_components M := by
    dsimp [toTildeΓNatIso, fromTildeΓNatTrans, tilde.isoTop, moduleSpecΓFunctor, Sheaf.forget]
    rw [toOpen_fromTildeΓ_app]
    exact (modulesSpecToSheaf.obj M).obj.map_id _

中文:
定义 tilde.adjunction
  签名: : tilde.functor R ⊣ moduleSpecΓFunctor where
  定义体: toTildeΓNatIso.hom
  counit := fromTildeΓNatTrans
  left_triangle_components M := by
    apply SpecModulesToSheafFullyFaithful.map_injective
    apply CategoryTheory.Sheaf.hom_ext
    apply (TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens).symm.injective
    ext r : 3
    apply IsLocalizedModule.ext (.powers (M := R) r.unop)
      (toOpen _ (PrimeSpectrum.basicOpen (R := R) r.unop)).hom
    · rw [Subtype.forall]
      change Submonoid.powers _ <= (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen r.unop le_rfl
    dsimp [toTildeΓNatIso, isoTop,
      TopCat.Sheaf.restrictHomEquivHom, Functor.IsCoverDense.restrictHomEquivHom,
      fromTildeΓNatTrans, moduleSpecΓFunctor, Sheaf.forget, sheafToPresheaf]
    simp only [← ModuleCat.hom_comp, Functor.map_comp]
    congr 1
    rw [ObjectProperty.FullSubcategory.comp_hom]
    dsimp
    rw [toOpen_map_app_assoc]; rw [toOpen_fromTildeΓ_app]
    rfl
  right_triangle_components M := by
    dsimp [toTildeΓNatIso, fromTildeΓNatTrans, tilde.isoTop, moduleSpecΓFunctor, Sheaf.forget]
    rw [toOpen_fromTildeΓ_app]
    exact (modulesSpecToSheaf.obj M).obj.map_id _

Depends on / 依赖: NatIso.hom
-/
def tilde.adjunction : tilde.functor R ⊣ moduleSpecΓFunctor where
  unit := toTildeΓNatIso.hom
  counit := fromTildeΓNatTrans
  left_triangle_components M := by
    apply SpecModulesToSheafFullyFaithful.map_injective
    apply CategoryTheory.Sheaf.hom_ext
    apply (TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens).symm.injective
    ext r : 3
    apply IsLocalizedModule.ext (.powers (M := R) r.unop)
      (toOpen _ (PrimeSpectrum.basicOpen (R := R) r.unop)).hom
    · rw [Subtype.forall]
      change Submonoid.powers _ <= (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen r.unop le_rfl
    dsimp [toTildeΓNatIso, isoTop,
      TopCat.Sheaf.restrictHomEquivHom, Functor.IsCoverDense.restrictHomEquivHom,
      fromTildeΓNatTrans, moduleSpecΓFunctor, Sheaf.forget, sheafToPresheaf]
    simp only [← ModuleCat.hom_comp, Functor.map_comp]
    congr 1
    rw [ObjectProperty.FullSubcategory.comp_hom]
    dsimp
    rw [toOpen_map_app_assoc]; rw [toOpen_fromTildeΓ_app]
    rfl
  right_triangle_components M := by
    dsimp [toTildeΓNatIso, fromTildeΓNatTrans, tilde.isoTop, moduleSpecΓFunctor, Sheaf.forget]
    rw [toOpen_fromTildeΓ_app]
    exact (modulesSpecToSheaf.obj M).obj.map_id _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (tilde.adjunction (R := R)).unit
  body: by
  dsimp [tilde.adjunction]; infer_instance

中文:
实例 :
  签名: 是同构 (tilde.adjunction (R := R)).unit
  定义体: by
  dsimp [tilde.adjunction]; infer_instance

Depends on / 依赖: adjunction, infer_instance, tilde.adjunction
-/
instance : IsIso (tilde.adjunction (R := R)).unit := by
  dsimp [tilde.adjunction]; infer_instance

/--
Definition of `tilde.fullyFaithfulFunctor` / `tilde.fullyFaithfulFunctor` 的定义

English:
definition tilde.fullyFaithfulFunctor
  signature: : (tilde.functor R).FullyFaithful
  body: tilde.adjunction.fullyFaithfulLOfIsIsoUnit

中文:
定义 tilde.fullyFaithfulFunctor
  签名: : (tilde.functor R).满忠实
  定义体: tilde.adjunction.fullyFaithfulLOfIsIsoUnit

Depends on / 依赖: adjunction, fullyFaithfulLOfIsIsoUnit, tilde.adjunction.fullyFaithfulLOfIsIsoUnit
-/
def tilde.fullyFaithfulFunctor : (tilde.functor R).FullyFaithful :=
  tilde.adjunction.fullyFaithfulLOfIsIsoUnit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (tilde.functor R).Full
  body: tilde.fullyFaithfulFunctor.full

中文:
实例 :
  签名: (tilde.functor R).满
  定义体: tilde.fullyFaithfulFunctor.full

Depends on / 依赖: fullyFaithfulFunctor, tilde.fullyFaithfulFunctor.full
-/
instance : (tilde.functor R).Full := tilde.fullyFaithfulFunctor.full
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (tilde.functor R).Faithful
  body: tilde.fullyFaithfulFunctor.faithful

中文:
实例 :
  签名: (tilde.functor R).忠实
  定义体: tilde.fullyFaithfulFunctor.faithful

Depends on / 依赖: faithful, fullyFaithfulFunctor, tilde.fullyFaithfulFunctor.faithful
-/
instance : (tilde.functor R).Faithful := tilde.fullyFaithfulFunctor.faithful
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (tilde.functor R).IsLeftAdjoint
  body: tilde.adjunction.isLeftAdjoint

中文:
实例 :
  签名: (tilde.functor R).是左伴随
  定义体: tilde.adjunction.isLeftAdjoint

Depends on / 依赖: adjunction, isLeftAdjoint, tilde.adjunction.isLeftAdjoint
-/
instance : (tilde.functor R).IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (tilde.functor R).Additive
  body: have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts (tilde.functor R)
  Functor.additive_of_preservesBinaryBiproducts _

中文:
实例 :
  签名: (tilde.functor R).加性
  定义体: have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts (tilde.functor R)
  Functor.additive_of_preservesBinaryBiproducts _

Depends on / 依赖: Functor, Functor.additive_of_preservesBinaryBiproducts, Limits, Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts, additive_of_preservesBinaryBiproducts, functor, preservesBinaryBiproducts_of_preservesBinaryCoproducts, tilde.functor
-/
instance : (tilde.functor R).Additive :=
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts (tilde.functor R)
  Functor.additive_of_preservesBinaryBiproducts _

section

variable {M N : ModuleCat R} (f g : M ⟶ N)

/--
lemma `tilde.map_zero` / 引理 `tilde.map_zero`

English:
lemma tilde.map_zero
  statement: tilde.map (0 : M ⟶ N) = 0
  proof: (tilde.functor R).map_zero _ _

中文:
引理 tilde.map_zero
  结论: tilde.map (0 : M ⟶ N) = 0
  证明: (tilde.functor R).map_zero _ _
-/
@[simp] lemma tilde.map_zero : tilde.map (0 : M ⟶ N) = 0 :=
  (tilde.functor R).map_zero _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `tilde.map_add` / 引理 `tilde.map_add`

English:
lemma tilde.map_add
  statement: tilde.map (f + g) = tilde.map f + tilde.map g
  proof: (tilde.functor R).map_add

中文:
引理 tilde.map_add
  结论: tilde.map (f + g) = tilde.map f + tilde.map g
  证明: (tilde.functor R).map_add
-/
@[simp] lemma tilde.map_add : tilde.map (f + g) = tilde.map f + tilde.map g :=
  (tilde.functor R).map_add

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `tilde.map_sub` / 引理 `tilde.map_sub`

English:
lemma tilde.map_sub
  statement: tilde.map (f - g) = tilde.map f - tilde.map g
  proof: (tilde.functor R).map_sub

中文:
引理 tilde.map_sub
  结论: tilde.map (f - g) = tilde.map f - tilde.map g
  证明: (tilde.functor R).map_sub
-/
@[simp] lemma tilde.map_sub : tilde.map (f - g) = tilde.map f - tilde.map g :=
  (tilde.functor R).map_sub

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `tilde.map_neg` / 引理 `tilde.map_neg`

English:
lemma tilde.map_neg
  statement: tilde.map (-f) = - tilde.map f
  proof: (tilde.functor R).map_neg

中文:
引理 tilde.map_neg
  结论: tilde.map (-f) = - tilde.map f
  证明: (tilde.functor R).map_neg
-/
@[simp] lemma tilde.map_neg : tilde.map (-f) = - tilde.map f :=
  (tilde.functor R).map_neg

end

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isIso_fromTildeΓ_iff` / 引理 `isIso_fromTildeΓ_iff`

English:
lemma isIso_fromTildeΓ_iff
  given: {M : (Spec R).Modules}
  proof: tilde.adjunction.isIso_counit_app_iff_mem_essImage

中文:
引理 isIso_fromTildeΓ_iff
  条件: {M : (Spec R).Modules}
  证明: tilde.adjunction.isIso_counit_app_iff_mem_essImage

Depends on / 依赖: adjunction, isIso_counit_app_iff_mem_essImage, tilde.adjunction.isIso_counit_app_iff_mem_essImage
-/
lemma isIso_fromTildeΓ_iff {M : (Spec R).Modules} :
    IsIso M.fromTildeΓ ↔ (tilde.functor R).essImage M :=
  tilde.adjunction.isIso_counit_app_iff_mem_essImage

section IsQuasicoherent

open Limits

/-- Tilde of `R` as an `R`-module is isomorphic to the structure sheaf `𝒪_{Spec R}`. -/
noncomputable
/--
Definition of `tildeSelf` / `tildeSelf` 的定义

English:
definition tildeSelf
  signature: : tilde (ModuleCat.of R R) ≅ SheafOfModules.unit.{u} _
  body: .refl _

中文:
定义 tildeSelf
  签名: : tilde (模范畴.of R R) ≅ 模层.unit.{u} _
  定义体: .refl _
-/
def tildeSelf : tilde (ModuleCat.of R R) ≅ SheafOfModules.unit.{u} _ := .refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (Scheme.Modules.fromTildeΓ (SheafOfModules.unit.{u} (Spec R).ringCatSheaf))
  body: isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩

中文:
实例 :
  签名: 是同构 (概形.Modules.fromTildeΓ (模层.unit.{u} (Spec R).ringCatSheaf))
  定义体: isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩

Depends on / 依赖: _iff.mpr, tildeSelf
-/
instance : IsIso (Scheme.Modules.fromTildeΓ (SheafOfModules.unit.{u} (Spec R).ringCatSheaf)) :=
  isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩

/-- Tilde of direct sums of `R` as an `R`-module is isomorphic to the free sheaf. -/
noncomputable
/--
Definition of `tildeFinsupp` / `tildeFinsupp` 的定义

English:
definition tildeFinsupp
  signature: (ι : Type u)
  body: letI H : IsColimit (tilde.functor R).mapCocone (ModuleCat.finsuppCocone R R ι) :=
    isColimitOfPreserves (tilde.functor R) (ModuleCat.finsuppCoconeIsColimit R R ι)
  letI iso : (Discrete.functor fun (_ : ι) => ModuleCat.of R R) ⋙ tilde.functor R ≅
         Discrete.functor fun _ => SheafOfModules.unit.{u} _ :=
      Discrete.natIso (fun _ => tildeSelf)
  IsColimit.coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv iso.symm _).symm H) (coproductIsCoproduct _)

中文:
定义 tildeFinsupp
  签名: (ι : 类型u)
  定义体: letI H : IsColimit (tilde.functor R).mapCocone (ModuleCat.finsuppCocone R R ι) :=
    isColimitOfPreserves (tilde.functor R) (ModuleCat.finsuppCoconeIsColimit R R ι)
  letI iso : (Discrete.functor fun (_ : ι) => ModuleCat.of R R) ⋙ tilde.functor R ≅
         Discrete.functor fun _ => SheafOfModules.unit.{u} _ :=
      Discrete.natIso (fun _ => tildeSelf)
  IsColimit.coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv iso.symm _).symm H) (coproductIsCoproduct _)

Depends on / 依赖: Discrete, Discrete.functor, Discrete.natIso, IsColimit, IsColimit.coconePointUniqueUpToIso, IsColimit.precomposeHomEquiv, ModuleCat, ModuleCat.finsuppCocone, ModuleCat.finsuppCoconeIsColimit, ModuleCat.of, SheafOfModules, SheafOfModules.unit, coconePointUniqueUpToIso, coproductIsCoproduct, finsuppCocone, finsuppCoconeIsColimit, functor, isColimitOfPreserves, iso.symm, mapCocone
-/
def tildeFinsupp (ι : Type u) : tilde (ModuleCat.of R (ι ->₀ R)) ≅ SheafOfModules.free.{u} ι :=
letI H : IsColimit (tilde.functor R).mapCocone (ModuleCat.finsuppCocone R R ι) :=
    isColimitOfPreserves (tilde.functor R) (ModuleCat.finsuppCoconeIsColimit R R ι)
  letI iso : (Discrete.functor fun (_ : ι) => ModuleCat.of R R) ⋙ tilde.functor R ≅
         Discrete.functor fun _ => SheafOfModules.unit.{u} _ :=
      Discrete.natIso (fun _ => tildeSelf)
  IsColimit.coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv iso.symm _).symm H) (coproductIsCoproduct _)

instance (ι : Type u) :
    IsIso (Scheme.Modules.fromTildeΓ (R := R) (SheafOfModules.free.{u} ι)) :=
  isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeFinsupp _⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Given a presentation of a module `M`, we may construct an associated presentation of `M^~`. -/
noncomputable
/--
Definition of `presentationTilde` / `presentationTilde` 的定义

English:
definition presentationTilde
  signature: (s : Set M) (hs : Submodule.span R s = ⊤)
  body: by
  haveI H₁ : Function.Exact
      (ModuleCat.ofHom (Finsupp.linearCombination (α := t) R (↑)))
      (ModuleCat.ofHom (Finsupp.linearCombination (α := s) (M := M) R (↑))) :=
    (LinearMap.exact_iff.mpr (by simp [Finsupp.range_linearCombination, ht]))
  refine SheafOfModules.presentationOfIsCokernelFree.{u}
      ((tildeFinsupp t).inv ≫ tilde.map (ModuleCat.ofHom (Finsupp.linearCombination R (↑))) ≫
        (tildeFinsupp s).hom) ((tildeFinsupp s).inv ≫
          tilde.map (ModuleCat.ofHom (Finsupp.linearCombination R (↑)))) (by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Preadditive.IsIso.comp_left_eq_zero]
    rw [← tilde.map_comp]; rw [← ModuleCat.ofHom_comp]
    convert! tilde.map_zero
    exact congr(ModuleCat.ofHom $(H₁.linearMap_comp_eq_zero))) ?_
  letI h₁ := ModuleCat.isColimitCokernelCofork _ _ H₁
    (by simp [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hs])
  refine IsCokernel.ofIso _ (CokernelCofork.mapIsColimit _ h₁ (tilde.functor R)) _ (tildeFinsupp t)
    (tildeFinsupp s) (.refl _) (by simp) (by simp)

中文:
定义 presentationTilde
  签名: (s : 集合 M) (hs : 子模.span R s = ⊤)
  定义体: by
  haveI H₁ : Function.Exact
      (ModuleCat.ofHom (Finsupp.linearCombination (α := t) R (↑)))
      (ModuleCat.ofHom (Finsupp.linearCombination (α := s) (M := M) R (↑))) :=
    (LinearMap.exact_iff.mpr (by simp [Finsupp.range_linearCombination, ht]))
  refine SheafOfModules.presentationOfIsCokernelFree.{u}
      ((tildeFinsupp t).inv ≫ tilde.map (ModuleCat.ofHom (Finsupp.linearCombination R (↑))) ≫
        (tildeFinsupp s).hom) ((tildeFinsupp s).inv ≫
          tilde.map (ModuleCat.ofHom (Finsupp.linearCombination R (↑)))) (by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Preadditive.IsIso.comp_left_eq_zero]
    rw [← tilde.map_comp]; rw [← ModuleCat.ofHom_comp]
    convert! tilde.map_zero
    exact congr(ModuleCat.ofHom $(H₁.linearMap_comp_eq_zero))) ?_
  letI h₁ := ModuleCat.isColimitCokernelCofork _ _ H₁
    (by simp [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hs])
  refine IsCokernel.ofIso _ (CokernelCofork.mapIsColimit _ h₁ (tilde.functor R)) _ (tildeFinsupp t)
    (tildeFinsupp s) (.refl _) (by simp) (by simp)

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Finsupp.range_linearCombination, Function, Function.Exact, LinearMap, LinearMap.exact_iff.mpr, ModuleCat, ModuleCat.ofHom, SheafOfModules, SheafOfModules.presentationOfIsCokernelFree, exact_iff, linearCombination, presentationOfIsCokernelFree, range_linearCombination, tilde.map, tildeFinsupp
-/
def presentationTilde (s : Set M) (hs : Submodule.span R s = ⊤)
    (t : Set (s ->₀ R))
    (ht : Submodule.span R t = LinearMap.ker (Finsupp.linearCombination R ((↑) : s -> M))) :
    (tilde M).Presentation := by
  haveI H₁ : Function.Exact
      (ModuleCat.ofHom (Finsupp.linearCombination (α := t) R (↑)))
      (ModuleCat.ofHom (Finsupp.linearCombination (α := s) (M := M) R (↑))) :=
    (LinearMap.exact_iff.mpr (by simp [Finsupp.range_linearCombination, ht]))
  refine SheafOfModules.presentationOfIsCokernelFree.{u}
      ((tildeFinsupp t).inv ≫ tilde.map (ModuleCat.ofHom (Finsupp.linearCombination R (↑))) ≫
        (tildeFinsupp s).hom) ((tildeFinsupp s).inv ≫
          tilde.map (ModuleCat.ofHom (Finsupp.linearCombination R (↑)))) (by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Preadditive.IsIso.comp_left_eq_zero]
    rw [← tilde.map_comp]; rw [← ModuleCat.ofHom_comp]
    convert! tilde.map_zero
    exact congr(ModuleCat.ofHom $(H₁.linearMap_comp_eq_zero))) ?_
  letI h₁ := ModuleCat.isColimitCokernelCofork _ _ H₁
    (by simp [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hs])
  refine IsCokernel.ofIso _ (CokernelCofork.mapIsColimit _ h₁ (tilde.functor R)) _ (tildeFinsupp t)
    (tildeFinsupp s) (.refl _) (by simp) (by simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (tilde M).IsQuasicoherent
  body: (presentationTilde.{u} _ .univ (by simp) _ (Submodule.span_eq _)).isQuasicoherent

中文:
实例 :
  签名: (tilde M).是Quasicoherent
  定义体: (presentationTilde.{u} _ .univ (by simp) _ (Submodule.span_eq _)).isQuasicoherent

Depends on / 依赖: Submodule, Submodule.span_eq, isQuasicoherent, presentationTilde, span_eq
-/
instance : (tilde M).IsQuasicoherent :=
  (presentationTilde.{u} _ .univ (by simp) _ (Submodule.span_eq _)).isQuasicoherent

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ((tilde.functor R).obj M).IsQuasicoherent
  body: inferInstanceAs (tilde M).IsQuasicoherent

中文:
实例 :
  签名: ((tilde.functor R).obj M).是Quasicoherent
  定义体: inferInstanceAs (tilde M).IsQuasicoherent

Depends on / 依赖: IsQuasicoherent
-/
instance : ((tilde.functor R).obj M).IsQuasicoherent :=
inferInstanceAs (tilde M).IsQuasicoherent

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_fromTildeΓ_of_presentation` / 引理 `isIso_fromTildeΓ_of_presentation`

English:
lemma isIso_fromTildeΓ_of_presentation
  given: (M : (Spec R).Modules) (P : M.Presentation)
  proof: by
  rw [isIso_fromTildeΓ_iff]
let g := (tilde.functor _).preimage (tildeFinsupp _).hom ≫ P.relations.π ≫ kernel.ι _ ≫
    (tildeFinsupp _).inv
  let iso : cokernel ((tilde.functor R).map g) ≅ cokernel (P.relations.π ≫ kernel.ι _) := by
    refine cokernel.mapIso _ _ (tildeFinsupp _) (tildeFinsupp _) ?_
    simp only [g, (tilde.functor R).map_preimage]
    simp
  exact ⟨cokernel g, ⟨PreservesCokernel.iso (tilde.functor R) g ≪≫ iso ≪≫
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) P.isColimit⟩⟩

中文:
引理 isIso_fromTildeΓ_of_presentation
  条件: (M : (Spec R).Modules) (P : M.呈现)
  证明: by
  rw [isIso_fromTildeΓ_iff]
let g := (tilde.functor _).preimage (tildeFinsupp _).hom ≫ P.relations.π ≫ kernel.ι _ ≫
    (tildeFinsupp _).inv
  let iso : cokernel ((tilde.functor R).map g) ≅ cokernel (P.relations.π ≫ kernel.ι _) := by
    refine cokernel.mapIso _ _ (tildeFinsupp _) (tildeFinsupp _) ?_
    simp only [g, (tilde.functor R).map_preimage]
    simp
  exact ⟨cokernel g, ⟨PreservesCokernel.iso (tilde.functor R) g ≪≫ iso ≪≫
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) P.isColimit⟩⟩

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, P.isColimit, P.relations, PreservesCokernel, PreservesCokernel.iso, coconePointUniqueUpToIso, cokernel, cokernel.mapIso, colimit, colimit.isColimit, functor, isColimit, kernel, mapIso, map_preimage, preimage, relations, tilde.functor, tildeFinsupp
-/
lemma isIso_fromTildeΓ_of_presentation (M : (Spec R).Modules) (P : M.Presentation) :
    IsIso M.fromTildeΓ := by
  rw [isIso_fromTildeΓ_iff]
let g := (tilde.functor _).preimage (tildeFinsupp _).hom ≫ P.relations.π ≫ kernel.ι _ ≫
    (tildeFinsupp _).inv
  let iso : cokernel ((tilde.functor R).map g) ≅ cokernel (P.relations.π ≫ kernel.ι _) := by
    refine cokernel.mapIso _ _ (tildeFinsupp _) (tildeFinsupp _) ?_
    simp only [g, (tilde.functor R).map_preimage]
    simp
  exact ⟨cokernel g, ⟨PreservesCokernel.iso (tilde.functor R) g ≪≫ iso ≪≫
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) P.isColimit⟩⟩

section IsLocalizing

variable (M : (Spec R).Modules) (f : R) {S : CommRingCat.{u}} (φ : R ⟶ S)

open TopologicalSpace

/--
Definition of `IsLocalizing` / `IsLocalizing` 的定义

English:
abbreviation IsLocalizing
  signature: (M : TopCat.Sheaf (ModuleCat R) (Spec R))
  body: forall f : R, IsLocalizedModule (.powers f) (M.obj.map (basicOpen f).leTop.op).hom

中文:
缩写 IsLocalizing
  签名: (M : 顶元素范畴.层 (模范畴 R) (Spec R))
  定义体: forall f : R, IsLocalizedModule (.powers f) (M.obj.map (basicOpen f).leTop.op).hom

Depends on / 依赖: IsLocalizedModule, M.obj.map, basicOpen, leTop.op, powers
-/
abbrev IsLocalizing (M : TopCat.Sheaf (ModuleCat R) (Spec R)) : Prop :=
  forall f : R, IsLocalizedModule (.powers f) (M.obj.map (basicOpen f).leTop.op).hom

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isLocalizing_of_iso` / 定理 `isLocalizing_of_iso`

English:
theorem isLocalizing_of_iso
  statement: {M N : TopCat.Sheaf (ModuleCat R) (Spec R)} (φ : M ≅ N)
  proof: by
  intro f
  rw [← IsLocalizedModule.comp_iff_of_bijective_left _ _ <|
    ConcreteCategory.bijective_of_isIso (φ.inv.hom.app (op (basicOpen f)))]; rw [← ModuleCat.hom_comp]; rw [φ.inv.hom.naturality (basicOpen f).leTop.op]; rw [ModuleCat.hom_comp]; rw [IsLocalizedModule.comp_iff_of_bijective_right _ _ ConcreteCategory.bijective_of_isIso _]
  exact hM f

中文:
定理 isLocalizing_of_iso
  结论: {M N : 顶元素范畴.层 (模范畴 R) (Spec R)} (φ : M ≅ N)
  证明: by
  intro f
  rw [← IsLocalizedModule.comp_iff_of_bijective_left _ _ <|
    ConcreteCategory.bijective_of_isIso (φ.inv.hom.app (op (basicOpen f)))]; rw [← ModuleCat.hom_comp]; rw [φ.inv.hom.naturality (basicOpen f).leTop.op]; rw [ModuleCat.hom_comp]; rw [IsLocalizedModule.comp_iff_of_bijective_right _ _ ConcreteCategory.bijective_of_isIso _]
  exact hM f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.bijective_of_isIso, IsLocalizedModule, IsLocalizedModule.comp_iff_of_bijective_left, IsLocalizedModule.comp_iff_of_bijective_right, ModuleCat, ModuleCat.hom_comp, basicOpen, bijective_of_isIso, comp_iff_of_bijective_left, comp_iff_of_bijective_right, hom_comp, inv.hom.app, inv.hom.naturality, leTop.op, naturality
-/
theorem isLocalizing_of_iso {M N : TopCat.Sheaf (ModuleCat R) (Spec R)} (φ : M ≅ N)
    (hM : IsLocalizing M) :
    IsLocalizing N := by
  intro f
  rw [← IsLocalizedModule.comp_iff_of_bijective_left _ _ <|
    ConcreteCategory.bijective_of_isIso (φ.inv.hom.app (op (basicOpen f)))]; rw [← ModuleCat.hom_comp]; rw [φ.inv.hom.naturality (basicOpen f).leTop.op]; rw [ModuleCat.hom_comp]; rw [IsLocalizedModule.comp_iff_of_bijective_right _ _ ConcreteCategory.bijective_of_isIso _]
  exact hM f

/--
theorem `isLocalizing_iff_of_iso` / 定理 `isLocalizing_iff_of_iso`

English:
theorem isLocalizing_iff_of_iso
  given: {M N : TopCat.Sheaf (ModuleCat R) (Spec R)} (φ : M ≅ N)
  proof: ⟨fun h => isLocalizing_of_iso φ h, fun h => isLocalizing_of_iso φ.symm h⟩

中文:
定理 isLocalizing_iff_of_iso
  条件: {M N : 顶元素范畴.层 (模范畴 R) (Spec R)} (φ : M ≅ N)
  证明: ⟨fun h => isLocalizing_of_iso φ h, fun h => isLocalizing_of_iso φ.symm h⟩

Depends on / 依赖: isLocalizing_of_iso
-/
theorem isLocalizing_iff_of_iso {M N : TopCat.Sheaf (ModuleCat R) (Spec R)} (φ : M ≅ N) :
    IsLocalizing M ↔ IsLocalizing N :=
  ⟨fun h => isLocalizing_of_iso φ h, fun h => isLocalizing_of_iso φ.symm h⟩

/--
theorem `isLocalizing_of_isIso_app_top` / 定理 `isLocalizing_of_isIso_app_top`

English:
theorem isLocalizing_of_isIso_app_top
  statement: {M N : TopCat.Sheaf (ModuleCat.{u} R) (Spec R)} {φ : M ⟶ N}
  proof: by
  refine TopCat.Sheaf.isIso_iff_isIso_basis (φ := φ) isBasis_basic_opens (fun f => ?_)
  refine ModuleCat.isIso_of_isLocalizedModule_comp (hM f) ?_
  rw [φ.hom.naturality]
  exact IsLocalizedModule.of_linearEquiv_right _ _ (asIso (φ.hom.app (op ⊤))).toLinearEquiv

中文:
定理 isLocalizing_of_isIso_app_top
  结论: {M N : 顶元素范畴.层 (模范畴.{u} R) (Spec R)} {φ : M ⟶ N}
  证明: by
  refine TopCat.Sheaf.isIso_iff_isIso_basis (φ := φ) isBasis_basic_opens (fun f => ?_)
  refine ModuleCat.isIso_of_isLocalizedModule_comp (hM f) ?_
  rw [φ.hom.naturality]
  exact IsLocalizedModule.of_linearEquiv_right _ _ (asIso (φ.hom.app (op ⊤))).toLinearEquiv

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.of_linearEquiv_right, ModuleCat, ModuleCat.isIso_of_isLocalizedModule_comp, TopCat, TopCat.Sheaf.isIso_iff_isIso_basis, hom.app, hom.naturality, isBasis_basic_opens, isIso_iff_isIso_basis, isIso_of_isLocalizedModule_comp, naturality, of_linearEquiv_right, toLinearEquiv
-/
theorem isLocalizing_of_isIso_app_top {M N : TopCat.Sheaf (ModuleCat.{u} R) (Spec R)} {φ : M ⟶ N}
    (h : IsIso (φ.hom.app (op ⊤))) (hM : IsLocalizing M) (hN : IsLocalizing N) :
    IsIso φ := by
  refine TopCat.Sheaf.isIso_iff_isIso_basis (φ := φ) isBasis_basic_opens (fun f => ?_)
  refine ModuleCat.isIso_of_isLocalizedModule_comp (hM f) ?_
  rw [φ.hom.naturality]
  exact IsLocalizedModule.of_linearEquiv_right _ _ (asIso (φ.hom.app (op ⊤))).toLinearEquiv

/--
theorem `isLocalizing_tilde` / 定理 `isLocalizing_tilde`

English:
theorem isLocalizing_tilde
  given: (M : ModuleCat R)
  proof: by
  intro f
  -- We can't rewrite with `tilde.toOpen_res` below, because of def-eq abuse between
  -- `Spec R` and `PrimeSpectrum R`.
  have heq : tilde.toOpen M ⊤ ≫ (modulesSpecToSheaf.obj (tilde M)).obj.map (basicOpen f).leTop.op =
      tilde.toOpen M (basicOpen f) :=
    tilde.toOpen_res _ _ _ _
  rw [← IsLocalizedModule.comp_iff_of_bijective_right _ _ <|
    ConcreteCategory.bijective_of_isIso (tilde.toOpen M ⊤)]; rw [← ModuleCat.hom_comp]; rw [heq]
  infer_instance

中文:
定理 isLocalizing_tilde
  条件: (M : 模范畴 R)
  证明: by
  intro f
  -- We can't rewrite with `tilde.toOpen_res` below, because of def-eq abuse between
  -- `Spec R` and `PrimeSpectrum R`.
  have heq : tilde.toOpen M ⊤ ≫ (modulesSpecToSheaf.obj (tilde M)).obj.map (basicOpen f).leTop.op =
      tilde.toOpen M (basicOpen f) :=
    tilde.toOpen_res _ _ _ _
  rw [← IsLocalizedModule.comp_iff_of_bijective_right _ _ <|
    ConcreteCategory.bijective_of_isIso (tilde.toOpen M ⊤)]; rw [← ModuleCat.hom_comp]; rw [heq]
  infer_instance
-/
theorem isLocalizing_tilde (M : ModuleCat R) :
    IsLocalizing (modulesSpecToSheaf.obj (tilde M)) := by
  intro f
  -- We can't rewrite with `tilde.toOpen_res` below, because of def-eq abuse between
  -- `Spec R` and `PrimeSpectrum R`.
  have heq : tilde.toOpen M ⊤ ≫ (modulesSpecToSheaf.obj (tilde M)).obj.map (basicOpen f).leTop.op =
      tilde.toOpen M (basicOpen f) :=
    tilde.toOpen_res _ _ _ _
  rw [← IsLocalizedModule.comp_iff_of_bijective_right _ _ <|
    ConcreteCategory.bijective_of_isIso (tilde.toOpen M ⊤)]; rw [← ModuleCat.hom_comp]; rw [heq]
  infer_instance

/--
theorem `isIso_fromTildeΓ_iff_isLocalizing` / 定理 `isIso_fromTildeΓ_iff_isLocalizing`

English:
theorem isIso_fromTildeΓ_iff_isLocalizing
  given: (M : (Spec R).Modules)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← isLocalizing_iff_of_iso (modulesSpecToSheaf.mapIso (asIso M.fromTildeΓ))]
    exact isLocalizing_tilde _
  · rw [← isIso_iff_of_reflects_iso _ modulesSpecToSheaf]
    refine isLocalizing_of_isIso_app_top ?_ (isLocalizing_tilde _) h
    rw [← isIso_comp_left_iff (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) ⊤)]; rw [Scheme.Modules.toOpen_fromTildeΓ_app]
    simpa using IsIso.id _

中文:
定理 isIso_fromTildeΓ_iff_isLocalizing
  条件: (M : (Spec R).Modules)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← isLocalizing_iff_of_iso (modulesSpecToSheaf.mapIso (asIso M.fromTildeΓ))]
    exact isLocalizing_tilde _
  · rw [← isIso_iff_of_reflects_iso _ modulesSpecToSheaf]
    refine isLocalizing_of_isIso_app_top ?_ (isLocalizing_tilde _) h
    rw [← isIso_comp_left_iff (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) ⊤)]; rw [Scheme.Modules.toOpen_fromTildeΓ_app]
    simpa using IsIso.id _

Depends on / 依赖: IsIso.id, M.fromTilde, Modules, Scheme, Scheme.Modules.toOpen_fromTilde, infer_instance, isIso_comp_left_iff, isIso_iff_of_reflects_iso, isLocalizing_iff_of_iso, isLocalizing_of_isIso_app_top, isLocalizing_tilde, mapIso, modulesSpecToSheaf, modulesSpecToSheaf.mapIso, modulesSpecToSheaf.obj, presheaf, presheaf.obj, tilde.toOpen, toOpen
-/
theorem isIso_fromTildeΓ_iff_isLocalizing (M : (Spec R).Modules) :
    IsIso M.fromTildeΓ ↔ IsLocalizing (modulesSpecToSheaf.obj M) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← isLocalizing_iff_of_iso (modulesSpecToSheaf.mapIso (asIso M.fromTildeΓ))]
    exact isLocalizing_tilde _
  · rw [← isIso_iff_of_reflects_iso _ modulesSpecToSheaf]
    refine isLocalizing_of_isIso_app_top ?_ (isLocalizing_tilde _) h
    rw [← isIso_comp_left_iff (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) ⊤)]; rw [Scheme.Modules.toOpen_fromTildeΓ_app]
    simpa using IsIso.id _

/--
Definition of `pushforwardCompModulesSpecToSheafIso` / `pushforwardCompModulesSpecToSheafIso` 的定义

English:
definition pushforwardCompModulesSpecToSheafIso
  signature: :
  body: (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (SheafOfModules.pushforwardCompForgetToSheafModuleCat _ _ _
    (initialOpOfTerminal isTerminalTop)) _ ≪≫ Functor.associator _ _ _ ≪≫
    (Functor.isoWhiskerLeft _ (Functor.associator _ _ _)) ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.sheafComposePushforwardComp φ) ≪≫
    (Functor.associator _ _ _).symm

中文:
定义 pushforwardCompModulesSpecToSheafIso
  签名: :
  定义体: (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (SheafOfModules.pushforwardCompForgetToSheafModuleCat _ _ _
    (initialOpOfTerminal isTerminalTop)) _ ≪≫ Functor.associator _ _ _ ≪≫
    (Functor.isoWhiskerLeft _ (Functor.associator _ _ _)) ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.sheafComposePushforwardComp φ) ≪≫
    (Functor.associator _ _ _).symm

Depends on / 依赖: Functor, Functor.associator, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, Modules, Scheme, Scheme.Modules.sheafComposePushforwardComp, SheafOfModules, SheafOfModules.pushforwardCompForgetToSheafModuleCat, associator, initialOpOfTerminal, isTerminalTop, isoWhiskerLeft, isoWhiskerRight, pushforwardCompForgetToSheafModuleCat, sheafComposePushforwardComp
-/
def pushforwardCompModulesSpecToSheafIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ modulesSpecToSheaf ≅
      modulesSpecToSheaf ⋙ TopCat.Sheaf.pushforward (ModuleCat S) (Spec.map φ).base ⋙
      sheafCompose _ (ModuleCat.restrictScalars φ.hom) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (SheafOfModules.pushforwardCompForgetToSheafModuleCat _ _ _
    (initialOpOfTerminal isTerminalTop)) _ ≪≫ Functor.associator _ _ _ ≪≫
    (Functor.isoWhiskerLeft _ (Functor.associator _ _ _)) ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.sheafComposePushforwardComp φ) ≪≫
    (Functor.associator _ _ _).symm

open scoped ModuleCat.Algebra in
/--
theorem `isLocalizing_pushforward_of_isLocalizing` / 定理 `isLocalizing_pushforward_of_isLocalizing`

English:
theorem isLocalizing_pushforward_of_isLocalizing
  statement: {M : (Spec S).Modules}
  proof: by
  rw [← Functor.comp_obj]; rw [isLocalizing_iff_of_iso ((pushforwardCompModulesSpecToSheafIso φ).app M)]
  have : CommRing ((Spec S).ringCatSheaf.obj.obj ((Opens.map (Spec.map φ).base).op.obj (op ⊤))) :=
    inferInstanceAs (CommRing Γ(Spec S, ⊤))
  algebraize [φ.hom]
  exact fun f => IsLocalizedModule.restrictScalars_powers f _ (h := h (φ f))

中文:
定理 isLocalizing_pushforward_of_isLocalizing
  结论: {M : (Spec S).Modules}
  证明: by
  rw [← Functor.comp_obj]; rw [isLocalizing_iff_of_iso ((pushforwardCompModulesSpecToSheafIso φ).app M)]
  have : CommRing ((Spec S).ringCatSheaf.obj.obj ((Opens.map (Spec.map φ).base).op.obj (op ⊤))) :=
    inferInstanceAs (CommRing Γ(Spec S, ⊤))
  algebraize [φ.hom]
  exact fun f => IsLocalizedModule.restrictScalars_powers f _ (h := h (φ f))

Depends on / 依赖: CommRing, Functor, Functor.comp_obj, IsLocalizedModule, IsLocalizedModule.restrictScalars_powers, Opens.map, Spec.map, algebraize, comp_obj, isLocalizing_iff_of_iso, op.obj, pushforwardCompModulesSpecToSheafIso, restrictScalars_powers, ringCatSheaf, ringCatSheaf.obj.obj
-/
theorem isLocalizing_pushforward_of_isLocalizing {M : (Spec S).Modules}
    (h : IsLocalizing (modulesSpecToSheaf.obj M)) :
    IsLocalizing (modulesSpecToSheaf.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj M)) := by
  rw [← Functor.comp_obj]; rw [isLocalizing_iff_of_iso ((pushforwardCompModulesSpecToSheafIso φ).app M)]
  have : CommRing ((Spec S).ringCatSheaf.obj.obj ((Opens.map (Spec.map φ).base).op.obj (op ⊤))) :=
    inferInstanceAs (CommRing Γ(Spec S, ⊤))
  algebraize [φ.hom]
  exact fun f => IsLocalizedModule.restrictScalars_powers f _ (h := h (φ f))

/--
theorem `isIso_fromTildeΓ_pushforward` / 定理 `isIso_fromTildeΓ_pushforward`

English:
theorem isIso_fromTildeΓ_pushforward
  given: (M : (Spec S).Modules) [h : IsIso M.fromTildeΓ]
  proof: by
  simp_all only [isIso_fromTildeΓ_iff_isLocalizing]
  exact isLocalizing_pushforward_of_isLocalizing φ h

中文:
定理 isIso_fromTildeΓ_pushforward
  条件: (M : (Spec S).Modules) [h : 是同构 M.fromTildeΓ]
  证明: by
  simp_all only [isIso_fromTildeΓ_iff_isLocalizing]
  exact isLocalizing_pushforward_of_isLocalizing φ h

Depends on / 依赖: isLocalizing_pushforward_of_isLocalizing
-/
theorem isIso_fromTildeΓ_pushforward (M : (Spec S).Modules) [h : IsIso M.fromTildeΓ] :
    IsIso ((Scheme.Modules.pushforward (Spec.map φ)).obj M).fromTildeΓ := by
  simp_all only [isIso_fromTildeΓ_iff_isLocalizing]
  exact isLocalizing_pushforward_of_isLocalizing φ h

end IsLocalizing

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Scheme.Modules.isQuasicoherent_restrictFunctor` / 实例 `Scheme.Modules.isQuasicoherent_restrictFunctor`

English:
instance Scheme.Modules.isQuasicoherent_restrictFunctor
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y)
  body: by
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf := { app U := (f.appIso U.unop).inv }
  have hα : IsIso α := NatIso.isIso_of_isIso_app _
  let φ : X.ringCatSheaf ⟶ (f.opensFunctor.sheafPushforwardContinuous _ _ _).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have : IsIso φ := by
    rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
    dsimp [φ]
    infer_instance
  exact SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u}
    f.opensFunctor φ (Scheme.Modules.restrictUnitIso _)

中文:
实例 概形.Modules.isQuasicoherent_restrictFunctor
  签名: {X Y : 概形.{u}} (f : X ⟶ Y)
  定义体: by
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf := { app U := (f.appIso U.unop).inv }
  have hα : IsIso α := NatIso.isIso_of_isIso_app _
  let φ : X.ringCatSheaf ⟶ (f.opensFunctor.sheafPushforwardContinuous _ _ _).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have : IsIso φ := by
    rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
    dsimp [φ]
    infer_instance
  exact SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u}
    f.opensFunctor φ (Scheme.Modules.restrictUnitIso _)

Depends on / 依赖: CommRingCat, Functor, Functor.whiskerRight, Modules, NatIso, NatIso.isIso_of_isIso_app, ObjectProperty, RingCat, Scheme, Scheme.Modules.r, SheafOfModules, SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint, U.unop, X.presheaf, X.ringCatSheaf, Y.presheaf, Y.ringCatSheaf, appIso, f.appIso, f.opensFunctor
-/
instance Scheme.Modules.isQuasicoherent_restrictFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) [M.IsQuasicoherent] :
    ((restrictFunctor f).obj M).IsQuasicoherent := by
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf := { app U := (f.appIso U.unop).inv }
  have hα : IsIso α := NatIso.isIso_of_isIso_app _
  let φ : X.ringCatSheaf ⟶ (f.opensFunctor.sheafPushforwardContinuous _ _ _).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have : IsIso φ := by
    rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
    dsimp [φ]
    infer_instance
  exact SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u}
    f.opensFunctor φ (Scheme.Modules.restrictUnitIso _)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Scheme.Modules.presentationRestrict` / `Scheme.Modules.presentationRestrict` 的定义

English:
definition Scheme.Modules.presentationRestrict
  signature: {X Y : Scheme.{u}} (f : Y ⟶ X)
  body: have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor f) :=
    inferInstance
  pres.map (Scheme.Modules.restrictFunctor.{u} f) (Scheme.Modules.restrictUnitIso _).symm

中文:
定义 概形.Modules.presentationRestrict
  签名: {X Y : 概形.{u}} (f : Y ⟶ X)
  定义体: have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor f) :=
    inferInstance
  pres.map (Scheme.Modules.restrictFunctor.{u} f) (Scheme.Modules.restrictUnitIso _).symm

Depends on / 依赖: Modules, PreservesColimitsOfSize, Scheme, Scheme.Modules.restrictFunctor, Scheme.Modules.restrictUnitIso, pres.map, restrictFunctor, restrictUnitIso
-/
def Scheme.Modules.presentationRestrict {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] {M : X.Modules} (pres : M.Presentation) :
    (M.restrict f).Presentation :=
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor f) :=
    inferInstance
  pres.map (Scheme.Modules.restrictFunctor.{u} f) (Scheme.Modules.restrictUnitIso _).symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Scheme.Modules.exists_isOpenCover_presentation` / 引理 `Scheme.Modules.exists_isOpenCover_presentation`

English:
lemma Scheme.Modules.exists_isOpenCover_presentation
  statement: {X : Scheme.{u}} (M : X.Modules)
  proof: by
  obtain ⟨⟨I, W, cov, pres⟩⟩ := SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := M)
  choose κ hsub heq using fun i => Opens.isBasis_iff_cover.mp X.isBasis_affineOpens (W i)
  refine ⟨Σ (i : I), κ i, fun j => j.2, fun i => ?_, ?_, ?_⟩
  · let u := X.homOfLE (U := i.2) (V := W i.1) (by simp [heq, le_sSup])
    have : PreservesColimitsOfSize.{u, u} (restrictFunctor u) := inferInstance
    let F := (overEquiv (W i.1)).functor ⋙ restrictFunctor u
    let iso : SheafOfModules.overFunctor X.ringCatSheaf _ ⋙ F ≅ restrictFunctor
      (Scheme.Opens.ι i.2.1) := (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv _) _ ≪≫
        (restrictFunctorComp _ _).symm ≪≫ (restrictFunctorCongr (by simp [u]))
exact SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso.app M).hom
      (pres i.1).map F (Scheme.Modules.restrictUnitIso _).symm
  · rw [Opens.coversTop_iff, IsOpenCover] at cov
    rw [IsOpenCover]; rw [iSup_sigma]; rw [← cov]
    refine iSup_congr fun i => ?_
    rw [heq i]; rw [sSup_eq_iSup']
  · intro j
    exact hsub _ j.2.2

中文:
引理 概形.Modules.存在_isOpenCover_presentation
  结论: {X : 概形.{u}} (M : X.Modules)
  证明: by
  obtain ⟨⟨I, W, cov, pres⟩⟩ := SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := M)
  choose κ hsub heq using fun i => Opens.isBasis_iff_cover.mp X.isBasis_affineOpens (W i)
  refine ⟨Σ (i : I), κ i, fun j => j.2, fun i => ?_, ?_, ?_⟩
  · let u := X.homOfLE (U := i.2) (V := W i.1) (by simp [heq, le_sSup])
    have : PreservesColimitsOfSize.{u, u} (restrictFunctor u) := inferInstance
    let F := (overEquiv (W i.1)).functor ⋙ restrictFunctor u
    let iso : SheafOfModules.overFunctor X.ringCatSheaf _ ⋙ F ≅ restrictFunctor
      (Scheme.Opens.ι i.2.1) := (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv _) _ ≪≫
        (restrictFunctorComp _ _).symm ≪≫ (restrictFunctorCongr (by simp [u]))
exact SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso.app M).hom
      (pres i.1).map F (Scheme.Modules.restrictUnitIso _).symm
  · rw [Opens.coversTop_iff, IsOpenCover] at cov
    rw [IsOpenCover]; rw [iSup_sigma]; rw [← cov]
    refine iSup_congr fun i => ?_
    rw [heq i]; rw [sSup_eq_iSup']
  · intro j
    exact hsub _ j.2.2

Depends on / 依赖: IsQuasicoherent, Opens.isBasis_iff_cover.mp, PreservesColimitsOfSize, SheafOfModules, SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData, SheafOfModules.overFunctor, X.homOfLE, X.isBasis_affineOpens, X.ringCatSheaf, functor, homOfLE, isBasis_affineOpens, isBasis_iff_cover, le_sSup, nonempty_quasicoherentData, overEquiv, overFunctor, restrictFunctor, ringCatSheaf
-/
lemma Scheme.Modules.exists_isOpenCover_presentation {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] :
    exists (ι : Type u) (U : ι -> X.Opens) (_ : forall i, (M.restrict (U i).ι).Presentation),
      IsOpenCover U ∧ (forall i, IsAffineOpen (U i)) := by
  obtain ⟨⟨I, W, cov, pres⟩⟩ := SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := M)
  choose κ hsub heq using fun i => Opens.isBasis_iff_cover.mp X.isBasis_affineOpens (W i)
  refine ⟨Σ (i : I), κ i, fun j => j.2, fun i => ?_, ?_, ?_⟩
  · let u := X.homOfLE (U := i.2) (V := W i.1) (by simp [heq, le_sSup])
    have : PreservesColimitsOfSize.{u, u} (restrictFunctor u) := inferInstance
    let F := (overEquiv (W i.1)).functor ⋙ restrictFunctor u
    let iso : SheafOfModules.overFunctor X.ringCatSheaf _ ⋙ F ≅ restrictFunctor
      (Scheme.Opens.ι i.2.1) := (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv _) _ ≪≫
        (restrictFunctorComp _ _).symm ≪≫ (restrictFunctorCongr (by simp [u]))
exact SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso.app M).hom
      (pres i.1).map F (Scheme.Modules.restrictUnitIso _).symm
  · rw [Opens.coversTop_iff, IsOpenCover] at cov
    rw [IsOpenCover]; rw [iSup_sigma]; rw [← cov]
    refine iSup_congr fun i => ?_
    rw [heq i]; rw [sSup_eq_iSup']
  · intro j
    exact hsub _ j.2.2

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Scheme.Modules.exists_affineOpenCover_presentation` / 引理 `Scheme.Modules.exists_affineOpenCover_presentation`

English:
lemma Scheme.Modules.exists_affineOpenCover_presentation
  statement: {X : Scheme.{u}} (M : X.Modules)
  proof: by
  obtain ⟨ι, U, pres, hU, hU'⟩ := M.exists_isOpenCover_presentation
  refine ⟨Scheme.AffineOpenCover.ofIsOpenCover _ hU hU', fun i => ⟨?_⟩⟩
exact SheafOfModules.Presentation.ofIsIso.{u, u, u} ((restrictFunctorComp _ _).app M).inv
    (presentationRestrict (hU' i).isoSpec.inv (pres i))

中文:
引理 概形.Modules.存在_affineOpenCover_presentation
  结论: {X : 概形.{u}} (M : X.Modules)
  证明: by
  obtain ⟨ι, U, pres, hU, hU'⟩ := M.exists_isOpenCover_presentation
  refine ⟨Scheme.AffineOpenCover.ofIsOpenCover _ hU hU', fun i => ⟨?_⟩⟩
exact SheafOfModules.Presentation.ofIsIso.{u, u, u} ((restrictFunctorComp _ _).app M).inv
    (presentationRestrict (hU' i).isoSpec.inv (pres i))

Depends on / 依赖: AffineOpenCover, M.exists_isOpenCover_presentation, Presentation, Scheme, Scheme.AffineOpenCover.ofIsOpenCover, SheafOfModules, SheafOfModules.Presentation.ofIsIso, exists_isOpenCover_presentation, isoSpec, isoSpec.inv, ofIsIso, ofIsOpenCover, presentationRestrict, restrictFunctorComp
-/
lemma Scheme.Modules.exists_affineOpenCover_presentation {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] :
    exists (𝒰 : Scheme.AffineOpenCover.{u} X),
      forall i, Nonempty (M.restrict (𝒰.f i)).Presentation := by
  obtain ⟨ι, U, pres, hU, hU'⟩ := M.exists_isOpenCover_presentation
  refine ⟨Scheme.AffineOpenCover.ofIsOpenCover _ hU hU', fun i => ⟨?_⟩⟩
exact SheafOfModules.Presentation.ofIsIso.{u, u, u} ((restrictFunctorComp _ _).app M).inv
    (presentationRestrict (hU' i).isoSpec.inv (pres i))

namespace QuasicoherentTilde

variable (M : (Spec R).Modules)

set_option backward.isDefEq.respectTransparency.types false in
-- TODO: Generalise this to a general scheme, replacing `f : R` by sections over a suitable set.
/--
Definition of `Aux` / `Aux` 的定义

English:
structure Aux
  parameters: (V : (Spec R).Opens)
  axioms and operations (2):
    - existence((f : R) (hf : basicOpen f <= V) (s : Γ(M, basicOpen f))) : exists (n : Nat) (t : Γ(M, V)), M.presheaf.map (homOfLE hf).op t = f ^ n • s
    - uniqueness((f : R) (hf : basicOpen f <= V) (t : Γ(M, V))) : M.presheaf.map (.op <| homOfLE hf) t = (0 : Γ(M, basicOpen f)) -> exists (n : Nat), f ^ n • t = 0

中文:
结构 Aux
  参数: (V : (Spec R).Opens)
  公理与运算 (2 个):
    - existence((f : R) (hf : basicOpen f <= V) (s : Γ(M, basicOpen f))) : 存在 (n : 自然数) (t : Γ(M, V)), M.presheaf.map (homOfLE hf).op t = f ^ n • s
    - uniqueness((f : R) (hf : basicOpen f <= V) (t : Γ(M, V))) : M.presheaf.map (.op <| homOfLE hf) t = (0 : Γ(M, basicOpen f)) -> 存在 (n : 自然数), f ^ n • t = 0
-/
private structure Aux (V : (Spec R).Opens) where
  existence (f : R) (hf : basicOpen f <= V) (s : Γ(M, basicOpen f)) :
    exists (n : Nat) (t : Γ(M, V)), M.presheaf.map (homOfLE hf).op t = f ^ n • s
  uniqueness (f : R) (hf : basicOpen f <= V) (t : Γ(M, V)) :
    M.presheaf.map (.op <| homOfLE hf) t = (0 : Γ(M, basicOpen f)) ->
    exists (n : Nat), f ^ n • t = 0

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Aux.of_le` / 引理 `Aux.of_le`

English:
lemma Aux.of_le
  statement: {M : (Spec R).Modules} {V : (Spec R).Opens} (g : R) (hg : basicOpen g <= V)
  proof: by
    obtain ⟨n, t, ht⟩ := hV.existence f (le_trans hfg hg) s
    use n, M.presheaf.map (homOfLE hg).op t
    simp [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, ht]
  uniqueness f hfg t ht := by
    obtain ⟨n, t', ht'⟩ := hV.existence g hg t
obtain ⟨m, hm⟩ := hV.uniqueness _ (le_trans hfg hg) t' by
      rw [← homOfLE_comp hfg hg]; rw [op_comp]; rw [M.presheaf.map_comp_apply]; rw [ht']; rw [M.map_smul_Spec]; rw [ht]
      simp
    refine ⟨m, ((M.isSMulRegular_of_le_basicOpen le_rfl).pow n).right_eq_zero_of_smul ?_⟩
    simp [smul_comm, ← ht', ← M.map_smul_Spec, hm]

中文:
引理 Aux.of_le
  结论: {M : (Spec R).Modules} {V : (Spec R).Opens} (g : R) (hg : basicOpen g <= V)
  证明: by
    obtain ⟨n, t, ht⟩ := hV.existence f (le_trans hfg hg) s
    use n, M.presheaf.map (homOfLE hg).op t
    simp [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, ht]
  uniqueness f hfg t ht := by
    obtain ⟨n, t', ht'⟩ := hV.existence g hg t
obtain ⟨m, hm⟩ := hV.uniqueness _ (le_trans hfg hg) t' by
      rw [← homOfLE_comp hfg hg]; rw [op_comp]; rw [M.presheaf.map_comp_apply]; rw [ht']; rw [M.map_smul_Spec]; rw [ht]
      simp
    refine ⟨m, ((M.isSMulRegular_of_le_basicOpen le_rfl).pow n).right_eq_zero_of_smul ?_⟩
    simp [smul_comm, ← ht', ← M.map_smul_Spec, hm]
-/
private lemma Aux.of_le {M : (Spec R).Modules} {V : (Spec R).Opens} (g : R) (hg : basicOpen g <= V)
    (hV : Aux M V) :
    Aux M (basicOpen g) where
  existence f hfg s := by
    obtain ⟨n, t, ht⟩ := hV.existence f (le_trans hfg hg) s
    use n, M.presheaf.map (homOfLE hg).op t
    simp [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, ht]
  uniqueness f hfg t ht := by
    obtain ⟨n, t', ht'⟩ := hV.existence g hg t
obtain ⟨m, hm⟩ := hV.uniqueness _ (le_trans hfg hg) t' by
      rw [← homOfLE_comp hfg hg]; rw [op_comp]; rw [M.presheaf.map_comp_apply]; rw [ht']; rw [M.map_smul_Spec]; rw [ht]
      simp
    refine ⟨m, ((M.isSMulRegular_of_le_basicOpen le_rfl).pow n).right_eq_zero_of_smul ?_⟩
    simp [smul_comm, ← ht', ← M.map_smul_Spec, hm]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Aux.of_eq_iSup_basicOpen` / 引理 `Aux.of_eq_iSup_basicOpen`

English:
lemma Aux.of_eq_iSup_basicOpen
  statement: {M : (Spec R).Modules} (V : (Spec R).Opens)
  proof: by
  have h₂ (i j : ι) : Aux M (basicOpen (g i * g j)) :=
    .of_le _ (basicOpen_mul_le_left _ _) (h₁ i)
  have hgle (i : ι) : basicOpen (g i) <= V := by rw [hg]; exact le_iSup_of_le _ le_rfl
  have hug (i : ι) (m : Nat) :
      IsUnit (algebraMap R (Module.End R Γ(M, basicOpen (g i))) (g i ^ m)) := by
    rw [map_pow]
    exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (g i) le_rfl).pow m
  -- We show existence and uniqueness separately.
  refine ⟨fun f hf s => ?_, fun f hf t hs => ?_⟩
  · have hfgi (i : ι) : basicOpen (f * g i) <= basicOpen (g i) := basicOpen_mul_le_right f (g i)
    let s' (i : ι) : Γ(M, basicOpen (f * g i)) :=
      M.presheaf.map (homOfLE <| basicOpen_mul_le_left f (g i)).op s
    /- By `h₁`, up to a factor of `f ^ N`, the restrictions of `s` to `D(f) ∩ D(gᵢ)` lift
    to sections `tᵢ` over `D(gᵢ)`. -/
    obtain ⟨N, t, ht⟩ : exists (N : Nat) (t : forall i, Γ(M, basicOpen (g i))),
        forall i, f ^ N • s' i = M.presheaf.map (homOfLE (basicOpen_mul_le_right f (g i))).op (t i) := by
      have (i : ι) : exists (n : Nat) (t : Γ(M, basicOpen (g i))),
          f ^ n • s' i = M.presheaf.map (homOfLE (hfgi i)).op t := by
        obtain ⟨n, t', ht'⟩ := (h₁ i).existence (f * g i) (hfgi i) (s' i)
        rw [mul_pow]; rw [mul_smul]; rw [smul_comm] at ht'
        obtain ⟨ψ, hψ⟩ := IsUnit.exists_right_inv (hug i n)
        use n, ψ t'
        apply (M.isSMulRegular_of_le_basicOpen (basicOpen_mul_le_right f (g i))).pow n
        dsimp
        rw [← ht']; rw [← Scheme.Modules.map_smul_Spec]
        congr 1
        exact congr($hψ t').symm
      choose n t' ht' using this
      have (i : ι) : n i <= ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have hN (i : ι) : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by grind
      refine ⟨⨆ i, n i, fun i => f ^ ((⨆ i, n i) - n i) • t' i, fun i => ?_⟩
      conv_lhs => rw [hN i]
      rw [pow_add]; rw [mul_smul]; rw [ht']; rw [M.map_smul_Spec]
    /- By `h₂`, up to a factor of `f ^ K`, the restrictions of `tᵢ` and `tⱼ` to
    to `D(gᵢ) ∩ D(gⱼ)` agree. -/
    obtain ⟨K, hK⟩ : exists (K : Nat), forall (i j : ι),
        M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (f ^ K • t i) =
          M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (f ^ K • t j) := by
      have (i j : ι) : exists (m : Nat),
          M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (f ^ m • t i) =
            M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (f ^ m • t j) := by
        have := (h₂ i j).uniqueness (f * (g i * g j)) (basicOpen_mul_le_right _ _)
          (M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (t i) -
            M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (t j)) ?_
        · obtain ⟨m, hm⟩ := this
          use m
          apply (M.isSMulRegular_of_le_basicOpen le_rfl).pow m
          simpa [M.map_smul_Spec _ (f ^ m), ← mul_smul, ← mul_smul, ← mul_pow, ← mul_comm f,
            smul_sub, sub_eq_zero] using hm
        · have hfgigi : basicOpen (f * (g i * g j)) <= basicOpen (f * g i) := by
            rw [← mul_assoc]
            exact basicOpen_mul_le_left _ _
          have hfgigj : basicOpen (f * (g i * g j)) <= basicOpen (f * g j) := by
            rw [mul_comm (g i) (g j)]; rw [← mul_assoc]
            exact basicOpen_mul_le_left _ _
          rw [map_sub]; rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [homOfLE_comp]; rw [homOfLE_comp]; rw [← homOfLE_comp hfgigi (hfgi i)]; rw [← homOfLE_comp hfgigj (hfgi j)]; rw [op_comp]; rw [M.presheaf.map_comp_apply]; rw [← ht i]; rw [M.map_smul_Spec]; rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [homOfLE_comp]; rw [op_comp]; rw [M.presheaf.map_comp_apply]; rw [← ht j]; rw [M.map_smul_Spec]; rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [homOfLE_comp]
          simp
      choose m hm using this
      let K := ⨆ i, ⨆ j, m i j
      refine ⟨K, fun i j => ?_⟩
      have : m i j <= K :=
        le_ciSup_of_le (Finite.bddAbove_range _) i (le_ciSup (Finite.bddAbove_range _) _)
      have : K = (K - m i j) + m i j := by lia
      rw [this]; rw [pow_add]; rw [mul_smul]; rw [mul_smul]; rw [M.map_smul_Spec]; rw [M.map_smul_Spec _ (f ^ (K - m i j))]; rw [hm i j]
    -- So up to a factor of `f ^ (N + K)`, the `tᵢ` glue.
    refine ⟨N + K, ?_⟩
    have := TopCat.Sheaf.existsUnique_gluing' ⟨_, M.isSheaf⟩ (fun i => basicOpen (g i)) V
      (fun i => homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl)) (by simp [hg])
      (fun i => f ^ K • t i) ?_
    · obtain ⟨a, ha, -⟩ := this
      use a
      refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i => basicOpen (f * g i)) _
          (fun i => homOfLE (basicOpen_mul_le_left f (g i))) ?_ _ _ ?_
      · rw [left_eq_inf.mpr hf, hg, inf_iSup_eq]
        simp_rw [basicOpen_mul]
        exact le_rfl
      · intro i
        rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [homOfLE_comp]; rw [← homOfLE_comp (basicOpen_mul_le_right _ _) (hgle i)]; rw [op_comp]; rw [M.presheaf.map_comp_apply]; rw [M.map_smul_Spec]; rw [ha]; rw [M.map_smul_Spec]; rw [pow_add]; rw [mul_smul]; rw [smul_comm]; rw [ht i]
    · intro i j
      have : Function.Injective (M.presheaf.map (eqToHom <| (basicOpen_mul (g i) (g j))).op) :=
        ConcreteCategory.injective_of_mono_of_preservesPullback _
      apply this
      dsimp [Opens.infLELeft, Opens.infLERight]
      simp_rw [← M.presheaf.map_comp_apply, ← op_comp, eqToHom_comp_homOfLE]
      exact hK i j
  · have (i : ι) : exists (n : Nat), M.presheaf.map (homOfLE (hgle i)).op (f ^ n • t) = 0 := by
      have := (h₁ i).uniqueness (f * g i) (basicOpen_mul_le_right f (g i))
        (M.presheaf.map (homOfLE (hgle i)).op t) ?_
      · obtain ⟨n, hn⟩ := this
        use n
        rw [mul_pow]; rw [mul_comm]; rw [mul_smul]; rw [← Scheme.Modules.map_smul_Spec] at hn
        exact ((M.isSMulRegular_of_le_basicOpen le_rfl).pow n).right_eq_zero_of_smul hn
      · rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp ((basicOpen_mul_le_left f (g i))) hf, op_comp, M.presheaf.map_comp_apply]
        simp [hs]
    choose n hn using this
    use ⨆ i, n i
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i => basicOpen (g i)) _
      (fun i => homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl))
    · simp [hg]
    · intro i
      have : n i <= ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by lia
      rw [this]; rw [pow_add]; rw [mul_smul]; rw [Scheme.Modules.map_smul_Spec]; rw [hn i]
      simp

中文:
引理 Aux.of_eq_iSup_basicOpen
  结论: {M : (Spec R).Modules} (V : (Spec R).Opens)
  证明: by
  have h₂ (i j : ι) : Aux M (basicOpen (g i * g j)) :=
    .of_le _ (basicOpen_mul_le_left _ _) (h₁ i)
  have hgle (i : ι) : basicOpen (g i) <= V := by rw [hg]; exact le_iSup_of_le _ le_rfl
  have hug (i : ι) (m : Nat) :
      IsUnit (algebraMap R (Module.End R Γ(M, basicOpen (g i))) (g i ^ m)) := by
    rw [map_pow]
    exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (g i) le_rfl).pow m
  -- We show existence and uniqueness separately.
  refine ⟨fun f hf s => ?_, fun f hf t hs => ?_⟩
  · have hfgi (i : ι) : basicOpen (f * g i) <= basicOpen (g i) := basicOpen_mul_le_right f (g i)
    let s' (i : ι) : Γ(M, basicOpen (f * g i)) :=
      M.presheaf.map (homOfLE <| basicOpen_mul_le_left f (g i)).op s
    /- By `h₁`, up to a factor of `f ^ N`, the restrictions of `s` to `D(f) ∩ D(gᵢ)` lift
    to sections `tᵢ` over `D(gᵢ)`. -/
    obtain ⟨N, t, ht⟩ : exists (N : Nat) (t : forall i, Γ(M, basicOpen (g i))),
        forall i, f ^ N • s' i = M.presheaf.map (homOfLE (basicOpen_mul_le_right f (g i))).op (t i) := by
      have (i : ι) : exists (n : Nat) (t : Γ(M, basicOpen (g i))),
          f ^ n • s' i = M.presheaf.map (homOfLE (hfgi i)).op t := by
        obtain ⟨n, t', ht'⟩ := (h₁ i).existence (f * g i) (hfgi i) (s' i)
        rw [mul_pow]; rw [mul_smul]; rw [smul_comm] at ht'
        obtain ⟨ψ, hψ⟩ := IsUnit.exists_right_inv (hug i n)
        use n, ψ t'
        apply (M.isSMulRegular_of_le_basicOpen (basicOpen_mul_le_right f (g i))).pow n
        dsimp
        rw [← ht']; rw [← Scheme.Modules.map_smul_Spec]
        congr 1
        exact congr($hψ t').symm
      choose n t' ht' using this
      have (i : ι) : n i <= ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have hN (i : ι) : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by grind
      refine ⟨⨆ i, n i, fun i => f ^ ((⨆ i, n i) - n i) • t' i, fun i => ?_⟩
      conv_lhs => rw [hN i]
      rw [pow_add]; rw [mul_smul]; rw [ht']; rw [M.map_smul_Spec]
    /- By `h₂`, up to a factor of `f ^ K`, the restrictions of `tᵢ` and `tⱼ` to
    to `D(gᵢ) ∩ D(gⱼ)` agree. -/
    obtain ⟨K, hK⟩ : exists (K : Nat), forall (i j : ι),
        M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (f ^ K • t i) =
          M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (f ^ K • t j) := by
      have (i j : ι) : exists (m : Nat),
          M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (f ^ m • t i) =
            M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (f ^ m • t j) := by
        have := (h₂ i j).uniqueness (f * (g i * g j)) (basicOpen_mul_le_right _ _)
          (M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (t i) -
            M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (t j)) ?_
        · obtain ⟨m, hm⟩ := this
          use m
          apply (M.isSMulRegular_of_le_basicOpen le_rfl).pow m
          simpa [M.map_smul_Spec _ (f ^ m), ← mul_smul, ← mul_smul, ← mul_pow, ← mul_comm f,
            smul_sub, sub_eq_zero] using hm
        · have hfgigi : basicOpen (f * (g i * g j)) <= basicOpen (f * g i) := by
            rw [← mul_assoc]
            exact basicOpen_mul_le_left _ _
          have hfgigj : basicOpen (f * (g i * g j)) <= basicOpen (f * g j) := by
            rw [mul_comm (g i) (g j)]; rw [← mul_assoc]
            exact basicOpen_mul_le_left _ _
          rw [map_sub]; rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [homOfLE_comp]; rw [homOfLE_comp]; rw [← homOfLE_comp hfgigi (hfgi i)]; rw [← homOfLE_comp hfgigj (hfgi j)]; rw [op_comp]; rw [M.presheaf.map_comp_apply]; rw [← ht i]; rw [M.map_smul_Spec]; rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [homOfLE_comp]; rw [op_comp]; rw [M.presheaf.map_comp_apply]; rw [← ht j]; rw [M.map_smul_Spec]; rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [homOfLE_comp]
          simp
      choose m hm using this
      let K := ⨆ i, ⨆ j, m i j
      refine ⟨K, fun i j => ?_⟩
      have : m i j <= K :=
        le_ciSup_of_le (Finite.bddAbove_range _) i (le_ciSup (Finite.bddAbove_range _) _)
      have : K = (K - m i j) + m i j := by lia
      rw [this]; rw [pow_add]; rw [mul_smul]; rw [mul_smul]; rw [M.map_smul_Spec]; rw [M.map_smul_Spec _ (f ^ (K - m i j))]; rw [hm i j]
    -- So up to a factor of `f ^ (N + K)`, the `tᵢ` glue.
    refine ⟨N + K, ?_⟩
    have := TopCat.Sheaf.existsUnique_gluing' ⟨_, M.isSheaf⟩ (fun i => basicOpen (g i)) V
      (fun i => homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl)) (by simp [hg])
      (fun i => f ^ K • t i) ?_
    · obtain ⟨a, ha, -⟩ := this
      use a
      refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i => basicOpen (f * g i)) _
          (fun i => homOfLE (basicOpen_mul_le_left f (g i))) ?_ _ _ ?_
      · rw [left_eq_inf.mpr hf, hg, inf_iSup_eq]
        simp_rw [basicOpen_mul]
        exact le_rfl
      · intro i
        rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [homOfLE_comp]; rw [← homOfLE_comp (basicOpen_mul_le_right _ _) (hgle i)]; rw [op_comp]; rw [M.presheaf.map_comp_apply]; rw [M.map_smul_Spec]; rw [ha]; rw [M.map_smul_Spec]; rw [pow_add]; rw [mul_smul]; rw [smul_comm]; rw [ht i]
    · intro i j
      have : Function.Injective (M.presheaf.map (eqToHom <| (basicOpen_mul (g i) (g j))).op) :=
        ConcreteCategory.injective_of_mono_of_preservesPullback _
      apply this
      dsimp [Opens.infLELeft, Opens.infLERight]
      simp_rw [← M.presheaf.map_comp_apply, ← op_comp, eqToHom_comp_homOfLE]
      exact hK i j
  · have (i : ι) : exists (n : Nat), M.presheaf.map (homOfLE (hgle i)).op (f ^ n • t) = 0 := by
      have := (h₁ i).uniqueness (f * g i) (basicOpen_mul_le_right f (g i))
        (M.presheaf.map (homOfLE (hgle i)).op t) ?_
      · obtain ⟨n, hn⟩ := this
        use n
        rw [mul_pow]; rw [mul_comm]; rw [mul_smul]; rw [← Scheme.Modules.map_smul_Spec] at hn
        exact ((M.isSMulRegular_of_le_basicOpen le_rfl).pow n).right_eq_zero_of_smul hn
      · rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp ((basicOpen_mul_le_left f (g i))) hf, op_comp, M.presheaf.map_comp_apply]
        simp [hs]
    choose n hn using this
    use ⨆ i, n i
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i => basicOpen (g i)) _
      (fun i => homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl))
    · simp [hg]
    · intro i
      have : n i <= ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by lia
      rw [this]; rw [pow_add]; rw [mul_smul]; rw [Scheme.Modules.map_smul_Spec]; rw [hn i]
      simp
-/
private lemma Aux.of_eq_iSup_basicOpen {M : (Spec R).Modules} (V : (Spec R).Opens)
    {ι : Type*} [Finite ι] (g : ι -> R) (hg : V = ⨆ i, basicOpen (g i))
    (h₁ : forall (i : ι), Aux M (basicOpen (g i))) :
    Aux M V := by
  have h₂ (i j : ι) : Aux M (basicOpen (g i * g j)) :=
    .of_le _ (basicOpen_mul_le_left _ _) (h₁ i)
  have hgle (i : ι) : basicOpen (g i) <= V := by rw [hg]; exact le_iSup_of_le _ le_rfl
  have hug (i : ι) (m : Nat) :
      IsUnit (algebraMap R (Module.End R Γ(M, basicOpen (g i))) (g i ^ m)) := by
    rw [map_pow]
    exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (g i) le_rfl).pow m
  -- We show existence and uniqueness separately.
  refine ⟨fun f hf s => ?_, fun f hf t hs => ?_⟩
  · have hfgi (i : ι) : basicOpen (f * g i) <= basicOpen (g i) := basicOpen_mul_le_right f (g i)
    let s' (i : ι) : Γ(M, basicOpen (f * g i)) :=
      M.presheaf.map (homOfLE <| basicOpen_mul_le_left f (g i)).op s
    /- By `h₁`, up to a factor of `f ^ N`, the restrictions of `s` to `D(f) ∩ D(gᵢ)` lift
    to sections `tᵢ` over `D(gᵢ)`. -/
    obtain ⟨N, t, ht⟩ : exists (N : Nat) (t : forall i, Γ(M, basicOpen (g i))),
        forall i, f ^ N • s' i = M.presheaf.map (homOfLE (basicOpen_mul_le_right f (g i))).op (t i) := by
      have (i : ι) : exists (n : Nat) (t : Γ(M, basicOpen (g i))),
          f ^ n • s' i = M.presheaf.map (homOfLE (hfgi i)).op t := by
        obtain ⟨n, t', ht'⟩ := (h₁ i).existence (f * g i) (hfgi i) (s' i)
        rw [mul_pow]; rw [mul_smul]; rw [smul_comm] at ht'
        obtain ⟨ψ, hψ⟩ := IsUnit.exists_right_inv (hug i n)
        use n, ψ t'
        apply (M.isSMulRegular_of_le_basicOpen (basicOpen_mul_le_right f (g i))).pow n
        dsimp
        rw [← ht']; rw [← Scheme.Modules.map_smul_Spec]
        congr 1
        exact congr($hψ t').symm
      choose n t' ht' using this
      have (i : ι) : n i <= ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have hN (i : ι) : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by grind
      refine ⟨⨆ i, n i, fun i => f ^ ((⨆ i, n i) - n i) • t' i, fun i => ?_⟩
      conv_lhs => rw [hN i]
      rw [pow_add]; rw [mul_smul]; rw [ht']; rw [M.map_smul_Spec]
    /- By `h₂`, up to a factor of `f ^ K`, the restrictions of `tᵢ` and `tⱼ` to
    to `D(gᵢ) ∩ D(gⱼ)` agree. -/
    obtain ⟨K, hK⟩ : exists (K : Nat), forall (i j : ι),
        M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (f ^ K • t i) =
          M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (f ^ K • t j) := by
      have (i j : ι) : exists (m : Nat),
          M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (f ^ m • t i) =
            M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (f ^ m • t j) := by
        have := (h₂ i j).uniqueness (f * (g i * g j)) (basicOpen_mul_le_right _ _)
          (M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (t i) -
            M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (t j)) ?_
        · obtain ⟨m, hm⟩ := this
          use m
          apply (M.isSMulRegular_of_le_basicOpen le_rfl).pow m
          simpa [M.map_smul_Spec _ (f ^ m), ← mul_smul, ← mul_smul, ← mul_pow, ← mul_comm f,
            smul_sub, sub_eq_zero] using hm
        · have hfgigi : basicOpen (f * (g i * g j)) <= basicOpen (f * g i) := by
            rw [← mul_assoc]
            exact basicOpen_mul_le_left _ _
          have hfgigj : basicOpen (f * (g i * g j)) <= basicOpen (f * g j) := by
            rw [mul_comm (g i) (g j)]; rw [← mul_assoc]
            exact basicOpen_mul_le_left _ _
          rw [map_sub]; rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [homOfLE_comp]; rw [homOfLE_comp]; rw [← homOfLE_comp hfgigi (hfgi i)]; rw [← homOfLE_comp hfgigj (hfgi j)]; rw [op_comp]; rw [M.presheaf.map_comp_apply]; rw [← ht i]; rw [M.map_smul_Spec]; rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [homOfLE_comp]; rw [op_comp]; rw [M.presheaf.map_comp_apply]; rw [← ht j]; rw [M.map_smul_Spec]; rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [homOfLE_comp]
          simp
      choose m hm using this
      let K := ⨆ i, ⨆ j, m i j
      refine ⟨K, fun i j => ?_⟩
      have : m i j <= K :=
        le_ciSup_of_le (Finite.bddAbove_range _) i (le_ciSup (Finite.bddAbove_range _) _)
      have : K = (K - m i j) + m i j := by lia
      rw [this]; rw [pow_add]; rw [mul_smul]; rw [mul_smul]; rw [M.map_smul_Spec]; rw [M.map_smul_Spec _ (f ^ (K - m i j))]; rw [hm i j]
    -- So up to a factor of `f ^ (N + K)`, the `tᵢ` glue.
    refine ⟨N + K, ?_⟩
    have := TopCat.Sheaf.existsUnique_gluing' ⟨_, M.isSheaf⟩ (fun i => basicOpen (g i)) V
      (fun i => homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl)) (by simp [hg])
      (fun i => f ^ K • t i) ?_
    · obtain ⟨a, ha, -⟩ := this
      use a
      refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i => basicOpen (f * g i)) _
          (fun i => homOfLE (basicOpen_mul_le_left f (g i))) ?_ _ _ ?_
      · rw [left_eq_inf.mpr hf, hg, inf_iSup_eq]
        simp_rw [basicOpen_mul]
        exact le_rfl
      · intro i
        rw [← M.presheaf.map_comp_apply]; rw [← op_comp]; rw [homOfLE_comp]; rw [← homOfLE_comp (basicOpen_mul_le_right _ _) (hgle i)]; rw [op_comp]; rw [M.presheaf.map_comp_apply]; rw [M.map_smul_Spec]; rw [ha]; rw [M.map_smul_Spec]; rw [pow_add]; rw [mul_smul]; rw [smul_comm]; rw [ht i]
    · intro i j
      have : Function.Injective (M.presheaf.map (eqToHom <| (basicOpen_mul (g i) (g j))).op) :=
        ConcreteCategory.injective_of_mono_of_preservesPullback _
      apply this
      dsimp [Opens.infLELeft, Opens.infLERight]
      simp_rw [← M.presheaf.map_comp_apply, ← op_comp, eqToHom_comp_homOfLE]
      exact hK i j
  · have (i : ι) : exists (n : Nat), M.presheaf.map (homOfLE (hgle i)).op (f ^ n • t) = 0 := by
      have := (h₁ i).uniqueness (f * g i) (basicOpen_mul_le_right f (g i))
        (M.presheaf.map (homOfLE (hgle i)).op t) ?_
      · obtain ⟨n, hn⟩ := this
        use n
        rw [mul_pow]; rw [mul_comm]; rw [mul_smul]; rw [← Scheme.Modules.map_smul_Spec] at hn
        exact ((M.isSMulRegular_of_le_basicOpen le_rfl).pow n).right_eq_zero_of_smul hn
      · rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp ((basicOpen_mul_le_left f (g i))) hf, op_comp, M.presheaf.map_comp_apply]
        simp [hs]
    choose n hn using this
    use ⨆ i, n i
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i => basicOpen (g i)) _
      (fun i => homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl))
    · simp [hg]
    · intro i
      have : n i <= ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by lia
      rw [this]; rw [pow_add]; rw [mul_smul]; rw [Scheme.Modules.map_smul_Spec]; rw [hn i]
      simp

/--
lemma `isLocalizing_iff_aux` / 引理 `isLocalizing_iff_aux`

English:
lemma isLocalizing_iff_aux
  given: (M : (Spec R).Modules)
  proof: by
  let φ (f : R) := ((modulesSpecToSheaf.obj M).obj.map (basicOpen f).leTop.op).hom
  refine ⟨fun h => ?_, fun h f => IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_⟩
  · have hf (f : R) : IsLocalizedModule.Away f (φ f) := h f
    refine ⟨fun f hle s => ?_, fun f hle s hs => ?_⟩
    · obtain ⟨n, y, hy⟩ := (hf f).surj _ _ s
      use n, y, hy.symm
    · obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f) (φ f)).mp hs
      use n, hn
  · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
  · intro x
    obtain ⟨n, t, ht⟩ := h.existence _ _ x
    use n, t, ht.symm
  · intro x hx
    obtain ⟨n, hn⟩ := h.uniqueness _ _ _ hx
    use n, hn

中文:
引理 isLocalizing_iff_aux
  条件: (M : (Spec R).Modules)
  证明: by
  let φ (f : R) := ((modulesSpecToSheaf.obj M).obj.map (basicOpen f).leTop.op).hom
  refine ⟨fun h => ?_, fun h f => IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_⟩
  · have hf (f : R) : IsLocalizedModule.Away f (φ f) := h f
    refine ⟨fun f hle s => ?_, fun f hle s hs => ?_⟩
    · obtain ⟨n, y, hy⟩ := (hf f).surj _ _ s
      use n, y, hy.symm
    · obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f) (φ f)).mp hs
      use n, hn
  · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
  · intro x
    obtain ⟨n, t, ht⟩ := h.existence _ _ x
    use n, t, ht.symm
  · intro x hx
    obtain ⟨n, hn⟩ := h.uniqueness _ _ _ hx
    use n, hn
-/
private lemma isLocalizing_iff_aux (M : (Spec R).Modules) :
    IsLocalizing (modulesSpecToSheaf.obj M) ↔ Aux M ⊤ := by
  let φ (f : R) := ((modulesSpecToSheaf.obj M).obj.map (basicOpen f).leTop.op).hom
  refine ⟨fun h => ?_, fun h f => IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_⟩
  · have hf (f : R) : IsLocalizedModule.Away f (φ f) := h f
    refine ⟨fun f hle s => ?_, fun f hle s hs => ?_⟩
    · obtain ⟨n, y, hy⟩ := (hf f).surj _ _ s
      use n, y, hy.symm
    · obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f) (φ f)).mp hs
      use n, hn
  · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
  · intro x
    obtain ⟨n, t, ht⟩ := h.existence _ _ x
    use n, t, ht.symm
  · intro x hx
    obtain ⟨n, hn⟩ := h.uniqueness _ _ _ hx
    use n, hn

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `aux_basicOpen_of_aux_restrict` / 引理 `aux_basicOpen_of_aux_restrict`

English:
lemma aux_basicOpen_of_aux_restrict
  statement: (M : (Spec R).Modules) (g : R)
  proof: by
  let a : R ⟶ CommRingCat.of (Localization.Away g) :=
CommRingCat.ofHom algebraMap R _
  set ψ : Spec (.of <| Localization.Away g) ⟶ Spec (.of R) := Spec.map a
  set M' : (Spec (.of <| Localization.Away g)).Modules := M.restrict ψ
  have heq (f : R) (hf : basicOpen f <= basicOpen g) :
      basicOpen f = ψ ''ᵁ basicOpen (a f) := by
    rw [← SpecMap_preimage_basicOpen]; rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    simp [a, ψ, hf]
  let iso : Γ(M.restrict ψ, ⊤) ≅ Γ(M, basicOpen g) :=
    M.restrictAppIso _ _ ≪≫ M.presheaf.mapIso (eqToIso <| by simp [ψ, a]).op
  let e (f : R) (hf : basicOpen f <= basicOpen g) : Γ(M', basicOpen (a f)) ≅ Γ(M, basicOpen f) :=
    M.restrictAppIso ψ (basicOpen (a f)) ≪≫ M.presheaf.mapIso (eqToIso <| heq f hf).op
  refine ⟨fun f hf s => ?_, fun f hf t ht => ?_⟩
  · obtain ⟨n, t, ht⟩ := h.existence (a f) le_top ((e _ hf).inv s)
    use n, iso.hom t
    have := congr((e _ hf).hom $ht)
    dsimp [M'] at this
    rw [← ConcreteCategory.comp_apply] at this
    simp only [homOfLE_leOfHom, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      eqToHom_op, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, e, iso] at this ⊢
    simp only [homOfLE_leOfHom, Scheme.Modules.map_restrictAppIso_hom_assoc, AddCommGrpCat.hom_comp,
      AddMonoidHom.coe_comp, Function.comp_apply, ← map_pow, ψ] at this
    rw [Scheme.Modules.restrictAppIso_smul_Spec] at this
    simpa [← Functor.map_comp_apply, eqToHom_comp_homOfLE_op, homOfLE_op_comp_eqToHom] using this
· obtain ⟨n, hn⟩ := h.uniqueness (a f) le_top (iso.inv t) by
      simpa [M', iso, ← M.presheaf.map_comp_apply, homOfLE_op_comp_eqToHom, e] using
        congr((e _ hf).inv $ht)
    use n
    have := congr(iso.hom $hn)
    dsimp [iso, ψ] at this
    rw [eqToHom_op]; rw [map_zero]; rw [← map_pow]; rw [Scheme.Modules.restrictAppIso_smul_Spec]; rw [M.map_smul_Spec]; rw [Iso.inv_hom_id_apply] at this
    simpa using this

中文:
引理 aux_basicOpen_of_aux_restrict
  结论: (M : (Spec R).Modules) (g : R)
  证明: by
  let a : R ⟶ CommRingCat.of (Localization.Away g) :=
CommRingCat.ofHom algebraMap R _
  set ψ : Spec (.of <| Localization.Away g) ⟶ Spec (.of R) := Spec.map a
  set M' : (Spec (.of <| Localization.Away g)).Modules := M.restrict ψ
  have heq (f : R) (hf : basicOpen f <= basicOpen g) :
      basicOpen f = ψ ''ᵁ basicOpen (a f) := by
    rw [← SpecMap_preimage_basicOpen]; rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    simp [a, ψ, hf]
  let iso : Γ(M.restrict ψ, ⊤) ≅ Γ(M, basicOpen g) :=
    M.restrictAppIso _ _ ≪≫ M.presheaf.mapIso (eqToIso <| by simp [ψ, a]).op
  let e (f : R) (hf : basicOpen f <= basicOpen g) : Γ(M', basicOpen (a f)) ≅ Γ(M, basicOpen f) :=
    M.restrictAppIso ψ (basicOpen (a f)) ≪≫ M.presheaf.mapIso (eqToIso <| heq f hf).op
  refine ⟨fun f hf s => ?_, fun f hf t ht => ?_⟩
  · obtain ⟨n, t, ht⟩ := h.existence (a f) le_top ((e _ hf).inv s)
    use n, iso.hom t
    have := congr((e _ hf).hom $ht)
    dsimp [M'] at this
    rw [← ConcreteCategory.comp_apply] at this
    simp only [homOfLE_leOfHom, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      eqToHom_op, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, e, iso] at this ⊢
    simp only [homOfLE_leOfHom, Scheme.Modules.map_restrictAppIso_hom_assoc, AddCommGrpCat.hom_comp,
      AddMonoidHom.coe_comp, Function.comp_apply, ← map_pow, ψ] at this
    rw [Scheme.Modules.restrictAppIso_smul_Spec] at this
    simpa [← Functor.map_comp_apply, eqToHom_comp_homOfLE_op, homOfLE_op_comp_eqToHom] using this
· obtain ⟨n, hn⟩ := h.uniqueness (a f) le_top (iso.inv t) by
      simpa [M', iso, ← M.presheaf.map_comp_apply, homOfLE_op_comp_eqToHom, e] using
        congr((e _ hf).inv $ht)
    use n
    have := congr(iso.hom $hn)
    dsimp [iso, ψ] at this
    rw [eqToHom_op]; rw [map_zero]; rw [← map_pow]; rw [Scheme.Modules.restrictAppIso_smul_Spec]; rw [M.map_smul_Spec]; rw [Iso.inv_hom_id_apply] at this
    simpa using this
-/
private lemma aux_basicOpen_of_aux_restrict (M : (Spec R).Modules) (g : R)
    (h : Aux (M.restrict <|
Spec.map CommRingCat.ofHom algebraMap R Localization.Away g) ⊤) :
      Aux M (basicOpen g) := by
  let a : R ⟶ CommRingCat.of (Localization.Away g) :=
CommRingCat.ofHom algebraMap R _
  set ψ : Spec (.of <| Localization.Away g) ⟶ Spec (.of R) := Spec.map a
  set M' : (Spec (.of <| Localization.Away g)).Modules := M.restrict ψ
  have heq (f : R) (hf : basicOpen f <= basicOpen g) :
      basicOpen f = ψ ''ᵁ basicOpen (a f) := by
    rw [← SpecMap_preimage_basicOpen]; rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    simp [a, ψ, hf]
  let iso : Γ(M.restrict ψ, ⊤) ≅ Γ(M, basicOpen g) :=
    M.restrictAppIso _ _ ≪≫ M.presheaf.mapIso (eqToIso <| by simp [ψ, a]).op
  let e (f : R) (hf : basicOpen f <= basicOpen g) : Γ(M', basicOpen (a f)) ≅ Γ(M, basicOpen f) :=
    M.restrictAppIso ψ (basicOpen (a f)) ≪≫ M.presheaf.mapIso (eqToIso <| heq f hf).op
  refine ⟨fun f hf s => ?_, fun f hf t ht => ?_⟩
  · obtain ⟨n, t, ht⟩ := h.existence (a f) le_top ((e _ hf).inv s)
    use n, iso.hom t
    have := congr((e _ hf).hom $ht)
    dsimp [M'] at this
    rw [← ConcreteCategory.comp_apply] at this
    simp only [homOfLE_leOfHom, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      eqToHom_op, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, e, iso] at this ⊢
    simp only [homOfLE_leOfHom, Scheme.Modules.map_restrictAppIso_hom_assoc, AddCommGrpCat.hom_comp,
      AddMonoidHom.coe_comp, Function.comp_apply, ← map_pow, ψ] at this
    rw [Scheme.Modules.restrictAppIso_smul_Spec] at this
    simpa [← Functor.map_comp_apply, eqToHom_comp_homOfLE_op, homOfLE_op_comp_eqToHom] using this
· obtain ⟨n, hn⟩ := h.uniqueness (a f) le_top (iso.inv t) by
      simpa [M', iso, ← M.presheaf.map_comp_apply, homOfLE_op_comp_eqToHom, e] using
        congr((e _ hf).inv $ht)
    use n
    have := congr(iso.hom $hn)
    dsimp [iso, ψ] at this
    rw [eqToHom_op]; rw [map_zero]; rw [← map_pow]; rw [Scheme.Modules.restrictAppIso_smul_Spec]; rw [M.map_smul_Spec]; rw [Iso.inv_hom_id_apply] at this
    simpa using this

end QuasicoherentTilde

open QuasicoherentTilde in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent` / 实例 `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`

English:
instance Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent
  signature: (M : (Spec R).Modules)
  body: by
  rw [isIso_fromTildeΓ_iff_isLocalizing]; rw [isLocalizing_iff_aux]
  obtain ⟨ι, U, pres, hU, hU'⟩ := M.exists_isOpenCover_presentation
  obtain ⟨s, hs⟩ := hU.exists_finite_of_compactSpace
  choose κ hκ a ha using fun i : s =>
    PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact (U i) (hU' i).isCompact
  refine Aux.of_eq_iSup_basicOpen _ (fun i : Sigma κ => a _ i.2) ?_ ?_
  · rw [IsOpenCover] at hs
    rw [eq_comm]; rw [iSup_sigma]; rw [← hs]
    exact iSup_congr fun i => (ha i).symm
  · intro i
    let t := (Spec R).homOfLE (U := PrimeSpectrum.basicOpen (a _ i.2)) (V := U i.1)
      (by rw [ha]; exact le_iSup_of_le _ le_rfl)
    let iso : restrictFunctor (U i.1).ι ⋙ restrictFunctor ((basicOpenIsoSpecAway _).inv ≫ t) ≅
        restrictFunctor (Spec.map (CommRingCat.ofHom <| algebraMap _ _)) :=
      (restrictFunctorComp _ _).symm ≪≫
        restrictFunctorCongr (by simp [t, basicOpenIsoSpecAway])
let pres := SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso.app M).hom
      presentationRestrict ((basicOpenIsoSpecAway _).inv ≫ t) (pres i.1)
    have : IsIso _ := isIso_fromTildeΓ_of_presentation (M.restrict _) pres
    rw [isIso_fromTildeΓ_iff_isLocalizing]; rw [isLocalizing_iff_aux] at this
    exact aux_basicOpen_of_aux_restrict _ _ this

中文:
实例 概形.Modules.isIso_fromTildeΓ_of_isQuasicoherent
  签名: (M : (Spec R).Modules)
  定义体: by
  rw [isIso_fromTildeΓ_iff_isLocalizing]; rw [isLocalizing_iff_aux]
  obtain ⟨ι, U, pres, hU, hU'⟩ := M.exists_isOpenCover_presentation
  obtain ⟨s, hs⟩ := hU.exists_finite_of_compactSpace
  choose κ hκ a ha using fun i : s =>
    PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact (U i) (hU' i).isCompact
  refine Aux.of_eq_iSup_basicOpen _ (fun i : Sigma κ => a _ i.2) ?_ ?_
  · rw [IsOpenCover] at hs
    rw [eq_comm]; rw [iSup_sigma]; rw [← hs]
    exact iSup_congr fun i => (ha i).symm
  · intro i
    let t := (Spec R).homOfLE (U := PrimeSpectrum.basicOpen (a _ i.2)) (V := U i.1)
      (by rw [ha]; exact le_iSup_of_le _ le_rfl)
    let iso : restrictFunctor (U i.1).ι ⋙ restrictFunctor ((basicOpenIsoSpecAway _).inv ≫ t) ≅
        restrictFunctor (Spec.map (CommRingCat.ofHom <| algebraMap _ _)) :=
      (restrictFunctorComp _ _).symm ≪≫
        restrictFunctorCongr (by simp [t, basicOpenIsoSpecAway])
let pres := SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso.app M).hom
      presentationRestrict ((basicOpenIsoSpecAway _).inv ≫ t) (pres i.1)
    have : IsIso _ := isIso_fromTildeΓ_of_presentation (M.restrict _) pres
    rw [isIso_fromTildeΓ_iff_isLocalizing]; rw [isLocalizing_iff_aux] at this
    exact aux_basicOpen_of_aux_restrict _ _ this

Depends on / 依赖: Aux.of_eq_iSup_basicOpen, IsOpenCover, M.exists_isOpenCover_presentation, PrimeSpectrum, PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact, eq_comm, exists_finite_of_compactSpace, exists_iSup_eq_of_isCompact, exists_isOpenCover_presentation, hU.exists_finite_of_compactSpace, iSup_congr, iSup_sigma, isBasis_basic_opens, isCompact, isLocalizing_iff_aux, of_eq_iSup_basicOpen
-/
instance Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (M : (Spec R).Modules)
    [M.IsQuasicoherent] : IsIso M.fromTildeΓ := by
  rw [isIso_fromTildeΓ_iff_isLocalizing]; rw [isLocalizing_iff_aux]
  obtain ⟨ι, U, pres, hU, hU'⟩ := M.exists_isOpenCover_presentation
  obtain ⟨s, hs⟩ := hU.exists_finite_of_compactSpace
  choose κ hκ a ha using fun i : s =>
    PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact (U i) (hU' i).isCompact
  refine Aux.of_eq_iSup_basicOpen _ (fun i : Sigma κ => a _ i.2) ?_ ?_
  · rw [IsOpenCover] at hs
    rw [eq_comm]; rw [iSup_sigma]; rw [← hs]
    exact iSup_congr fun i => (ha i).symm
  · intro i
    let t := (Spec R).homOfLE (U := PrimeSpectrum.basicOpen (a _ i.2)) (V := U i.1)
      (by rw [ha]; exact le_iSup_of_le _ le_rfl)
    let iso : restrictFunctor (U i.1).ι ⋙ restrictFunctor ((basicOpenIsoSpecAway _).inv ≫ t) ≅
        restrictFunctor (Spec.map (CommRingCat.ofHom <| algebraMap _ _)) :=
      (restrictFunctorComp _ _).symm ≪≫
        restrictFunctorCongr (by simp [t, basicOpenIsoSpecAway])
let pres := SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso.app M).hom
      presentationRestrict ((basicOpenIsoSpecAway _).inv ≫ t) (pres i.1)
    have : IsIso _ := isIso_fromTildeΓ_of_presentation (M.restrict _) pres
    rw [isIso_fromTildeΓ_iff_isLocalizing]; rw [isLocalizing_iff_aux] at this
    exact aux_basicOpen_of_aux_restrict _ _ this

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isQuasicoherent_iff_isIso_fromTildeΓ` / 定理 `isQuasicoherent_iff_isIso_fromTildeΓ`

English:
theorem isQuasicoherent_iff_isIso_fromTildeΓ
  given: (M : (Spec R).Modules)
  proof: by
  refine ⟨fun h => inferInstance, fun h => ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (asIso <| M.fromTildeΓ) inferInstance

中文:
定理 isQuasicoherent_iff_isIso_fromTildeΓ
  条件: (M : (Spec R).Modules)
  证明: by
  refine ⟨fun h => inferInstance, fun h => ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (asIso <| M.fromTildeΓ) inferInstance

Depends on / 依赖: M.fromTilde, SheafOfModules, SheafOfModules.isQuasicoherent, isQuasicoherent, prop_of_iso, ringCatSheaf
-/
theorem isQuasicoherent_iff_isIso_fromTildeΓ (M : (Spec R).Modules) :
    M.IsQuasicoherent ↔ IsIso M.fromTildeΓ := by
  refine ⟨fun h => inferInstance, fun h => ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (asIso <| M.fromTildeΓ) inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `essImage_tilde` / 引理 `essImage_tilde`

English:
lemma essImage_tilde
  statement: (tilde.functor R).essImage =
  proof: by
  refine le_antisymm ?_ ?_
  · intro M ⟨N, ⟨e⟩⟩
    exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e
      (by dsimp; infer_instance)
  · intro M (h : M.IsQuasicoherent)
exact ⟨((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)), ⟨asIso M.fromTildeΓ⟩⟩

中文:
引理 essImage_tilde
  结论: (tilde.functor R).essImage =
  证明: by
  refine le_antisymm ?_ ?_
  · intro M ⟨N, ⟨e⟩⟩
    exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e
      (by dsimp; infer_instance)
  · intro M (h : M.IsQuasicoherent)
exact ⟨((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)), ⟨asIso M.fromTildeΓ⟩⟩

Depends on / 依赖: IsQuasicoherent, M.IsQuasicoherent, M.fromTilde, SheafOfModules, SheafOfModules.isQuasicoherent, infer_instance, isQuasicoherent, le_antisymm, modulesSpecToSheaf, modulesSpecToSheaf.obj, presheaf, presheaf.obj, prop_of_iso, ringCatSheaf
-/
lemma essImage_tilde : (tilde.functor R).essImage =
    SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf := by
  refine le_antisymm ?_ ?_
  · intro M ⟨N, ⟨e⟩⟩
    exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e
      (by dsimp; infer_instance)
  · intro M (h : M.IsQuasicoherent)
exact ⟨((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)), ⟨asIso M.fromTildeΓ⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `M ↦ M^~` is an equivalence of categories from `ModuleCat R` to the full subcategory
of quasi-coherent `𝒪_{Spec R}`-modules. -/
@[simps! functor inverse unitIso counitIso_hom_app_hom]
/--
Definition of `tildeEquiv` / `tildeEquiv` 的定义

English:
definition tildeEquiv
  signature: :
  body: ObjectProperty.lift _ (tilde.functor R) fun _ => by
    dsimp [SheafOfModules.isQuasicoherent]
    infer_instance
  inverse := ObjectProperty.ι _ ⋙ moduleSpecΓFunctor (R := R)
  unitIso := tilde.toTildeΓNatIso
  counitIso :=
    haveI (M : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory) :
      IsIso (Scheme.Modules.fromTildeΓ M.obj) := inferInstance
    NatIso.ofComponents
      (fun M => ObjectProperty.isoMk _ (asIso <| Scheme.Modules.fromTildeΓ M.obj))
      fun f => ObjectProperty.hom_ext _ (tilde.adjunction (R := R).counit.naturality f.hom)
  functor_unitIso_comp M :=
    ObjectProperty.hom_ext _ (tilde.adjunction (R := R).left_triangle_components M)

中文:
定义 tildeEquiv
  签名: :
  定义体: ObjectProperty.lift _ (tilde.functor R) fun _ => by
    dsimp [SheafOfModules.isQuasicoherent]
    infer_instance
  inverse := ObjectProperty.ι _ ⋙ moduleSpecΓFunctor (R := R)
  unitIso := tilde.toTildeΓNatIso
  counitIso :=
    haveI (M : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory) :
      IsIso (Scheme.Modules.fromTildeΓ M.obj) := inferInstance
    NatIso.ofComponents
      (fun M => ObjectProperty.isoMk _ (asIso <| Scheme.Modules.fromTildeΓ M.obj))
      fun f => ObjectProperty.hom_ext _ (tilde.adjunction (R := R).counit.naturality f.hom)
  functor_unitIso_comp M :=
    ObjectProperty.hom_ext _ (tilde.adjunction (R := R).left_triangle_components M)

Depends on / 依赖: FullSubcategory, M.obj, Modules, NatIso, NatIso.ofComponents, ObjectProperty, ObjectProperty.hom_ext, ObjectProperty.isoMk, ObjectProperty.lift, Scheme, Scheme.Modules.fromTilde, SheafOfModules, SheafOfModules.isQuasicoherent, adjunctio, counitIso, functor, hom_ext, infer_instance, inverse, isQuasicoherent
-/
def tildeEquiv :
    ModuleCat R ≌ (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory where
  functor := ObjectProperty.lift _ (tilde.functor R) fun _ => by
    dsimp [SheafOfModules.isQuasicoherent]
    infer_instance
  inverse := ObjectProperty.ι _ ⋙ moduleSpecΓFunctor (R := R)
  unitIso := tilde.toTildeΓNatIso
  counitIso :=
    haveI (M : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory) :
      IsIso (Scheme.Modules.fromTildeΓ M.obj) := inferInstance
    NatIso.ofComponents
      (fun M => ObjectProperty.isoMk _ (asIso <| Scheme.Modules.fromTildeΓ M.obj))
      fun f => ObjectProperty.hom_ext _ (tilde.adjunction (R := R).counit.naturality f.hom)
  functor_unitIso_comp M :=
    ObjectProperty.hom_ext _ (tilde.adjunction (R := R).left_triangle_components M)

end IsQuasicoherent

end AlgebraicGeometry

namespace ModuleCat

@[deprecated (since := "2026-02-11")] noncomputable alias tilde := AlgebraicGeometry.tilde
@[deprecated (since := "2026-02-11")] noncomputable alias Tilde.toOpen := tilde.toOpen
@[deprecated (since := "2026-02-11")] alias Tilde.toOpen_res := tilde.toOpen_res
@[deprecated (since := "2026-02-11")] noncomputable alias Tilde.toStalk := tilde.toStalk

end ModuleCat
