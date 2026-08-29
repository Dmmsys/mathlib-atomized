/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Ring-theoretic results in terms of categorical language
-/

public section

universe u

open CategoryTheory

/--
Instance `localization_unit_isIso` / 实例 `localization_unit_isIso`

English:
instance localization_unit_isIso
  signature: (R : CommRingCat)
  body: Iso.isIso_hom (IsLocalization.atOne R (Localization.Away (1 : R))).toRingEquiv.toCommRingCatIso

中文:
实例 localization_unit_isIso
  签名: (R : 交换环范畴)
  定义体: Iso.isIso_hom (IsLocalization.atOne R (Localization.Away (1 : R))).toRingEquiv.toCommRingCatIso

Depends on / 依赖: IsLocalization, IsLocalization.atOne, Iso.isIso_hom, Localization, Localization.Away, isIso_hom, toCommRingCatIso, toRingEquiv, toRingEquiv.toCommRingCatIso
-/
instance localization_unit_isIso (R : CommRingCat) :
    IsIso (CommRingCat.ofHom <| algebraMap R (Localization.Away (1 : R))) :=
  Iso.isIso_hom (IsLocalization.atOne R (Localization.Away (1 : R))).toRingEquiv.toCommRingCatIso

/--
Instance `localization_unit_isIso'` / 实例 `localization_unit_isIso'`

English:
instance localization_unit_isIso'
  signature: (R : CommRingCat)
  body: by
  cases R
  exact localization_unit_isIso _

中文:
实例 localization_unit_isIso'
  签名: (R : 交换环范畴)
  定义体: by
  cases R
  exact localization_unit_isIso _

Depends on / 依赖: localization_unit_isIso
-/
instance localization_unit_isIso' (R : CommRingCat) :
    @IsIso CommRingCat _ R _ (CommRingCat.ofHom <| algebraMap R (Localization.Away (1 : R))) := by
  cases R
  exact localization_unit_isIso _

/--
theorem `IsLocalization.epi` / 定理 `IsLocalization.epi`

English:
theorem IsLocalization.epi
  statement: {R : Type*} [CommRing R] (M : Submonoid R) (S : Type _) [CommRing S]
  proof: ⟨fun _ _ h => CommRingCat.hom_ext ringHom_ext M congr(($h).hom)⟩

中文:
定理 是Localization.epi
  结论: {R : 类型} [交换环 R] (M : 子幺半群 R) (S : 类型 _) [交换环 S]
  证明: ⟨fun _ _ h => CommRingCat.hom_ext ringHom_ext M congr(($h).hom)⟩

Depends on / 依赖: CommRingCat, CommRingCat.hom_ext, hom_ext, ringHom_ext
-/
theorem IsLocalization.epi {R : Type*} [CommRing R] (M : Submonoid R) (S : Type _) [CommRing S]
    [Algebra R S] [IsLocalization M S] : Epi (CommRingCat.ofHom <| algebraMap R S) :=
⟨fun _ _ h => CommRingCat.hom_ext ringHom_ext M congr(($h).hom)⟩

/--
Instance `Localization.epi` / 实例 `Localization.epi`

English:
instance Localization.epi
  signature: {R : Type*} [CommRing R] (M : Submonoid R)
  body: IsLocalization.epi M _

中文:
实例 Localization.epi
  签名: {R : 类型} [交换环 R] (M : 子幺半群 R)
  定义体: IsLocalization.epi M _

Depends on / 依赖: IsLocalization, IsLocalization.epi
-/
instance Localization.epi {R : Type*} [CommRing R] (M : Submonoid R) :
    Epi (CommRingCat.ofHom <| algebraMap R <| Localization M) :=
  IsLocalization.epi M _

/--
Instance `Localization.epi'` / 实例 `Localization.epi'`

English:
instance Localization.epi'
  signature: {R : CommRingCat} (M : Submonoid R)
  body: by
  rcases R with ⟨α, str⟩
  exact IsLocalization.epi M _

@[instance]

中文:
实例 Localization.epi'
  签名: {R : 交换环范畴} (M : 子幺半群 R)
  定义体: by
  rcases R with ⟨α, str⟩
  exact IsLocalization.epi M _

@[instance]

Depends on / 依赖: IsLocalization, IsLocalization.epi
-/
instance Localization.epi' {R : CommRingCat} (M : Submonoid R) :
    @Epi CommRingCat _ R _ (CommRingCat.ofHom <| algebraMap R <| Localization M :) := by
  rcases R with ⟨α, str⟩
  exact IsLocalization.epi M _

@[instance]
/--
theorem `CommRingCat.isLocalHom_comp` / 定理 `CommRingCat.isLocalHom_comp`

English:
theorem CommRingCat.isLocalHom_comp
  statement: {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T)
  proof: RingHom.isLocalHom_comp _ _

中文:
定理 交换环范畴.isLocalHom_comp
  结论: {R S T : 交换环范畴} (f : R ⟶ S) (g : S ⟶ T)
  证明: RingHom.isLocalHom_comp _ _

Depends on / 依赖: RingHom, RingHom.isLocalHom_comp, isLocalHom_comp
-/
theorem CommRingCat.isLocalHom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T)
    [IsLocalHom g.hom] [IsLocalHom f.hom] : IsLocalHom (f ≫ g).hom :=
  RingHom.isLocalHom_comp _ _

/--
theorem `isLocalHom_of_iso` / 定理 `isLocalHom_of_iso`

English:
theorem isLocalHom_of_iso
  given: {R S : CommRingCat} (f : R ≅ S)
  statement: IsLocalHom f.hom.hom
  proof: { map_nonunit := fun a ha => by
      convert! f.inv.hom.isUnit_map ha
      simp }

中文:
定理 isLocalHom_of_iso
  条件: {R S : 交换环范畴} (f : R ≅ S)
  结论: 是Local态射 f.hom.hom
  证明: { map_nonunit := fun a ha => by
      convert! f.inv.hom.isUnit_map ha
      simp }

Depends on / 依赖: convert, f.inv.hom.isUnit_map, isUnit_map, map_nonunit
-/
theorem isLocalHom_of_iso {R S : CommRingCat} (f : R ≅ S) : IsLocalHom f.hom.hom :=
  { map_nonunit := fun a ha => by
      convert! f.inv.hom.isUnit_map ha
      simp }

-- see Note [lower instance priority]
@[instance 100]
/--
theorem `isLocalHom_of_isIso` / 定理 `isLocalHom_of_isIso`

English:
theorem isLocalHom_of_isIso
  given: {R S : CommRingCat} (f : R ⟶ S) [IsIso f]
  proof: isLocalHom_of_iso (asIso f)

中文:
定理 isLocalHom_of_isIso
  条件: {R S : 交换环范畴} (f : R ⟶ S) [是同构 f]
  证明: isLocalHom_of_iso (asIso f)

Depends on / 依赖: isLocalHom_of_iso
-/
theorem isLocalHom_of_isIso {R S : CommRingCat} (f : R ⟶ S) [IsIso f] :
    IsLocalHom f.hom :=
  isLocalHom_of_iso (asIso f)
