/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic

/-! # Standard Open Immersion

We define the property `RingHom.IsStandardOpenImmersion` on ring homomorphisms: it means that the
morphism is a localization map away from some element. We also define the equivalent
`Algebra.IsStandardOpenImmersion`.
-/

@[expose] public section

universe u

namespace Algebra

open IsLocalization Away

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
  [Algebra R S] [Algebra R T]

/--
Definition of `IsStandardOpenImmersion` / `IsStandardOpenImmersion` 的定义

English:
class IsStandardOpenImmersion
  parameters: (R S : Type*) [CommSemiring R] [CommSemiring S]
  axioms and operations (1):
    - exists_away((R S)) : exists r : R, IsLocalization.Away r S

中文:
类 是StandardOpenImmersion
  参数: (R S : 类型) [交换半环 R] [交换半环 S]
  公理与运算 (1 个):
    - exists_away((R S)) : 存在 r : R, 是Localization.Away r S
-/
@[mk_iff] class IsStandardOpenImmersion (R S : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R S] : Prop where
  exists_away (R S) : exists r : R, IsLocalization.Away r S

namespace IsStandardOpenImmersion

instance (r : R) : IsStandardOpenImmersion R (Localization.Away r) :=
  ⟨r, inferInstance⟩

variable (R S T) in
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  statement: [Algebra S T] [IsScalarTower R S T]
  proof: let ⟨r, _⟩ := exists_away R S
  let ⟨s, _⟩ := exists_away S T
  have : Away (algebraMap R S (sec r s).1) T :=
    .of_associated (associated_sec_fst r s).symm
  ⟨r * (sec r s).1, mul' S T r _⟩

中文:
定理 trans
  结论: [代数 S T] [标量塔 R S T]
  证明: let ⟨r, _⟩ := exists_away R S
  let ⟨s, _⟩ := exists_away S T
  have : Away (algebraMap R S (sec r s).1) T :=
    .of_associated (associated_sec_fst r s).symm
  ⟨r * (sec r s).1, mul' S T r _⟩
-/
@[trans] theorem trans [Algebra S T] [IsScalarTower R S T]
    [IsStandardOpenImmersion R S] [IsStandardOpenImmersion S T] :
    IsStandardOpenImmersion R T :=
  let ⟨r, _⟩ := exists_away R S
  let ⟨s, _⟩ := exists_away S T
  have : Away (algebraMap R S (sec r s).1) T :=
    .of_associated (associated_sec_fst r s).symm
  ⟨r * (sec r s).1, mul' S T r _⟩

open _root_.TensorProduct in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsStandardOpenImmersion
  signature: R T] : IsStandardOpenImmersion S (S otimes[R] T)
  body: let ⟨r, _⟩ := exists_away R T
  ⟨algebraMap R S r, inferInstance⟩

中文:
实例 [是StandardOpenImmersion
  签名: R T] : 是StandardOpenImmersion S (S otimes[R] T)
  定义体: let ⟨r, _⟩ := exists_away R T
  ⟨algebraMap R S r, inferInstance⟩

Depends on / 依赖: algebraMap, exists_away
-/
instance [IsStandardOpenImmersion R T] : IsStandardOpenImmersion S (S otimes[R] T) :=
  let ⟨r, _⟩ := exists_away R T
  ⟨algebraMap R S r, inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStandardOpenImmersion R R
  body: ⟨1, IsLocalization.away_of_isUnit_of_bijective R isUnit_one Function.bijective_id⟩

中文:
实例 :
  签名: 是StandardOpenImmersion R R
  定义体: ⟨1, IsLocalization.away_of_isUnit_of_bijective R isUnit_one Function.bijective_id⟩

Depends on / 依赖: Function, Function.bijective_id, IsLocalization, IsLocalization.away_of_isUnit_of_bijective, away_of_isUnit_of_bijective, bijective_id, isUnit_one
-/
instance : IsStandardOpenImmersion R R :=
  ⟨1, IsLocalization.away_of_isUnit_of_bijective R isUnit_one Function.bijective_id⟩

/--
lemma `of_bijective` / 引理 `of_bijective`

English:
lemma of_bijective
  given: (h : Function.Bijective (algebraMap R S))
  proof: by
  rw [Algebra.isStandardOpenImmersion_iff]
  use 1
  apply IsLocalization.away_of_isUnit_of_bijective _ isUnit_one h

中文:
引理 of_bijective
  条件: (h : 函数.双射 (algebraMap R S))
  证明: by
  rw [Algebra.isStandardOpenImmersion_iff]
  use 1
  apply IsLocalization.away_of_isUnit_of_bijective _ isUnit_one h

Depends on / 依赖: Algebra, Algebra.isStandardOpenImmersion_iff, IsLocalization, IsLocalization.away_of_isUnit_of_bijective, away_of_isUnit_of_bijective, isStandardOpenImmersion_iff, isUnit_one
-/
lemma of_bijective (h : Function.Bijective (algebraMap R S)) :
    IsStandardOpenImmersion R S := by
  rw [Algebra.isStandardOpenImmersion_iff]
  use 1
  apply IsLocalization.away_of_isUnit_of_bijective _ isUnit_one h

/--
lemma `of_algEquiv` / 引理 `of_algEquiv`

English:
lemma of_algEquiv
  statement: {T : Type*} [CommSemiring T] [Algebra R T] (e : S ≃ₐ[R] T)
  proof: by
  rw [Algebra.isStandardOpenImmersion_iff] at *
  obtain ⟨r, hr⟩ := h
  use r
  exact IsLocalization.isLocalization_of_algEquiv _ e

中文:
引理 of_algEquiv
  结论: {T : 类型} [交换半环 T] [代数 R T] (e : S ≃ₐ[R] T)
  证明: by
  rw [Algebra.isStandardOpenImmersion_iff] at *
  obtain ⟨r, hr⟩ := h
  use r
  exact IsLocalization.isLocalization_of_algEquiv _ e

Depends on / 依赖: Algebra, Algebra.isStandardOpenImmersion_iff, IsLocalization, IsLocalization.isLocalization_of_algEquiv, isLocalization_of_algEquiv, isStandardOpenImmersion_iff
-/
lemma of_algEquiv {T : Type*} [CommSemiring T] [Algebra R T] (e : S ≃ₐ[R] T)
    [h : IsStandardOpenImmersion R S] :
    IsStandardOpenImmersion R T := by
  rw [Algebra.isStandardOpenImmersion_iff] at *
  obtain ⟨r, hr⟩ := h
  use r
  exact IsLocalization.isLocalization_of_algEquiv _ e

/--
lemma `iff_of_algEquiv` / 引理 `iff_of_algEquiv`

English:
lemma iff_of_algEquiv
  statement: {T : Type*} [CommSemiring T] [Algebra R T]
  proof: ⟨fun _ => .of_algEquiv e, fun _ => .of_algEquiv e.symm⟩

中文:
引理 iff_of_algEquiv
  结论: {T : 类型} [交换半环 T] [代数 R T]
  证明: ⟨fun _ => .of_algEquiv e, fun _ => .of_algEquiv e.symm⟩

Depends on / 依赖: e.symm, of_algEquiv
-/
lemma iff_of_algEquiv {T : Type*} [CommSemiring T] [Algebra R T]
    (e : S ≃ₐ[R] T) :
    IsStandardOpenImmersion R S ↔ IsStandardOpenImmersion R T :=
  ⟨fun _ => .of_algEquiv e, fun _ => .of_algEquiv e.symm⟩

variable (R S) in
/--
lemma `of_isPushout` / 引理 `of_isPushout`

English:
lemma of_isPushout
  statement: (R' S' : Type*) [CommSemiring R'] [CommSemiring S']
  proof: have : IsPushout R R' S S' := by rwa [IsPushout.comm]
  .of_algEquiv (IsPushout.equiv R _ S _)

中文:
引理 of_isPushout
  结论: (R' S' : 类型) [交换半环 R'] [交换半环 S']
  证明: have : IsPushout R R' S S' := by rwa [IsPushout.comm]
  .of_algEquiv (IsPushout.equiv R _ S _)

Depends on / 依赖: IsPushout, IsPushout.comm, IsPushout.equiv, of_algEquiv
-/
lemma of_isPushout (R' S' : Type*) [CommSemiring R'] [CommSemiring S']
    [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S']
    [IsScalarTower R S S'] [IsPushout R S R' S'] [IsStandardOpenImmersion R S] :
    IsStandardOpenImmersion R' S' :=
  have : IsPushout R R' S S' := by rwa [IsPushout.comm]
  .of_algEquiv (IsPushout.equiv R _ S _)

end Algebra.IsStandardOpenImmersion

namespace RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R ->+* S) (g : S ->+* T)

/-- A standard open immersion is one that is a localization map away from some element. -/
@[algebraize RingHom.IsStandardOpenImmersion.toAlgebra]
/--
Definition of `IsStandardOpenImmersion` / `IsStandardOpenImmersion` 的定义

English:
definition IsStandardOpenImmersion
  signature: : Prop
  body: letI := f.toAlgebra
  Algebra.IsStandardOpenImmersion R S

中文:
定义 是StandardOpenImmersion
  签名: : 命题
  定义体: letI := f.toAlgebra
  Algebra.IsStandardOpenImmersion R S

Depends on / 依赖: Algebra, Algebra.IsStandardOpenImmersion, IsStandardOpenImmersion, f.toAlgebra, toAlgebra
-/
def IsStandardOpenImmersion : Prop :=
  letI := f.toAlgebra
  Algebra.IsStandardOpenImmersion R S

/--
lemma `isStandardOpenImmersion_algebraMap` / 引理 `isStandardOpenImmersion_algebraMap`

English:
lemma isStandardOpenImmersion_algebraMap
  given: [Algebra R S]
  proof: by
  rw [IsStandardOpenImmersion]; rw [toAlgebra_algebraMap]

中文:
引理 isStandardOpenImmersion_algebraMap
  条件: [代数 R S]
  证明: by
  rw [IsStandardOpenImmersion]; rw [toAlgebra_algebraMap]

Depends on / 依赖: IsStandardOpenImmersion, toAlgebra_algebraMap
-/
lemma isStandardOpenImmersion_algebraMap [Algebra R S] :
    (algebraMap R S).IsStandardOpenImmersion ↔ Algebra.IsStandardOpenImmersion R S := by
  rw [IsStandardOpenImmersion]; rw [toAlgebra_algebraMap]

namespace IsStandardOpenImmersion

/--
lemma `algebraMap` / 引理 `algebraMap`

English:
lemma algebraMap
  given: [Algebra R S] (r : R) [IsLocalization.Away r S]
  proof: isStandardOpenImmersion_algebraMap.2 ⟨r, inferInstance⟩

中文:
引理 algebraMap
  条件: [代数 R S] (r : R) [是Localization.Away r S]
  证明: isStandardOpenImmersion_algebraMap.2 ⟨r, inferInstance⟩
-/
protected lemma algebraMap [Algebra R S] (r : R) [IsLocalization.Away r S] :
    (algebraMap R S).IsStandardOpenImmersion :=
  isStandardOpenImmersion_algebraMap.2 ⟨r, inferInstance⟩

/--
lemma `toAlgebra` / 引理 `toAlgebra`

English:
lemma toAlgebra
  given: {f : R ->+* S} (hf : f.IsStandardOpenImmersion)
  proof: letI := f.toAlgebra; hf

中文:
引理 toAlgebra
  条件: {f : R ->+* S} (hf : f.是StandardOpenImmersion)
  证明: letI := f.toAlgebra; hf

Depends on / 依赖: f.toAlgebra, toAlgebra
-/
lemma toAlgebra {f : R ->+* S} (hf : f.IsStandardOpenImmersion) :
    @Algebra.IsStandardOpenImmersion R S _ _ f.toAlgebra :=
  letI := f.toAlgebra; hf

/--
lemma `of_bijective` / 引理 `of_bijective`

English:
lemma of_bijective
  given: {f : R ->+* S} (hf : Function.Bijective f)
  statement: f.IsStandardOpenImmersion
  proof: letI := f.toAlgebra
  ⟨1, IsLocalization.away_of_isUnit_of_bijective _ isUnit_one hf⟩

中文:
引理 of_bijective
  条件: {f : R ->+* S} (hf : 函数.双射 f)
  结论: f.是StandardOpenImmersion
  证明: letI := f.toAlgebra
  ⟨1, IsLocalization.away_of_isUnit_of_bijective _ isUnit_one hf⟩

Depends on / 依赖: IsLocalization, IsLocalization.away_of_isUnit_of_bijective, away_of_isUnit_of_bijective, f.toAlgebra, isUnit_one, toAlgebra
-/
lemma of_bijective {f : R ->+* S} (hf : Function.Bijective f) : f.IsStandardOpenImmersion :=
  letI := f.toAlgebra
  ⟨1, IsLocalization.away_of_isUnit_of_bijective _ isUnit_one hf⟩

variable (R) in
/--
lemma `id` / 引理 `id`

English:
lemma id
  statement: (RingHom.id R).IsStandardOpenImmersion
  proof: of_bijective Function.bijective_id

中文:
引理 id
  结论: (环态射.id R).是StandardOpenImmersion
  证明: of_bijective Function.bijective_id

Depends on / 依赖: Function, Function.bijective_id, bijective_id, of_bijective
-/
lemma id : (RingHom.id R).IsStandardOpenImmersion :=
  of_bijective Function.bijective_id

variable {f g} in
/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  given: (hf : f.IsStandardOpenImmersion) (hg : g.IsStandardOpenImmersion)
  proof: by
  algebraize [f, g, g.comp f]
  obtain ⟨r, hr⟩ := hf
  obtain ⟨s, hs⟩ := hg
  exact .trans _ S _

中文:
引理 comp
  条件: (hf : f.是StandardOpenImmersion) (hg : g.是StandardOpenImmersion)
  证明: by
  algebraize [f, g, g.comp f]
  obtain ⟨r, hr⟩ := hf
  obtain ⟨s, hs⟩ := hg
  exact .trans _ S _

Depends on / 依赖: algebraize, g.comp
-/
lemma comp (hf : f.IsStandardOpenImmersion) (hg : g.IsStandardOpenImmersion) :
    (g.comp f).IsStandardOpenImmersion := by
  algebraize [f, g, g.comp f]
  obtain ⟨r, hr⟩ := hf
  obtain ⟨s, hs⟩ := hg
  exact .trans _ S _

/--
theorem `containsIdentities` / 定理 `containsIdentities`

English:
theorem containsIdentities
  statement: ContainsIdentities.{u} IsStandardOpenImmersion
  proof: id

中文:
定理 containsIdentities
  结论: 余ntainsIdentities.{u} 是StandardOpenImmersion
  证明: id
-/
theorem containsIdentities : ContainsIdentities.{u} IsStandardOpenImmersion := id

/--
theorem `stableUnderComposition` / 定理 `stableUnderComposition`

English:
theorem stableUnderComposition
  statement: StableUnderComposition.{u} IsStandardOpenImmersion
  proof: @comp

中文:
定理 stableUnderComposition
  结论: StableUnderComposition.{u} 是StandardOpenImmersion
  证明: @comp
-/
theorem stableUnderComposition : StableUnderComposition.{u} IsStandardOpenImmersion := @comp

/--
theorem `respectsIso` / 定理 `respectsIso`

English:
theorem respectsIso
  statement: RespectsIso.{u} IsStandardOpenImmersion
  proof: stableUnderComposition.respectsIso fun e => of_bijective e.bijective

中文:
定理 respectsIso
  结论: RespectsIso.{u} 是StandardOpenImmersion
  证明: stableUnderComposition.respectsIso fun e => of_bijective e.bijective

Depends on / 依赖: bijective, e.bijective, of_bijective, respectsIso, stableUnderComposition, stableUnderComposition.respectsIso
-/
theorem respectsIso : RespectsIso.{u} IsStandardOpenImmersion :=
  stableUnderComposition.respectsIso fun e => of_bijective e.bijective

/--
theorem `isStableUnderBaseChange` / 定理 `isStableUnderBaseChange`

English:
theorem isStableUnderBaseChange
  statement: IsStableUnderBaseChange.{u} IsStandardOpenImmersion
  proof: by
  refine .mk respectsIso ?_
  introv h
  rw [isStandardOpenImmersion_algebraMap] at h ⊢
  infer_instance

中文:
定理 isStableUnderBaseChange
  结论: 是StableUnderBaseChange.{u} 是StandardOpenImmersion
  证明: by
  refine .mk respectsIso ?_
  introv h
  rw [isStandardOpenImmersion_algebraMap] at h ⊢
  infer_instance

Depends on / 依赖: infer_instance, introv, isStandardOpenImmersion_algebraMap, respectsIso
-/
theorem isStableUnderBaseChange : IsStableUnderBaseChange.{u} IsStandardOpenImmersion := by
  refine .mk respectsIso ?_
  introv h
  rw [isStandardOpenImmersion_algebraMap] at h ⊢
  infer_instance

/--
theorem `holdsForLocalizationAway` / 定理 `holdsForLocalizationAway`

English:
theorem holdsForLocalizationAway
  statement: HoldsForLocalizationAway.{u} IsStandardOpenImmersion
  proof: by
  introv R h
  exact .algebraMap r

中文:
定理 holdsForLocalizationAway
  结论: HoldsForLocalizationAway.{u} 是StandardOpenImmersion
  证明: by
  introv R h
  exact .algebraMap r

Depends on / 依赖: algebraMap, introv
-/
theorem holdsForLocalizationAway : HoldsForLocalizationAway.{u} IsStandardOpenImmersion := by
  introv R h
  exact .algebraMap r

end IsStandardOpenImmersion

end RingHom
