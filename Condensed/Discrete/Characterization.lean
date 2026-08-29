/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Discrete.Colimit
public import Mathlib.Condensed.Discrete.Module
/-!

# Characterizing discrete condensed sets and `R`-modules.

This file proves a characterization of discrete condensed sets, discrete condensed `R`-modules over
a ring `R`, discrete light condensed sets, and discrete light condensed `R`-modules over a ring `R`.
see `CondensedSet.isDiscrete_tfae`, `CondensedMod.isDiscrete_tfae`, `LightCondSet.isDiscrete_tfae`,
and `LightCondMod.isDiscrete_tfae`.

Informally, we can say: The following conditions characterize a condensed set `X` as discrete
(`CondensedSet.isDiscrete_tfae`):

1. There exists a set `X'` and an isomorphism `X ≅ cst X'`, where `cst X'` denotes the constant
   sheaf on `X'`.
2. The counit induces an isomorphism `cst X(*) ⟶ X`.
3. There exists a set `X'` and an isomorphism `X ≅ LocallyConstant · X'`.
4. The counit induces an isomorphism `LocallyConstant · X(*) ⟶ X`.
5. For every profinite set `S = limᵢSᵢ`, the canonical map `colimᵢX(Sᵢ) ⟶ X(S)` is an isomorphism.

The analogues for light condensed sets, condensed `R`-modules over any ring, and light
condensed `R`-modules are nearly identical (`CondensedMod.isDiscrete_tfae`,
`LightCondSet.isDiscrete_tfae`, and `LightCondMod.isDiscrete_tfae`).
-/

public section

universe u

open CategoryTheory Limits Functor FintypeCat

namespace Condensed

variable {C : Type*} [Category* C] [HasWeakSheafify (coherentTopology CompHaus.{u}) C]

/--
Definition of `IsDiscrete` / `IsDiscrete` 的定义

English:
abbreviation IsDiscrete
  signature: (X : Condensed.{u} C)
  body: X.IsConstant (coherentTopology CompHaus)

中文:
缩写 是离散
  签名: (X : Condensed.{u} C)
  定义体: X.IsConstant (coherentTopology CompHaus)

Depends on / 依赖: CompHaus, IsConstant, X.IsConstant, coherentTopology
-/
abbrev IsDiscrete (X : Condensed.{u} C) := X.IsConstant (coherentTopology CompHaus)

end Condensed

namespace CondensedSet

open CompHausLike.LocallyConstant

/--
lemma `mem_locallyConstant_essImage_of_isColimit_mapCocone` / 引理 `mem_locallyConstant_essImage_of_isColimit_mapCocone`

English:
lemma mem_locallyConstant_essImage_of_isColimit_mapCocone
  statement: (X : CondensedSet.{u})
  proof: by
  let e : CondensedSet.{u} ≌ Sheaf (coherentTopology Profinite) _ :=
    (Condensed.ProfiniteCompHaus.equivalence (Type (u + 1))).symm
  let i : (e.functor.obj X).obj ≅ (e.functor.obj (LocallyConstant.functor.obj _)).obj :=
    Condensed.isoLocallyConstantOfIsColimit _ h
  exact ⟨_, ⟨e.functor.preimageIso ((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

中文:
引理 mem_locallyConstant_essImage_of_isColimit_mapCocone
  结论: (X : CondensedSet.{u})
  证明: by
  let e : CondensedSet.{u} ≌ Sheaf (coherentTopology Profinite) _ :=
    (Condensed.ProfiniteCompHaus.equivalence (Type (u + 1))).symm
  let i : (e.functor.obj X).obj ≅ (e.functor.obj (LocallyConstant.functor.obj _)).obj :=
    Condensed.isoLocallyConstantOfIsColimit _ h
  exact ⟨_, ⟨e.functor.preimageIso ((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

Depends on / 依赖: Condensed, Condensed.ProfiniteCompHaus.equivalence, Condensed.isoLocallyConstantOfIsColimit, CondensedSet, LocallyConstant, LocallyConstant.functor.obj, Profinite, ProfiniteCompHaus, coherentTopology, e.functor.obj, e.functor.preimageIso, equivalence, functor, i.symm, isoLocallyConstantOfIsColimit, preimageIso, sheafToPresheaf
-/
lemma mem_locallyConstant_essImage_of_isColimit_mapCocone (X : CondensedSet.{u})
    (h : forall S : Profinite.{u}, IsColimit <|
      (profiniteToCompHaus.op ⋙ X.obj).mapCocone S.asLimitCone.op) :
    CondensedSet.LocallyConstant.functor.essImage X := by
  let e : CondensedSet.{u} ≌ Sheaf (coherentTopology Profinite) _ :=
    (Condensed.ProfiniteCompHaus.equivalence (Type (u + 1))).symm
  let i : (e.functor.obj X).obj ≅ (e.functor.obj (LocallyConstant.functor.obj _)).obj :=
    Condensed.isoLocallyConstantOfIsColimit _ h
  exact ⟨_, ⟨e.functor.preimageIso ((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

/--
Definition of `LocallyConstant.adjunction` / `LocallyConstant.adjunction` 的定义

English:
abbreviation LocallyConstant.adjunction
  signature: :
  body: CompHausLike.LocallyConstant.adjunction _ _

中文:
缩写 局部常数.adjunction
  签名: :
  定义体: CompHausLike.LocallyConstant.adjunction _ _

Depends on / 依赖: CompHausLike, CompHausLike.LocallyConstant.adjunction, LocallyConstant, adjunction
-/
noncomputable abbrev LocallyConstant.adjunction :
    CondensedSet.LocallyConstant.functor ⊣ Condensed.underlying (Type (u + 1)) :=
  CompHausLike.LocallyConstant.adjunction _ _

open Condensed

open CondensedSet.LocallyConstant List in
/--
theorem `isDiscrete_tfae` / 定理 `isDiscrete_tfae`

English:
theorem isDiscrete_tfae
  given: (X : CondensedSet.{u})
  proof: by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ CompHaus.isTerminalPUnit adjunction _
  tfae_have 1 ↔ 5 :=
    have : functor.Faithful := inferInstance
    have : functor.Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ CompHaus.isTerminalPUnit adjunction _
  tfae_have 1 ↔ 6 :=
    (Sheaf.isConstant_iff_of_equivalence (coherentTopology Profinite)
      (coherentTopology CompHaus) profiniteToCompHaus Profinite.isTerminalPUnit
      CompHaus.isTerminalPUnit _).symm
  tfae_have 7 -> 4 := fun h =>
    mem_locallyConstant_essImage_of_isColimit_mapCocone X (fun S => (h S).some)
  tfae_have 4 -> 7 := fun ⟨Y, ⟨i⟩⟩ S =>
    ⟨IsColimit.mapCoconeEquiv (isoWhiskerLeft profiniteToCompHaus.op
      ((sheafToPresheaf _ _).mapIso i))
      (Condensed.isColimitLocallyConstantPresheafDiagram Y S)⟩
  tfae_finish

中文:
定理 isDiscrete_tfae
  条件: (X : CondensedSet.{u})
  证明: by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ CompHaus.isTerminalPUnit adjunction _
  tfae_have 1 ↔ 5 :=
    have : functor.Faithful := inferInstance
    have : functor.Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ CompHaus.isTerminalPUnit adjunction _
  tfae_have 1 ↔ 6 :=
    (Sheaf.isConstant_iff_of_equivalence (coherentTopology Profinite)
      (coherentTopology CompHaus) profiniteToCompHaus Profinite.isTerminalPUnit
      CompHaus.isTerminalPUnit _).symm
  tfae_have 7 -> 4 := fun h =>
    mem_locallyConstant_essImage_of_isColimit_mapCocone X (fun S => (h S).some)
  tfae_have 4 -> 7 := fun ⟨Y, ⟨i⟩⟩ S =>
    ⟨IsColimit.mapCoconeEquiv (isoWhiskerLeft profiniteToCompHaus.op
      ((sheafToPresheaf _ _).mapIso i))
      (Condensed.isColimitLocallyConstantPresheafDiagram Y S)⟩
  tfae_finish

Depends on / 依赖: CompHaus, CompHaus.isTerminalPUnit, Faithful, Sheaf.isConstant_iff_isIso_counit_app, Sheaf.isConstant_iff_mem_essImage, adjunction, functor, functor.Faithful, functor.Full, isConstant_iff_isIso_counit_app, isConstant_iff_mem_essImage, isTerminalPUnit, tfae_have
-/
theorem isDiscrete_tfae (X : CondensedSet.{u}) :
    TFAE
    [ X.IsDiscrete
    , IsIso ((Condensed.discreteUnderlyingAdj _).counit.app X)
    , (Condensed.discrete _).essImage X
    , CondensedSet.LocallyConstant.functor.essImage X
    , IsIso (CondensedSet.LocallyConstant.adjunction.counit.app X)
    , Sheaf.IsConstant (coherentTopology Profinite)
        ((Condensed.ProfiniteCompHaus.equivalence _).inverse.obj X)
    , forall S : Profinite.{u}, Nonempty
        (IsColimit <| (profiniteToCompHaus.op ⋙ X.obj).mapCocone S.asLimitCone.op)
    ] := by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ CompHaus.isTerminalPUnit adjunction _
  tfae_have 1 ↔ 5 :=
    have : functor.Faithful := inferInstance
    have : functor.Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ CompHaus.isTerminalPUnit adjunction _
  tfae_have 1 ↔ 6 :=
    (Sheaf.isConstant_iff_of_equivalence (coherentTopology Profinite)
      (coherentTopology CompHaus) profiniteToCompHaus Profinite.isTerminalPUnit
      CompHaus.isTerminalPUnit _).symm
  tfae_have 7 -> 4 := fun h =>
    mem_locallyConstant_essImage_of_isColimit_mapCocone X (fun S => (h S).some)
  tfae_have 4 -> 7 := fun ⟨Y, ⟨i⟩⟩ S =>
    ⟨IsColimit.mapCoconeEquiv (isoWhiskerLeft profiniteToCompHaus.op
      ((sheafToPresheaf _ _).mapIso i))
      (Condensed.isColimitLocallyConstantPresheafDiagram Y S)⟩
  tfae_finish

end CondensedSet

namespace CondensedMod

variable (R : Type (u + 1)) [Ring R]

/--
lemma `isDiscrete_iff_isDiscrete_forget` / 引理 `isDiscrete_iff_isDiscrete_forget`

English:
lemma isDiscrete_iff_isDiscrete_forget
  given: (M : CondensedMod R)
  proof: Sheaf.isConstant_iff_forget (coherentTopology CompHaus)
    (forget (ModuleCat R)) M CompHaus.isTerminalPUnit

中文:
引理 isDiscrete_iff_isDiscrete_forget
  条件: (M : CondensedMod R)
  证明: Sheaf.isConstant_iff_forget (coherentTopology CompHaus)
    (forget (ModuleCat R)) M CompHaus.isTerminalPUnit

Depends on / 依赖: CompHaus, CompHaus.isTerminalPUnit, ModuleCat, Sheaf.isConstant_iff_forget, coherentTopology, forget, isConstant_iff_forget, isTerminalPUnit
-/
lemma isDiscrete_iff_isDiscrete_forget (M : CondensedMod R) :
    M.IsDiscrete ↔ ((Condensed.forget R).obj M).IsDiscrete :=
  Sheaf.isConstant_iff_forget (coherentTopology CompHaus)
    (forget (ModuleCat R)) M CompHaus.isTerminalPUnit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R)
  body: hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _

中文:
实例 :
  签名: 有LimitsOfSize.{u, u + 1} (模范畴.{u + 1} R)
  定义体: hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _

Depends on / 依赖: hasLimitsOfSizeShrink
-/
instance : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R) :=
  hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _

open CondensedMod.LocallyConstant List in
/--
theorem `isDiscrete_tfae` / 定理 `isDiscrete_tfae`

English:
theorem isDiscrete_tfae
  given: (M : CondensedMod.{u} R)
  proof: by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ CompHaus.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 5 :=
    have : (functor R).Faithful := inferInstance
    have : (functor R).Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ CompHaus.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 6 :=
    (Sheaf.isConstant_iff_of_equivalence (coherentTopology Profinite)
      (coherentTopology CompHaus) profiniteToCompHaus Profinite.isTerminalPUnit
      CompHaus.isTerminalPUnit _).symm
  tfae_have 7 -> 1 := by
    intro h
    rw [isDiscrete_iff_isDiscrete_forget]; rw [((CondensedSet.isDiscrete_tfae _).out 0 6 :)]
    intro S
    let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat R)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ⟨isColimitOfPreserves (forget (ModuleCat R)) (h S).some⟩
  tfae_have 1 -> 7 := by
    intro h S
    rw [isDiscrete_iff_isDiscrete_forget]; rw [((CondensedSet.isDiscrete_tfae _).out 0 6 :)] at h
    let : ReflectsFilteredColimitsOfSize.{u, u} (forget (ModuleCat R)) :=
      reflectsFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ⟨isColimitOfReflects (forget (ModuleCat R)) (h S).some⟩
  tfae_finish

中文:
定理 isDiscrete_tfae
  条件: (M : CondensedMod.{u} R)
  证明: by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ CompHaus.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 5 :=
    have : (functor R).Faithful := inferInstance
    have : (functor R).Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ CompHaus.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 6 :=
    (Sheaf.isConstant_iff_of_equivalence (coherentTopology Profinite)
      (coherentTopology CompHaus) profiniteToCompHaus Profinite.isTerminalPUnit
      CompHaus.isTerminalPUnit _).symm
  tfae_have 7 -> 1 := by
    intro h
    rw [isDiscrete_iff_isDiscrete_forget]; rw [((CondensedSet.isDiscrete_tfae _).out 0 6 :)]
    intro S
    let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat R)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ⟨isColimitOfPreserves (forget (ModuleCat R)) (h S).some⟩
  tfae_have 1 -> 7 := by
    intro h S
    rw [isDiscrete_iff_isDiscrete_forget]; rw [((CondensedSet.isDiscrete_tfae _).out 0 6 :)] at h
    let : ReflectsFilteredColimitsOfSize.{u, u} (forget (ModuleCat R)) :=
      reflectsFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ⟨isColimitOfReflects (forget (ModuleCat R)) (h S).some⟩
  tfae_finish

Depends on / 依赖: CompHaus, CompHaus.isTerminalPUnit, Faithful, Sheaf.isConstant_iff_isIso_counit_app, Sheaf.isConstant_iff_mem_essImage, adjunction, functor, isConstant_iff_isIso_counit_app, isConstant_iff_mem_essImage, isTerminalPUnit, tfae_have
-/
theorem isDiscrete_tfae (M : CondensedMod.{u} R) :
    TFAE
    [ M.IsDiscrete
    , IsIso ((Condensed.discreteUnderlyingAdj _).counit.app M)
    , (Condensed.discrete _).essImage M
    , (CondensedMod.LocallyConstant.functor R).essImage M
    , IsIso ((CondensedMod.LocallyConstant.adjunction R).counit.app M)
    , Sheaf.IsConstant (coherentTopology Profinite)
        ((Condensed.ProfiniteCompHaus.equivalence _).inverse.obj M)
    , forall S : Profinite.{u}, Nonempty
        (IsColimit <| (profiniteToCompHaus.op ⋙ M.obj).mapCocone S.asLimitCone.op)
    ] := by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ CompHaus.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 5 :=
    have : (functor R).Faithful := inferInstance
    have : (functor R).Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ CompHaus.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 6 :=
    (Sheaf.isConstant_iff_of_equivalence (coherentTopology Profinite)
      (coherentTopology CompHaus) profiniteToCompHaus Profinite.isTerminalPUnit
      CompHaus.isTerminalPUnit _).symm
  tfae_have 7 -> 1 := by
    intro h
    rw [isDiscrete_iff_isDiscrete_forget]; rw [((CondensedSet.isDiscrete_tfae _).out 0 6 :)]
    intro S
    let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat R)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ⟨isColimitOfPreserves (forget (ModuleCat R)) (h S).some⟩
  tfae_have 1 -> 7 := by
    intro h S
    rw [isDiscrete_iff_isDiscrete_forget]; rw [((CondensedSet.isDiscrete_tfae _).out 0 6 :)] at h
    let : ReflectsFilteredColimitsOfSize.{u, u} (forget (ModuleCat R)) :=
      reflectsFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ⟨isColimitOfReflects (forget (ModuleCat R)) (h S).some⟩
  tfae_finish

end CondensedMod

namespace LightCondensed

variable {C : Type*} [Category* C] [HasWeakSheafify (coherentTopology LightProfinite.{u}) C]

/--
Definition of `IsDiscrete` / `IsDiscrete` 的定义

English:
abbreviation IsDiscrete
  signature: (X : LightCondensed.{u} C)
  body: X.IsConstant (coherentTopology LightProfinite)

中文:
缩写 是离散
  签名: (X : LightCondensed.{u} C)
  定义体: X.IsConstant (coherentTopology LightProfinite)

Depends on / 依赖: IsConstant, LightProfinite, X.IsConstant, coherentTopology
-/
abbrev IsDiscrete (X : LightCondensed.{u} C) := X.IsConstant (coherentTopology LightProfinite)

end LightCondensed

namespace LightCondSet

/--
lemma `mem_locallyConstant_essImage_of_isColimit_mapCocone` / 引理 `mem_locallyConstant_essImage_of_isColimit_mapCocone`

English:
lemma mem_locallyConstant_essImage_of_isColimit_mapCocone
  statement: (X : LightCondSet.{u})
  proof: by
  let i : X.obj ≅ (LightCondSet.LocallyConstant.functor.obj _).obj :=
    LightCondensed.isoLocallyConstantOfIsColimit _ h
  exact ⟨_, ⟨((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

中文:
引理 mem_locallyConstant_essImage_of_isColimit_mapCocone
  结论: (X : LightCondSet.{u})
  证明: by
  let i : X.obj ≅ (LightCondSet.LocallyConstant.functor.obj _).obj :=
    LightCondensed.isoLocallyConstantOfIsColimit _ h
  exact ⟨_, ⟨((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

Depends on / 依赖: LightCondSet, LightCondSet.LocallyConstant.functor.obj, LightCondensed, LightCondensed.isoLocallyConstantOfIsColimit, LocallyConstant, X.obj, functor, i.symm, isoLocallyConstantOfIsColimit, preimageIso, sheafToPresheaf
-/
lemma mem_locallyConstant_essImage_of_isColimit_mapCocone (X : LightCondSet.{u})
    (h : forall S : LightProfinite.{u}, IsColimit <|
      X.obj.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    LightCondSet.LocallyConstant.functor.essImage X := by
  let i : X.obj ≅ (LightCondSet.LocallyConstant.functor.obj _).obj :=
    LightCondensed.isoLocallyConstantOfIsColimit _ h
  exact ⟨_, ⟨((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

/--
Definition of `LocallyConstant.adjunction` / `LocallyConstant.adjunction` 的定义

English:
abbreviation LocallyConstant.adjunction
  signature: :
  body: CompHausLike.LocallyConstant.adjunction _ _

中文:
缩写 局部常数.adjunction
  签名: :
  定义体: CompHausLike.LocallyConstant.adjunction _ _
-/
noncomputable abbrev LocallyConstant.adjunction :
    LightCondSet.LocallyConstant.functor ⊣ LightCondensed.underlying (Type u) :=
  CompHausLike.LocallyConstant.adjunction _ _

open LightCondSet.LocallyConstant List in
/--
theorem `isDiscrete_tfae` / 定理 `isDiscrete_tfae`

English:
theorem isDiscrete_tfae
  given: (X : LightCondSet.{u})
  proof: by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ LightProfinite.isTerminalPUnit adjunction X
  tfae_have 1 ↔ 5 :=
    have : functor.Faithful := inferInstance
    have : functor.Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ LightProfinite.isTerminalPUnit adjunction X
  tfae_have 6 -> 4 := fun h =>
    mem_locallyConstant_essImage_of_isColimit_mapCocone X (fun S => (h S).some)
  tfae_have 4 -> 6 := fun ⟨Y, ⟨i⟩⟩ S =>
    ⟨IsColimit.mapCoconeEquiv ((sheafToPresheaf _ _).mapIso i)
      (LightCondensed.isColimitLocallyConstantPresheafDiagram Y S)⟩
  tfae_finish

中文:
定理 isDiscrete_tfae
  条件: (X : LightCondSet.{u})
  证明: by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ LightProfinite.isTerminalPUnit adjunction X
  tfae_have 1 ↔ 5 :=
    have : functor.Faithful := inferInstance
    have : functor.Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ LightProfinite.isTerminalPUnit adjunction X
  tfae_have 6 -> 4 := fun h =>
    mem_locallyConstant_essImage_of_isColimit_mapCocone X (fun S => (h S).some)
  tfae_have 4 -> 6 := fun ⟨Y, ⟨i⟩⟩ S =>
    ⟨IsColimit.mapCoconeEquiv ((sheafToPresheaf _ _).mapIso i)
      (LightCondensed.isColimitLocallyConstantPresheafDiagram Y S)⟩
  tfae_finish

Depends on / 依赖: Faithful, LightProfinite, LightProfinite.isTerminalPUnit, Sheaf.isConstant_iff_isIso_counit_app, Sheaf.isConstant_iff_mem_essImage, adjunction, functor, functor.Faithful, functor.Full, isConstant_iff_isIso_counit_app, isConstant_iff_mem_essImage, isTerminalPUnit, tfae_have
-/
theorem isDiscrete_tfae (X : LightCondSet.{u}) :
    TFAE
    [ X.IsDiscrete
    , IsIso ((LightCondensed.discreteUnderlyingAdj _).counit.app X)
    , (LightCondensed.discrete _).essImage X
    , LightCondSet.LocallyConstant.functor.essImage X
    , IsIso (LightCondSet.LocallyConstant.adjunction.counit.app X)
    , forall S : LightProfinite.{u}, Nonempty
        (IsColimit <| X.obj.mapCocone (coconeRightOpOfCone S.asLimitCone))
    ] := by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ LightProfinite.isTerminalPUnit adjunction X
  tfae_have 1 ↔ 5 :=
    have : functor.Faithful := inferInstance
    have : functor.Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ LightProfinite.isTerminalPUnit adjunction X
  tfae_have 6 -> 4 := fun h =>
    mem_locallyConstant_essImage_of_isColimit_mapCocone X (fun S => (h S).some)
  tfae_have 4 -> 6 := fun ⟨Y, ⟨i⟩⟩ S =>
    ⟨IsColimit.mapCoconeEquiv ((sheafToPresheaf _ _).mapIso i)
      (LightCondensed.isColimitLocallyConstantPresheafDiagram Y S)⟩
  tfae_finish

end LightCondSet

namespace LightCondMod

variable (R : Type u) [Ring R]

/--
lemma `isDiscrete_iff_isDiscrete_forget` / 引理 `isDiscrete_iff_isDiscrete_forget`

English:
lemma isDiscrete_iff_isDiscrete_forget
  given: (M : LightCondMod R)
  proof: Sheaf.isConstant_iff_forget (coherentTopology LightProfinite.{u})
    (forget (ModuleCat R)) M LightProfinite.isTerminalPUnit.{u}

中文:
引理 isDiscrete_iff_isDiscrete_forget
  条件: (M : LightCondMod R)
  证明: Sheaf.isConstant_iff_forget (coherentTopology LightProfinite.{u})
    (forget (ModuleCat R)) M LightProfinite.isTerminalPUnit.{u}

Depends on / 依赖: LightProfinite, LightProfinite.isTerminalPUnit, ModuleCat, Sheaf.isConstant_iff_forget, coherentTopology, forget, isConstant_iff_forget, isTerminalPUnit
-/
lemma isDiscrete_iff_isDiscrete_forget (M : LightCondMod R) :
    M.IsDiscrete ↔ ((LightCondensed.forget R).obj M).IsDiscrete :=
  Sheaf.isConstant_iff_forget (coherentTopology LightProfinite.{u})
    (forget (ModuleCat R)) M LightProfinite.isTerminalPUnit.{u}

open LightCondMod.LocallyConstant List in
/--
theorem `isDiscrete_tfae` / 定理 `isDiscrete_tfae`

English:
theorem isDiscrete_tfae
  given: (M : LightCondMod.{u} R)
  proof: by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _
    LightProfinite.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 5 :=
    have : (functor R).Faithful := inferInstance
    have : (functor R).Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ LightProfinite.isTerminalPUnit (adjunction R) _
  tfae_have 6 -> 1 := by
    intro h
    rw [isDiscrete_iff_isDiscrete_forget]; rw [((LightCondSet.isDiscrete_tfae _).out 0 5 :)]
    intro S
    let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat R)) :=
      preservesFilteredColimitsOfSize_shrink.{0, u, 0, u} _
    exact ⟨isColimitOfPreserves (forget (ModuleCat R)) (h S).some⟩
  tfae_have 1 -> 6 := by
    intro h S
    rw [isDiscrete_iff_isDiscrete_forget]; rw [((LightCondSet.isDiscrete_tfae _).out 0 5 :)] at h
    let : ReflectsFilteredColimitsOfSize.{0, 0} (forget (ModuleCat R)) :=
      reflectsFilteredColimitsOfSize_shrink.{0, u, 0, u} _
    exact ⟨isColimitOfReflects (forget (ModuleCat R)) (h S).some⟩
  tfae_finish

中文:
定理 isDiscrete_tfae
  条件: (M : LightCondMod.{u} R)
  证明: by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _
    LightProfinite.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 5 :=
    have : (functor R).Faithful := inferInstance
    have : (functor R).Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ LightProfinite.isTerminalPUnit (adjunction R) _
  tfae_have 6 -> 1 := by
    intro h
    rw [isDiscrete_iff_isDiscrete_forget]; rw [((LightCondSet.isDiscrete_tfae _).out 0 5 :)]
    intro S
    let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat R)) :=
      preservesFilteredColimitsOfSize_shrink.{0, u, 0, u} _
    exact ⟨isColimitOfPreserves (forget (ModuleCat R)) (h S).some⟩
  tfae_have 1 -> 6 := by
    intro h S
    rw [isDiscrete_iff_isDiscrete_forget]; rw [((LightCondSet.isDiscrete_tfae _).out 0 5 :)] at h
    let : ReflectsFilteredColimitsOfSize.{0, 0} (forget (ModuleCat R)) :=
      reflectsFilteredColimitsOfSize_shrink.{0, u, 0, u} _
    exact ⟨isColimitOfReflects (forget (ModuleCat R)) (h S).some⟩
  tfae_finish

Depends on / 依赖: Faithful, LightProfinite, LightProfinite.isTerminalPUnit, Sheaf.isConstant_iff_isIso_counit_app, Sheaf.isConstant_iff_mem_essImage, adjunction, functor, isConstant_iff_isIso_counit_app, isConstant_iff_mem_essImage, isTerminalPUnit, tfae_have
-/
theorem isDiscrete_tfae (M : LightCondMod.{u} R) :
    TFAE
    [ M.IsDiscrete
    , IsIso ((LightCondensed.discreteUnderlyingAdj _).counit.app M)
    , (LightCondensed.discrete _).essImage M
    , (LightCondMod.LocallyConstant.functor R).essImage M
    , IsIso ((LightCondMod.LocallyConstant.adjunction R).counit.app M)
    , forall S : LightProfinite.{u}, Nonempty
        (IsColimit <| M.obj.mapCocone (coconeRightOpOfCone S.asLimitCone))
    ] := by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _
    LightProfinite.isTerminalPUnit (adjunction R) _
  tfae_have 1 ↔ 5 :=
    have : (functor R).Faithful := inferInstance
    have : (functor R).Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ LightProfinite.isTerminalPUnit (adjunction R) _
  tfae_have 6 -> 1 := by
    intro h
    rw [isDiscrete_iff_isDiscrete_forget]; rw [((LightCondSet.isDiscrete_tfae _).out 0 5 :)]
    intro S
    let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat R)) :=
      preservesFilteredColimitsOfSize_shrink.{0, u, 0, u} _
    exact ⟨isColimitOfPreserves (forget (ModuleCat R)) (h S).some⟩
  tfae_have 1 -> 6 := by
    intro h S
    rw [isDiscrete_iff_isDiscrete_forget]; rw [((LightCondSet.isDiscrete_tfae _).out 0 5 :)] at h
    let : ReflectsFilteredColimitsOfSize.{0, 0} (forget (ModuleCat R)) :=
      reflectsFilteredColimitsOfSize_shrink.{0, u, 0, u} _
    exact ⟨isColimitOfReflects (forget (ModuleCat R)) (h S).some⟩
  tfae_finish

end LightCondMod
