/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Locally Free Sheaves

A sheaf of modules is locally free if it is locally isomorphic to a free module.

## Main Definitions

- `SheafOfModules.LocalGeneratorsData.IsLocallyFreeData`: This is defined as a predicate on
  `SheafOfModules.LocalGeneratorData` where `q : M.LocalGeneratorData` is said to be locally
  free data if `(q.generators i).π` is an isomorphism for all `i` in `q.I`.

- `SheafOfModules.IsLocallyFree`: `M : SheafOfModules R` is locally free is there exists locally
  free data for it.

-/

public section

universe u v₁ u₁

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

noncomputable section

namespace SheafOfModules

section

variable [forall X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [forall X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

/--
Definition of `IsLocallyFreeData` / `IsLocallyFreeData` 的定义

English:
class IsLocallyFreeData
  parameters: {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
  axioms and operations (1):
    - isIso : forall i, IsIso (q.generators i).π  [default: by infer_instance]

中文:
类 IsLocallyFreeData
  参数: {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
  公理与运算 (1 个):
    - isIso : 对任意 i, IsIso (q.generators i).π  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsLocallyFreeData {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) : Prop where
  isIso : forall i, IsIso (q.generators i).π := by infer_instance

attribute [instance] IsLocallyFreeData.isIso

/--
Instance `IsLocallyFreeData.shrink` / 实例 `IsLocallyFreeData.shrink`

English:
instance IsLocallyFreeData.shrink
  signature: {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
  body: inferInstanceAs (IsIso (q.generators i.2.choose).π)

中文:
实例 IsLocallyFreeData.shrink
  签名: {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
  定义体: inferInstanceAs (IsIso (q.generators i.2.choose).π)

Depends on / 依赖: generators, q.generators
-/
instance IsLocallyFreeData.shrink {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] : q.shrink.IsLocallyFreeData where
  isIso i := inferInstanceAs (IsIso (q.generators i.2.choose).π)

end LocalGeneratorsData

/-- A sheaf of modules is locally free if it is locally isomorphic to free sheaves:
There exist local generators satisfying `IsLocallyFreeData`. -/
@[stacks 01C6 "(1)"]
/--
Definition of `IsLocallyFree` / `IsLocallyFree` 的定义

English:
class IsLocallyFree
  parameters: (M : SheafOfModules.{u} R)
  axioms and operations (1):
    - exists_isLocallyFreeData : exists q : LocalGeneratorsData.{u₁} M, q.IsLocallyFreeData

中文:
类 IsLocallyFree
  参数: (M : SheafOfModules.{u} R)
  公理与运算 (1 个):
    - exists_isLocallyFreeData : 存在 q : LocalGeneratorsData.{u₁} M, q.IsLocallyFreeData
-/
class IsLocallyFree (M : SheafOfModules.{u} R) : Prop where
  exists_isLocallyFreeData : exists q : LocalGeneratorsData.{u₁} M, q.IsLocallyFreeData

/--
theorem `LocalGeneratorsData.isLocallyFree` / 定理 `LocalGeneratorsData.isLocallyFree`

English:
theorem LocalGeneratorsData.isLocallyFree
  statement: {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
  proof: ⟨q.shrink, inferInstance⟩

中文:
定理 LocalGeneratorsData.isLocallyFree
  结论: {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
  证明: ⟨q.shrink, inferInstance⟩

Depends on / 依赖: q.shrink, shrink
-/
theorem LocalGeneratorsData.isLocallyFree {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] : M.IsLocallyFree := ⟨q.shrink, inferInstance⟩

end

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The generating sections of the free sheaf of modules. -/
@[expose, simps]
/--
Definition of `free.generatingSections` / `free.generatingSections` 的定义

English:
definition free.generatingSections
  signature: (I : Type u)
  body: I
  s (i) := freeSection i
  epi := by
    simp only [Equiv.symm_apply_apply]
    infer_instance

@[simp]

中文:
定义 free.generatingSections
  签名: (I : 类型u)
  定义体: I
  s (i) := freeSection i
  epi := by
    simp only [Equiv.symm_apply_apply]
    infer_instance

@[simp]

Depends on / 依赖: GeneratingSections
-/
def free.generatingSections (I : Type u) : (free (R := R) I).GeneratingSections where
  I := I
  s (i) := freeSection i
  epi := by
    simp only [Equiv.symm_apply_apply]
    infer_instance

@[simp]
/--
lemma `free.generatingSections_π` / 引理 `free.generatingSections_π`

English:
lemma free.generatingSections_π
  given: (I : Type u)
  proof: Equiv.symm_apply_apply (free I).freeHomEquiv _

中文:
引理 free.generatingSections_π
  条件: (I : 类型u)
  证明: Equiv.symm_apply_apply (free I).freeHomEquiv _
-/
lemma free.generatingSections_π (I : Type u) :
    (free.generatingSections (R := R) I).π = 𝟙 (free I) :=
  Equiv.symm_apply_apply (free I).freeHomEquiv _

set_option backward.isDefEq.respectTransparency false in
instance (I : Type u) : IsIso (free.generatingSections (R := R) I).π := by
  rw [free.generatingSections_π]
  infer_instance

variable [forall X, HasSheafify (J.over X) AddCommGrpCat.{u}] [HasBinaryProducts C]
  [forall X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (I : Type u) :
    (free.generatingSections (R := R) I).localGeneratorsData.IsLocallyFreeData where
  isIso i := by
    dsimp
    infer_instance

instance (I : Type u) : (free (R := R) I).IsLocallyFree where
  exists_isLocallyFreeData := ⟨(free.generatingSections I).localGeneratorsData, inferInstance⟩

end

section

variable [forall X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [forall X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

/-- Given locally free data, this is the `QuasiCoherentData` where there are no relations. -/
@[expose, simps]
/--
Definition of `quasiCoherentData` / `quasiCoherentData` 的定义

English:
definition quasiCoherentData
  signature: {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) [q.IsLocallyFreeData]
  body: q.I
  X := q.X
  coversTop := q.coversTop
  presentation i := {
    generators := q.generators i
    relations.I := ULift Empty
    relations.s j := Empty.rec _ j.down
    relations.epi := IsZero.epi (IsZero.of_iso (isZero_zero _) (Limits.kernel.ofMono _)) _ }

@[simp]

中文:
定义 quasiCoherentData
  签名: {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) [q.IsLocallyFreeData]
  定义体: q.I
  X := q.X
  coversTop := q.coversTop
  presentation i := {
    generators := q.generators i
    relations.I := ULift Empty
    relations.s j := Empty.rec _ j.down
    relations.epi := IsZero.epi (IsZero.of_iso (isZero_zero _) (Limits.kernel.ofMono _)) _ }

@[simp]
-/
def quasiCoherentData {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] :
    M.QuasicoherentData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  presentation i := {
    generators := q.generators i
    relations.I := ULift Empty
    relations.s j := Empty.rec _ j.down
    relations.epi := IsZero.epi (IsZero.of_iso (isZero_zero _) (Limits.kernel.ofMono _)) _ }

@[simp]
/--
lemma `quasiCoherentData_localGeneratorsData` / 引理 `quasiCoherentData_localGeneratorsData`

English:
lemma quasiCoherentData_localGeneratorsData
  statement: {M : SheafOfModules.{u} R}
  proof: rfl

中文:
引理 quasiCoherentData_localGeneratorsData
  结论: {M : SheafOfModules.{u} R}
  证明: rfl
-/
lemma quasiCoherentData_localGeneratorsData {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] :
    q.quasiCoherentData.localGeneratorsData = q := rfl

end LocalGeneratorsData

instance (priority := 100) (M : SheafOfModules.{u} R) [h : M.IsLocallyFree] : M.IsQuasicoherent :=
  have := h.exists_isLocallyFreeData.choose_spec
  h.exists_isLocallyFreeData.choose.quasiCoherentData.isQuasicoherent

end

end SheafOfModules
