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

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

/-- Local generator data `q` is locally free data if all of the natural morphisms
`free (q.generators i).I ⟶ M.over (q.X i)` are isomorphisms. -/
/-
**SheafOfModules.LocalGeneratorsData.IsLocallyFreeData** 是 Mathlib 中的一个类，位于命名空间 
`SheafOfModules.LocalGeneratorsData`。
形式化陈述：IsLocallyFreeData {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) :
 Prop where isIso : forall i, IsIso (q.generators i).π
参数：q : M.LocalGeneratorsData。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Local generator data `q` is locally free data if all of the natural morphisms
`free (q.generators i).I ⟶ M.over (q.X i)` are isomorphisms.
-/
class IsLocallyFreeData {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) : Prop where
  isIso : ∀ i, IsIso (q.generators i).π := by infer_instance

attribute [instance] IsLocallyFreeData.isIso
/-
**SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.shrink** 是 Mathlib 中的一个定理
，位于命名空间 `SheafOfModules.LocalGeneratorsData.IsLocallyFreeData`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R : CategoryTheory.Sheaf J RingCat} [inst_1 : ∀
 (X : C), CategoryTheory.HasWeakSheafify (J.over X) AddCommGrpCat]   [inst_2 : ∀
 (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat] {M : SheafOfModules 
R}   (q : M.LocalGeneratorsData) [q.IsLocallyFreeData], q.shrink.IsLocallyFreeDa
ta
参数：X : C；J.over X；X : C；J.over X；q : M.LocalGeneratorsData。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsLocallyFreeData.shrink {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] : q.shrink.IsLocallyFreeData where
  isIso i := inferInstanceAs (IsIso (q.generators i.2.choose).π)

end LocalGeneratorsData

/-- A sheaf of modules is locally free if it is locally isomorphic to free sheaves:
There exist local generators satisfying `IsLocallyFreeData`. -/
@[stacks 01C6 "(1)"]
/-
**SheafOfModules.IsLocallyFree** 是 Mathlib 中的一个归纳类型，位于命名空间 `SheafOfModules`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Sheaf J RingCa
t} →         [∀ (X : C), CategoryTheory.HasWeakSheafify (J.over X) AddCommGrpCat
] →           [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat] → Sh
eafOfModules R → Prop
参数：X : C；J.over X；X : C；J.over X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sheaf of modules is locally free if it is locally isomorphic to free sheaves:
There exist local generators satisfying `IsLocallyFreeData`.
-/
class IsLocallyFree (M : SheafOfModules.{u} R) : Prop where
  exists_isLocallyFreeData : ∃ q : LocalGeneratorsData.{u₁} M, q.IsLocallyFreeData
/-
**SheafOfModules.LocalGeneratorsData.isLocallyFree** 是 Mathlib 中的一个定理，位于命名空间 `Sh
eafOfModules.LocalGeneratorsData`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R : CategoryTheory.Sheaf J RingCat} [inst_1 : ∀
 (X : C), CategoryTheory.HasWeakSheafify (J.over X) AddCommGrpCat]   [inst_2 : ∀
 (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat] {M : SheafOfModules 
R}   (q : M.LocalGeneratorsData) [q.IsLocallyFreeData], M.IsLocallyFree
参数：X : C；J.over X；X : C；J.over X；q : M.LocalGeneratorsData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.shrink`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.Grothendiec
kTopology C}   {R : CategoryTheory.Sheaf J RingCa…
-/
theorem LocalGeneratorsData.isLocallyFree {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] : M.IsLocallyFree := ⟨q.shrink, inferInstance⟩

end

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The generating sections of the free sheaf of modules. -/
@[expose, simps]
/-
**SheafOfModules.free.generatingSections** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModul
es.free`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Sheaf J RingCa
t} →         [inst_1 : CategoryTheory.HasWeakSheafify J AddCommGrpCat] →        
   [inst_2 : J.WEqualsLocallyBijective AddCommGrpCat] → (I : Type u) → (SheafOfM
odules.free I).GeneratingSections
参数：I : Type u；SheafOfModules.free I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The generating sections of the free sheaf of modules.
-/
def free.generatingSections (I : Type u) : (free (R := R) I).GeneratingSections where
  I := I
  s (i) := freeSection i
  epi := by
    simp only [Equiv.symm_apply_apply]
    infer_instance

@[simp]
/-
**SheafOfModules.free.generatingSections_** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModu
les`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma free.generatingSections_π (I : Type u) :
    (free.generatingSections (R := R) I).π = 𝟙 (free I) :=
  Equiv.symm_apply_apply (free I).freeHomEquiv _

set_option backward.isDefEq.respectTransparency false in
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : Type u) : IsIso (free.generatingSections (R := R) I).π := by
  rw [free.generatingSections_π]
  infer_instance

variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}] [HasBinaryProducts C]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : Type u) :
    (free.generatingSections (R := R) I).localGeneratorsData.IsLocallyFreeData where
  isIso i := by
    dsimp
    infer_instance
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : Type u) : (free (R := R) I).IsLocallyFree where
  exists_isLocallyFreeData := ⟨(free.generatingSections I).localGeneratorsData, inferInstance⟩

end

section

variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

/-- Given locally free data, this is the `QuasiCoherentData` where there are no relations. -/
@[expose, simps]
/-
**SheafOfModules.LocalGeneratorsData.quasiCoherentData** 是 Mathlib 中的一个定义，位于命名空间
 `SheafOfModules.LocalGeneratorsData`。
形式化陈述：quasiCoherentData {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) [
q.IsLocallyFreeData] : M.QuasicoherentData where I
参数：q : M.LocalGeneratorsData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given locally free data, this is the `QuasiCoherentData` where there are no rela
tions.
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
/-
**SheafOfModules.LocalGeneratorsData.quasiCoherentData_localGeneratorsData** 是 M
athlib 中的一个引理，位于命名空间 `SheafOfModules.LocalGeneratorsData`。
形式化陈述：quasiCoherentData_localGeneratorsData {M : SheafOfModules.{u} R} (q : M.Lo
calGeneratorsData) [q.IsLocallyFreeData] : q.quasiCoherentData.localGeneratorsDa
ta = q
参数：q : M.LocalGeneratorsData。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
-/
lemma quasiCoherentData_localGeneratorsData {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] :
    q.quasiCoherentData.localGeneratorsData = q := rfl

end LocalGeneratorsData

/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (M : SheafOfModules.{u} R) [h : M.IsLocallyFree] : M.IsQuasicoherent :=
  have := h.exists_isLocallyFreeData.choose_spec
  h.exists_isLocallyFreeData.choose.quasiCoherentData.isQuasicoherent

end

end SheafOfModules

