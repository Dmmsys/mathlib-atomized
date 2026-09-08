/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.Condensed.Functors
public import Mathlib.Condensed.Limits

/-!

# Solid modules

This file contains the definition of a solid `R`-module: `CondensedMod.isSolid R`. Solid modules
groups were introduced in [scholze2019condensed], Definition 5.1.

## Main definition

* `CondensedMod.IsSolid R`: the predicate on condensed `R`-modules describing the property of
  being solid.

TODO (hard): prove that `((profiniteSolid ℤ).obj S).IsSolid` for `S : Profinite`.
TODO (slightly easier): prove that `((profiniteSolid 𝔽ₚ).obj S).IsSolid` for `S : Profinite`.
-/

@[expose] public section

universe u

variable (R : Type (u + 1)) [Ring R]

open CategoryTheory Limits Profinite Condensed

noncomputable section

namespace Condensed

/-- The free condensed `R`-module on a finite set. -/
/-
**Condensed.finFree** 是 Mathlib 中的一个缩写定义，位于命名空间 `Condensed`。
形式化陈述：finFree : FintypeCat.{u} ⥤ CondensedMod.{u} R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free condensed `R`-module on a finite set.
-/
abbrev finFree : FintypeCat.{u} ⥤ CondensedMod.{u} R :=
  FintypeCat.toProfinite ⋙ profiniteToCondensed ⋙ free R

/-- The free condensed `R`-module on a profinite space. -/
/-
**Condensed.profiniteFree** 是 Mathlib 中的一个缩写定义，位于命名空间 `Condensed`。
形式化陈述：profiniteFree : Profinite.{u} ⥤ CondensedMod.{u} R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free condensed `R`-module on a profinite space.
-/
abbrev profiniteFree : Profinite.{u} ⥤ CondensedMod.{u} R :=
  profiniteToCondensed ⋙ free R

/-- The functor sending a profinite space `S` to the condensed `R`-module `R[S]^\solid`. -/
/-
**Condensed.profiniteSolid** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：profiniteSolid : Profinite.{u} ⥤ CondensedMod.{u} R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor sending a profinite space `S` to the condensed `R`-module `R[S]^\sol
id`.
-/
def profiniteSolid : Profinite.{u} ⥤ CondensedMod.{u} R :=
  Functor.rightKanExtension FintypeCat.toProfinite (finFree R)

/-- The natural transformation `FintypeCat.toProfinite ⋙ profiniteSolid R ⟶ finFree R`
which is part of the assertion that `profiniteSolid R` is the (pointwise) right
Kan extension of `finFree R` along `FintypeCat.toProfinite`. -/
/-
**Condensed.profiniteSolidCounit** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：profiniteSolidCounit : FintypeCat.toProfinite ⋙ profiniteSolid R ⟶ finFree
 R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `FintypeCat.toProfinite ⋙ profiniteSolid R ⟶ finFree 
R`
which is part of the assertion that `profiniteSolid R` is the (pointwise) right
Kan extension of `finFree R` along `FintypeCat.toProfinite`.
-/
def profiniteSolidCounit : FintypeCat.toProfinite ⋙ profiniteSolid R ⟶ finFree R :=
  Functor.rightKanExtensionCounit FintypeCat.toProfinite (finFree R)
/-
**Condensed.** 是 Mathlib 中的一个实例，位于命名空间 `Condensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (profiniteSolid R).IsRightKanExtension (profiniteSolidCounit R) := by
  dsimp only [profiniteSolidCounit, profiniteSolid]
  infer_instance

/-- The functor `Profinite.{u} ⥤ CondensedMod.{u} R` is a pointwise
right Kan extension of `finFree R : FintypeCat.{u} ⥤ CondensedMod.{u} R`
along `FintypeCat.toProfinite`. -/
/-
**Condensed.profiniteSolidIsPointwiseRightKanExtension** 是 Mathlib 中的一个定义，位于命名空间
 `Condensed`。
形式化陈述：profiniteSolidIsPointwiseRightKanExtension : (Functor.RightExtension.mk _ 
(profiniteSolidCounit R)).IsPointwiseRightKanExtension
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Condensed.instIsRightKanExtensionFintypeCatCondensedModProfiniteProfinit
eSolidProfiniteSolidCounit`：∀ (R : Type (u + 1)) [inst : Ring R],   (Condensed.p
rofiniteSolid R).IsRightKanExtension (Condensed.profiniteSolidCounit R)

--- 原说明 ---
The functor `Profinite.{u} ⥤ CondensedMod.{u} R` is a pointwise
right Kan extension of `finFree R : FintypeCat.{u} ⥤ CondensedMod.{u} R`
along `FintypeCat.toProfinite`.
-/
def profiniteSolidIsPointwiseRightKanExtension :
    (Functor.RightExtension.mk _ (profiniteSolidCounit R)).IsPointwiseRightKanExtension :=
  Functor.isPointwiseRightKanExtensionOfIsRightKanExtension _ _

/-- The natural transformation `R[S] ⟶ R[S]^\solid`. -/
/-
**Condensed.profiniteSolidification** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：profiniteSolidification : profiniteFree R ⟶ profiniteSolid.{u} R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Condensed.instIsRightKanExtensionFintypeCatCondensedModProfiniteProfinit
eSolidProfiniteSolidCounit`：∀ (R : Type (u + 1)) [inst : Ring R],   (Condensed.p
rofiniteSolid R).IsRightKanExtension (Condensed.profiniteSolidCounit R)

--- 原说明 ---
The natural transformation `R[S] ⟶ R[S]^\solid`.
-/
def profiniteSolidification : profiniteFree R ⟶ profiniteSolid.{u} R :=
  (profiniteSolid R).liftOfIsRightKanExtension (profiniteSolidCounit R) _ (𝟙 _)

end Condensed

/--
The predicate on condensed `R`-modules describing the property of being solid.

TODO: This is not the correct definition of solid `R`-modules for a general `R`. The correct one is
as follows: Use this to define solid modules over a finite type `ℤ`-algebra `R`. In particular this
gives a definition of solid modules over `ℤ[X]` (polynomials in one variable). Then a solid
`R`-module over a general ring `R` is the condition that for every `r ∈ R` and every ring
homomorphism `ℤ[X] → R` such that `X` maps to `r`, the underlying `ℤ[X]`-module is solid.
-/
/-
**CondensedMod.IsSolid** 是 Mathlib 中的一个归纳类型，位于命名空间 `CondensedMod`。
形式化陈述：(R : Type (u + 1)) → [inst : Ring R] → CondensedMod R → Prop
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate on condensed `R`-modules describing the property of being solid.

TODO: This is not the correct definition of solid `R`-modules for a general `R`.
 The correct one is
as follows: Use this to define solid modules over a finite type `ℤ`-algebra `R`.
 In particular this
gives a definition of solid modules over `ℤ[X]` (polynomials in one variable). T
hen a solid
`R`-module over a general ring `R` is the condition that for every `r ∈ R` and e
very ring
homomorphism `ℤ[X] → R` such that `X` maps to `r`, the underlying `ℤ[X]`-module 
is solid.
-/
class CondensedMod.IsSolid (A : CondensedMod.{u} R) : Prop where
  isIso_solidification_map : ∀ X : Profinite.{u}, IsIso ((yoneda.obj A).map
    ((profiniteSolidification R).app X).op)
