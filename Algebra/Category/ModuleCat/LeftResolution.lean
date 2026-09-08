/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.LeftResolution.Basic

/-!
# Functorial projective resolutions of modules

The fact that an `R`-module `M` can be functorially written as a quotient of a
projective `R`-module is expressed as the definition `ModuleCat.projectiveResolution`.
Using the construction in the file `Mathlib/Algebra/Homology/LeftResolution/Basic.lean`,
we may obtain a functor `(projectiveResolution R).chainComplexFunctor` which
sends `M : ModuleCat R` to a projective resolution.

-/

@[expose] public section

universe u

variable (R : Type u) [Ring R]

namespace ModuleCat

open CategoryTheory Abelian

/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Type u) : Projective ((free R).obj X) where
  factors {M N} f p hp := by
    rw [epi_iff_surjective] at hp
    obtain ⟨s, hs⟩ := hp.hasRightInverse
    exact ⟨freeDesc (↾fun x ↦ s (f (freeMk x))), by cat_disch⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An `R`-module `M` can be functorially written as a quotient of a
projective `R`-module. -/
/-
**ModuleCat.projectiveResolution** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：projectiveResolution : LeftResolution (ObjectProperty.ι (isProjective (Mod
uleCat.{u} R))) where F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-module `M` can be functorially written as a quotient of a
projective `R`-module.
-/
noncomputable def projectiveResolution :
    LeftResolution (ObjectProperty.ι (isProjective (ModuleCat.{u} R))) where
  F := ObjectProperty.lift _ (forget _ ⋙ free R) (by dsimp; infer_instance)
  π := (adj R).counit

end ModuleCat

