/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-!
# `FGModuleCat K` is an abelian category.

-/

public section

noncomputable section

universe v u

open CategoryTheory Limits

namespace FGModuleCat

variable {k : Type u} [Ring k] [IsNoetherianRing k]

/-
**FGModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : FGModuleCat k} (f : X ⟶ Y) : IsIso (Abelian.coimageImageComparison f) :=
  have := IsIso.of_isIso_fac_right (Abelian.PreservesCoimage.hom_coimageImageComparison
      (forget₂ (FGModuleCat k) (ModuleCat k)) f).symm
  Functor.FullyFaithful.isIso_of_isIso_map (ModuleCat.isFG k).fullyFaithfulι _
/-
**FGModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Abelian (FGModuleCat k) := Abelian.ofCoimageImageComparisonIsIso

end FGModuleCat

