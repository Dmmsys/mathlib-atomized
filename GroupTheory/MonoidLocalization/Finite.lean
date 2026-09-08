/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Localization of a finitely generated submonoid

## TODO

If `Mathlib/GroupTheory/Finiteness.lean` wasn't so heavy, this could move earlier.
-/

public section

open Localization

variable {M : Type*} [CommMonoid M] {S : Submonoid M}

namespace Localization

/-- The localization of a finitely generated monoid at a finitely generated submonoid is
finitely generated. -/
@[to_additive /-- The localization of a finitely generated monoid at a finitely generated submonoid
is finitely generated. -/]
/-
**Localization.fg** 是 Mathlib 中的一个引理，位于命名空间 `Localization`。
形式化陈述：fg [Monoid.FG M] (hS : S.FG) : Monoid.FG Localization S
参数：hS : S.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.fg_of_surjective`：Monoid.fg_of_surjective {M' : Type*} [Monoid M'
] [Monoid.FG M] (f : M ->* M') (hf : Function.Surjective f) : Monoid.FG M'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.fg_iff_submonoid_fg`：Monoid.fg_iff_submonoid_fg (N : Submonoid M)
 : Monoid.FG N ↔ N.FG
· 使用引理 `Localization.mkHom_surjective`：mkHom_surjective : Surjective (mkHom (S
-/
lemma fg [Monoid.FG M] (hS : S.FG) : Monoid.FG <| Localization S := by
  rw [← Monoid.fg_iff_submonoid_fg] at hS; exact Monoid.fg_of_surjective mkHom mkHom_surjective

end Localization

namespace Algebra.GrothendieckGroup

/-- The Grothendieck group of a finitely generated monoid is finitely generated. -/
@[to_additive /-- The Grothendieck group of a finitely generated monoid is finitely generated. -/]
/-
**Algebra.GrothendieckGroup.instFG** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Grothendie
ckGroup`。
形式化陈述：instFG [Monoid.FG M] : Monoid.FG GrothendieckGroup M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Localization.fg`：fg [Monoid.FG M] (hS : S.FG) : Monoid.FG Localization S
· 使用定理 `Monoid.FG.fg_top`：∀ {M : Type u_1} {inst : Monoid M} [self : Monoid.FG M
], ⊤.FG

--- 原说明 ---
The Grothendieck group of a finitely generated monoid is finitely generated.
-/
instance instFG [Monoid.FG M] : Monoid.FG <| GrothendieckGroup M := fg Monoid.FG.fg_top

end Algebra.GrothendieckGroup

