/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Ext in Grothendieck abelian categories

Let `C : Type u` be an abelian category (with `Category.{v} C`).
If `C` is a Grothendieck abelian category relatively to a universe `w`,
the morphisms in `C` must be `w`-small, and as `C` has enough injectives,
the `Ext`-groups are also `w`-small. If `C` is a nonzero category,
it is possible to show that any `w`-small type `T` injects into a type
of morphisms in `C` (consider the various inclusions
`X ⟶ ∐ (fun (_ : T) ↦ X)` for a nonzero object `X : C`). It follows that it
is reasonable to think that the universe `w` is unique, and is the best
choice for the universe where the `Ext`-groups in `C` should be defined.

In this situation, we make `HasExt.{w} C` an instance.
As a result, when `X` and `Y` are objects in `C` and `n : ℕ`,
we have `Ext X Y n : Type w`.

-/

public section

namespace CategoryTheory

universe w v u

/-
**CategoryTheory.IsGrothendieckAbelian.hasExt** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.IsGrothendieckAbelian`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [CategoryTheory.IsGrothendieckAbelian.{w, v, u} C], Categor
yTheory.HasExt C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.hasExt_of_enoughInjectives`：hasExt_of_enoughInjectives [L
ocallySmall.{w} C] [EnoughInjectives C] : HasExt.{w} C
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.locallySmall`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
-/
instance IsGrothendieckAbelian.hasExt
    (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    HasExt.{w} C :=
  hasExt_of_enoughInjectives _

end CategoryTheory

