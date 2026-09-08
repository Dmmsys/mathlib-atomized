/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Topology.Category.TopCat.Adjunctions
public import Mathlib.Topology.Compactification.StoneCech

/-!
# Adjunctions involving the category of Stonean spaces

This file constructs the left adjoint `typeToStonean` to the forgetful functor from Stonean spaces
to sets, using the Stone-Cech compactification. This allows to conclude that the monomorphisms in
`Stonean` are precisely the injective maps (see `Stonean.mono_iff_injective`).
-/

@[expose] public section

universe u

open CategoryTheory Adjunction

namespace Stonean

/-- The object part of the compactification functor from types to Stonean spaces. -/
/-
**Stonean.stoneCechObj** 是 Mathlib 中的一个定义，位于命名空间 `Stonean`。
形式化陈述：stoneCechObj (X : Type u) : Stonean
参数：X : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object part of the compactification functor from types to Stonean spaces.
-/
def stoneCechObj (X : Type u) : Stonean :=
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  haveI : ExtremallyDisconnected (StoneCech X) :=
    CompactT2.Projective.extremallyDisconnected StoneCech.projective
  of (StoneCech X)

/-- The equivalence of homsets to establish the adjunction between the Stone-Cech compactification
functor and the forgetful functor. -/
/-
**Stonean.stoneCechEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Stonean`。
形式化陈述：stoneCechEquivalence (X : Type u) (Y : Stonean.{u}) : (stoneCechObj X ⟶ Y)
 ≃ (X ⟶ Y)
参数：X : Type u；Y : Stonean.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The equivalence of homsets to establish the adjunction between the Stone-Cech co
mpactification
functor and the forgetful functor.
-/
noncomputable def stoneCechEquivalence (X : Type u) (Y : Stonean.{u}) :
    (stoneCechObj X ⟶ Y) ≃ (X ⟶ Y) := by
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  refine fullyFaithfulToCompHaus.homEquiv.trans ?_
  exact (_root_.stoneCechEquivalence (TopCat.of X) (toCompHaus.obj Y)).trans
    (TopCat.adj₁.homEquiv _ _)

end Stonean

/-- The Stone-Cech compactification functor from types to Stonean spaces. -/
/-
**typeToStonean** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：typeToStonean : Type u ⥤ Stonean.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Stone-Cech compactification functor from types to Stonean spaces.
-/
noncomputable def typeToStonean : Type u ⥤ Stonean.{u} :=
  leftAdjointOfEquiv (G := forget _) Stonean.stoneCechEquivalence fun _ _ _ _ _ => rfl

namespace Stonean

/-- The Stone-Cech compactification functor is left adjoint to the forgetful functor. -/
/-
**Stonean.stoneCechAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `Stonean`。
形式化陈述：stoneCechAdjunction : typeToStonean ⊣ (forget Stonean)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Stone-Cech compactification functor is left adjoint to the forgetful functor
.
-/
noncomputable def stoneCechAdjunction : typeToStonean ⊣ (forget Stonean) :=
  adjunctionOfEquivLeft (G := forget _) stoneCechEquivalence fun _ _ _ _ _ => rfl

/-- The forgetful functor from Stonean spaces, being a right adjoint, preserves limits. -/
/-
**Stonean.forget.preservesLimits** 是 Mathlib 中的一个定理，位于命名空间 `Stonean.forget`。
形式化陈述：CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget Stonean)
参数：CategoryTheory.forget Stonean。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`：rightAdjoint_pre
servesLimits : PreservesLimitsOfSize.{v, u} G where preservesLimitsOfShape

--- 原说明 ---
The forgetful functor from Stonean spaces, being a right adjoint, preserves limi
ts.
-/
noncomputable instance forget.preservesLimits : Limits.PreservesLimits (forget Stonean) :=
  rightAdjoint_preservesLimits stoneCechAdjunction

end Stonean

