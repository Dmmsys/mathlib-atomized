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

/--
Definition of `stoneCechObj` / `stoneCechObj` 的定义

English:
definition stoneCechObj
  signature: (X : Type u)
  body: letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  haveI : ExtremallyDisconnected (StoneCech X) :=
    CompactT2.Projective.extremallyDisconnected StoneCech.projective
  of (StoneCech X)

中文:
定义 stoneCechObj
  签名: (X : 类型u)
  定义体: letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  haveI : ExtremallyDisconnected (StoneCech X) :=
    CompactT2.Projective.extremallyDisconnected StoneCech.projective
  of (StoneCech X)

Depends on / 依赖: CompactT2, CompactT2.Projective.extremallyDisconnected, DiscreteTopology, ExtremallyDisconnected, Projective, StoneCech, StoneCech.projective, TopologicalSpace, extremallyDisconnected, projective
-/
def stoneCechObj (X : Type u) : Stonean :=
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  haveI : ExtremallyDisconnected (StoneCech X) :=
    CompactT2.Projective.extremallyDisconnected StoneCech.projective
  of (StoneCech X)

/--
Definition of `stoneCechEquivalence` / `stoneCechEquivalence` 的定义

English:
definition stoneCechEquivalence
  signature: (X : Type u) (Y : Stonean.{u})
  body: by
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  refine fullyFaithfulToCompHaus.homEquiv.trans ?_
  exact (_root_.stoneCechEquivalence (TopCat.of X) (toCompHaus.obj Y)).trans
    (TopCat.adj₁.homEquiv _ _)

中文:
定义 stoneCechEquivalence
  签名: (X : 类型u) (Y : Stonean.{u})
  定义体: by
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  refine fullyFaithfulToCompHaus.homEquiv.trans ?_
  exact (_root_.stoneCechEquivalence (TopCat.of X) (toCompHaus.obj Y)).trans
    (TopCat.adj₁.homEquiv _ _)

Depends on / 依赖: DiscreteTopology, TopCat, TopCat.adj, TopCat.of, TopologicalSpace, _root_, _root_.stoneCechEquivalence, fullyFaithfulToCompHaus, fullyFaithfulToCompHaus.homEquiv.trans, homEquiv, stoneCechEquivalence, toCompHaus, toCompHaus.obj
-/
noncomputable def stoneCechEquivalence (X : Type u) (Y : Stonean.{u}) :
    (stoneCechObj X ⟶ Y) ≃ (X ⟶ Y) := by
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  refine fullyFaithfulToCompHaus.homEquiv.trans ?_
  exact (_root_.stoneCechEquivalence (TopCat.of X) (toCompHaus.obj Y)).trans
    (TopCat.adj₁.homEquiv _ _)

end Stonean

/--
Definition of `typeToStonean` / `typeToStonean` 的定义

English:
definition typeToStonean
  signature: : Type u ⥤ Stonean.{u}
  body: leftAdjointOfEquiv (G := forget _) Stonean.stoneCechEquivalence fun _ _ _ _ _ => rfl

中文:
定义 typeToStonean
  签名: : 类型u ⥤ Stonean.{u}
  定义体: leftAdjointOfEquiv (G := forget _) Stonean.stoneCechEquivalence fun _ _ _ _ _ => rfl

Depends on / 依赖: Stonean, Stonean.stoneCechEquivalence, forget, leftAdjointOfEquiv, stoneCechEquivalence
-/
noncomputable def typeToStonean : Type u ⥤ Stonean.{u} :=
  leftAdjointOfEquiv (G := forget _) Stonean.stoneCechEquivalence fun _ _ _ _ _ => rfl

namespace Stonean

/--
Definition of `stoneCechAdjunction` / `stoneCechAdjunction` 的定义

English:
definition stoneCechAdjunction
  signature: : typeToStonean ⊣ (forget Stonean)
  body: adjunctionOfEquivLeft (G := forget _) stoneCechEquivalence fun _ _ _ _ _ => rfl

中文:
定义 stoneCechAdjunction
  签名: : typeToStonean ⊣ (forget Stonean)
  定义体: adjunctionOfEquivLeft (G := forget _) stoneCechEquivalence fun _ _ _ _ _ => rfl

Depends on / 依赖: adjunctionOfEquivLeft, forget, stoneCechEquivalence
-/
noncomputable def stoneCechAdjunction : typeToStonean ⊣ (forget Stonean) :=
  adjunctionOfEquivLeft (G := forget _) stoneCechEquivalence fun _ _ _ _ _ => rfl

/--
Instance `forget.preservesLimits` / 实例 `forget.preservesLimits`

English:
instance forget.preservesLimits
  signature: : Limits.PreservesLimits (forget Stonean)
  body: rightAdjoint_preservesLimits stoneCechAdjunction

中文:
实例 forget.preservesLimits
  签名: : Limits.PreservesLimits (forget Stonean)
  定义体: rightAdjoint_preservesLimits stoneCechAdjunction

Depends on / 依赖: rightAdjoint_preservesLimits, stoneCechAdjunction
-/
noncomputable instance forget.preservesLimits : Limits.PreservesLimits (forget Stonean) :=
  rightAdjoint_preservesLimits stoneCechAdjunction

end Stonean
