/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.CompHausLike.Limits
public import Mathlib.Topology.Category.LightProfinite.Basic
/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib/Topology/Category/CompHausLike/Limits.lean`) to the special case of
`LightProfinite`.
-/

public section

namespace LightProfinite

universe u w

open CategoryTheory Limits CompHausLike

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasExplicitPullbacks
  body: {
    hasProp := ⟨show TotallyDisconnectedSpace {_xy : _ | _} from inferInstance,
      show SecondCountableTopology {_xy : _ | _} from inferInstance⟩ }

中文:
实例 :
  签名: 有ExplicitPullbacks
  定义体: {
    hasProp := ⟨show TotallyDisconnectedSpace {_xy : _ | _} from inferInstance,
      show SecondCountableTopology {_xy : _ | _} from inferInstance⟩ }
-/
instance : HasExplicitPullbacks
    (fun Y => TotallyDisconnectedSpace Y ∧ SecondCountableTopology Y) where
  hasProp _ _ := {
    hasProp := ⟨show TotallyDisconnectedSpace {_xy : _ | _} from inferInstance,
      show SecondCountableTopology {_xy : _ | _} from inferInstance⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasExplicitFiniteCoproducts.{w, u}
  body: { hasProp :=
    ⟨show TotallyDisconnectedSpace (Σ (_a : _), _) from inferInstance,
      show SecondCountableTopology (Σ (_a : _), _) from inferInstance⟩ }

中文:
实例 :
  签名: 有ExplicitFiniteCoproducts.{w, u}
  定义体: { hasProp :=
    ⟨show TotallyDisconnectedSpace (Σ (_a : _), _) from inferInstance,
      show SecondCountableTopology (Σ (_a : _), _) from inferInstance⟩ }

Depends on / 依赖: hasProp
-/
instance : HasExplicitFiniteCoproducts.{w, u}
    (fun Y => TotallyDisconnectedSpace Y ∧ SecondCountableTopology Y) where
  hasProp _ := { hasProp :=
    ⟨show TotallyDisconnectedSpace (Σ (_a : _), _) from inferInstance,
      show SecondCountableTopology (Σ (_a : _), _) from inferInstance⟩ }

/--
Definition of `isTerminalPUnit` / `isTerminalPUnit` 的定义

English:
abbreviation isTerminalPUnit
  signature: : IsTerminal (LightProfinite.of PUnit.{u + 1})
  body: CompHausLike.isTerminalPUnit

中文:
缩写 isTerminalPUnit
  签名: : 是终止 (LightProfinite.of 命题单元.{u + 1})
  定义体: CompHausLike.isTerminalPUnit

Depends on / 依赖: CompHausLike, CompHausLike.isTerminalPUnit, isTerminalPUnit
-/
abbrev isTerminalPUnit : IsTerminal (LightProfinite.of PUnit.{u + 1}) :=
  CompHausLike.isTerminalPUnit

instance {X Y Z : LightProfinite} (f : X ⟶ Z) (g : Y ⟶ Z) [h : Epi g] :
    Epi (CompHausLike.pullback.fst f g) := by
  rw [LightProfinite.epi_iff_surjective] at h ⊢
  intro x
  obtain ⟨y, hy⟩ := h (f x)
  exact ⟨⟨⟨x, y⟩, hy.symm⟩, rfl⟩

instance {X Y Z : LightProfinite} (f : X ⟶ Z) (g : Y ⟶ Z) [h : Epi f] :
    Epi (CompHausLike.pullback.snd f g) := by
  rw [LightProfinite.epi_iff_surjective] at h ⊢
  intro y
  obtain ⟨x, hx⟩ := h (g y)
  exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩

example : FinitaryExtensive LightProfinite.{u} := inferInstance

noncomputable example : PreservesFiniteCoproducts lightProfiniteToCompHaus.{u} := inferInstance

end LightProfinite
