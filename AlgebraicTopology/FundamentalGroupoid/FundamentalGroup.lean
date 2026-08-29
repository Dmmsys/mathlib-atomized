/-
Copyright (c) 2021 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Path

/-!
# Fundamental group of a space

Given a topological space `X` and a basepoint `x`, the fundamental group is the automorphism group
of `x` i.e. the group with elements being loops based at `x` (quotiented by homotopy equivalence).
-/

@[expose] public section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ : X}

noncomputable section

open CategoryTheory

variable (X)

/--
Definition of `FundamentalGroup` / `FundamentalGroup` 的定义

English:
abbreviation FundamentalGroup
  signature: (x : X)
  body: End (FundamentalGroupoid.mk x)

中文:
缩写 FundamentalGroup
  签名: (x : X)
  定义体: End (FundamentalGroupoid.mk x)

Depends on / 依赖: FundamentalGroupoid, FundamentalGroupoid.mk
-/
abbrev FundamentalGroup (x : X) :=
  End (FundamentalGroupoid.mk x)

variable {X}

namespace FundamentalGroup

variable {x : X} {p q : FundamentalGroup X x}

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : FundamentalGroup X x) = .refl x
  proof: rfl

中文:
定理 one_def
  结论: (1 : FundamentalGroup X x) = .refl x
  证明: rfl
-/
theorem one_def : (1 : FundamentalGroup X x) = .refl x := rfl
/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  statement: p * q = q.trans p
  proof: rfl

中文:
定理 mul_def
  结论: p * q = q.trans p
  证明: rfl
-/
theorem mul_def : p * q = q.trans p := rfl
/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  statement: p⁻¹ = p.symm
  proof: rfl

中文:
定理 inv_def
  结论: p⁻¹ = p.symm
  证明: rfl
-/
theorem inv_def : p⁻¹ = p.symm := rfl

/--
Definition of `fundamentalGroupMulEquivOfPath` / `fundamentalGroupMulEquivOfPath` 的定义

English:
definition fundamentalGroupMulEquivOfPath
  signature: (p : Path x₀ x₁)
  body: ((Groupoid.isoEquivHom ..).symm ⟦p⟧).conj

中文:
定义 fundamentalGroupMulEquivOfPath
  签名: (p : Path x₀ x₁)
  定义体: ((Groupoid.isoEquivHom ..).symm ⟦p⟧).conj

Depends on / 依赖: Groupoid, Groupoid.isoEquivHom, isoEquivHom
-/
def fundamentalGroupMulEquivOfPath (p : Path x₀ x₁) :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  ((Groupoid.isoEquivHom ..).symm ⟦p⟧).conj

variable (x₀ x₁)

/--
Definition of `fundamentalGroupMulEquivOfPathConnected` / `fundamentalGroupMulEquivOfPathConnected` 的定义

English:
definition fundamentalGroupMulEquivOfPathConnected
  signature: [PathConnectedSpace X]
  body: fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath x₀ x₁)

中文:
定义 fundamentalGroupMulEquivOfPathConnected
  签名: [PathConnectedSpace X]
  定义体: fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath x₀ x₁)

Depends on / 依赖: PathConnectedSpace, PathConnectedSpace.somePath, fundamentalGroupMulEquivOfPath, somePath
-/
def fundamentalGroupMulEquivOfPathConnected [PathConnectedSpace X] :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath x₀ x₁)

/--
Definition of `toArrow` / `toArrow` 的定义

English:
abbreviation toArrow
  signature: {x : X} (p : FundamentalGroup X x)
  body: p

中文:
缩写 toArrow
  签名: {x : X} (p : FundamentalGroup X x)
  定义体: p
-/
abbrev toArrow {x : X} (p : FundamentalGroup X x) :
    FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x :=
  p

/--
Definition of `toPath` / `toPath` 的定义

English:
abbreviation toPath
  signature: {x : X} (p : FundamentalGroup X x)
  body: toArrow p

中文:
缩写 toPath
  签名: {x : X} (p : FundamentalGroup X x)
  定义体: toArrow p

Depends on / 依赖: toArrow
-/
abbrev toPath {x : X} (p : FundamentalGroup X x) : Path.Homotopic.Quotient x x :=
  toArrow p

/--
Definition of `fromArrow` / `fromArrow` 的定义

English:
abbreviation fromArrow
  signature: {x : X}
  body: p

中文:
缩写 fromArrow
  签名: {x : X}
  定义体: p
-/
abbrev fromArrow {x : X}
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) :
    FundamentalGroup X x :=
  p

/--
Definition of `fromPath` / `fromPath` 的定义

English:
abbreviation fromPath
  signature: {x : X} (p : Path.Homotopic.Quotient x x)
  body: fromArrow p

中文:
缩写 fromPath
  签名: {x : X} (p : Path.Homotopic.Quotient x x)
  定义体: fromArrow p

Depends on / 依赖: fromArrow
-/
abbrev fromPath {x : X} (p : Path.Homotopic.Quotient x x) : FundamentalGroup X x :=
  fromArrow p

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : C(X, Y)) (x : X)
  body: (FundamentalGroupoid.map f).mapEnd _

中文:
定义 map
  签名: (f : C(X, Y)) (x : X)
  定义体: (FundamentalGroupoid.map f).mapEnd _
-/
@[simps!] def map (f : C(X, Y)) (x : X) : FundamentalGroup X x ->* FundamentalGroup Y (f x) :=
  (FundamentalGroupoid.map f).mapEnd _

variable (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)

/--
Definition of `mapOfEq` / `mapOfEq` 的定义

English:
definition mapOfEq
  signature: : FundamentalGroup X x ->* FundamentalGroup Y y
  body: (eqToIso <| congr_arg FundamentalGroupoid.mk h).conj.toMonoidHom.comp (map f x)

中文:
定义 mapOfEq
  签名: : FundamentalGroup X x ->* FundamentalGroup Y y
  定义体: (eqToIso <| congr_arg FundamentalGroupoid.mk h).conj.toMonoidHom.comp (map f x)

Depends on / 依赖: FundamentalGroupoid, FundamentalGroupoid.mk, congr_arg, conj.toMonoidHom.comp, eqToIso, toMonoidHom
-/
def mapOfEq : FundamentalGroup X x ->* FundamentalGroup Y y :=
  (eqToIso <| congr_arg FundamentalGroupoid.mk h).conj.toMonoidHom.comp (map f x)

/--
theorem `mapOfEq_apply` / 定理 `mapOfEq_apply`

English:
theorem mapOfEq_apply
  given: (p : FundamentalGroup X x)
  proof: FundamentalGroupoid.conj_eqToHom ..

中文:
定理 mapOfEq_apply
  条件: (p : FundamentalGroup X x)
  证明: FundamentalGroupoid.conj_eqToHom ..

Depends on / 依赖: FundamentalGroupoid, FundamentalGroupoid.conj_eqToHom, conj_eqToHom
-/
theorem mapOfEq_apply (p : FundamentalGroup X x) :
    mapOfEq f h p = (Path.Homotopic.Quotient.map p f).cast h.symm h.symm :=
  FundamentalGroupoid.conj_eqToHom ..

end FundamentalGroup
