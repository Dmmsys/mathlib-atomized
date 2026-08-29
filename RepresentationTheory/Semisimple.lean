/-
Copyright (c) 2026 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity

/-!
# Semisimple representations

This file defines the typeclass `IsSemisimpleRepresentation` for semisimple monoid representations.

-/

namespace Representation

variable {k G V : Type*}

public section

open scoped MonoidAlgebra

variable [Monoid G] [Field k] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/--
Definition of `IsSemisimpleRepresentation` / `IsSemisimpleRepresentation` 的定义

English:
abbreviation IsSemisimpleRepresentation
  body: ComplementedLattice (Subrepresentation ρ)

中文:
缩写 IsSemisimpleRepresentation
  定义体: ComplementedLattice (Subrepresentation ρ)

Depends on / 依赖: ComplementedLattice, Subrepresentation
-/
abbrev IsSemisimpleRepresentation :=
  ComplementedLattice (Subrepresentation ρ)

/--
theorem `isSemisimpleRepresentation_iff_isSemisimpleModule_asModule` / 定理 `isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`

English:
theorem isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
  proof: by
  rw [isSemisimpleModule_iff]
  exact OrderIso.complementedLattice_iff Subrepresentation.subrepresentationSubmoduleOrderIso

中文:
定理 isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
  证明: by
  rw [isSemisimpleModule_iff]
  exact OrderIso.complementedLattice_iff Subrepresentation.subrepresentationSubmoduleOrderIso

Depends on / 依赖: OrderIso, OrderIso.complementedLattice_iff, Subrepresentation, Subrepresentation.subrepresentationSubmoduleOrderIso, complementedLattice_iff, isSemisimpleModule_iff, subrepresentationSubmoduleOrderIso
-/
theorem isSemisimpleRepresentation_iff_isSemisimpleModule_asModule :
    IsSemisimpleRepresentation ρ ↔ IsSemisimpleModule k[G] ρ.asModule := by
  rw [isSemisimpleModule_iff]
  exact OrderIso.complementedLattice_iff Subrepresentation.subrepresentationSubmoduleOrderIso

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isSemisimpleModule_iff_isSemisimpleRepresentation_ofModule` / 定理 `isSemisimpleModule_iff_isSemisimpleRepresentation_ofModule`

English:
theorem isSemisimpleModule_iff_isSemisimpleRepresentation_ofModule
  statement: (M : Type*) [AddCommGroup M]
  proof: by
  rw [isSemisimpleModule_iff]
  exact OrderIso.complementedLattice_iff Subrepresentation.submoduleSubrepresentationOrderIso

中文:
定理 isSemisimpleModule_iff_isSemisimpleRepresentation_ofModule
  结论: (M : 类型) [AddCommGroup M]
  证明: by
  rw [isSemisimpleModule_iff]
  exact OrderIso.complementedLattice_iff Subrepresentation.submoduleSubrepresentationOrderIso

Depends on / 依赖: OrderIso, OrderIso.complementedLattice_iff, Subrepresentation, Subrepresentation.submoduleSubrepresentationOrderIso, complementedLattice_iff, isSemisimpleModule_iff, submoduleSubrepresentationOrderIso
-/
theorem isSemisimpleModule_iff_isSemisimpleRepresentation_ofModule (M : Type*) [AddCommGroup M]
    [Module k[G] M] :
    IsSemisimpleModule k[G] M ↔ IsSemisimpleRepresentation (ofModule (k := k) (G := G) M) := by
  rw [isSemisimpleModule_iff]
  exact OrderIso.complementedLattice_iff Subrepresentation.submoduleSubrepresentationOrderIso

end

end Representation
