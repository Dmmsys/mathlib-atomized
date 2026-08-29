/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-! # Augmentation ideals

* `Ideal.IsAugmentation` : An ideal `I` of an `A`-algebra `S` is an augmentation ideal
  if its underlying submodule is a complement of `1 : Submodule A S`.

* `Ideal.isAugmentation_subalgebra_iff` : If `S` is a subalgebra of an `R`-algebra `A`,
  then an ideal `I`of `A` is an augmentation ideal for the `R`-algebra structure if and only if
  it is an augmentation ideal for the `S`-algebra structure.

-/

@[expose] public section

namespace Ideal

variable (R : Type*) [CommSemiring R] {A : Type*}

open Submodule Subalgebra

/--
Definition of `IsAugmentation` / `IsAugmentation` 的定义

English:
definition IsAugmentation
  signature: [Semiring A] [Algebra R A] (I : Ideal A)
  body: IsCompl 1 (I.restrictScalars R)

中文:
定义 IsAugmentation
  签名: [Semiring A] [Algebra R A] (I : Ideal A)
  定义体: IsCompl 1 (I.restrictScalars R)

Depends on / 依赖: I.restrictScalars, IsCompl, restrictScalars
-/
def IsAugmentation [Semiring A] [Algebra R A] (I : Ideal A) : Prop :=
  IsCompl 1 (I.restrictScalars R)

/--
lemma `isAugmentation_iff` / 引理 `isAugmentation_iff`

English:
lemma isAugmentation_iff
  given: [Semiring A] [Algebra R A] (I : Ideal A)
  proof: Iff.rfl

中文:
引理 isAugmentation_iff
  条件: [Semiring A] [Algebra R A] (I : Ideal A)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isAugmentation_iff [Semiring A] [Algebra R A] (I : Ideal A) :
    I.IsAugmentation R ↔ IsCompl 1 (I.restrictScalars R) := Iff.rfl

/--
theorem `isAugmentation_subalgebra_iff` / 定理 `isAugmentation_subalgebra_iff`

English:
theorem isAugmentation_subalgebra_iff
  statement: [CommSemiring A] [Algebra R A]
  proof: by
  simp [Ideal.IsAugmentation, ← Submodule.isCompl_restrictScalars_iff R]

中文:
定理 isAugmentation_subalgebra_iff
  结论: [CommSemiring A] [Algebra R A]
  证明: by
  simp [Ideal.IsAugmentation, ← Submodule.isCompl_restrictScalars_iff R]

Depends on / 依赖: Ideal.IsAugmentation, IsAugmentation, Submodule, Submodule.isCompl_restrictScalars_iff, isCompl_restrictScalars_iff
-/
theorem isAugmentation_subalgebra_iff [CommSemiring A] [Algebra R A]
    {S : Subalgebra R A} {I : Ideal A} :
    I.IsAugmentation S ↔ IsCompl S.toSubmodule (I.restrictScalars R) := by
  simp [Ideal.IsAugmentation, ← Submodule.isCompl_restrictScalars_iff R]

end Ideal

end
