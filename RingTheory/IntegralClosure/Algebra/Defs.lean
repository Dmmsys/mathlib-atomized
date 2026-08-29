/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# Integral algebras

## Main definitions

Let `R` be a `CommRing` and let `A` be an R-algebra.

* `Algebra.IsIntegral R A` : An algebra is integral if every element of the extension is integral
  over the base ring.
-/

public section


open Polynomial Submodule

section Ring

variable {R S A : Type*}
variable [CommRing R] [Ring A] [Ring S] (f : R ->+* S)

variable [Algebra R A] (R)

variable (A)

/--
Definition of `Algebra.IsIntegral` / `Algebra.IsIntegral` 的定义

English:
class Algebra.IsIntegral
  parameters: : Prop where
  axioms and operations (1):
    - isIntegral : forall x : A, IsIntegral R x

中文:
类 Algebra.IsIntegral
  参数: : 命题 where
  公理与运算 (1 个):
    - isIntegral : 对任意 x : A, Is整数egral R x
-/
@[mk_iff] protected class Algebra.IsIntegral : Prop where
  isIntegral : forall x : A, IsIntegral R x

variable {R A}

/--
lemma `Algebra.isIntegral_def` / 引理 `Algebra.isIntegral_def`

English:
lemma Algebra.isIntegral_def
  statement: Algebra.IsIntegral R A ↔ forall x : A, IsIntegral R x
  proof: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

中文:
引理 Algebra.isIntegral_def
  结论: Algebra.Is整数egral R A ↔ 对任意 x : A, Is整数egral R x
  证明: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
-/
lemma Algebra.isIntegral_def : Algebra.IsIntegral R A ↔ forall x : A, IsIntegral R x :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/--
lemma `algebraMap_isIntegral_iff` / 引理 `algebraMap_isIntegral_iff`

English:
lemma algebraMap_isIntegral_iff
  statement: (algebraMap R A).IsIntegral ↔ Algebra.IsIntegral R A
  proof: (Algebra.isIntegral_iff ..).symm

中文:
引理 algebraMap_isIntegral_iff
  结论: (algebraMap R A).Is整数egral ↔ Algebra.Is整数egral R A
  证明: (Algebra.isIntegral_iff ..).symm

Depends on / 依赖: Algebra, Algebra.isIntegral_iff, isIntegral_iff
-/
lemma algebraMap_isIntegral_iff : (algebraMap R A).IsIntegral ↔ Algebra.IsIntegral R A :=
  (Algebra.isIntegral_iff ..).symm

end Ring
