/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Algebraic elements and algebraic extensions

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.

## Main definitions

* `IsAlgebraic`: algebraic elements of an algebra.
* `Transcendental`: transcendental elements of an algebra are those that are not algebraic.
* `Subalgebra.IsAlgebraic`: a subalgebra is algebraic if all its elements are algebraic.
* `Algebra.IsAlgebraic`: an algebra is algebraic if all its elements are algebraic.
* `Algebra.Transcendental`: an algebra is transcendental if some element is transcendental.

## Main results

* `transcendental_iff`: an element `x : A` is transcendental over `R` iff out of `R[X]`
  only the zero polynomial evaluates to 0 at `x`.
* `Subalgebra.isAlgebraic_iff`: a subalgebra is algebraic iff it is algebraic as an algebra.
-/

@[expose] public section

assert_not_exists IsIntegralClosure LinearIndependent IsLocalRing MvPolynomial

universe u v w
open Polynomial

section

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- An element of an R-algebra is algebraic over R if it is a root of a nonzero polynomial
with coefficients in R. -/
@[stacks 09GC "Algebraic elements"]
/--
Definition of `IsAlgebraic` / `IsAlgebraic` 的定义

English:
definition IsAlgebraic
  signature: (x : A)
  body: exists p : R[X], p != 0 ∧ aeval x p = 0

中文:
定义 是代数
  签名: (x : A)
  定义体: exists p : R[X], p != 0 ∧ aeval x p = 0
-/
def IsAlgebraic (x : A) : Prop :=
  exists p : R[X], p != 0 ∧ aeval x p = 0

/--
Definition of `Transcendental` / `Transcendental` 的定义

English:
definition Transcendental
  signature: (x : A)
  body: ¬IsAlgebraic R x

中文:
定义 超越
  签名: (x : A)
  定义体: ¬IsAlgebraic R x

Depends on / 依赖: IsAlgebraic
-/
def Transcendental (x : A) : Prop :=
  ¬IsAlgebraic R x

variable {R}

/--
theorem `transcendental_iff` / 定理 `transcendental_iff`

English:
theorem transcendental_iff
  given: {x : A}
  proof: by
  rw [Transcendental]; rw [IsAlgebraic]; rw [not_exists]
  congr! 1; tauto

中文:
定理 transcendental_iff
  条件: {x : A}
  证明: by
  rw [Transcendental]; rw [IsAlgebraic]; rw [not_exists]
  congr! 1; tauto

Depends on / 依赖: IsAlgebraic, Transcendental, not_exists
-/
theorem transcendental_iff {x : A} :
    Transcendental R x ↔ forall p : R[X], aeval x p = 0 -> p = 0 := by
  rw [Transcendental]; rw [IsAlgebraic]; rw [not_exists]
  congr! 1; tauto

/--
Definition of `Subalgebra.IsAlgebraic` / `Subalgebra.IsAlgebraic` 的定义

English:
definition Subalgebra.IsAlgebraic
  signature: (S : Subalgebra R A)
  body: forall x in S, IsAlgebraic R x

中文:
定义 子代数.是代数
  签名: (S : 子代数 R A)
  定义体: forall x in S, IsAlgebraic R x
-/
protected def Subalgebra.IsAlgebraic (S : Subalgebra R A) : Prop :=
  forall x in S, IsAlgebraic R x

variable (R A) in
/-- An algebra is algebraic if all its elements are algebraic. -/
@[stacks 09GC "Algebraic extensions"]
/--
Definition of `Algebra.IsAlgebraic` / `Algebra.IsAlgebraic` 的定义

English:
class Algebra.IsAlgebraic
  parameters: : Prop where
  axioms and operations (1):
    - isAlgebraic : forall x : A, IsAlgebraic R x

中文:
类 代数.是代数
  参数: : 命题 where
  公理与运算 (1 个):
    - isAlgebraic : 对任意 x : A, 是代数 R x
-/
protected class Algebra.IsAlgebraic : Prop where
  isAlgebraic : forall x : A, IsAlgebraic R x

variable (R A) in
/--
Definition of `Algebra.Transcendental` / `Algebra.Transcendental` 的定义

English:
class Algebra.Transcendental
  parameters: : Prop where
  axioms and operations (1):
    - transcendental : exists x : A, Transcendental R x

中文:
类 代数.超越
  参数: : 命题 where
  公理与运算 (1 个):
    - transcendental : 存在 x : A, 超越 R x
-/
protected class Algebra.Transcendental : Prop where
  transcendental : exists x : A, Transcendental R x

variable (R A) in
/--
lemma `Algebra.nontrivial_of_isAlgebraic` / 引理 `Algebra.nontrivial_of_isAlgebraic`

English:
lemma Algebra.nontrivial_of_isAlgebraic
  given: [Algebra.IsAlgebraic R A]
  statement: Nontrivial R
  proof: by
  obtain ⟨p, hp, -⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) (0 : A)
  exact .of_polynomial_ne hp

中文:
引理 代数.nontrivial_of_isAlgebraic
  条件: [代数.是代数 R A]
  结论: 非平凡 R
  证明: by
  obtain ⟨p, hp, -⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) (0 : A)
  exact .of_polynomial_ne hp

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, isAlgebraic, of_polynomial_ne
-/
lemma Algebra.nontrivial_of_isAlgebraic [Algebra.IsAlgebraic R A] : Nontrivial R := by
  obtain ⟨p, hp, -⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) (0 : A)
  exact .of_polynomial_ne hp

/--
lemma `Algebra.isAlgebraic_def` / 引理 `Algebra.isAlgebraic_def`

English:
lemma Algebra.isAlgebraic_def
  statement: Algebra.IsAlgebraic R A ↔ forall x : A, IsAlgebraic R x
  proof: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

中文:
引理 代数.isAlgebraic_def
  结论: 代数.是代数 R A ↔ 对任意 x : A, 是代数 R x
  证明: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
-/
lemma Algebra.isAlgebraic_def : Algebra.IsAlgebraic R A ↔ forall x : A, IsAlgebraic R x :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/--
lemma `Algebra.transcendental_def` / 引理 `Algebra.transcendental_def`

English:
lemma Algebra.transcendental_def
  statement: Algebra.Transcendental R A ↔ exists x : A, Transcendental R x
  proof: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

中文:
引理 代数.transcendental_def
  结论: 代数.超越 R A ↔ 存在 x : A, 超越 R x
  证明: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
-/
lemma Algebra.transcendental_def : Algebra.Transcendental R A ↔ exists x : A, Transcendental R x :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/--
theorem `Algebra.transcendental_iff_not_isAlgebraic` / 定理 `Algebra.transcendental_iff_not_isAlgebraic`

English:
theorem Algebra.transcendental_iff_not_isAlgebraic
  proof: by
  simp [isAlgebraic_def, transcendental_def, Transcendental]

中文:
定理 代数.transcendental_iff_not_isAlgebraic
  证明: by
  simp [isAlgebraic_def, transcendental_def, Transcendental]

Depends on / 依赖: Transcendental, isAlgebraic_def, transcendental_def
-/
theorem Algebra.transcendental_iff_not_isAlgebraic :
    Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A := by
  simp [isAlgebraic_def, transcendental_def, Transcendental]

/--
theorem `Subalgebra.isAlgebraic_iff` / 定理 `Subalgebra.isAlgebraic_iff`

English:
theorem Subalgebra.isAlgebraic_iff
  given: (S : Subalgebra R A)
  proof: by
  delta Subalgebra.IsAlgebraic
  rw [Subtype.forall']; rw [Algebra.isAlgebraic_def]
  refine forall_congr' fun x => exists_congr fun p => and_congr Iff.rfl ?_
  have h : Function.Injective S.val := Subtype.val_injective
  conv_rhs => rw [← h.eq_iff, map_zero]
  rw [← aeval_algHom_apply]; rw [S.va

中文:
定理 子代数.isAlgebraic_iff
  条件: (S : 子代数 R A)
  证明: by
  delta Subalgebra.IsAlgebraic
  rw [Subtype.forall']; rw [Algebra.isAlgebraic_def]
  refine forall_congr' fun x => exists_congr fun p => and_congr Iff.rfl ?_
  have h : Function.Injective S.val := Subtype.val_injective
  conv_rhs => rw [← h.eq_iff, map_zero]
  rw [← aeval_algHom_apply]; rw [S.va

Depends on / 依赖: Algebra, Algebra.isAlgebraic_def, Function, Function.Injective, Iff.rfl, Injective, IsAlgebraic, S.val, S.val_apply, Subalgebra, Subalgebra.IsAlgebraic, Subtype, Subtype.forall, Subtype.val_injective, aeval_algHom_apply, and_congr, conv_rhs, eq_iff, exists_congr, forall_congr
-/
theorem Subalgebra.isAlgebraic_iff (S : Subalgebra R A) :
    S.IsAlgebraic ↔ Algebra.IsAlgebraic R S := by
  delta Subalgebra.IsAlgebraic
  rw [Subtype.forall']; rw [Algebra.isAlgebraic_def]
  refine forall_congr' fun x => exists_congr fun p => and_congr Iff.rfl ?_
  have h : Function.Injective S.val := Subtype.val_injective
  conv_rhs => rw [← h.eq_iff, map_zero]
  rw [← aeval_algHom_apply]; rw [S.val_apply]

/--
theorem `Algebra.isAlgebraic_iff` / 定理 `Algebra.isAlgebraic_iff`

English:
theorem Algebra.isAlgebraic_iff
  statement: Algebra.IsAlgebraic R A ↔ (⊤ : Subalgebra R A).IsAlgebraic
  proof: by
  delta Subalgebra.IsAlgebraic
  simp only [Algebra.isAlgebraic_def, Algebra.mem_top, forall_prop_of_true]

中文:
定理 代数.isAlgebraic_iff
  结论: 代数.是代数 R A ↔ (⊤ : 子代数 R A).是代数
  证明: by
  delta Subalgebra.IsAlgebraic
  simp only [Algebra.isAlgebraic_def, Algebra.mem_top, forall_prop_of_true]

Depends on / 依赖: Algebra, Algebra.isAlgebraic_def, Algebra.mem_top, IsAlgebraic, Subalgebra, Subalgebra.IsAlgebraic, forall_prop_of_true, isAlgebraic_def, mem_top
-/
theorem Algebra.isAlgebraic_iff : Algebra.IsAlgebraic R A ↔ (⊤ : Subalgebra R A).IsAlgebraic := by
  delta Subalgebra.IsAlgebraic
  simp only [Algebra.isAlgebraic_def, Algebra.mem_top, forall_prop_of_true]

end
