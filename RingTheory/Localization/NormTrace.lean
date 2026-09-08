/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Discriminant

/-!

# Field/algebra norm / trace and localization

This file contains results on the combination of `IsLocalization` and `Algebra.norm`,
`Algebra.trace` and `Algebra.discr`.

## Main results

* `Algebra.norm_localization`: let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M`
  of `R S` respectively. Then the norm of `a : Sₘ` over `Rₘ` is the norm of `a : S` over `R`
  if `S` is free as `R`-module.

* `Algebra.trace_localization`: let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M`
  of `R S` respectively. Then the trace of `a : Sₘ` over `Rₘ` is the trace of `a : S` over `R`
  if `S` is free as `R`-module.

* `Algebra.discr_localizationLocalization`: let `S` be an extension of `R` and `Rₘ Sₘ` be
  localizations at `M` of `R S` respectively. Let `b` be an `R`-basis of `S`. Then discriminant of
  the `Rₘ`-basis of `Sₘ` induced by `b` is the discriminant of `b`.

## Tags

field norm, algebra norm, localization

-/

public section

open Module
open scoped nonZeroDivisors

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {Rₘ Sₘ : Type*} [CommRing Rₘ] [Algebra R Rₘ] [CommRing Sₘ] [Algebra S Sₘ]
variable (M : Submonoid R)
variable [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
variable [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
include M
open Algebra

/-
**Algebra.map_leftMulMatrix_localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.map_leftMulMatrix_localization {ι : Type*} [Fintype ι] [DecidableE
q ι] (b : Basis ι R S) (a : S) : (algebraMap R Rₘ).mapMatrix (leftMulMatrix b a)
 = leftMulMatrix (b.localizationLocalization Rₘ M Sₘ) (algebraMap S Sₘ a)
参数：b : Basis ι R S；a : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Algebra.leftMulMatrix_eq_repr_mul`：leftMulMatrix_eq_repr_mul (x : S) (i 
j) : leftMulMatrix b x i j = b.repr (x * b j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.localizationLocalization_apply`：localizationLocalization_ap
ply {ι : Type*} (b : Basis ι R A) (i) : b.localizationLocalization Rₛ S Aₛ i = a
lgebraMap A Aₛ (b i)
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Module.Basis.localizationLocalization_repr_algebraMap`：localizationLocal
ization_repr_algebraMap {ι : Type*} (b : Basis ι R A) (x i) : (b.localizationLoc
alization Rₛ S Aₛ).repr (algebraMap A Aₛ x)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Algebra.map_leftMulMatrix_localization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι R S) (a : S) :
    (algebraMap R Rₘ).mapMatrix (leftMulMatrix b a) =
    leftMulMatrix (b.localizationLocalization Rₘ M Sₘ) (algebraMap S Sₘ a) := by
  ext i j
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, leftMulMatrix_eq_repr_mul, ← map_mul,
    Basis.localizationLocalization_apply, Basis.localizationLocalization_repr_algebraMap]

/-- Let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M` of `R S` respectively.
Then the norm of `a : Sₘ` over `Rₘ` is the norm of `a : S` over `R` if `S` is free as `R`-module.
-/
/-
**Algebra.norm_localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.norm_localization [Module.Free R S] [Module.Finite R S] (a : S) : 
Algebra.norm Rₘ (algebraMap S Sₘ a) = algebraMap R Rₘ (Algebra.norm R a)
参数：a : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_eq_matrix_det`：norm_eq_matrix_det [Fintype ι] [DecidableEq 
ι] (b : Basis ι R S) (s : S) : norm R s = Matrix.det (Algebra.leftMulMatrix b s)
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.map_leftMulMatrix_localization`：Algebra.map_leftMulMatrix_locali
zation {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (a : S) : (alge
braMap R Rₘ).mapMatrix (left…

--- 原说明 ---
Let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M` of `R S` resp
ectively.
Then the norm of `a : Sₘ` over `Rₘ` is the norm of `a : S` over `R` if `S` is fr
ee as `R`-module.
-/
theorem Algebra.norm_localization [Module.Free R S] [Module.Finite R S] (a : S) :
    Algebra.norm Rₘ (algebraMap S Sₘ a) = algebraMap R Rₘ (Algebra.norm R a) := by
  cases subsingleton_or_nontrivial R
  · have : Subsingleton Rₘ := Module.subsingleton R Rₘ
    simp [eq_iff_true_of_subsingleton]
  let b := Module.Free.chooseBasis R S
  let := Classical.decEq (Module.Free.ChooseBasisIndex R S)
  rw [Algebra.norm_eq_matrix_det (b.localizationLocalization Rₘ M Sₘ),
    Algebra.norm_eq_matrix_det b, RingHom.map_det, ← Algebra.map_leftMulMatrix_localization]

variable {M} in
/-- The norm of `a : S` in `R` can be computed in `Sₘ`. -/
/-
**Algebra.norm_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.norm_eq_iff [Module.Free R S] [Module.Finite R S] {a : S} {b : R} 
(hM : M <= nonZeroDivisors R) : Algebra.norm R a = b ↔ (Algebra.norm Rₘ) ((algeb
raMap S Sₘ) a) = algebraMap R Rₘ b
参数：hM : M <= nonZeroDivisors R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.norm_localization`：Algebra.norm_localization [Module.Free R S] [
Module.Finite R S] (a : S) : Algebra.norm Rₘ (algebraMap S Sₘ a) = algebraMap R 
Rₘ (Algebra.nor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…

--- 原说明 ---
The norm of `a : S` in `R` can be computed in `Sₘ`.
-/
lemma Algebra.norm_eq_iff [Module.Free R S] [Module.Finite R S] {a : S} {b : R}
    (hM : M ≤ nonZeroDivisors R) : Algebra.norm R a = b ↔
      (Algebra.norm Rₘ) ((algebraMap S Sₘ) a) = algebraMap R Rₘ b :=
  ⟨fun h ↦ h.symm ▸ Algebra.norm_localization _ M _, fun h ↦
    IsLocalization.injective Rₘ hM <| h.symm ▸ (Algebra.norm_localization R M a).symm⟩

/-- Let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M` of `R S` respectively.
Then the trace of `a : Sₘ` over `Rₘ` is the trace of `a : S` over `R` if `S` is free as `R`-module.
-/
/-
**Algebra.trace_localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.trace_localization [Module.Free R S] [Module.Finite R S] (a : S) :
 Algebra.trace Rₘ Sₘ (algebraMap S Sₘ a) = algebraMap R Rₘ (Algebra.trace R S a)
参数：a : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.trace_eq_matrix_trace`：trace_eq_matrix_trace [DecidableEq ι] (b 
: Basis ι R S) (s : S) : trace R S s = Matrix.trace (Algebra.leftMulMatrix b s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.map_leftMulMatrix_localization`：Algebra.map_leftMulMatrix_locali
zation {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (a : S) : (alge
braMap R Rₘ).mapMatrix (left…
· 使用定理 `AddMonoidHom.map_trace`：∀ {n : Type u_3} {R : Type u_6} {S : Type u_7} [
inst : Fintype n] [inst_1 : AddCommMonoid R] [inst_2 : AddCommMonoid S]   {F : T
ype u_8} [in…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
Let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M` of `R S` resp
ectively.
Then the trace of `a : Sₘ` over `Rₘ` is the trace of `a : S` over `R` if `S` is 
free as `R`-module.
-/
theorem Algebra.trace_localization [Module.Free R S] [Module.Finite R S] (a : S) :
    Algebra.trace Rₘ Sₘ (algebraMap S Sₘ a) = algebraMap R Rₘ (Algebra.trace R S a) := by
  cases subsingleton_or_nontrivial R
  · have : Subsingleton Rₘ := Module.subsingleton R Rₘ
    simp [eq_iff_true_of_subsingleton]
  let b := Module.Free.chooseBasis R S
  let := Classical.decEq (Module.Free.ChooseBasisIndex R S)
  rw [Algebra.trace_eq_matrix_trace (b.localizationLocalization Rₘ M Sₘ),
    Algebra.trace_eq_matrix_trace b, ← Algebra.map_leftMulMatrix_localization]
  exact (AddMonoidHom.map_trace (algebraMap R Rₘ).toAddMonoidHom _).symm

section LocalizationLocalization

variable (Sₘ : Type*) [CommRing Sₘ] [Algebra S Sₘ] [Algebra Rₘ Sₘ] [Algebra R Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-
**Algebra.traceMatrix_localizationLocalization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.traceMatrix_localizationLocalization (b : Basis ι R S) : Algebra.t
raceMatrix Rₘ (b.localizationLocalization Rₘ M Sₘ) = (algebraMap R Rₘ).mapMatrix
 (Algebra.traceMatrix R b)
参数：b : Basis ι R S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.localizationLocalization_apply`：localizationLocalization_ap
ply {ι : Type*} (b : Basis ι R A) (i) : b.localizationLocalization Rₛ S Aₛ i = a
lgebraMap A Aₛ (b i)
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Algebra.trace_localization`：Algebra.trace_localization [Module.Free R S]
 [Module.Finite R S] (a : S) : Algebra.trace Rₘ Sₘ (algebraMap S Sₘ a) = algebra
Map R Rₘ (Algebr…
-/
theorem Algebra.traceMatrix_localizationLocalization (b : Basis ι R S) :
    Algebra.traceMatrix Rₘ (b.localizationLocalization Rₘ M Sₘ) =
      (algebraMap R Rₘ).mapMatrix (Algebra.traceMatrix R b) := by
  have : Module.Finite R S := Module.Finite.of_basis b
  have : Module.Free R S := Module.Free.of_basis b
  ext i j : 2
  simp_rw [RingHom.mapMatrix_apply, Matrix.map_apply, traceMatrix_apply, traceForm_apply,
    Basis.localizationLocalization_apply, ← map_mul]
  exact Algebra.trace_localization R M _

/-- Let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M` of `R S` respectively. Let
`b` be an `R`-basis of `S`. Then discriminant of the `Rₘ`-basis of `Sₘ` induced by `b` is the
discriminant of `b`.
-/
/-
**Algebra.discr_localizationLocalization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.discr_localizationLocalization (b : Basis ι R S) : Algebra.discr R
ₘ (b.localizationLocalization Rₘ M Sₘ) = algebraMap R Rₘ (Algebra.discr R b)
参数：b : Basis ι R S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.discr_def`：discr_def [Fintype ι] (b : ι -> B) : discr A b = (tra
ceMatrix A b).det
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `Algebra.traceMatrix_localizationLocalization`：Algebra.traceMatrix_locali
zationLocalization (b : Basis ι R S) : Algebra.traceMatrix Rₘ (b.localizationLoc
alization Rₘ M Sₘ) = (algebraMap R…

--- 原说明 ---
Let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M` of `R S` resp
ectively. Let
`b` be an `R`-basis of `S`. Then discriminant of the `Rₘ`-basis of `Sₘ` induced 
by `b` is the
discriminant of `b`.
-/
theorem Algebra.discr_localizationLocalization (b : Basis ι R S) :
    Algebra.discr Rₘ (b.localizationLocalization Rₘ M Sₘ) =
    algebraMap R Rₘ (Algebra.discr R b) := by
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det,
    Algebra.traceMatrix_localizationLocalization]

end LocalizationLocalization

