/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.FiniteType

/-!
# Minimal polynomials on a finite algebra

This file proves the bound on the degree of a minimal polynomial on an algebra
that is finite as a module.

-/

public section

variable {A B : Type*} [CommRing A] [Ring B] [Algebra A B] [Module.Finite A B] (x : B)

open Polynomial

namespace minpoly

variable (A) in
/-
**minpoly.natDegree_le_spanFinrank** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：natDegree_le_spanFinrank : (minpoly A x).natDegree <= (⊤ : Submodule A B).
spanFinrank
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero`：LinearMap.exi
sts_monic_and_natDegree_eq_and_aeval_eq_zero [Module.Finite R M] (f : Module.End
 R M) : exists p : R[X], p.Monic ∧ p.natDegree …
· 使用定理 `Polynomial.natDegree_le_natDegree`：natDegree_le_natDegree [Semiring S] {
q : S[X]} (hpq : p.degree <= q.degree) : p.natDegree <= q.natDegree
· 使用定理 `minpoly.min`：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x 
p = 0) : degree (minpoly A x) <= degree p
· 使用定理 `Algebra.lmul_injective`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemi
ring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   Function.Injective ⇑(Alg
ebra.lmul R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
-/
theorem natDegree_le_spanFinrank :
    (minpoly A x).natDegree ≤ (⊤ : Submodule A B).spanFinrank := by
  rcases LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero _ (Algebra.lmul A _ x) with
    ⟨f, f_monic, f_deg, f_aeval⟩
  refine f_deg ▸ (natDegree_le_natDegree <| minpoly.min _ _ f_monic ?_)
  rw [aeval_algHom_apply] at f_aeval
  exact Algebra.lmul_injective (R := A) <| by simpa using f_aeval
/-
**minpoly.natDegree_le** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：natDegree_le [Module.Free A B] : (minpoly A x).natDegree <= Module.finrank
 A B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `Module.finrank_subsingleton`：∀ {R : Type u} {M : Type v} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Subsingleton R],
 Module.finrank R…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `Module.finrank_eq_spanFinrank_of_free`：Module.finrank_eq_spanFinrank_of_
free [StrongRankCondition R] [Module.Free R M] : Module.finrank R M = (⊤ : Submo
dule R M).spanFinrank
· 使用定理 `strongRankCondition_of_orzechProperty`：∀ (R : Type u) [inst : Semiring R
] [Nontrivial R] [OrzechProperty R], StrongRankCondition R
· 使用定理 `CommRing.orzechProperty`：∀ (R : Type u_1) [inst : CommRing R], OrzechPro
perty R
· 使用定理 `minpoly.natDegree_le_spanFinrank`：natDegree_le_spanFinrank : (minpoly A 
x).natDegree <= (⊤ : Submodule A B).spanFinrank
-/
theorem natDegree_le [Module.Free A B] : (minpoly A x).natDegree ≤ Module.finrank A B := by
  nontriviality A
  simpa [Module.finrank_eq_spanFinrank_of_free] using natDegree_le_spanFinrank A x
/-
**minpoly.degree_le** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：degree_le [Module.Free A B] : (minpoly A x).degree <= Module.finrank A B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_le_of_natDegree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.natDegree ≤ n → p.degree ≤ ↑n
· 使用定理 `minpoly.natDegree_le`：natDegree_le [Module.Free A B] : (minpoly A x).nat
Degree <= Module.finrank A B
-/
theorem degree_le [Module.Free A B] : (minpoly A x).degree ≤ Module.finrank A B :=
  degree_le_of_natDegree_le <| natDegree_le x

end minpoly

