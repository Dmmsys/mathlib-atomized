/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Subsingleton
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!

# Some results on the ranks of subalgebras

This file contains some results on the ranks of subalgebras,
which are corollaries of `rank_mul_rank`.
Since their proof essentially depends on the fact that a non-trivial commutative ring
satisfies the strong rank condition, we put them into a separate file.

-/

public section

open Module

namespace Subalgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A B : Subalgebra R S)

section
variable [Module.Free R A] [Module.Free A (Algebra.adjoin A (B : Set S))]

/-
**Subalgebra.rank_sup_eq_rank_left_mul_rank_of_free** 是 Mathlib 中的一个定理，位于命名空间 `S
ubalgebra`。
形式化陈述：rank_sup_eq_rank_left_mul_rank_of_free : Module.rank R ↥(A ⊔ B) = Module.r
ank R A * Module.rank A (Algebra.adjoin A (B : Set S))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `rank_subsingleton'`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsin
gleton M…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `rank_mul_rank`：rank_mul_rank (A : Type v) [AddCommMonoid A] [Module K A]
 [Module F A] [IsScalarTower F K A] [Module.Free K A] : Module.rank F K * Module
.ra…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Algebra.restrictScalars_adjoin`：Algebra.restrictScalars_adjoin (F : Type
*) [CommSemiring F] {E : Type*} [CommSemiring E] [Algebra F E] (K : Subalgebra F
 E) (S : Set E) : (A…
-/
theorem rank_sup_eq_rank_left_mul_rank_of_free :
    Module.rank R ↥(A ⊔ B) = Module.rank R A * Module.rank A (Algebra.adjoin A (B : Set S)) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have := Module.subsingleton R S; simp
  nontriviality S using rank_subsingleton'
  let : Algebra A (Algebra.adjoin A (B : Set S)) := Subalgebra.algebra _
  let : SMul A (Algebra.adjoin A (B : Set S)) := Algebra.toSMul
  have : IsScalarTower R A (Algebra.adjoin A (B : Set S)) :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [rank_mul_rank R A (Algebra.adjoin A (B : Set S))]
  change _ = Module.rank R ((Algebra.adjoin A (B : Set S)).restrictScalars R)
  rw [Algebra.restrictScalars_adjoin]; rfl
/-
**Subalgebra.finrank_sup_eq_finrank_left_mul_finrank_of_free** 是 Mathlib 中的一个定理，
位于命名空间 `Subalgebra`。
形式化陈述：finrank_sup_eq_finrank_left_mul_finrank_of_free : finrank R ↥(A ⊔ B) = fin
rank R A * finrank A (Algebra.adjoin A (B : Set S))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Subalgebra.rank_sup_eq_rank_left_mul_rank_of_free`：rank_sup_eq_rank_left
_mul_rank_of_free : Module.rank R ↥(A ⊔ B) = Module.rank R A * Module.rank A (Al
gebra.adjoin A (B : Set S))
-/
theorem finrank_sup_eq_finrank_left_mul_finrank_of_free :
    finrank R ↥(A ⊔ B) = finrank R A * finrank A (Algebra.adjoin A (B : Set S)) := by
  simpa only [map_mul] using! congr(Cardinal.toNat $(rank_sup_eq_rank_left_mul_rank_of_free A B))
/-
**Subalgebra.finrank_left_dvd_finrank_sup_of_free** 是 Mathlib 中的一个定理，位于命名空间 `Sub
algebra`。
形式化陈述：finrank_left_dvd_finrank_sup_of_free : finrank R A ∣ finrank R ↥(A ⊔ B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.finrank_sup_eq_finrank_left_mul_finrank_of_free`：finrank_sup_
eq_finrank_left_mul_finrank_of_free : finrank R ↥(A ⊔ B) = finrank R A * finrank
 A (Algebra.adjoin A (B : Set S))
-/
theorem finrank_left_dvd_finrank_sup_of_free :
    finrank R A ∣ finrank R ↥(A ⊔ B) := ⟨_, finrank_sup_eq_finrank_left_mul_finrank_of_free A B⟩

end

section
variable [Module.Free R B] [Module.Free B (Algebra.adjoin B (A : Set S))]

/-
**Subalgebra.rank_sup_eq_rank_right_mul_rank_of_free** 是 Mathlib 中的一个定理，位于命名空间 `
Subalgebra`。
形式化陈述：rank_sup_eq_rank_right_mul_rank_of_free : Module.rank R ↥(A ⊔ B) = Module.
rank R B * Module.rank B (Algebra.adjoin B (A : Set S))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Subalgebra.rank_sup_eq_rank_left_mul_rank_of_free`：rank_sup_eq_rank_left
_mul_rank_of_free : Module.rank R ↥(A ⊔ B) = Module.rank R A * Module.rank A (Al
gebra.adjoin A (B : Set S))
-/
theorem rank_sup_eq_rank_right_mul_rank_of_free :
    Module.rank R ↥(A ⊔ B) = Module.rank R B * Module.rank B (Algebra.adjoin B (A : Set S)) := by
  rw [sup_comm, rank_sup_eq_rank_left_mul_rank_of_free]
/-
**Subalgebra.finrank_sup_eq_finrank_right_mul_finrank_of_free** 是 Mathlib 中的一个定理
，位于命名空间 `Subalgebra`。
形式化陈述：finrank_sup_eq_finrank_right_mul_finrank_of_free : finrank R ↥(A ⊔ B) = fi
nrank R B * finrank B (Algebra.adjoin B (A : Set S))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Subalgebra.finrank_sup_eq_finrank_left_mul_finrank_of_free`：finrank_sup_
eq_finrank_left_mul_finrank_of_free : finrank R ↥(A ⊔ B) = finrank R A * finrank
 A (Algebra.adjoin A (B : Set S))
-/
theorem finrank_sup_eq_finrank_right_mul_finrank_of_free :
    finrank R ↥(A ⊔ B) = finrank R B * finrank B (Algebra.adjoin B (A : Set S)) := by
  rw [sup_comm, finrank_sup_eq_finrank_left_mul_finrank_of_free]
/-
**Subalgebra.finrank_right_dvd_finrank_sup_of_free** 是 Mathlib 中的一个定理，位于命名空间 `Su
balgebra`。
形式化陈述：finrank_right_dvd_finrank_sup_of_free : finrank R B ∣ finrank R ↥(A ⊔ B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.finrank_sup_eq_finrank_right_mul_finrank_of_free`：finrank_sup
_eq_finrank_right_mul_finrank_of_free : finrank R ↥(A ⊔ B) = finrank R B * finra
nk B (Algebra.adjoin B (A : Set S))
-/
theorem finrank_right_dvd_finrank_sup_of_free :
    finrank R B ∣ finrank R ↥(A ⊔ B) := ⟨_, finrank_sup_eq_finrank_right_mul_finrank_of_free A B⟩

end

end Subalgebra

