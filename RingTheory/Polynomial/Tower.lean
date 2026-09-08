/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Algebra towers for polynomial

This file proves some basic results about the algebra tower structure for the type `R[X]`.

This structure itself is provided elsewhere as `Polynomial.isScalarTower`

When you update this file, you can also try to make a corresponding update in
`RingTheory.MvPolynomial.Tower`.
-/

public section


open Module

variable (R A B : Type*)

namespace Polynomial

section Semiring

variable [CommSemiring R] [CommSemiring A] [Semiring B]
variable [Algebra R A] [Algebra A B] [Algebra R B]
variable [IsScalarTower R A B]
variable {R B}

@[simp]
/-
**Polynomial.aeval_map_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_map_algebraMap (x : B) (p : R[X]) : aeval x (map (algebraMap R A) p)
 = aeval x p
参数：x : B；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.eval₂_map`：eval₂_map [Semiring T] (g : S ->+* T) (x : T) : (p
.map f).eval₂ g x = p.eval₂ (g.comp f) x
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
-/
theorem aeval_map_algebraMap (x : B) (p : R[X]) : aeval x (map (algebraMap R A) p) = aeval x p := by
  rw [aeval_def, aeval_def, eval₂_map, IsScalarTower.algebraMap_eq R A B]

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Semiring B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable {R A}

/-
**Polynomial.aeval_algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_algebraMap_apply (x : A) (p : R[X]) : aeval (algebraMap A B x) p = a
lgebraMap A B (aeval x p)
参数：x : A；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.hom_eval₂`：hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.c
omp f) (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
-/
theorem aeval_algebraMap_apply (x : A) (p : R[X]) :
    aeval (algebraMap A B x) p = algebraMap A B (aeval x p) := by
  rw [aeval_def, aeval_def, hom_eval₂, ← IsScalarTower.algebraMap_eq]

@[simp]
/-
**Polynomial.aeval_algebraMap_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：aeval_algebraMap_eq_zero_iff [IsDomain A] [IsTorsionFree A B] [Nontrivial 
B] (x : A) (p : R[X]) : aeval (algebraMap A B x) p = 0 ↔ aeval x p = 0
参数：x : A；p : R[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `iff_false_intro`：∀ {a : Prop}, ¬a → (a ↔ False)
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem aeval_algebraMap_eq_zero_iff [IsDomain A] [IsTorsionFree A B] [Nontrivial B] (x : A)
    (p : R[X]) : aeval (algebraMap A B x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebraMap_apply, Algebra.algebraMap_eq_smul_one, smul_eq_zero,
    iff_false_intro (one_ne_zero' B), or_false]

variable {B}
/-
**Polynomial.aeval_algebraMap_eq_zero_iff_of_injective** 是 Mathlib 中的一个定理，位于命名空间
 `Polynomial`。
形式化陈述：aeval_algebraMap_eq_zero_iff_of_injective {x : A} {p : R[X]} (h : Function
.Injective (algebraMap A B)) : aeval (algebraMap A B x) p = 0 ↔ aeval x p = 0
参数：h : Function.Injective (algebraMap A B)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem aeval_algebraMap_eq_zero_iff_of_injective {x : A} {p : R[X]}
    (h : Function.Injective (algebraMap A B)) : aeval (algebraMap A B x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebraMap_apply, ← (algebraMap A B).map_zero, h.eq_iff]

end CommSemiring

end Polynomial

namespace Subalgebra

open Polynomial

section CommSemiring

variable {R A} [CommSemiring R] [CommSemiring A] [Algebra R A]

@[simp]
/-
**Subalgebra.aeval_coe** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：aeval_coe (S : Subalgebra R A) (x : S) (p : R[X]) : aeval (x : A) p = aeva
l x p
参数：S : Subalgebra R A；x : S；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)
· 使用定理 `Subalgebra.isScalarTower_mid`：∀ {R : Type u} {A : Type v} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {α
 : Type u_1} {β : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem aeval_coe (S : Subalgebra R A) (x : S) (p : R[X]) : aeval (x : A) p = aeval x p :=
  aeval_algebraMap_apply A x p

end CommSemiring

end Subalgebra

namespace Polynomial

variable {R A} [CommSemiring R] [CommRing A] [Algebra R A]

/-
**Polynomial.aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial`。
形式化陈述：aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C (s : Multiset A) {x : A} (hx
 : x in s) {p : R[X]} (hp : p.mapAlg R A = (s.map (X - C ·)).prod) : aeval x p =
 0
参数：s : Multiset A；hx : x in s；hp : p.mapAlg R A = (s.map (X - C ·)).prod。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Polynomial.mapAlg_eq_map`：mapAlg_eq_map (S : Type v) [Semiring S] [Algeb
ra R S] (p : R[X]) : mapAlg R S p = map (algebraMap R S) p
· 使用定理 `map_multiset_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst 
: CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MonoidHomCla
ss F M …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `Multiset.prod_eq_zero`：prod_eq_zero (h : (0 : M₀) in s) : s.prod = 0
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C (s : Multiset A) {x : A} (hx : x ∈ s)
    {p : R[X]} (hp : p.mapAlg R A = (s.map (X - C ·)).prod) : aeval x p = 0 := by
  rw [← aeval_map_algebraMap A, ← mapAlg_eq_map, hp, map_multiset_prod, Multiset.prod_eq_zero]
  rw [Multiset.map_map, Multiset.mem_map]
  exact ⟨x, hx, by simp⟩

end Polynomial

