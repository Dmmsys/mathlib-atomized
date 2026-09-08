/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Algebra towers for multivariate polynomial

This file proves some basic results about the algebra tower structure for the type
`MvPolynomial σ R`.

This structure itself is provided elsewhere as `MvPolynomial.isScalarTower`

When you update this file, you can also try to make a corresponding update in
`RingTheory.Polynomial.Tower`.
-/

public section


variable (R A B : Type*) {σ : Type*}

namespace MvPolynomial

section Semiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra A B] [Algebra R B]
variable [IsScalarTower R A B]
variable {R B}

/-
**MvPolynomial.aeval_map_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_map_algebraMap (x : σ -> B) (p : MvPolynomial σ R) : aeval x (map (a
lgebraMap R A) p) = aeval x p
参数：x : σ -> B；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_def`：aeval_def (p : MvPolynomial σ R) : aeval f p = e
val₂ (algebraMap R S₁) f p
· 使用定理 `MvPolynomial.eval₂_map`：eval₂_map [CommSemiring S₂] (f : R ->+* S₁) (g :
 σ -> S₂) (φ : S₁ ->+* S₂) (p : MvPolynomial σ R) : eval₂ φ g (map f p) = eval₂ 
(φ.comp f) g…
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
-/
theorem aeval_map_algebraMap (x : σ → B) (p : MvPolynomial σ R) :
    aeval x (map (algebraMap R A) p) = aeval x p := by
  rw [aeval_def, aeval_def, eval₂_map, IsScalarTower.algebraMap_eq R A B]

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable {R A}

/-
**MvPolynomial.aeval_algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_algebraMap_apply (x : σ -> A) (p : MvPolynomial σ R) : aeval (algebr
aMap A B ∘ x) p = algebraMap A B (MvPolynomial.aeval x p)
参数：x : σ -> A；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_def`：aeval_def (p : MvPolynomial σ R) : aeval f p = e
val₂ (algebraMap R S₁) f p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.coe_eval₂Hom`：coe_eval₂Hom (f : R ->+* S₁) (g : σ -> S₁) : 
⇑(eval₂Hom f g) = eval₂ f g
· 使用定理 `MvPolynomial.map_eval₂Hom`：map_eval₂Hom [CommSemiring S₂] (f : R ->+* S₁
) (g : σ -> S₁) (φ : S₁ ->+* S₂) (p : MvPolynomial σ R) : φ (eval₂Hom f g p) = e
val₂Hom (φ.comp…
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
theorem aeval_algebraMap_apply (x : σ → A) (p : MvPolynomial σ R) :
    aeval (algebraMap A B ∘ x) p = algebraMap A B (MvPolynomial.aeval x p) := by
  rw [aeval_def, aeval_def, ← coe_eval₂Hom, ← coe_eval₂Hom, map_eval₂Hom, ←
    IsScalarTower.algebraMap_eq, Function.comp_def]

@[simp]
/-
**MvPolynomial.aeval_C_comp_left** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_C_comp_left {ι : Type*} (f : σ -> A) (p : MvPolynomial σ R) : aeval 
(C (σ
参数：f : σ -> A；p : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : σ -> A)
 (p : MvPolynomial σ R) : aeval (algebraMap A B ∘ x) p = algebraMap A B (MvPolyn
omial.aeval x p)
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma aeval_C_comp_left {ι : Type*} (f : σ → A) (p : MvPolynomial σ R) :
    aeval (C (σ := ι) ∘ f) p = C (aeval f p) :=
  aeval_algebraMap_apply ..
/-
**MvPolynomial.aeval_algebraMap_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynom
ial`。
形式化陈述：aeval_algebraMap_eq_zero_iff [IsDomain A] [Module.IsTorsionFree A B] [Nont
rivial B] (x : σ -> A) (p : MvPolynomial σ R) : aeval (algebraMap A B ∘ x) p = 0
 ↔ aeval x p = 0
参数：x : σ -> A；p : MvPolynomial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : σ -> A)
 (p : MvPolynomial σ R) : aeval (algebraMap A B ∘ x) p = algebraMap A B (MvPolyn
omial.aeval x p)
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
lemma aeval_algebraMap_eq_zero_iff [IsDomain A] [Module.IsTorsionFree A B] [Nontrivial B]
    (x : σ → A) (p : MvPolynomial σ R) : aeval (algebraMap A B ∘ x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebraMap_apply, Algebra.algebraMap_eq_smul_one, smul_eq_zero,
    iff_false_intro (one_ne_zero' B), or_false]
/-
**MvPolynomial.aeval_algebraMap_eq_zero_iff_of_injective** 是 Mathlib 中的一个定理，位于命名
空间 `MvPolynomial`。
形式化陈述：aeval_algebraMap_eq_zero_iff_of_injective {x : σ -> A} {p : MvPolynomial σ
 R} (h : Function.Injective (algebraMap A B)) : aeval (algebraMap A B ∘ x) p = 0
 ↔ aeval x p = 0
参数：h : Function.Injective (algebraMap A B)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : σ -> A)
 (p : MvPolynomial σ R) : aeval (algebraMap A B ∘ x) p = algebraMap A B (MvPolyn
omial.aeval x p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem aeval_algebraMap_eq_zero_iff_of_injective {x : σ → A} {p : MvPolynomial σ R}
    (h : Function.Injective (algebraMap A B)) :
    aeval (algebraMap A B ∘ x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebraMap_apply, ← (algebraMap A B).map_zero, h.eq_iff]

end CommSemiring

end MvPolynomial

namespace Subalgebra

open MvPolynomial

section CommSemiring

variable {R A} [CommSemiring R] [CommSemiring A] [Algebra R A]

@[simp]
/-
**Subalgebra.mvPolynomial_aeval_coe** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mvPolynomial_aeval_coe (S : Subalgebra R A) (x : σ -> S) (p : MvPolynomial
 σ R) : aeval (fun i => (x i : A)) p = aeval x p
参数：S : Subalgebra R A；x : σ -> S；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : σ -> A)
 (p : MvPolynomial σ R) : aeval (algebraMap A B ∘ x) p = algebraMap A B (MvPolyn
omial.aeval x p)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem mvPolynomial_aeval_coe (S : Subalgebra R A) (x : σ → S) (p : MvPolynomial σ R) :
    aeval (fun i => (x i : A)) p = aeval x p := by convert! aeval_algebraMap_apply A x p

end CommSemiring

end Subalgebra

