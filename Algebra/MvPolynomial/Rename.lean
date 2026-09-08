/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Renaming variables of polynomials

This file establishes the `rename` operation on multivariate polynomials,
which modifies the set of variables.

## Main declarations

* `MvPolynomial.rename`
* `MvPolynomial.renameEquiv`

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ α : Type*` (indexing the variables)

+ `R S : Type*` `[CommSemiring R]` `[CommSemiring S]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`.

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ α`

-/

@[expose] public section


noncomputable section

open Set Function Finsupp AddMonoidAlgebra

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

namespace MvPolynomial

section Rename

/-- Rename all the variables in a multivariable polynomial. -/
/-
**MvPolynomial.rename** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：rename (f : σ -> τ) : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R
参数：f : σ -> τ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rename all the variables in a multivariable polynomial.
-/
def rename (f : σ → τ) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  AddMonoidAlgebra.mapDomainAlgHom _ _ (mapDomain.addMonoidHom f)

set_option backward.isDefEq.respectTransparency.types false in
/-
**MvPolynomial.rename_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_C (f : σ -> τ) (r : R) : rename f (C r) = C r
参数：f : σ -> τ；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.mapDomainAlgHom_apply`：∀ (R : Type u_1) (A : Type u_4) 
{M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [i
nst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.mapDomain_single`：∀ {R : Type u_3} {M : Type u_6} {N : 
Type u_7} [inst : Semiring R] {f : M → N} {a : M} {r : R},   AddMonoidAlgebra.ma
pDomain f (AddMonoidAlg…
· 使用定理 `Finsupp.mapDomain.addMonoidHom_apply`：∀ {α : Type u_1} {β : Type u_2} {M
 : Type u_5} [inst : AddCommMonoid M] (f : α → β) (v : α →₀ M),   (Finsupp.mapDo
main.addMonoidHom f) v = F…
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rename_C (f : σ → τ) (r : R) : rename f (C r) = C r := by
  unfold rename C monomial MvPolynomial; simp

@[simp]
/-
**MvPolynomial.rename_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_X (f : σ -> τ) (i : σ) : rename f (X i : MvPolynomial σ R) = X (f i
)
参数：f : σ -> τ；i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.mapDomainAlgHom_apply`：∀ (R : Type u_1) (A : Type u_4) 
{M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [i
nst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.mapDomain_single`：∀ {R : Type u_3} {M : Type u_6} {N : 
Type u_7} [inst : Semiring R] {f : M → N} {a : M} {r : R},   AddMonoidAlgebra.ma
pDomain f (AddMonoidAlg…
· 使用定理 `Finsupp.mapDomain.addMonoidHom_apply`：∀ {α : Type u_1} {β : Type u_2} {M
 : Type u_5} [inst : AddCommMonoid M] (f : α → β) (v : α →₀ M),   (Finsupp.mapDo
main.addMonoidHom f) v = F…
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rename_X (f : σ → τ) (i : σ) : rename f (X i : MvPolynomial σ R) = X (f i) := by
  simp [MvPolynomial, rename, X, monomial]

@[simp]
/-
**MvPolynomial.rename_zero** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_zero (f : σ -> τ) : (0 : MvPolynomial σ R).rename f = 0
参数：f : σ -> τ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rename_zero (f : σ → τ) : (0 : MvPolynomial σ R).rename f = 0 := rfl
/-
**MvPolynomial.map_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_rename (f : R ->+* S) (g : σ -> τ) (p : MvPolynomial σ R) : map f (ren
ame g p) = rename g (map f p)
参数：f : R ->+* S；g : σ -> τ；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_C`：rename_C (f : σ -> τ) (r : R) : rename f (C r) = 
C r
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
-/
theorem map_rename (f : R →+* S) (g : σ → τ) (p : MvPolynomial σ R) :
    map f (rename g p) = rename g (map f p) := by
  apply MvPolynomial.induction_on p
    (fun a => by simp only [map_C, rename_C])
    (fun p q hp hq => by simp only [hp, hq, map_add]) fun p n hp => by
    simp only [hp, rename_X, map_X, map_mul]
/-
**MvPolynomial.map_comp_rename** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：map_comp_rename (f : R ->+* S) (g : σ -> τ) : (map f).comp (rename g).toRi
ngHom = (rename g).toRingHom.comp (map f)
参数：f : R ->+* S；g : σ -> τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPolynomial.map_rename`：map_rename (f : R ->+* S) (g : σ -> τ) (p : MvP
olynomial σ R) : map f (rename g p) = rename g (map f p)
-/
lemma map_comp_rename (f : R →+* S) (g : σ → τ) :
    (map f).comp (rename g).toRingHom = (rename g).toRingHom.comp (map f) :=
  RingHom.ext fun p ↦ map_rename f g p

@[simp]
/-
**MvPolynomial.rename_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_rename (f : σ -> τ) (g : τ -> α) (p : MvPolynomial σ R) : rename g 
(rename f p) = rename (g ∘ f) p
参数：f : σ -> τ；g : τ -> α；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.mapDomainAlgHom_apply`：∀ (R : Type u_1) (A : Type u_4) 
{M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [i
nst_2 : Algebra R A] [inst_3…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.mapDomain.addMonoidHom_comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {M : Type u_5} [inst : AddCommMonoid M] (f : β → γ) (g : α → β),   F
insupp.mapDomain.addMonoi…
· 使用定理 `AddMonoidAlgebra.mapDomainAlgHom_comp`：∀ {R : Type u_1} {A : Type u_4} {
M : Type u_7} {N : Type u_8} {O : Type u_9} [inst : CommSemiring R]   [inst_1 : 
Semiring A] [inst_2 : Algeb…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rename_rename (f : σ → τ) (g : τ → α) (p : MvPolynomial σ R) :
    rename g (rename f p) = rename (g ∘ f) p := by
  simp [MvPolynomial, rename, mapDomain.addMonoidHom_comp]
/-
**MvPolynomial.rename_comp_rename** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_comp_rename (f : σ -> τ) (g : τ -> α) : (rename (R
参数：f : σ -> τ；g : τ -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `MvPolynomial.rename_rename`：rename_rename (f : σ -> τ) (g : τ -> α) (p :
 MvPolynomial σ R) : rename g (rename f p) = rename (g ∘ f) p
-/
lemma rename_comp_rename (f : σ → τ) (g : τ → α) :
    (rename (R := R) g).comp (rename f) = rename (g ∘ f) :=
  AlgHom.ext fun p ↦ rename_rename f g p

@[simp]
/-
**MvPolynomial.rename_id** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_id : rename id = AlgHom.id R (MvPolynomial σ R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain.addMonoidHom_id`：∀ {α : Type u_1} {M : Type u_5} [inst
 : AddCommMonoid M], Finsupp.mapDomain.addMonoidHom id = AddMonoidHom.id (α →₀ M
)
· 使用定理 `AddMonoidAlgebra.mapDomainAlgHom_id`：∀ {R : Type u_1} {A : Type u_4} {M 
: Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]
   [inst_3 : AddMonoid M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rename_id : rename id = AlgHom.id R (MvPolynomial σ R) := by simp [MvPolynomial, rename]
/-
**MvPolynomial.rename_id_apply** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_id_apply (p : MvPolynomial σ R) : rename id p = p
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_id`：rename_id : rename id = AlgHom.id R (MvPolynomia
l σ R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rename_id_apply (p : MvPolynomial σ R) : rename id p = p := by
  simp
/-
**MvPolynomial.rename_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_monomial (f : σ -> τ) (d : σ ->₀ Nat) (r : R) : rename f (monomial 
d r) = monomial (d.mapDomain f) r
参数：f : σ -> τ；d : σ ->₀ Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.mapDomainAlgHom_apply`：∀ (R : Type u_1) (A : Type u_4) 
{M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [i
nst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.mapDomain_single`：∀ {R : Type u_3} {M : Type u_6} {N : 
Type u_7} [inst : Semiring R] {f : M → N} {a : M} {r : R},   AddMonoidAlgebra.ma
pDomain f (AddMonoidAlg…
· 使用定理 `Finsupp.mapDomain.addMonoidHom_apply`：∀ {α : Type u_1} {β : Type u_2} {M
 : Type u_5} [inst : AddCommMonoid M] (f : α → β) (v : α →₀ M),   (Finsupp.mapDo
main.addMonoidHom f) v = F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rename_monomial (f : σ → τ) (d : σ →₀ ℕ) (r : R) :
    rename f (monomial d r) = monomial (d.mapDomain f) r := by
  simp [MvPolynomial, rename, monomial]
/-
**MvPolynomial.rename_eq_aeval** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_eq_aeval (f : σ -> τ) : rename (R
参数：f : σ -> τ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rename_eq_aeval (f : σ → τ) : rename (R := R) f = aeval (X ∘ f) := by ext; simp

@[deprecated (since := "2026-06-18")] alias rename_eq := rename_eq_aeval
/-
**MvPolynomial.rename_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_injective (f : σ -> τ) (hf : Function.Injective f) : Function.Injec
tive (rename f : MvPolynomial σ R -> MvPolynomial τ R)
参数：f : σ -> τ；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.mapDomain_injective`：∀ {R : Type u_3} {M : Type u_6} {N
 : Type u_7} [inst : Semiring R] {f : M → N},   Function.Injective f → Function.
Injective (AddMonoidAlgebr…
· 使用定理 `Finsupp.mapDomain_injective`：mapDomain_injective {f : α -> β} (hf : Func
tion.Injective f) : Function.Injective (mapDomain f : (α ->₀ M) -> β ->₀ M)
-/
theorem rename_injective (f : σ → τ) (hf : Function.Injective f) :
    Function.Injective (rename f : MvPolynomial σ R → MvPolynomial τ R) :=
  AddMonoidAlgebra.mapDomain_injective (Finsupp.mapDomain_injective hf)

@[simp]
/-
**MvPolynomial.rename_eq_zero_iff_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `MvPoly
nomial`。
形式化陈述：rename_eq_zero_iff_of_injective (p : MvPolynomial σ R) {f : σ -> τ} (hf : 
f.Injective) : p.rename f = 0 ↔ p = 0
参数：p : MvPolynomial σ R；hf : f.Injective。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MvPolynomial.rename_zero`：rename_zero (f : σ -> τ) : (0 : MvPolynomial σ
 R).rename f = 0
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MvPolynomial.rename_injective`：rename_injective (f : σ -> τ) (hf : Funct
ion.Injective f) : Function.Injective (rename f : MvPolynomial σ R -> MvPolynomi
al τ R)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rename_eq_zero_iff_of_injective (p : MvPolynomial σ R) {f : σ → τ}
    (hf : f.Injective) : p.rename f = 0 ↔ p = 0 := by
  rw [← rename_zero f, (MvPolynomial.rename_injective _ hf).eq_iff]
/-
**MvPolynomial.rename_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_leftInverse {f : σ -> τ} {g : τ -> σ} (hf : Function.LeftInverse f 
g) : Function.LeftInverse (rename f : MvPolynomial σ R -> MvPolynomial τ R) (ren
ame g)
参数：hf : Function.LeftInverse f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_rename`：rename_rename (f : σ -> τ) (g : τ -> α) (p :
 MvPolynomial σ R) : rename g (rename f p) = rename (g ∘ f) p
· 使用定理 `Function.LeftInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → f ∘ g = id
· 使用定理 `MvPolynomial.rename_id`：rename_id : rename id = AlgHom.id R (MvPolynomia
l σ R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rename_leftInverse {f : σ → τ} {g : τ → σ} (hf : Function.LeftInverse f g) :
    Function.LeftInverse (rename f : MvPolynomial σ R → MvPolynomial τ R) (rename g) := by
  intro x
  simp [hf.comp_eq_id]
/-
**MvPolynomial.rename_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_rightInverse {f : σ -> τ} {g : τ -> σ} (hf : Function.RightInverse 
f g) : Function.RightInverse (rename f : MvPolynomial σ R -> MvPolynomial τ R) (
rename g)
参数：hf : Function.RightInverse f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.rename_leftInverse`：rename_leftInverse {f : σ -> τ} {g : τ 
-> σ} (hf : Function.LeftInverse f g) : Function.LeftInverse (rename f : MvPolyn
omial σ R -> MvPolyno…
-/
theorem rename_rightInverse {f : σ → τ} {g : τ → σ} (hf : Function.RightInverse f g) :
    Function.RightInverse (rename f : MvPolynomial σ R → MvPolynomial τ R) (rename g) :=
  rename_leftInverse hf
/-
**MvPolynomial.rename_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_surjective (f : σ -> τ) (hf : Function.Surjective f) : Function.Sur
jective (rename f : MvPolynomial σ R -> MvPolynomial τ R)
参数：f : σ -> τ；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.hasRightInverse`：∀ {α : Sort u} {β : Sort v} {f : α 
→ β}, Function.Surjective f → Function.HasRightInverse f
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `MvPolynomial.rename_rightInverse`：rename_rightInverse {f : σ -> τ} {g : 
τ -> σ} (hf : Function.RightInverse f g) : Function.RightInverse (rename f : MvP
olynomial σ R -> MvPol…
-/
theorem rename_surjective (f : σ → τ) (hf : Function.Surjective f) :
    Function.Surjective (rename f : MvPolynomial σ R → MvPolynomial τ R) :=
  let ⟨_, hf⟩ := hf.hasRightInverse; rename_rightInverse hf |>.surjective

section

variable {f : σ → τ} (hf : Function.Injective f) {p q : MvPolynomial τ R}

open scoped Classical in
/-- Given a function between sets of variables `f : σ → τ` that is injective with proof `hf`,
  `MvPolynomial.killCompl hf` is the `AlgHom` from `R[τ]` to `R[σ]` that is left inverse to
  `rename f : R[σ] → R[τ]` and sends the variables in the complement of the range of `f` to `0`. -/
/-
**MvPolynomial.killCompl** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：killCompl : MvPolynomial τ R ->ₐ[R] MvPolynomial σ R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a function between sets of variables `f : σ → τ` that is injective with pr
oof `hf`,
  `MvPolynomial.killCompl hf` is the `AlgHom` from `R[τ]` to `R[σ]` that is left
 inverse to
  `rename f : R[σ] → R[τ]` and sends the variables in the complement of the rang
e of `f` to `0`.
-/
def killCompl : MvPolynomial τ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i => if h : i ∈ Set.range f then X <| (Equiv.ofInjective f hf).symm ⟨i, h⟩ else 0
/-
**MvPolynomial.killCompl_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：killCompl_C (r : R) : killCompl hf (C r) = C r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
-/
theorem killCompl_C (r : R) : killCompl hf (C r) = C r := algHom_C _ _
/-
**MvPolynomial.killCompl_comp_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：killCompl_comp_rename : (killCompl hf).comp (rename f) = AlgHom.id R _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MvPolynomial.killCompl.eq_1`：∀ {σ : Type u_1} {τ : Type u_2} {R : Type u
_4} [inst : CommSemiring R] {f : σ → τ} (hf : Function.Injective f),   MvPolynom
ial.killCompl hf …
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Equiv.ofInjective_symm_apply`：ofInjective_symm_apply {α β} {f : α -> β} 
(hf : Injective f) (a : α) : (ofInjective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a
-/
theorem killCompl_comp_rename : (killCompl hf).comp (rename f) = AlgHom.id R _ :=
  algHom_ext fun i => by
    dsimp
    rw [rename_X, killCompl, aeval_X, dif_pos ⟨i, rfl⟩, Equiv.ofInjective_symm_apply]

@[simp]
/-
**MvPolynomial.killCompl_rename_app** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：killCompl_rename_app (p : MvPolynomial σ R) : killCompl hf (rename f p) = 
p
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `MvPolynomial.killCompl_comp_rename`：killCompl_comp_rename : (killCompl h
f).comp (rename f) = AlgHom.id R _
-/
theorem killCompl_rename_app (p : MvPolynomial σ R) : killCompl hf (rename f p) = p :=
  AlgHom.congr_fun (killCompl_comp_rename hf) p
/-
**MvPolynomial.killCompl_map** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：killCompl_map (φ : R ->+* S) (p : MvPolynomial τ R) : (p.map φ).killCompl 
hf = (p.killCompl hf).map φ
参数：φ : R ->+* S；p : MvPolynomial τ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MvPolynomial.ringHom_ext'`：ringHom_ext' {A : Type*} [Semiring A] {f g : 
MvPolynomial σ R ->+* A} (hC : f.comp C = g.comp C) (hX : forall i, f (X i) = g 
(X i)) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma killCompl_map (φ : R →+* S) (p : MvPolynomial τ R) :
    (p.map φ).killCompl hf = (p.killCompl hf).map φ := by
  simp only [← AlgHom.coe_toRingHom, ← RingHom.comp_apply]
  congr
  ext i n
  · simp
  · by_cases h : i ∈ Set.range f <;> simp [killCompl, h]

@[simp]
/-
**MvPolynomial.killCompl_monomial_mapDomain** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynom
ial`。
形式化陈述：killCompl_monomial_mapDomain {s : σ ->₀ Nat} {c : R} : (monomial (s.mapDom
ain f) c).killCompl hf = monomial s c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.killCompl_rename_app`：killCompl_rename_app (p : MvPolynomia
l σ R) : killCompl hf (rename f p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma killCompl_monomial_mapDomain {s : σ →₀ ℕ} {c : R} :
    (monomial (s.mapDomain f) c).killCompl hf = monomial s c := by
  simp [← rename_monomial]
/-
**MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range** 是 Mathlib 中的一个引理，位于命
名空间 `MvPolynomial`。
形式化陈述：killCompl_monomial_eq_zero_of_notMem_range {s : τ ->₀ Nat} (c : R) {a : τ}
 (ha : a in s.support) (hs : a ∉ Set.range f) : (monomial s c).killCompl hf = 0
参数：c : R；ha : a in s.support；hs : a ∉ Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.killCompl.eq_1`：∀ {σ : Type u_1} {τ : Type u_2} {R : Type u
_4} [inst : CommSemiring R] {f : σ → τ} (hf : Function.Injective f),   MvPolynom
ial.killCompl hf …
· 使用定理 `MvPolynomial.aeval_monomial`：aeval_monomial (g : σ -> S₁) (d : σ ->₀ Nat
) (r : R) : aeval g (monomial d r) = algebraMap _ _ r * d.prod fun i k => g i ^ 
k
· 使用定理 `Finsupp.prod.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst
 : Zero M] [inst_1 : CommMonoid N] (f : α →₀ M) (g : α → M → N),   f.prod g = ∏ 
a ∈ f.s…
· 使用定理 `mul_eq_zero_of_right`：mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0)
 : a * b = 0
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma killCompl_monomial_eq_zero_of_notMem_range {s : τ →₀ ℕ} (c : R)
    {a : τ} (ha : a ∈ s.support) (hs : a ∉ Set.range f) :
    (monomial s c).killCompl hf = 0 := by
  rw [killCompl, aeval_monomial, Finsupp.prod]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero ha
  simp [hs, zero_pow (Finsupp.mem_support_iff.mp ha)]
/-
**MvPolynomial.killCompl_monomial_eq_zero_of_not_subset** 是 Mathlib 中的一个引理，位于命名空
间 `MvPolynomial`。
形式化陈述：killCompl_monomial_eq_zero_of_not_subset {s : τ ->₀ Nat} (c : R) (hs : ¬ ↑
s.support subseteq Set.range f) : (monomial s c).killCompl hf = 0
参数：c : R；hs : ¬ ↑s.support subseteq Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用引理 `MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range`：killCompl_monom
ial_eq_zero_of_notMem_range {s : τ ->₀ Nat} (c : R) {a : τ} (ha : a in s.support
) (hs : a ∉ Set.range f) : (monomial s c).kil…
-/
lemma killCompl_monomial_eq_zero_of_not_subset {s : τ →₀ ℕ} (c : R)
    (hs : ¬ ↑s.support ⊆ Set.range f) : (monomial s c).killCompl hf = 0 :=
  have ⟨_, ha, hs⟩ := Set.not_subset.mp hs
  killCompl_monomial_eq_zero_of_notMem_range hf c ha hs
/-
**MvPolynomial.killCompl_monomial_eq_monomial_comapDomain_of_subset** 是 Mathlib 
中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：killCompl_monomial_eq_monomial_comapDomain_of_subset {s : τ ->₀ Nat} (c : 
R) (hs : ↑s.support subseteq Set.range f) : (monomial s c).killCompl hf = monomi
al (s.comapDomain f hf.injOn) c
参数：c : R；hs : ↑s.support subseteq Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.mapDomain_comapDomain`：mapDomain_comapDomain (hf : Function.Inje
ctive f) (l : β ->₀ M) (hl : ↑l.support subseteq Set.range f) : mapDomain f (com
apDomain f l hf.inj…
· 使用引理 `MvPolynomial.killCompl_monomial_mapDomain`：killCompl_monomial_mapDomain 
{s : σ ->₀ Nat} {c : R} : (monomial (s.mapDomain f) c).killCompl hf = monomial s
 c
-/
lemma killCompl_monomial_eq_monomial_comapDomain_of_subset {s : τ →₀ ℕ} (c : R)
    (hs : ↑s.support ⊆ Set.range f) :
    (monomial s c).killCompl hf = monomial (s.comapDomain f hf.injOn) c := by
  nth_rw 1 [← s.mapDomain_comapDomain f hf hs, killCompl_monomial_mapDomain]
/-
**MvPolynomial.killCompl_monomial** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：killCompl_monomial {s} {c : R} [Decidable (↑s.support subseteq Set.range f
)] : (monomial s c).killCompl hf = if ↑s.support subseteq Set.range f then monom
ial (s.comapDomain f hf.injOn) c else 0
参数：↑s.support subseteq Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `MvPolynomial.killCompl_monomial_eq_monomial_comapDomain_of_subset`：killC
ompl_monomial_eq_monomial_comapDomain_of_subset {s : τ ->₀ Nat} (c : R) (hs : ↑s
.support subseteq Set.range f) : (monomial s c).killCom…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `MvPolynomial.killCompl_monomial_eq_zero_of_not_subset`：killCompl_monomia
l_eq_zero_of_not_subset {s : τ ->₀ Nat} (c : R) (hs : ¬ ↑s.support subseteq Set.
range f) : (monomial s c).killCompl hf = 0
-/
lemma killCompl_monomial {s} {c : R} [Decidable (↑s.support ⊆ Set.range f)] :
    (monomial s c).killCompl hf =
      if ↑s.support ⊆ Set.range f then monomial (s.comapDomain f hf.injOn) c else 0 := by
  split_ifs with h
  · exact killCompl_monomial_eq_monomial_comapDomain_of_subset hf c h
  · exact killCompl_monomial_eq_zero_of_not_subset hf c h
/-
**MvPolynomial.coeff_killCompl** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_killCompl {s} : (p.killCompl hf).coeff s = p.coeff (s.mapDomain f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on'`：induction_on' {P : MvPolynomial σ R -> Prop}
 (p : MvPolynomial σ R) (monomial : forall (u : σ ->₀ Nat) (a : R), P (monomial 
u a)) (add : for…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.killCompl_monomial`：killCompl_monomial {s} {c : R} [Decidab
le (↑s.support subseteq Set.range f)] : (monomial s c).killCompl hf = if ↑s.supp
ort subseteq Set.rang…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Finsupp.mapDomain_injective`：mapDomain_injective {f : α -> β} (hf : Func
tion.Injective f) : Function.Injective (mapDomain f : (α ->₀ M) -> β ->₀ M)
· 使用定理 `Finsupp.mapDomain_comapDomain`：mapDomain_comapDomain (hf : Function.Inje
ctive f) (l : β ->₀ M) (hl : ↑l.support subseteq Set.range f) : mapDomain f (com
apDomain f l hf.inj…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Finsupp.mapDomain_support`：mapDomain_support [DecidableEq β] {f : α -> β
} {s : α ->₀ M} : (s.mapDomain f).support subseteq s.support.image f
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
-/
lemma coeff_killCompl {s} :
    (p.killCompl hf).coeff s = p.coeff (s.mapDomain f) := by
  classical
  apply p.induction_on' (P := fun p ↦ (p.killCompl hf).coeff s = p.coeff (s.mapDomain f))
  · intro u r
    rw [killCompl_monomial]
    split_ifs with h
    · simp [← (Finsupp.mapDomain_injective hf).eq_iff, u.mapDomain_comapDomain _ hf h]
    · simp? says simp only [coeff_zero, coeff_monomial, right_eq_ite_iff]
      intro rfl
      contrapose! h
      apply subset_trans <| SetLike.coe_subset_coe.mpr <| Finsupp.mapDomain_support
      simp
  · simp_intro ..
/-
**MvPolynomial.support_killCompl** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：support_killCompl {p : MvPolynomial τ R} : (p.killCompl hf).support = p.su
pport.preimage (Finsupp.mapDomain f) (Finsupp.mapDomain_injective hf).injOn
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Finsupp.mapDomain_injective`：mapDomain_injective {f : α -> β} (hf : Func
tion.Injective f) : Function.Injective (mapDomain f : (α ->₀ M) -> β ->₀ M)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MvPolynomial.coeff_killCompl`：coeff_killCompl {s} : (p.killCompl hf).coe
ff s = p.coeff (s.mapDomain f)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma support_killCompl {p : MvPolynomial τ R} :
    (p.killCompl hf).support =
      p.support.preimage (Finsupp.mapDomain f) (Finsupp.mapDomain_injective hf).injOn := by
  ext x
  simp [coeff_killCompl]

end

section

variable (R)

/-- `MvPolynomial.rename e` is an equivalence when `e` is. -/
@[simps apply]
/-
**MvPolynomial.renameEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：renameEquiv (f : σ ≃ τ) : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R
参数：f : σ ≃ τ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`MvPolynomial.rename e` is an equivalence when `e` is.
-/
def renameEquiv (f : σ ≃ τ) : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R :=
  { rename f with
    toFun := rename f
    invFun := rename f.symm
    left_inv := fun p => by rw [rename_rename, f.symm_comp_self, rename_id_apply]
    right_inv := fun p => by rw [rename_rename, f.self_comp_symm, rename_id_apply] }

@[simp]
/-
**MvPolynomial.renameEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：renameEquiv_refl : renameEquiv R (Equiv.refl σ) = AlgEquiv.refl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.renameEquiv_apply`：∀ {σ : Type u_1} {τ : Type u_2} (R : Typ
e u_4) [inst : CommSemiring R] (f : σ ≃ τ) (a : MvPolynomial σ R),   (MvPolynomi
al.renameEquiv R f) …
· 使用定理 `MvPolynomial.rename_id`：rename_id : rename id = AlgHom.id R (MvPolynomia
l σ R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem renameEquiv_refl : renameEquiv R (Equiv.refl σ) = AlgEquiv.refl :=
  AlgEquiv.ext (by simp)

@[simp]
/-
**MvPolynomial.renameEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：renameEquiv_symm (f : σ ≃ τ) : (renameEquiv R f).symm = renameEquiv R f.sy
mm
参数：f : σ ≃ τ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem renameEquiv_symm (f : σ ≃ τ) : (renameEquiv R f).symm = renameEquiv R f.symm :=
  rfl

@[simp]
/-
**MvPolynomial.renameEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：renameEquiv_trans (e : σ ≃ τ) (f : τ ≃ α) : (renameEquiv R e).trans (renam
eEquiv R f) = renameEquiv R (e.trans f)
参数：e : σ ≃ τ；f : τ ≃ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `MvPolynomial.rename_rename`：rename_rename (f : σ -> τ) (g : τ -> α) (p :
 MvPolynomial σ R) : rename g (rename f p) = rename (g ∘ f) p
-/
theorem renameEquiv_trans (e : σ ≃ τ) (f : τ ≃ α) :
    (renameEquiv R e).trans (renameEquiv R f) = renameEquiv R (e.trans f) :=
  AlgEquiv.ext (rename_rename e f)

end

section

variable (f : R →+* S) (k : σ → τ) (g : τ → S) (p : MvPolynomial σ R)

/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_rename : (rename k p).eval₂ f g = p.eval₂ f (g ∘ k) := by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]
/-
**MvPolynomial.eval_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_rename (g : τ -> R) (p : MvPolynomial σ R) : eval g (rename k p) = ev
al (g ∘ k) p
参数：g : τ -> R；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_rename`：eval₂_rename : (rename k p).eval₂ f g = p.eva
l₂ f (g ∘ k)
-/
theorem eval_rename (g : τ → R) (p : MvPolynomial σ R) : eval g (rename k p) = eval (g ∘ k) p :=
  eval₂_rename _ _ _ _
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_rename : eval₂Hom f g (rename k p) = eval₂Hom f (g ∘ k) p :=
  eval₂_rename _ _ _ _
/-
**MvPolynomial.aeval_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_rename [Algebra R S] : aeval g (rename k p) = aeval (g ∘ k) p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂Hom_rename`：eval₂Hom_rename : eval₂Hom f g (rename k p
) = eval₂Hom f (g ∘ k) p
-/
theorem aeval_rename [Algebra R S] : aeval g (rename k p) = aeval (g ∘ k) p :=
  eval₂Hom_rename _ _ _ _
/-
**MvPolynomial.aeval_comp_rename** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_comp_rename [Algebra R S] : (aeval (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `MvPolynomial.aeval_rename`：aeval_rename [Algebra R S] : aeval g (rename 
k p) = aeval (g ∘ k) p
-/
lemma aeval_comp_rename [Algebra R S] :
    (aeval (R := R) g).comp (rename k) = MvPolynomial.aeval (g ∘ k) :=
  AlgHom.ext fun p ↦ aeval_rename k g p
/-
**MvPolynomial.rename_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rename_eval₂ (g : τ → MvPolynomial σ R) :
    rename k (p.eval₂ C (g ∘ k)) = (rename k p).eval₂ C (rename k ∘ g) := by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]
/-
**MvPolynomial.rename_prod_mk_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rename_prod_mk_eval₂ (j : τ) (g : σ → MvPolynomial σ R) :
    rename (Prod.mk j) (p.eval₂ C g) = p.eval₂ C fun x => rename (Prod.mk j) (g x) := by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_rename_prod_mk (g : σ × τ → S) (i : σ) (p : MvPolynomial τ R) :
    (rename (Prod.mk i) p).eval₂ f g = eval₂ f (fun j => g (i, j)) p := by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]
/-
**MvPolynomial.eval_rename_prod_mk** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_rename_prod_mk (g : σ × τ -> R) (i : σ) (p : MvPolynomial τ R) : eval
 g (rename (Prod.mk i) p) = eval (fun j => g (i, j)) p
参数：g : σ × τ -> R；i : σ；p : MvPolynomial τ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_rename_prod_mk`：eval₂_rename_prod_mk (g : σ × τ -> S)
 (i : σ) (p : MvPolynomial τ R) : (rename (Prod.mk i) p).eval₂ f g = eval₂ f (fu
n j => g (i, j)) p
-/
theorem eval_rename_prod_mk (g : σ × τ → R) (i : σ) (p : MvPolynomial τ R) :
    eval g (rename (Prod.mk i) p) = eval (fun j => g (i, j)) p :=
  eval₂_rename_prod_mk (RingHom.id _) _ _ _

end

/-- Every polynomial is a polynomial in finitely many variables. -/
/-
**MvPolynomial.exists_finset_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：exists_finset_rename (p : MvPolynomial σ R) : exists (s : Finset σ) (q : M
vPolynomial { x // x in s } R), p = rename (↑) q
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_C`：rename_C (f : σ -> τ) (r : R) : rename f (C r) = 
C r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.rename_rename`：rename_rename (f : σ -> τ) (g : τ -> α) (p :
 MvPolynomial σ R) : rename g (rename f p) = rename (g ∘ f) p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)

--- 原说明 ---
Every polynomial is a polynomial in finitely many variables.
-/
theorem exists_finset_rename (p : MvPolynomial σ R) :
    ∃ (s : Finset σ) (q : MvPolynomial { x // x ∈ s } R), p = rename (↑) q := by
  classical
  apply induction_on p
  · intro r
    exact ⟨∅, C r, by rw [rename_C]⟩
  · rintro p q ⟨s, p, rfl⟩ ⟨t, q, rfl⟩
    refine ⟨s ∪ t, ⟨?_, ?_⟩⟩
    · refine rename (Subtype.map id ?_) p + rename (Subtype.map id ?_) q <;>
        simp +contextual only [id, true_or, or_true,
          Finset.mem_union, forall_true_iff]
    · simp only [rename_rename, map_add]
      rfl
  · rintro p n ⟨s, p, rfl⟩
    refine ⟨insert n s, ⟨?_, ?_⟩⟩
    · refine rename (Subtype.map id ?_) p * X ⟨n, s.mem_insert_self n⟩
      simp +contextual only [id, or_true, Finset.mem_insert, forall_true_iff]
    · simp only [rename_rename, rename_X, map_mul]
      rfl

/-- `exists_finset_rename` for two polynomials at once: for any two polynomials `p₁`, `p₂` in a
  polynomial semiring `R[σ]` of possibly infinitely many variables, `exists_finset_rename₂` yields
  a finite subset `s` of `σ` such that both `p₁` and `p₂` are contained in the polynomial semiring
  `R[s]` of finitely many variables. -/
/-
**MvPolynomial.exists_finset_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：exists_finset_rename (p : MvPolynomial σ R) : exists (s : Finset σ) (q : M
vPolynomial { x // x in s } R), p = rename (↑) q
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_C`：rename_C (f : σ -> τ) (r : R) : rename f (C r) = 
C r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.rename_rename`：rename_rename (f : σ -> τ) (g : τ -> α) (p :
 MvPolynomial σ R) : rename g (rename f p) = rename (g ∘ f) p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)

--- 原说明 ---
`exists_finset_rename` for two polynomials at once: for any two polynomials `p₁`
, `p₂` in a
  polynomial semiring `R[σ]` of possibly infinitely many variables, `exists_fins
et_rename₂` yields
  a finite subset `s` of `σ` such that both `p₁` and `p₂` are contained in the p
olynomial semiring
  `R[s]` of finitely many variables.
-/
theorem exists_finset_rename₂ (p₁ p₂ : MvPolynomial σ R) :
    ∃ (s : Finset σ) (q₁ q₂ : MvPolynomial s R), p₁ = rename (↑) q₁ ∧ p₂ = rename (↑) q₂ := by
  obtain ⟨s₁, q₁, rfl⟩ := exists_finset_rename p₁
  obtain ⟨s₂, q₂, rfl⟩ := exists_finset_rename p₂
  classical
    use s₁ ∪ s₂
    use rename (fun x ↦ ⟨x, Finset.subset_union_left x.2⟩) q₁
    use rename (fun x ↦ ⟨x, Finset.subset_union_right x.2⟩) q₂
    constructor <;> simp [Function.comp_def]

/-- Every polynomial is a polynomial in finitely many variables. -/
/-
**MvPolynomial.exists_fin_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：exists_fin_rename (p : MvPolynomial σ R) : exists (n : Nat) (f : Fin n -> 
σ) (_hf : Injective f) (q : MvPolynomial (Fin n) R), p = rename f q
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.exists_finset_rename`：exists_finset_rename (p : MvPolynomia
l σ R) : exists (s : Finset σ) (q : MvPolynomial { x // x in s } R), p = rename 
(↑) q
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.rename_rename`：rename_rename (f : σ -> τ) (g : τ -> α) (p :
 MvPolynomial σ R) : rename g (rename f p) = rename (g ∘ f) p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Every polynomial is a polynomial in finitely many variables.
-/
theorem exists_fin_rename (p : MvPolynomial σ R) :
    ∃ (n : ℕ) (f : Fin n → σ) (_hf : Injective f) (q : MvPolynomial (Fin n) R), p = rename f q := by
  obtain ⟨s, q, rfl⟩ := exists_finset_rename p
  let n := Fintype.card { x // x ∈ s }
  let e := Fintype.equivFin { x // x ∈ s }
  refine ⟨n, (↑) ∘ e.symm, Subtype.val_injective.comp e.symm.injective, rename e q, ?_⟩
  rw [← rename_rename, rename_rename e]
  simp only [Function.comp_def, Equiv.symm_apply_apply, rename_rename]

end Rename

/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_cast_comp (f : σ → τ) (c : ℤ →+* R) (g : τ → R) (p : MvPolynomial σ ℤ) :
    eval₂ c (g ∘ f) p = eval₂ c g (rename f p) := (eval₂_rename c f g p).symm

section Coeff

@[simp]
/-
**MvPolynomial.coeff_rename_mapDomain** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_rename_mapDomain (f : σ -> τ) (hf : Injective f) (φ : MvPolynomial σ
 R) (d : σ ->₀ Nat) : (rename f φ).coeff (d.mapDomain f) = φ.coeff d
参数：f : σ -> τ；hf : Injective f；φ : MvPolynomial σ R；d : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on'`：induction_on' {P : MvPolynomial σ R -> Prop}
 (p : MvPolynomial σ R) (monomial : forall (u : σ ->₀ Nat) (a : R), P (monomial 
u a)) (add : for…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_monomial`：rename_monomial (f : σ -> τ) (d : σ ->₀ Na
t) (r : R) : rename f (monomial d r) = monomial (d.mapDomain f) r
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Finsupp.mapDomain_injective`：mapDomain_injective {f : α -> β} (hf : Func
tion.Injective f) : Function.Injective (mapDomain f : (α ->₀ M) -> β ->₀ M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
-/
theorem coeff_rename_mapDomain (f : σ → τ) (hf : Injective f) (φ : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (rename f φ).coeff (d.mapDomain f) = φ.coeff d := by
  classical
  induction φ using MvPolynomial.induction_on' with
  | monomial u r =>
    rw [rename_monomial, coeff_monomial, coeff_monomial]
    simp only [(Finsupp.mapDomain_injective hf).eq_iff]
  | add =>
    simp only [*, map_add, coeff_add]

@[simp]
/-
**MvPolynomial.coeff_rename_embDomain** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_rename_embDomain (f : σ ↪ τ) (φ : MvPolynomial σ R) (d : σ ->₀ Nat) 
: (rename f φ).coeff (d.embDomain f) = φ.coeff d
参数：f : σ ↪ τ；φ : MvPolynomial σ R；d : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.embDomain_eq_mapDomain`：embDomain_eq_mapDomain (f : α ↪ β) (v : 
α ->₀ M) : embDomain f v = mapDomain f v
· 使用定理 `MvPolynomial.coeff_rename_mapDomain`：coeff_rename_mapDomain (f : σ -> τ)
 (hf : Injective f) (φ : MvPolynomial σ R) (d : σ ->₀ Nat) : (rename f φ).coeff 
(d.mapDomain f) = φ.coeff…
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem coeff_rename_embDomain (f : σ ↪ τ) (φ : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (rename f φ).coeff (d.embDomain f) = φ.coeff d := by
  rw [Finsupp.embDomain_eq_mapDomain f, coeff_rename_mapDomain f f.injective]

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.coeff_rename_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_rename_eq_zero (f : σ -> τ) (φ : MvPolynomial σ R) (d : τ ->₀ Nat) (
h : forall u : σ ->₀ Nat, u.mapDomain f = d -> φ.coeff u = 0) : (rename f φ).coe
ff d = 0
参数：f : σ -> τ；φ : MvPolynomial σ R；d : τ ->₀ Nat；h : forall u : σ ->₀ Nat, u.map
Domain f = d -> φ.coeff u = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.notMem_support_iff`：notMem_support_iff {p : MvPolynomial σ 
R} {m : σ ->₀ Nat} : m ∉ p.support ↔ p.coeff m = 0
· 使用定理 `Finsupp.mapDomain_support`：mapDomain_support [DecidableEq β] {f : α -> β
} {s : α ->₀ M} : (s.mapDomain f).support subseteq s.support.image f
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
-/
theorem coeff_rename_eq_zero (f : σ → τ) (φ : MvPolynomial σ R) (d : τ →₀ ℕ)
    (h : ∀ u : σ →₀ ℕ, u.mapDomain f = d → φ.coeff u = 0) : (rename f φ).coeff d = 0 := by
  classical
  rw [← notMem_support_iff]
  intro H
  replace H := mapDomain_support H
  rw [Finset.mem_image] at H
  obtain ⟨u, hu, rfl⟩ := H
  specialize h u rfl
  rw [Finsupp.mem_support_iff] at hu
  contradiction
/-
**MvPolynomial.coeff_rename_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_rename_ne_zero (f : σ -> τ) (φ : MvPolynomial σ R) (d : τ ->₀ Nat) (
h : (rename f φ).coeff d != 0) : exists u : σ ->₀ Nat, u.mapDomain f = d ∧ φ.coe
ff u != 0
参数：f : σ -> τ；φ : MvPolynomial σ R；d : τ ->₀ Nat；h : (rename f φ).coeff d != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `MvPolynomial.coeff_rename_eq_zero`：coeff_rename_eq_zero (f : σ -> τ) (φ 
: MvPolynomial σ R) (d : τ ->₀ Nat) (h : forall u : σ ->₀ Nat, u.mapDomain f = d
 -> φ.coeff u = 0) : (r…
-/
theorem coeff_rename_ne_zero (f : σ → τ) (φ : MvPolynomial σ R) (d : τ →₀ ℕ)
    (h : (rename f φ).coeff d ≠ 0) : ∃ u : σ →₀ ℕ, u.mapDomain f = d ∧ φ.coeff u ≠ 0 := by
  contrapose! h
  apply coeff_rename_eq_zero _ _ _ h

@[simp]
/-
**MvPolynomial.constantCoeff_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：constantCoeff_rename {τ : Type*} (f : σ -> τ) (φ : MvPolynomial σ R) : con
stantCoeff (rename f φ) = constantCoeff φ
参数：f : σ -> τ；φ : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_C`：rename_C (f : σ -> τ) (r : R) : rename f (C r) = 
C r
· 使用定理 `MvPolynomial.constantCoeff_C`：constantCoeff_C (r : R) : constantCoeff (C
 r : MvPolynomial σ R) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MvPolynomial.constantCoeff_X`：constantCoeff_X (i : σ) : constantCoeff (X
 i : MvPolynomial σ R) = 0
-/
theorem constantCoeff_rename {τ : Type*} (f : σ → τ) (φ : MvPolynomial σ R) :
    constantCoeff (rename f φ) = constantCoeff φ := by
  apply φ.induction_on
  · intro a
    simp only [constantCoeff_C, rename_C]
  · intro p q hp hq
    simp only [hp, hq, map_add]
  · intro p n hp
    simp only [hp, rename_X, constantCoeff_X, map_mul]

end Coeff

section Support

/-
**MvPolynomial.support_rename_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：support_rename_of_injective {p : MvPolynomial σ R} {f : σ -> τ} [Decidable
Eq τ] (h : Function.Injective f) : (rename f p).support = Finset.image (Finsupp.
mapDomain f) p.support
参数：h : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mapDomain_support_of_injective`：mapDomain_support_of_injective [
DecidableEq β] {f : α -> β} (hf : Function.Injective f) (s : α ->₀ M) : (mapDoma
in f s).support = Finset.ima…
· 使用定理 `Finsupp.mapDomain_injective`：mapDomain_injective {f : α -> β} (hf : Func
tion.Injective f) : Function.Injective (mapDomain f : (α ->₀ M) -> β ->₀ M)
-/
theorem support_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} [DecidableEq τ]
    (h : Function.Injective f) :
    (rename f p).support = Finset.image (Finsupp.mapDomain f) p.support :=
  Finsupp.mapDomain_support_of_injective (Finsupp.mapDomain_injective h) _
/-
**MvPolynomial.support_rename_killCompl_subset** 是 Mathlib 中的一个引理，位于命名空间 `MvPoly
nomial`。
形式化陈述：support_rename_killCompl_subset {p : MvPolynomial τ R} {f : σ -> τ} (hf : 
f.Injective) : ((p.killCompl hf).rename f).support subseteq p.support
参数：hf : f.Injective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.support_rename_of_injective`：support_rename_of_injective {p
 : MvPolynomial σ R} {f : σ -> τ} [DecidableEq τ] (h : Function.Injective f) : (
rename f p).support = Finset.i…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Finsupp.mapDomain_injective`：mapDomain_injective {f : α -> β} (hf : Func
tion.Injective f) : Function.Injective (mapDomain f : (α ->₀ M) -> β ->₀ M)
· 使用引理 `MvPolynomial.support_killCompl`：support_killCompl {p : MvPolynomial τ R}
 : (p.killCompl hf).support = p.support.preimage (Finsupp.mapDomain f) (Finsupp.
mapDomain_injective …
· 使用定理 `Finset.image_preimage`：image_preimage [DecidableEq β] (f : α -> β) (s : 
Finset β) [forall x, Decidable (x in Set.range f)] (hf : Set.InjOn f (f ⁻¹' ↑s))
 : image f …
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
-/
lemma support_rename_killCompl_subset {p : MvPolynomial τ R} {f : σ → τ} (hf : f.Injective) :
    ((p.killCompl hf).rename f).support ⊆ p.support := by
  classical
  rw [MvPolynomial.support_rename_of_injective hf, support_killCompl, Finset.image_preimage]
  exact Finset.filter_subset ..

end Support

end MvPolynomial

