/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.Order.Ring.Finset

/-!
## Expand multivariate polynomials

Given a multivariate polynomial `φ`, one may replace every occurrence of `X i` by `X i ^ n`,
for some natural number `n`.
This operation is called `MvPolynomial.expand` and it is an algebra homomorphism.

### Main declaration

* `MvPolynomial.expand`: expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/

@[expose] public section


namespace MvPolynomial

section CommSemiring

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

See also `Polynomial.expand`. -/
/-
**MvPolynomial.expand** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：expand : MvPolynomial σ R ->ₐ[R] MvPolynomial σ R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

See also `Polynomial.expand`.
-/
noncomputable def expand : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  bind₁ fun i ↦ X i ^ p
/-
**MvPolynomial.coe_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_expand : (expand p (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_expand :
    (expand p (R := R) (σ := σ)) = eval₂ C ((fun s ↦ X s : σ → MvPolynomial σ R) ^ p) := rfl
/-
**MvPolynomial.expand_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_C (r : R) : expand p (C r : MvPolynomial σ R) = C r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂Hom_C`：eval₂Hom_C (f : R ->+* S₁) (g : σ -> S₁) (r : R
) : eval₂Hom f g (C r) = f r
-/
theorem expand_C (r : R) : expand p (C r : MvPolynomial σ R) = C r :=
  eval₂Hom_C _ _ _

@[simp]
/-
**MvPolynomial.expand_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_X (i : σ) : expand p (X i : MvPolynomial σ R) = X i ^ p
参数：i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂Hom_X'`：eval₂Hom_X' (f : R ->+* S₁) (g : σ -> S₁) (i :
 σ) : eval₂Hom f g (X i) = g i
-/
theorem expand_X (i : σ) : expand p (X i : MvPolynomial σ R) = X i ^ p :=
  eval₂Hom_X' _ _ _

@[simp]
/-
**MvPolynomial.expand_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_monomial (d : σ ->₀ Nat) (r : R) : expand p (monomial d r) = monomi
al (p • d) r
参数：d : σ ->₀ Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.expand.eq_1`：∀ {σ : Type u_1} {R : Type u_3} [inst : CommSe
miring R] (p : ℕ),   MvPolynomial.expand p = MvPolynomial.bind₁ fun i => MvPolyn
omial.X i ^ p
· 使用定理 `MvPolynomial.bind₁_monomial`：bind₁_monomial (f : σ -> MvPolynomial τ R) 
(d : σ ->₀ Nat) (r : R) : bind₁ f (monomial d r) = C r * ∏ i in d.support, f i ^
 d i
· 使用定理 `MvPolynomial.monomial_eq`：monomial_eq : monomial s a = C a * (s.prod fun
 n e => X n ^ e : MvPolynomial σ R)
· 使用定理 `Finsupp.prod_of_support_subset`：prod_of_support_subset (f : α ->₀ M) {s 
: Finset α} (hs : f.support subseteq s) (g : α -> M -> N) (h : forall i in s, g 
i 0 = 1) : f.prod g …
· 使用定理 `Finsupp.support_smul`：support_smul [Zero M] [SMulZeroClass R M] {b : R} 
{g : α ->₀ M} : (b • g).support subseteq g.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
-/
theorem expand_monomial (d : σ →₀ ℕ) (r : R) :
    expand p (monomial d r) = monomial (p • d) r := by
  rw [expand, bind₁_monomial, monomial_eq, Finsupp.prod_of_support_subset _ Finsupp.support_smul]
  · simp [pow_mul]
  · simp

@[simp]
/-
**MvPolynomial.expand_zero** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_zero : expand 0 (σ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.expand_X`：expand_X (i : σ) : expand p (X i : MvPolynomial σ
 R) = X i ^ p
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expand_zero :
    expand 0 (σ := σ) (R := R) = .comp (Algebra.ofId R _) (MvPolynomial.aeval (1 : σ → R)) := by
  ext1 i
  simp
/-
**MvPolynomial.expand_zero_apply** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_zero_apply (f : MvPolynomial σ R) : expand 0 f = .C (MvPolynomial.e
val 1 f)
参数：f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.expand_zero`：expand_zero : expand 0 (σ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expand_zero_apply (f : MvPolynomial σ R) : expand 0 f = .C (MvPolynomial.eval 1 f) := by
  simp

@[simp]
/-
**MvPolynomial.expand_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_one : expand 1 = AlgHom.id R (MvPolynomial σ R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.expand_X`：expand_X (i : σ) : expand p (X i : MvPolynomial σ
 R) = X i ^ p
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expand_one : expand 1 = AlgHom.id R (MvPolynomial σ R) := by
  ext1 i
  simp
/-
**MvPolynomial.expand_one_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_one_apply (f : MvPolynomial σ R) : expand 1 f = f
参数：f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.expand_one`：expand_one : expand 1 = AlgHom.id R (MvPolynomi
al σ R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expand_one_apply (f : MvPolynomial σ R) : expand 1 f = f := by simp
/-
**MvPolynomial.expand_mul_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_mul_eq_comp (q : Nat) : expand (σ
参数：q : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.expand_X`：expand_X (i : σ) : expand p (X i : MvPolynomial σ
 R) = X i ^ p
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expand_mul_eq_comp (q : ℕ) :
    expand (σ := σ) (R := R) (p * q) = (expand p).comp (expand q) := by
  ext1 i
  simp [pow_mul]
/-
**MvPolynomial.expand_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_mul (q : Nat) (φ : MvPolynomial σ R) : φ.expand (p * q) = (φ.expand
 q).expand p
参数：q : Nat；φ : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `MvPolynomial.expand_mul_eq_comp`：expand_mul_eq_comp (q : Nat) : expand (
σ
-/
theorem expand_mul (q : ℕ) (φ : MvPolynomial σ R) : φ.expand (p * q) = (φ.expand q).expand p :=
  DFunLike.congr_fun (expand_mul_eq_comp p q) φ

@[simp]
/-
**MvPolynomial.coeff_expand_smul** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_expand_smul (hp : p != 0) (φ : MvPolynomial σ R) (m : σ ->₀ Nat) : (
expand p φ).coeff (p • m) = φ.coeff m
参数：hp : p != 0；φ : MvPolynomial σ R；m : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on'`：induction_on' {P : MvPolynomial σ R -> Prop}
 (p : MvPolynomial σ R) (monomial : forall (u : σ ->₀ Nat) (a : R), P (monomial 
u a)) (add : for…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.expand_monomial`：expand_monomial (d : σ ->₀ Nat) (r : R) : 
expand p (monomial d r) = monomial (p • d) r
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
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
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
-/
lemma coeff_expand_smul (hp : p ≠ 0) (φ : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (expand p φ).coeff (p • m) = φ.coeff m := by
  classical
  induction φ using induction_on' <;> simp [*, nsmul_right_inj hp]

@[simp]
/-
**MvPolynomial.coeff_expand_zero** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_expand_zero (hp : p != 0) (φ : MvPolynomial σ R) : (expand p φ).coef
f 0 = φ.coeff 0
参数：hp : p != 0；φ : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `MvPolynomial.coeff_expand_smul`：coeff_expand_smul (hp : p != 0) (φ : MvP
olynomial σ R) (m : σ ->₀ Nat) : (expand p φ).coeff (p • m) = φ.coeff m
-/
lemma coeff_expand_zero (hp : p ≠ 0) (φ : MvPolynomial σ R) :
    (expand p φ).coeff 0 = φ.coeff 0 :=
  calc (expand p φ).coeff 0 = (expand p φ).coeff (p • 0) := by rw [smul_zero]
                          _ = φ.coeff 0 := by rw [coeff_expand_smul p hp]

/-- Expansion is injective. -/
/-
**MvPolynomial.expand_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_injective {n : Nat} (hn : 0 < n) : Function.Injective (expand n (R
参数：hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MvPolynomial.coeff_expand_smul`：coeff_expand_smul (hp : p != 0) (φ : MvP
olynomial σ R) (m : σ ->₀ Nat) : (expand p φ).coeff (p • m) = φ.coeff m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.ne_zero_iff_zero_lt`：∀ {n : ℕ}, n ≠ 0 ↔ 0 < n

--- 原说明 ---
Expansion is injective.
-/
theorem expand_injective {n : ℕ} (hn : 0 < n) : Function.Injective (expand n (R := R) (σ := σ)) :=
  fun g g' H => by
    ext d
    rw [← coeff_expand_smul _ (n.ne_zero_iff_zero_lt.mpr hn), H, coeff_expand_smul _
      (n.ne_zero_iff_zero_lt.mpr hn)]
/-
**MvPolynomial.expand_inj** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_inj {p : Nat} (hp : 0 < p) {f g : MvPolynomial σ R} : expand p f = 
expand p g ↔ f = g
参数：hp : 0 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MvPolynomial.expand_injective`：expand_injective {n : Nat} (hn : 0 < n) :
 Function.Injective (expand n (R
-/
theorem expand_inj {p : ℕ} (hp : 0 < p) {f g : MvPolynomial σ R} :
    expand p f = expand p g ↔ f = g := (expand_injective hp).eq_iff
/-
**MvPolynomial.expand_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_eq_zero {p : Nat} (hp : 0 < p) {f : MvPolynomial σ R} : expand p f 
= 0 ↔ f = 0
参数：hp : 0 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `MvPolynomial.expand_injective`：expand_injective {n : Nat} (hn : 0 < n) :
 Function.Injective (expand n (R
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem expand_eq_zero {p : ℕ} (hp : 0 < p) {f : MvPolynomial σ R} : expand p f = 0 ↔ f = 0 :=
  (expand_injective hp).eq_iff' (map_zero _)
/-
**MvPolynomial.expand_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_ne_zero {p : Nat} (hp : 0 < p) {f : MvPolynomial σ R} : expand p f 
!= 0 ↔ f != 0
参数：hp : 0 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MvPolynomial.expand_eq_zero`：expand_eq_zero {p : Nat} (hp : 0 < p) {f : 
MvPolynomial σ R} : expand p f = 0 ↔ f = 0
-/
theorem expand_ne_zero {p : ℕ} (hp : 0 < p) {f : MvPolynomial σ R} : expand p f ≠ 0 ↔ f ≠ 0 :=
  (expand_eq_zero hp).not
/-
**MvPolynomial.expand_eq_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：expand_eq_C {p : Nat} (hp : 0 < p) {f : MvPolynomial σ R} {r : R} : expand
 p f = C r ↔ f = C r
参数：hp : 0 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.expand_C`：expand_C (r : R) : expand p (C r : MvPolynomial σ
 R) = C r
· 使用定理 `MvPolynomial.expand_inj`：expand_inj {p : Nat} (hp : 0 < p) {f g : MvPoly
nomial σ R} : expand p f = expand p g ↔ f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem expand_eq_C {p : ℕ} (hp : 0 < p) {f : MvPolynomial σ R} {r : R} :
    expand p f = C r ↔ f = C r := by
  rw [← expand_C, expand_inj hp, expand_C]
/-
**MvPolynomial.expand_comp_bind** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem expand_comp_bind₁ (p : ℕ) (f : σ → MvPolynomial τ R) :
    (expand p).comp (bind₁ f) = bind₁ fun i ↦ expand p (f i) := by
  ext1 i
  simp
/-
**MvPolynomial.expand_bind** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem expand_bind₁ (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    expand p (bind₁ f φ) = bind₁ (fun i ↦ expand p (f i)) φ := by
  rw [← AlgHom.comp_apply, expand_comp_bind₁]

@[simp]
/-
**MvPolynomial.map_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_expand (f : R ->+* S) (φ : MvPolynomial σ R) : map f (expand p φ) = ex
pand p (map f φ)
参数：f : R ->+* S；φ : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.map_bind₁`：map_bind₁ (f : R ->+* S) (g : σ -> MvPolynomial 
τ R) (φ : MvPolynomial σ R) : map f (bind₁ g φ) = bind₁ (fun i : σ => (map f) (g
 i)) (map f …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_expand (f : R →+* S) (φ : MvPolynomial σ R) :
    map f (expand p φ) = expand p (map f φ) := by simp [expand, map_bind₁]

@[simp]
/-
**MvPolynomial.rename_comp_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_comp_expand (f : σ -> τ) : (rename f).comp (expand p) = (expand p).
comp (rename f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R)
参数：f : σ -> τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.expand_X`：expand_X (i : σ) : expand p (X i : MvPolynomial σ
 R) = X i ^ p
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rename_comp_expand (f : σ → τ) :
    (rename f).comp (expand p) =
      (expand p).comp (rename f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) := by
  ext1 i
  simp

@[simp]
/-
**MvPolynomial.rename_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_expand (f : σ -> τ) (φ : MvPolynomial σ R) : rename f (expand p φ) 
= expand p (rename f φ)
参数：f : σ -> τ；φ : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `MvPolynomial.rename_comp_expand`：rename_comp_expand (f : σ -> τ) : (rena
me f).comp (expand p) = (expand p).comp (rename f : MvPolynomial σ R ->ₐ[R] MvPo
lynomial τ R)
-/
theorem rename_expand (f : σ → τ) (φ : MvPolynomial σ R) :
    rename f (expand p φ) = expand p (rename f φ) :=
  DFunLike.congr_fun (rename_comp_expand p f) φ
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eval₂Hom_comp_expand (f : R →+* S) (g : σ → S) :
    (eval₂Hom f g).comp (expand p (σ := σ) (R := R) : MvPolynomial σ R →+* MvPolynomial σ R) =
      eval₂Hom f (g ^ p) := by
  ext <;> simp

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eval₂_expand (f : R →+* S) (g : σ → S) (φ : MvPolynomial σ R) :
    eval₂ f g (expand p φ) = eval₂ f (g ^ p) φ :=
  DFunLike.congr_fun (eval₂Hom_comp_expand p f g) φ

@[simp]
/-
**MvPolynomial.aeval_comp_expand** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_comp_expand {A : Type*} [CommSemiring A] [Algebra R A] (f : σ -> A) 
: (aeval f).comp (expand p) = aeval (R
参数：f : σ -> A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.expand_X`：expand_X (i : σ) : expand p (X i : MvPolynomial σ
 R) = X i ^ p
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma aeval_comp_expand {A : Type*} [CommSemiring A] [Algebra R A] (f : σ → A) :
    (aeval f).comp (expand p) = aeval (R := R) (f ^ p) := by
  ext; simp

@[simp]
/-
**MvPolynomial.aeval_expand** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_expand {A : Type*} [CommSemiring A] [Algebra R A] (f : σ -> A) (φ : 
MvPolynomial σ R) : aeval f (expand p φ) = aeval (f ^ p) φ
参数：f : σ -> A；φ : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPolynomial.eval₂_expand`：eval₂_expand (f : R ->+* S) (g : σ -> S) (φ :
 MvPolynomial σ R) : eval₂ f g (expand p φ) = eval₂ f (g ^ p) φ
-/
lemma aeval_expand {A : Type*} [CommSemiring A] [Algebra R A]
    (f : σ → A) (φ : MvPolynomial σ R) :
    aeval f (expand p φ) = aeval (f ^ p) φ :=
  eval₂_expand ..

@[simp]
/-
**MvPolynomial.eval_expand** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_expand (f : σ -> R) (φ : MvPolynomial σ R) : eval f (expand p φ) = ev
al (f ^ p) φ
参数：f : σ -> R；φ : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPolynomial.eval₂_expand`：eval₂_expand (f : R ->+* S) (g : σ -> S) (φ :
 MvPolynomial σ R) : eval₂ f g (expand p φ) = eval₂ f (g ^ p) φ
-/
lemma eval_expand (f : σ → R) (φ : MvPolynomial σ R) :
    eval f (expand p φ) = eval (f ^ p) φ :=
  eval₂_expand ..

section

variable {p} (φ : MvPolynomial σ R)

/-
**MvPolynomial.support_expand_subset** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：support_expand_subset [DecidableEq σ] : (expand p φ).support subseteq φ.su
pport.image (p • ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.as_sum`：as_sum (p : MvPolynomial σ R) : p = ∑ v in p.suppor
t, monomial v (coeff v p)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.expand_monomial`：expand_monomial (d : σ ->₀ Nat) (r : R) : 
expand p (monomial d r) = monomial (p • d) r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MvPolynomial.support_sum`：support_sum {α : Type*} [DecidableEq σ] {s : F
inset α} {f : α -> MvPolynomial σ R} : (∑ x in s, f x).support subseteq s.biUnio
n fun x => (f …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma support_expand_subset [DecidableEq σ] :
    (expand p φ).support ⊆ φ.support.image (p • ·) := by
  conv_lhs => rw [φ.as_sum]
  simp only [map_sum, expand_monomial]
  refine MvPolynomial.support_sum.trans ?_
  aesop (add simp Finset.subset_iff)
/-
**MvPolynomial.coeff_expand_of_not_dvd** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_expand_of_not_dvd {m : σ ->₀ Nat} {i : σ} (h : ¬ p ∣ m i) : (expand 
p φ).coeff m = 0
参数：h : ¬ p ∣ m i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `mem_of_le_of_mem`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike A B] [
inst_1 : LE A] [IsConcreteLE A B] {S T : A},   S ≤ T → ∀ ⦃x : B⦄, x ∈ S → x ∈ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用引理 `MvPolynomial.support_expand_subset`：support_expand_subset [DecidableEq σ
] : (expand p φ).support subseteq φ.support.image (p • ·)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_expand_of_not_dvd {m : σ →₀ ℕ} {i : σ} (h : ¬ p ∣ m i) :
    (expand p φ).coeff m = 0 := by
  classical
  contrapose! h
  grw [← mem_support_iff, support_expand_subset, Finset.mem_image] at h
  rcases h with ⟨a, -, rfl⟩
  exact ⟨a i, by simp⟩
/-
**MvPolynomial.support_expand** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：support_expand [DecidableEq σ] (hp : p != 0) : (expand p φ).support = φ.su
pport.image (p • ·)
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `MvPolynomial.support_expand_subset`：support_expand_subset [DecidableEq σ
] : (expand p φ).support subseteq φ.support.image (p • ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.coeff_expand_smul`：coeff_expand_smul (hp : p != 0) (φ : MvP
olynomial σ R) (m : σ ->₀ Nat) : (expand p φ).coeff (p • m) = φ.coeff m
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma support_expand [DecidableEq σ] (hp : p ≠ 0) :
    (expand p φ).support = φ.support.image (p • ·) := by
  refine (support_expand_subset φ).antisymm ?_
  simp [Finset.image_subset_iff, hp]
/-
**MvPolynomial.totalDegree_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_expand (f : MvPolynomial σ R) : (expand p f).totalDegree = f.t
otalDegree * p
参数：f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MvPolynomial.expand_zero`：expand_zero : expand 0 (σ
· 使用定理 `MvPolynomial.totalDegree_C`：totalDegree_C (a : R) : (C a : MvPolynomial 
σ R).totalDegree = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MvPolynomial.totalDegree_zero`：totalDegree_zero : (0 : MvPolynomial σ R)
.totalDegree = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MvPolynomial.totalDegree_eq`：totalDegree_eq (p : MvPolynomial σ R) : p.t
otalDegree = p.support.sup fun m => Multiset.card (toMultiset m)
· 使用引理 `MvPolynomial.support_expand`：support_expand [DecidableEq σ] (hp : p != 0
) : (expand p φ).support = φ.support.image (p • ·)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.ne_zero_iff_zero_lt`：∀ {n : ℕ}, n ≠ 0 ↔ 0 < n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.card_toMultiset`：card_toMultiset (f : α ->₀ Nat) : Multiset.card
 (toMultiset f) = f.sum fun _ => id
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用引理 `Finset.sup_mul₀`：Finset.sup_mul₀ (s : Finset ι) (f : ι -> R) (a : R) : s
.sup f * a = s.sup (f · * a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …
· 使用定理 `Finsupp.support_smul`：support_smul [Zero M] [SMulZeroClass R M] {b : R} 
{g : α ->₀ M} : (b • g).support subseteq g.support
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 34 条，此处仅展示前 30 条）
-/
theorem totalDegree_expand (f : MvPolynomial σ R) :
    (expand p f).totalDegree = f.totalDegree * p := by
  classical
  rcases p.eq_zero_or_pos with hp | hp
  · simp [hp]
  by_cases hf : f = 0
  · rw [hf, map_zero, totalDegree_zero, zero_mul]
  simp_rw [totalDegree_eq, support_expand _ (p.ne_zero_iff_zero_lt.mpr hp)]
  simp only [Finsupp.card_toMultiset, Finset.sup_image, Finset.sup_mul₀, Function.comp_def]
  congr! 2 with d
  rw [Finsupp.sum_of_support_subset _ Finsupp.support_smul _ (by simp)]
  simp [Finsupp.sum, Finset.sum_mul, mul_comm p]

end

end CommSemiring

section CommRing

variable (R σ : Type*) [CommRing R]

/-
**MvPolynomial.isLocalHom_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：isLocalHom_expand {p : Nat} (hp : p != 0) : IsLocalHom (expand p (R
参数：hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.isUnit_iff`：isUnit_iff : IsUnit P ↔ IsUnit (P.coeff 0) ∧ fo
rall i != 0, IsNilpotent (P.coeff i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MvPolynomial.coeff_expand_zero`：coeff_expand_zero (hp : p != 0) (φ : MvP
olynomial σ R) : (expand p φ).coeff 0 = φ.coeff 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MvPolynomial.coeff_expand_smul`：coeff_expand_smul (hp : p != 0) (φ : MvP
olynomial σ R) (m : σ ->₀ Nat) : (expand p φ).coeff (p • m) = φ.coeff m
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem isLocalHom_expand {p : ℕ} (hp : p ≠ 0) : IsLocalHom (expand p (R := R) (σ := σ)) := by
  refine ⟨fun f hf => ?_⟩
  rw [MvPolynomial.isUnit_iff] at hf ⊢
  simp only [coeff_expand_zero p hp] at hf
  refine ⟨hf.1, fun i hi ↦ ?_⟩
  rw [← coeff_expand_smul p hp]
  apply hf.2
  simp [hi, hp]

variable {R}
/-
**MvPolynomial.of_irreducible_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：of_irreducible_expand {p : Nat} (hp : p != 0) {f : MvPolynomial σ R} (hf :
 Irreducible (expand p f)) : Irreducible f
参数：hp : p != 0；hf : Irreducible (expand p f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.isLocalHom_expand`：isLocalHom_expand {p : Nat} (hp : p != 0
) : IsLocalHom (expand p (R
· 使用引理 `Irreducible.of_map`：Irreducible.of_map [FunLike F M N] [MonoidHomClass F
 M N] [IsLocalHom f] (hfx : Irreducible (f x)) : Irreducible x where not_isUnit 
hu
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem of_irreducible_expand {p : ℕ} (hp : p ≠ 0) {f : MvPolynomial σ R}
    (hf : Irreducible (expand p f)) :
    Irreducible f :=
  let _ := isLocalHom_expand R σ hp
  hf.of_map

end CommRing

end MvPolynomial

