/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro, Elias Judin
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Fin
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.Finsupp.Option
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Equivalences between polynomial rings

This file establishes a number of equivalences between polynomial rings,
based on equivalences between the underlying types.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`.

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

## Tags

equivalence, isomorphism, morphism, ring hom, hom

-/

@[expose] public section


noncomputable section

open Polynomial Set Function Finsupp AddMonoidAlgebra

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

section Equiv

variable (R) [CommSemiring R]

/-- The algebra isomorphism between multivariable polynomials indexed by a type with a unique
element and polynomials over the ground ring. -/
@[simps]
/-
**MvPolynomial.uniqueAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：uniqueAlgEquiv (σ : Type*) [Unique σ] : MvPolynomial σ R ≃ₐ[R] R[X] where 
toFun
参数：σ : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra isomorphism between multivariable polynomials indexed by a type with
 a unique
element and polynomials over the ground ring.
-/
def uniqueAlgEquiv (σ : Type*) [Unique σ] : MvPolynomial σ R ≃ₐ[R] R[X] where
  toFun := eval₂ Polynomial.C fun _ => Polynomial.X
  invFun := Polynomial.eval₂ MvPolynomial.C (X default)
  left_inv := by
    let f : R[X] →+* MvPolynomial σ R := Polynomial.eval₂RingHom MvPolynomial.C (X default)
    let g : MvPolynomial σ R →+* R[X] := eval₂Hom Polynomial.C fun _ => Polynomial.X
    change ∀ p, f.comp g p = p
    apply is_id
    · ext a
      dsimp [f, g]
      rw [eval₂_C, Polynomial.eval₂_C]
    · intro i
      dsimp [f, g]
      rw [eval₂_X, Polynomial.eval₂_X]
      rw [← Unique.eq_default i]
  right_inv p :=
    Polynomial.induction_on p (fun a => by rw [Polynomial.eval₂_C, MvPolynomial.eval₂_C])
    (fun p q hp hq => by rw [Polynomial.eval₂_add, MvPolynomial.eval₂_add, hp, hq]) fun p n _ => by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  map_mul' _ _ := eval₂_mul _ _
  map_add' _ _ := eval₂_add _ _
  commutes' _ := eval₂_C _ _ _
/-
**MvPolynomial.uniqueAlgEquiv_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：uniqueAlgEquiv_monomial [Unique σ] {d : σ ->₀ Nat} {r : R} : (MvPolynomial
.uniqueAlgEquiv R σ) (MvPolynomial.monomial d r) = Polynomial.monomial (d defaul
t) r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.uniqueAlgEquiv_apply`：∀ (R : Type u) [inst : CommSemiring R
] (σ : Type u_2) [inst_1 : Unique σ] (p : MvPolynomial σ R),   (MvPolynomial.uni
queAlgEquiv R σ) p = Mv…
· 使用定理 `MvPolynomial.eval₂_monomial`：eval₂_monomial : (monomial s a).eval₂ f g =
 f a * s.prod fun n e => g n ^ e
· 使用定理 `Finsupp.prod_pow`：prod_pow [Fintype α] (f : α ->₀ Nat) (g : α -> N) : (f
.prod fun a b => g a ^ b) = ∏ a, g a ^ f a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniqueAlgEquiv_monomial [Unique σ] {d : σ →₀ ℕ} {r : R} :
    (MvPolynomial.uniqueAlgEquiv R σ) (MvPolynomial.monomial d r)
      = Polynomial.monomial (d default) r := by
  simp [Polynomial.C_mul_X_pow_eq_monomial]
/-
**MvPolynomial.uniqueAlgEquiv_symm_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynom
ial`。
形式化陈述：uniqueAlgEquiv_symm_monomial [Unique σ] {d : σ ->₀ Nat} {r : R} : (MvPolyn
omial.uniqueAlgEquiv R σ).symm (Polynomial.monomial (d default) r) = MvPolynomia
l.monomial d r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.uniqueAlgEquiv_symm_apply`：∀ (R : Type u) [inst : CommSemir
ing R] (σ : Type u_2) [inst_1 : Unique σ] (p : Polynomial R),   (MvPolynomial.un
iqueAlgEquiv R σ).symm p = P…
· 使用定理 `Polynomial.eval₂_monomial`：eval₂_monomial {n : Nat} {r : R} : (monomial 
n r).eval₂ f x = f r * x ^ n
· 使用定理 `MvPolynomial.monomial_eq`：monomial_eq : monomial s a = C a * (s.prod fun
 n e => X n ^ e : MvPolynomial σ R)
· 使用定理 `Finsupp.prod_pow`：prod_pow [Fintype α] (f : α ->₀ Nat) (g : α -> N) : (f
.prod fun a b => g a ^ b) = ∏ a, g a ^ f a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniqueAlgEquiv_symm_monomial [Unique σ] {d : σ →₀ ℕ} {r : R} :
    (MvPolynomial.uniqueAlgEquiv R σ).symm (Polynomial.monomial (d default) r)
      = MvPolynomial.monomial d r := by
  simp [MvPolynomial.monomial_eq]

/-- The coefficient of `X ^ n` in `uniqueAlgEquiv R σ P` is the coefficient of the unique
monomial of degree `n` in `P`. -/
/-
**MvPolynomial.coeff_uniqueAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_uniqueAlgEquiv [Unique σ] (P : MvPolynomial σ R) (n : Nat) : (MvPoly
nomial.uniqueAlgEquiv R σ P : Polynomial R).coeff n = coeff (Finsupp.single defa
ult n) P
参数：P : MvPolynomial σ R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on'`：induction_on' {P : MvPolynomial σ R -> Prop}
 (p : MvPolynomial σ R) (monomial : forall (u : σ ->₀ Nat) (a : R), P (monomial 
u a)) (add : for…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.uniqueAlgEquiv_monomial`：uniqueAlgEquiv_monomial [Unique σ]
 {d : σ ->₀ Nat} {r : R} : (MvPolynomial.uniqueAlgEquiv R σ) (MvPolynomial.monom
ial d r) = Polynomial.mono…
· 使用定理 `Finsupp.unique_single`：unique_single [Unique α] (x : α ->₀ M) : x = sing
le default (x default)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.uniqueAlgEquiv_apply`：∀ (R : Type u) [inst : CommSemiring R
] (σ : Type u_2) [inst_1 : Unique σ] (p : MvPolynomial σ R),   (MvPolynomial.uni
queAlgEquiv R σ) p = Mv…
· 使用定理 `MvPolynomial.eval₂_add`：eval₂_add : (p + q).eval₂ f g = p.eval₂ f g + q.
eval₂ f g
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
· 使用定理 `congrArg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ
) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'

--- 原说明 ---
The coefficient of `X ^ n` in `uniqueAlgEquiv R σ P` is the coefficient of the u
nique
monomial of degree `n` in `P`.
-/
theorem coeff_uniqueAlgEquiv [Unique σ] (P : MvPolynomial σ R) (n : ℕ) :
    (MvPolynomial.uniqueAlgEquiv R σ P : Polynomial R).coeff n =
      coeff (Finsupp.single default n) P := by
  induction P using induction_on' with
  | monomial d r =>
      rw [uniqueAlgEquiv_monomial, Finsupp.unique_single d]
      simp [Polynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  | add P Q hP hQ =>
      simpa using congrArg₂ (· + ·) hP hQ

/-- The coefficient of a monomial in `(uniqueAlgEquiv R σ).symm P` is the coefficient of the
corresponding univariate monomial in `P`. -/
/-
**MvPolynomial.coeff_uniqueAlgEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：coeff_uniqueAlgEquiv_symm [Unique σ] (P : Polynomial R) (d : σ ->₀ Nat) : 
coeff d ((MvPolynomial.uniqueAlgEquiv R σ).symm P) = P.coeff (d default)
参数：P : Polynomial R；d : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.unique_single`：unique_single [Unique α] (x : α ->₀ M) : x = sing
le default (x default)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.coeff_uniqueAlgEquiv`：coeff_uniqueAlgEquiv [Unique σ] (P : 
MvPolynomial σ R) (n : Nat) : (MvPolynomial.uniqueAlgEquiv R σ P : Polynomial R)
.coeff n = coeff (Finsu…
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b

--- 原说明 ---
The coefficient of a monomial in `(uniqueAlgEquiv R σ).symm P` is the coefficien
t of the
corresponding univariate monomial in `P`.
-/
theorem coeff_uniqueAlgEquiv_symm [Unique σ] (P : Polynomial R) (d : σ →₀ ℕ) :
    coeff d ((MvPolynomial.uniqueAlgEquiv R σ).symm P) = P.coeff (d default) := by
  rw [Finsupp.unique_single d, ← coeff_uniqueAlgEquiv R, AlgEquiv.apply_symm_apply,
    Finsupp.single_eq_same]

/-- The algebra isomorphism between multivariable polynomials in a single variable and
polynomials over the ground ring. -/
@[deprecated uniqueAlgEquiv (since := "2026-04-15")]
/-
**MvPolynomial.pUnitAlgEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `MvPolynomial`。
形式化陈述：pUnitAlgEquiv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra isomorphism between multivariable polynomials in a single variable a
nd
polynomials over the ground ring.
-/
abbrev pUnitAlgEquiv := uniqueAlgEquiv (R := R) PUnit

@[deprecated uniqueAlgEquiv_monomial (since := "2026-04-15")]
/-
**MvPolynomial.pUnitAlgEquiv_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：pUnitAlgEquiv_monomial {d : PUnit ->₀ Nat} {r : R} : MvPolynomial.pUnitAlg
Equiv R (MvPolynomial.monomial d r) = Polynomial.monomial (d ()) r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.uniqueAlgEquiv_monomial`：uniqueAlgEquiv_monomial [Unique σ]
 {d : σ ->₀ Nat} {r : R} : (MvPolynomial.uniqueAlgEquiv R σ) (MvPolynomial.monom
ial d r) = Polynomial.mono…
-/
theorem pUnitAlgEquiv_monomial {d : PUnit →₀ ℕ} {r : R} :
    MvPolynomial.pUnitAlgEquiv R (MvPolynomial.monomial d r)
      = Polynomial.monomial (d ()) r :=
  uniqueAlgEquiv_monomial _

@[deprecated uniqueAlgEquiv_symm_monomial (since := "2026-04-15")]
/-
**MvPolynomial.pUnitAlgEquiv_symm_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：pUnitAlgEquiv_symm_monomial {d : PUnit ->₀ Nat} {r : R} : (MvPolynomial.pU
nitAlgEquiv R).symm (Polynomial.monomial (d ()) r) = MvPolynomial.monomial d r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.uniqueAlgEquiv_symm_monomial`：uniqueAlgEquiv_symm_monomial 
[Unique σ] {d : σ ->₀ Nat} {r : R} : (MvPolynomial.uniqueAlgEquiv R σ).symm (Pol
ynomial.monomial (d default) r)…
-/
theorem pUnitAlgEquiv_symm_monomial {d : PUnit →₀ ℕ} {r : R} :
    (MvPolynomial.pUnitAlgEquiv R).symm (Polynomial.monomial (d ()) r)
      = MvPolynomial.monomial d r :=
  uniqueAlgEquiv_symm_monomial _

section Map

variable {R} (σ)

/-- If `e : A ≃+* B` is an isomorphism of rings, then so is `map e`. -/
/-
**MvPolynomial.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：mapEquiv [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂) : MvPolynomia
l σ S₁ ≃+* MvPolynomial σ S₂
参数：e : S₁ ≃+* S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e : A ≃+* B` is an isomorphism of rings, then so is `map e`.
-/
def mapEquiv [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂) :
    MvPolynomial σ S₁ ≃+* MvPolynomial σ S₂ :=
  AddMonoidAlgebra.mapRingEquiv _ e

@[simp]
/-
**MvPolynomial.mapEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：mapEquiv_apply [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂) (x : Mv
Polynomial σ S₁) : mapEquiv σ e x = map e x
参数：e : S₁ ≃+* S₂；x : MvPolynomial σ S₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapEquiv_apply [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂)
    (x : MvPolynomial σ S₁) :
    mapEquiv σ e x = map e x := rfl

@[simp]
/-
**MvPolynomial.mapEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mapEquiv_refl : mapEquiv σ (RingEquiv.refl R) = RingEquiv.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `MvPolynomial.map_id`：map_id : forall p : MvPolynomial σ R, map (RingHom.
id R) p = p
-/
theorem mapEquiv_refl : mapEquiv σ (RingEquiv.refl R) = RingEquiv.refl _ :=
  RingEquiv.ext map_id

@[simp]
/-
**MvPolynomial.mapEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mapEquiv_symm [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂) : (mapEq
uiv σ e).symm = mapEquiv σ e.symm
参数：e : S₁ ≃+* S₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapEquiv_symm [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂) :
    (mapEquiv σ e).symm = mapEquiv σ e.symm :=
  rfl

@[simp]
/-
**MvPolynomial.mapEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mapEquiv_trans [CommSemiring S₁] [CommSemiring S₂] [CommSemiring S₃] (e : 
S₁ ≃+* S₂) (f : S₂ ≃+* S₃) : (mapEquiv σ e).trans (mapEquiv σ f) = mapEquiv σ (e
.trans f)
参数：e : S₁ ≃+* S₂；f : S₂ ≃+* S₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidAlgebra.mapRingEquiv_trans`：∀ {R : Type u_3} {S : Type u_4} {T 
: Type u_5} {M : Type u_6} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 :
 Semiring T] [inst_3 : Ad…
-/
theorem mapEquiv_trans [CommSemiring S₁] [CommSemiring S₂] [CommSemiring S₃] (e : S₁ ≃+* S₂)
    (f : S₂ ≃+* S₃) : (mapEquiv σ e).trans (mapEquiv σ f) = mapEquiv σ (e.trans f) :=
  (AddMonoidAlgebra.mapRingEquiv_trans _ _).symm

variable {A₁ A₂ A₃ : Type*} [CommSemiring A₁] [CommSemiring A₂] [CommSemiring A₃]
variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

/-- If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebras, then so is `map e`. -/
/-
**MvPolynomial.mapAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：mapAlgEquiv (e : A₁ ≃ₐ[R] A₂) : MvPolynomial σ A₁ ≃ₐ[R] MvPolynomial σ A₂
参数：e : A₁ ≃ₐ[R] A₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebras, then so is `map e`.
-/
def mapAlgEquiv (e : A₁ ≃ₐ[R] A₂) : MvPolynomial σ A₁ ≃ₐ[R] MvPolynomial σ A₂ :=
  AddMonoidAlgebra.mapAlgEquiv _ _ e

@[simp]
/-
**MvPolynomial.mapAlgEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：mapAlgEquiv_apply (e : A₁ ≃ₐ[R] A₂) (x : MvPolynomial σ A₁) : mapAlgEquiv 
σ e x = map e x
参数：e : A₁ ≃ₐ[R] A₂；x : MvPolynomial σ A₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapAlgEquiv_apply (e : A₁ ≃ₐ[R] A₂) (x : MvPolynomial σ A₁) :
    mapAlgEquiv σ e x = map e x :=
  rfl

@[simp]
/-
**MvPolynomial.mapAlgEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mapAlgEquiv_refl : mapAlgEquiv σ (AlgEquiv.refl : A₁ ≃ₐ[R] A₁) = AlgEquiv.
refl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `MvPolynomial.map_id`：map_id : forall p : MvPolynomial σ R, map (RingHom.
id R) p = p
-/
theorem mapAlgEquiv_refl : mapAlgEquiv σ (AlgEquiv.refl : A₁ ≃ₐ[R] A₁) = AlgEquiv.refl :=
  AlgEquiv.ext map_id

@[simp]
/-
**MvPolynomial.mapAlgEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mapAlgEquiv_symm (e : A₁ ≃ₐ[R] A₂) : (mapAlgEquiv σ e).symm = mapAlgEquiv 
σ e.symm
参数：e : A₁ ≃ₐ[R] A₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAlgEquiv_symm (e : A₁ ≃ₐ[R] A₂) : (mapAlgEquiv σ e).symm = mapAlgEquiv σ e.symm :=
  rfl

@[simp]
/-
**MvPolynomial.mapAlgEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mapAlgEquiv_trans (e : A₁ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₃) : (mapAlgEquiv σ e).
trans (mapAlgEquiv σ f) = mapAlgEquiv σ (e.trans f)
参数：e : A₁ ≃ₐ[R] A₂；f : A₂ ≃ₐ[R] A₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidAlgebra.mapAlgEquiv_trans`：∀ {R : Type u_1} {A : Type u_4} {B :
 Type u_5} {C : Type u_6} {M : Type u_7} [inst : CommSemiring R]   [inst_1 : Sem
iring A] [inst_2 : Semir…
-/
theorem mapAlgEquiv_trans (e : A₁ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₃) :
    (mapAlgEquiv σ e).trans (mapAlgEquiv σ f) = mapAlgEquiv σ (e.trans f) :=
  (AddMonoidAlgebra.mapAlgEquiv_trans _ _).symm

end Map

section Eval

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_uniqueAlgEquiv [Unique σ] {f : MvPolynomial σ R} {φ : R →+* S}
    {a : σ → S} :
    ((MvPolynomial.uniqueAlgEquiv R σ) f : Polynomial R).eval₂ φ (a default) =
      f.eval₂ φ a := by
  simp only [MvPolynomial.uniqueAlgEquiv_apply]
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [← MvPolynomial.uniqueAlgEquiv_apply (R := R) (σ := σ), uniqueAlgEquiv_monomial]
    simp only [Polynomial.eval₂_monomial, eval₂_monomial]
    rw [Finsupp.unique_single d, Finsupp.prod_single_index]
    · simp
    · simp only [pow_zero]
  | add f g hf hg => simp only [eval₂_add, Polynomial.eval₂_add, hf, hg]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_uniqueAlgEquiv_symm [Unique σ] {f : Polynomial R} {φ : R →+* S}
    {a : σ → S} :
    ((MvPolynomial.uniqueAlgEquiv R σ).symm f : MvPolynomial σ R).eval₂ φ a =
      f.eval₂ φ (a default) := by
  rw [(eval₂_uniqueAlgEquiv (R := R) (σ := σ) (f := (MvPolynomial.uniqueAlgEquiv R σ).symm f)
    (φ := φ) (a := a)).symm]
  rw [AlgEquiv.apply_symm_apply]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_const_uniqueAlgEquiv_symm [Unique σ] {f : Polynomial R}
    {φ : R →+* S} {a : S} :
    ((MvPolynomial.uniqueAlgEquiv R σ).symm f : MvPolynomial σ R).eval₂ φ (fun _ ↦ a) =
      f.eval₂ φ a := by
  rw [eval₂_uniqueAlgEquiv_symm]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_const_uniqueAlgEquiv [Unique σ] {f : MvPolynomial σ R}
    {φ : R →+* S} {a : S} :
    ((MvPolynomial.uniqueAlgEquiv R σ) f : Polynomial R).eval₂ φ a =
      f.eval₂ φ (fun _ ↦ a) := by
  rw [← eval₂_uniqueAlgEquiv]

@[deprecated eval₂_uniqueAlgEquiv_symm (since := "2026-04-15")]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_pUnitAlgEquiv_symm {f : Polynomial R} {φ : R →+* S} {a : Unit → S} :
    ((MvPolynomial.pUnitAlgEquiv R).symm f : MvPolynomial Unit R).eval₂ φ a =
      f.eval₂ φ (a ()) :=
  eval₂_uniqueAlgEquiv_symm

@[deprecated eval₂_const_uniqueAlgEquiv_symm (since := "2026-04-15")]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_const_pUnitAlgEquiv_symm {f : Polynomial R} {φ : R →+* S} {a : S} :
    ((MvPolynomial.pUnitAlgEquiv R).symm f : MvPolynomial Unit R).eval₂ φ (fun _ ↦ a) =
      f.eval₂ φ a :=
  eval₂_const_uniqueAlgEquiv_symm

@[deprecated eval₂_uniqueAlgEquiv (since := "2026-04-15")]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_pUnitAlgEquiv {f : MvPolynomial PUnit R} {φ : R →+* S} {a : PUnit → S} :
    ((MvPolynomial.pUnitAlgEquiv R) f : Polynomial R).eval₂ φ (a default) = f.eval₂ φ a :=
  eval₂_uniqueAlgEquiv

@[deprecated eval₂_const_uniqueAlgEquiv (since := "2026-04-15")]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_const_pUnitAlgEquiv {f : MvPolynomial PUnit R} {φ : R →+* S} {a : S} :
    ((MvPolynomial.pUnitAlgEquiv R) f : Polynomial R).eval₂ φ a = f.eval₂ φ (fun _ ↦ a) :=
  eval₂_const_uniqueAlgEquiv

end Eval

section

variable (S₁ S₂ S₃)

section isEmptyRingEquiv
variable [IsEmpty σ]

variable (σ) in
/-- The algebra isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps! apply]
/-
**MvPolynomial.isEmptyAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：isEmptyAlgEquiv : MvPolynomial σ R ≃ₐ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra isomorphism between multivariable polynomials in no variables
and the ground ring.
-/
def isEmptyAlgEquiv : MvPolynomial σ R ≃ₐ[R] R := AddMonoidAlgebra.uniqueAlgEquiv ..

variable {R S₁} in
@[simp]
/-
**MvPolynomial.aeval_injective_iff_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `MvPolyn
omial`。
形式化陈述：aeval_injective_iff_of_isEmpty [CommSemiring S₁] [Algebra R S₁] {f : σ -> 
S₁} : Function.Injective (aeval f : MvPolynomial σ R ->ₐ[R] S₁) ↔ Function.Injec
tive (algebraMap R S₁)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Injective (f
 ∘ g) ↔ Function.Inje…
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma aeval_injective_iff_of_isEmpty [CommSemiring S₁] [Algebra R S₁] {f : σ → S₁} :
    Function.Injective (aeval f : MvPolynomial σ R →ₐ[R] S₁) ↔
      Function.Injective (algebraMap R S₁) := by
  have : aeval f = (Algebra.ofId R S₁).comp (@isEmptyAlgEquiv R σ _ _).toAlgHom := by
    ext i
    exact IsEmpty.elim' ‹IsEmpty σ› i
  rw [this, ← Injective.of_comp_iff' _ (@isEmptyAlgEquiv R σ _ _).bijective]
  rfl

variable (σ) in
/-- The ring isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps! apply]
/-
**MvPolynomial.isEmptyRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：isEmptyRingEquiv : MvPolynomial σ R ≃+* R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring isomorphism between multivariable polynomials in no variables
and the ground ring.
-/
def isEmptyRingEquiv : MvPolynomial σ R ≃+* R := AddMonoidAlgebra.uniqueRingEquiv _

variable (σ) in
/-
**MvPolynomial.isEmptyRingEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：∀ (R : Type u) (σ : Type u_1) [inst : CommSemiring R] [inst_1 : IsEmpty σ]
 (r : R),   (MvPolynomial.isEmptyRingEquiv R σ).symm r = MvPolynomial.C r
参数：R : Type u；σ : Type u_1；r : R；MvPolynomial.isEmptyRingEquiv R σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.uniqueRingEquiv_symm_apply`：∀ {R : Type u_1} (M : Type 
u_4) [inst : Semiring R] [inst_1 : AddMonoid M] [inst_2 : Subsingleton M] (r : R
),   (AddMonoidAlgebra.uniqueRing…
-/
@[simp] lemma isEmptyRingEquiv_symm_apply (r : R) : (isEmptyRingEquiv R σ).symm r = C r :=
  AddMonoidAlgebra.uniqueRingEquiv_symm_apply ..
/-
**MvPolynomial.isEmptyRingEquiv_symm_toRingHom** 是 Mathlib 中的一个引理，位于命名空间 `MvPoly
nomial`。
形式化陈述：isEmptyRingEquiv_symm_toRingHom : (isEmptyRingEquiv R σ).symm.toRingHom = 
C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.isEmptyRingEquiv_symm_apply`：∀ (R : Type u) (σ : Type u_1) 
[inst : CommSemiring R] [inst_1 : IsEmpty σ] (r : R),   (MvPolynomial.isEmptyRin
gEquiv R σ).symm r = MvPolynom…
· 使用定理 `MvPolynomial.coeff_C`：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : M
vPolynomial σ R) = if 0 = m then a else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isEmptyRingEquiv_symm_toRingHom : (isEmptyRingEquiv R σ).symm.toRingHom = C := by ext; simp
/-
**MvPolynomial.isEmptyRingEquiv_eq_coeff_zero** 是 Mathlib 中的一个引理，位于命名空间 `MvPolyn
omial`。
形式化陈述：isEmptyRingEquiv_eq_coeff_zero {x : MvPolynomial σ R} : isEmptyRingEquiv R
 σ x = x.coeff 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isEmptyRingEquiv_eq_coeff_zero {x : MvPolynomial σ R} : isEmptyRingEquiv R σ x = x.coeff 0 :=
  rfl
/-
**MvPolynomial.isEmptyAlgEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
形式化陈述：∀ (R : Type u) {σ : Type u_1} [inst : CommSemiring R] [inst_1 : IsEmpty σ]
 (r : R),   (MvPolynomial.isEmptyAlgEquiv R σ).symm r = MvPolynomial.C r
参数：R : Type u；r : R；MvPolynomial.isEmptyAlgEquiv R σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.isEmptyRingEquiv_symm_apply`：∀ (R : Type u) (σ : Type u_1) 
[inst : CommSemiring R] [inst_1 : IsEmpty σ] (r : R),   (MvPolynomial.isEmptyRin
gEquiv R σ).symm r = MvPolynom…
-/
@[simp] lemma isEmptyAlgEquiv_symm_apply (r : R) : (isEmptyAlgEquiv R σ).symm r = C r :=
  isEmptyRingEquiv_symm_apply ..
/-
**MvPolynomial.isEmptyAlgEquiv_symm_toRingHom** 是 Mathlib 中的一个引理，位于命名空间 `MvPolyn
omial`。
形式化陈述：isEmptyAlgEquiv_symm_toRingHom : (isEmptyAlgEquiv R σ).symm.toRingHom = C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPolynomial.isEmptyRingEquiv_symm_toRingHom`：isEmptyRingEquiv_symm_toRi
ngHom : (isEmptyRingEquiv R σ).symm.toRingHom = C
-/
lemma isEmptyAlgEquiv_symm_toRingHom : (isEmptyAlgEquiv R σ).symm.toRingHom = C :=
  isEmptyRingEquiv_symm_toRingHom _

end isEmptyRingEquiv

/-- A helper function for `sumRingEquiv`. -/
@[simps]
/-
**MvPolynomial.mvPolynomialEquivMvPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `MvPolyno
mial`。
形式化陈述：mvPolynomialEquivMvPolynomial [CommSemiring S₃] (f : MvPolynomial S₁ R ->+
* MvPolynomial S₂ S₃) (g : MvPolynomial S₂ S₃ ->+* MvPolynomial S₁ R) (hfgC : (f
.comp g).comp C = C) (hfgX : forall n, f (g (X n)) = X n) (hgfC : (g.comp f).com
p C = C) (hgfX : forall n, g (f (X n)) = X n) : MvPolynomial S₁ R ≃+* MvPolynomi
al S₂ S₃ where toFun
参数：f : MvPolynomial S₁ R ->+* MvPolynomial S₂ S₃；g : MvPolynomial S₂ S₃ ->+* MvP
olynomial S₁ R；hfgC : (f.comp g).comp C = C；hfgX : forall n, f (g (X n)) = X n；h
gfC : (g.comp f).comp C = C；hgfX : forall n, g (f (X n)) = X n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper function for `sumRingEquiv`.
-/
def mvPolynomialEquivMvPolynomial [CommSemiring S₃] (f : MvPolynomial S₁ R →+* MvPolynomial S₂ S₃)
    (g : MvPolynomial S₂ S₃ →+* MvPolynomial S₁ R) (hfgC : (f.comp g).comp C = C)
    (hfgX : ∀ n, f (g (X n)) = X n) (hgfC : (g.comp f).comp C = C) (hgfX : ∀ n, g (f (X n)) = X n) :
    MvPolynomial S₁ R ≃+* MvPolynomial S₂ S₃ where
  toFun := f
  invFun := g
  left_inv := is_id (RingHom.comp _ _) hgfC hgfX
  right_inv := is_id (RingHom.comp _ _) hfgC hfgX
  map_mul' := f.map_mul
  map_add' := f.map_add

/-- The ring isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.
-/
/-
**MvPolynomial.sumRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：sumRingEquiv : MvPolynomial (S₁ oplus S₂) R ≃+* MvPolynomial S₁ (MvPolynom
ial S₂ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.
-/
def sumRingEquiv : MvPolynomial (S₁ ⊕ S₂) R ≃+* MvPolynomial S₁ (MvPolynomial S₂ R) :=
  (mapDomainRingEquiv _ sumFinsuppAddEquivProdFinsupp).trans curryRingEquiv

@[simp]
/-
**MvPolynomial.sumRingEquiv_C** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：sumRingEquiv_C (r : R) : sumRingEquiv R S₁ S₂ (C r) = C (C r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.mapDomainRingEquiv_single`：∀ {R : Type u_3} {M : Type u
_6} {N : Type u_7} [inst : Semiring R] [inst_1 : AddMonoid M] [inst_2 : AddMonoi
d N]   (e : M ≃+ N) (r : R) (m :…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_apply`：∀ {M : Type u_5} [inst : Ad
dMonoid M] {α : Type u_12} {β : Type u_13} (f : α ⊕ β →₀ M),   Finsupp.sumFinsup
pAddEquivProdFinsupp f = (Finsupp…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.comapDomain_zero`：comapDomain_zero (f : α -> β) (hif : Set.InjOn
 f (f ⁻¹' ↑(0 : β ->₀ M).support)
· 使用定理 `AddMonoidAlgebra.curryRingEquiv_single`：∀ {R : Type u_1} {M : Type u_4} 
{N : Type u_5} [inst : Semiring R] [inst_1 : AddMonoid M] [inst_2 : AddMonoid N]
 (m : M)   (n : N) (r : R), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumRingEquiv_C (r : R) : sumRingEquiv R S₁ S₂ (C r) = C (C r) := by
  unfold sumRingEquiv C MvPolynomial; simp [monomial]

@[simp]
/-
**MvPolynomial.sumRingEquiv_X_inl** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：sumRingEquiv_X_inl (s : S₁) : sumRingEquiv R S₁ S₂ (X <| .inl s) = X s
参数：s : S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.mapDomainRingEquiv_single`：∀ {R : Type u_3} {M : Type u
_6} {N : Type u_7} [inst : Semiring R] [inst_1 : AddMonoid M] [inst_2 : AddMonoi
d N]   (e : M ≃+ N) (r : R) (m :…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_apply`：∀ {M : Type u_5} [inst : Ad
dMonoid M] {α : Type u_12} {β : Type u_13} (f : α ⊕ β →₀ M),   Finsupp.sumFinsup
pAddEquivProdFinsupp f = (Finsupp…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.comapDomain_single`：comapDomain_single (f : α -> β) (a : α) (m :
 M) (hif : Set.InjOn f (f ⁻¹' (single (f a) m).support)) : comapDomain f (Finsup
p.single (f a) m…
· 使用引理 `Finsupp.comapDomain_single_of_not_mem_range`：comapDomain_single_of_not_m
em_range [Zero M] {f : α -> β} {b : β} (hb : b ∉ Set.range f) (m : M) (hf) : com
apDomain f (single b m) hf = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AddMonoidAlgebra.curryRingEquiv_single`：∀ {R : Type u_1} {M : Type u_4} 
{N : Type u_5} [inst : Semiring R] [inst_1 : AddMonoid M] [inst_2 : AddMonoid N]
 (m : M)   (n : N) (r : R), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumRingEquiv_X_inl (s : S₁) : sumRingEquiv R S₁ S₂ (X <| .inl s) = X s := by
  unfold sumRingEquiv X MvPolynomial; simp [monomial, AddMonoidAlgebra.one_def]

@[simp]
/-
**MvPolynomial.sumRingEquiv_X_inr** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：sumRingEquiv_X_inr (s : S₂) : sumRingEquiv R S₁ S₂ (X <| .inr s) = C (X s)
参数：s : S₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.mapDomainRingEquiv_single`：∀ {R : Type u_3} {M : Type u
_6} {N : Type u_7} [inst : Semiring R] [inst_1 : AddMonoid M] [inst_2 : AddMonoi
d N]   (e : M ≃+ N) (r : R) (m :…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_apply`：∀ {M : Type u_5} [inst : Ad
dMonoid M] {α : Type u_12} {β : Type u_13} (f : α ⊕ β →₀ M),   Finsupp.sumFinsup
pAddEquivProdFinsupp f = (Finsupp…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finsupp.comapDomain_single_of_not_mem_range`：comapDomain_single_of_not_m
em_range [Zero M] {f : α -> β} {b : β} (hb : b ∉ Set.range f) (m : M) (hf) : com
apDomain f (single b m) hf = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.comapDomain_single`：comapDomain_single (f : α -> β) (a : α) (m :
 M) (hif : Set.InjOn f (f ⁻¹' (single (f a) m).support)) : comapDomain f (Finsup
p.single (f a) m…
· 使用定理 `AddMonoidAlgebra.curryRingEquiv_single`：∀ {R : Type u_1} {M : Type u_4} 
{N : Type u_5} [inst : Semiring R] [inst_1 : AddMonoid M] [inst_2 : AddMonoid N]
 (m : M)   (n : N) (r : R), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumRingEquiv_X_inr (s : S₂) : sumRingEquiv R S₁ S₂ (X <| .inr s) = C (X s) := by
  unfold sumRingEquiv C X MvPolynomial; simp [monomial]

@[simp]
/-
**MvPolynomial.sumRingEquiv_symm_C_C** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：sumRingEquiv_symm_C_C (r : R) : (sumRingEquiv R S₁ S₂).symm (C <| C r) = C
 r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumRingEquiv_symm_C_C (r : R) : (sumRingEquiv R S₁ S₂).symm (C <| C r) = C r := by
  simp [← sumRingEquiv_C]

@[simp]
/-
**MvPolynomial.sumRingEquiv_symm_X** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：sumRingEquiv_symm_X (s : S₁) : (sumRingEquiv R S₁ S₂).symm (X s) = X (.inl
 s)
参数：s : S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumRingEquiv_symm_X (s : S₁) : (sumRingEquiv R S₁ S₂).symm (X s) = X (.inl s) := by
  simp [← sumRingEquiv_X_inl]

@[simp]
/-
**MvPolynomial.sumRingEquiv_symm_C_X** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：sumRingEquiv_symm_C_X (s : S₂) : (sumRingEquiv R S₁ S₂).symm (C <| X s) = 
X (.inr s)
参数：s : S₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumRingEquiv_symm_C_X (s : S₂) : (sumRingEquiv R S₁ S₂).symm (C <| X s) = X (.inr s) := by
  simp [← sumRingEquiv_X_inr]

/-- The function from multivariable polynomials in a sum of two types,
to multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.

See `sumRingEquiv` for the ring isomorphism.
-/
@[deprecated sumRingEquiv (since := "2026-06-18")]
/-
**MvPolynomial.sumToIter** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：sumToIter : MvPolynomial (S₁ oplus S₂) R ->+* MvPolynomial S₁ (MvPolynomia
l S₂ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function from multivariable polynomials in a sum of two types,
to multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.

See `sumRingEquiv` for the ring isomorphism.
-/
def sumToIter : MvPolynomial (S₁ ⊕ S₂) R →+* MvPolynomial S₁ (MvPolynomial S₂ R) :=
  eval₂Hom (C.comp C) fun bc => Sum.recOn bc X (C ∘ X)

@[deprecated sumRingEquiv_C (since := "2026-06-18")]
/-
**MvPolynomial.sumToIter_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：sumToIter_C (a : R) : sumToIter R S₁ S₂ (C a) = C (C a)
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_C`：eval₂_C (a) : (C a).eval₂ f g = f a
-/
theorem sumToIter_C (a : R) : sumToIter R S₁ S₂ (C a) = C (C a) :=
  eval₂_C _ _ a

@[deprecated sumRingEquiv_X_inl (since := "2026-06-18")]
/-
**MvPolynomial.sumToIter_Xl** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：sumToIter_Xl (b : S₁) : sumToIter R S₁ S₂ (X (Sum.inl b)) = X b
参数：b : S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_X`：eval₂_X (n) : (X n).eval₂ f g = g n
-/
theorem sumToIter_Xl (b : S₁) : sumToIter R S₁ S₂ (X (Sum.inl b)) = X b :=
  eval₂_X _ _ (Sum.inl b)

@[deprecated sumRingEquiv_X_inr (since := "2026-06-18")]
/-
**MvPolynomial.sumToIter_Xr** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：sumToIter_Xr (c : S₂) : sumToIter R S₁ S₂ (X (Sum.inr c)) = C (X c)
参数：c : S₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_X`：eval₂_X (n) : (X n).eval₂ f g = g n
-/
theorem sumToIter_Xr (c : S₂) : sumToIter R S₁ S₂ (X (Sum.inr c)) = C (X c) :=
  eval₂_X _ _ (Sum.inr c)

/-- The function from multivariable polynomials in one type,
with coefficients in multivariable polynomials in another type,
to multivariable polynomials in the sum of the two types.

See `sumRingEquiv` for the ring isomorphism.
-/
@[deprecated sumRingEquiv (since := "2026-06-18")]
/-
**MvPolynomial.iterToSum** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：iterToSum : MvPolynomial S₁ (MvPolynomial S₂ R) ->+* MvPolynomial (S₁ oplu
s S₂) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function from multivariable polynomials in one type,
with coefficients in multivariable polynomials in another type,
to multivariable polynomials in the sum of the two types.

See `sumRingEquiv` for the ring isomorphism.
-/
def iterToSum : MvPolynomial S₁ (MvPolynomial S₂ R) →+* MvPolynomial (S₁ ⊕ S₂) R :=
  eval₂Hom (eval₂Hom C (X ∘ Sum.inr)) (X ∘ Sum.inl)

@[deprecated sumRingEquiv_symm_C_C (since := "2026-06-18")]
/-
**MvPolynomial.iterToSum_C_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：iterToSum_C_C (a : R) : iterToSum R S₁ S₂ (C (C a)) = C a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.eval₂_C`：eval₂_C (a) : (C a).eval₂ f g = f a
-/
theorem iterToSum_C_C (a : R) : iterToSum R S₁ S₂ (C (C a)) = C a :=
  Eq.trans (eval₂_C _ _ (C a)) (eval₂_C _ _ _)

@[deprecated sumRingEquiv_symm_X (since := "2026-06-18")]
/-
**MvPolynomial.iterToSum_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：iterToSum_X (b : S₁) : iterToSum R S₁ S₂ (X b) = X (Sum.inl b)
参数：b : S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_X`：eval₂_X (n) : (X n).eval₂ f g = g n
-/
theorem iterToSum_X (b : S₁) : iterToSum R S₁ S₂ (X b) = X (Sum.inl b) :=
  eval₂_X _ _ _

@[deprecated sumRingEquiv_symm_C_X (since := "2026-06-18")]
/-
**MvPolynomial.iterToSum_C_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：iterToSum_C_X (c : S₂) : iterToSum R S₁ S₂ (C (X c)) = X (Sum.inr c)
参数：c : S₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.eval₂_C`：eval₂_C (a) : (C a).eval₂ f g = f a
· 使用定理 `MvPolynomial.eval₂_X`：eval₂_X (n) : (X n).eval₂ f g = g n
-/
theorem iterToSum_C_X (c : S₂) : iterToSum R S₁ S₂ (C (X c)) = X (Sum.inr c) :=
  Eq.trans (eval₂_C _ _ (X c)) (eval₂_X _ _ _)

@[deprecated (since := "2026-06-18")] alias iterToSum_sumToIter := RingEquiv.symm_apply_apply
@[deprecated (since := "2026-06-18")] alias sumToIter_iterToSum := RingEquiv.apply_symm_apply

set_option backward.isDefEq.respectTransparency false in
/-- The algebra isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.
-/
@[simps!]
/-
**MvPolynomial.sumAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：sumAlgEquiv : MvPolynomial (S₁ oplus S₂) R ≃ₐ[R] MvPolynomial S₁ (MvPolyno
mial S₂ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.
-/
def sumAlgEquiv : MvPolynomial (S₁ ⊕ S₂) R ≃ₐ[R] MvPolynomial S₁ (MvPolynomial S₂ R) :=
  (domCongr _ _ sumFinsuppAddEquivProdFinsupp).trans (curryAlgEquiv _)

@[simp]
/-
**MvPolynomial.sumAlgEquiv_C_inl** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：sumAlgEquiv_C_inl (r : R) : sumAlgEquiv R S₁ S₂ (C r) = C (C r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.domCongr_single`：∀ {R : Type u_1} {A : Type u_4} {M : T
ype u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Algebra R A] [inst_3…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_apply`：∀ {M : Type u_5} [inst : Ad
dMonoid M] {α : Type u_12} {β : Type u_13} (f : α ⊕ β →₀ M),   Finsupp.sumFinsup
pAddEquivProdFinsupp f = (Finsupp…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.comapDomain_zero`：comapDomain_zero (f : α -> β) (hif : Set.InjOn
 f (f ⁻¹' ↑(0 : β ->₀ M).support)
· 使用定理 `AddMonoidAlgebra.curryAlgEquiv_single`：∀ {R : Type u_1} {A : Type u_4} {
M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [in
st_2 : Algebra R A] [inst_3…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumAlgEquiv_C_inl (r : R) : sumAlgEquiv R S₁ S₂ (C r) = C (C r) := by
  ext; simp [sumAlgEquiv, C, monomial, coeff]

@[simp]
/-
**MvPolynomial.sumAlgEquiv_symm_C_C** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：sumAlgEquiv_symm_C_C (r : R) : (sumAlgEquiv R S₁ S₂).symm (C <| C r) = C r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.curryAlgEquiv_symm_single`：∀ {R : Type u_1} {A : Type u
_4} {M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A] 
  [inst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.domCongr_single`：∀ {R : Type u_1} {A : Type u_4} {M : T
ype u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Algebra R A] [inst_3…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_symm_apply`：∀ {M : Type u_5} [inst
 : AddMonoid M] {α : Type u_12} {β : Type u_13} (fg : (α →₀ M) × (β →₀ M)),   Fi
nsupp.sumFinsuppAddEquivProdFinsupp.sy…
· 使用定理 `Finsupp.sumElim_zero_zero`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3
} [inst : Zero γ], Finsupp.sumElim 0 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumAlgEquiv_symm_C_C (r : R) : (sumAlgEquiv R S₁ S₂).symm (C <| C r) = C r := by
  ext; simp [sumAlgEquiv, C, monomial, coeff]

@[simp]
/-
**MvPolynomial.sumAlgEquiv_X_inl** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：sumAlgEquiv_X_inl (c : S₁) : sumAlgEquiv R S₁ S₂ (X <| .inl c) = X c
参数：c : S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.domCongr_single`：∀ {R : Type u_1} {A : Type u_4} {M : T
ype u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Algebra R A] [inst_3…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_apply`：∀ {M : Type u_5} [inst : Ad
dMonoid M] {α : Type u_12} {β : Type u_13} (f : α ⊕ β →₀ M),   Finsupp.sumFinsup
pAddEquivProdFinsupp f = (Finsupp…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.comapDomain_single`：comapDomain_single (f : α -> β) (a : α) (m :
 M) (hif : Set.InjOn f (f ⁻¹' (single (f a) m).support)) : comapDomain f (Finsup
p.single (f a) m…
· 使用引理 `Finsupp.comapDomain_single_of_not_mem_range`：comapDomain_single_of_not_m
em_range [Zero M] {f : α -> β} {b : β} (hb : b ∉ Set.range f) (m : M) (hf) : com
apDomain f (single b m) hf = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AddMonoidAlgebra.curryAlgEquiv_single`：∀ {R : Type u_1} {A : Type u_4} {
M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [in
st_2 : Algebra R A] [inst_3…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumAlgEquiv_X_inl (c : S₁) : sumAlgEquiv R S₁ S₂ (X <| .inl c) = X c := by
  ext; simp [sumAlgEquiv, X, monomial, coeff, AddMonoidAlgebra.one_def]

@[simp]
/-
**MvPolynomial.sumAlgEquiv_symm_X** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：sumAlgEquiv_symm_X (c : S₁) : (sumAlgEquiv R S₁ S₂).symm (X c) = (X <| .in
l c)
参数：c : S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.curryAlgEquiv_symm_single`：∀ {R : Type u_1} {A : Type u
_4} {M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A] 
  [inst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.domCongr_single`：∀ {R : Type u_1} {A : Type u_4} {M : T
ype u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Algebra R A] [inst_3…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_symm_apply`：∀ {M : Type u_5} [inst
 : AddMonoid M] {α : Type u_12} {β : Type u_13} (fg : (α →₀ M) × (β →₀ M)),   Fi
nsupp.sumFinsuppAddEquivProdFinsupp.sy…
· 使用定理 `Finsupp.sumElim_single_zero`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} [inst : Zero γ] (a : α) (c : γ),   (fun₀ | a => c).sumElim 0 = fun₀ | Sum.in
l a => c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumAlgEquiv_symm_X (c : S₁) : (sumAlgEquiv R S₁ S₂).symm (X c) = (X <| .inl c) := by
  ext; simp [sumAlgEquiv, X, monomial, coeff, AddMonoidAlgebra.one_def]

@[simp]
/-
**MvPolynomial.sumAlgEquiv_X_inr** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：sumAlgEquiv_X_inr (c : S₂) : sumAlgEquiv R S₁ S₂ (X <| .inr c) = C (X c)
参数：c : S₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.domCongr_single`：∀ {R : Type u_1} {A : Type u_4} {M : T
ype u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Algebra R A] [inst_3…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_apply`：∀ {M : Type u_5} [inst : Ad
dMonoid M] {α : Type u_12} {β : Type u_13} (f : α ⊕ β →₀ M),   Finsupp.sumFinsup
pAddEquivProdFinsupp f = (Finsupp…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finsupp.comapDomain_single_of_not_mem_range`：comapDomain_single_of_not_m
em_range [Zero M] {f : α -> β} {b : β} (hb : b ∉ Set.range f) (m : M) (hf) : com
apDomain f (single b m) hf = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.comapDomain_single`：comapDomain_single (f : α -> β) (a : α) (m :
 M) (hif : Set.InjOn f (f ⁻¹' (single (f a) m).support)) : comapDomain f (Finsup
p.single (f a) m…
· 使用定理 `AddMonoidAlgebra.curryAlgEquiv_single`：∀ {R : Type u_1} {A : Type u_4} {
M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [in
st_2 : Algebra R A] [inst_3…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumAlgEquiv_X_inr (c : S₂) : sumAlgEquiv R S₁ S₂ (X <| .inr c) = C (X c) := by
  ext; simp [sumAlgEquiv, C, X, monomial, coeff]

@[simp]
/-
**MvPolynomial.sumAlgEquiv_symm_C_X** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：sumAlgEquiv_symm_C_X (c : S₂) : (sumAlgEquiv R S₁ S₂).symm (C <| X c) = X 
(.inr c)
参数：c : S₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.curryAlgEquiv_symm_single`：∀ {R : Type u_1} {A : Type u
_4} {M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A] 
  [inst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.domCongr_single`：∀ {R : Type u_1} {A : Type u_4} {M : T
ype u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Algebra R A] [inst_3…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_symm_apply`：∀ {M : Type u_5} [inst
 : AddMonoid M] {α : Type u_12} {β : Type u_13} (fg : (α →₀ M) × (β →₀ M)),   Fi
nsupp.sumFinsuppAddEquivProdFinsupp.sy…
· 使用定理 `Finsupp.sumElim_zero_single`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} [inst : Zero γ] (b : β) (c : γ),   (Finsupp.sumElim 0 fun₀ | b => c) = fun₀ 
| Sum.inr b => c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumAlgEquiv_symm_C_X (c : S₂) : (sumAlgEquiv R S₁ S₂).symm (C <| X c) = X (.inr c) := by
  ext; simp [sumAlgEquiv, C, X, monomial, coeff]
/-
**MvPolynomial.sumAlgEquiv_comp_rename_inr** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomi
al`。
形式化陈述：sumAlgEquiv_comp_rename_inr : (sumAlgEquiv R S₁ S₂).toAlgHom.comp (rename 
Sum.inr) = IsScalarTower.toAlgHom R (MvPolynomial S₂ R) (MvPolynomial S₁ (MvPoly
nomial S₂ R))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用引理 `MvPolynomial.sumAlgEquiv_X_inr`：sumAlgEquiv_X_inr (c : S₂) : sumAlgEquiv
 R S₁ S₂ (X <| .inr c) = C (X c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumAlgEquiv_comp_rename_inr :
    (sumAlgEquiv R S₁ S₂).toAlgHom.comp (rename Sum.inr) = IsScalarTower.toAlgHom R
        (MvPolynomial S₂ R) (MvPolynomial S₁ (MvPolynomial S₂ R)) := by
  ext; simp
/-
**MvPolynomial.sumAlgEquiv_comp_rename_inl** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomi
al`。
形式化陈述：sumAlgEquiv_comp_rename_inl : (sumAlgEquiv R S₁ S₂).toAlgHom.comp (rename 
.inl) = MvPolynomial.mapAlgHom (Algebra.ofId _ _)
该定理/引理给出了一组等式。
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
· 使用引理 `MvPolynomial.sumAlgEquiv_X_inl`：sumAlgEquiv_X_inl (c : S₁) : sumAlgEquiv
 R S₁ S₂ (X <| .inl c) = X c
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumAlgEquiv_comp_rename_inl :
    (sumAlgEquiv R S₁ S₂).toAlgHom.comp (rename .inl) =
      MvPolynomial.mapAlgHom (Algebra.ofId _ _) := by
  ext; simp

section commAlgEquiv
variable {R S₁ S₂ : Type*} [CommSemiring R]

variable (R S₁ S₂) in
/-- The algebra isomorphism between multivariable polynomials in variables `S₁` of multivariable
polynomials in variables `S₂` and multivariable polynomials in variables `S₂` of multivariable
polynomials in variables `S₁`. -/
noncomputable
/-
**MvPolynomial.commAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：commAlgEquiv : MvPolynomial S₁ (MvPolynomial S₂ R) ≃ₐ[R] MvPolynomial S₂ (
MvPolynomial S₁ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def commAlgEquiv : MvPolynomial S₁ (MvPolynomial S₂ R) ≃ₐ[R] MvPolynomial S₂ (MvPolynomial S₁ R) :=
  AddMonoidAlgebra.commAlgEquiv _
/-
**MvPolynomial.commAlgEquiv_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u_2} {S₁ : Type u_3} {S₂ : Type u_4} [inst : CommSemiring R] (
p : MvPolynomial S₂ R),   (MvPolynomial.commAlgEquiv R S₁ S₂) (MvPolynomial.C p)
 = (MvPolynomial.map MvPolynomial.C) p
参数：p : MvPolynomial S₂ R；MvPolynomial.commAlgEquiv R S₁ S₂；MvPolynomial.C p；MvPo
lynomial.map MvPolynomial.C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidAlgebra.commAlgEquiv_single_zero_single`：∀ {R : Type u_1} {A : 
Type u_4} {M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiri
ng A]   [inst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.mapAlgHom_single`：∀ {R : Type u_1} {A : Type u_4} {B : 
Type u_5} {M : Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2
 : Semiring B] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
@[simp] lemma commAlgEquiv_C (p) : commAlgEquiv R S₁ S₂ (.C p) = .map C p := by
  suffices (commAlgEquiv R S₁ S₂).toAlgHom.comp
      (IsScalarTower.toAlgHom R (MvPolynomial S₂ R) _) = mapAlgHom (Algebra.ofId _ _) by
    exact DFunLike.congr_fun this p
  ext; simp [commAlgEquiv, mapAlgHom, X, C, monomial, coeff, AddMonoidAlgebra.one_def]
/-
**MvPolynomial.commAlgEquiv_C_X** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：commAlgEquiv_C_X (i) : commAlgEquiv R S₁ S₂ (.C (.X i)) = .X i
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.commAlgEquiv_C`：∀ {R : Type u_2} {S₁ : Type u_3} {S₂ : Type
 u_4} [inst : CommSemiring R] (p : MvPolynomial S₂ R),   (MvPolynomial.commAlgEq
uiv R S₁ S₂) (MvP…
· 使用定理 `AddMonoidAlgebra.mapRingHom_single`：∀ {R : Type u_3} {S : Type u_4} {M :
 Type u_6} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : AddMonoid M]   (f
 : R →+* S) (a : M) (b :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma commAlgEquiv_C_X (i) : commAlgEquiv R S₁ S₂ (.C (.X i)) = .X i := by simp [map, X, monomial]
/-
**MvPolynomial.commAlgEquiv_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u_2} {S₁ : Type u_3} {S₂ : Type u_4} [inst : CommSemiring R] (
i : S₁),   (MvPolynomial.commAlgEquiv R S₁ S₂) (MvPolynomial.X i) = MvPolynomial
.C (MvPolynomial.X i)
参数：i : S₁；MvPolynomial.commAlgEquiv R S₁ S₂；MvPolynomial.X i；MvPolynomial.X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.commAlgEquiv_single_zero`：∀ {R : Type u_1} {A : Type u_
4} {M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]  
 [inst_2 : Algebra R A] [inst_3…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma commAlgEquiv_X (i) : commAlgEquiv R S₁ S₂ (.X i) = .C (.X i) := by
  ext x y; simp [X, C, monomial, commAlgEquiv]

end commAlgEquiv

section optionEquivLeft

-- this speeds up typeclass search in the lemma below
attribute [local instance] IsScalarTower.right

/-- The algebra isomorphism between multivariable polynomials in `Option S₁` and
polynomials with coefficients in `MvPolynomial S₁ R`.
-/
@[simps! -isSimp]
/-
**MvPolynomial.optionEquivLeft** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：optionEquivLeft : MvPolynomial (Option S₁) R ≃ₐ[R] Polynomial (MvPolynomia
l S₁ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra isomorphism between multivariable polynomials in `Option S₁` and
polynomials with coefficients in `MvPolynomial S₁ R`.
-/
def optionEquivLeft : MvPolynomial (Option S₁) R ≃ₐ[R] Polynomial (MvPolynomial S₁ R) :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun o => o.elim Polynomial.X fun s => Polynomial.C (X s))
    (Polynomial.aevalTower (MvPolynomial.rename some) (X none))
    (by ext : 2 <;> simp) (by ext i : 2; cases i <;> simp)

@[simp]
/-
**MvPolynomial.optionEquivLeft_X_some** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：optionEquivLeft_X_some (x : S₁) : optionEquivLeft R S₁ (X (some x)) = Poly
nomial.C (X x)
参数：x : S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.optionEquivLeft_apply`：∀ (R : Type u) (S₁ : Type v) [inst :
 CommSemiring R] (a : MvPolynomial (Option S₁) R),   (MvPolynomial.optionEquivLe
ft R S₁) a =     (MvPoly…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionEquivLeft_X_some (x : S₁) : optionEquivLeft R S₁ (X (some x)) = Polynomial.C (X x) := by
  simp [optionEquivLeft_apply, aeval_X]

@[simp]
/-
**MvPolynomial.optionEquivLeft_X_none** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：optionEquivLeft_X_none : optionEquivLeft R S₁ (X none) = Polynomial.X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.optionEquivLeft_apply`：∀ (R : Type u) (S₁ : Type v) [inst :
 CommSemiring R] (a : MvPolynomial (Option S₁) R),   (MvPolynomial.optionEquivLe
ft R S₁) a =     (MvPoly…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionEquivLeft_X_none : optionEquivLeft R S₁ (X none) = Polynomial.X := by
  simp [optionEquivLeft_apply, aeval_X]

@[simp]
/-
**MvPolynomial.optionEquivLeft_C** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：optionEquivLeft_C (r : R) : optionEquivLeft R S₁ (C r) = Polynomial.C (C r
)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.optionEquivLeft_apply`：∀ (R : Type u) (S₁ : Type v) [inst :
 CommSemiring R] (a : MvPolynomial (Option S₁) R),   (MvPolynomial.optionEquivLe
ft R S₁) a =     (MvPoly…
· 使用定理 `MvPolynomial.aeval_C`：aeval_C (r : R) : aeval f (C r) = algebraMap R S₁ 
r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionEquivLeft_C (r : R) : optionEquivLeft R S₁ (C r) = Polynomial.C (C r) := by
  simp only [optionEquivLeft_apply, aeval_C, Polynomial.algebraMap_apply, algebraMap_eq]
/-
**MvPolynomial.optionEquivLeft_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：optionEquivLeft_monomial (m : Option S₁ ->₀ Nat) (r : R) : optionEquivLeft
 R S₁ (monomial m r) = .monomial (m none) (monomial m.some r)
参数：m : Option S₁ ->₀ Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.optionEquivLeft_apply`：∀ (R : Type u) (S₁ : Type v) [inst :
 CommSemiring R] (a : MvPolynomial (Option S₁) R),   (MvPolynomial.optionEquivLe
ft R S₁) a =     (MvPoly…
· 使用定理 `MvPolynomial.aeval_monomial`：aeval_monomial (g : σ -> S₁) (d : σ ->₀ Nat
) (r : R) : aeval g (monomial d r) = algebraMap _ _ r * d.prod fun i k => g i ^ 
k
· 使用定理 `Finsupp.prod_option_index`：prod_option_index [AddZeroClass M] [CommMonoi
d N] (f : Option α ->₀ M) (b : Option α -> M -> N) (h_zero : forall o, b o 0 = 1
) (h_add : fora…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `MvPolynomial.monomial_eq`：monomial_eq : monomial s a = C a * (s.prod fun
 n e => X n ^ e : MvPolynomial σ R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `map_finsuppProd`：map_finsuppProd [Zero M] [CommMonoid N] [CommMonoid P] 
{H : Type*} [FunLike H N P] [MonoidHomClass H N P] (h : H) (f : α ->₀ M) (g : α 
-> M …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
-/
theorem optionEquivLeft_monomial (m : Option S₁ →₀ ℕ) (r : R) :
    optionEquivLeft R S₁ (monomial m r) = .monomial (m none) (monomial m.some r) := by
  rw [optionEquivLeft_apply, aeval_monomial, prod_option_index]
  · rw [MvPolynomial.monomial_eq, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.algebraMap_apply, algebraMap_eq, Option.elim_none, Option.elim_some,
      map_mul, mul_assoc]
    simp only [mul_comm, map_finsuppProd, map_pow]
  · simp
  · intros; rw [pow_add]

@[simp]
/-
**MvPolynomial.optionEquivLeft_symm_C_X** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`
。
形式化陈述：optionEquivLeft_symm_C_X (x : S₁) : (optionEquivLeft R S₁).symm (.C (X x))
 = .X (.some x)
参数：x : S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_symm_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `Polynomial.aevalTower_C`：aevalTower_C (x : R) : aevalTower g y (C x) = g
 x
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionEquivLeft_symm_C_X (x : S₁) :
    (optionEquivLeft R S₁).symm (.C (X x)) = .X (.some x) := by
  simp [optionEquivLeft]

@[simp]
/-
**MvPolynomial.optionEquivLeft_symm_C_C** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`
。
形式化陈述：optionEquivLeft_symm_C_C (x : R) : (optionEquivLeft R S₁).symm (.C (.C x))
 = .C x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_symm_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `Polynomial.aevalTower_C`：aevalTower_C (x : R) : aevalTower g y (C x) = g
 x
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionEquivLeft_symm_C_C (x : R) :
    (optionEquivLeft R S₁).symm (.C (.C x)) = .C x := by simp [optionEquivLeft]

@[simp]
/-
**MvPolynomial.optionEquivLeft_symm_X** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：optionEquivLeft_symm_X : (optionEquivLeft R S₁).symm .X = .X .none
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_symm_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `Polynomial.aevalTower_X`：aevalTower_X : aevalTower g y X = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionEquivLeft_symm_X :
    (optionEquivLeft R S₁).symm .X = .X .none := by simp [optionEquivLeft]

/-- The coefficient of `n.some` in the `n none`-th coefficient of `optionEquivLeft R S₁ f`
equals the coefficient of `n` in `f` -/
/-
**MvPolynomial.optionEquivLeft_coeff_some_coeff_none** 是 Mathlib 中的一个定理，位于命名空间 `
MvPolynomial`。
形式化陈述：optionEquivLeft_coeff_some_coeff_none (n : Option S₁ ->₀ Nat) (f : MvPolyn
omial (Option S₁) R) : coeff n.some (Polynomial.coeff (optionEquivLeft R S₁ f) (
n none)) = coeff n f
参数：n : Option S₁ ->₀ Nat；f : MvPolynomial (Option S₁) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on'`：induction_on' {P : MvPolynomial σ R -> Prop}
 (p : MvPolynomial σ R) (monomial : forall (u : σ ->₀ Nat) (a : R), P (monomial 
u a)) (add : for…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.optionEquivLeft_monomial`：optionEquivLeft_monomial (m : Opt
ion S₁ ->₀ Nat) (r : R) : optionEquivLeft R S₁ (monomial m r) = .monomial (m non
e) (monomial m.some r)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
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
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q

--- 原说明 ---
The coefficient of `n.some` in the `n none`-th coefficient of `optionEquivLeft R
 S₁ f`
equals the coefficient of `n` in `f`
-/
theorem optionEquivLeft_coeff_some_coeff_none
    (n : Option S₁ →₀ ℕ) (f : MvPolynomial (Option S₁) R) :
    coeff n.some (Polynomial.coeff (optionEquivLeft R S₁ f) (n none)) = coeff n f := by
  induction f using MvPolynomial.induction_on' generalizing n with
  | monomial j r =>
    rw [optionEquivLeft_monomial]
    classical
    simp only [Polynomial.coeff_monomial, MvPolynomial.coeff_monomial, apply_ite]
    simp only [coeff_zero]
    by_cases hj : j = n
    · simp [hj]
    · rw [if_neg hj]
      simp only [ite_eq_right_iff]
      intro hj_none hj_some
      apply False.elim (hj _)
      simp only [Finsupp.ext_iff, Option.forall, hj_none, true_and]
      simpa only [Finsupp.ext_iff] using! hj_some
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]
/-
**MvPolynomial.optionEquivLeft_elim_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：optionEquivLeft_elim_eval (s : S₁ -> R) (y : R) (f : MvPolynomial (Option 
S₁) R) : eval (fun x => Option.elim x y s) f = Polynomial.eval y (Polynomial.map
 (eval s) (optionEquivLeft R S₁ f))
参数：s : S₁ -> R；y : R；f : MvPolynomial (Option S₁) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.forall`：∀ {α : Type u_1} {p : Option α → Prop}, (∀ (x : Option α)
, p x) ↔ p none ∧ ∀ (x : α), p (some x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `MvPolynomial.optionEquivLeft_apply`：∀ (R : Type u) (S₁ : Type v) [inst :
 CommSemiring R] (a : MvPolynomial (Option S₁) R),   (MvPolynomial.optionEquivLe
ft R S₁) a =     (MvPoly…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem optionEquivLeft_elim_eval (s : S₁ → R) (y : R) (f : MvPolynomial (Option S₁) R) :
    eval (fun x ↦ Option.elim x y s) f =
      Polynomial.eval y (Polynomial.map (eval s) (optionEquivLeft R S₁ f)) := by
  -- turn this into a def `Polynomial.mapAlgHom`
  let φ : (MvPolynomial S₁ R)[X] →ₐ[R] R[X] :=
    { Polynomial.mapRingHom (eval s) with
      commutes' := fun r => by
        convert! Polynomial.map_C (eval s)
        exact (eval_C _).symm }
  change
    aeval (fun x ↦ Option.elim x y s) f =
      (Polynomial.aeval y).comp (φ.comp (optionEquivLeft _ _).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  rw [Option.forall]
  simp only [aeval_X, Option.elim_none, AlgHom.coe_comp, Polynomial.coe_aeval_eq_eval,
    AlgHom.coe_mk, Polynomial.coe_mapRingHom, AlgEquiv.coe_toAlgHom, comp_apply,
    optionEquivLeft_apply, Polynomial.map_X, Polynomial.eval_X, Option.elim_some,
    Polynomial.map_C, eval_X, Polynomial.eval_C, implies_true, and_self, φ]
/-
**MvPolynomial.mem_support_coeff_optionEquivLeft** 是 Mathlib 中的一个定理，位于命名空间 `MvPo
lynomial`。
形式化陈述：mem_support_coeff_optionEquivLeft {f : MvPolynomial (Option σ) R} {i : Nat
} {m : σ ->₀ Nat} : m in ((optionEquivLeft R σ f).coeff i).support ↔ m.optionEli
m i in f.support
参数：Option σ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finsupp.some_optionElim`：some_optionElim (y : M) (f : α ->₀ M) : (f.opti
onElim y).some = f
· 使用引理 `Finsupp.optionElim_apply_eq_elim`：optionElim_apply_eq_elim (y : M) (f : 
α ->₀ M) (a : Option α) : f.optionElim y a = a.elim y f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_coeff_optionEquivLeft {f : MvPolynomial (Option σ) R} {i : ℕ} {m : σ →₀ ℕ} :
    m ∈ ((optionEquivLeft R σ f).coeff i).support ↔ m.optionElim i ∈ f.support := by
  simp [← optionEquivLeft_coeff_some_coeff_none]

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.support_optionEquivLeft** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：support_optionEquivLeft (p : MvPolynomial (Option σ) R) : (optionEquivLeft
 R σ p).support = Finset.image (fun m => m none) p.support
参数：p : MvPolynomial (Option σ) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finsupp.some_optionElim`：some_optionElim (y : M) (f : α ->₀ M) : (f.opti
onElim y).some = f
· 使用引理 `Finsupp.optionElim_apply_eq_elim`：optionElim_apply_eq_elim (y : M) (f : 
α ->₀ M) (a : Option α) : f.optionElim y a = a.elim y f
· 使用引理 `Finsupp.optionElim_apply_none`：optionElim_apply_none (y : M) (f : α ->₀ 
M) : f.optionElim y none = y
-/
lemma support_optionEquivLeft (p : MvPolynomial (Option σ) R) :
    (optionEquivLeft R σ p).support = Finset.image (fun m => m none) p.support := by
  ext i
  simp only [Polynomial.mem_support_iff, ne_eq, MvPolynomial.ext_iff, coeff_zero, not_forall,
    Finset.mem_image, mem_support_iff, ← optionEquivLeft_coeff_some_coeff_none]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨optionElim i m, by simpa using! hm, optionElim_apply_none _ _⟩
  · rintro ⟨m, h, rfl⟩
    exact ⟨some m, h⟩
/-
**MvPolynomial.nonempty_support_optionEquivLeft** 是 Mathlib 中的一个定理，位于命名空间 `MvPol
ynomial`。
形式化陈述：nonempty_support_optionEquivLeft {f : MvPolynomial (Option σ) R} (h : f !=
 0) : (optionEquivLeft R σ f).support.Nonempty
参数：Option σ；h : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.support_nonempty`：∀ {R : Type u} [inst : Semiring R] {p : Pol
ynomial R}, p.support.Nonempty ↔ p ≠ 0
· 使用定理 `EmbeddingLike.map_ne_zero_iff`：∀ {F : Type u_1} {M : Type u_4} {N : Type
 u_5} [inst : Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [EmbeddingLik
e F M N] [ZeroHomCl…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem nonempty_support_optionEquivLeft {f : MvPolynomial (Option σ) R} (h : f ≠ 0) :
    (optionEquivLeft R σ f).support.Nonempty := by
  rwa [Polynomial.support_nonempty, EmbeddingLike.map_ne_zero_iff]
/-
**MvPolynomial.degree_optionEquivLeft** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degree_optionEquivLeft {f : MvPolynomial (Option σ) R} (h : f != 0) : (opt
ionEquivLeft R σ f).degree = degreeOf none f
参数：Option σ；h : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_eq_sup`：degreeOf_eq_sup (n : σ) (f : MvPolynomial 
σ R) : degreeOf n f = f.support.sup fun m => m n
· 使用引理 `MvPolynomial.support_optionEquivLeft`：support_optionEquivLeft (p : MvPol
ynomial (Option σ) R) : (optionEquivLeft R σ p).support = Finset.image (fun m =>
 m none) p.support
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Polynomial.degree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R), p.degree = p.support.max
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
· 使用定理 `Finset.coe_sup_of_nonempty`：coe_sup_of_nonempty (h : s.Nonempty) (f : β 
-> α) : (↑(s.sup f) : WithBot α) = s.sup ((↑) ∘ f)
· 使用定理 `MvPolynomial.nonempty_support_optionEquivLeft`：nonempty_support_optionEq
uivLeft {f : MvPolynomial (Option σ) R} (h : f != 0) : (optionEquivLeft R σ f).s
upport.Nonempty
· 使用定理 `Finset.max_eq_sup_coe`：max_eq_sup_coe {s : Finset α} : s.max = s.sup (↑)
-/
theorem degree_optionEquivLeft {f : MvPolynomial (Option σ) R} (h : f ≠ 0) :
    (optionEquivLeft R σ f).degree = degreeOf none f := by
  have h' : ((optionEquivLeft R σ f).support.sup fun x => x) = degreeOf none f := by
    rw [degreeOf_eq_sup, support_optionEquivLeft, Finset.sup_image, Function.comp_def]
  rw [Polynomial.degree, ← h', Nat.cast_withBot,
    Finset.coe_sup_of_nonempty (nonempty_support_optionEquivLeft R h), Finset.max_eq_sup_coe,
    Function.comp_def]

@[simp]
/-
**MvPolynomial.natDegree_optionEquivLeft** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial
`。
形式化陈述：natDegree_optionEquivLeft (p : MvPolynomial (Option σ) R) : Polynomial.nat
Degree (optionEquivLeft R σ p) = p.degreeOf none
参数：p : MvPolynomial (Option σ) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `MvPolynomial.degreeOf_zero`：degreeOf_zero (n : σ) : degreeOf n (0 : MvPo
lynomial σ R) = 0
· 使用定理 `Polynomial.natDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R), p.natDegree = WithBot.unbotD 0 p.degree
· 使用定理 `MvPolynomial.degree_optionEquivLeft`：degree_optionEquivLeft {f : MvPolyn
omial (Option σ) R} (h : f != 0) : (optionEquivLeft R σ f).degree = degreeOf non
e f
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
· 使用定理 `WithBot.unbotD_coe`：unbotD_coe {α} (d x : α) : unbotD d x = x
-/
lemma natDegree_optionEquivLeft (p : MvPolynomial (Option σ) R) :
    Polynomial.natDegree (optionEquivLeft R σ p) = p.degreeOf none := by
  by_cases c : p = 0
  · rw [c, map_zero, Polynomial.natDegree_zero, degreeOf_zero]
  · rw [Polynomial.natDegree, degree_optionEquivLeft R c, Nat.cast_withBot, WithBot.unbotD_coe]

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.totalDegree_coeff_optionEquivLeft_add_le** 是 Mathlib 中的一个引理，位于命名空
间 `MvPolynomial`。
形式化陈述：totalDegree_coeff_optionEquivLeft_add_le (p : MvPolynomial (Option S₁) R) 
(i : Nat) (hi : i <= p.totalDegree) : ((optionEquivLeft R S₁ p).coeff i).totalDe
gree + i <= p.totalDegree
参数：p : MvPolynomial (Option S₁) R；i : Nat；hi : i <= p.totalDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.totalDegree_zero`：totalDegree_zero : (0 : MvPolynomial σ R)
.totalDegree = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MvPolynomial.totalDegree.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : Com
mSemiring R] (p : MvPolynomial σ R),   p.totalDegree = p.support.sup fun s => s.
sum fun x e => e
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finset.add_sup`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M]
 [inst_1 : LinearOrder M] [CanonicallyOrderedAdd M]   [inst_3 : Sub M] [AddLeftR
efle…
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.sum_add_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : DecidableEq α] [inst_1 : AddZeroClass M]   [inst_2 : AddCommMonoid N] {f 
g : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.Embedding.some_apply`：∀ {α : Type u_1}, ⇑Function.Embedding.som
e = some
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.sum_embDomain`：∀ {α : Type u_1} {β : Type u_7} {M : Type u_8} {N
 : Type u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] {v : α →₀ M}   {f : α ↪
 β} {g : β …
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.optionEquivLeft_coeff_some_coeff_none`：optionEquivLeft_coef
f_some_coeff_none (n : Option S₁ ->₀ Nat) (f : MvPolynomial (Option S₁) R) : coe
ff n.some (Polynomial.coeff (optionEquiv…
· 使用定理 `Finsupp.some_add`：some_add [AddZeroClass M] (f g : Option α ->₀ M) : (f 
+ g).some = f.some + g.some
（共 35 条，此处仅展示前 30 条）
-/
lemma totalDegree_coeff_optionEquivLeft_add_le
    (p : MvPolynomial (Option S₁) R) (i : ℕ) (hi : i ≤ p.totalDegree) :
    ((optionEquivLeft R S₁ p).coeff i).totalDegree + i ≤ p.totalDegree := by
  classical
  by_cases hpi : (optionEquivLeft R S₁ p).coeff i = 0
  · rw [hpi]; simpa
  rw [totalDegree, add_comm, Finset.add_sup (by simpa only [support_nonempty]), Finset.sup_le_iff]
  intro σ hσ
  refine le_trans ?_ (Finset.le_sup (b := σ.embDomain .some + .single .none i) ?_)
  · simp [Finsupp.sum_add_index, Finsupp.sum_embDomain, add_comm i]
  · simpa [mem_support_iff, ← optionEquivLeft_coeff_some_coeff_none R S₁] using hσ

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.totalDegree_coeff_optionEquivLeft_le** 是 Mathlib 中的一个引理，位于命名空间 `M
vPolynomial`。
形式化陈述：totalDegree_coeff_optionEquivLeft_le (p : MvPolynomial (Option S₁) R) (i :
 Nat) : ((optionEquivLeft R S₁ p).coeff i).totalDegree <= p.totalDegree
参数：p : MvPolynomial (Option S₁) R；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.totalDegree_zero`：totalDegree_zero : (0 : MvPolynomial σ R)
.totalDegree = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `MvPolynomial.totalDegree.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : Com
mSemiring R] (p : MvPolynomial σ R),   p.totalDegree = p.support.sup fun s => s.
sum fun x e => e
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finsupp.sum_add_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : DecidableEq α] [inst_1 : AddZeroClass M]   [inst_2 : AddCommMonoid N] {f 
g : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.Embedding.some_apply`：∀ {α : Type u_1}, ⇑Function.Embedding.som
e = some
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.sum_embDomain`：∀ {α : Type u_1} {β : Type u_7} {M : Type u_8} {N
 : Type u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] {v : α →₀ M}   {f : α ↪
 β} {g : β …
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.optionEquivLeft_coeff_some_coeff_none`：optionEquivLeft_coef
f_some_coeff_none (n : Option S₁ ->₀ Nat) (f : MvPolynomial (Option S₁) R) : coe
ff n.some (Polynomial.coeff (optionEquiv…
· 使用定理 `Finsupp.some_add`：some_add [AddZeroClass M] (f g : Option α ->₀ M) : (f 
+ g).some = f.some + g.some
· 使用定理 `Finsupp.some_embDomain_some`：∀ {α : Type u_1} {M : Type u_2} [inst : Zer
o M] (f : α →₀ M), (Finsupp.embDomain Function.Embedding.some f).some = f
· 使用定理 `Finsupp.some_single_none`：some_single_none (m : M) : (single none m : Op
tion α ->₀ M).some = 0
（共 34 条，此处仅展示前 30 条）
-/
lemma totalDegree_coeff_optionEquivLeft_le
    (p : MvPolynomial (Option S₁) R) (i : ℕ) :
    ((optionEquivLeft R S₁ p).coeff i).totalDegree ≤ p.totalDegree := by
  classical
  by_cases hpi : (optionEquivLeft R S₁ p).coeff i = 0
  · rw [hpi]; simp
  rw [totalDegree, Finset.sup_le_iff]
  intro σ hσ
  refine le_trans ?_ (Finset.le_sup (b := σ.embDomain .some + .single .none i) ?_)
  · simp [Finsupp.sum_add_index, Finsupp.sum_embDomain]
  · simpa [mem_support_iff, ← optionEquivLeft_coeff_some_coeff_none R S₁] using hσ
/-
**MvPolynomial.optionEquivLeft_coeff_coeff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：optionEquivLeft_coeff_coeff (p : MvPolynomial (Option σ) R) (m : Nat) (d :
 σ ->₀ Nat) : coeff d (((optionEquivLeft R σ) p).coeff m) = p.coeff (d.optionEli
m m)
参数：p : MvPolynomial (Option σ) R；m : Nat；d : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.optionEquivLeft_coeff_some_coeff_none`：optionEquivLeft_coef
f_some_coeff_none (n : Option S₁ ->₀ Nat) (f : MvPolynomial (Option S₁) R) : coe
ff n.some (Polynomial.coeff (optionEquiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finsupp.some_optionElim`：some_optionElim (y : M) (f : α ->₀ M) : (f.opti
onElim y).some = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finsupp.optionElim_apply_eq_elim`：optionElim_apply_eq_elim (y : M) (f : 
α ->₀ M) (a : Option α) : f.optionElim y a = a.elim y f
-/
theorem optionEquivLeft_coeff_coeff
    (p : MvPolynomial (Option σ) R) (m : ℕ) (d : σ →₀ ℕ) :
    coeff d (((optionEquivLeft R σ) p).coeff m) = p.coeff (d.optionElim m) := by
  rw [← optionEquivLeft_coeff_some_coeff_none]
  congr <;> simp

end optionEquivLeft

/-- The algebra isomorphism between multivariable polynomials in `Option S₁` and
multivariable polynomials with coefficients in polynomials.
-/
@[simps!]
/-
**MvPolynomial.optionEquivRight** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：optionEquivRight : MvPolynomial (Option S₁) R ≃ₐ[R] MvPolynomial S₁ R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra isomorphism between multivariable polynomials in `Option S₁` and
multivariable polynomials with coefficients in polynomials.
-/
def optionEquivRight : MvPolynomial (Option S₁) R ≃ₐ[R] MvPolynomial S₁ R[X] :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun o => o.elim (C Polynomial.X) X)
    (MvPolynomial.aevalTower (Polynomial.aeval (X none)) fun i => X (Option.some i))
    (by
      ext : 2 <;>
        simp only [MvPolynomial.algebraMap_eq, Option.elim, AlgHom.coe_comp, AlgHom.id_comp,
          IsScalarTower.coe_toAlgHom', comp_apply, aevalTower_C, Polynomial.aeval_X, aeval_X,
          aevalTower_X, AlgHom.coe_id, id])
    (by
      ext ⟨i⟩ : 2 <;>
        simp only [Option.elim, AlgHom.coe_comp, comp_apply, aeval_X, aevalTower_C,
          Polynomial.aeval_X, AlgHom.coe_id, id, aevalTower_X])
/-
**MvPolynomial.optionEquivRight_X_some** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：optionEquivRight_X_some (x : S₁) : optionEquivRight R S₁ (X (some x)) = X 
x
参数：x : S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.optionEquivRight_apply`：∀ (R : Type u) (S₁ : Type v) [inst 
: CommSemiring R] (a : MvPolynomial (Option S₁) R),   (MvPolynomial.optionEquivR
ight R S₁) a =     (MvPol…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionEquivRight_X_some (x : S₁) : optionEquivRight R S₁ (X (some x)) = X x := by
  simp [optionEquivRight_apply, aeval_X]
/-
**MvPolynomial.optionEquivRight_X_none** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：optionEquivRight_X_none : optionEquivRight R S₁ (X none) = C Polynomial.X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.optionEquivRight_apply`：∀ (R : Type u) (S₁ : Type v) [inst 
: CommSemiring R] (a : MvPolynomial (Option S₁) R),   (MvPolynomial.optionEquivR
ight R S₁) a =     (MvPol…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionEquivRight_X_none : optionEquivRight R S₁ (X none) = C Polynomial.X := by
  simp [optionEquivRight_apply, aeval_X]
/-
**MvPolynomial.optionEquivRight_C** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：optionEquivRight_C (r : R) : optionEquivRight R S₁ (C r) = C (Polynomial.C
 r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.optionEquivRight_apply`：∀ (R : Type u) (S₁ : Type v) [inst 
: CommSemiring R] (a : MvPolynomial (Option S₁) R),   (MvPolynomial.optionEquivR
ight R S₁) a =     (MvPol…
· 使用定理 `MvPolynomial.aeval_C`：aeval_C (r : R) : aeval f (C r) = algebraMap R S₁ 
r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionEquivRight_C (r : R) : optionEquivRight R S₁ (C r) = C (Polynomial.C r) := by
  simp only [optionEquivRight_apply, aeval_C, algebraMap_apply, Polynomial.algebraMap_eq]

variable (n : ℕ)

/-- The algebra isomorphism between multivariable polynomials in `Fin (n + 1)` and
polynomials over multivariable polynomials in `Fin n`.
-/
/-
**MvPolynomial.finSuccEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：finSuccEquiv : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial
 (Fin n) R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra isomorphism between multivariable polynomials in `Fin (n + 1)` and
polynomials over multivariable polynomials in `Fin n`.
-/
def finSuccEquiv : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv n)).trans (optionEquivLeft R (Fin n))
/-
**MvPolynomial.finSuccEquiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：finSuccEquiv_eq : (finSuccEquiv R n : MvPolynomial (Fin (n + 1)) R ->+* Po
lynomial (MvPolynomial (Fin n) R)) = eval₂Hom (Polynomial.C.comp (C : R ->+* MvP
olynomial (Fin n) R)) fun i : Fin (n + 1) => Fin.cases Polynomial.X (fun k => Po
lynomial.C (X k)) i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ringHom_ext'`：ringHom_ext' {A : Type*} [Semiring A] {f g : 
MvPolynomial σ R ->+* A} (hC : f.comp C = g.comp C) (hX : forall i, f (X i) = g 
(X i)) : f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.renameEquiv_apply`：∀ {σ : Type u_1} {τ : Type u_2} (R : Typ
e u_4) [inst : CommSemiring R] (f : σ ≃ τ) (a : MvPolynomial σ R),   (MvPolynomi
al.renameEquiv R f) …
· 使用定理 `MvPolynomial.rename_C`：rename_C (f : σ -> τ) (r : R) : rename f (C r) = 
C r
· 使用定理 `MvPolynomial.optionEquivLeft_apply`：∀ (R : Type u) (S₁ : Type v) [inst :
 CommSemiring R] (a : MvPolynomial (Option S₁) R),   (MvPolynomial.optionEquivLe
ft R S₁) a =     (MvPoly…
· 使用定理 `MvPolynomial.aeval_C`：aeval_C (r : R) : aeval f (C r) = algebraMap R S₁ 
r
· 使用定理 `MvPolynomial.eval₂_C`：eval₂_C (a) : (C a).eval₂ f g = f a
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `MvPolynomial.eval₂Hom_X'`：eval₂Hom_X' (f : R ->+* S₁) (g : σ -> S₁) (i :
 σ) : eval₂Hom f g (X i) = g i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `finSuccEquiv_succ`：finSuccEquiv_succ (m : Fin n) : (finSuccEquiv n) m.su
cc = some m
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem finSuccEquiv_eq :
    (finSuccEquiv R n : MvPolynomial (Fin (n + 1)) R →+* Polynomial (MvPolynomial (Fin n) R)) =
      eval₂Hom (Polynomial.C.comp (C : R →+* MvPolynomial (Fin n) R)) fun i : Fin (n + 1) =>
        Fin.cases Polynomial.X (fun k => Polynomial.C (X k)) i := by
  ext i : 2
  · simp only [finSuccEquiv, optionEquivLeft_apply, aeval_C, AlgEquiv.coe_trans, RingHom.coe_coe,
      coe_eval₂Hom, comp_apply, renameEquiv_apply, eval₂_C, RingHom.coe_comp, rename_C]
    rfl
  · refine Fin.cases ?_ ?_ i <;> simp [optionEquivLeft_apply, finSuccEquiv]
/-
**MvPolynomial.finSuccEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：finSuccEquiv_apply (p : MvPolynomial (Fin (n + 1)) R) : finSuccEquiv R n p
 = eval₂Hom (Polynomial.C.comp (C : R ->+* MvPolynomial (Fin n) R)) (fun i : Fin
 (n + 1) => Fin.cases Polynomial.X (fun k => Polynomial.C (X k)) i) p
参数：p : MvPolynomial (Fin (n + 1)) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.finSuccEquiv_eq`：finSuccEquiv_eq : (finSuccEquiv R n : MvPo
lynomial (Fin (n + 1)) R ->+* Polynomial (MvPolynomial (Fin n) R)) = eval₂Hom (P
olynomial.C.comp (…
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
-/
theorem finSuccEquiv_apply (p : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv R n p =
      eval₂Hom (Polynomial.C.comp (C : R →+* MvPolynomial (Fin n) R))
        (fun i : Fin (n + 1) => Fin.cases Polynomial.X (fun k => Polynomial.C (X k)) i) p := by
  rw [← finSuccEquiv_eq, RingHom.coe_coe]
/-
**MvPolynomial.finSuccEquiv_comp_C_eq_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：finSuccEquiv_comp_C_eq_C {R : Type u} [CommSemiring R] (n : Nat) : (↑(MvPo
lynomial.finSuccEquiv R n).symm : Polynomial (MvPolynomial (Fin n) R) ->+* _).co
mp (Polynomial.C.comp MvPolynomial.C) = (MvPolynomial.C : R ->+* MvPolynomial (F
in n.succ) R)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.finSuccEquiv_apply`：finSuccEquiv_apply (p : MvPolynomial (F
in (n + 1)) R) : finSuccEquiv R n p = eval₂Hom (Polynomial.C.comp (C : R ->+* Mv
Polynomial (Fin n) R)…
· 使用定理 `MvPolynomial.eval₂Hom_C`：eval₂Hom_C (f : R ->+* S₁) (g : σ -> S₁) (r : R
) : eval₂Hom f g (C r) = f r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finSuccEquiv_comp_C_eq_C {R : Type u} [CommSemiring R] (n : ℕ) :
    (↑(MvPolynomial.finSuccEquiv R n).symm : Polynomial (MvPolynomial (Fin n) R) →+* _).comp
        (Polynomial.C.comp MvPolynomial.C) =
      (MvPolynomial.C : R →+* MvPolynomial (Fin n.succ) R) := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply]
  refine
    (MvPolynomial.finSuccEquiv R n).injective
      (Trans.trans ((MvPolynomial.finSuccEquiv R n).apply_symm_apply _) ?_)
  simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]

variable {n} {R}
/-
**MvPolynomial.finSuccEquiv_X_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：finSuccEquiv_X_zero : finSuccEquiv R n (X 0) = Polynomial.X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.finSuccEquiv_apply`：finSuccEquiv_apply (p : MvPolynomial (F
in (n + 1)) R) : finSuccEquiv R n p = eval₂Hom (Polynomial.C.comp (C : R ->+* Mv
Polynomial (Fin n) R)…
· 使用定理 `MvPolynomial.eval₂Hom_X'`：eval₂Hom_X' (f : R ->+* S₁) (g : σ -> S₁) (i :
 σ) : eval₂Hom f g (X i) = g i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finSuccEquiv_X_zero : finSuccEquiv R n (X 0) = Polynomial.X := by simp [finSuccEquiv_apply]
/-
**MvPolynomial.finSuccEquiv_X_succ** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：finSuccEquiv_X_succ {j : Fin n} : finSuccEquiv R n (X j.succ) = Polynomial
.C (X j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.finSuccEquiv_apply`：finSuccEquiv_apply (p : MvPolynomial (F
in (n + 1)) R) : finSuccEquiv R n p = eval₂Hom (Polynomial.C.comp (C : R ->+* Mv
Polynomial (Fin n) R)…
· 使用定理 `MvPolynomial.eval₂Hom_X'`：eval₂Hom_X' (f : R ->+* S₁) (g : σ -> S₁) (i :
 σ) : eval₂Hom f g (X i) = g i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finSuccEquiv_X_succ {j : Fin n} : finSuccEquiv R n (X j.succ) = Polynomial.C (X j) := by
  simp [finSuccEquiv_apply]

/-- The coefficient of `m` in the `i`-th coefficient of `finSuccEquiv R n f` equals the
    coefficient of `Finsupp.cons i m` in `f`. -/
/-
**MvPolynomial.finSuccEquiv_coeff_coeff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：finSuccEquiv_coeff_coeff (m : Fin n ->₀ Nat) (f : MvPolynomial (Fin (n + 1
)) R) (i : Nat) : coeff m (Polynomial.coeff (finSuccEquiv R n f) i) = coeff (m.c
ons i) f
参数：m : Fin n ->₀ Nat；f : MvPolynomial (Fin (n + 1)) R；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on'`：induction_on' {P : MvPolynomial σ R -> Prop}
 (p : MvPolynomial σ R) (monomial : forall (u : σ ->₀ Nat) (a : R), P (monomial 
u a)) (add : for…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.finSuccEquiv_apply`：finSuccEquiv_apply (p : MvPolynomial (F
in (n + 1)) R) : finSuccEquiv R n p = eval₂Hom (Polynomial.C.comp (C : R ->+* Mv
Polynomial (Fin n) R)…
· 使用定理 `MvPolynomial.eval₂_monomial`：eval₂_monomial : (monomial s a).eval₂ f g =
 f a * s.prod fun n e => g n ^ e
· 使用定理 `Finsupp.prod_pow`：prod_pow [Fintype α] (f : α ->₀ Nat) (g : α -> N) : (f
.prod fun a b => g a ^ b) = ∏ a, g a ^ f a
· 使用定理 `Fin.prod_univ_succ`：prod_univ_succ (f : Fin (n + 1) -> M) : ∏ i, f i = f
 0 * ∏ i : Fin n, f i.succ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `MvPolynomial.coeff_C_mul`：coeff_C_mul (m) (a : R) (p : MvPolynomial σ R)
 : coeff m (C a * p) = a * coeff m p
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_boole`：mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (a * if P then 1 else 0) = if P then a else 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.coeff_C_mul_X_pow`：coeff_C_mul_X_pow (x : R) (k n : Nat) : co
eff (C x * X ^ k : R[X]) n = if n = k then x else 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MvPolynomial.monomial_eq`：monomial_eq : monomial s a = C a * (s.prod fun
 n e => X n ^ e : MvPolynomial σ R)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
The coefficient of `m` in the `i`-th coefficient of `finSuccEquiv R n f` equals 
the
    coefficient of `Finsupp.cons i m` in `f`.
-/
theorem finSuccEquiv_coeff_coeff (m : Fin n →₀ ℕ) (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ) :
    coeff m (Polynomial.coeff (finSuccEquiv R n f) i) = coeff (m.cons i) f := by
  induction f using MvPolynomial.induction_on' generalizing i m with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]
  | monomial j r =>
    simp only [finSuccEquiv_apply, coe_eval₂Hom, eval₂_monomial, RingHom.coe_comp, Finsupp.prod_pow,
      Polynomial.coeff_C_mul, coeff_C_mul, coeff_monomial, Fin.prod_univ_succ, Fin.cases_zero,
      Fin.cases_succ, ← _root_.map_prod, ← map_pow, Function.comp_apply]
    rw [← mul_boole, mul_comm (Polynomial.X ^ j 0), Polynomial.coeff_C_mul_X_pow]; congr 1
    obtain rfl | hjmi := eq_or_ne j (m.cons i)
    · simpa only [cons_zero, cons_succ, if_pos rfl, monomial_eq, C_1, one_mul,
        Finsupp.prod_pow] using! coeff_monomial m m (1 : R)
    · simp only [hjmi, if_false]
      obtain hij | rfl := ne_or_eq i (j 0)
      · simp only [hij, if_false, coeff_zero]
      simp only [if_true]
      have hmj : m ≠ j.tail := by
        rintro rfl
        rw [cons_tail] at hjmi
        contradiction
      simpa only [monomial_eq, C_1, one_mul, Finsupp.prod_pow, tail_apply, if_neg hmj.symm] using!
        coeff_monomial m j.tail (1 : R)
/-
**MvPolynomial.eval_eq_eval_mv_eval'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_eq_eval_mv_eval' (s : Fin n -> R) (y : R) (f : MvPolynomial (Fin (n +
 1)) R) : eval (Fin.cons y s : Fin (n + 1) -> R) f = Polynomial.eval y (Polynomi
al.map (eval s) (finSuccEquiv R n f))
参数：s : Fin n -> R；y : R；f : MvPolynomial (Fin (n + 1)) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.forall_iff_succ`：∀ {n : ℕ} {P : Fin (n + 1) → Prop}, (∀ (i : Fin (n 
+ 1)), P i) ↔ P 0 ∧ ∀ (i : Fin n), P i.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `MvPolynomial.finSuccEquiv_apply`：finSuccEquiv_apply (p : MvPolynomial (F
in (n + 1)) R) : finSuccEquiv R n p = eval₂Hom (Polynomial.C.comp (C : R ->+* Mv
Polynomial (Fin n) R)…
· 使用定理 `MvPolynomial.eval₂Hom_X'`：eval₂Hom_X' (f : R ->+* S₁) (g : σ -> S₁) (i :
 σ) : eval₂Hom f g (X i) = g i
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem eval_eq_eval_mv_eval' (s : Fin n → R) (y : R) (f : MvPolynomial (Fin (n + 1)) R) :
    eval (Fin.cons y s : Fin (n + 1) → R) f =
      Polynomial.eval y (Polynomial.map (eval s) (finSuccEquiv R n f)) := by
  -- turn this into a def `Polynomial.mapAlgHom`
  let φ : (MvPolynomial (Fin n) R)[X] →ₐ[R] R[X] :=
    { Polynomial.mapRingHom (eval s) with
      commutes' := fun r => by
        convert! Polynomial.map_C (eval s)
        exact (eval_C _).symm }
  change
    aeval (Fin.cons y s : Fin (n + 1) → R) f =
      (Polynomial.aeval y).comp (φ.comp (finSuccEquiv R n).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  rw [Fin.forall_iff_succ]
  simp only [aeval_X, Fin.cons_zero, AlgHom.coe_comp, Polynomial.coe_aeval_eq_eval,
    AlgHom.coe_mk, Polynomial.coe_mapRingHom, AlgEquiv.coe_toAlgHom,
    comp_apply, finSuccEquiv_apply, eval₂Hom_X', Fin.cases_zero, Polynomial.map_X,
    Polynomial.eval_X, Fin.cons_succ, Fin.cases_succ, Polynomial.map_C, eval_X, Polynomial.eval_C,
    implies_true, and_self, φ]
/-
**MvPolynomial.coeff_eval_eq_eval_coeff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：coeff_eval_eq_eval_coeff (s' : S₁ -> R) (f : Polynomial (MvPolynomial S₁ R
)) (i : Nat) : Polynomial.coeff (Polynomial.map (eval s') f) i = eval s' (Polyno
mial.coeff f i)
参数：s' : S₁ -> R；f : Polynomial (MvPolynomial S₁ R)；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_eval_eq_eval_coeff (s' : S₁ → R) (f : Polynomial (MvPolynomial S₁ R))
    (i : ℕ) : Polynomial.coeff (Polynomial.map (eval s') f) i = eval s' (Polynomial.coeff f i) := by
  simp only [Polynomial.coeff_map]
/-
**MvPolynomial.mem_support_coeff_finSuccEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyn
omial`。
形式化陈述：mem_support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : Nat
} {m : Fin n ->₀ Nat} : m in ((finSuccEquiv R n f).coeff i).support ↔ m.cons i i
n f.support
参数：Fin (n + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.finSuccEquiv_coeff_coeff`：finSuccEquiv_coeff_coeff (m : Fin
 n ->₀ Nat) (f : MvPolynomial (Fin (n + 1)) R) (i : Nat) : coeff m (Polynomial.c
oeff (finSuccEquiv R n f) i…
-/
theorem mem_support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {m : Fin n →₀ ℕ} :
    m ∈ ((finSuccEquiv R n f).coeff i).support ↔ m.cons i ∈ f.support := by
  apply Iff.intro
  · intro h
    simpa [← finSuccEquiv_coeff_coeff] using h
  · intro h
    simpa [mem_support_iff, ← finSuccEquiv_coeff_coeff m f i] using h

/--
The `totalDegree` of a multivariable polynomial `p` is at least `i` more than the `totalDegree` of
the `i`th coefficient of `finSuccEquiv` applied to `p`, if this is nonzero.
-/
/-
**MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le** 是 Mathlib 中的一个引理，位于命名空间 `
MvPolynomial`。
形式化陈述：totalDegree_coeff_finSuccEquiv_add_le (f : MvPolynomial (Fin (n + 1)) R) (
i : Nat) (hi : (finSuccEquiv R n f).coeff i != 0) : totalDegree ((finSuccEquiv R
 n f).coeff i) + i <= totalDegree f
参数：f : MvPolynomial (Fin (n + 1)) R；i : Nat；hi : (finSuccEquiv R n f).coeff i !=
 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MvPolynomial.support_eq_empty`：support_eq_empty {p : MvPolynomial σ R} :
 p.support = ∅ ↔ p = 0
· 使用定理 `Finset.exists_mem_eq_sup`：exists_mem_eq_sup [OrderBot α] (s : Finset ι) 
(h : s.Nonempty) (f : ι -> α) : exists i, i in s ∧ s.sup f = f i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.totalDegree.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : Com
mSemiring R] (p : MvPolynomial σ R),   p.totalDegree = p.support.sup fun s => s.
sum fun x e => e
· 使用引理 `Finsupp.sum_cons`：sum_cons [AddCommMonoid M] (n : Nat) (σ : Fin n ->₀ M)
 (i : M) : (sum (cons i σ) fun _ e => e) = i + sum σ (fun _ e => e)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MvPolynomial.le_totalDegree`：le_totalDegree {p : MvPolynomial σ R} {s : 
σ ->₀ Nat} (h : s in p.support) : (s.sum fun _ e => e) <= totalDegree p
· 使用定理 `MvPolynomial.mem_support_coeff_finSuccEquiv`：mem_support_coeff_finSuccEq
uiv {f : MvPolynomial (Fin (n + 1)) R} {i : Nat} {m : Fin n ->₀ Nat} : m in ((fi
nSuccEquiv R n f).coeff i).suppor…

--- 原说明 ---
The `totalDegree` of a multivariable polynomial `p` is at least `i` more than th
e `totalDegree` of
the `i`th coefficient of `finSuccEquiv` applied to `p`, if this is nonzero.
-/
lemma totalDegree_coeff_finSuccEquiv_add_le (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ)
    (hi : (finSuccEquiv R n f).coeff i ≠ 0) :
    totalDegree ((finSuccEquiv R n f).coeff i) + i ≤ totalDegree f := by
  have hf'_sup : ((finSuccEquiv R n f).coeff i).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, support_eq_empty]
    exact hi
  -- Let σ be a monomial index of ((finSuccEquiv R n p).coeff i) of maximal total degree
  have ⟨σ, hσ1, hσ2⟩ := Finset.exists_mem_eq_sup (support _) hf'_sup
                          (fun s => Finsupp.sum s fun _ e => e)
  -- Then cons i σ is a monomial index of p with total degree equal to the desired bound
  let σ' : Fin (n + 1) →₀ ℕ := cons i σ
  convert! le_totalDegree (s := σ') _
  · rw [totalDegree, hσ2, sum_cons, add_comm]
  · rw [← mem_support_coeff_finSuccEquiv]
    exact hσ1

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.support_finSuccEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) : (finSuccEquiv R 
n f).support = Finset.image (fun m : Fin (n + 1) ->₀ Nat => m 0) f.support
参数：f : MvPolynomial (Fin (n + 1)) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.finSuccEquiv_coeff_coeff`：finSuccEquiv_coeff_coeff (m : Fin
 n ->₀ Nat) (f : MvPolynomial (Fin (n + 1)) R) (i : Nat) : coeff m (Polynomial.c
oeff (finSuccEquiv R n f) i…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.cons_zero`：cons_zero : cons y s 0 = y
· 使用定理 `Finsupp.cons_tail`：cons_tail : cons (t 0) (tail t) = t
-/
theorem support_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n f).support = Finset.image (fun m : Fin (n + 1) →₀ ℕ => m 0) f.support := by
  ext i
  simp only [Polynomial.mem_support_iff, ne_eq, MvPolynomial.ext_iff, coeff_zero, not_forall,
    Finset.mem_image, mem_support_iff, finSuccEquiv_coeff_coeff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨cons i m, hm, cons_zero _ _⟩
  · rintro ⟨m, h, rfl⟩
    exact ⟨tail m, by simpa using h⟩
/-
**MvPolynomial.mem_support_finSuccEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：mem_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {x} : x in (fi
nSuccEquiv R n f).support ↔ x in (fun m : Fin (n + 1) ->₀ _ => m 0) '' f.support
参数：Fin (n + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.support_finSuccEquiv`：support_finSuccEquiv (f : MvPolynomia
l (Fin (n + 1)) R) : (finSuccEquiv R n f).support = Finset.image (fun m : Fin (n
 + 1) ->₀ Nat => m 0) f…
-/
theorem mem_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {x} :
    x ∈ (finSuccEquiv R n f).support ↔ x ∈ (fun m : Fin (n + 1) →₀ _ ↦ m 0) '' f.support := by
  simpa using congr(x ∈ $(support_finSuccEquiv f))
/-
**MvPolynomial.image_support_finSuccEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
形式化陈述：image_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : Nat} : 
((finSuccEquiv R n f).coeff i).support.image (Finsupp.cons i) = {m in f.support 
| m 0 = i}
参数：Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.finSuccEquiv_coeff_coeff`：finSuccEquiv_coeff_coeff (m : Fin
 n ->₀ Nat) (f : MvPolynomial (Fin (n + 1)) R) (i : Nat) : coeff m (Polynomial.c
oeff (finSuccEquiv R n f) i…
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finsupp.cons_tail`：cons_tail : cons (t 0) (tail t) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem image_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} :
    ((finSuccEquiv R n f).coeff i).support.image (Finsupp.cons i) = {m ∈ f.support | m 0 = i} := by
  ext m
  rw [Finset.mem_filter, Finset.mem_image, mem_support_iff]
  conv_lhs =>
    congr
    ext
    rw [mem_support_iff, finSuccEquiv_coeff_coeff, Ne]
  constructor
  · grind [cons_zero]
  · intro h
    use tail m
    rw [← h.2, cons_tail]
    simp [h.1]
/-
**MvPolynomial.mem_image_support_coeff_finSuccEquiv** 是 Mathlib 中的一个引理，位于命名空间 `M
vPolynomial`。
形式化陈述：mem_image_support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i
 : Nat} {x} : x in Finsupp.cons i '' ((finSuccEquiv R n f).coeff i).support ↔ x 
in f.support ∧ x 0 = i
参数：Fin (n + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.image_support_finSuccEquiv`：image_support_finSuccEquiv {f :
 MvPolynomial (Fin (n + 1)) R} {i : Nat} : ((finSuccEquiv R n f).coeff i).suppor
t.image (Finsupp.cons i) = {m…
-/
lemma mem_image_support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {x} :
    x ∈ Finsupp.cons i '' ((finSuccEquiv R n f).coeff i).support ↔
      x ∈ f.support ∧ x 0 = i := by
  simpa using congr(x ∈ $image_support_finSuccEquiv)

-- TODO: generalize `finSuccEquiv R n` to an arbitrary ZeroHom
/-
**MvPolynomial.nonempty_support_finSuccEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyno
mial`。
形式化陈述：nonempty_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} (h : f !=
 0) : (finSuccEquiv R n f).support.Nonempty
参数：Fin (n + 1)；h : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.support_nonempty`：∀ {R : Type u} [inst : Semiring R] {p : Pol
ynomial R}, p.support.Nonempty ↔ p ≠ 0
· 使用定理 `EmbeddingLike.map_ne_zero_iff`：∀ {F : Type u_1} {M : Type u_4} {N : Type
 u_5} [inst : Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [EmbeddingLik
e F M N] [ZeroHomCl…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem nonempty_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquiv R n f).support.Nonempty := by
  rwa [Polynomial.support_nonempty, EmbeddingLike.map_ne_zero_iff]
/-
**MvPolynomial.degree_finSuccEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degree_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} (h : f != 0) : (fin
SuccEquiv R n f).degree = degreeOf 0 f
参数：Fin (n + 1)；h : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_eq_sup`：degreeOf_eq_sup (n : σ) (f : MvPolynomial 
σ R) : degreeOf n f = f.support.sup fun m => m n
· 使用定理 `MvPolynomial.support_finSuccEquiv`：support_finSuccEquiv (f : MvPolynomia
l (Fin (n + 1)) R) : (finSuccEquiv R n f).support = Finset.image (fun m : Fin (n
 + 1) ->₀ Nat => m 0) f…
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Polynomial.degree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R), p.degree = p.support.max
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
· 使用定理 `Finset.coe_sup_of_nonempty`：coe_sup_of_nonempty (h : s.Nonempty) (f : β 
-> α) : (↑(s.sup f) : WithBot α) = s.sup ((↑) ∘ f)
· 使用定理 `MvPolynomial.nonempty_support_finSuccEquiv`：nonempty_support_finSuccEqui
v {f : MvPolynomial (Fin (n + 1)) R} (h : f != 0) : (finSuccEquiv R n f).support
.Nonempty
· 使用定理 `Finset.max_eq_sup_coe`：max_eq_sup_coe {s : Finset α} : s.max = s.sup (↑)
-/
theorem degree_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquiv R n f).degree = degreeOf 0 f := by
  -- TODO: these should be lemmas
  have h₀ : ∀ {α β : Type _} (f : α → β), (fun x => x) ∘ f = f := fun f => rfl
  have h₁ : ∀ {α β : Type _} (f : α → β), f ∘ (fun x => x) = f := fun f => rfl
  have h' : ((finSuccEquiv R n f).support.sup fun x => x) = degreeOf 0 f := by
    rw [degreeOf_eq_sup, support_finSuccEquiv, Finset.sup_image, h₀]
  rw [Polynomial.degree, ← h', Nat.cast_withBot,
    Finset.coe_sup_of_nonempty (nonempty_support_finSuccEquiv h), Finset.max_eq_sup_coe, h₁]
/-
**MvPolynomial.natDegree_finSuccEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：natDegree_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) : (finSuccEquiv 
R n f).natDegree = degreeOf 0 f
参数：f : MvPolynomial (Fin (n + 1)) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `MvPolynomial.degreeOf_zero`：degreeOf_zero (n : σ) : degreeOf n (0 : MvPo
lynomial σ R) = 0
· 使用定理 `Polynomial.natDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R), p.natDegree = WithBot.unbotD 0 p.degree
· 使用定理 `MvPolynomial.degree_finSuccEquiv`：degree_finSuccEquiv {f : MvPolynomial 
(Fin (n + 1)) R} (h : f != 0) : (finSuccEquiv R n f).degree = degreeOf 0 f
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
· 使用定理 `WithBot.unbotD_coe`：unbotD_coe {α} (d x : α) : unbotD d x = x
-/
theorem natDegree_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n f).natDegree = degreeOf 0 f := by
  by_cases c : f = 0
  · rw [c, map_zero, Polynomial.natDegree_zero, degreeOf_zero]
  · rw [Polynomial.natDegree, degree_finSuccEquiv c, Nat.cast_withBot, WithBot.unbotD_coe]

/--
The `MvPolynomial.degreeOf` of a particular variable in a multivariate polynomial
is equal to the `Polynomial.natDegree` of the single-variable polynomial
obtained by treating the multivariable polynomial as a single variable polynomial
over multivariable polynomials in the remaining variables
-/
/-
**MvPolynomial.degreeOf_eq_natDegree** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_eq_natDegree [DecidableEq σ] (a : σ) (p : MvPolynomial σ R) : deg
reeOf a p = (optionEquivLeft R {b // b != a} (rename (Equiv.optionSubtypeNe a).s
ymm p)).natDegree
参数：a : σ；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.natDegree_optionEquivLeft`：natDegree_optionEquivLeft (p : M
vPolynomial (Option σ) R) : Polynomial.natDegree (optionEquivLeft R σ p) = p.deg
reeOf none
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.optionSubtypeNe_symm_apply`：∀ {α : Type u_1} [inst : DecidableEq α
] (a b : α),   (Equiv.optionSubtypeNe a).symm b = if h : b = a then none else so
me ⟨b, h⟩
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `MvPolynomial.degreeOf_rename_of_injective`：degreeOf_rename_of_injective 
{p : MvPolynomial σ R} {f : σ -> τ} (h : Function.Injective f) (i : σ) : degreeO
f (f i) (rename f p) = degreeOf…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
The `MvPolynomial.degreeOf` of a particular variable in a multivariate polynomia
l
is equal to the `Polynomial.natDegree` of the single-variable polynomial
obtained by treating the multivariable polynomial as a single variable polynomia
l
over multivariable polynomials in the remaining variables
-/
lemma degreeOf_eq_natDegree [DecidableEq σ] (a : σ) (p : MvPolynomial σ R) :
    degreeOf a p =
      (optionEquivLeft R {b // b ≠ a} (rename (Equiv.optionSubtypeNe a).symm p)).natDegree := by
  rw [natDegree_optionEquivLeft, eq_comm]
  convert! degreeOf_rename_of_injective (Equiv.injective (Equiv.optionSubtypeNe a).symm) a
  rw [Equiv.optionSubtypeNe_symm_apply, dif_pos rfl]
/-
**MvPolynomial.degreeOf_coeff_finSuccEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：degreeOf_coeff_finSuccEquiv (p : MvPolynomial (Fin (n + 1)) R) (j : Fin n)
 (i : Nat) : degreeOf j (Polynomial.coeff (finSuccEquiv R n p) i) <= degreeOf j.
succ p
参数：p : MvPolynomial (Fin (n + 1)) R；j : Fin n；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_eq_sup`：degreeOf_eq_sup (n : σ) (f : MvPolynomial 
σ R) : degreeOf n f = f.support.sup fun m => m n
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.cons_succ`：cons_succ : cons y s i.succ = s i
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.mem_support_coeff_finSuccEquiv`：mem_support_coeff_finSuccEq
uiv {f : MvPolynomial (Fin (n + 1)) R} {i : Nat} {m : Fin n ->₀ Nat} : m in ((fi
nSuccEquiv R n f).coeff i).suppor…
-/
theorem degreeOf_coeff_finSuccEquiv (p : MvPolynomial (Fin (n + 1)) R) (j : Fin n) (i : ℕ) :
    degreeOf j (Polynomial.coeff (finSuccEquiv R n p) i) ≤ degreeOf j.succ p := by
  rw [degreeOf_eq_sup, degreeOf_eq_sup, Finset.sup_le_iff]
  intro m hm
  rw [← Finsupp.cons_succ j i m]
  exact Finset.le_sup
    (f := fun (g : Fin (Nat.succ n) →₀ ℕ) => g (Fin.succ j))
    (mem_support_coeff_finSuccEquiv.1 hm)

/-- Consider a multivariate polynomial `φ` whose variables are indexed by `Option σ`,
and suppose that `σ ≃ Fin n`.
Then one may view `φ` as a polynomial over `MvPolynomial (Fin n) R`, by

1. renaming the variables via `Option σ ≃ Fin (n+1)`, and then singling out the `0`-th variable
    via `MvPolynomial.finSuccEquiv`;
2. first viewing it as polynomial over `MvPolynomial σ R` via `MvPolynomial.optionEquivLeft`,
    and then renaming the variables.

This lemma shows that both constructions are the same. -/
/-
**MvPolynomial.finSuccEquiv_rename_finSuccEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MvPol
ynomial`。
形式化陈述：finSuccEquiv_rename_finSuccEquiv (e : σ ≃ Fin n) (φ : MvPolynomial (Option
 σ) R) : ((finSuccEquiv R n) ((rename ((Equiv.optionCongr e).trans (_root_.finSu
ccEquiv n).symm)) φ)) = Polynomial.map (rename e).toRingHom (optionEquivLeft R σ
 φ)
参数：e : σ ≃ Fin n；φ : MvPolynomial (Option σ) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `MvPolynomial.ringHom_ext`：ringHom_ext {A : Type*} [Semiring A] {f g : Mv
Polynomial σ R ->+* A} (hC : forall r, f (C r) = g (C r)) (hX : forall i, f (X i
) = g (X i)) :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `MvPolynomial.finSuccEquiv_apply`：finSuccEquiv_apply (p : MvPolynomial (F
in (n + 1)) R) : finSuccEquiv R n p = eval₂Hom (Polynomial.C.comp (C : R ->+* Mv
Polynomial (Fin n) R)…
· 使用定理 `MvPolynomial.eval₂Hom_C`：eval₂Hom_C (f : R ->+* S₁) (g : σ -> S₁) (r : R
) : eval₂Hom f g (C r) = f r
· 使用定理 `MvPolynomial.optionEquivLeft_apply`：∀ (R : Type u) (S₁ : Type v) [inst :
 CommSemiring R] (a : MvPolynomial (Option S₁) R),   (MvPolynomial.optionEquivLe
ft R S₁) a =     (MvPoly…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `Equiv.optionCongr_apply`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) (a 
: Option α), e.optionCongr a = Option.map (⇑e) a
· 使用定理 `finSuccEquiv_symm_none`：finSuccEquiv_symm_none : (finSuccEquiv n).symm n
one = 0
· 使用定理 `MvPolynomial.eval₂Hom_X'`：eval₂Hom_X' (f : R ->+* S₁) (g : σ -> S₁) (i :
 σ) : eval₂Hom f g (X i) = g i
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `finSuccEquiv_symm_some`：finSuccEquiv_symm_some (m : Fin n) : (finSuccEqu
iv n).symm (some m) = m.succ
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
Consider a multivariate polynomial `φ` whose variables are indexed by `Option σ`
,
and suppose that `σ ≃ Fin n`.
Then one may view `φ` as a polynomial over `MvPolynomial (Fin n) R`, by

1. renaming the variables via `Option σ ≃ Fin (n+1)`, and then singling out the 
`0`-th variable
    via `MvPolynomial.finSuccEquiv`;
2. first viewing it as polynomial over `MvPolynomial σ R` via `MvPolynomial.opti
onEquivLeft`,
    and then renaming the variables.

This lemma shows that both constructions are the same.
-/
lemma finSuccEquiv_rename_finSuccEquiv (e : σ ≃ Fin n) (φ : MvPolynomial (Option σ) R) :
    ((finSuccEquiv R n) ((rename ((Equiv.optionCongr e).trans (_root_.finSuccEquiv n).symm)) φ)) =
      Polynomial.map (rename e).toRingHom (optionEquivLeft R σ φ) := by
  suffices (finSuccEquiv R n).toRingEquiv.toRingHom.comp (rename ((Equiv.optionCongr e).trans
        (_root_.finSuccEquiv n).symm)).toRingHom =
      (Polynomial.mapRingHom (rename e).toRingHom).comp (optionEquivLeft R σ) by
    exact DFunLike.congr_fun this φ
  apply ringHom_ext
  · simp [Polynomial.algebraMap_apply, algebraMap_eq, finSuccEquiv_apply, optionEquivLeft_apply]
  · rintro (i | i) <;> simp [finSuccEquiv_apply, optionEquivLeft_apply]

end

@[simp]
/-
**MvPolynomial.rename_polynomial_aeval_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：rename_polynomial_aeval_X {σ τ : Type*} (f : σ -> τ) (i : σ) (p : R[X]) : 
rename f (Polynomial.aeval (X i) p) = Polynomial.aeval (X (f i) : MvPolynomial τ
 R) p
参数：f : σ -> τ；i : σ；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
-/
theorem rename_polynomial_aeval_X {σ τ : Type*} (f : σ → τ) (i : σ) (p : R[X]) :
    rename f (Polynomial.aeval (X i) p) = Polynomial.aeval (X (f i) : MvPolynomial τ R) p := by
  rw [← aeval_algHom_apply, rename_X]

end Equiv

end MvPolynomial

section toMvPolynomial

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The embedding of `R[X]` into `R[Xᵢ]` as an `R`-algebra homomorphism. -/
/-
**Polynomial.toMvPolynomial** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Polynomial.toMvPolynomial (i : σ) : R[X] ->ₐ[R] MvPolynomial σ R
参数：i : σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of `R[X]` into `R[Xᵢ]` as an `R`-algebra homomorphism.
-/
noncomputable def Polynomial.toMvPolynomial (i : σ) : R[X] →ₐ[R] MvPolynomial σ R :=
  aeval (MvPolynomial.X i)

@[simp]
/-
**Polynomial.toMvPolynomial_C** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Polynomial.toMvPolynomial_C (i : σ) (r : R) : (C r).toMvPolynomial i = MvP
olynomial.C r
参数：i : σ；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Polynomial.toMvPolynomial_C (i : σ) (r : R) : (C r).toMvPolynomial i = MvPolynomial.C r := by
  simp [toMvPolynomial]

@[simp]
/-
**Polynomial.toMvPolynomial_X** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Polynomial.toMvPolynomial_X (i : σ) : X.toMvPolynomial i = MvPolynomial.X 
(R
参数：i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Polynomial.toMvPolynomial_X (i : σ) : X.toMvPolynomial i = MvPolynomial.X (R := R) i := by
  simp [toMvPolynomial]
/-
**Polynomial.toMvPolynomial_eq_rename_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Polynomial.toMvPolynomial_eq_rename_comp (i : σ) : toMvPolynomial (R
参数：i : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.algHom_ext`：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
 : f = g
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.toMvPolynomial_X`：Polynomial.toMvPolynomial_X (i : σ) : X.toM
vPolynomial i = MvPolynomial.X (R
· 使用定理 `MvPolynomial.uniqueAlgEquiv_symm_apply`：∀ (R : Type u) [inst : CommSemir
ing R] (σ : Type u_2) [inst_1 : Unique σ] (p : Polynomial R),   (MvPolynomial.un
iqueAlgEquiv R σ).symm p = P…
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Polynomial.toMvPolynomial_eq_rename_comp (i : σ) :
    toMvPolynomial (R := R) i =
      (MvPolynomial.rename (fun _ : Unit ↦ i)).comp (MvPolynomial.uniqueAlgEquiv R Unit).symm := by
  ext
  simp
/-
**Polynomial.toMvPolynomial_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Polynomial.toMvPolynomial_injective (i : σ) : Function.Injective (toMvPoly
nomial (R
参数：i : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.toMvPolynomial_eq_rename_comp`：Polynomial.toMvPolynomial_eq_r
ename_comp (i : σ) : toMvPolynomial (R
· 使用定理 `MvPolynomial.rename_injective`：rename_injective (f : σ -> τ) (hf : Funct
ion.Injective f) : Function.Injective (rename f : MvPolynomial σ R -> MvPolynomi
al τ R)
-/
lemma Polynomial.toMvPolynomial_injective (i : σ) :
    Function.Injective (toMvPolynomial (R := R) i) := by
  simp only [toMvPolynomial_eq_rename_comp, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom,
    EquivLike.injective_comp]
  exact MvPolynomial.rename_injective (fun x ↦ i) fun _ _ _ ↦ rfl
/-
**Polynomial.toMvPolynomial_inj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Polynomial.toMvPolynomial_inj {i : σ} {p q : R[X]} : toMvPolynomial (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.toMvPolynomial_injective`：Polynomial.toMvPolynomial_injective
 (i : σ) : Function.Injective (toMvPolynomial (R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma Polynomial.toMvPolynomial_inj {i : σ} {p q : R[X]} :
    toMvPolynomial (R := R) i p = toMvPolynomial i q ↔ p = q :=
  ⟨fun h ↦ Polynomial.toMvPolynomial_injective i h, fun h ↦ by rw [h]⟩

@[simp]
/-
**MvPolynomial.eval_comp_toMvPolynomial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MvPolynomial.eval_comp_toMvPolynomial (f : σ -> R) (i : σ) : (eval f).comp
 (toMvPolynomial (R
参数：f : σ -> R；i : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ringHom_ext'`：ringHom_ext' {S} [Semiring S] {f g : R[X] ->+* 
S} (h₁ : f.comp C = g.comp C) (h₂ : f X = g X) : f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.toMvPolynomial_C`：Polynomial.toMvPolynomial_C (i : σ) (r : R)
 : (C r).toMvPolynomial i = MvPolynomial.C r
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Polynomial.toMvPolynomial_X`：Polynomial.toMvPolynomial_X (i : σ) : X.toM
vPolynomial i = MvPolynomial.X (R
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
-/
lemma MvPolynomial.eval_comp_toMvPolynomial (f : σ → R) (i : σ) :
    (eval f).comp (toMvPolynomial (R := R) i) = Polynomial.evalRingHom (f i) := by
  ext <;> simp

@[simp]
/-
**MvPolynomial.eval_toMvPolynomial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MvPolynomial.eval_toMvPolynomial (f : σ -> R) (i : σ) (p : R[X]) : eval f 
(p.toMvPolynomial i) = Polynomial.eval (f i) p
参数：f : σ -> R；i : σ；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `MvPolynomial.eval_comp_toMvPolynomial`：MvPolynomial.eval_comp_toMvPolyno
mial (f : σ -> R) (i : σ) : (eval f).comp (toMvPolynomial (R
-/
lemma MvPolynomial.eval_toMvPolynomial (f : σ → R) (i : σ) (p : R[X]) :
    eval f (p.toMvPolynomial i) = Polynomial.eval (f i) p :=
  DFunLike.congr_fun (eval_comp_toMvPolynomial ..) p

@[simp]
/-
**MvPolynomial.aeval_comp_toMvPolynomial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MvPolynomial.aeval_comp_toMvPolynomial (f : σ -> S) (i : σ) : (aeval (R
参数：f : σ -> S；i : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.algHom_ext`：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
 : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.toMvPolynomial_X`：Polynomial.toMvPolynomial_X (i : σ) : X.toM
vPolynomial i = MvPolynomial.X (R
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MvPolynomial.aeval_comp_toMvPolynomial (f : σ → S) (i : σ) :
    (aeval (R := R) f).comp (toMvPolynomial i) = Polynomial.aeval (f i) := by
  ext
  simp

@[simp]
/-
**MvPolynomial.aeval_toMvPolynomial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MvPolynomial.aeval_toMvPolynomial (f : σ -> S) (i : σ) (p : R[X]) : aeval 
f (p.toMvPolynomial i) = Polynomial.aeval (f i) p
参数：f : σ -> S；i : σ；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `MvPolynomial.aeval_comp_toMvPolynomial`：MvPolynomial.aeval_comp_toMvPoly
nomial (f : σ -> S) (i : σ) : (aeval (R
-/
lemma MvPolynomial.aeval_toMvPolynomial (f : σ → S) (i : σ) (p : R[X]) :
    aeval f (p.toMvPolynomial i) = Polynomial.aeval (f i) p :=
  DFunLike.congr_fun (aeval_comp_toMvPolynomial ..) p

@[simp]
/-
**MvPolynomial.rename_comp_toMvPolynomial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MvPolynomial.rename_comp_toMvPolynomial (f : σ -> τ) (a : σ) : (rename (R
参数：f : σ -> τ；a : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.algHom_ext`：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
 : f = g
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.toMvPolynomial_X`：Polynomial.toMvPolynomial_X (i : σ) : X.toM
vPolynomial i = MvPolynomial.X (R
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MvPolynomial.rename_comp_toMvPolynomial (f : σ → τ) (a : σ) :
    (rename (R := R) f).comp (Polynomial.toMvPolynomial a) = Polynomial.toMvPolynomial (f a) := by
  ext
  simp

@[simp]
/-
**MvPolynomial.rename_toMvPolynomial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MvPolynomial.rename_toMvPolynomial (f : σ -> τ) (a : σ) (p : R[X]) : (rena
me (R
参数：f : σ -> τ；a : σ；p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `MvPolynomial.rename_comp_toMvPolynomial`：MvPolynomial.rename_comp_toMvPo
lynomial (f : σ -> τ) (a : σ) : (rename (R
-/
lemma MvPolynomial.rename_toMvPolynomial (f : σ → τ) (a : σ) (p : R[X]) :
    (rename (R := R) f) (p.toMvPolynomial a) = p.toMvPolynomial (f a) :=
  DFunLike.congr_fun (rename_comp_toMvPolynomial ..) p

end toMvPolynomial

